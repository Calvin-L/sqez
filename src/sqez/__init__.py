# MIT License
#
# Copyright (c) 2024 Calvin Loncaric
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.


"""
SQEZ is a thin thread-safe wrapper around sqlite3.

To use the module, create a Connection and then use that to create
a ReadTransaction or WriteTransaction:

    import sqez

    with sqez.Connection("path/to/db") as conn:

        with sqez.WriteTransaction(conn) as tx:
            tx.exec("CREATE TABLE foo (value INT)")
            inserted = tx.exec("INSERT INTO foo (value) VALUES (?)", (5,))
            assert inserted == 1
            assert tx.select("SELECT * FROM foo WHERE value=?", (1,)) == []

        with sqez.ReadTransaction(conn) as tx:
            rows = tx.select("SELECT * FROM foo")
            assert rows == [(5,)]
"""


from abc import ABC, abstractmethod
from collections import deque
from enum import Enum
from pathlib import PurePath
from types import TracebackType
from typing import Any, Self, Optional, Union, Literal, TypeAlias, Callable
import logging
import sqlite3
import threading
import time
import re


__all__ = [
    'Connection',
    'Transaction',
    'ReadTransaction',
    'WriteTransaction',
]


_logger = logging.getLogger(__name__)
_SELECT_START_REGEX = re.compile(r"^\s*(?:SELECT|WITH|VALUES)\b", re.IGNORECASE)


def _no_cleanup() -> None:
    pass


class _LockMode(Enum):
    IDLE  = 0
    READ  = 1
    WRITE = 2


_READ_OR_WRITE: TypeAlias = Literal[_LockMode.READ, _LockMode.WRITE]


class _FairRWLock:
    __slots__ = ("_cv", "_mode", "_active_clients", "_pending_readers", "_pending_writers")

    def __init__(self) -> None:
        self._cv = threading.Condition(threading.Lock())
        self._mode: _LockMode = _LockMode.IDLE
        self._active_clients: set[threading.Thread] = set()
        self._pending_readers: set[threading.Thread] = set()
        self._pending_writers: deque[threading.Thread] = deque([])

    def acquire(self, desired_mode: _READ_OR_WRITE) -> None:
        cv = self._cv
        active_clients = self._active_clients
        pending_readers = self._pending_readers
        pending_writers = self._pending_writers
        me = threading.current_thread()
        with cv:
            if self._mode == _LockMode.IDLE and not pending_readers and not pending_writers:
                # fast path
                self._mode = desired_mode
            else:
                # slow path: register interest
                if desired_mode == _LockMode.WRITE:
                    pending_writers.append(me)
                else:
                    pending_readers.add(me)

                # wait loop
                while True:
                    if self._mode == _LockMode.IDLE:
                        if desired_mode == _LockMode.WRITE:
                            if pending_writers[0] is me:
                                pending_writers.popleft()
                                self._mode = desired_mode
                                break
                        else:
                            active_clients.update(pending_readers)
                            pending_readers.clear()
                            self._mode = desired_mode
                            break
                    elif me in active_clients:
                        break
                    cv.wait()

    def release(self, cleanup: Callable[[], None] = _no_cleanup) -> None:
        cv = self._cv
        active_clients = self._active_clients
        pending_readers = self._pending_readers
        pending_writers = self._pending_writers
        me = threading.current_thread()
        with cv:
            active_clients.discard(me)
            if not active_clients:
                try:
                    cleanup()
                finally:
                    if self._mode == _LockMode.WRITE:
                        if pending_readers:
                            self._mode = _LockMode.READ
                            active_clients.update(pending_readers)
                            pending_readers.clear()
                        else:
                            self._mode = _LockMode.IDLE
                    else:
                        if pending_writers:
                            self._mode = _LockMode.WRITE
                            active_clients.add(pending_writers.popleft())
                        else:
                            self._mode = _LockMode.IDLE
                    cv.notify_all()


class _Resource(ABC):
    """
    A resource has an idempotent close() method.  It can be used as a context
    manager, in which case it closes when the block exits.  Also, __del__
    calls close() just in case.
    """

    __slots__ = ()

    @abstractmethod
    def close(self) -> None:
        """
        Close the resource.
        """
        raise NotImplementedError()

    def __del__(self) -> None:
        self.close()

    def __enter__(self) -> Self:
        return self

    def __exit__(self, exc_type: Optional[type], exc_val: Optional[Exception], exc_tb: Optional[TracebackType]) -> None:
        self.close()


class _ConnectionState(Enum):
    IDLE         = 0
    READ_LOCKED  = 1
    WRITE_LOCKED = 2
    CORRUPT      = 3
    CLOSED       = 4


class Connection(_Resource):
    """
    A connection to a SQLite database.  Connection objects can be used as
    context managers; the connection will be closed at the end of the context.

    Multiple threads can safely share one Connection.
    """

    __slots__ = ("_txn_lock", "_exec_lock", "_state", "_conn", "_cursor")

    def __init__(self, filename: Union[str, PurePath]):
        """
        Create a connection.

        Parameters:

         - filename -- the file to open
        """

        super().__init__()
        _logger.debug("Opening connection to sqlite db %s...", filename)
        start = time.time()
        assert sqlite3.threadsafety > 0, "sqlite3 module is not safe to share between threads"
        self._txn_lock = _FairRWLock()
        self._exec_lock = threading.Lock()
        self._state: _ConnectionState = _ConnectionState.IDLE

        # 2024/8/15: Initially I had tried to make this work with the shiny new
        # "autocommit" setting, if available (see commented-out code below).
        # But I was bitten because when autocommit is False,
        #  > sqlite3 ensures that a transaction is always open
        # which is an utterly insane decision.  It seems to be allowed by
        # PEP 249, but (my reading of) the spirit of the law makes this choice
        # incredibly bizarre; shouldn't multiple connections in different
        # processes be able to collaborate on the same DB?
        #
        # In the future I may investigate leveraging the fact that autocommit
        # mode uses `BEGIN DEFERRED`, but I don't have the time right now.  So,
        # legacy `isolation_level=None` it is.
        self._conn = sqlite3.connect(filename, timeout=5, check_same_thread=False, isolation_level=None)

        # connect_opts: dict[str, Any] = {}
        # if sys.version_info >= (3, 12):
        #     # Reminder: autocommit=False means "the connection is operating in manual commit (transactional) mode".
        #     # See: https://peps.python.org/pep-0249/
        #     connect_opts["autocommit"] = False
        # else:
        #     # Reminder: isolation_level=None means "transactions are never implicitly opened".
        #     # This option is ignored if autocommit != LEGACY_TRANSACTION_CONTROL, but that
        #     # option is not available in Python < 3.12.
        #     connect_opts["isolation_level"] = None
        # self._conn = sqlite3.connect(filename, timeout=5, check_same_thread=False, **connect_opts)

        # Subsequent initialization might throw exceptions.  In that
        # case WE are responsible for cleaning up the connection,
        # since this object has not been returned to the caller yet.
        try:
            self._cursor = self._conn.cursor()
            # Subsequent initialization might throw exceptions.  In that
            # case WE are responsible for cleaning up the cursor,
            # since this object has not been returned to the caller yet.
            try:
                self._cursor.execute("PRAGMA journal_mode=WAL")
                _logger.debug("Opened connection in %ims", (time.time() - start) * 1000)
            except:
                self._cursor.close()
                raise
        except:
            self._conn.close()
            raise

    def close(self) -> None:
        """
        Close the connection.  Any open transactions will become unusable.
        """

        # Wait for all in-progress transactions to close.
        self._txn_lock.acquire(_LockMode.WRITE)

        try:
            if self._state != _ConnectionState.CLOSED:
                # Prevent any future operations on this connection.
                self._state = _ConnectionState.CLOSED

                # Close all resources.
                try:
                    self._cursor.close()
                finally:
                    self._conn.close()
        finally:
            self._txn_lock.release()

    def _begin_deferred_if_not_in_txn(self) -> None:
        match self._state:
            case _ConnectionState.IDLE:
                self._state = _ConnectionState.CORRUPT # in case begin fails
                assert not self._conn.in_transaction
                self._cursor.execute("BEGIN DEFERRED")
                # Force SQLite to upgrade our transaction to a shared read transaction
                # immediately.  This is intended to work around (what I see as) a
                # massive gap in SQLite's transaction isolation, where certain error
                # codes that seem to imply something about the state of the database
                # (e.g. missing table) are actually computed OUTSIDE the scope of the
                # transaction, and therefore can appear to change due to repeated calls
                # within the same transaction.  No repeatable reads means no
                # serializability!
                #
                # Anyways, doing a read ensures that our transaction is immediately
                # upgraded to a read transaction, and therefore we can trust the error
                # codes reported by subsequent statements.
                #
                # See: https://sqlite.org/forum/forumpost/d025322e746a5930
                self._cursor.execute("SELECT * FROM sqlite_schema LIMIT 1")
                self._state = _ConnectionState.READ_LOCKED
            case _ConnectionState.READ_LOCKED:
                pass
            case _:
                raise Exception(f"Illegal connection state {self._state}")

    def _begin_immediate(self) -> None:
        match self._state:
            case _ConnectionState.IDLE:
                self._state = _ConnectionState.CORRUPT # in case begin fails
                assert not self._conn.in_transaction
                self._cursor.execute("BEGIN IMMEDIATE")
                self._state = _ConnectionState.WRITE_LOCKED
            case _:
                raise Exception(f"Illegal connection state {self._state}")

    def _exec(self, sql: str, argv: tuple[Any, ...] = ()) -> list[tuple[Any, ...]]:
        match self._state:
            case _ConnectionState.READ_LOCKED | _ConnectionState.WRITE_LOCKED:
                assert self._conn.in_transaction
                return list(self._cursor.execute(sql, argv))
            case _:
                raise Exception(f"Illegal connection state {self._state}")

    @property
    def _rowcount(self) -> int:
        return self._cursor.rowcount

    def _rollback(self) -> None:
        match self._state:
            case _ConnectionState.READ_LOCKED | _ConnectionState.WRITE_LOCKED:
                self._state = _ConnectionState.CORRUPT # in case rollback fails
                assert self._conn.in_transaction
                self._cursor.execute("ROLLBACK")
                self._state = _ConnectionState.IDLE
            case _ConnectionState.CLOSED:
                pass
            case _:
                raise Exception(f"Illegal connection state {self._state}")

    def _commit(self) -> None:
        match self._state:
            case _ConnectionState.WRITE_LOCKED:
                self._state = _ConnectionState.CORRUPT # in case commit fails
                assert self._conn.in_transaction
                self._cursor.execute("COMMIT")
                self._state = _ConnectionState.IDLE
            case _:
                raise Exception(f"Illegal connection state {self._state}")


class _TransactionState(Enum):
    OPEN             = 1
    COMMIT_AMBIGUOUS = 2
    COMMITTED        = 3
    CLOSED           = 4


class Transaction(_Resource):
    """
    A Transaction is either a ReadTransaction or a WriteTransaction.  Both
    kinds of transactions support select().

    Transactions are not thread-safe.
    """

    __slots__ = ("_state", "_connection")

    def __init__(self, connection: Connection) -> None:
        """
        Create a transaction.

        Parameters:

         - connection    -- the underlying connection
        """

        super().__init__()
        self._state = _TransactionState.OPEN
        self._connection = connection

    def select(self, sql: str, argv: tuple[Any, ...] = ()) -> list[tuple[Any, ...]]:
        """
        Read data out of the database.

        Parameters:

         - sql  -- a SELECT, WITH-SELECT, or VALUES statement
         - argv -- values to bind to '?' placeholders in the given sql

        Returns the read rows as a list of tuples.
        """

        if self._state != _TransactionState.OPEN:
            raise Exception("Transaction is not open")
        if not _SELECT_START_REGEX.match(sql):
            raise Exception(f"{sql!r} is not a SELECT statement")
        _logger.debug("Selecting %r", sql)
        start = time.time()

        with self._connection._exec_lock:
            assert self._connection._conn.in_transaction
            result = self._connection._exec(sql, argv)

        _logger.debug("Executed in %ims", (time.time() - start) * 1000)
        return result


class ReadTransaction(Transaction):
    """
    A read-only transaction.
    """

    __slots__ = ()

    def __init__(self, connection: Connection) -> None:
        """
        Create a read-only transaction.

        Parameters:

         - connection -- the connection to use

        This constructor will block until there are no open writers on the
        connection.  Multiple read transactions can proceed in parallel.
        """

        _logger.debug("Opening ReadTransaction...")
        start = time.time()
        super().__init__(connection)

        self._connection._txn_lock.acquire(_LockMode.READ)

        # Subsequent initialization might throw exceptions.  In that
        # case WE are responsible for releasing the lock,
        # since this object has not been returned to the caller yet.
        try:
            with self._connection._exec_lock:
                self._connection._begin_deferred_if_not_in_txn()
            _logger.debug("Opened ReadTransaction in %ims", (time.time() - start) * 1000)
        except:
            self._connection._txn_lock.release()
            raise

    def close(self) -> None:
        if self._state != _TransactionState.CLOSED:
            self._state = _TransactionState.CLOSED
            _logger.debug("Closing ReadTransaction...")
            start = time.time()
            self._connection._txn_lock.release(self._connection._rollback)
            _logger.debug("Closed in %ims", (time.time() - start) * 1000)


class WriteTransaction(Transaction):
    """
    A read/write transaction.
    """

    __slots__ = ()

    def __init__(self, connection: Connection) -> None:
        """
        Create a read/write transaction.

        Parameters:

         - connection -- the connection to use

        This constructor will block until there are no open readers or
        writers on the connection.
        """

        _logger.debug("Opening WriteTransaction...")
        start = time.time()
        super().__init__(connection)

        self._connection._txn_lock.acquire(_LockMode.WRITE)

        # Subsequent initialization might throw exceptions.  In that
        # case WE are responsible for releasing the lock,
        # since this object has not been returned to the caller yet.
        try:
            self._connection._begin_immediate()
            _logger.debug("Opened WriteTransaction in %ims", (time.time() - start) * 1000)
        except:
            self._connection._txn_lock.release()
            raise

    def exec(self, sql: str, argv: tuple[Any, ...] = ()) -> int:
        """
        Execute an arbitrary SQL statement.

        Parameters:

         - sql  -- a SELECT, WITH-SELECT, or VALUES statement
         - argv -- values to bind to '?' placeholders in the given sql

        Returns the number of modified rows.  If the statement was not an
        INSERT, UPDATE, or DELETE then the number is arbitrary.
        """

        if self._state != _TransactionState.OPEN:
            raise Exception("Transaction is not open")
        _logger.debug("Executing %r...", sql)
        start = time.time()
        assert self._connection._conn.in_transaction
        self._connection._exec(sql, argv) # don't need _exc_lock; holding exclusive _txn_lock
        result: int = self._connection._rowcount
        _logger.debug("Executed in %ims", (time.time() - start) * 1000)
        return result

    def commit(self) -> None:
        """
        Commit this transaction, making it durable and visible to subsequent
        readers.

        This method should rarely be called directly; if you use a
        WriteTransaction as a context manager then it will automatically commit
        at the end of the block (provided the block exits normally).

        But, it is OK to call this method directly, even if this object is used
        as a context manager, in which case it simply commits early.  Calling
        this method also closes the transaction, making it unusable.
        """

        if self._state != _TransactionState.OPEN:
            raise Exception("Transaction is not open")
        _logger.debug("Committing...")
        start = time.time()
        self._state = _TransactionState.COMMIT_AMBIGUOUS
        self._connection._commit() # don't need _exc_lock; holding exclusive _txn_lock
        self._state = _TransactionState.COMMITTED
        _logger.debug("Committed in %ims", (time.time() - start) * 1000)

    def __exit__(self, exc_type: Optional[type], exc_val: Optional[Exception], exc_tb: Optional[TracebackType]) -> None:
        try:
            if exc_type is None and self._state == _TransactionState.OPEN:
                self.commit()
        finally:
            super().__exit__(exc_type, exc_val, exc_tb)

    def close(self) -> None:
        """
        Close the transaction without committing ("abort" or "rollback").
        No-op if the transaction has already committed.
        """

        try:
            if self._state in (_TransactionState.OPEN, _TransactionState.COMMIT_AMBIGUOUS):
                _logger.debug("Rolling back WriteTransaction...")
                start = time.time()
                self._connection._rollback() # don't need _exc_lock; holding exclusive _txn_lock
                _logger.debug("Rolled back in %ims", (time.time() - start) * 1000)
        finally:
            if self._state != _TransactionState.CLOSED:
                self._state = _TransactionState.CLOSED
                self._connection._txn_lock.release()
