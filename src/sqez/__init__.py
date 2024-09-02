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


from abc import ABC, abstractmethod
from collections import deque
from pathlib import PurePath
from types import TracebackType
from typing import Any, Self, Optional, Union, Literal, TypeAlias, Callable
import logging
import sqlite3
import threading
import time
import re


_logger = logging.getLogger(__name__)
_IDLE_MODE: Literal[0] = 0
_READ_MODE: Literal[1] = 1
_WRITE_MODE: Literal[2] = 2
_READ_OR_WRITE: TypeAlias = Literal[1, 2]
_IDLE_OR_READ_OR_WRITE: TypeAlias = Literal[0, 1, 2]
_SELECT_START_REGEX = re.compile(r"^\s*(?:SELECT|WITH|VALUES)\b", re.IGNORECASE)


def _no_cleanup() -> None:
    pass


class _FairRWLock:
    __slots__ = ("_cv", "_mode", "_active_clients", "_pending_readers", "_pending_writers")

    def __init__(self) -> None:
        self._cv = threading.Condition(threading.Lock())
        self._mode: _IDLE_OR_READ_OR_WRITE = 0
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
            if self._mode == _IDLE_MODE and not pending_readers and not pending_writers:
                # fast path
                self._mode = desired_mode
            else:
                # slow path: register interest
                if desired_mode == _WRITE_MODE:
                    pending_writers.append(me)
                else:
                    pending_readers.add(me)

                # wait loop
                while True:
                    if self._mode == _IDLE_MODE:
                        if desired_mode == _WRITE_MODE:
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
                    if self._mode == _WRITE_MODE:
                        if pending_readers:
                            self._mode = _READ_MODE
                            active_clients.update(pending_readers)
                            pending_readers.clear()
                        else:
                            self._mode = _IDLE_MODE
                    else:
                        if pending_writers:
                            self._mode = _WRITE_MODE
                            active_clients.add(pending_writers.popleft())
                        else:
                            self._mode = _IDLE_MODE
                    cv.notify_all()


class _Resource(ABC):
    __slots__ = ()

    @abstractmethod
    def close(self) -> None:
        raise NotImplementedError()

    def __del__(self) -> None:
        self.close()

    def __enter__(self) -> Self:
        return self

    def __exit__(self, exc_type: Optional[type], exc_val: Optional[Exception], exc_tb: Optional[TracebackType]) -> None:
        self.close()


class Connection(_Resource):
    __slots__ = ("_txn_lock", "_exec_lock", "_state", "_conn", "_cursor")

    IDLE         = 0
    READ_LOCKED  = 1
    WRITE_LOCKED = 2
    CORRUPT      = 3
    CLOSED       = 4

    def __init__(self, filename: Union[str, PurePath]):
        super().__init__()
        _logger.debug("Opening connection to sqlite db %s...", filename)
        start = time.time()
        assert sqlite3.threadsafety > 0, "sqlite3 module is not safe to share between threads"
        self._txn_lock = _FairRWLock()
        self._exec_lock = threading.Lock()
        self._state = Connection.IDLE

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
        # Wait for all in-progress transactions to close.
        self._txn_lock.acquire(_WRITE_MODE)

        try:
            if self._state != Connection.CLOSED:
                # Prevent any future operations on this connection.
                self._state = Connection.CLOSED

                # Close all resources.
                try:
                    self._cursor.close()
                finally:
                    self._conn.close()
        finally:
            self._txn_lock.release()

    def _begin_deferred_if_not_in_txn(self) -> None:
        match self._state:
            case Connection.IDLE:
                self._state = Connection.CORRUPT # in case begin fails
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
                self._state = Connection.READ_LOCKED
            case Connection.READ_LOCKED:
                pass
            case _:
                raise Exception(f"Illegal connection state {self._state}")

    def _begin_immediate(self) -> None:
        match self._state:
            case Connection.IDLE:
                self._state = Connection.CORRUPT # in case begin fails
                assert not self._conn.in_transaction
                self._cursor.execute("BEGIN IMMEDIATE")
                self._state = Connection.WRITE_LOCKED
            case _:
                raise Exception(f"Illegal connection state {self._state}")

    def _exec(self, sql: str, argv: tuple[Any, ...] = ()) -> list[tuple[Any, ...]]:
        match self._state:
            case Connection.READ_LOCKED | Connection.WRITE_LOCKED:
                assert self._conn.in_transaction
                return list(self._cursor.execute(sql, argv))
            case _:
                raise Exception(f"Illegal connection state {self._state}")

    @property
    def _rowcount(self) -> int:
        return self._cursor.rowcount

    def _rollback(self) -> None:
        match self._state:
            case Connection.READ_LOCKED | Connection.WRITE_LOCKED:
                self._state = Connection.CORRUPT # in case rollback fails
                assert self._conn.in_transaction
                self._cursor.execute("ROLLBACK")
                self._state = Connection.IDLE
            case Connection.CLOSED:
                pass
            case _:
                raise Exception(f"Illegal connection state {self._state}")

    def _commit(self) -> None:
        match self._state:
            case Connection.WRITE_LOCKED:
                self._state = Connection.CORRUPT # in case commit fails
                assert self._conn.in_transaction
                self._cursor.execute("COMMIT")
                self._state = Connection.IDLE
            case _:
                raise Exception(f"Illegal connection state {self._state}")


class Transaction(_Resource):
    OPEN_RO          : Literal[1] = 1
    OPEN_RW          : Literal[2] = 2
    COMMIT_AMBIGUOUS : Literal[3] = 3
    COMMITTED        : Literal[4] = 4
    CLOSED           : Literal[5] = 5
    OPEN             = {OPEN_RO, OPEN_RW}

    __slots__ = ("_state", "_connection")

    def __init__(self, connection: Connection, initial_state: Literal[1, 2]) -> None:
        super().__init__()
        self._state: Literal[1, 2, 3, 4, 5] = initial_state
        self._connection = connection

    def select(self, sql: str, argv: tuple[Any, ...] = ()) -> list[tuple[Any, ...]]:
        if self._state not in Transaction.OPEN:
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
    __slots__ = ()

    def __init__(self, connection: Connection) -> None:
        _logger.debug("Opening ReadTransaction...")
        start = time.time()
        super().__init__(connection, Transaction.OPEN_RO)

        self._connection._txn_lock.acquire(_READ_MODE)

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
        if self._state != Transaction.CLOSED:
            self._state = Transaction.CLOSED
            _logger.debug("Closing ReadTransaction...")
            start = time.time()
            self._connection._txn_lock.release(self._connection._rollback)
            _logger.debug("Closed in %ims", (time.time() - start) * 1000)


class WriteTransaction(Transaction):
    __slots__ = ()

    def __init__(self, connection: Connection) -> None:
        _logger.debug("Opening WriteTransaction...")
        start = time.time()
        super().__init__(connection, Transaction.OPEN_RW)

        self._connection._txn_lock.acquire(_WRITE_MODE)

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
        if self._state not in Transaction.OPEN:
            raise Exception("Transaction is not open")
        _logger.debug("Executing %r...", sql)
        start = time.time()
        assert self._connection._conn.in_transaction
        self._connection._exec(sql, argv) # don't need _exc_lock; holding exclusive _txn_lock
        result: int = self._connection._rowcount
        _logger.debug("Executed in %ims", (time.time() - start) * 1000)
        return result

    def commit(self) -> None:
        if self._state not in Transaction.OPEN:
            raise Exception("Transaction is not open")
        _logger.debug("Committing...")
        start = time.time()
        self._state = Transaction.COMMIT_AMBIGUOUS
        self._connection._commit() # don't need _exc_lock; holding exclusive _txn_lock
        self._state = Transaction.COMMITTED
        _logger.debug("Committed in %ims", (time.time() - start) * 1000)

    def __exit__(self, exc_type: Optional[type], exc_val: Optional[Exception], exc_tb: Optional[TracebackType]) -> None:
        try:
            if exc_type is None and self._state == Transaction.OPEN_RW:
                self.commit()
        finally:
            super().__exit__(exc_type, exc_val, exc_tb)

    def close(self) -> None:
        try:
            if self._state in (Transaction.OPEN_RW, Transaction.COMMIT_AMBIGUOUS):
                _logger.debug("Rolling back WriteTransaction...")
                start = time.time()
                self._connection._rollback() # don't need _exc_lock; holding exclusive _txn_lock
                _logger.debug("Rolled back in %ims", (time.time() - start) * 1000)
        finally:
            if self._state != Transaction.CLOSED:
                self._state = Transaction.CLOSED
                self._connection._txn_lock.release()
