# SQEZ

SQLite Easy Mode (SQEZ) is a thin thread-safe wrapper around Python's [`sqlite3`](https://docs.python.org/3/library/sqlite3.html) module.

"SQEZ" is pronounced "squeezy".

## Quickstart

SQEZ is not (yet) available in PyPI.
You can use it by copying `src/sqez/` to your project.

```python
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
```

 - A `Connection` is expensive to create.  But, once established, interaction with the DB is fast.
 - The only thing you can do with a `Connection` is open `Transaction`s.  (Well, that or `close()` the `Connection`.)
 - Every read and write is done through a `Transaction`; a `Transaction` is either a `ReadTransaction` (which can read with `.select()`) or a `WriteTransaction` (which can read with `.select()` and write with `.exec()`).
 - Multiple `Transaction`s can share the same connection.  Transactions are strictly serializable.
 - A `Connection` is thread-safe, but a `Transaction` is not.

## Motivation

SQLite is one of the highest-quality pieces of software ever written.
Even so, there are a few sharp edges in Python's `sqlite3` module.
SQEZ was designed to make the API a bit more pleasant.

For me "pleasant" largely revolves around resource/transaction management and threads.
SQEZ does not save you from learning effective SQL, but it will save you from having to write `BEGIN IMMEDIATE` and `COMMIT` in your code.

### `sqlite3.Connection` can be used as a context manager, but unlike all other closable resources, it does not close on exit.
The `Cursor` objects cannot be used as a context manager at all.

```python
# DO NOT USE! This leaks a Connection object.
with sqlite3.connect("path/to/db") as conn:
    ...
```

```python
# Correct, but awkward!  Very un-Pythonic.
conn = sqlite3.connect("path/to/db")
try:
    ...
finally:
    conn.close()
```

```python
# This one will Just Work: the connection will be closed when the block exits.
with sqez.Connection("path/to/db") as conn:
    ...
```

### `sqlite3` has a confusing menagerie of poorly-named "autocommit" and "isolation" modes.
A transaction is a set of isolated reads and writes.
SQLite has [strictly serializable transactions](https://jepsen.io/consistency/models/strict-serializable), which is ideal from a safety and ease-of-development standpoint.
But, the `sqlite3` module makes it unclear when a transaction is open.
It is easy to make mistakes where related operations do not happen in the same transaction or where transactions are left open for too long.
(This is especially problematic in multi-threaded programs.)

In SQLite, [all operations happen within the scope of a transaction](https://sqlite.org/lang_transaction.html).
SQEZ makes that behavior explicit by using concrete `Transaction` objects as context managers:

```python
with sqez.Connection("path/to/db") as conn:

    # This transaction will commit if the block exits normally or rollback if
    # the block throws an exception.
    with sqez.WriteTransaction(conn) as tx:
        tx.select(...)
        tx.exec(...)
        if random.choice([True, False]):
            raise Exception("!")
```

### `sqlite3` has poor support for threaded applications.
By default, `sqlite3` does pedantic thread safety checking.
SQEZ instead offers thread-safe `Connection` objects, which saves the overhead of establishing a separate connection for each new thread.
`Transaction` objects are not thread-safe, but if properly synchronized they can be shared among threads.

Crucially, in SQEZ multiple threads can open transactions concurrently:

```python
with sqez.Connection("path/to/db") as conn:
    t1 = threading.Thread(daemon=True, target=lambda: job1(conn))
    t2 = threading.Thread(daemon=True, target=lambda: job2(conn))
    t1.start()
    t2.start()
    t1.join()
    t2.join()
```

Although keep in mind that SQLite uses a single global lock to make write transactions strictly serializable.
SQEZ has some clever internal concurrency control to make read transactions proceed somewhat in parallel without `SQLITE_BUSY` errors.

### Every project should use write-ahead logging (WAL mode), but it is not the default.

SQEZ enables [WAL mode](https://www.sqlite.org/wal.html) on every `Connection`.

## Sharp Edges

 - Deadlocks are possible.  Do not try to open a transaction while another is open in the same thread.
