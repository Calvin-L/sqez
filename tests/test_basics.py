#!/usr/bin/env python3

from typing import Callable, Any
import threading
import logging

from sqez import *

class ExpectedException(Exception):
    pass

def test_basics() -> None:
    print("---- test_basics() ----")
    with Connection(":memory:") as conn:
        with WriteTransaction(conn) as tx:
            tx.exec("CREATE TABLE foo (value INT)")
            inserted = tx.exec("INSERT INTO foo (value) VALUES (?)", (5,))
            assert inserted == 1
        with ReadTransaction(conn) as tx:
            rows = tx.select("SELECT * FROM foo")
            assert rows == [(5,)]

def test_exception() -> None:
    print("---- test_exception() ----")
    with Connection(":memory:") as conn:
        with WriteTransaction(conn) as tx:
            tx.exec("CREATE TABLE foo (value INT)")
        try:
            with WriteTransaction(conn) as tx:
                inserted = tx.exec("INSERT INTO foo (value) VALUES (?)", (5,))
                raise ExpectedException()
        except ExpectedException:
            pass
        with ReadTransaction(conn) as tx:
            rows = tx.select("SELECT * FROM foo")
            assert rows == []

def par(*jobs: Callable[[], None]) -> None:
    threads = [threading.Thread(target=j, daemon=True) for j in jobs]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

def test_concurrency1() -> None:
    print("---- test_concurrency1() ----")
    with Connection(":memory:") as conn:
        with WriteTransaction(conn) as init:
            init.exec("CREATE TABLE foo (value INT)")
        def t1() -> None:
            with WriteTransaction(conn) as tx:
                tx.exec("INSERT INTO foo (value) VALUES (?)", (1,))
        def t2() -> None:
            with WriteTransaction(conn) as tx:
                tx.exec("INSERT INTO foo (value) VALUES (?)", (2,))
        par(t1, t2)
        with ReadTransaction(conn) as tx:
            assert tx.select("SELECT value FROM foo ORDER BY value ASC") == [(1,), (2,)]

def test_concurrency2() -> None:
    print("---- test_concurrency2() ----")
    with Connection(":memory:") as conn:
        count = 0
        def job() -> None:
            nonlocal count
            with ReadTransaction(conn) as tx:
                tx.select("SELECT * FROM sqlite_schema")
        par(job, job, job)

def test_early_connection_close() -> None:
    with Connection(":memory:") as conn:
        conn.close()
        message = None
        try:
            with ReadTransaction(conn) as tx:
                pass
        except Exception as e:
            message = str(e)
        assert message == "Illegal connection state _ConnectionState.CLOSED" # TODO: better message

def test_early_read_transaction_close() -> None:
    with Connection(":memory:") as conn:
        with ReadTransaction(conn) as tx:
            tx.close()
            message = None
            try:
                tx.select("SELECT * FROM sqlite_schema")
            except Exception as e:
                message = str(e)
            assert message == "Transaction is not open"

def test_early_write_transaction_close() -> None:
    with Connection(":memory:") as conn:
        with WriteTransaction(conn) as tx:
            tx.exec("CREATE TABLE foo (val INT)")
        with WriteTransaction(conn) as tx:
            tx.close()
            message = None
            try:
                tx.exec("INSERT INTO foo (val) VALUES (1)")
            except Exception as e:
                message = str(e)
            assert message == "Transaction is not open"
        with ReadTransaction(conn) as tx:
            assert tx.select("SELECT val FROM foo") == []

def test_early_write_transaction_commit() -> None:
    with Connection(":memory:") as conn:
        with WriteTransaction(conn) as tx:
            tx.exec("CREATE TABLE foo (val INT)")
        with WriteTransaction(conn) as tx:
            tx.exec("INSERT INTO foo (val) VALUES (1)")
            tx.commit()
            message = None
            try:
                tx.exec("INSERT INTO foo (val) VALUES (2)")
            except Exception as e:
                message = str(e)
            assert message == "Transaction is not open"
        with ReadTransaction(conn) as tx:
            assert tx.select("SELECT val FROM foo") == [(1,)]

def test_exotic_selects() -> None:
    with Connection(":memory:") as conn:
        with ReadTransaction(conn) as tx:
            assert tx.select("SELECT count(*) FROM sqlite_schema") == [(0,)]
            assert tx.select("""
                WITH tmp (cnt) AS (SELECT count(*) FROM sqlite_schema)
                SELECT * FROM tmp
                """) == [(0,)]
            assert tx.select("VALUES (1, 2, 3)") == [(1,2,3)]

            message = None
            try:
                tx.select("CREATE TABLE foo (x INT)")
            except Exception as e:
                message = str(e)
            assert message == "'CREATE TABLE foo (x INT)' is not a SELECT statement"

def test_sneaky_insert() -> None:
    # I don't know of a reliable way to TRULY enforce that tx.select() only
    # accepts read operations.  To allow compound WITH-SELECT statements we
    # also have to admit compound WITH-INSERT statements.  :(  But we can at
    # least ensure that the effects of such an operation are invisible to other
    # transactions.
    with Connection(":memory:") as conn:
        with WriteTransaction(conn) as tx:
            tx.exec("CREATE TABLE foo (x INT)")
        with ReadTransaction(conn) as tx:
            tx.select("""
                WITH tmp (cnt) AS (SELECT count(*) FROM sqlite_schema)
                INSERT INTO foo (x) SELECT cnt FROM tmp
                """) == [(0,)]
        with ReadTransaction(conn) as tx:
            assert tx.select("SELECT * FROM foo") == []
