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

def test_two_readonly() -> None:
    print("---- test_two_readonly() ----")
    with Connection(":memory:") as conn:
        with ReadTransaction(conn) as tx1:
            tx1.select("SELECT * FROM sqlite_schema")
            with ReadTransaction(conn) as tx2:
                tx2.select("SELECT * FROM sqlite_schema")
                tx1.select("SELECT * FROM sqlite_schema")
            tx1.select("SELECT * FROM sqlite_schema")

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
        cv = threading.Condition(threading.Lock())
        count = 0
        def job() -> None:
            nonlocal count
            with ReadTransaction(conn) as tx:
                with cv:
                    count += 1
                    cv.notify_all()
                    while count < 3:
                        cv.wait()
                tx.select("SELECT * FROM sqlite_schema")
        par(job, job, job)

if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG)
    test_basics()
    test_exception()
    test_two_readonly()
    test_concurrency1()
    test_concurrency2()
