#!/usr/bin/env python3

import threading
import os
from pathlib import PurePath
import logging
import time
import tempfile

import sqez
from test_basics import par

_logger = logging.getLogger(__name__)

CONNECTIONS = 2
WRITERS_PER_CONNECTION = 2
READERS_PER_CONNECTION = 2

class SharedState:
    def __init__(self, db_file: PurePath) -> None:
        self._db_file = db_file
        self._lock = threading.Lock()
        self._running = True
        self._underestimate = 0
        self._overestimate = 0

    @property
    def db_file(self) -> PurePath:
        return self._db_file

    @property
    def running(self) -> bool:
        with self._lock:
            return self._running

    def stop(self) -> None:
        with self._lock:
            self._running = False

    @property
    def underestimate(self) -> int:
        with self._lock:
            return self._underestimate

    @property
    def overestimate(self) -> int:
        with self._lock:
            return self._overestimate

    def update_underestimate(self, val: int) -> None:
        with self._lock:
            self._underestimate = max(self._underestimate, val)

    def update_overestimate(self, val: int) -> None:
        with self._lock:
            self._overestimate = max(self._overestimate, val)

def test_strict_serializability() -> None:
    with tempfile.TemporaryDirectory() as d:
        db_file = PurePath(d) / "db.sqlite"

        with sqez.Connection(db_file) as conn:
            with sqez.WriteTransaction(conn) as tx:
                tx.exec("CREATE TABLE counter (value INT)")
                tx.exec("INSERT INTO counter (value) VALUES (0)")

        st = SharedState(db_file)

        par(*([lambda: one_conn(st)] * CONNECTIONS + [lambda: stop(st)]))

        with sqez.Connection(db_file) as conn:
            with sqez.ReadTransaction(conn) as tx:
                (val,), = tx.select("SELECT value FROM counter")

    print(f"Underestimate: {st.underestimate}")
    print(f"Value: {val}")
    print(f"Overestimate: {st.overestimate}")
    assert st.underestimate == val and val == st.overestimate
    assert val > 0

def stop(st: SharedState) -> None:
    time.sleep(5)
    st.stop()

def one_conn(st: SharedState) -> None:
    try:
        with sqez.Connection(st.db_file) as conn:
            par(*([lambda: reader(st, conn)] * CONNECTIONS + [lambda: writer(st, conn)] * CONNECTIONS))
    except:
        st.stop()
        _logger.exception("one_conn")

def reader(st: SharedState, conn: sqez.Connection) -> None:
    try:
        while st.running:
            lo = st.underestimate
            with sqez.ReadTransaction(conn) as tx:
                (val,), = tx.select("SELECT value FROM counter")
            hi = st.overestimate
            assert lo <= val <= hi
    except:
        st.stop()
        _logger.exception("reader")

def writer(st: SharedState, conn: sqez.Connection) -> None:
    try:
        while st.running:
            with sqez.WriteTransaction(conn) as tx:
                (current,), = tx.select("SELECT value FROM counter")
                st.update_overestimate(current + 1)
                tx.exec("UPDATE counter SET value=?", (current + 1,))
            st.update_underestimate(current + 1)
    except:
        st.stop()
        _logger.exception("writer")

def test_rwr() -> None:
    """
    Test this scenario:

             Connection     Connection
                  1              2
             __________        ____
            |          |      |    |
              R1    R2          W1
        --------------------------------
        1.  begin
        2.                     begin
        3.                     write
        4.                     commit
        5.         begin
        6.         read

    R2 must observe the effect of W1.
    """
    with tempfile.TemporaryDirectory() as d:
        with sqez.Connection(PurePath(d) / "db.sqlite") as c1:
            with sqez.WriteTransaction(c1) as tx:
                tx.exec("CREATE TABLE counter (value INT)")
                tx.exec("INSERT INTO counter (value) VALUES (0)")

            with sqez.Connection(PurePath(d) / "db.sqlite") as c2:
                with sqez.ReadTransaction(c1) as tx1:
                    (val1,), = tx1.select("SELECT value FROM counter")

                    with sqez.WriteTransaction(c2) as w:
                        w.exec("UPDATE counter SET value=1")

                    def close_tx1() -> None:
                        try:
                            time.sleep(2)
                        finally:
                            tx1.close()

                    t = threading.Thread(target=close_tx1)
                    t.start()

                    # Previously there was a bug where tx2 would "piggyback" on
                    # the already-open transaction tx1 on c2.  But, for strict
                    # serializability, tx2 must open a new transaction so that
                    # it sees w's effects.
                    with sqez.ReadTransaction(c1) as tx2:
                        (val2,), = tx2.select("SELECT value FROM counter")

                    t.join()

                assert val1 == 0
                assert val2 == 1
