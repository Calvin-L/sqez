#!/usr/bin/env python3

import threading
import os
from pathlib import PurePath
import logging
import time

import sqez
from test_basics import par

_logger = logging.getLogger(__name__)

CONNECTIONS = 2
WRITERS_PER_CONNECTION = 2
READERS_PER_CONNECTION = 2
DB_FILE = PurePath(os.path.abspath(__file__)).parent / "test_strict_serializability.sqlite"

class SharedState:
    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._running = True
        self._underestimate = 0
        self._overestimate = 0

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
    try:
        os.unlink(DB_FILE)
    except FileNotFoundError:
        pass

    with sqez.Connection(DB_FILE) as conn:
        with sqez.WriteTransaction(conn) as tx:
            tx.exec("CREATE TABLE counter (value INT)")
            tx.exec("INSERT INTO counter (value) VALUES (0)")

    st = SharedState()

    par(*([lambda: one_conn(st)] * CONNECTIONS + [lambda: stop(st)]))

    with sqez.Connection(DB_FILE) as conn:
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
        with sqez.Connection(DB_FILE) as conn:
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
