from __future__ import annotations

import pytest
from exo import proc
from exo.backend.datarace_analysis import DataRaceDetection


def test_basic_parsing():
    @proc
    def foo(a: i8):
        b: i8
        b = 0
        for tid in fork(2):
            a = b
            Barrier()

    # will fail if can't parse


def test_detect_trivial_dr():
    @proc
    def foo(a: i8):
        b: i8
        b = 0
        for tid in fork(2):
            a = b

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert detector.has_data_race()


def test_verifies_trivial_safe():
    @proc
    def foo(a: i8[2]):
        b: i8
        b = 0
        for tid in fork(2):
            a[tid] = b

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()
