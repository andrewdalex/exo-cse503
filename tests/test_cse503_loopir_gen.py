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
        for tid in fork(2):
            a = 0

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert detector.has_data_race()


def test_verifies_trivial_safe():
    @proc
    def foo(a: i8[2]):
        for tid in fork(2):
            a[tid] = 0

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_verifies_trivial_loop_unsafe():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            for i in seq(0, 5):
                a[i] = 0

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert detector.has_data_race()


def test_verifies_loop_split_zero_copy_safe():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            for i in seq(0, 5):
                a[i + 5 * tid] = 0

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_verifies_overlapping_zero_copy_unsafe():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            for i in seq(0, 5):
                a[i + tid] = 0

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert detector.has_data_race()


def test_reads_overlap_writes():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            for i in seq(0, 5):
                a[i + 5 * tid] = a[i]

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert detector.has_data_race()


def test_reads_not_overlap_writes():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            for i in seq(0, 4):
                a[i + 5 * tid] = a[9]

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_thread_local_ok():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            sum: i8
            sum = 0
            for i in seq(0, 5):
                sum += a[i + 5 * tid]

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()
