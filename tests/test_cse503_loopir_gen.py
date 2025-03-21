from __future__ import annotations

import pytest
from exo import proc
from exo.backend.datarace_analysis import DataRaceDetection

from src.exo.API_cursors import WindowExprCursor


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


def test_basic_branch_unsafe():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            if tid == 0 or tid == 1:
                for i in seq(0, 10):
                    a[i] = 0

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert detector.has_data_race()


def test_basic_branch_safe():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            if tid == 0:
                for i in seq(0, 5):
                    a[i] = 0
            if tid == 1:
                for i in seq(5, 10):
                    a[i] = 1

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_if_else_safe():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            if tid == 0:
                for i in seq(0, 5):
                    a[i] = 0
            else:
                for i in seq(5, 10):
                    a[i] = 1

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_if_else_not_safe():
    @proc
    def foo(a: i8[10]):
        for tid in fork(3):
            if tid == 0:
                for i in seq(0, 5):
                    a[i] = 0
            else:  # tid 1 and 2
                for i in seq(5, 10):
                    a[i] = 1

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert detector.has_data_race()


def test_array_dependent_type_restricts_racey_loop():
    @proc
    def foo(m: size, a: i8[m]):
        assert m == 5
        for tid in fork(3):
            if tid == 0:
                for i in seq(0, m):
                    a[i] = 0
            else:
                for i in seq(6, m):
                    a[i] = 1

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_fork_in_loop_safe():
    @proc
    def foo(a: i8[10]):
        for i in seq(0, 5):
            for tid in fork(2):
                a[2 * i + tid] = 0

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_fork_in_loop_unsafe():
    @proc
    def foo(a: i8[10]):
        for i in seq(0, 5):
            for tid in fork(2):
                a[i] = 0

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert detector.has_data_race()


def test_drb001_yes():
    @proc
    def foo(a: i32[1000]):
        for tid in fork(2):
            for i in seq(0, 499):
                a[i + 500 * tid] = a[i + 499 * tid + 1] + 1
            # boundary
            if tid == 0:
                a[499] = a[500] + 1
            else:
                a[998] = a[999] + 1

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert detector.has_data_race()


def test_drb112_no():
    """

    DRB is testing the linear clause in OMP here, Exo can't really do this
    but this is semantically equivalent
    """

    @proc
    def foo(a: i32[100], b: i32[100], c: i32[100]):
        for tid in fork(2):
            for i in seq(0, 50):
                c[i + tid * 50] += a[i + tid * 50] * b[i + tid * 50]

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


# Barriers
def test_barrier_simple_safe():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            for i in seq(0, 5):
                a[2 * i + tid] = 0
            Barrier()
            a[5 + tid] = 1

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_barrier_simple_unsafe_before():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            for i in seq(0, 5):
                a[2 * i] = 0
            Barrier()
            a[5 + tid] = 1

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert detector.has_data_race()


def test_barrier_simple_unsafe_after():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            for i in seq(0, 5):
                a[2 * i + tid] = 0
            Barrier()
            a[5] = 1

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert detector.has_data_race()


def test_barrier_three_regions_safe():
    @proc
    def foo(a: i8[10]):
        for tid in fork(3):
            a[tid] = 0  # 0, 1, 2
            Barrier()
            a[1 + tid] = 10  # 1, 2, 3
            a[4 + tid] = 100  # 4, 5, 6
            Barrier()
            a[2 * tid] = a[2 * tid + 1]  # writes 0 2 4, reads 1 3 5

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_barrier_three_regions_unsafe():
    @proc
    def foo(a: i8[10]):
        for tid in fork(3):
            a[tid] = 0  # 0, 1, 2
            # Barrier()
            a[1 + tid] = 10  # 1, 2, 3
            a[4 + tid] = 100  # 4, 5, 6
            Barrier()
            a[2 * tid] = a[2 * tid + 1]  # writes 0 2 4, reads 1 3 5

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert detector.has_data_race()


def test_barrier_three_regions_unsafe2():
    @proc
    def foo(a: i8[10]):
        for tid in fork(3):
            a[tid] = 0  # 0, 1, 2
            Barrier()
            a[1 + tid] = 10  # 1, 2, 3
            a[4 + tid] = 100  # 4, 5, 6
            # Barrier()
            a[2 * tid] = a[2 * tid + 1]  # writes 0 2 4, reads 1 3 5

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert detector.has_data_race()


def test_multiple_forks_safe():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            for i in seq(0, 5):
                a[2 * i + tid] = 0
        for tid in fork(2):
            for i in seq(0, 5):
                a[2 * i + tid] = 10

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_multiple_forks_unsafe_first():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            for i in seq(0, 5):
                a[2 * i] = 0
        for tid in fork(2):
            for i in seq(0, 5):
                a[2 * i + tid] = 10

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert detector.has_data_race()


def test_multiple_forks_unsafe_second():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            for i in seq(0, 5):
                a[2 * i + tid] = 0
        for tid in fork(2):
            for i in seq(0, 5):
                a[2 * i] = 10

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


def test_barrier_loop():
    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            a[tid] = 0
            for i in seq(2, 4):
                a[i + 5 * tid] = 1

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_barrier_loop():
    """

    Failing because interior regions not supported yet
    """

    @proc
    def foo(a: i8[10]):
        for tid in fork(2):
            a[tid] = 0
            for i in seq(2, 5):
                Barrier()
                a[2 * i + tid] = 1
                Barrier()
                a[2 * i + tid + 1] = 2

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_single_barrier_in_loop():
    @proc
    def foo(a: i8[1000]):
        for tid in fork(2):
            a[tid] = 0
            for i in seq(2, 10):
                a[i + tid] = 0
                Barrier()

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_drb120_no():
    @proc
    def foo(var: i8[1]):
        var[0] = 0
        for tid in fork(2):
            if tid == 0:
                var[0] += 1
            Barrier()
            if tid == 1:
                var[0] += 1

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_triple_nested():
    @proc
    def foo(var: i8[40000]):
        for tid in fork(2):
            for i in seq(0, 10):
                for j in seq(0, 10):
                    for k in seq(0, 10):
                        var[i + j + k + tid * 100] = 7

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_loop_internal_barrier():
    @proc
    def foo(a: i32[100]):
        for tid in fork(2):
            for i in seq(0, 10):
                a[50 + i + tid] = 0
                Barrier()
                a[i + tid] = 0
                Barrier()

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert not detector.has_data_race()


def test_loop_internal_race():
    @proc
    def foo(a: i32[100]):
        for tid in fork(2):
            for i in seq(0, 10):
                a[50 + i + tid] = 0
                Barrier()
                a[i] = 0
                Barrier()

    detector = DataRaceDetection(foo.INTERNAL_proc())
    assert detector.has_data_race()


# def test_barrier_loop():
#     @proc
#     def foo(a: i8[10]):
#         for tid in fork(2):
#             # a[tid] = 0
#             for i in seq(0, 5):
#                 a[2 * i + tid] = 0
#                 Barrier()
#                 a[2 * i + tid] = 1
#             # a[5 + tid] = 2

#     detector = DataRaceDetection(foo.INTERNAL_proc())
#     assert detector.has_data_race()
