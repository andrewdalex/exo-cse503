from __future__ import annotations

import pytest
from exo import proc


def test_basic_parsing():
    @proc
    def foo(a: i8):
        b: i8
        b = 0
        for tid in fork(2):
            a += b
            Barrier()
