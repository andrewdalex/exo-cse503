from collections import ChainMap
from pysmt.shortcuts import (
    Symbol,
    And,
    BVUGE,
    BVULT,
    Equals,
    Int,
    NotEquals,
    TRUE,
    get_model,
    BV,
)
from pysmt.typing import BV32

from ..core.LoopIR import LoopIR


class DataRaceDetection:
    def __init__(self, proc: LoopIR.proc):
        self.proc = proc
        self.prog_to_accesses = {}
        # name -> symbol
        self.prog_var_to_sym = ChainMap()

        self._stmts = proc.body

    def add_access(self, name, access_formula):
        if name in self.prog_to_accesses:
            self.prog_to_accesses[name] = And(
                self.prog_to_accesses[name], access_formula
            )
        else:
            self.prog_to_accesses[name] = access_formula

    def add_sym_var(self, name):
        # todo just assuming we only do this for int vars now
        self.prog_var_to_sym[name] = Symbol(repr(name), BV32)

    def get_sym_var(self, name):
        return self.prog_var_to_sym[name]

    def formula_from_expr(self, expr):
        """
        expr assumed to be loop indexing expression so don't have to handle everything,
        typechecker will rule certain things out
        """
        if isinstance(expr, LoopIR.Const):
            # since expr is a loop index expr, should be castable to int
            return Int(expr.val)
        elif isinstance(expr, LoopIR.Read):
            # no indices, this is in loop index
            return self.get_sym_var(expr.name)
        else:
            assert False and "Bad Case"

    def is_fork_body_safe(self, fork_stmt):
        """
        returns "if fork body is safe"
        """
        if isinstance(fork_stmt.thread_count, LoopIR.Const):
            thread_count = fork_stmt.thread_count.val
        else:
            assert False
        self.add_sym_var(fork_stmt.tid)

        thread_1 = Symbol("thread_1", BV32)
        thread_2 = Symbol("thread_2", BV32)
        domains = And(
            [
                And(BVUGE(t, BV(0, 32)), BVULT(t, BV(thread_count, 32)))
                for t in [thread_1, thread_2]
            ]
        )
        domains = And(domains, NotEquals(thread_1, thread_2))

        thread_local = []
        for stmt in fork_stmt.body:
            if isinstance(stmt, (LoopIR.Reduce, LoopIR.Assign)):
                if stmt.name in thread_local:
                    continue
                if not stmt.idx:
                    self.add_access(stmt.name, BV(0, 32))
                elif len(stmt.idx) == 1:
                    self.add_access(stmt.name, self.formula_from_expr(stmt.idx[0]))
            elif isinstance(stmt, LoopIR.Alloc):
                # TODO add to thread local vars list, don't verify on
                pass

        tid = self.get_sym_var(fork_stmt.tid)
        for k, v in self.prog_to_accesses.items():
            f = Equals(v.substitute({tid: thread_1}), v.substitute({tid: thread_2}))
            f = And(domains, f)
            model = get_model(f)
            if model:
                print("DataRace!")
                print(model)
                return False
        return True

    def has_data_race(self):
        """
        return true if there exists a data race in this proc body
        """
        for stmt in self._stmts:
            if isinstance(stmt, LoopIR.Fork):
                if not self.is_fork_body_safe(stmt):
                    return True
        return False

    def new_scope(self):
        self.prog_var_to_sym = self.prog_var_to_sym.new_child()

    def del_scope(self):
        self.prog_var_to_sym = self.prog_var_to_sym.parents
