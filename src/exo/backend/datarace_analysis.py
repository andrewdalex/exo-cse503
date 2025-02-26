from collections import ChainMap
from pysmt.shortcuts import *
from pysmt.typing import BV32

from ..core.LoopIR import LoopIR


class DataRaceDetection:
    def __init__(self, proc: LoopIR.proc):
        self.proc = proc
        # name -> access formula (parameterized by program var's symbol
        self.prog_var_to_accesses = {}
        # name -> symbol
        self.prog_var_to_sym = ChainMap()

        # name -> restriction on var
        self.domains = ChainMap()

        self._stmts = proc.body

    def add_access(self, name, access_formula):

        if name in self.prog_var_to_accesses:
            self.prog_var_to_accesses[name] = Or(
                self.prog_var_to_accesses[name], access_formula
            )
        else:
            self.prog_var_to_accesses[name] = access_formula

    def get_or_create_sym_var(self, name):
        if name in self.prog_var_to_sym:
            return self.prog_var_to_sym[name]
        else:
            sym = Symbol(repr(name), BV32)
            self.prog_var_to_sym[name] = sym
            return sym

    @staticmethod
    def get_prog_var_used_in_expr(expr):
        """
        only used for indexing expressions so limited handling
        """
        if isinstance(expr, LoopIR.Read):
            return [expr.name]
        elif isinstance(expr, LoopIR.BinOp):
            return DataRaceDetection.get_prog_var_used_in_expr(
                expr.lhs
            ) + DataRaceDetection.get_prog_var_used_in_expr(expr.rhs)
        else:
            return []

    def domain_formula_from_prog_vars(self, var_list):
        if not var_list:
            return TRUE()
        term = self.domains.get(var_list[0], TRUE())
        for i in range(1, len(var_list)):
            var = var_list[i]
            if var in self.domains:
                term = And(term, self.domains[var_list[i]])
        return term

    def formula_from_expr(self, expr):
        """
        expr assumed to be loop indexing expression so don't have to handle everything,
        typechecker will rule certain things out
        """
        if isinstance(expr, LoopIR.Const):
            # since expr is a loop index expr, should be castable to int
            return BV(expr.val, 32)
        elif isinstance(expr, LoopIR.Read):
            # no indices, this is in loop index
            return self.prog_var_to_sym[expr.name]
        elif isinstance(expr, LoopIR.BinOp):
            lhs_formula = self.formula_from_expr(expr.lhs)
            rhs_formula = self.formula_from_expr(expr.rhs)
            if expr.op == "+":
                return BVAdd(lhs_formula, rhs_formula)
            elif expr.op == "*":
                return BVMul(lhs_formula, rhs_formula)
            elif expr.op == "-":
                return BVSub(lhs_formula, rhs_formula)
            elif expr.op == "/":
                return BVUDiv(lhs_formula, rhs_formula)
            elif expr.op == "%":
                return BVURem(lhs_formula, rhs_formula)
            else:
                assert False and "Bad Case"

        else:
            assert False and "Bad Case"

    def proc_stmts(self, stmts):
        for stmt in stmts:
            if isinstance(stmt, (LoopIR.Reduce, LoopIR.Assign)):
                access_var = self.get_or_create_sym_var(stmt.name)
                if not stmt.idx:
                    formula = Equals(access_var, BV(0, 32))
                    self.add_access(stmt.name, formula)
                elif len(stmt.idx) == 1:
                    formula = self.formula_from_expr(stmt.idx[0])
                    formula = Equals(access_var, formula)
                    ref_vars = DataRaceDetection.get_prog_var_used_in_expr(stmt.idx[0])
                    domain = self.domain_formula_from_prog_vars(ref_vars)
                    self.add_access(stmt.name, And(formula, domain))
            elif isinstance(stmt, LoopIR.Alloc):
                # TODO thread local should figure this out
                pass
            elif isinstance(stmt, LoopIR.For):
                sym_var = self.get_or_create_sym_var(stmt.iter)
                lower = self.formula_from_expr(stmt.lo)
                upper = self.formula_from_expr(stmt.hi)
                self.domains[stmt.iter] = And(
                    BVUGE(sym_var, lower), BVULT(sym_var, upper)
                )
                self.proc_stmts(stmt.body)

    def is_fork_body_safe(self, fork_stmt):
        """
        returns "if fork body is safe"
        """
        if isinstance(fork_stmt.thread_count, LoopIR.Const):
            thread_count = fork_stmt.thread_count.val
        else:
            assert False
        tid = self.get_or_create_sym_var(fork_stmt.tid)

        thread_1 = Symbol("thread_1", BV32)
        thread_2 = Symbol("thread_2", BV32)
        thread_domains = And(
            [
                And(BVUGE(t, BV(0, 32)), BVULT(t, BV(thread_count, 32)))
                for t in [thread_1, thread_2]
            ]
        )
        thread_domains = And(thread_domains, NotEquals(thread_1, thread_2))
        self.proc_stmts(fork_stmt.body)

        access_sym1 = Symbol("idx1", BV32)
        access_sym2 = Symbol("idx2", BV32)
        for k, v in self.prog_var_to_accesses.items():
            access_param = self.prog_var_to_sym[k]
            access_set_1 = v.substitute({tid: thread_1, access_param: access_sym1})

            # need to remap all symbolic values in access set except thread id and the access param
            # to avoid introducing "synchronization" between the sets
            remapped_access_set_2 = DataRaceDetection.remap_free_vars(
                v, [tid, access_param]
            )
            access_set_2 = remapped_access_set_2.substitute(
                {tid: thread_2, access_param: access_sym2}
            )

            f = Equals(access_sym1, access_sym2)
            domains = And([access_set_1, access_set_2, thread_domains])
            model = get_model(And(f, domains))
            print(domains)
            if model:
                print("DataRace!")
                print(model)
                return False
        return True

    @staticmethod
    def remap_free_vars(formula, fixed_vars):
        free_vars = formula.get_free_variables()
        sym_id = 0
        for f in free_vars:
            if f not in fixed_vars:
                formula = formula.substitute({f: Symbol(f"_internal{sym_id}", BV32)})
                sym_id += 1
        return formula

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
