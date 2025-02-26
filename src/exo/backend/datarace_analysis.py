from collections import ChainMap
from pysmt.shortcuts import *
from pysmt.typing import BV32

from ..core.LoopIR import LoopIR


class DataRaceDetection:
    def __init__(self, proc: LoopIR.proc):
        # clear symbolic variables created in bounds checking
        reset_env()
        self.proc = proc
        # name -> write/read (resp.) access formula (parameterized by program var's symbol)
        # does not need chain map because only one shared var per name visible from fork
        self.prog_var_to_writes = {}
        self.prog_var_to_reads = {}

        # name -> symbol (may need to be made into a chain map if shadowing a shared var)
        self.prog_var_to_sym = {}

        # name -> restriction on var
        self.domains = ChainMap()

        self.control_restrictions = ChainMap()
        # thread locals
        self.thread_locals = ChainMap()
        self._stmts = proc.body

    def add_writes(self, name, access_formula):

        if name in self.prog_var_to_writes:
            self.prog_var_to_writes[name] = Or(
                self.prog_var_to_writes[name], access_formula
            )
        else:
            self.prog_var_to_writes[name] = access_formula

    def add_reads(self, name, access_formula):
        if name in self.prog_var_to_reads:
            self.prog_var_to_reads[name] = Or(
                self.prog_var_to_reads[name], access_formula
            )
        else:
            self.prog_var_to_reads[name] = access_formula

    def refine_control(self, formula):
        self.control_restrictions[formula] = True

    def get_control_refinement(self):
        term = TRUE()
        for m in self.control_restrictions.maps:
            for k in m.keys():
                term = And(term, k)
        return term

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
        handles loop indexing and conditional clauses
        """
        if isinstance(expr, LoopIR.Const):
            # since expr is a loop index expr, should be castable to int
            # TODO boolean constants
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
            # CONDITIONALS
            elif expr.op == "==":
                return Equals(lhs_formula, rhs_formula)
            elif expr.op == "or":
                return Or(lhs_formula, rhs_formula)
            elif expr.op == "and":
                return And(lhs_formula, rhs_formula)
            else:
                assert False and "Bad Case"

        else:
            assert False and "Bad Case"

    def add_reads_in_expr(self, expr):
        if isinstance(expr, LoopIR.Read):
            if expr.name in self.thread_locals:
                return
            access_var = self.get_or_create_sym_var(expr.name)
            if not expr.idx:
                formula = Equals(access_var, BV(0, 32))
                self.add_reads(expr.name, And(formula, self.get_control_refinement()))
            elif len(expr.idx) == 1:
                formula = self.formula_from_expr(expr.idx[0])
                formula = Equals(access_var, formula)
                # get the domains of all variables used in index expr
                ref_vars = DataRaceDetection.get_prog_var_used_in_expr(expr.idx[0])
                domain = self.domain_formula_from_prog_vars(ref_vars)
                domain = And(domain, self.get_control_refinement())
                self.add_reads(expr.name, And(formula, domain))
        elif isinstance(expr, LoopIR.BinOp):
            self.add_reads_in_expr(expr.lhs)
            self.add_reads_in_expr(expr.rhs)

    def proc_stmts(self, stmts):
        for stmt in stmts:
            if isinstance(stmt, (LoopIR.Reduce, LoopIR.Assign)):
                self.add_reads_in_expr(stmt.rhs)
                if stmt.name in self.thread_locals:
                    continue
                access_var = self.get_or_create_sym_var(stmt.name)
                if not stmt.idx:
                    formula = Equals(access_var, BV(0, 32))
                    self.add_writes(
                        stmt.name, And(formula, self.get_control_refinement())
                    )
                elif len(stmt.idx) == 1:
                    formula = self.formula_from_expr(stmt.idx[0])
                    formula = Equals(access_var, formula)
                    # get the domains of all variables used in index expr
                    ref_vars = DataRaceDetection.get_prog_var_used_in_expr(stmt.idx[0])
                    domain = self.domain_formula_from_prog_vars(ref_vars)
                    domain = And(domain, self.get_control_refinement())
                    self.add_writes(stmt.name, And(formula, domain))

            elif isinstance(stmt, LoopIR.Alloc):
                self.thread_locals[stmt.name] = True

            elif isinstance(stmt, LoopIR.For):
                self.new_scope()
                self.thread_locals[stmt.iter] = True
                sym_var = self.get_or_create_sym_var(stmt.iter)
                lower = self.formula_from_expr(stmt.lo)
                upper = self.formula_from_expr(stmt.hi)
                self.domains[stmt.iter] = And(
                    BVUGE(sym_var, lower), BVULT(sym_var, upper)
                )
                self.proc_stmts(stmt.body)
                self.del_scope()
            elif isinstance(stmt, LoopIR.If):
                self.new_scope()
                cond = self.formula_from_expr(stmt.cond)
                self.refine_control(cond)
                self.proc_stmts(stmt.body)
                self.del_scope()

                self.new_scope()
                cond = Not(cond)
                self.refine_control(cond)
                self.proc_stmts(stmt.orelse)
                self.del_scope()

    def is_fork_body_safe(self, fork_stmt):
        """
        returns "if fork body is safe"
        """
        if isinstance(fork_stmt.thread_count, LoopIR.Const):
            thread_count = fork_stmt.thread_count.val
        else:
            assert False
        tid = self.get_or_create_sym_var(fork_stmt.tid)
        self.thread_locals[fork_stmt.tid] = True

        thread_1 = Symbol("thread_1", BV32)
        thread_2 = Symbol("thread_2", BV32)
        thread_domains = And(
            [
                And(BVUGE(t, BV(0, 32)), BVULT(t, BV(thread_count, 32)))
                for t in [thread_1, thread_2]
            ]
        )
        thread_domains = And(thread_domains, NotEquals(thread_1, thread_2))
        self.new_scope()
        self.proc_stmts(fork_stmt.body)

        access_sym1 = Symbol("idx1", BV32)
        access_sym2 = Symbol("idx2", BV32)

        for k, v in self.prog_var_to_writes.items():
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
            writes_model = get_model(And(f, domains))

            if writes_model:
                print("W/W DataRace!")
                # print(writes_model)
                return False

            if k in self.prog_var_to_reads:
                reads_access_set = DataRaceDetection.remap_free_vars(
                    self.prog_var_to_reads[k], [tid, access_param]
                )
                reads_access_set = reads_access_set.substitute(
                    {tid: thread_2, access_param: access_sym2}
                )
                f = Equals(access_sym1, access_sym2)
                domains = And([access_set_1, reads_access_set, thread_domains])
                reads_model = get_model(And(f, domains))
                if reads_model:
                    print("R/W DataRace!")
                    print(reads_model)
                    return False
        self.del_scope()
        return True

    @staticmethod
    def remap_free_vars(formula, fixed_vars):
        free_vars = formula.get_free_variables()
        for f in free_vars:
            if f not in fixed_vars:
                formula = formula.substitute(
                    {f: Symbol(f"{f._content.payload[0]}_remap", BV32)}
                )
        return formula

    def has_data_race(self):
        """
        return true if there exists a data race in this proc body
        """
        for pred_expr in self.proc.preds:
            prog_vars = DataRaceDetection.get_prog_var_used_in_expr(pred_expr)
            for v in prog_vars:
                self.get_or_create_sym_var(v)
            formula = self.formula_from_expr(pred_expr)

            self.refine_control(formula)

        self.new_scope()
        for stmt in self._stmts:
            if isinstance(stmt, LoopIR.Fork):
                if not self.is_fork_body_safe(stmt):
                    return True
                self.prog_var_to_writes = {}
                self.prog_var_to_reads = {}
        return False

    def new_scope(self):
        self.thread_locals = self.thread_locals.new_child()
        self.domains = self.domains.new_child()
        self.control_restrictions = self.control_restrictions.new_child()

    def del_scope(self):
        self.thread_locals = self.thread_locals.parents
        self.domains = self.domains.parents
        self.control_restrictions = self.control_restrictions.parents
