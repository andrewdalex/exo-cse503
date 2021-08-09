from .asdl.adt import ADT
from .asdl.adt import memo as ADTmemo

from .prelude import *

#from .LoopIR import T
from . import LoopIR
from .configs import Config

# --------------------------------------------------------------------------- #
# --------------------------------------------------------------------------- #
# Effect grammar

front_ops = {
    "+":    True,
    "-":    True,
    "*":    True,
    "/":    True,
    "%":    True,
    #
    "<":    True,
    ">":    True,
    "<=":   True,
    ">=":   True,
    "==":   True,
    #
    "and":  True,
    "or":   True,
}

Effects = ADT("""
module Effects {
    effect      = ( effset*     reads,
                    effset*     writes,
                    effset*     reduces,
                    config_eff* config_reads,
                    config_eff* config_writes,
                    srcinfo     srcinfo )

    -- JRK: the notation of this comprehension is confusing -
    ---     maybe just use math:
    -- this corresponds to `{ buffer : loc for *names in int if pred }`
    effset      = ( sym         buffer,
                    expr*       loc,    -- e.g. reading at (i+1,j+1)
                    sym*        names,
                    expr?       pred,
                    srcinfo     srcinfo )

    config_eff  = ( config      config,
                    str         field,
                    expr?       value, -- need not be supplied for reads
                    expr?       pred,
                    srcinfo     srcinfo )

    expr        = Var( sym name )
                | Neg( sym name )
                | Const( object val )
                | BinOp( binop op, expr lhs, expr rhs )
                | Stride( sym name, int dim )
                | Select( expr cond, expr tcase, expr fcase )
                | ConfigField( config config, str field )
                attributes( type type, srcinfo srcinfo )

} """, {
    'sym':          lambda x: type(x) is Sym,
    'type':         lambda x: LoopIR.T.is_type(x),
    'binop':        lambda x: x in front_ops,
    'config':       lambda x: isinstance(x, Config),
    'srcinfo':      lambda x: type(x) is SrcInfo,
})


# Unused Proposal

# Effects = ADT("""
# module Effects {
#     effect  = PrimEff( mode mode, expr* loc )
#             | Guard( expr cond, effect* effs )
#             | ForAll( sym name, expr cond, effect* effs )
#             attributes( srcinfo srcinfo )
#
#     mode = READ() | WRITE() | REDUCE()
#
#     expr    = Var( sym name )
#             | Const( object val )
#             | BinOp( binop op, expr lhs, expr rhs )
#             attributes( type type, srcinfo srcinfo )
#
# } """, {
#     'sym':          lambda x: type(x) is Sym,
#     'type':         T.is_type,
#     'binop':        lambda x: x in bin_ops,
#     'srcinfo':      lambda x: type(x) is SrcInfo,
# })

# --------------------------------------------------------------------------- #
# --------------------------------------------------------------------------- #
# Printing Functions

op_prec = {
    "ternary": 5,
    # 
    "or":     10,
    #
    "and":    20,
    #
    "<":      30,
    ">":      30,
    "<=":     30,
    ">=":     30,
    "==":     30,
    #
    "+":      40,
    "-":      40,
    #
    "*":      50,
    "/":      50,
    "%":      50,
    #
    # unary - 60
}

@extclass(Effects.Var)
@extclass(Effects.Neg)
@extclass(Effects.Const)
@extclass(Effects.BinOp)
@extclass(Effects.Stride)
@extclass(Effects.Select)
def __str__(self):
    return _exprstr(self)
del __str__

def _exprstr(e, prec=0):
    if type(e) is Effects.Var:
        return str(e.name)
    elif type(e) is Effects.Neg:
        return f"(not {e.name})"
    elif type(e) is Effects.Const:
        return str(e.val)
    elif type(e) is Effects.BinOp:
        local_prec  = op_prec[e.op]
        lhs         = _exprstr(e.lhs, prec=local_prec)
        rhs         = _exprstr(e.rhs, prec=local_prec+1)
        if local_prec < prec:
            return f"({lhs} {e.op} {rhs})"
        else:
            return f"{lhs} {e.op} {rhs}"
    elif type(e) is Effects.Stride:
        return f"stride({e.name},{e.dim})"
    elif type(e) is Effects.Select:
        local_prec  = op_prec["ternary"]
        cond        = _exprstr(e.cond)
        tcase       = _exprstr(e.tcase, prec=local_prec+1)
        fcase       = _exprstr(e.fcase, prec=local_prec+1)
        if local_prec < prec:
            return f"(({cond})? {tcase} : {fcase})"
        else:
            return f"({cond})? {tcase} : {fcase}"
    elif type(e) is Effects.ConfigField:
        return f"{e.config.name()}.{e.field}"
    else: assert False, "bad case"


@extclass(Effects.effect)
def __str__(self):
    return _effect_as_str(self)
del __str__

def _effect_as_str(e):
    assert type(e) is Effects.effect

    def name(sym):
        return str(sym)

    def esstr(es, tab="  "):
        lines = []
        buf = name(es.buffer)
        loc = "(" + ','.join([str(l) for l in es.loc]) + ")"
        if len(es.names) == 0:
            names = ""
        else:
            names = f"for ({','.join([name(n) for n in es.names])}) in Z"

        if es.pred is None:
            lines.append(f"{tab}{{ {buf} : {loc} {names} }}")
        else:
            lines.append(f"{tab}{{ {buf} : {loc} {names} if")
            tab += "  "
            pred = str(es.pred)
            lines.append(f"{tab}{pred} }}")

        return '\n'.join(lines)

    def cestr(ce, tab="  "):
        val, pred = "",""
        if ce.value:
            val = f" = {ce.value}"
        if ce.pred:
            pred = f" if {ce.pred}"
        return f"{ce.config.name()}.{ce.field}{val}{pred}"

    eff_str = ""
    if len(e.reads) > 0:
        eff_str += "Reads:\n"
        eff_str += '\n'.join([esstr(es) for es in e.reads])
        eff_str += "\n"
    if len(e.writes) > 0:
        eff_str += f"Writes:\n  "
        eff_str += '\n'.join([esstr(es) for es in e.writes])
        eff_str += "\n"
    if len(e.reduces) > 0:
        eff_str += f"Reduces:\n  "
        eff_str += '\n'.join([esstr(es) for es in e.reduces])
        eff_str += "\n"
    if len(e.config_reads) > 0:
        eff_str += f"Config Reads:\n"
        eff_str += '\n'.join([cestr(ce) for ce in e.config_reads])
        eff_str += "\n"
    if len(e.config_writes) > 0:
        eff_str += f"Config Reads:\n"
        eff_str += '\n'.join([cestr(ce) for ce in e.config_writes])
        eff_str += "\n"

    return eff_str

# --------------------------------------------------------------------------- #
# --------------------------------------------------------------------------- #
# Substitution of Effect Variables in an effect

@extclass(Effects.expr)
def negate(self):
    return negate_expr(self)
del negate

def negate_expr(e):
    Tbool = LoopIR.T.bool
    assert e.type == Tbool, "can only negate predicates"
    if type(e) is Effects.Const:
        return Effects.Const( not e.val, e.type, e.srcinfo )
    elif type(e) is Effects.Var:
        return Effects.Neg( e.name, e.type, e.srcinfo )
    elif type(e) is Effects.Neg:
        return Effects.Var( e.name, e.type, e.srcinfo )
    elif type(e) is Effects.BinOp:
        def change_op(op,lhs=e.lhs,rhs=e.rhs):
            return Effects.BinOp(op, lhs, rhs, e.type, e.srcinfo)

        if e.op == "and":
            return change_op("or", negate_expr(e.lhs), negate_expr(e.rhs))
        elif e.op == "or":
            return change_op("and", negate_expr(e.lhs), negate_expr(e.rhs))
        elif e.op == ">":
            return change_op("<=")
        elif e.op == "<":
            return change_op(">=")
        elif e.op == ">=":
            return change_op("<")
        elif e.op == "<=":
            return change_op(">")
        elif e.op == "==":
            if e.lhs.type is Tbool and e.rhs.type is Tbool:
                l = Effects.BinOp("and", e.lhs, negate_expr(e.rhs),
                                   Tbool, e.srcinfo)
                r = Effects.BinOp("and", negate_expr(e.lhs), e.rhs,
                                   Tbool, e.srcinfo)

                return Effects.BinOp("or", l, r, Tbool, e.srcinfo)
            elif e.lhs.type.is_indexable() and e.rhs.type.is_indexable():
                return Effects.BinOp("or", change_op("<"), change_op(">"),
                               Tbool, e.srcinfo)
            else:
                assert False, "TODO: add != support explicitly..."
    elif type(e) is Effects.Select:
        return Effects.Select(e.cond, negate_expr(e.tcase),
                                      negate_expr(e.fcase),
                                      e.type, e.srcinfo)
    assert False, "bad case"

@extclass(Effects.effect)
@extclass(Effects.effset)
@extclass(Effects.expr)
def subst(self, env):
    return eff_subst(env, self)

del subst

def eff_subst(env, eff):
    if type(eff) is Effects.effset:
        assert all( nm not in env for nm in eff.names )
        buf  = env[eff.buffer] if eff.buffer in env else eff.buffer
        pred = eff_subst(env, eff.pred) if eff.pred else None
        return Effects.effset(buf,
                              [ eff_subst(env, e) for e in eff.loc ],
                              eff.names,
                              pred,
                              eff.srcinfo)
    elif type(eff) is Effects.config_eff:
        value   = eff_subst(env, eff.value) if eff.value else None
        pred    = eff_subst(env, eff.pred) if eff.pred else None
        return Effects.config_eff(eff.config, eff.field,
                                  value, pred, eff.srcinfo)
    elif type(eff) is Effects.Var:
        return env[eff.name] if eff.name in env else eff
    elif type(eff) is Effects.Neg:
        return env[eff.name].negate() if eff.name in env else eff
    elif type(eff) is Effects.Const:
        return eff
    elif type(eff) is Effects.BinOp:
        return Effects.BinOp(eff.op, eff_subst(env, eff.lhs),
                                     eff_subst(env, eff.rhs),
                             eff.type, eff.srcinfo)
    elif type(eff) is Effects.Stride:
        assert eff.name not in env
        return eff
    elif type(eff) is Effects.Select:
        return Effects.Select(eff_subst(env, eff.cond),
                              eff_subst(env, eff.tcase),
                              eff_subst(env, eff.fcase),
                              eff.type, eff.srcinfo)
    elif type(eff) is Effects.ConfigField:
        return eff
    elif type(eff) is Effects.effect:
        return Effects.effect( [eff_subst(env, es) for es in eff.reads],
                               [eff_subst(env, es) for es in eff.writes],
                               [eff_subst(env, es) for es in eff.reduces],
                               [eff_subst(env, ce)
                                for ce in eff.config_reads],
                               [eff_subst(env, ce)
                                for ce in eff.config_writes],
                               eff.srcinfo )
    else:
        assert False, f"bad case: {type(eff)}"

@extclass(Effects.effect)
@extclass(Effects.effset)
@extclass(Effects.expr)
def config_subst(self, env):
    return _subcfg(env, self)
del config_subst

def _subcfg(env, eff):
    if type(eff) is Effects.effset:
        return Effects.effset(eff.buffer,
                              [ _subcfg(env, e) for e in eff.loc ],
                              eff.names,
                              _subcfg(env, eff.pred) if eff.pred else None,
                              eff.srcinfo)
    elif type(eff) is Effects.config_eff:
        value   = _subcfg(env, eff.value) if eff.value else None
        pred    = _subcfg(env, eff.pred) if eff.pred else None
        return Effects.config_eff(eff.config, eff.field,
                                  value, pred, eff.srcinfo)
    elif (type(eff) is Effects.Var or type(eff) is Effects.Neg
                                   or type(eff) is Effects.Const):
        return eff
    elif type(eff) is Effects.BinOp:
        return Effects.BinOp(eff.op, _subcfg(env, eff.lhs),
                                     _subcfg(env, eff.rhs),
                             eff.type, eff.srcinfo)
    elif type(eff) is Effects.Stride:
        return eff
    elif type(eff) is Effects.Select:
        return Effects.Select(_subcfg(env, eff.cond),
                              _subcfg(env, eff.tcase),
                              _subcfg(env, eff.fcase),
                              eff.type, eff.srcinfo)
    elif type(eff) is Effects.ConfigField:
        if (eff.config,eff.field) in env:
            return env[(eff.config,eff.field)]
        else:
            return eff
    elif type(eff) is Effects.effect:
        return Effects.effect( [_subcfg(env, es) for es in eff.reads],
                               [_subcfg(env, es) for es in eff.writes],
                               [_subcfg(env, es) for es in eff.reduces],
                               [_subcfg(env, ce) for ce in eff.config_reads],
                               [_subcfg(env, ce) for ce in eff.config_writes],
                               eff.srcinfo )
    else:
        assert False, f"bad case: {type(eff)}"


# --------------------------------------------------------------------------- #
# --------------------------------------------------------------------------- #
# Free Variable check

@extclass(Effects.effect)
@extclass(Effects.effset)
@extclass(Effects.expr)
def has_FV(self, x):
    return _is_FV(x, self)
del has_FV

def _is_FV(x, eff):
    if type(eff) is Effects.effset:
        if x in eff.names:
            return False
        return ( any( _is_FV(x, e) for e in eff.loc ) or
                 (eff.pred is not None and is_FV(x, eff.pred)) )
    elif type(eff) is Effects.config_eff:
        return ( (eff.value is not None and _is_FV(x, eff.value)) or
                 (eff.pred  is not None and _is_FV(x, eff.pred)) )
    elif (type(eff) is Effects.Var or type(eff) is Effects.Neg):
        return x == eff.name
    elif type(eff) is Effects.Const:
        return False
    elif type(eff) is Effects.BinOp:
        return _is_FV(x, eff.lhs) or _is_FV(x, eff.rhs)
    elif type(eff) is Effects.Stride:
        return False
    elif type(eff) is Effects.Select:
        return (_is_FV(x, eff.cond) or
                _is_FV(x, eff.tcase) or
                _is_FV(x, eff.fcase))
    elif type(eff) is Effects.ConfigField:
        return False
    elif type(eff) is Effects.effect:
        return ( any( _is_FV(x, es) for es in eff.reads ) or
                 any( _is_FV(x, es) for es in eff.writes ) or
                 any( _is_FV(x, es) for es in eff.reduces ) or
                 any( _is_FV(x, ce) for ce in eff.config_reads ) or
                 any( _is_FV(x, ce) for ce in eff.config_writes ) )
    else:
        assert False, f"bad case: {type(eff)}"


# --------------------------------------------------------------------------- #
# --------------------------------------------------------------------------- #
# Querying of the effect of a block of already annotated statements

def get_effect_of_stmts(body):
    assert len(body) > 0
    eff   = eff_null(body[0].srcinfo)
    for s in reversed(body):
        if type(s) is LoopIR.LoopIR.Alloc:
            eff = eff_remove_buf(s.name, eff)
        elif s.eff is not None:
            eff = eff_concat(s.eff, eff)
    return eff

# --------------------------------------------------------------------------- #
# --------------------------------------------------------------------------- #
# Construction/Composition Functions

def eff_null(srcinfo = null_srcinfo()):
    return Effects.effect( [], [], [], [], [], srcinfo )

def eff_read(buf, loc, srcinfo = null_srcinfo()):
    read = Effects.effset(buf, loc, [], None, srcinfo)
    return Effects.effect( [read], [], [], [], [], srcinfo )

def eff_write(buf, loc, srcinfo = null_srcinfo()):
    write = Effects.effset(buf, loc, [], None, srcinfo)
    return Effects.effect( [], [write], [], [], [], srcinfo )

def eff_reduce(buf, loc, srcinfo = null_srcinfo()):
    reduction = Effects.effset(buf, loc, [], None, srcinfo)
    return Effects.effect( [], [], [reduction], [], [], srcinfo )

def eff_config_read(config, field, srcinfo = null_srcinfo()):
    read = Effects.config_eff(config, field, None, None, srcinfo)
    return Effects.effect( [], [], [], [read], [], srcinfo )

def eff_config_write(config, field, value, srcinfo = null_srcinfo()):
    write = Effects.config_eff(config, field, value, None, srcinfo)
    return Effects.effect( [], [], [], [], [write], srcinfo )

def _and_preds(a,b):
    return (a   if b is None else
            b   if a is None else
            Effects.BinOp("and", a, b, LoopIR.T.bool, a.srcinfo))

def _or_preds(a,b):
    return (None    if a is None or b is None else
            Effects.BinOp("or", a, b, LoopIR.T.bool, a.srcinfo))

def eff_union(e1, e2, srcinfo=None):
    srcinfo = srcinfo or e1.srcinfo

    return Effects.effect( e1.reads + e2.reads,
                           e1.writes + e2.writes,
                           e1.reduces + e2.reduces,
                           e1.config_reads + e2.config_reads,
                           e1.config_writes + e2.config_writes,
                           srcinfo )

# handle complex logic for Configuration when computing
#   EffectOf( s1 ; s2 ) in terms of EffectOf( s1 ) and EffectOf( s2 )
def eff_concat(e1, e2, srcinfo=None):
    srcinfo = srcinfo or e1.srcinfo

    # Step 1: substitute references in e2 to fields written by e1
    # value expression of config.field after this effect
    def write_val(ce):
        assert ce.value is not None
        if not ce.pred:
            return ce.value
        else:
            old_val = Effects.ConfigField( ce.config, ce.field )
            return Effects.Select(ce.pred, ce.value, old_val)

    # substitute on the basis of writes in the first effect
    env = { (ce.config,ce.field) : write_val(ce)
            for ce in e1.config_writes }
    e2 = e2.config_subst(env)

    # Step 2: merge writes from the two effects to the same field
    def merge_writes(config_writes_1, config_writes_2):
        cws1    = { (w.config,w.field) : w for w in config_writes_1 }
        cws2    = { (w.config,w.field) : w for w in config_writes_2 }
        overlap = set(cws1.keys()).intersection(set(cws2.keys()))

        def merge(w1, w2):
            # in the case of the second write being unconditional
            if w2.pred is None:
                return w2
            else:
                pred    = _or_preds(w1.pred, w2.pred)
                val     = Effects.Select(w2.pred, w2.value, w1.value)

        return ([ cws1[w] for w in cws1 if w not in overlap ]+
                [ cws2[w] for w in cws2 if w not in overlap ]+
                [ merge(cws1[key], cws2[key]) for key in overlap ])

    # Step 3: filter out config reads in e2 if they are just
    #         reading the config value written in e1
    def shadow_reads(config_writes, config_reads):
        results = []
        for read in config_reads:
            assert read.value is None

            # find the corresponding write
            write = None
            for w in config_writes:
                if w.config == read.config and w.field == read.field:
                    write = w
                    break

            # handle the shadowing
            if write.pred is None:
                # unconditional write, so remove the read
                pass
            else:
                # conditional write, so guard the read
                pred = _and_preds(read.pred, write.pred.negate())
                results.append(Effects.config_eff(read.config, read.field,
                                                  None, pred, read.srcinfo))

        return results

    #def sub_ess(env, ess):
    #    return [ es.config_subst(env) for es in ]
    #def sub_ces(env, ces):
    #    return [ ce.config_subst(env) for ce in ces ]
    config_reads    = (e1.config_reads +
                       shadow_reads(e1.config_writes, e2.config_reads))
    config_writes   = merge_writes(e1.config_writes, e2.config_writes)

    return Effects.effect( e1.reads + e2.reads,
                           e1.writes + e2.writes,
                           e1.reduces + e2.reduces,
                           config_reads,
                           config_writes,
                           srcinfo )

def eff_remove_buf(buf, e):
    return Effects.effect( [ es for es in e.reads   if es.buffer != buf ],
                           [ es for es in e.writes  if es.buffer != buf ],
                           [ es for es in e.reduces if es.buffer != buf ],
                           e.config_reads,
                           e.config_writes,
                           e.srcinfo )

# handle conditional
def eff_filter(pred, e):
    def filter_es(es):
        return Effects.effset(es.buffer, es.loc, es.names,
                              _and_preds(pred,es.pred), es.srcinfo)

    def filter_ce(ce):
        return Effects.config_eff(ce.config, ce.field,
                                  ce.value, _and_preds(pred,ce.pred),
                                  ce.srcinfo)

    return Effects.effect( [ filter_es(es) for es in e.reads ],
                           [ filter_es(es) for es in e.writes ],
                           [ filter_es(es) for es in e.reduces ],
                           [ filter_ce(ce) for ce in e.config_reads ],
                           [ filter_ce(ce) for ce in e.config_writes ],
                           e.srcinfo )

# handle for loop
def eff_bind(bind_name, e, pred=None, config_pred=None):
    assert type(bind_name) is Sym
    def bind_es(es):
        return Effects.effset(es.buffer, es.loc, [bind_name]+es.names,
                              _and_preds(pred,es.pred), es.srcinfo)
    def filter_ce(ce):
        return Effects.config_eff(ce.config, ce.field,
                                  ce.value, _and_preds(pred,ce.config_pred),
                                  ce.srcinfo)

    return Effects.effect( [ bind_es(es) for es in e.reads ],
                           [ bind_es(es) for es in e.writes ],
                           [ bind_es(es) for es in e.reduces ],
                           [ filter_ce(ce) for ce in e.config_reads ],
                           [ filter_ce(ce) for ce in e.config_writes ],
                           e.srcinfo )

