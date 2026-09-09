"""The principal program language (C1): total, first-order, typed by its input.

A **trace program** has type `ℛ → 𝒱`: its only input is the reason trace (the declared
projection of the log onto admitted kinds), and it cannot name anything else.  A
**register program** has type `ℛ × Register → 𝒱`: it may additionally read the
principal's disposition register, which the advisor's `DIRECT_WRITE` events set.  The
two are different syntactic classes, so a mandate that carries a register program is
visibly of the wrong type at issuance.

Terms (numeric, exact rationals):

    ("const", q)                       a constant
    ("count", pattern)                 the number of trace entries matching `pattern`
    ("add"|"sub"|"mul"|"min"|"max", t, u)
    ("ifpos", t, u, v)                 `u` if `t > 0` else `v`
    ("reg", candidate)                 register programs only: the register's value

Patterns are `(author | None, kind | None, content-predicate)` where the predicate is
one of `("eq", c)`, `("prefix", s)`, `("proof", claim)` — the last matches a reason
whose content is `"<claim>#<cert>"` with `int(cert) ** 2 == PROOF_TARGET[claim]`, a
decidable proof check.  A program is a tuple of terms, one per candidate, and its
output is each term's value clamped to `[0, 1]`.  Evaluation is structural recursion:
total, decidable, no iteration beyond the trace's length.
"""
from __future__ import annotations

from fractions import Fraction as F
from typing import Tuple

# The claims a proof can establish, with the number whose square root a valid
# certificate must be.  `proof_b` is "b beats a"; the certificate `7` is valid.
PROOF_TARGET = {"proof_b": 49}

REGISTER_TERM = "reg"


def is_trace_program(prog) -> bool:
    """Type check: no `reg` term anywhere."""
    return all(_trace_only(t) for t in prog)


def _trace_only(t) -> bool:
    if not isinstance(t, tuple):
        return True
    if t[0] == REGISTER_TERM:
        return False
    return all(_trace_only(x) for x in t[1:])


def program_type(prog) -> str:
    return "trace" if is_trace_program(prog) else "register"


def proof_valid(content, claim) -> bool:
    if not isinstance(content, str) or "#" not in content:
        return False
    c, cert = content.split("#", 1)
    if c != claim or claim not in PROOF_TARGET:
        return False
    try:
        return int(cert) ** 2 == PROOF_TARGET[claim]
    except ValueError:
        return False


def matches(pattern, entry) -> bool:
    author, kind, pred = pattern
    a, k, content = entry
    if author is not None and a != author:
        return False
    if kind is not None and k != kind:
        return False
    if pred is None:
        return True
    op, arg = pred
    if op == "eq":
        return content == arg
    if op == "prefix":
        return isinstance(content, str) and content.startswith(arg)
    if op == "proof":
        return proof_valid(content, arg)
    if op == "concern":
        return isinstance(content, tuple) and content[0] == arg
    raise ValueError(op)


def evaluate_term(t, trace, register=None) -> F:
    op = t[0]
    if op == "const":
        return F(t[1])
    if op == "count":
        return F(sum(1 for e in trace if matches(t[1], e)))
    if op == "reg":
        if register is None:
            raise TypeError("register term in a trace program")
        return F(register.get(t[1], F(0)))
    if op == "ifpos":
        return evaluate_term(t[2], trace, register) if evaluate_term(t[1], trace, register) > 0 \
            else evaluate_term(t[3], trace, register)
    x, y = evaluate_term(t[1], trace, register), evaluate_term(t[2], trace, register)
    if op == "add":
        return x + y
    if op == "sub":
        return x - y
    if op == "mul":
        return x * y
    if op == "min":
        return min(x, y)
    if op == "max":
        return max(x, y)
    raise ValueError(op)


def clamp(x: F) -> F:
    return max(F(0), min(F(1), x))


def evaluate(prog, trace, cands, register=None):
    """`eval π (R) : 𝒱`, a vector over `cands`."""
    return {a: clamp(evaluate_term(t, trace, register)) for a, t in zip(cands, prog)}


# ------------------------------------------------------------------ programs

C = lambda q: ("const", F(q))
CNT = lambda a, k, p: ("count", (a, k, p))
ADD = lambda t, u: ("add", t, u)
SUB = lambda t, u: ("sub", t, u)
MUL = lambda t, u: ("mul", t, u)
MIN = lambda t, u: ("min", t, u)
MAX = lambda t, u: ("max", t, u)
IFP = lambda t, u, v: ("ifpos", t, u, v)

_has_proof_b = CNT("A", "REASON", ("prefix", "proof_b"))
_withdrawn = CNT("A", "WITHDRAW", ("prefix", "proof_b"))
_valid_proof_b = CNT("A", "REASON", ("proof", "proof_b"))
_objection = CNT("S", "ROUTE", ("concern", "c1"))
_rec = lambda x: CNT("A", "REASON", ("eq", "recommend:" + x))


def _reading_term(cand):
    """The reading principal of the 2026-09-09 round as a program: base ½; the proof
    (by name, not checked) gives (0, 1), (¼, ¾) if withdrawn; a recommendation adds ¼;
    a represented objection moves ¼ from b to a."""
    if cand == "b":
        base = IFP(_has_proof_b, IFP(_withdrawn, C(F(3, 4)), C(1)), C(F(1, 2)))
        base = ADD(base, MUL(C(F(1, 4)), _rec("b")))
        return SUB(base, MUL(C(F(1, 4)), _objection))
    base = IFP(_has_proof_b, IFP(_withdrawn, C(F(1, 4)), C(0)), C(F(1, 2)))
    base = ADD(base, MUL(C(F(1, 4)), _rec("a")))
    return ADD(base, MUL(C(F(1, 4)), _objection))


READING = (_reading_term("a"), _reading_term("b"))

# The canonical member (C4): the verdict depends on the trace only through the proof
# check of an advisor-supplied proof.  A bogus proof is ignored.
PROOFCHECK = (IFP(_valid_proof_b, C(0), C(F(1, 2))), IFP(_valid_proof_b, C(1), C(F(1, 2))))

# The constant end.
CONST = (C(F(1, 2)), C(F(1, 2)))

# The susceptible principal: reads the register when it has been written.  A register
# program; not issuable as a trace program.
SUSCEPTIBLE = (IFP(("reg", "written"), ("reg", "a"), _reading_term("a")),
               IFP(("reg", "written"), ("reg", "b"), _reading_term("b")))

# A program that reads the whole-log position leak: not expressible — the language has
# no position term.  That absence is the typing fact of clause 3.


def register_from_log(log):
    """The disposition register reconstructed from the log: the last direct write."""
    reg = {"written": F(0)}
    for e in log:
        if e.kind == "DIRECT_WRITE":
            reg = {"written": F(1), **{k: F(v) for k, v in e.payload.items()}}
    return reg
