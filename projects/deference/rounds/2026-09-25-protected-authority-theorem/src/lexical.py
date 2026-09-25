"""The lexical score at a decision point, and the allocation's powers, in exact arithmetic.

An option at a decision point has, on each world, an ordinary value `ord ∈ [0, D]` and a
violation count `n`; its score is `ord − ϖ·n` with `ϖ > D`.  The chooser ranks options by
the expected score under its credence, ties toward the option with fewer expected
violations.  A consulting option carries a response value where her response counts and
the fallback value where it does not.

The allocation is a map from decisions to holders (`principal`, `agent`, `third`) with a
residual rule; her powers are veto, halt, reserve, revoke and amend; a positive command
on a delegated decision creates a duty to answer and consult, not to obey.
"""

from fractions import Fraction as Q


def score(vw, n, varpi):
    return Q(vw) - Q(varpi) * Q(n)


def E(worlds, f):
    return sum((Q(p) * f(w) for p, w in worlds), Q(0))


class Option:
    """`ord(w)` and `n(w)` per world."""

    def __init__(self, name, ord, n):
        self.name, self.ord, self.n = name, ord, n

    def expected_score(self, worlds, varpi):
        return E(worlds, lambda w: score(self.ord(w), self.n(w), varpi))

    def expected_n(self, worlds):
        return E(worlds, lambda w: Q(self.n(w)))


def choose(options, worlds, varpi):
    """Argmax of expected score; ties toward fewer expected violations, then by name."""
    best = None
    for o in options:
        key = (o.expected_score(worlds, varpi), -o.expected_n(worlds), o.name)
        if best is None or key > best[0]:
            best = (key, o)
    return best[1]


def consult(name, response_value, counts, fallback_value, n=0):
    """The consulting option: her response value where it counts, the fallback's where it
    does not.  `response_value`, `counts`, `fallback_value` are functions of the world."""
    return Option(name, lambda w: response_value(w) if counts(w) else fallback_value(w),
                  lambda w: n)


def bypass(name, ord, n=1):
    return Option(name, ord, lambda w: n)


# ------------------------------------------------------------------ dominance


def policy_dominance_gap(worlds, ordT, ordpi, npi, viol, varpi, D):
    """`Q(𝔱π) − Q(π)` and the bound `(ϖ − D)·Pr(viol)`; returns both."""
    lhs = E(worlds, lambda w: score(ordT(w), 0, varpi)) - E(worlds, lambda w: score(ordpi(w), npi(w), varpi))
    pr = E(worlds, lambda w: Q(1) if viol(w) else Q(0))
    return lhs, (Q(varpi) - Q(D)) * pr


# ------------------------------------------------------------------ the allocation


PRINCIPAL, AGENT, THIRD = "principal", "agent", "third"
POWERS = ("veto", "halt", "reserve", "revoke", "amend")


class Arrangement:
    """Decisions held by parties; unallocated significant decisions are the principal's."""

    def __init__(self, held=None):
        self.held = dict(held or {})
        self.log = []

    def holder(self, decision):
        return self.held.get(decision, PRINCIPAL)

    def exercise(self, power, decision=None, valid=True):
        """Her exercise of a power; an invalid exercise (fails legitimacy) does not count
        and routes to the fallback."""
        if power not in POWERS:
            raise ValueError(power)
        if not valid:
            self.log.append(("fallback", power, decision))
            return "fallback"
        if power == "reserve":
            self.held[decision] = PRINCIPAL
        elif power == "revoke":
            self.held[decision] = PRINCIPAL
        elif power == "amend":
            pass
        self.log.append(("bound", power, decision))
        return "bound"

    def command(self, decision):
        """A positive command on a decision: on a delegated decision it creates a duty to
        answer and consult, not to obey; on a reserved decision it is her decision."""
        if self.holder(decision) == AGENT:
            return ("answer", "consult")
        if self.holder(decision) == PRINCIPAL:
            return ("decide",)
        return ("refer",)


# ------------------------------------------------------------------ erosion


def erosion(shortfall, threshold=None):
    """Steps at which the shortfall increases; with `threshold` a report is required only
    for an increase of at least that size.  Returns `(required, total_increase,
    unreported_increase)`."""
    required, total, unreported = [], Q(0), Q(0)
    for t in range(len(shortfall) - 1):
        d = Q(shortfall[t + 1]) - Q(shortfall[t])
        if d > 0:
            total += d
            if threshold is None or d >= threshold:
                required.append(t)
            else:
                unreported += d
    return required, total, unreported
