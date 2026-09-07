"""Partial evaluations, completions, and the three regrets, exact.

Worlds carry a credence; `C(w)` is the common activation; `Vp[w][a]` is the partial
evaluation, present only where `C(w)`; a completion is any total table agreeing with
`Vp` on certified worlds; a followed strategy is a world-dependent probability vector
over candidates.
"""
from __future__ import annotations

from fractions import Fraction as F


def expect(pi, X):
    return sum((pi[w] * X(w) for w in pi), F(0))


def ind(C, w):
    return F(1) if C(w) else F(0)


def mass(pi, C):
    return expect(pi, lambda w: ind(C, w))


def complete(pi, C, Vp, cands, fill):
    """A completion: `fill(w, a)` off the certified set."""
    return {w: {a: (Vp[w][a] if C(w) else fill(w, a)) for a in cands} for w in pi}


def activated(C, Vbar, a):
    return lambda w: ind(C, w) * Vbar[w][a]


def followed(alpha, X):
    """`X[w][a]` under the world-dependent mixture `alpha[w][a]`."""
    return lambda w: sum((alpha[w][a] * X[w][a] for a in X[w]), F(0))


def regret_U(pi, C, Vbar, alpha, cands):
    best = max(expect(pi, activated(C, Vbar, a)) for a in cands)
    return best - expect(pi, lambda w: ind(C, w) * followed(alpha, Vbar)(w))


def regret_V(pi, Vbar, alpha, cands):
    best = max(expect(pi, lambda w, a=a: Vbar[w][a]) for a in cands)
    return best - expect(pi, followed(alpha, Vbar))


def cond_expect_partial(pi, C, X):
    """`E[X | C]` for a partial `X(w)` defined only where `C(w)`."""
    return expect(pi, lambda w: X(w) if C(w) else F(0)) / mass(pi, C)


def regret_auth(pi, C, Vp, alpha, cands):
    best = max(cond_expect_partial(pi, C, lambda w, a=a: Vp[w][a]) for a in cands)
    return best - cond_expect_partial(
        pi, C, lambda w: sum((alpha[w][a] * Vp[w][a] for a in cands), F(0)))


def void_mass(pi, C):
    return expect(pi, lambda w: 1 - ind(C, w))
