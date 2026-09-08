"""Exact finite model of protected reason coverage.

Per concern and world: `active`, `rep` (represented in the process), `in_trace`
(present in the declared reason trace at commitment).  `live` = active and not
represented.  The barrier says a certified world has no live protected concern; the
bridge says representation lands in the trace; coverage is the conclusion.
"""
from __future__ import annotations

from fractions import Fraction as F


def live(d, c, w):
    return d["active"](c, w) and not d["rep"](c, w)


def rep_faithful(d, scope, worlds):
    return all(d["in_trace"](c, w) for c in scope for w in worlds if d["rep"](c, w))


def no_bind_live(d, scope, worlds, C):
    return all(not live(d, c, w) for w in worlds if C(w) for c in scope)


def covered(d, scope, worlds, C):
    return all(d["in_trace"](c, w) for w in worlds if C(w) for c in scope if d["active"](c, w))


def cov_fail(d, scope, w):
    return any(d["active"](c, w) and not d["in_trace"](c, w) for c in scope)


def mass(pi, event):
    return sum((pi[w] for w in pi if event(w)), F(0))
