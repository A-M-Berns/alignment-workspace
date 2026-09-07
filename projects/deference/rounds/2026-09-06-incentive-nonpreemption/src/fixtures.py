"""Exact episodes for the mediation register (after the 2026-08-18 round's)."""
from __future__ import annotations

from fractions import Fraction as Q

from src.mediation import Episode, Prep

CHOICES = ("d0", "d1")
ACTIONS = ("u0",)
KEEP = Prep("keep", CHOICES)
SEIZE = Prep("seize", ("d0",))
COMMIT_0 = Prep("commit-d0", CHOICES)
COMMIT_1 = Prep("commit-d1", CHOICES)
HEDGE = Prep("hedge", CHOICES)


def build(credence, cell, preps, want, quantity, grade=None):
    states = tuple(credence)
    if grade is None:
        grade = {(s, d): (Q(1) if d == want[s] else Q(0)) for s in states for d in CHOICES}
    table = {(s, p.name, d, u): Q(quantity(s, p.name, d, u))
             for s in states for p in preps for d in CHOICES for u in ACTIONS}
    return Episode(states, dict(cell), dict(credence), CHOICES, tuple(preps), ACTIONS,
                   grade, table, Q(1))


def committed():
    """Preparation pays only if it matches the realized choice; preemption buys the
    prediction error and nothing else."""
    def q(s, prep, d, u):
        if prep == "hedge":
            return Q(1, 2)
        return Q(1) if prep == f"commit-{d}" else Q(-1)
    return build({"s0": Q(3, 4), "s1": Q(1, 4)}, {"s0": "c0", "s1": "c0"},
                 (COMMIT_0, COMMIT_1, HEDGE), {"s0": "d0", "s1": "d1"}, q)


def override_after_full_update():
    """The agent predicts the principal exactly and values the other item."""
    return build({"s0": Q(1)}, {"s0": "c0"}, (KEEP,), {"s0": "d0"},
                 lambda s, p, d, u: Q(-1) if d == "d0" else Q(1))


def foreclosing():
    """A preparation that leaves one option and pays for it."""
    def q(s, prep, d, u):
        if prep == "seize":
            return Q(1)
        want = "d0" if s == "s0" else "d1"
        return Q(1, 2) if d == want else Q(-1)
    return build({"s0": Q(1, 2), "s1": Q(1, 2)}, {"s0": "c0", "s1": "c0"},
                 (KEEP, SEIZE), {"s0": "d0", "s1": "d1"}, q)


def mild_disagreement():
    """The agent mildly prefers the item the principal does not choose, at a
    preparation that pays for matching; both acceleration and override are live."""
    def q(s, prep, d, u):
        want = "d0" if s == "s0" else "d1"
        base = Q(1) if prep == f"commit-{d}" else Q(-1, 2)
        return base + (Q(1, 5) if d != want else Q(0))
    return build({"s0": Q(3, 5), "s1": Q(2, 5)}, {"s0": "c0", "s1": "c0"},
                 (COMMIT_0, COMMIT_1), {"s0": "d0", "s1": "d1"}, q)
