"""The provisional-amendment state machine over authority profiles.

States are labelled profiles from `authority.py`:
  live(G, U)             the pre-amendment floor
  provisional(G ∪ R, U)  R granted, every r ∈ R covered by the recall route
  final(G ∪ R, U ∪ R')   the recall route dismantled for R' ⊆ R

Transitions:
  grant     live -> provisional        slow (scope grows)
  recall    provisional -> live        fast (scope shrinks, coverage unchanged)
  finalize  provisional -> final       slow iff R' ≠ ∅ (coverage shrinks)
  revoke    final -> live              fast in the order, but only *possible* if the
                                       grants in R' can still be overridden — which is
                                       what `U ∪ R'` says they cannot.
"""
from __future__ import annotations

from src.authority import geq, lane


def grant(live, R):
    G, U = live
    return (G | R, U)


def recall(prov, R):
    G, U = prov
    return (G - R, U)


def finalize(prov, Rp):
    G, U = prov
    return (G, U | Rp)


def recall_possible(profile, R):
    """Recall of R needs every r ∈ R to be overridable: R ∩ U = ∅."""
    return not (R & profile[1])
