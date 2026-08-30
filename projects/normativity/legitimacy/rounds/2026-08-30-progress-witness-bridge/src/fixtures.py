"""Exact finite fixtures for the restricted Progress witness bridge.

These calculations illustrate the paper proof and countermodels. They are not a proof
of an asymptotic theorem and do not register a claim.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Iterable, Sequence

Q = Fraction


def pairwise_gain(p_source: Q, v_source: Q, v_target: Q) -> Q:
    """Gain from moving all source-label mass to the target label."""
    return p_source * (v_target - v_source)


def restricted_witness_holds(
    p_source: Q, margin: Q, valuations: Iterable[tuple[Q, Q]]
) -> bool:
    """Finite check of the pairwise Sensitivity inequality on supplied valuations."""
    vals = tuple(valuations)
    if not vals or margin <= 0:
        return False
    if any(v_target - v_source < margin for v_source, v_target in vals):
        return False
    robust_gain = min(
        pairwise_gain(p_source, v_source, v_target)
        for v_source, v_target in vals
    )
    return robust_gain >= margin * p_source


def weighted_mass(
    attention: Sequence[Q], applicability: Sequence[Q], defects: Sequence[Q]
) -> tuple[Q, Q]:
    """Return `(W,D)` for aligned finite prefixes."""
    if not (len(attention) == len(applicability) == len(defects)):
        raise ValueError("attention, applicability, and defects must align")
    weights = [a * c for a, c in zip(attention, applicability)]
    return sum(weights, Q(0)), sum(
        (w * d for w, d in zip(weights, defects)), Q(0)
    )


def opposite_pairwise_rows_feasible(forward: Q, backward: Q) -> bool:
    """Whether `vy-vx>=forward` and `vx-vy>=backward` can hold together."""
    return forward + backward <= 0


def power_of_two_applicability(horizon: int) -> list[Q]:
    """Predictable sparse exposure used in the changing-applicability fixture."""
    return [Q(1) if n > 0 and n & (n - 1) == 0 else Q(0) for n in range(horizon)]


def harmonic_defects(horizon: int) -> list[Q]:
    """A live issue whose designated source defect vanishes without an event."""
    return [Q(1, n + 1) for n in range(horizon)]


def row_active(enabled: bool, applicable: bool, disposed: bool) -> bool:
    """The restricted compiler's activation gate."""
    return enabled and applicable and not disposed
