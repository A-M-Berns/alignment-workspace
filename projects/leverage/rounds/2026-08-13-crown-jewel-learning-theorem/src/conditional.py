"""The conditional rate, and where the margin comes from.

Two refinements of the merged bridge lemma.

**The denominator.** The merged round bounded `Q_T(g) <= B_T(g)/delta_g` and read
it against `T`. That is the wrong denominator: a reason exposed only `o(T)` times
makes `Q_T/T -> 0` say nothing. The quantity that means *learning how to respond
to a reason* is `Q_T(g)/M_T(g)`, where `M_T(g)` counts the occasions the reason was
actually before the learner. Dividing the same inequality gives the coverage
condition in its weakest form: `B_T(g) = o(M_T(g))`, which for a `sqrt(T)` regret
bound is `M_T(g) >> sqrt(T)` — far weaker than positive density.

**The margin.** `delta_g > 0` is a hypothesis in the merged lemma. For a class of
repairs it can be *derived* from the loss construction instead, under a structural
side condition that is itself a public predicate. `margin_certificate` below states
the condition and `derived_margin` returns the guaranteed value.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Mapping, Optional, Sequence


# ------------------------------------------------------------ the arithmetic


def bad_mass_bound(regret_bound: Fraction, margin: Fraction) -> Fraction:
    """`Q_T <= B_T / delta`. The merged lemma, rearranged."""
    if margin <= 0:
        raise ValueError("a margin bound needs a strictly positive margin")
    return regret_bound / margin


def conditional_rate_bound(
    regret_bound: Fraction, margin: Fraction, exposure: Fraction
) -> Fraction:
    """`Q_T/M_T <= B_T/(delta * M_T)`.

    Undefined where the reason was never exposed, which is a real case and is
    raised rather than returned as zero: a learner never asked has no conditional
    rate, not a perfect one.
    """
    if exposure <= 0:
        raise ValueError("no selected occasions: the conditional rate is undefined")
    return bad_mass_bound(regret_bound, margin) / exposure


def coverage_suffices(
    regret_bounds: Sequence[Fraction], exposures: Sequence[Fraction]
) -> bool:
    """Whether `B_T/M_T` is decreasing along the given horizons.

    The finite shadow of `B_T = o(M_T)`. Checked over a horizon family rather than
    asserted asymptotically.
    """
    ratios = [b / m for b, m in zip(regret_bounds, exposures)]
    return all(later < earlier for earlier, later in zip(ratios, ratios[1:]))


# --------------------------------------------------------------- the margin


@dataclass(frozen=True)
class MarginCertificate:
    """Why a repair's improvement is guaranteed rather than assumed.

    `weight` is the loss component the repair discharges. `side_condition` names
    the public predicate under which discharging it creates no offsetting charge.
    Both are data; neither reads a loss.
    """

    repair: str
    discharges: str
    weight: Fraction
    side_condition: str


def derived_margin(
    certificate: MarginCertificate,
    side_condition_holds: bool,
) -> Optional[Fraction]:
    """The margin the loss construction guarantees, or `None` if it does not.

    Returning `None` rather than zero keeps "the margin is not derivable here"
    distinct from "the margin is zero", which are different situations and have
    different consequences for the theorem.
    """
    return certificate.weight if side_condition_holds else None
