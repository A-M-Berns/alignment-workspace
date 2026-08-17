"""The Budgeter's dependence on its assessment-world process.

Logical Induction's `Budgeter` is parameterized by the deductive process: both its
shutoff test and its scaling factor quantify over the worlds propositionally
consistent with the current stage. A generalized construction assessed against a
support-live process must use a Budgeter parameterized by **that** process, and
the two are different functions of the same belief history.

That is why "the same algorithm under two criteria" is false. The criterion is not
the only thing the world set feeds; it feeds the construction that sets prices.

Written to the source's shape (`arXiv:1609.03543`, `defprop` Budgeter): the
returned strategy is the trader's own strategy scaled by

    inf over W in L of [ max(1, -W(T_n) / (b + W(sum_{i<n} T_i))) ]^{-1} ,

which is at most one, and smaller the more damaging the worst assessed world.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

from market import ONE, ZERO, holdings_value


def scaling(position: Sequence[Fraction], prices: Sequence[Fraction],
            prior_value: dict, budget: Fraction,
            assessment_worlds: Sequence[Sequence[Fraction]]) -> Fraction:
    """The Budgeter's scaling factor against a given assessment-world process.

    `prior_value` maps a world (as a tuple) to the trader's cumulative value
    there before this date. `budget` is the source's `b`. Returns a rational in
    `(0, 1]`.
    """
    if not assessment_worlds:
        raise ValueError("an empty assessment process leaves the infimum undefined")
    best = None
    for world in assessment_worlds:
        key = tuple(world)
        denominator = Fraction(budget) + prior_value.get(key, ZERO)
        if denominator <= 0:
            return ZERO                      # the shutoff branch has fired
        ratio = -holdings_value(position, prices, world) / denominator
        factor = ONE / max(ONE, ratio)
        if best is None or factor < best:
            best = factor
    return best


def shutoff(prior_values: Sequence[dict], budget: Fraction,
            assessment_worlds_by_date: Sequence[Sequence[Sequence[Fraction]]]) -> bool:
    """Whether the Budgeter has already zeroed the trader.

    Fires when some earlier date's cumulative value fell to `-b` or below in some
    world assessed **at that date**, which is where the process's nesting is
    consumed: a world live now was live then.
    """
    for values, worlds in zip(prior_values, assessment_worlds_by_date):
        for world in worlds:
            if values.get(tuple(world), ZERO) <= -Fraction(budget):
                return True
    return False
