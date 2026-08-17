"""The force contract: what a force mechanism declares, and what it then owes.

The point of writing this down separately from the compiler is that it is
mechanism-neutral. It says what force must achieve, in quantities an outside
party can check, without saying how. A constrained market maker could sign the
same contract; the traderized compiler is one implementation of it.

A declaration carries five things — the row presentation, the ordinary-volume
bound the mechanism is robust to, the market maker's slack, the enforcement
intensities, and the promised conformance. The theorem turns the first four into
the fifth. That is what makes a price outside tolerance attributable: it is a
failure of the implementation or of a declared assumption, and the declaration
says which assumptions were made.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

from deduction import world_deficit
from enforcement import EnforcementTrader, Region
from market import ZERO


def certified_intensity(slack: Fraction, volume: Fraction,
                        tolerance: Fraction) -> Fraction:
    """The intensity that buys a declared conformance tolerance.

    From `sum_j beta_j g_j^2 <= slack + volume`, a uniform intensity of
    `(slack + volume) / tolerance^2` forces every row violation to at most
    `tolerance`. The volume bound is available before the price is set — it is
    the constant the trading-firm construction already computes from the belief
    history — so the intensity is choosable at the date it is needed.
    """
    tolerance = Fraction(tolerance)
    if tolerance <= 0:
        raise ValueError("tolerance is positive")
    return (Fraction(slack) + Fraction(volume)) / tolerance ** 2


class ForceDeclaration:
    """What the mechanism puts its name to at one date."""

    def __init__(self, region: Region, volume: Fraction, slack: Fraction,
                 tolerance: Fraction) -> None:
        self.region = region
        self.volume = Fraction(volume)
        self.slack = Fraction(slack)
        self.tolerance = Fraction(tolerance)
        self.intensity = certified_intensity(self.slack, self.volume,
                                             self.tolerance)

    def trader(self) -> EnforcementTrader:
        return EnforcementTrader(self.region, self.intensity)

    def conformance_holds(self, price: Sequence[Fraction]) -> bool:
        """Whether the displayed price meets the promise.

        Compared squarewise so the check is exact: `g <= tolerance` and
        `g^2 <= tolerance^2` agree for nonnegative quantities, and the second
        needs no root.
        """
        return all(g ** 2 <= self.tolerance ** 2
                   for g in self.region.violations(price))

    def budget_consumed(self, price: Sequence[Fraction]) -> Fraction:
        """`sum_j beta_j g_j^2`, which the enforcement inequality caps at
        `slack + volume`. Reading it at the displayed price is how a verifier
        confirms the mechanism was inside its own declaration."""
        return self.trader().weighted_square_violation(price)

    def liability_bound(self, price: Sequence[Fraction],
                        world: Sequence[Fraction]) -> Fraction:
        """`sum_j beta_j g_j(P) d_j(W)` — the date's enforcement liability ceiling.

        From the liability identity: the realised position's value in `W` is at
        least the weighted square violation minus this. Two factors, and both are
        needed: a live violation, and a row that excludes `W`.
        """
        trader = self.trader()
        deficits = world_deficit(self.region, world)
        return sum((beta * row.violation(price) * deficit
                    for beta, row, deficit
                    in zip(trader.betas, self.region.rows, deficits)), ZERO)


def volume_times_depth(volume: Fraction, deficits: Sequence[Fraction]) -> Fraction:
    """`C * max_j d_j(W)`: the intensity-free reading of the liability ceiling.

    The bound of `ForceDeclaration.liability_bound` carries the intensities, but
    they cancel against the conformance they buy. What is left is the ordinary
    volume times how deep the region excludes the world — so a mechanism cannot
    make its liability smaller by enforcing harder, and cannot make it larger
    either. Checked against the exact ledger in `test_contract`.
    """
    return Fraction(volume) * max(deficits, default=ZERO)


def cumulative_liability_bound(schedule: Sequence[tuple[Fraction, Sequence[Fraction]]]
                               ) -> Fraction:
    """Sum of `volume * depth` over dates: the safety condition's left side.

    Finite here is sufficient for the criterion to survive, by the safety
    theorem. World-inclusiveness is the case where every depth is zero, which is
    one way for this sum to converge and not the only one.
    """
    return sum((volume_times_depth(volume, deficits)
                for volume, deficits in schedule), ZERO)
