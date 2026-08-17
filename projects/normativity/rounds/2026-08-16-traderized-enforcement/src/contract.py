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
from market import ONE, ZERO


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
    disturbance = Fraction(slack) + Fraction(volume)
    if disturbance < 0:
        raise ValueError("slack and volume are nonnegative")
    if disturbance == 0:
        # An undisturbed market makes the formula return zero intensity, and a
        # zero intensity enforces nothing: `beta * g^2 <= 0` with `beta = 0` is
        # `0 <= 0`, which constrains no violation, so the conformance promise
        # would be derived from a vacuous inequality. Any positive intensity
        # instead forces `g = 0` exactly, which is a *stronger* guarantee than
        # the declared tolerance and is what the enforcement inequality actually
        # gives here. One is as good as any other; `1` is the choice.
        #
        # In the source market this branch is unreachable — `eps_n = 2^-n > 0`
        # at every date — so it is a guard against a caller declaring a market
        # the paper does not have, not a case the mechanism must live in.
        return ONE
    return disturbance / tolerance ** 2


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
    """`C * max_j d_j(W)`. **This is not a bound on the liability.**

    It was claimed as one, on the reasoning that the enforcement position offsets
    the ordinary one at equilibrium and so has size `C` whatever the intensity.
    That holds only where the contract forces the aggregate to vanish. Positive
    market-maker slack does not force it, and
    `test_regressions.IntensityFreeCeilingIsFalse` exhibits a date where the
    ordinary position is zero, the contract holds, conformance holds, and the
    liability is thirteen times this quantity.

    Kept computable so the regression can pin it. Use `declared_liability_bound`.
    """
    return Fraction(volume) * max(deficits, default=ZERO)


def declared_liability_bound(slack: Fraction, volume: Fraction,
                             tolerance: Fraction,
                             deficits: Sequence[Fraction]) -> Fraction:
    """`(slack + volume) * sum_j d_j(W) / tolerance`.

    What survives, in declared quantities. It follows from the kernel-checked
    identity — the liability is at most `sum_j beta_j g_j d_j` — by substituting
    the promised conformance `g_j <= tolerance` and the prescribed intensity.

    The intensity does **not** cancel, and the direction is the opposite of the
    withdrawn claim: a tighter promised tolerance needs a larger intensity, which
    permits a larger position, which raises the ceiling. Conformance and
    liability are traded against each other rather than independent.
    """
    tolerance = Fraction(tolerance)
    if tolerance <= 0:
        raise ValueError("tolerance is positive")
    return ((Fraction(slack) + Fraction(volume))
            * sum(deficits, ZERO) / tolerance)


def cumulative_liability_bound(
        schedule: Sequence[tuple[Fraction, Fraction, Fraction, Sequence[Fraction]]]
) -> Fraction:
    """Sum of `declared_liability_bound` over dates: the safety condition's left
    side, in the corrected form.

    Finite here is sufficient for the criterion to survive, by the safety
    theorem. A region containing every live world gives every deficit zero, which
    is one way for this sum to converge and not the only one.
    """
    return sum((declared_liability_bound(slack, volume, tolerance, deficits)
                for slack, volume, tolerance, deficits in schedule), ZERO)
