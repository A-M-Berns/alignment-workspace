"""Funding accounting for the enforcement trader.

Three quantities are tracked separately because collapsing any two of them is
one of the ways the construction can be made to look better than it is.

* **enforcement intensity** — the `beta_j` of `enforcement.EnforcementTrader`.
  A position size. It appears in the enforcement inequality and nowhere in this
  file.
* **worst-case exposure** — the largest single-date loss the realised position
  could take over *all* worlds. This is what an outside funder would have to
  stand behind if the market demanded collateral.
* **enforcement liability** — the cumulative value of the realised positions
  assessed in a world that is still *plausible* at the assessing date. This is
  the quantity Logical Induction's exploitation definition is stated over, and
  it is the one the safety theorem needs bounded.

`worst_case_exposure` may diverge while `liability` stays at zero. The two are
not the same number and the round's central positive result is exactly that
gap.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

from market import ZERO, Vector, holdings_value, min_value


class FundingLedger:
    """A date-indexed record of what enforcement cost.

    `credit_at(t)` is the cumulative external credit drawn through date `t`:
    finite at every finite date by construction, with no uniform bound imposed
    over dates. Whether it stays bounded is a fact about the trajectory, not an
    assumption of the model.
    """

    def __init__(self) -> None:
        self.dates: list[int] = []
        self.positions: list[Vector] = []
        self.prices: list[Vector] = []
        self.exposures: list[Fraction] = []

    def record(self, date: int, position: Sequence[Fraction],
               prices: Sequence[Fraction]) -> None:
        self.dates.append(date)
        self.positions.append(tuple(position))
        self.prices.append(tuple(prices))
        self.exposures.append(-min_value(position, prices))

    def exposure_at(self, date: int) -> Fraction:
        """Worst-case single-date loss at one date."""
        return self.exposures[self.dates.index(date)]

    def credit_at(self, date: int) -> Fraction:
        """Cumulative worst-case external credit drawn through `date`."""
        return sum((e for d, e in zip(self.dates, self.exposures) if d <= date),
                   ZERO)

    def cumulative_value(self, date: int, world: Sequence[Fraction]) -> Fraction:
        """`W(sum_{i <= date} E_i(P))`: the trader's net worth in one world."""
        return sum((holdings_value(pos, pr, world)
                    for d, pos, pr in zip(self.dates, self.positions, self.prices)
                    if d <= date), ZERO)

    def liability(self, plausible: dict[int, Sequence[Vector]]) -> Fraction:
        """`sup` over dates and plausible worlds of the cumulative *loss*.

        `plausible[d]` is the set of worlds propositionally consistent with the
        deductive stage at date `d`. Returns the least `B` with
        `W(sum_{i <= d} E_i) >= -B` over every recorded date and plausible
        world; zero when the trader never shows a plausible loss.
        """
        worst = ZERO
        for date in self.dates:
            for world in plausible.get(date, ()):
                loss = -self.cumulative_value(date, world)
                if loss > worst:
                    worst = loss
        return worst

    def credit_trajectory(self) -> list[tuple[int, Fraction]]:
        return [(d, self.credit_at(d)) for d in self.dates]


def exploitation_bound(liability: Fraction) -> Fraction:
    """The plausible-net-worth ceiling the safety theorem gives ordinary traders.

    Logical Induction's market maker caps the *aggregate* day-`n` value at
    `2^-n`, so the aggregate's cumulative plausible value is under `1`.
    Subtracting the enforcement trader leaves ordinary traders with at most
    `1 + B`, where `B` is the enforcement liability. Bounded `B` is therefore
    bounded ordinary upside, which is the failure of exploitation.
    """
    return Fraction(1) + Fraction(liability)
