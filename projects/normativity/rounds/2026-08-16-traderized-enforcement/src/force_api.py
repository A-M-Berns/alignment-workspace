"""The consumable entry point for traderized force.

One function in, one certificate out. A component that has an admissibility
constraint in price space calls `compile_force`; everything else in this round is
the justification for what it returns.

Specified in `projects/normativity/notes/TRADERIZED_FORCE_INTERFACE.md`. Names
are provisional.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

from contract import ForceDeclaration, declared_liability_bound
from enforcement import Region, Row
from market import ZERO


class ForceCertificate:
    """What a caller receives: a position, a promise, and an obligation.

    The promise is `conformance`: every row violation at a contract-satisfying
    price is at most the declared tolerance. The obligation is
    `liability_ceiling`: the caller's own layer must show the cumulative value of
    the positions over its assessment worlds is bounded, and this is the per-date
    ceiling it may use.
    """

    def __init__(self, declaration: ForceDeclaration) -> None:
        self.declaration = declaration
        self.intensity = declaration.intensity
        self.tolerance = declaration.tolerance

    def position(self, prices: Sequence[Fraction]):
        """The realised day-`t` position at the displayed prices."""
        return self.declaration.trader().coefficients(prices)

    def conformance_holds(self, prices: Sequence[Fraction]) -> bool:
        return self.declaration.conformance_holds(prices)

    def budget_consumed(self, prices: Sequence[Fraction]) -> Fraction:
        return self.declaration.budget_consumed(prices)

    def liability_ceiling(self, deficits: Sequence[Fraction]) -> Fraction:
        """The per-date ceiling in declared quantities, given the exclusion
        deficits of an assessment world."""
        return declared_liability_bound(self.declaration.slack,
                                        self.declaration.volume,
                                        self.declaration.tolerance, deficits)


def compile_force(rows: Sequence[tuple[Sequence[Fraction], Fraction]],
                  dimension: int, slack: Fraction, volume: Fraction,
                  tolerance: Fraction) -> ForceCertificate:
    """Compile a price-space row system into a certified enforcement position.

    `rows` are `(coefficients, right-hand side)` pairs meaning
    `⟪c, P⟫ ≥ r`. The caller supplies the market maker's slack, a bound on the
    ordinary aggregate's realised position, and the tolerance it wants promised.

    Raises when the region is empty on the cube's rational corners, which is the
    cheapest nonemptiness screen and **not** a full feasibility certificate: that
    is the adapter's job, upstream.
    """
    region = Region(dimension, [Row(c, r) for c, r in rows])
    if not _plausibly_nonempty(region, dimension):
        raise ValueError("region appears empty; run the feasibility adapter")
    return ForceCertificate(ForceDeclaration(region, volume, slack, tolerance))


def _plausibly_nonempty(region: Region, dimension: int) -> bool:
    from enforcement import grid
    return any(region.contains(p) for p in grid(dimension, 4))
