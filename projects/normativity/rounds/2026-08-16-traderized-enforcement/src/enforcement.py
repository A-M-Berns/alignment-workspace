"""Admissible regions, the constraint-to-trade compiler, and enforcement.

An admissible region is presented as a finite system of rational rows
`c_j . x >= r_j` intersected with the cube. The compiler turns that presentation
into one day-`n` trading strategy whose coefficient vector is

    zeta_E(p) = sum_j beta_j * max(0, r_j - c_j . p) * c_j,

which is buildable from price features, rational constants, addition,
multiplication and `max` — so it is an expressible feature in Logical
Induction's sense, and therefore a legal trading strategy rather than a
functional written down outside the framework.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Iterable, Sequence

from market import (ONE, ZERO, Vector, add, dot, in_cube, l1, max_gain,
                    scale, sub)


class Row:
    """One rational half-space `c . x >= r`."""

    __slots__ = ("c", "r")

    def __init__(self, c: Sequence[Fraction], r: Fraction) -> None:
        self.c = tuple(Fraction(x) for x in c)
        self.r = Fraction(r)

    def slack(self, p: Sequence[Fraction]) -> Fraction:
        return dot(self.c, p) - self.r

    def violation(self, p: Sequence[Fraction]) -> Fraction:
        """`g_j(p) = max(0, r_j - c_j . p)`; zero exactly when the row holds."""
        v = self.r - dot(self.c, p)
        return v if v > 0 else ZERO

    def __repr__(self) -> str:
        return f"Row({self.c!r} >= {self.r})"


class Region:
    """A nonempty admissible region: the cube cut by finitely many rows."""

    def __init__(self, dimension: int, rows: Iterable[Row]) -> None:
        self.dimension = dimension
        self.rows = tuple(rows)

    def contains(self, p: Sequence[Fraction]) -> bool:
        return in_cube(p) and all(row.slack(p) >= 0 for row in self.rows)

    def violations(self, p: Sequence[Fraction]) -> tuple[Fraction, ...]:
        return tuple(row.violation(p) for row in self.rows)

    def grid_points(self, denominator: int) -> list[Vector]:
        """Every region point on the rational grid of the given denominator."""
        out = []
        for point in grid(self.dimension, denominator):
            if self.contains(point):
                out.append(point)
        return out


def grid(dimension: int, denominator: int) -> list[Vector]:
    """Exact rational grid over the cube. No floating point anywhere."""
    axis = [Fraction(i, denominator) for i in range(denominator + 1)]
    return [tuple(pt) for pt in product(axis, repeat=dimension)]


# --- the constraint-to-trade compiler --------------------------------------

class EnforcementTrader:
    """The violation-proportional trader compiled from a region presentation.

    `intensities` are the per-row position sizes `beta_j`. They are a trading
    intensity and nothing else: they are not a budget, not a credit line, and
    not an amount of money the trader holds. What they buy is stated in
    `enforcement_bound`.
    """

    def __init__(self, region: Region,
                 intensities: Sequence[Fraction] | Fraction) -> None:
        self.region = region
        if isinstance(intensities, (int, Fraction)):
            self.betas = tuple(Fraction(intensities) for _ in region.rows)
        else:
            self.betas = tuple(Fraction(b) for b in intensities)
        if len(self.betas) != len(region.rows):
            raise ValueError("one intensity per row")
        if any(b <= 0 for b in self.betas):
            raise ValueError("intensities are positive")

    def coefficients(self, p: Sequence[Fraction]) -> Vector:
        """The realised day-`n` position at displayed prices `p`."""
        total = tuple(ZERO for _ in range(self.region.dimension))
        for beta, row in zip(self.betas, self.region.rows):
            g = row.violation(p)
            if g:
                total = add(total, scale(beta * g, row.c))
        return total

    def weighted_square_violation(self, p: Sequence[Fraction]) -> Fraction:
        """`sum_j beta_j g_j(p)^2` — the quantity the contract bounds."""
        return sum((beta * row.violation(p) ** 2
                    for beta, row in zip(self.betas, self.region.rows)), ZERO)


class SingleSeparatorTrader:
    """The naive compiler: one row at a time, ignoring the rest of the region.

    Kept because it is what a hyperplane-separation reading of the idea
    produces, and because it fails — see `PROSECUTION.md` W3.
    """

    def __init__(self, region: Region, intensity: Fraction,
                 row_index: int = 0) -> None:
        self.region = region
        self.beta = Fraction(intensity)
        self.row_index = row_index

    def coefficients(self, p: Sequence[Fraction]) -> Vector:
        row = self.region.rows[self.row_index]
        g = row.violation(p)
        if not g:
            return tuple(ZERO for _ in range(self.region.dimension))
        return scale(self.beta * g, row.c)


# --- the enforcement inequality --------------------------------------------

def enforcement_residual(trader: EnforcementTrader,
                         p: Sequence[Fraction],
                         slack: Fraction,
                         ordinary_l1: Fraction) -> Fraction:
    """`(slack + ordinary_l1) - sum_j beta_j g_j(p)^2`.

    Nonnegative exactly when the enforcement inequality holds at `p`. The
    inequality itself is derived in `ENFORCEMENT.md` §2; this function is what
    the tests check it against on exact rational fixtures.
    """
    return (Fraction(slack) + Fraction(ordinary_l1)
            - trader.weighted_square_violation(p))


def contract_feasible_prices(trader: EnforcementTrader,
                             denominator: int,
                             slack: Fraction,
                             ordinary: Sequence[Fraction] | None = None
                             ) -> list[Vector]:
    """Every grid price the market maker could return against this aggregate.

    The market maker's brute-force search accepts any belief state meeting its
    contract, so the honest question is not "what does the fixed point do" but
    "what does the whole contract-feasible set look like". This enumerates it
    on a rational grid.
    """
    zero = tuple(ZERO for _ in range(trader.region.dimension))
    tau = tuple(Fraction(x) for x in ordinary) if ordinary is not None else zero
    out = []
    for p in grid(trader.region.dimension, denominator):
        zeta = add(trader.coefficients(p), tau)
        if max_gain(zeta, p) <= Fraction(slack):
            out.append(p)
    return out


def worst_ordinary_response(trader: EnforcementTrader,
                            p: Sequence[Fraction],
                            budget: Fraction,
                            denominator: int) -> tuple[Vector, Fraction] | None:
    """The ordinary-trader position of `l1` mass `<= budget` that best hides
    a violation at `p`: it maximises how far outside the region the contract
    still lets the displayed price sit.

    Returns the position and the resulting `max_gain`, or `None` if no grid
    position brings the aggregate inside the contract at slack zero.
    """
    best = None
    zeta_e = trader.coefficients(p)
    axis = [Fraction(i, denominator) for i in range(-denominator, denominator + 1)]
    for tau in product(axis, repeat=trader.region.dimension):
        if l1(tau) > Fraction(budget):
            continue
        g = max_gain(add(zeta_e, tuple(tau)), p)
        if best is None or g < best[1]:
            best = (tuple(tau), g)
    return best
