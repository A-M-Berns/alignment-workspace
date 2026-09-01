"""Row-indexed enforcement books, local authority capacity, and scheduling.

The enforcement book decomposes over rows, `E_t = sum_j E_t^j`, so the assessed
account decomposes too: `V_N(omega) = sum_j V_N^j(omega)`. The market maker's
contract caps the *aggregate*; isolating one summand needs floors on the rest.

Local **authority capacity** and lifetime **SafeCert** are different objects and
this module keeps them apart:

    capacity(t)   a predictable set of allocations available on date t
    SafeCert      a property of the realized account over the whole history

Exact rationals throughout.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence


# --- book decomposition ---------------------------------------------------


class Book:
    """One row's assessed account, as its dated increments at one world."""

    def __init__(self, increments: Sequence[Fraction]):
        self.increments = list(increments)

    def prefix(self, horizon: int) -> Fraction:
        return sum(self.increments[:horizon], Fraction(0))

    def floor(self) -> Fraction:
        """The least `B` with every prefix at least `-B`."""
        worst = Fraction(0)
        total = Fraction(0)
        for x in self.increments:
            total += x
            worst = max(worst, -total)
        return worst

    def ceiling(self) -> Fraction:
        best = Fraction(0)
        total = Fraction(0)
        for x in self.increments:
            total += x
            best = max(best, total)
        return best


def aggregate(books: Sequence[Book]) -> Book:
    horizon = max(len(b.increments) for b in books)
    total = []
    for t in range(horizon):
        total.append(sum((b.increments[t] if t < len(b.increments) else Fraction(0)
                          for b in books), Fraction(0)))
    return Book(total)


def subset_ceiling_bound(books: Sequence[Book], subset: Sequence[int],
                         cap: Fraction) -> Fraction:
    """`U + sum_{j not in subset} B_j`, the bound Lemma R1 gives.

    Uniform over subsets when the complement's floors are summed in full.
    """
    return cap + sum((books[j].floor() for j in range(len(books))
                      if j not in set(subset)), Fraction(0))


# --- local capacity -------------------------------------------------------


def authority_cap(allowance: Fraction, budget: Fraction,
                  depth: Fraction) -> Fraction:
    """`a <= allowance^2 / (budget * depth^2)`.

    `budget` is the date's slack-plus-volume, `depth` the worst live exclusion
    depth. Inverting the worst-case charge `sqrt(a * budget) * depth <= allowance`.
    """
    if depth <= 0:
        raise ValueError("a zero-depth row has no liability ceiling to invert")
    return allowance ** 2 / (budget * depth ** 2)


def charge_squared(alloc: Fraction, budget: Fraction,
                   depth: Fraction) -> Fraction:
    """`(sqrt(a * budget) * depth)^2 = a * budget * depth^2`."""
    return alloc * budget * depth ** 2


# The allowance an allocation consumes is `sqrt(a * budget) * depth`, which is
# irrational in general. `authority_cap` is its inverse, so every schedule below
# is specified by rational allowances and the allocations are derived; the module
# never takes a square root and only ever compares allowances.


# --- scheduling, specified by allowances ---------------------------------


def schedule_from_allowances(allowances: Sequence[Sequence[Fraction]],
                             budget: Fraction,
                             depths: Sequence[Fraction]) -> list[list[Fraction]]:
    """Turn a rational allowance matrix into the allocations it buys."""
    return [[authority_cap(b, budget, depths[r]) if b > 0 else Fraction(0)
             for r, b in enumerate(row)]
            for row in allowances]


def proportional_allowances(horizon: int, reasons: int,
                            allowance: Fraction) -> list[list[Fraction]]:
    """Every reason gets an equal share of every date's allowance."""
    share = allowance / reasons
    return [[share] * reasons for _ in range(horizon)]


def round_robin_allowances(horizon: int, reasons: int,
                           allowance: Fraction) -> list[list[Fraction]]:
    """One reason gets the whole allowance on its turn and nothing otherwise."""
    out = []
    for t in range(horizon):
        row = [Fraction(0)] * reasons
        row[t % reasons] = allowance
        out.append(row)
    return out


def spend(allowances: Sequence[Sequence[Fraction]]) -> list[Fraction]:
    """The allowance each date consumes in total."""
    return [sum(row, Fraction(0)) for row in allowances]


def totals(schedule: Sequence[Sequence[Fraction]]) -> list[Fraction]:
    reasons = len(schedule[0])
    return [sum((row[r] for row in schedule), Fraction(0))
            for r in range(reasons)]
