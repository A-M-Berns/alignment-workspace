"""The motivating normative constraint process, and its safety obligation.

Not a hypothetical region: the statics already in the normativity line. At date
`t` the settlement interface supplies a post-settlement simplex, an endorsed
region, and a declared core minimum `theta_min`; `NL-SI-A2` turns the core
condition into one rational row per endorsement; `CORE_CONDITION.md` compiles
that row into a price-space row a trader can act on.

The force region splits into two families whose liability properties are
different, and conflating them is the mistake this module exists to prevent:

* **settlement / coherence rows**, whose right-hand sides are minima over the
  assessed worlds. Every assessed world satisfies them, so their exclusion
  deficit is identically zero and they contribute **nothing** to enforcement
  liability.
* **core / endorsement rows**, which are useful precisely when they exclude a
  credal state the settled record still permits. They are where liability comes
  from, and their worst deficit is `max(0, r - m_c)` — how far the endorsement's
  demand exceeds what the worst assessed world delivers, **independent of the
  declared core minimum**.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

from contract import ForceDeclaration, declared_liability_bound
from core import compile_core_row, indicator
from deduction import support_rows, world_deficit
from enforcement import Region, Row
from market import ZERO, Fragment


class Endorsement:
    """One book endorsement `<c, q> >= r`, with `c` indexed by worlds."""

    def __init__(self, sentence: str, rhs: Fraction) -> None:
        self.sentence = sentence
        self.rhs = Fraction(rhs)

    def coefficient(self, fragment: Fragment,
                    worlds: Sequence[Sequence[Fraction]]):
        return indicator(fragment, self.sentence, worlds)

    def worst_delivery(self, fragment: Fragment,
                       worlds: Sequence[Sequence[Fraction]]) -> Fraction:
        """`m_c = min_w c_w`, the least an assessed world delivers."""
        return min(self.coefficient(fragment, worlds))

    def exclusion_depth(self, fragment: Fragment,
                        worlds: Sequence[Sequence[Fraction]]) -> Fraction:
        """`max(0, r - m_c)`: the worst deficit its core row can carry.

        Independent of `theta`. Settlement can only raise `m_c` — the assessed
        worlds shrink — so this quantity is **non-increasing along a settlement
        trajectory**, which is what the interface's monotonicity buys here.
        """
        return max(ZERO, self.rhs - self.worst_delivery(fragment, worlds))


def force_region(fragment: Fragment, settled: dict,
                 endorsements: Sequence[Endorsement],
                 theta: Fraction) -> tuple[Region, Region]:
    """`K_t^norm`, returned as its two families rather than one merged region."""
    worlds = fragment.pc_worlds(settled)
    settlement = Region(fragment.dimension, support_rows(fragment, settled))
    core_rows = [compile_core_row(e.coefficient(fragment, worlds), e.rhs,
                                  theta, fragment, worlds)
                 for e in endorsements]
    return settlement, Region(fragment.dimension, core_rows)


def family_deficits(region: Region,
                    worlds: Sequence[Sequence[Fraction]]) -> Fraction:
    """The worst exclusion deficit a family imposes on any assessed world."""
    return max((max(world_deficit(region, w), default=ZERO) for w in worlds),
               default=ZERO)


def liability_bound_at_date(settlement: Region, core: Region,
                            worlds: Sequence[Sequence[Fraction]],
                            slack: Fraction, volume: Fraction,
                            tolerance: Fraction) -> Fraction:
    """The declared-quantity ceiling for the merged region at one date.

    Both families are declared to the same force mechanism, so the ceiling reads
    the merged deficit vector; the settlement family contributes zero to it.
    """
    merged = Region(settlement.dimension,
                    list(settlement.rows) + list(core.rows))
    worst = max((sum(world_deficit(merged, w), ZERO) for w in worlds),
                default=ZERO)
    return declared_liability_bound(slack, volume, tolerance, (worst,))


def trajectory_bound(dates: Sequence[dict]) -> Fraction:
    """Cumulative ceiling over a trajectory of per-date declarations."""
    return sum((liability_bound_at_date(**d) for d in dates), ZERO)
