"""The licence chain on the one-coordinate countermodel, in exact rationals.

Mirrors `WarrantEntitlement.lean` Part A on `Countermodel`: two occurrences `r₁`, `r₂`
each `P(φ) ≥ 1/2`; the forced region is `[1/2, 1]` under either docket; a certificate
cites an occurrence for its lower row; `Supported` needs the citation live; `Licensed`
needs the issuing event authorized.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction as F


@dataclass(frozen=True)
class Occurrence:
    id: int
    lower_bound: F          # the premise row `P(φ) ≥ lower_bound`
    source: str
    cites: str | None = None
    defeaters: frozenset = frozenset()


def countermodel_grounds() -> list[Occurrence]:
    return [Occurrence(1, F(1, 2), "party 1"), Occurrence(2, F(1, 2), "party 2")]


def live_rows(G: list[Occurrence], defeated: set[int]) -> dict[int, F]:
    return {o.id: o.lower_bound for o in G if o.id not in defeated}


def forced_interval(G: list[Occurrence], defeated: set[int]) -> tuple[F, F]:
    lows = live_rows(G, defeated).values()
    return (max(lows, default=F(0)), F(1))


def admissible(G: list[Occurrence], defeated: set[int], v: F) -> bool:
    lo, hi = forced_interval(G, defeated)
    return lo <= v <= hi


@dataclass(frozen=True)
class Certificate:
    """A lower-bound row cited by occurrence, the cube face `P(φ) ≤ 1` as the upper
    row, and the two attained endpoints."""
    lower_cite: int
    lo_point: F = F(1, 2)
    hi_point: F = F(1)


def supported(G: list[Occurrence], defeated: set[int], v: F, c: Certificate) -> bool:
    rows = live_rows(G, defeated)
    if c.lower_cite not in rows:            # the positively weighted row must be cited live
        return False
    lo_val = rows[c.lower_cite]
    return (lo_val <= v <= F(1)
            and admissible(G, defeated, c.lo_point) and c.lo_point == lo_val
            and admissible(G, defeated, c.hi_point) and c.hi_point == F(1))


def licensed(G: list[Occurrence], defeated: set[int], v: F, c: Certificate, event: int,
             authorized: set[int]) -> bool:
    return supported(G, defeated, v, c) and event in authorized


def defeat(defeated: set[int], port: int) -> set[int]:
    return set(defeated) | {port}
