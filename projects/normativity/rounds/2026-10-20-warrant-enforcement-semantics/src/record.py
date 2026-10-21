"""The record of a market run on the one-coordinate countermodel (Part C).

A run carries the grounds, the docket, the certificate events, the authorized events
and the price.  The record carries everything but the price; the enforcer's position
enters it as the force algebra's `Σ β · violation · normal` over the live rows.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction as F

from licence import Certificate, countermodel_grounds, licensed


@dataclass(frozen=True)
class MarketRun:
    price: F
    defeated: frozenset = frozenset()
    certs: tuple = ()
    authorized: frozenset = frozenset()
    beta: F = F(1)

    def __init__(self, price: F, defeated=(), certs=(), authorized=(), beta: F = F(1)):
        object.__setattr__(self, "price", price)
        object.__setattr__(self, "defeated", frozenset(defeated))
        object.__setattr__(self, "certs", tuple(certs))
        object.__setattr__(self, "authorized", frozenset(authorized))
        object.__setattr__(self, "beta", beta)


@dataclass(frozen=True)
class RecordEntry:
    grounds: tuple
    defeated: frozenset
    certs: tuple
    authorized: frozenset
    position: F

    def decide_licensed(self, v: F, c: Certificate, event: int) -> bool:
        return licensed(list(self.grounds), set(self.defeated), v, c, event, set(self.authorized))


def position(run: MarketRun) -> F:
    """`Σ_rows β · max(0, lower − p) · 1` over the live premise rows."""
    G = countermodel_grounds()
    return sum((run.beta * max(F(0), o.lower_bound - run.price)
                for o in G if o.id not in run.defeated), F(0))


def trace(run: MarketRun) -> RecordEntry:
    return RecordEntry(tuple(countermodel_grounds()), run.defeated, run.certs, run.authorized,
                       position(run))
