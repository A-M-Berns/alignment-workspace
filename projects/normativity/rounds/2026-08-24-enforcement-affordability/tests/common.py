"""Shared fixture machinery for the enforcement-affordability suites."""
from __future__ import annotations

import pathlib
import sys
from fractions import Fraction as Q

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "src"))

from market_model import (  # noqa: E402
    Box,
    BudgetedTrader,
    Enforcer,
    Ledger,
    Segment,
    UnbudgetedTrader,
    all_patterns,
    geometric_slack,
    intensity,
    lifetime_liability,
    loss_cap,
    run_market,
    solve_day,
    value_of,
)

ZERO = Q(0)
ONE = Q(1)
HALF = Q(1, 2)

P0 = (ZERO,)
P1 = (ONE,)
BOTH = (P0, P1)


def undecided(day: int):
    return BOTH


def settled_true(day: int):
    return (P1,)


def delta_half(n: int) -> Q:
    return HALF


def delta_inv(n: int) -> Q:
    return Q(1, n)


def delta_dyadic(n: int) -> Q:
    return Q(1, 2 ** n)


def interval(lo: Q, hi: Q) -> Box:
    return Box(((lo, hi),))


def const_schedule(region, A: Q, delta_fn):
    def schedule(day: int):
        return region, intensity(A, day, delta_fn(day))
    return schedule


def seller(F: Q):
    return lambda day, prices: {"phi": -F}


def buyer(F: Q):
    return lambda day, prices: {"phi": F}


def eps_of(day: int) -> Q:
    return Q(1, 2 ** day)


def enforcer_coeffs(enf: Enforcer):
    """Realized per-day enforcement coefficients on a one-sentence support."""
    return [(day, shares.get("phi", ZERO), prices["phi"])
            for day, shares, prices in enf.ledger.trades]


def conservation_check(traders, support, tables, days: int) -> None:
    """The ledger form of the MarketMaker guarantee: the summed cumulative
    value of all traders is at most the geometric slack, at every table."""
    slack = geometric_slack(days)
    for table in tables:
        total = sum(t.ledger.worth(table) for t in traders)
        assert total <= slack, (table, total, slack)
