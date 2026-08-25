"""Trajectories that exercise the safety condition, and the claims they separate.

Three things are easy to conflate and are different:

**A. Fixed-request monotonicity.** For one fixed row presentation and support,
`Omega' subset Omega` gives `D(Omega') <= D(Omega)`. This is a one-line
consequence of `D` being a maximum over the live worlds, and it is the only
monotonicity that holds without further hypotheses.

**B. Day-indexed compilation.** A frozen injunction over `Expect(X)` compiles to
a *different* row system at each day, because `E_n(X)` is the precision-`n+1`
threshold bundle. So A does not give `D_{n+1} <= D_n`, and the counterexample
below shows it fails: `D` rises across a day on which nothing was unsettled.

**C. The charge.** `q_t = (eps_t + M_t) * D_t / delta_t`. `D_t` falling does not
make `q_t` fall, and it is `sum_t q_t` that the safety condition bounds.

The trajectories are synthetic. They exist to show the mechanics run from
normative standing through the exact certificate to a cumulative account, and to
exhibit both a convergent and a divergent case; none of them is a normative
source anyone should believe in.
"""
from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from typing import Optional, Sequence

import li
import safety
import variants as v
from epistemic import (SettlementReading, SettlementSemantics, Stage,
                       deductive_entries)
from li import LUV
from pipeline import run_day
from waist import Expect, Ineq, Injunction

Q = Fraction


def grid_for(days: Sequence[int]) -> tuple:
    return li.merged_grid(days)


def ceiling(X, bound: Q = Q(1, 2), name: str = "Jcap") -> Injunction:
    return Injunction(name, (
        Ineq(((Q(1), Expect(X)),), rhs=bound, label="value-ceiling"),))


def stage_with(X, days: Sequence[int], settled: Optional[tuple] = None) -> Stage:
    """Threshold coherence over every day's grid, plus an optional settlement."""
    chain = deductive_entries(li.threshold_chain(X.luv, grid_for(days)),
                              note="threshold coherence")
    if settled is None:
        return Stage.of(chain)
    sem = SettlementSemantics()
    sem.admit(SettlementReading("l:pin", "o:pin", settled, "the readout"))
    return Stage.of(chain, sem.entries(["l:pin"]))



#: The builders below are memoized. Each drives several days of exponential
#: geometry and the suite asks for the same trajectory from several tests; the
#: cache changes what a run costs and not what it returns, because a built
#: trajectory is only ever read.

# ----------------------------------------------- A. fixed-request monotonicity


@lru_cache(maxsize=None)
def fixed_request_two_assessments(day: int = 2):
    """One compiled request, two nested live-world sets.

    Returns `(compiled, wide, narrow)` with `narrow` a subset of `wide`, so a
    test can compare the two certificates for the same request.
    """
    X = v.x0()
    J = ceiling(X)
    run = run_day(day, stage_with(X, (day,)), v._std([("s", J)]))
    wide = run.live_worlds
    narrow = tuple(w for w in wide if w[0] == Q(1))
    return run.compiled, wide, narrow


# -------------------------------------------- B. the mesh raises the deficit


#: The settlement the counterexample turns on: the quantity is at most `1/2`.
#: A world obeying it still reads `X` at `2/3` on the precision-3 mesh, because
#: the precision-`k` reading of a value is `ceil(x*k)/k` and that is not
#: monotone in `k` — it is `1/2` at `k = 2` and `2/3` at `k = 3` for `x` just
#: under `1/2`. So a ceiling at `1/2` is met at the coarser mesh and violated at
#: the finer one, with nothing about the world having changed.
def _at_most_half(X) -> tuple:
    return (li.Neg(X.luv.gt(Q(1, 2))), li.Neg(X.luv.gt(Q(2, 3))))


@lru_cache(maxsize=None)
def mesh_counterexample():
    """`D` rises from day 1 to day 2 on one frozen injunction and one stage.

    The stage settles that the quantity is at most `1/2`; the injunction is
    `Expect(X) <= 1/2` throughout. Then

        day 1, k = 2: the fragment is {X>0, X>1/2}; every live world reads X at
                      most 1/2; D_1 = 0 and the request is free
        day 2, k = 3: the fragment is {X>0, X>1/3, X>2/3}; a live world obeying
                      the same settlement reads X at 2/3; D_2 = 1/6 and the
                      request is charged

    Nothing was unsettled, no injunction changed, and the deficit rose.
    """
    X = v.x0()
    J = ceiling(X)
    view = v._std([("s", J)])
    days = (1, 2)
    stage = stage_with(X, days, settled=_at_most_half(X))
    return X, J, {n: run_day(n, stage, view) for n in days}


@lru_cache(maxsize=None)
def mesh_counterexample_with_growth():
    """The same, with the day-2 stage strictly larger than the day-1 stage.

    Day 2 additionally settles that the quantity is positive. Settlement is
    doing real work and the deficit still rises, because the cause is the mesh.

    The comparison is also worth naming precisely: the day-1 and day-2 live
    worlds are patterns over *different* fragments — `{X>0, X>1/2}` against
    `{X>0, X>1/3, X>2/3}` — so "the live-world set shrank" is not a well-formed
    premise for a cross-day comparison in the first place. Fixed-request
    monotonicity is a statement about one request and two nested assessments,
    and across days there is no one request.
    """
    X = v.x0()
    J = ceiling(X)
    view = v._std([("s", J)])
    days = (1, 2)
    early = _at_most_half(X)
    late = early + (X.luv.gt(Q(0)),)
    return X, J, {
        1: run_day(1, stage_with(X, days, settled=early), view),
        2: run_day(2, stage_with(X, days, settled=late), view),
    }


# ------------------------------------------------------- C. charged trajectories


def _run_schedule(X, J, days, stage_at, slack_at, volume_at, tolerance_at,
                  account) -> list:
    out = []
    view = v._std([("s", J)])
    for n in days:
        run = run_day(n, stage_at(n), view, slack=slack_at(n),
                      volume=volume_at(n), tolerance=tolerance_at(n),
                      account=account, label=f"day-{n}")
        out.append(run)
    return out


@lru_cache(maxsize=None)
def settlement_closes_the_gap(days=(0, 1, 2, 3), settle_from: int = 2,
                              capital: Q = Q(100)):
    """Settlement removes every excluded world from day `settle_from` on.

    Once the value is settled at `0`, no live world violates `Expect(X) <= 1/2`,
    so `D_t = 0`, `q_t = 0`, and the tail of the sum is exactly zero. The series
    converges because it is eventually zero — which is the strongest form the
    settlement route can take and the only one this round exhibits.
    """
    X = v.x0()
    J = ceiling(X)
    account = safety.OutflowAccount(Q(capital))
    grid = grid_for(days)
    settled = li.valued_at(X.luv, Q(0), max(days) + 1)

    def stage_at(n):
        if n < settle_from:
            return stage_with(X, days)
        return stage_with(X, days, settled=settled)

    runs = _run_schedule(X, J, days, stage_at, lambda n: Q(1, 100),
                         lambda n: Q(1), lambda n: Q(1, 10), account)
    return {"runs": runs, "account": account,
            "charges": [r.charged for r in runs]}


@lru_cache(maxsize=None)
def pressure_decays(days=(0, 1, 2, 3, 4), capital: Q = Q(100)):
    """The ordinary aggregate's bound decays; the deficit does not.

    `eps_t + M_t = 2^-t` against a deficit that stays positive and a tolerance
    fixed at `1`. This is the shape `FUNDING_AND_SAFETY.md` §9 uses to refute a
    depth-only limitative claim, run here through the real certificate: the
    charge is summable while the region excludes a live world at every date.
    """
    X = v.x0()
    J = ceiling(X)
    account = safety.OutflowAccount(Q(capital))
    runs = _run_schedule(
        X, J, days, lambda n: stage_with(X, days),
        lambda n: Q(1, 2 ** (n + 1)), lambda n: Q(1, 2 ** (n + 1)),
        lambda n: Q(1), account)
    return {"runs": runs, "account": account,
            "charges": [r.charged for r in runs]}


@lru_cache(maxsize=None)
def nothing_decays(days=(0, 1, 2, 3, 4), capital: Q = Q(12)):
    """Every factor is constant, so the charge is constant and the sum diverges.

    The account is deliberately small: the run exhibits the date at which
    quarantine fires, force is withheld, and no price is produced. That is the
    architecture's behaviour when the safety condition fails, and it is a
    withholding rather than a violation.
    """
    X = v.x0()
    J = ceiling(X)
    account = safety.OutflowAccount(Q(capital))
    runs = _run_schedule(X, J, days, lambda n: stage_with(X, days),
                         lambda n: Q(1, 100), lambda n: Q(1),
                         lambda n: Q(1, 10), account)
    return {"runs": runs, "account": account,
            "charges": [r.charged for r in runs]}


@lru_cache(maxsize=None)
def tolerance_route(days=(0, 1, 2, 3, 4, 5), capital: Q = Q(1000)):
    """Loosening the tolerance, and where that route stops.

    `delta_t` rises to its ceiling of `1` and can go no further: a conformance
    promise of more than `1` says nothing about a price in `[0, 1]`, and
    `force_api.compile_safe_force` defaults its relaxation ceiling to `1` for
    that reason. The run shows the charge falling while the tolerance loosens
    and then going **constant** once the ceiling is reached, so the tail is a
    constant series and the sum diverges. This route buys a bounded factor and
    then stops.

    The consequence, stated as an inequality rather than a claim about the
    corpus: while `delta_t <= 1`,

        q_t  =  (eps_t + M_t) * D_t / delta_t  >=  (eps_t + M_t) * D_t ,

    so `sum_t q_t < inf` requires `sum_t (eps_t + M_t) * D_t < inf`. Tolerance
    alone cannot make a divergent product converge.
    """
    X = v.x0()
    J = ceiling(X)
    account = safety.OutflowAccount(Q(capital))
    runs = _run_schedule(
        X, J, days, lambda n: stage_with(X, days), lambda n: Q(1, 100),
        lambda n: Q(1), lambda n: min(Q(1), Q(1, 8) * 2 ** n), account)
    return {"runs": runs, "account": account,
            "charges": [r.charged for r in runs]}


def partial_sums(charges: Sequence) -> list:
    out, running = [], Q(0)
    for c in charges:
        running += c.charge
        out.append(running)
    return out
