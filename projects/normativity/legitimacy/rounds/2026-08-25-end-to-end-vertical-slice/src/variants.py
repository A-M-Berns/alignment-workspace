"""Adversarial mutations of the canonical toy, one per boundary under test.

Each builder here sets up a case and returns the object the boundary produces —
a run, an exception, a non-exposure, a certificate. The tests then assert *which*
boundary refused it, because the interesting result is not that a bad case fails
but where.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Optional

import li
from epistemic import (RawOutcome, SettlementReading, SettlementSemantics,
                       Stage, deductive_entries)
from pipeline import run_day
from standing import PValue
from toy import GRID, PHI, Trajectory, j0, registry, x0, x1
from waist import (CertifiedLUV, Expect, Ineq, Injunction, MalformedInjunction,
                   NonExposure, Prob, ValueRegistry, ValueSpec, kappa,
                   luv_exposure, refusing)

Q = Fraction


def _std(pairs) -> dict:
    """A bare normative view carrying the given injunctions, for a run.

    The pipeline reads standing, not a history, so a variant that is about the
    compiler rather than about the record supplies the view directly.
    """
    from ri_core import ACTIVE, PForce, StandingState
    return {sid: StandingState(ACTIVE, frozenset(),
                               PForce("commit", "schema", J))
            for sid, J in pairs}


def _chain(*luvs) -> tuple:
    out = ()
    for X in luvs:
        out += li.threshold_chain(X.luv, GRID)
    return deductive_entries(out, note="threshold coherence")


def base_stage(*luvs) -> Stage:
    return Stage.of(_chain(*luvs))


# ------------------------------------------------------------ value layer


def failed_query() -> NonExposure:
    """A query the specification cannot compile to a legitimate LUV."""
    return registry().compile_value("v0", "incomparable")


def unknown_query() -> NonExposure:
    return registry().compile_value("v0", "no-such-query")


def unbounded_exposure() -> NonExposure:
    """An exposure whose certified values leave `[0,1]`: refused at the waist."""
    reg = ValueRegistry()
    reg.admit(ValueSpec("vbad", {}, (
        ("q", luv_exposure("thresholds-bad", {"low": Q(0), "high": Q(3, 2)})),)))
    return reg.compile_value("vbad", "q")


def two_active_specs() -> dict:
    """Two value specifications active at once, both exposing LUVs.

    Neither is privileged and neither shadows the other: the quantities are
    named after their own specifications, so both are available and no rule is
    needed to pick between them.
    """
    reg = ValueRegistry()
    reg.admit(ValueSpec("vA", {}, (
        ("q", luv_exposure("t-A", {"low": Q(0), "high": Q(1)})),)))
    reg.admit(ValueSpec("vB", {}, (
        ("q", luv_exposure("t-B", {"low": Q(0), "high": Q(1)})),)))
    return {"registry": reg,
            "XA": reg.compile_value("vA", "q"),
            "XB": reg.compile_value("vB", "q")}


def rewriting_a_frozen_spec() -> Exception:
    """Re-admitting a specification id is refused, which is the rigidity."""
    reg = registry()
    try:
        reg.admit(ValueSpec("v0", {"about": "a rewrite"}, ()))
    except ValueError as exc:
        return exc
    raise AssertionError("a frozen specification was rewritten")


# ------------------------------------------------------- plural value


def plural_value() -> dict:
    """Three dimensions of plural value, exposed as three LUVs.

    No scalarisation anywhere: the specification exposes three observables, and
    the operative layer constrains them separately. Incomparability is preserved
    by there being no injunction that trades them off.
    """
    reg = ValueRegistry()
    reg.admit(ValueSpec("vp", {}, tuple(
        (dim, luv_exposure(f"t-{dim}", {"low": Q(0), "high": Q(1)}))
        for dim in ("safety", "usefulness", "cost"))))
    return {"registry": reg,
            "dims": {d: reg.compile_value("vp", d)
                     for d in ("safety", "usefulness", "cost")}}


def plural_separate_ceilings():
    """Each dimension gets its own ceiling; nothing is added across them."""
    dims = plural_value()["dims"]
    J = Injunction("Jplural", tuple(
        Ineq(((Q(1), Expect(X)),), rhs=Q(3, 4), label=f"{d}-ceiling")
        for d, X in sorted(dims.items())))
    return dims, J


def plural_affine_tradeoff():
    """One inequality mixing the dimensions: a declared rate of exchange.

    Representable, and the point is that it is *declared* rather than inherent.
    The value layer did not scalarise; an injunction chose a tradeoff, and the
    normative event that issued it is answerable for that choice.
    """
    dims = plural_value()["dims"]
    J = Injunction("Jtradeoff", (
        Ineq(((Q(2), Expect(dims["safety"])),
              (Q(-1), Expect(dims["cost"]))),
             rhs=Q(7, 10), label="declared-exchange-rate"),))
    return dims, J


# --------------------------------------------------------- malformed


def empty_injunction() -> Injunction:
    return Injunction("Jempty", ())


def constant_false_injunction() -> Injunction:
    return Injunction("Jfalse", (Ineq((), const=Q(1), rhs=Q(0)),))


def constant_true_injunction() -> Injunction:
    return Injunction("Jtrue", (Ineq((), const=Q(0), rhs=Q(1)),))


def float_coefficient_injunction() -> Injunction:
    X = x0()
    return Injunction("Jfloat", (Ineq(((0.5, Expect(X)),), rhs=Q(1, 2)),))


def self_inconsistent_injunction() -> Injunction:
    """One payload demanding a quantity be both above and below."""
    X = x0()
    return Injunction("Jself", (
        Ineq(((Q(1), Expect(X)),), rhs=Q(1, 4), label="ceiling"),
        Ineq(((Q(-1), Expect(X)),), rhs=Q(-3, 4), label="floor"),
    ))


# ------------------------------------------------------------ conflicts


def empty_intersection(day: int = 2):
    """Two individually satisfiable injunctions with no common price."""
    X = x0()
    low = Injunction("Jlow", (
        Ineq(((Q(1), Expect(X)),), rhs=Q(1, 4), label="ceiling"),))
    high = Injunction("Jhigh", (
        Ineq(((Q(-1), Expect(X)),), rhs=Q(-3, 4), label="floor"),))
    return run_day(day, base_stage(X), _std([("s:low", low), ("s:high", high)]))


def incompatible_with_deduction(day: int = 2):
    """A satisfiable region whose intersection with `K^D` is empty.

    The stage settles the exposed quantity at `1`, so every stage-consistent
    world holds every threshold and `K^D` is the single point `(1,1,1)`. An
    injunction capping the expectation strictly below `1` is then satisfiable in
    the cube and unsatisfiable against deduction.
    """
    X = x0()
    stage = Stage.of(_chain(X),
                     deductive_entries(li.valued_at(X.luv, Q(1), 3),
                                       note="the quantity is settled at 1"))
    J = Injunction("Jcap", (
        Ineq(((Q(1), Expect(X)),), rhs=Q(1, 2), label="ceiling"),))
    return run_day(day, stage, _std([("s:cap", J)]))


def unsatisfiable_stage(day: int = 2):
    """A stage no world satisfies, from two settlements that conflict.

    Nothing downstream fails: the pinned
    `isLogicalInductor_of_stage_unsatisfiable` makes the criterion hold
    vacuously over such a process, so the guarantees go quiet rather than
    breaking. The pipeline reports the state because nothing else would.
    """
    X = x0()
    sem = SettlementSemantics()
    sem.admit(SettlementReading("l:up", "o:1", (X.luv.gt(Q(2, 3)),),
                                "the readout was high"))
    sem.admit(SettlementReading("l:down", "o:2", (li.Neg(X.luv.gt(Q(1, 3))),),
                                "the recount was low"))
    stage = Stage.of(_chain(X), sem.entries(["l:up", "l:down"]))
    J = Injunction("Jcap", (
        Ineq(((Q(1), Expect(X)),), rhs=Q(1, 2), label="ceiling"),))
    return run_day(day, stage, _std([("s:cap", J)])), stage


def settlement_against_deduction(day: int = 2):
    """A settlement whose content contradicts the deductive channel.

    Threshold coherence is deductive; a settlement affirming `X > 2/3` while
    denying `X > 1/3` contradicts it. The stage is unsatisfiable and the sources
    are attributable, which is all the architecture claims: no contradiction is
    repaired, and neither channel wins.
    """
    X = x0()
    sem = SettlementSemantics()
    sem.admit(SettlementReading(
        "l:bad", "o:3",
        (X.luv.gt(Q(2, 3)), li.Neg(X.luv.gt(Q(1, 3)))),
        "a reading incompatible with the quantity's own coherence"))
    stage = Stage.of(_chain(X), sem.entries(["l:bad"]))
    J = Injunction("Jcap", (
        Ineq(((Q(1), Expect(X)),), rhs=Q(1, 2), label="ceiling"),))
    return run_day(day, stage, _std([("s:cap", J)])), stage


# ------------------------------------------------------ settlement layer


def uninterpreted_outcome() -> dict:
    """A raw observation with no exact reading yet.

    It enters the ledger with its provenance and denotes nothing, so it
    eliminates no world. That is the settlement-side counterpart of a value
    query that compiles to no LUV, and it is a state rather than a failure.
    """
    X = x0()
    outcome = RawOutcome("o:ambiguous", "the operator said it looked fine")
    sem = SettlementSemantics()
    reading = sem.admit(SettlementReading(
        "l:ambiguous", outcome.id, (),
        "no exact account of what was settled is available yet"))
    stage = Stage.of(_chain(X), sem.entries(["l:ambiguous"]))
    return {"outcome": outcome, "reading": reading, "stage": stage,
            "baseline": base_stage(X)}


def rewriting_a_settlement() -> Exception:
    sem = SettlementSemantics()
    sem.admit(SettlementReading("l:one", "o:1", (li.Atom("a"),)))
    try:
        sem.admit(SettlementReading("l:one", "o:1", (li.Atom("b"),)))
    except ValueError as exc:
        return exc
    raise AssertionError("a settlement denotation was rewritten")


def unrelated_language_extension(day: int = 1):
    """Growth of the LI language away from the fragment changes nothing.

    New atoms, new stage sentences about them, and a new settlement mentioning
    only them. The day's coordinates, rows, deductive vertices and enforced
    region must all be identical to the run without them.
    """
    X = x0()
    J = j0(X)
    view = _std([("s:J0", J)])
    before = run_day(day, base_stage(X), view)

    sem = SettlementSemantics()
    sem.admit(SettlementReading(
        "l:unrelated", "o:unrelated",
        (li.Atom("weather"), li.Implies(li.Atom("weather"), li.Atom("umbrella"))),
        "about something else entirely"))
    grown = Stage.of(_chain(X),
                     deductive_entries((li.Atom("tide"),), note="unrelated"),
                     sem.entries(["l:unrelated"]))
    after = run_day(day, grown, view)
    return before, after


def old_settlement_stays_rigid():
    """An old settlement's denotation is unchanged by later language growth."""
    X = x0()
    sem = SettlementSemantics()
    sem.admit(SettlementReading("l:old", "o:old", (X.luv.gt(Q(1, 3)),),
                                "the first reading"))
    early = sem.sem("l:old")
    sem.admit(SettlementReading("l:new", "o:new", (li.Atom("newly-nameable"),),
                                "vocabulary that did not exist before"))
    return early, sem.sem("l:old")


# ------------------------------------------------- reflective / future price


def reflective_luv() -> CertifiedLUV:
    """A LUV whose thresholds are sentences about a later day's price.

    The waist does not notice: `Expect` takes a `CertifiedLUV`, and this is one.
    What a reflective quantity needs is exactly what any LUV needs — a threshold
    family with an efficiency witness and a world-value presentation — and
    supplying those is upstream work, not a widening.
    """
    from li import LUV
    return CertifiedLUV(
        luv=LUV("X[reflect:P_{n+1}(phi)]"),
        code_witness="thresholds-reflective",
        values=(("low", Q(0)), ("high", Q(1))),
        origin=("reflect", "P_{n+1}(phi)"))


def reflective_injunction(day: int = 1):
    """A frozen injunction over a reflective LUV, run like any other."""
    X = reflective_luv()
    J = Injunction("Jreflect", (
        Ineq(((Q(1), Expect(X)),), rhs=Q(1, 2), label="future-price-ceiling"),))
    return run_day(day, base_stage(X), _std([("s:reflect", J)]))


# ------------------------------------------------- traderization boundary


def syntactically_fine_but_inadmissible(day: int = 1):
    """A payload that passes every syntactic check and fails admissibility.

    This is the standing case rather than an exotic one: any injunction that
    moves the region at all lands here.
    """
    X = x0()
    J = Injunction("Jordinary", (
        Ineq(((Q(1), Expect(X)),), rhs=Q(1, 2), label="ceiling"),))
    return run_day(day, base_stage(X), _std([("s:ord", J)]))


def inert_injunction(day: int = 1):
    """An injunction that every stage-consistent world already satisfies.

    `Expect(X) <= 1` is implied by the LUV being a `[0,1]` quantity, so no world
    violates it, admissibility passes — and the enforced region is exactly
    `K^D`. The two facts are the same fact.
    """
    X = x0()
    J = Injunction("Jinert", (
        Ineq(((Q(1), Expect(X)),), rhs=Q(1), label="trivial-ceiling"),))
    return run_day(day, base_stage(X), _std([("s:inert", J)]))


def frozen_injunction_across_days(days=(0, 1, 2, 3)):
    """One frozen payload, compiled at several days.

    The syntax does not move; the low-level realization does, because `E_n(X)`
    is the precision-`n+1` threshold bundle. What is asked for is whether the
    compiled constraint means the same thing, and the answer this returns is the
    evidence for it.
    """
    X = x0()
    J = Injunction("Jfrozen", (
        Ineq(((Q(1), Expect(X)), (Q(-1), Prob(PHI))), rhs=Q(1, 5),
             label="mixed"),))
    view = _std([("s:frozen", J)])
    return X, J, {n: run_day(n, base_stage(X), view) for n in days}
