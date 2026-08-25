"""The day-`n` pipeline, from operative standing to a resulting cognitive state.

    N_n  ->  O_n  ->  kappa_n  ->  K^N_n  ->  K_n = K^D_n ∩ K^N_n  ->  trader  ->  P_n

Each stage is a separate function returning a separate object, and the run
record keeps all of them, because the point of the slice is to be able to point
at which stage refused a bad case.

Two channels stay independent up to the composition step: the epistemic
substrate produces `K^D_n` from `Sigma_n` and never reads an injunction, and the
operative projection produces `K^N_n` from active standing and never reads a
world. They meet once, at an intersection.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Optional, Sequence

import conflict
import geometry
import safety
from conflict import (Infeasible, cube_constraints, decide, from_rows,
                      hull_system)
from epistemic import Stage, admissible_patterns, pc_worlds, stage_satisfiable
from li import ONE, ZERO, payout
from waist import (Compiled, Expect, Injunction, MalformedInjunction, Prob,
                   coordinates_for, kappa)


# ----------------------------------------------- N -> O, keeping the identity


def operative_projection(std: dict) -> tuple:
    """`O_n = {(i, J_i) : i is active standing carrying an injunction}`.

    Deliberately boring, and deliberately paired. Reflective Integrity's own
    projection is `O_t = { compiledClause p : ... }`, a set of clauses with the
    standing dropped; two distinct active standings carrying equal payloads
    collapse in it, and nothing in it can be walked back to the event that
    issued it. Enforcement provenance and per-term conflict attribution both
    need the identity, so the projection consumed here is the graph rather than
    the image.

    `std` is a normative view: `standing_id -> state` with `.kind` and
    `.payload`. Nothing is reinterpreted, nothing is dropped for infeasibility,
    nothing is prioritised, and no injunction is optimised away.
    """
    out = []
    for x, state in sorted(std.items()):
        if state.kind != "Active":
            continue
        payload = state.payload
        clause = getattr(payload, "clause", None)
        if isinstance(clause, Injunction):
            out.append((x, clause))
    return tuple(out)


# ------------------------------------------------------------- conflict states


@dataclass(frozen=True)
class ConflictReport:
    """Which of the three states holds, with the certificate for it."""

    malformed: tuple = ()             # (standing_id, message)
    self_inconsistent: tuple = ()     # (standing_id, Infeasible)
    normatively_empty: Optional[Infeasible] = None
    deductively_empty: bool = False
    incompatible: Optional[Infeasible] = None

    @property
    def state(self) -> str:
        if self.malformed:
            return "A-malformed"
        if self.self_inconsistent:
            return "A-self-inconsistent"
        if self.normatively_empty is not None:
            return "B-empty-intersection"
        if self.deductively_empty:
            return "D-stage-unsatisfiable"
        if self.incompatible is not None:
            return "C-incompatible-with-deduction"
        return "none"

    @property
    def blocking(self) -> bool:
        return self.state != "none"


# ---------------------------------------------------------- the day's record


@dataclass
class DayRun:
    day: int
    stage: Stage
    projection: tuple
    coords: tuple = ()
    compiled: Optional[Compiled] = None
    deductive_vertices: tuple = ()
    region_vertices: tuple = ()
    conflict: ConflictReport = field(default_factory=ConflictReport)
    obligations: tuple = ()
    live_worlds: tuple = ()
    excluded_worlds: tuple = ()
    charged: Optional["safety.Charged"] = None
    prices: tuple = ()
    readings: tuple = ()

    @property
    def sharp_deficit(self) -> Fraction:
        """`D_t`, the billed aggregate: `max over live omega of sum_j d_j(omega)`.

        The one quantity the safety theorem is stated against. Read off the
        canonical certificate rather than recomputed here.
        """
        return ZERO if self.charged is None else self.charged.sharp

    @property
    def charge(self) -> Optional[Fraction]:
        """`q_t = (eps_t + M_t) * D_t / delta_t`, or `None` if nothing ran."""
        return None if self.charged is None else self.charged.charge

    @property
    def enforced(self) -> bool:
        return bool(self.region_vertices) and not self.conflict.blocking

    def obligation(self, name: str):
        for o in self.obligations:
            if o.name == name:
                return o
        raise KeyError(name)


@dataclass(frozen=True)
class Obligation:
    """One hypothesis of the traderization interface, and its verdict here.

    `source` names the declaration or function that actually asks for it, so a
    reader can check that the obligation is the real one and not a paraphrase.
    """

    name: str
    source: str
    verdict: str                      # "pass" | "fail" | "declared" | "n/a"
    detail: str = ""


# ------------------------------------------------------------------ the run


def run_day(day: int, stage: Stage, std: dict,
            tolerance: Fraction = Fraction(1, 10),
            slack: Fraction = Fraction(1, 100),
            volume: Fraction = ONE,
            prior: Optional[Sequence[Fraction]] = None,
            schedule_declared_computable: bool = True,
            account=None, policy: str = "quarantine",
            label: str = "", observe: bool = False) -> DayRun:
    """One day of the slice, end to end.

    `stage` is `Sigma_n`; `std` is the normative view at the corresponding RI
    state. The two arrive separately and are never derived from each other.

    `observe=True` computes what the day's force would cost and emits none:
    no account is consulted, no position is constructed, and no price is
    produced. That is the path a machine takes to *read* its own liability
    pressure, and it is deliberately not the path that exercises force.

    `account` is the enforcement channel's `OutflowAccount`. A day whose charge
    the account cannot fund emits no force under the default `quarantine`
    policy, and then no price is produced: the market is not updated by a
    request that was never paid for. Passing no account supplies a large one, so
    that a caller studying geometry is not silently studying affordability.
    """
    projection = operative_projection(std)
    run = DayRun(day=day, stage=stage, projection=projection)

    malformed = []
    wellformed = []
    for standing_id, J in projection:
        try:
            J.check_wellformed()
        except MalformedInjunction as exc:
            malformed.append((standing_id, str(exc)))
        else:
            wellformed.append((standing_id, J))
    if malformed:
        run.conflict = ConflictReport(malformed=tuple(malformed))
        return run

    run.coords = coordinates_for(wellformed, day)
    run.compiled = kappa(wellformed, day, run.coords)
    d = len(run.coords)

    self_bad = []
    for standing_id, J in wellformed:
        one = kappa([(standing_id, J)], day, run.coords)
        cert = decide(from_rows(one.rows, d) + cube_constraints(d), d)
        if cert is not None:
            self_bad.append((standing_id, cert))
    if self_bad:
        run.conflict = ConflictReport(self_inconsistent=tuple(self_bad))
        return run

    joint = decide(from_rows(run.compiled.rows, d) + cube_constraints(d), d)
    if joint is not None:
        run.conflict = ConflictReport(normatively_empty=joint)
        return run

    if not stage_satisfiable(stage):
        run.conflict = ConflictReport(deductively_empty=True)
        return run

    run.deductive_vertices = tuple(admissible_patterns(stage, run.coords))
    if not run.deductive_vertices:
        run.conflict = ConflictReport(deductively_empty=True)
        return run

    cons, m = hull_system(run.compiled.rows, run.deductive_vertices)
    meet = decide(cons, m)
    if meet is not None:
        run.conflict = ConflictReport(incompatible=meet)
        return run

    run.region_vertices = tuple(
        geometry.generate_region(run.deductive_vertices, run.compiled.rows))

    run.live_worlds = _live_worlds(stage, run.coords)
    run.excluded_worlds = _excluded(run)
    if observe:
        run.charged = safety.observe(run.compiled, run.live_worlds, day,
                                     slack=slack, volume=volume,
                                     tolerance=tolerance)
    else:
        run.charged = safety.charge_force(
            run.compiled, run.live_worlds, day, run.region_vertices[0],
            account if account is not None
            else safety.OutflowAccount(Fraction(10 ** 6)),
            slack=slack, volume=volume, tolerance=tolerance, policy=policy,
            label=label or f"day-{day}")
    run.obligations = _obligations(run, tolerance, schedule_declared_computable)

    if prior is not None and run.charged.emitted:
        run.prices = tuple(geometry.project_onto(prior, run.region_vertices))
        run.readings = _readings(run)
    return run


def _live_worlds(stage: Stage, coords: tuple) -> tuple:
    """The assessment state: `PC(Sigma_n)` restricted to the day's fragment.

    One entry per distinct pattern. A stage world and its fragment restriction
    are different objects, and it is the restriction the rows are evaluated at,
    so two full worlds agreeing on the fragment are one live world here.
    """
    seen: list = []
    for world in pc_worlds(stage, coords):
        point = tuple(payout(world, phi) for phi in coords)
        if point not in seen:
            seen.append(point)
    return tuple(seen)


def _excluded(run: DayRun) -> tuple:
    """The live worlds the rows exclude, with each one's *total* row deficit.

    The per-world number here is `sum_j d_j(omega)`, which is the quantity the
    sharp aggregate maximises over — not the per-row worst, which belongs to the
    conservative aggregate and is a different number. Reported for inspection;
    the billed figure is the certificate's, never this loop's.
    """
    out = []
    for point in run.live_worlds:
        total = sum((row.violation(point) for row in run.compiled.rows), ZERO)
        if total > ZERO:
            out.append((point, total))
    return tuple(out)


def _obligations(run: DayRun, tolerance: Fraction,
                 declared_computable: bool) -> tuple:
    """The traderization interface's hypotheses, checked one at a time.

    Every `source` here names something that exists: a field of
    `RationalConstraintSchedule`, a precondition of `force_api.compile_force`,
    or the admissibility hypothesis of `end_to_end_of_constraints_effective`.
    """
    d = len(run.coords)
    out = [
        Obligation(
            "priceable", "ConstraintSchedule.RationalConstraintSchedule.coords",
            "pass",
            f"{d} coordinates, each a sentence the market prices"),
        Obligation(
            "nodup", "RationalConstraintSchedule.nodup",
            "pass" if len(set(run.coords)) == d else "fail",
            "each priced sentence listed once"),
        Obligation(
            "tol_pos", "RationalConstraintSchedule.tol_pos",
            "pass" if Fraction(tolerance) > ZERO else "fail",
            f"tolerance {tolerance}"),
        Obligation(
            "nonempty", "RationalPolytope.verts_ne / force_api.compile_force",
            "pass" if run.region_vertices else "fail",
            f"{len(run.region_vertices)} generating vertices"),
    ]
    in_cube = all(ZERO <= x <= ONE for v in run.region_vertices for x in v)
    out.append(Obligation(
        "region_in_cube", "RationalConstraintSchedule.region_in_cube",
        "pass" if in_cube else "fail",
        "generating vertices are credences"))
    out.append(Obligation(
        "effective_presentation", "RationalConstraintSchedule.Computation",
        "declared" if declared_computable else "fail",
        "coords, tol and vertex data as computable functions of the date; "
        "declared by the schedule's construction, not proved here"))
    admissible = not run.excluded_worlds
    out.append(Obligation(
        "admissibility",
        "EffectiveRepresentation.end_to_end_of_constraints_effective, hadm",
        "pass" if admissible else "fail",
        "every live world satisfies the region; D_t = 0 and force is free"
        if admissible else
        f"{len(run.excluded_worlds)} of {len(run.live_worlds)} live worlds "
        f"excluded; sharp deficit D_t = {run.sharp_deficit}"))
    c = run.charged
    if admissible:
        out.append(Obligation(
            "bounded_liability", "force_api.compile_safe_force / outflow account",
            "n/a", "unused: the unconditional branch applies"))
    elif c is not None and c.observed:
        out.append(Obligation(
            "bounded_liability", "safety.observe / price_request",
            "n/a",
            f"not evaluated: this is an observation of what force would cost "
            f"(q_t = {c.charge}), and no account was consulted"))
    elif c is not None and c.emitted:
        out.append(Obligation(
            "bounded_liability", "force_api.compile_safe_force / outflow account",
            "pass",
            f"charged q_t = {c.charge} against the account and emitted; the "
            f"holder may quote the lifetime ceiling {c.safety_bound} as B. "
            f"That sum_t q_t stays finite is the source's obligation and is "
            f"established for nothing here"))
    else:
        out.append(Obligation(
            "bounded_liability", "force_api.compile_safe_force / outflow account",
            "fail",
            (c.withheld if c is not None else "no charge was attempted")
            + "; force is withheld and no price is produced"))
    return tuple(out)


def _readings(run: DayRun) -> tuple:
    """What the resulting price vector says about each cognitive quantity."""
    prices = dict(zip(run.coords, run.prices))
    seen: list = []
    out: list = []
    for _, J in run.projection:
        for ineq in J.ineqs:
            for _, q in ineq.atoms:
                if q in seen:
                    continue
                seen.append(q)
                if isinstance(q, Prob):
                    out.append((repr(q), prices[q.phi]))
                else:
                    out.append((repr(q), q.x.luv.expect(prices, run.day)))
    return tuple(out)


# ------------------------------------------------- the inertness dichotomy


def deductively_inert(run: DayRun) -> bool:
    """Whether the operative region changes nothing at this day.

    True exactly when every deductive vertex satisfies every compiled row —
    which, `K^N_n` being an intersection of half-spaces and therefore convex,
    gives `K^D_n subset K^N_n` and hence `K_n = K^D_n`.

    This is the same condition as the `admissibility` obligation, and that they
    coincide is the round's central negative result: an injunction is inside the
    unconditional traderization theorem's hypothesis exactly when it makes no
    difference to the prices.
    """
    return all(all(row.slack(v) >= ZERO for row in run.compiled.rows)
               for v in run.deductive_vertices)
