"""The settlement interface as a formal object, and the parametric composite.

Folder-local; readable against `THEORY_11` and `THEORY_12` alone.

Vocabulary. Following the monograph, an engine supplies **reports** (what it
writes), **timing** (when), and **enforcement** (the weight behind what it
writes). The clause letters J, C, P, T are frozen opaque identifiers -- they are
entrenched in the reading audit, the mapping table, and this module's predicate
names -- and the prose carries the real names. See `GLOSSARY.md`.

Each clause is one predicate of exactly one kind. **Checkable**: a computable
predicate over declared engine data and a finite record prefix, returning
obstructions. **Declared**: a hypothesis object carrying its own statement,
holding exactly when a matching object is supplied. An engine satisfying the
interface has been checked *plus* a printed list of what nobody checked.
"""

from __future__ import annotations

from dataclasses import dataclass, field, fields
from fractions import Fraction as Q
from typing import Mapping, Sequence

from src.coherence import Layering, Prices, Schedule, attribute, incoherence
from src.core import clipping_adapter
from src.interval import Book, Language, SettledFact

LOGICAL = "logical"
EMPIRICAL = "empirical"
CHECKABLE = "checkable"
DECLARED = "declared"
REFUSAL = "refusal"
BOUNDED_BUDGETS = "bounded-budgets"
MEANS = (REFUSAL, BOUNDED_BUDGETS)
PRECOMMITTED = "precommitted"
ANYTIME_VALID = "anytime-valid"


# --------------------------------------------------------------------------
# Record citizens
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Procedure:
    procedure_id: str
    channel: str
    outcome_space: tuple[str, ...]
    owner: str
    horizon: int | None = None

    def well_formed(self) -> bool:
        if self.channel not in (LOGICAL, EMPIRICAL) or len(set(self.outcome_space)) < 2:
            return False
        if self.channel == EMPIRICAL:
            return self.horizon is not None and self.horizon >= 0
        return self.horizon is None


def report_variable(procedure_id: str, date: int) -> str:
    return f"X[{procedure_id}@{date}]"


@dataclass(frozen=True)
class Settlement:
    """A dated settlement event. No basis, no stake, no charge, no objection surface."""

    variable_id: str
    procedure_id: str
    date: int
    value: str
    funder_profile: tuple[str, ...] = ()
    derivation: str | None = None
    era: int = 0


@dataclass(frozen=True)
class RequestKey:
    """Names a question, never an outcome. There is no field for an outcome."""

    target: str
    procedure_id: str
    funder_id: str
    requested_date: int
    scheduled_date: int


def key_fields() -> tuple[str, ...]:
    return tuple(f.name for f in fields(RequestKey))


def key_from_intent(target: str, procedure_id: str, funder_id: str,
                    requested_date: int, scheduled_date: int,
                    intended_outcome: str) -> RequestKey:
    """The intended outcome is the one argument with no field to land in."""
    del intended_outcome
    return RequestKey(target, procedure_id, funder_id, requested_date, scheduled_date)


def directional_variants(key: RequestKey,
                         outcome_space: Sequence[str]) -> frozenset[RequestKey]:
    return frozenset(
        key_from_intent(key.target, key.procedure_id, key.funder_id,
                        key.requested_date, key.scheduled_date, o)
        for o in (tuple(outcome_space) or ("",)))


@dataclass(frozen=True)
class Request:
    request_id: str
    key: RequestKey
    subsidy: Q
    stopping_rule: str = PRECOMMITTED
    declared_stop: int | None = None
    executed_date: int | None = None
    settled_variable: str | None = None


@dataclass(frozen=True)
class Position:
    actor_id: str
    target: str
    date: int
    fresh: bool = True


@dataclass(frozen=True)
class Query:
    query_id: str
    admitted_date: int
    deadline: int
    upstream: tuple[str, ...] = ()
    service_work: Q = Q(1)
    ripe: bool = True
    tolled: bool = False
    liability: Q = Q(0)


@dataclass(frozen=True)
class Docket:
    capacity: Q = Q(1)
    queries: tuple[Query, ...] = ()


@dataclass(frozen=True)
class Eras:
    boundaries: tuple[int, ...] = ()
    translations: tuple[tuple[str, str], ...] = ()

    def era_of(self, date: int) -> int:
        return sum(1 for b in self.boundaries if date >= b)


@dataclass(frozen=True)
class PricedState:
    date: int
    language: Language
    book: Book
    settled: tuple[SettledFact, ...] = ()
    prices: Prices | None = None


@dataclass(frozen=True)
class Breach:
    date: int
    layering: Layering
    realized: Q
    party: str
    tolled: bool
    chargeable: bool


@dataclass(frozen=True)
class Record:
    """A finite record prefix: everything the checkable clauses read."""

    horizon: int = 0
    settlements: tuple[Settlement, ...] = ()
    requests: tuple[Request, ...] = ()
    positions: tuple[Position, ...] = ()
    docket: Docket = field(default_factory=Docket)
    eras: Eras = field(default_factory=Eras)
    priced_states: tuple[PricedState, ...] = ()
    breaches: tuple[Breach, ...] = ()
    live_instruments: tuple[tuple[int, int], ...] = ()
    worst_case_exposure: Q = Q(0)


@dataclass(frozen=True)
class Declaration:
    """Everything the engine puts on the public record about itself."""

    engine_id: str
    procedures: tuple[Procedure, ...]
    tolerance: Schedule
    certificate_type: str | None = None
    downside_limit: Q | None = None
    downside_means: str | None = None
    core_minimum: Q | None = None
    gating_capacity: int | None = None
    overtaking_bound: int | None = None
    logical_jurisdiction: tuple[str, ...] = ()

    @property
    def by_id(self) -> Mapping[str, Procedure]:
        return {p.procedure_id: p for p in self.procedures}


@dataclass(frozen=True)
class Hypothesis:
    """A clause nobody checked, carrying its own statement."""

    hypothesis_id: str
    clause: str
    statement: str
    declared_by: str


@dataclass(frozen=True)
class Verdict:
    clause: str
    kind: str
    holds: bool
    obstructions: tuple[str, ...] = ()
    leaned_on: tuple[str, ...] = ()


def _v(clause: str, kind: str, obstructions: Sequence[str],
       leaned_on: Sequence[str] = ()) -> Verdict:
    return Verdict(clause, kind, not obstructions, tuple(obstructions), tuple(leaned_on))


def _declared(clause: str, hypotheses: Sequence[Hypothesis], detail: str) -> Verdict:
    for h in hypotheses:
        if h.clause == clause:
            return Verdict(clause, DECLARED, True, (), (h.hypothesis_id,))
    return Verdict(clause, DECLARED, False, (f"no hypothesis object declares {detail}",))


# --------------------------------------------------------------------------
# Clause predicates
# --------------------------------------------------------------------------


def J1(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Declared settleable class: procedures, outcome spaces, channels, horizons."""
    obs = []
    known = d.by_id
    for p in d.procedures:
        if not p.well_formed():
            obs.append(f"procedure {p.procedure_id!r} is not well declared")
    for s in r.settlements:
        p = known.get(s.procedure_id)
        if p is None:
            obs.append(f"{s.variable_id!r} names an undeclared procedure")
            continue
        if s.value not in p.outcome_space:
            obs.append(f"{s.variable_id!r} carries a value outside its outcome space")
        if s.variable_id != report_variable(s.procedure_id, s.date):
            obs.append(f"{s.variable_id!r} is not its procedure-and-date variable")
    return _v("J1", CHECKABLE, obs)


def J2(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Write-once, owner-only. A second settlement is a jurisdiction violation."""
    obs = []
    seen: set[str] = set()
    known = d.by_id
    for s in r.settlements:
        if s.variable_id in seen:
            obs.append(f"{s.variable_id!r} is settled twice: a jurisdiction violation "
                       "routed to the breach stack")
            continue
        seen.add(s.variable_id)
        p = known.get(s.procedure_id)
        if p is not None and p.owner != d.engine_id:
            obs.append(f"{s.variable_id!r} was written by a non-owning engine")
    return _v("J2", CHECKABLE, obs)


def J3(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Transport under migration: bridge, never re-settle."""
    obs = []
    translation = dict(r.eras.translations)
    settled_ids = {s.variable_id for s in r.settlements}
    for s in r.settlements:
        if s.era != r.eras.era_of(s.date):
            obs.append(f"{s.variable_id!r} records an era its date contradicts")
        image = translation.get(s.variable_id)
        if image is not None and image in settled_ids:
            obs.append(f"{s.variable_id!r} is re-spoken as {image!r} in the new "
                       "vocabulary rather than bridged")
    return _v("J3", CHECKABLE, obs)


def C1_logical(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Completeness over the decidable fragment. Declared: no prefix decides it."""
    verdict = _declared("C1-logical", h,
                        "eventual decision of the declared logical jurisdiction")
    if verdict.holds and not d.logical_jurisdiction and any(
            p.channel == LOGICAL for p in d.procedures):
        return Verdict("C1-logical", DECLARED, False,
                       ("a logical procedure is declared with an empty jurisdiction, "
                        "so the hypothesis has no content",))
    return verdict


def C1_empirical(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Funding-responsive completeness, checkable in exactly its conditional form."""
    obs = []
    known = d.by_id
    settled_ids = {s.variable_id for s in r.settlements}
    for p in d.procedures:
        if p.channel == EMPIRICAL and p.horizon is None:
            obs.append(f"empirical procedure {p.procedure_id!r} declares no horizon")
    for req in r.requests:
        p = known.get(req.key.procedure_id)
        if p is None or p.channel != EMPIRICAL or req.executed_date is None:
            continue
        due = req.executed_date + (p.horizon or 0)
        if due <= r.horizon and req.settled_variable not in settled_ids:
            obs.append(f"request {req.request_id!r} was funded and run, its horizon "
                       f"elapsed at {due}, and nothing settles it")
    return _v("C1-empirical", CHECKABLE, obs)


def C2(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Ripeness and tolling."""
    obs = []
    known = d.by_id
    for q in r.docket.queries:
        horizons = [known[p].horizon for p in q.upstream
                    if p in known and known[p].horizon is not None]
        rateless = any(p in known and known[p].channel == LOGICAL for p in q.upstream)
        reach = q.admitted_date + (max(horizons) if horizons else 0)
        if reach > q.deadline and q.ripe:
            obs.append(f"query {q.query_id!r} is unripe (horizons reach {reach} against "
                       f"a deadline of {q.deadline}) and was admitted as ripe")
        if not q.ripe and Q(q.liability) != 0:
            obs.append(f"unripe query {q.query_id!r} accrued liability {q.liability}")
        if rateless and not q.tolled:
            obs.append(f"query {q.query_id!r} depends on the rateless channel untolled")
    return _v("C2", CHECKABLE, obs)


def adequacy(d: Declaration, r: Record) -> tuple[str, ...]:
    """The general adequacy inequality: per query, and over every window.

    Per query, with `a` the admission date, `H` the greatest declared horizon
    among its upstream procedures, `W` its declared service work and `k` the
    per-date capacity: `a + H + ceiling(W/k) <= deadline`.

    Aggregate, writing `release = a + H` for the date downstream service may
    first begin: for every window, the work released and due inside it must fit
    the capacity the window supplies. Windows are delimited by releases and
    deadlines, not by deadlines alone.
    """
    obs = []
    known = d.by_id
    capacity = Q(r.docket.capacity)
    if capacity <= 0:
        return ("the docket declares no positive service capacity",)
    demands = []
    for q in r.docket.queries:
        if not q.ripe:
            continue
        horizons = [known[p].horizon for p in q.upstream
                    if p in known and known[p].horizon is not None]
        upstream = max(horizons) if horizons else 0
        service = -((-Q(q.service_work)) // capacity)
        if q.admitted_date + upstream + service > q.deadline:
            obs.append(f"query {q.query_id!r} violates the per-query adequacy "
                       f"inequality: {q.admitted_date} + {upstream} + {service} > "
                       f"{q.deadline}")
        demands.append((q.admitted_date + upstream, q.deadline, Q(q.service_work)))
    for start in sorted({rel for rel, _, _ in demands}):
        for end in sorted({dl for _, dl, _ in demands}):
            if end < start:
                continue
            total = sum((w for rel, dl, w in demands if rel >= start and dl <= end),
                        Q(0))
            supplied = capacity * Q(end - start + 1)
            if total > supplied:
                obs.append(f"the window [{start},{end}] must serve {total} work but "
                           f"supplies only {supplied}")
    return tuple(obs)


def C3(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Adequacy. Vacuous on a purely logical docket -- coverage of nothing."""
    return _v("C3", CHECKABLE, adequacy(d, r))


def P1(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Enforcement minimum, relative reading: a linear program at each date."""
    obs = []
    if d.core_minimum is None or Q(d.core_minimum) <= 0:
        return _v("P1", CHECKABLE, ("the engine certifies no positive core minimum",))
    for state in r.priced_states:
        admission = clipping_adapter(state.language, state.book, state.settled,
                                     Q(d.core_minimum), state.date)
        if not admission.admitted:
            obs.append(f"no reference at date {state.date} admits the certified core "
                       f"minimum {d.core_minimum}: {admission.consequence}")
    return _v("P1", CHECKABLE, obs)


def P1_persistence(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """That the certified core minimum keeps being satisfiable. Declared."""
    return _declared("P1-persistence", h,
                     "persistence of the certified core minimum under contraction")


def P2(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Downside establishment: a declared worldwise limit and a declared means."""
    obs = []
    if d.downside_limit is None or Q(d.downside_limit) < 0:
        obs.append("the engine declares no nonnegative downside limit")
    if d.downside_means not in MEANS:
        obs.append(f"the establishing means {d.downside_means!r} is not declared")
    if d.downside_limit is not None and Q(r.worst_case_exposure) < -Q(d.downside_limit):
        obs.append(f"recorded exposure {r.worst_case_exposure} breaches the declared "
                   f"limit -{d.downside_limit}")
    return _v("P2", CHECKABLE, obs)


def P3(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Finite gating: finitely many live per date, under a fair queue."""
    obs = []
    if d.gating_capacity is None or d.gating_capacity < 0:
        obs.append("the engine declares no finite gating capacity")
    else:
        for date, live in r.live_instruments:
            if live > d.gating_capacity:
                obs.append(f"date {date} carries {live} live instruments above the "
                           f"declared capacity {d.gating_capacity}")
    if d.overtaking_bound is not None:
        for req in r.requests:
            waited = ((req.executed_date if req.executed_date is not None else r.horizon)
                      - req.key.requested_date)
            if waited > d.overtaking_bound:
                obs.append(f"request {req.request_id!r} waited {waited} above the "
                           f"declared overtaking bound {d.overtaking_bound}")
    return _v("P3", CHECKABLE, obs)


def P4(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """A certificate type is named. Its semantics holding is a separate clause."""
    return _v("P4", CHECKABLE,
              () if d.certificate_type else ("the engine names no certificate type",))


def P4_semantics(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """That the named type's semantics hold of this engine. Declared."""
    return _declared("P4-semantics", h,
                     "the named certificate type's semantics on every history")


def realized_incoherence(state: PricedState) -> Q | None:
    if state.prices is None:
        return None
    report = incoherence(state.language, state.settled, state.prices)
    return None if report.value is None else Q(report.value)


def T1(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Tolerance conformance, against the adopted incoherence functional."""
    obs = []
    for state in r.priced_states:
        realized = realized_incoherence(state)
        if realized is None:
            continue
        declared = d.tolerance.at(state.date)
        if realized > declared:
            obs.append(f"date {state.date} realized incoherence {realized} above the "
                       f"declared tolerance {declared}")
    return _v("T1", CHECKABLE, obs)


def T2(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Certification layering: who carries a breach."""
    obs = []
    for b in r.breaches:
        expected = attribute(b.layering, Q(b.realized))
        if (expected.party != b.party or expected.tolled != b.tolled
                or expected.chargeable != b.chargeable):
            obs.append(f"the breach at date {b.date} is recorded as {b.party!r} but "
                       f"the layering makes it {expected.party!r}")
        if Q(b.layering.engine_certified) != d.tolerance.at(b.date):
            obs.append(f"the breach at date {b.date} cites a certified tolerance the "
                       "declared schedule does not carry")
    return _v("T2", CHECKABLE, obs)


def F1(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Request-keyed subsidy; directional funding unconstructible."""
    obs = []
    expected = ("target", "procedure_id", "funder_id", "requested_date",
                "scheduled_date")
    if key_fields() != expected:
        obs.append(f"the request key's fields are {key_fields()}, not {expected}")
    known = d.by_id
    for req in r.requests:
        if Q(req.subsidy) < 0:
            obs.append(f"request {req.request_id!r} carries a negative subsidy")
        p = known.get(req.key.procedure_id)
        if p is None:
            obs.append(f"request {req.request_id!r} keys an undeclared procedure")
            continue
        if len(directional_variants(req.key, p.outcome_space)) != 1:
            obs.append(f"request {req.request_id!r} admits more than one key across "
                       "intended outcomes")
    return _v("F1", CHECKABLE, obs)


def F2(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Stopping neutrality. Which witnesses are available is engine-relative."""
    obs = []
    for req in r.requests:
        if req.stopping_rule == PRECOMMITTED:
            if req.declared_stop is None:
                obs.append(f"request {req.request_id!r} claims a precommitted rule "
                           "with no declared stop")
            elif req.executed_date is not None and req.executed_date != req.declared_stop:
                obs.append(f"request {req.request_id!r} stopped at {req.executed_date}, "
                           f"not at its precommitted {req.declared_stop}")
        elif req.stopping_rule == ANYTIME_VALID:
            if not d.certificate_type:
                obs.append(f"request {req.request_id!r} leans on an anytime-valid "
                           "certificate from an engine naming no certificate type")
        else:
            obs.append(f"request {req.request_id!r} names no recognized witness")
    return _v("F2", CHECKABLE, obs)


def F3(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Probe blackout: no fresh funder position on the target inside the window."""
    obs = []
    for req in r.requests:
        start = req.key.requested_date
        end = req.executed_date if req.executed_date is not None else r.horizon
        for pos in r.positions:
            if (pos.actor_id == req.key.funder_id and pos.target == req.key.target
                    and pos.fresh and start <= pos.date <= end):
                obs.append(f"funder {pos.actor_id!r} took a fresh position on "
                           f"{pos.target!r} at {pos.date}, inside [{start},{end}]")
    return _v("F3", CHECKABLE, obs)


def F4(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Funder provenance recorded per settlement."""
    obs = []
    funded = {req.settled_variable: req.key.funder_id for req in r.requests
              if req.settled_variable}
    for s in r.settlements:
        funder = funded.get(s.variable_id)
        if funder is not None and funder not in s.funder_profile:
            obs.append(f"{s.variable_id!r} was funded by {funder!r} and does not "
                       "record it")
    return _v("F4", CHECKABLE, obs)


def S8_logical(d: Declaration, r: Record, h: Sequence[Hypothesis] = ()) -> Verdict:
    """Proof-carrying logical settlements: a derivation ships with each."""
    obs = []
    known = d.by_id
    for s in r.settlements:
        p = known.get(s.procedure_id)
        if p is not None and p.channel == LOGICAL and not s.derivation:
            obs.append(f"logical settlement {s.variable_id!r} ships no derivation")
    return _v("S8-logical", CHECKABLE, obs)


CHECKABLE_CLAUSES = (("J1", J1), ("J2", J2), ("J3", J3),
                     ("C1-empirical", C1_empirical), ("C2", C2), ("C3", C3),
                     ("P1", P1), ("P2", P2), ("P3", P3), ("P4", P4),
                     ("T1", T1), ("T2", T2), ("F1", F1), ("F2", F2), ("F3", F3),
                     ("F4", F4), ("S8-logical", S8_logical))
DECLARED_CLAUSES = (("C1-logical", C1_logical), ("P1-persistence", P1_persistence),
                    ("P4-semantics", P4_semantics))
ALL_CLAUSES = CHECKABLE_CLAUSES + DECLARED_CLAUSES


@dataclass(frozen=True)
class InterfaceReport:
    engine_id: str
    verdicts: tuple[Verdict, ...]

    @property
    def by_clause(self) -> Mapping[str, Verdict]:
        return {v.clause: v for v in self.verdicts}

    @property
    def checkable_hold(self) -> bool:
        return all(v.holds for v in self.verdicts if v.kind == CHECKABLE)

    @property
    def satisfies(self) -> bool:
        return all(v.holds for v in self.verdicts)

    @property
    def failing(self) -> tuple[str, ...]:
        return tuple(v.clause for v in self.verdicts if not v.holds)

    @property
    def leaned_on(self) -> tuple[str, ...]:
        return tuple(sorted({x for v in self.verdicts for x in v.leaned_on}))

    @property
    def obstructions(self) -> tuple[str, ...]:
        return tuple(o for v in self.verdicts for o in v.obstructions)


def evaluate(d: Declaration, r: Record, h: Sequence[Hypothesis] = (),
             clauses: Sequence[str] | None = None) -> InterfaceReport:
    wanted = set(clauses) if clauses is not None else None
    return InterfaceReport(d.engine_id, tuple(
        predicate(d, r, h) for name, predicate in ALL_CLAUSES
        if wanted is None or name in wanted))


# --------------------------------------------------------------------------
# The reference engine
# --------------------------------------------------------------------------


def reference_engine() -> Declaration:
    """A finite table of reports, declared horizons, and a refusing enforcement.

    The smallest thing that is an engine at all, and the existence proof that
    the checkable fragment is jointly satisfiable.
    """
    return Declaration(
        engine_id="engine:reference",
        procedures=(Procedure("proc:thermometer", EMPIRICAL, ("cold", "warm"),
                              "engine:reference", horizon=2),
                    Procedure("proc:decide", LOGICAL, ("proved", "refuted"),
                              "engine:reference")),
        tolerance=Schedule("tolerance:exact", {}, Q(0)),
        certificate_type="table exactness", downside_limit=Q(0),
        downside_means=REFUSAL, core_minimum=Q(1, 4), gating_capacity=2,
        overtaking_bound=4, logical_jurisdiction=("phi",))


def reference_record() -> Record:
    """A finite prefix on which the reference engine satisfies every checkable clause."""
    from src.interval import Endorsement

    language = Language(("w1", "w2", "w3"),
                        {"A": ("w1", "w2"), "B": ("w2", "w3"), "C": ("w2",)})
    book = Book(1, (Endorsement("e:A", (Q(1), Q(1), Q(0)), Q(3, 5)),))
    state = PricedState(0, language, book, (), Prices(1, {"A": Q(3, 5), "B": Q(2, 5)}))
    key = RequestKey(report_variable("proc:thermometer", 1), "proc:thermometer",
                     "funder:a", 0, 1)
    request = Request("r:1", key, Q(1), PRECOMMITTED, 1, 1,
                      report_variable("proc:thermometer", 1))
    settlements = (
        Settlement(report_variable("proc:thermometer", 1), "proc:thermometer", 1,
                   "warm", ("funder:a",)),
        Settlement(report_variable("proc:decide", 2), "proc:decide", 2, "proved",
                   (), derivation="derivation:phi"))
    docket = Docket(Q(1), (
        Query("q:empirical", 0, 6, ("proc:thermometer",), Q(1), True, False, Q(0)),
        Query("q:logical", 0, 9, ("proc:decide",), Q(1), True, True, Q(0))))
    return Record(horizon=4, settlements=settlements, requests=(request,),
                  docket=docket, priced_states=(state,),
                  live_instruments=((0, 1), (1, 2), (2, 1)))


# --------------------------------------------------------------------------
# The parametric composite
# --------------------------------------------------------------------------


def movement_recursion(theta: Q, quote_error: Q, risk: Q, ordinary: Q,
                       jumps: int) -> tuple[Q, ...]:
    """The corpus movement recursion, restated folder-locally.

    `U_0 = ordinary`, and `U_{k+1} = (1 + kappa) U_k + quote_error/theta +
    (kappa + 1) risk` with `kappa = (1 - theta)/theta`.
    """
    if jumps < 0:
        raise ValueError("the jump count is nonnegative")
    if not Q(0) < Q(theta) <= Q(1):
        raise ValueError("the core coefficient lies in (0,1]")
    kappa = (Q(1) - Q(theta)) / Q(theta)
    additive = Q(quote_error) / Q(theta) + (kappa + Q(1)) * Q(risk)
    value = Q(ordinary)
    out = [value]
    for _ in range(jumps):
        value = (Q(1) + kappa) * value + additive
        out.append(value)
    return tuple(out)


def wealth_cap(theta: Q, quote_error: Q, risk: Q, movement: Q) -> Q:
    """`quote_error/theta + kappa (risk + movement)`."""
    kappa = (Q(1) - Q(theta)) / Q(theta)
    return Q(quote_error) / Q(theta) + kappa * (Q(risk) + Q(movement))


CONSUMED = ("J1", "J2", "J3", "C1-empirical", "C2", "C3", "P1", "P2", "P3", "P4",
            "T1", "T2", "S8-logical")
DECLARED_REQUIRED = ("C1-logical", "P1-persistence", "P4-semantics")
COMPILER_CONTRACT = ("compiler:publication-before-demand",
                     "compiler:coherent-extension",
                     "compiler:summable-drift",
                     "compiler:solver-budget")
AUDIT_CONDITIONALS = ("consistency-of-declared-theory",
                      "core-minimum-or-clipping-adapter", "working-tolerance")
MECHANISM_SIDE = ("mechanism:terminal-certificate", "mechanism:noninterference",
                  "mechanism:event-order-and-refusal")


@dataclass(frozen=True)
class Parameters:
    quote_error: Q = Q(0)
    risk_limit: Q = Q(2)
    ordinary_movement: Q = Q(0)
    book_changes: int = 1

    def well_formed(self) -> bool:
        return (Q(self.quote_error) >= 0 and Q(self.risk_limit) >= 0
                and Q(self.ordinary_movement) >= 0 and self.book_changes >= 0)


@dataclass(frozen=True)
class CompositeVerdict:
    engine_id: str
    holds: bool
    bound: Q | None
    movement_cap: Q | None
    core_minimum: Q | None
    failing_clauses: tuple[str, ...]
    missing: tuple[str, ...]
    leaned_on: tuple[str, ...]
    obstructions: tuple[str, ...]


def parametric_composite(d: Declaration, r: Record, params: Parameters,
                         hypotheses: Sequence[Hypothesis] = ()) -> CompositeVerdict:
    """The composite, quantified over any engine satisfying the relevant clauses.

    Returns no bound at all when any hypothesis is absent, and names the missing
    one. The point of making the theorem consume the interface is that it cannot
    quietly report a cap it has not earned.
    """
    if not params.well_formed():
        raise ValueError("the parameters must be nonnegative")
    report = evaluate(d, r, hypotheses)
    by_clause = report.by_clause
    failing = tuple(n for n in CONSUMED if n in by_clause and not by_clause[n].holds)
    missing = [n for n in DECLARED_REQUIRED if n in by_clause and not by_clause[n].holds]
    supplied = {h.clause for h in hypotheses}
    for name in COMPILER_CONTRACT + AUDIT_CONDITIONALS + MECHANISM_SIDE:
        if name not in supplied:
            missing.append(name)
    theta = d.core_minimum
    if (theta is None or Q(theta) <= 0) and "P1" not in failing:
        failing = failing + ("P1",)
    if failing or missing:
        return CompositeVerdict(d.engine_id, False, None, None,
                                None if theta is None else Q(theta), failing,
                                tuple(missing), report.leaned_on, report.obstructions)
    theta = Q(theta)
    caps = movement_recursion(theta, params.quote_error, params.risk_limit,
                              params.ordinary_movement, params.book_changes)
    cap = caps[params.book_changes]
    return CompositeVerdict(d.engine_id, True,
                            wealth_cap(theta, params.quote_error, params.risk_limit, cap),
                            cap, theta, (), (), report.leaned_on, ())


def full_hypotheses(declared_by: str) -> tuple[Hypothesis, ...]:
    """Every hypothesis object the composite needs, with its statement."""
    statements = {
        "C1-logical": "the declared process eventually decides every sentence of the "
                      "declared logical jurisdiction, with no rate promised",
        "P1-persistence": "the certified core minimum remains satisfiable at every "
                          "future date as settlement contracts the region",
        "P4-semantics": "the named certificate type's semantics hold of this engine "
                        "on every history",
        "compiler:publication-before-demand":
            "each date publishes its rational compact convex region before demand",
        "compiler:coherent-extension":
            "the retained world mixture extends coherently to fresh queried sentences",
        "compiler:summable-drift":
            "reference drift is bounded by a computable schedule with finite total",
        "compiler:solver-budget":
            "the constrained quote's selection errors sum to a finite total",
        "consistency-of-declared-theory":
            "the declared theory is consistent, so no report variable receives a "
            "second settlement",
        "core-minimum-or-clipping-adapter":
            "either the certified core minimum is stably satisfiable, or the "
            "mechanism runs the clipping adapter and treats an empty admissible "
            "region as a detected breach",
        "working-tolerance":
            "at every date a merits certificate issues, the governing tolerance is "
            "working for the displayed book",
        "mechanism:terminal-certificate":
            "the mechanism's jointly serviceable terminal certificate",
        "mechanism:noninterference":
            "the market and mechanism noninterference and account-assignment contracts",
        "mechanism:event-order-and-refusal":
            "the mechanism's event order and refusal contract",
    }
    return tuple(Hypothesis(f"H:{c}", c, s, declared_by) for c, s in statements.items())
