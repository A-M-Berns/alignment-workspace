"""The abstract normative-constraint and legitimacy interface.

This module states the statics and the two dynamic conditions independently of
the docket, warrant, tolling and charge machinery of the finite substrate, and
supplies the executable checks that decide them.

Three objects and nothing else:

* a **state** `x` — commitments, standards, vocabulary, liability ledger, cost;
* a **reason context** `r` — the grounds on the record at a date;
* a **constraint** `Gamma(x, r)` — the admissible successors.

`Gamma` is presented as a membership decision on a declared edit alphabet rather
than as a set, because the interesting structural facts (scope, availability,
defeat, magnitude, footprint) are properties of the decision and are lost when
the set is taken as primitive.  Where a finite alphabet is declared, `admissible`
returns the set itself.

The footprint discipline is structural, not a check: `Gamma` receives a
`ReasonView` over the state, and that view raises on the cost coordinate.  A
constraint that consulted what a move saves cannot be written against this
interface rather than being written and then rejected.

Exact rationals throughout; no float enters a verdict path.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from fractions import Fraction as Q
from typing import Iterable, Mapping, Sequence

# --------------------------------------------------------------------------
# Verdicts
# --------------------------------------------------------------------------

ADMIT = "admit"
REJECT = "reject"
UNRESOLVED = "unresolved"


@dataclass(frozen=True)
class Verdict:
    """Three-valued, because the substrate's magnitude question is unresolved.

    `unresolved` is not `reject`.  A trajectory containing an unresolved step is
    uncertified, which is a different thing from illegitimate, and collapsing the
    two would answer a normative question by choosing a default.
    """

    kind: str
    code: str = ""
    detail: str = ""

    @property
    def admitted(self) -> bool:
        return self.kind == ADMIT


def _admit() -> Verdict:
    return Verdict(ADMIT)


def _reject(code: str, detail: str = "") -> Verdict:
    return Verdict(REJECT, code, detail)


def _unresolved(code: str, detail: str = "") -> Verdict:
    return Verdict(UNRESOLVED, code, detail)


# --------------------------------------------------------------------------
# Reasons
# --------------------------------------------------------------------------

GROUND_KINDS = ("interval", "impediment", "authority", "ratification", "defeat",
                "identification")

EXOGENOUS = "exogenous"
ENDOGENOUS = "endogenous"


@dataclass(frozen=True)
class Ground:
    """A record item that can be cited in support of a move.

    `source` is the provenance partition the composition analysis needs: a ground
    the settlement channel wrote, versus one the reasoner (or an advisor acting
    through it) wrote.  Nothing in the local checks reads it; it is a hypothesis
    of the composition statement, exposed here so that statement can be made.
    """

    ground_id: str
    filed_at: int
    licenses: frozenset[str]
    kind: str = "interval"
    source: str = EXOGENOUS
    bears_on: frozenset[str] = frozenset()
    allowance: Q = Q(0)
    defeated_at: int | None = None
    defeats: str | None = None

    def available_at(self, date: int) -> bool:
        return self.filed_at <= date

    def live_at(self, date: int) -> bool:
        return self.defeated_at is None or self.defeated_at > date


@dataclass(frozen=True)
class ReasonContext:
    """The grounds on the record, read at a date.

    Reading is date-relative by construction: a ground filed later is invisible
    rather than inadmissible, so importing a later fact as though it had been
    available has no representation here.
    """

    date: int
    grounds: tuple[Ground, ...]

    def visible(self) -> tuple[Ground, ...]:
        return tuple(g for g in self.grounds if g.available_at(self.date))

    def get(self, ground_id: str) -> Ground | None:
        for ground in self.visible():
            if ground.ground_id == ground_id:
                return ground
        return None

    def at(self, date: int) -> "ReasonContext":
        return ReasonContext(date, self.grounds)

    def with_ground(self, ground: Ground) -> "ReasonContext":
        return ReasonContext(self.date, self.grounds + (ground,))


# --------------------------------------------------------------------------
# Liabilities and the ledger
# --------------------------------------------------------------------------

LIVE = "live"
SUSPENDED = "suspended"
CLOSED = "closed"

CARRY = "carry"
REFINE = "refine"
IDENTIFY = "identify"
SUSPEND = "suspend"
DISCHARGE = "discharge"
LOSE = "lose"
REINSTATE = "reinstate"

DISPOSITION_MODES = (CARRY, REFINE, IDENTIFY, SUSPEND, DISCHARGE, LOSE, REINSTATE)
TERMINAL_MODES = (DISCHARGE, LOSE)


@dataclass(frozen=True)
class Liability:
    """An identified normative demand.  Identity is opaque: it is not the
    vocabulary the demand was first stated in, which is what lets a demand
    survive a change of vocabulary."""

    liability_id: str
    carrier: str
    status: str = LIVE
    route: str | None = None


@dataclass(frozen=True)
class Disposition:
    """What a transition does to one liability.  Every live liability gets
    exactly one, which is the whole content of the diachronic condition."""

    liability_id: str
    mode: str
    targets: tuple[str, ...] = ()
    backing: str | None = None
    disclosed: bool = False


# --------------------------------------------------------------------------
# States
# --------------------------------------------------------------------------

COST = "cost"


@dataclass(frozen=True)
class State:
    """A reasoner state.

    `standards` is the applicability machinery: which coordinates a ground of a
    given kind may license.  It is a coordinate of the state, so a change to it
    is a move that itself needs licensing.  That is the point at which the naive
    local condition and the one this module states come apart.
    """

    date: int
    commitments: Mapping[str, Q] = field(default_factory=dict)
    standards: Mapping[str, frozenset[str]] = field(default_factory=dict)
    vocabulary: frozenset[str] = frozenset()
    ledger: Mapping[str, Liability] = field(default_factory=dict)
    cost: Q = Q(0)

    def live(self) -> tuple[str, ...]:
        return tuple(sorted(k for k, v in self.ledger.items()
                            if v.status in (LIVE, SUSPENDED)))

    def open_live(self) -> tuple[str, ...]:
        return tuple(sorted(k for k, v in self.ledger.items() if v.status == LIVE))


class FootprintError(RuntimeError):
    """Raised when a constraint reads a coordinate outside its declared
    footprint.  The failure is loud on purpose: a silent read is the thing the
    footprint exists to prevent."""


CONSTRAINT_FOOTPRINT = ("commitments", "standards", "vocabulary", "ledger", "date")


@dataclass(frozen=True)
class ReasonView:
    """The only handle a constraint gets on a state.

    Every read is served from the declared footprint and the cost coordinate is
    not in it.  This is the abstract form of the substrate's structural
    no-cost-laundering condition: legitimacy is out of reach of profitability
    because profitability is out of reach of the constraint.
    """

    state: State
    log: list[str] = field(default_factory=list)

    def read(self, field_name: str):
        if field_name not in CONSTRAINT_FOOTPRINT:
            raise FootprintError(
                f"{field_name!r} is outside the constraint footprint "
                f"{CONSTRAINT_FOOTPRINT}")
        self.log.append(field_name)
        return getattr(self.state, field_name)


# --------------------------------------------------------------------------
# Edits
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class Edit:
    """A proposed transition.

    `moves` covers substantive commitments; `standards_moves` and `vocabulary_*`
    cover the reasoner's own normative and conceptual machinery.  They are listed
    separately only so a model can exhibit a constraint that constrains one and
    not the other; the condition below treats all three as coordinates.
    """

    edit_id: str
    moves: Mapping[str, Q] = field(default_factory=dict)
    standards_moves: Mapping[str, frozenset[str]] = field(default_factory=dict)
    vocabulary_add: frozenset[str] = frozenset()
    vocabulary_drop: frozenset[str] = frozenset()
    cited: tuple[str, ...] = ()
    authority: str | None = None
    dispositions: tuple[Disposition, ...] = ()
    files: tuple[Ground, ...] = ()
    files_liabilities: tuple[Liability, ...] = ()
    charge: Q = Q(0)


STANDARDS_COORDINATE = "standards"
VOCABULARY_COORDINATE = "vocabulary"


def touched_coordinates(edit: Edit) -> frozenset[str]:
    """Every coordinate the edit moves, with the reasoner's own machinery named
    as coordinates rather than treated as a free background."""
    touched = set(edit.moves)
    if edit.standards_moves:
        touched.add(STANDARDS_COORDINATE)
    if edit.vocabulary_add or edit.vocabulary_drop:
        touched.add(VOCABULARY_COORDINATE)
    return frozenset(touched)


# --------------------------------------------------------------------------
# The constraint
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class Policy:
    """The parameters that are normative commitments rather than bookkeeping.

    `bears_on` and `magnitude_ok` are supplied, not derived.  `reflexive_machinery`
    is the switch this round needs: whether the reasoner's own standards count as
    a coordinate the scope condition ranges over.  With it off, the condition is
    the naive one and standard laundering passes; with it on, laundering must be
    licensed like anything else.
    """

    reflexive_machinery: bool = True
    magnitude_coordinates: frozenset[str] = frozenset()
    require_bears_on: bool = True


DEFAULT_POLICY = Policy()


def _licensed_coordinates(view: ReasonView, grounds: Sequence[Ground],
                          policy: Policy) -> frozenset[str]:
    """What the cited grounds license, filtered through the state's standards.

    A ground's own `licenses` declaration is not enough: the state's standards
    say which coordinates a ground of that kind may reach at all.  The
    intersection is what the scope condition compares against.
    """
    standards = view.read("standards")
    allowed: set[str] = set()
    for ground in grounds:
        permitted = standards.get(ground.kind)
        if permitted is None:
            continue
        allowed |= set(ground.licenses) & set(permitted)
    return frozenset(allowed)


def constrain(state: State, reasons: ReasonContext, edit: Edit,
              policy: Policy = DEFAULT_POLICY) -> Verdict:
    """Decide whether `edit` carries the state to an admissible successor.

    The clauses are the abstract residue of the substrate's certificate checks.
    Each is named for the obstruction it reports first.
    """
    view = ReasonView(state)
    date = view.read("date")
    context = reasons.at(date)

    cited: list[Ground] = []
    for ground_id in edit.cited:
        ground = context.get(ground_id)
        if ground is None:
            return _reject("constraint.not_available",
                           f"{ground_id} is not on the record at {date}")
        cited.append(ground)

    for ground in cited:
        if not ground.live_at(date):
            return _reject("constraint.defeated_ground", ground.ground_id)
        if ground.kind == "ratification":
            return _reject("constraint.successor_ratification", ground.ground_id)

    touched = touched_coordinates(edit)
    if not policy.reflexive_machinery:
        touched = frozenset(c for c in touched
                            if c not in (STANDARDS_COORDINATE, VOCABULARY_COORDINATE))

    licensed = _licensed_coordinates(view, cited, policy)
    outside = touched - licensed
    if outside:
        return _reject("constraint.out_of_scope", ",".join(sorted(outside)))

    if policy.require_bears_on:
        commitments = view.read("commitments")
        for coordinate in sorted(edit.moves):
            if not any(coordinate in ground.bears_on for ground in cited):
                return _reject("constraint.no_reason_connection", coordinate)

    for coordinate in sorted(policy.magnitude_coordinates & frozenset(edit.moves)):
        commitments = view.read("commitments")
        old = commitments.get(coordinate, Q(0))
        new = edit.moves[coordinate]
        allowance = sum((g.allowance for g in cited), Q(0))
        if new - old > allowance:
            return _unresolved("constraint.magnitude_unresolved",
                               f"{coordinate}: {new - old} > {allowance}")

    burden = _burden_preservation(view, edit)
    if burden is not None:
        return burden

    return _admit()


def _burden_preservation(view: ReasonView, edit: Edit) -> Verdict | None:
    """The local half of answerability: an edit may not strike an obligation out.

    This is the one clause the two conditions share.  It is stated here because a
    reasoner that could erase a liability inside a single admitted edit would make
    the diachronic condition unenforceable one step at a time.
    """
    ledger = view.read("ledger")
    for disposition in edit.dispositions:
        if disposition.liability_id not in ledger:
            return _reject("burden.unknown", disposition.liability_id)
        if disposition.mode not in DISPOSITION_MODES:
            return _reject("burden.invalid_mode", disposition.mode)
    disposed = {d.liability_id for d in edit.dispositions}
    state_live = {k for k, v in ledger.items() if v.status == LIVE}
    for liability_id in sorted(state_live - disposed):
        # Silence is carrying, not dropping.  A model that let an edit drop an
        # obligation by omission would put the whole conservation result on the
        # honesty of the edit's author.
        continue
    return None


def admissible(state: State, reasons: ReasonContext, alphabet: Sequence[Edit],
               policy: Policy = DEFAULT_POLICY) -> tuple[Edit, ...]:
    """`Gamma(x, r)` presented as a set, over a declared finite edit alphabet."""
    return tuple(edit for edit in alphabet
                 if constrain(state, reasons, edit, policy).admitted)


# --------------------------------------------------------------------------
# Applying an edit
# --------------------------------------------------------------------------

def apply_edit(state: State, edit: Edit) -> State:
    """The successor state.  Total: it does not decide admissibility, so an
    inadmissible edit still has a successor and a model can display it."""
    commitments = dict(state.commitments)
    commitments.update(edit.moves)
    standards = dict(state.standards)
    standards.update(edit.standards_moves)
    vocabulary = (state.vocabulary | edit.vocabulary_add) - edit.vocabulary_drop
    ledger = dict(state.ledger)

    for liability in edit.files_liabilities:
        ledger[liability.liability_id] = liability

    for disposition in edit.dispositions:
        current = ledger.get(disposition.liability_id)
        if current is None:
            continue
        if disposition.mode == CARRY:
            pass
        elif disposition.mode in (REFINE, IDENTIFY):
            ledger[disposition.liability_id] = replace(current, status=CLOSED)
            for target in disposition.targets:
                ledger.setdefault(target, Liability(target, current.carrier, LIVE))
        elif disposition.mode == SUSPEND:
            ledger[disposition.liability_id] = replace(
                current, status=SUSPENDED, route=disposition.backing)
        elif disposition.mode == REINSTATE:
            ledger[disposition.liability_id] = replace(current, status=LIVE, route=None)
        elif disposition.mode in TERMINAL_MODES:
            ledger[disposition.liability_id] = replace(current, status=CLOSED)

    return State(date=state.date + 1, commitments=commitments, standards=standards,
                 vocabulary=vocabulary, ledger=ledger, cost=state.cost + edit.charge)


# --------------------------------------------------------------------------
# Trajectories
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class Step:
    edit: Edit
    reasons: ReasonContext


@dataclass(frozen=True)
class Trajectory:
    """A run: an initial state and a sequence of steps.  States are derived, not
    stored, so a trajectory cannot disagree with its own transitions."""

    initial: State
    steps: tuple[Step, ...]

    def states(self) -> tuple[State, ...]:
        states = [self.initial]
        for step in self.steps:
            states.append(apply_edit(states[-1], step.edit))
        return tuple(states)

    def final(self) -> State:
        return self.states()[-1]

    def __add__(self, other: "Trajectory") -> "Trajectory":
        return Trajectory(self.initial, self.steps + other.steps)


# --------------------------------------------------------------------------
# Reasons-responsiveness
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class RRReport:
    verdicts: tuple[Verdict, ...]

    @property
    def responsive(self) -> bool:
        return all(v.kind == ADMIT for v in self.verdicts)

    @property
    def uncertified(self) -> bool:
        return any(v.kind == UNRESOLVED for v in self.verdicts)

    def codes(self) -> tuple[str, ...]:
        return tuple(v.code for v in self.verdicts if v.code)


def reasons_responsive(trajectory: Trajectory,
                       policy: Policy = DEFAULT_POLICY) -> RRReport:
    """Every transition lands in the constraint generated by the reasons
    available at that stage."""
    states = trajectory.states()
    verdicts = tuple(constrain(states[i], step.reasons, step.edit, policy)
                     for i, step in enumerate(trajectory.steps))
    return RRReport(verdicts)


# --------------------------------------------------------------------------
# Diachronic answerability
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class Obstruction:
    code: str
    liability_id: str
    date: int
    detail: str = ""


@dataclass(frozen=True)
class DAReport:
    obstructions: tuple[Obstruction, ...]

    @property
    def answerable(self) -> bool:
        return not self.obstructions

    def codes(self) -> tuple[str, ...]:
        return tuple(o.code for o in self.obstructions)


def diachronically_answerable(trajectory: Trajectory) -> DAReport:
    """Every liability live at a date has exactly one disposition at that date,
    every terminal disposition carries its backing, suspension does not close,
    and descendants are fresh."""
    obstructions: list[Obstruction] = []
    states = trajectory.states()
    seen: set[str] = set(states[0].ledger)

    for index, step in enumerate(trajectory.steps):
        state = states[index]
        edit = step.edit
        by_liability: dict[str, list[Disposition]] = {}
        for disposition in edit.dispositions:
            by_liability.setdefault(disposition.liability_id, []).append(disposition)

        for liability_id in state.open_live():
            given = by_liability.get(liability_id, [])
            if len(given) > 1:
                obstructions.append(Obstruction("da.conflicting_disposition",
                                                liability_id, state.date))
            if not given:
                # Carrying is the default and is not an obstruction; what the
                # condition forbids is a live liability whose state changes with
                # no disposition naming it.
                after = trajectory.states()[index + 1].ledger.get(liability_id)
                if after is None or after.status != LIVE:
                    obstructions.append(Obstruction("da.undisposed_change",
                                                    liability_id, state.date))

        for disposition in edit.dispositions:
            liability = state.ledger.get(disposition.liability_id)
            if liability is None:
                obstructions.append(Obstruction("da.unknown_liability",
                                                disposition.liability_id, state.date))
                continue
            if liability.status == CLOSED:
                obstructions.append(Obstruction("da.acts_on_closed",
                                                disposition.liability_id, state.date))
            if disposition.mode == DISCHARGE and not disposition.backing:
                obstructions.append(Obstruction("da.discharge_without_witness",
                                                disposition.liability_id, state.date))
            if disposition.mode == LOSE:
                if not disposition.backing:
                    obstructions.append(Obstruction("da.loss_without_authorization",
                                                    disposition.liability_id, state.date))
                if not disposition.disclosed:
                    obstructions.append(Obstruction("da.undisclosed_loss",
                                                    disposition.liability_id, state.date))
            if disposition.mode == SUSPEND and not disposition.backing:
                obstructions.append(Obstruction("da.suspension_without_route",
                                                disposition.liability_id, state.date))
            if disposition.mode == REINSTATE and not disposition.backing:
                obstructions.append(Obstruction("da.reinstatement_without_basis",
                                                disposition.liability_id, state.date))
            if disposition.mode in (REFINE, IDENTIFY):
                if not disposition.targets:
                    obstructions.append(Obstruction("da.empty_refinement",
                                                    disposition.liability_id, state.date))
                if disposition.mode == IDENTIFY and not disposition.backing:
                    obstructions.append(Obstruction("da.unlicensed_identification",
                                                    disposition.liability_id, state.date))
                for target in disposition.targets:
                    if target in seen and disposition.mode == REFINE:
                        obstructions.append(Obstruction("da.stale_descendant",
                                                        target, state.date))
                    seen.add(target)

        for liability in edit.files_liabilities:
            seen.add(liability.liability_id)

        after = states[index + 1]
        for liability_id in state.open_live():
            before_status = state.ledger[liability_id].status
            after_status = after.ledger[liability_id].status
            named = liability_id in by_liability
            if before_status != after_status and not named:
                obstructions.append(Obstruction("da.silent_status_change",
                                                liability_id, state.date))

    return DAReport(tuple(obstructions))


# --------------------------------------------------------------------------
# Fates: the conservation fold
# --------------------------------------------------------------------------

FATE_LIVE = "live"
FATE_DISCHARGED = "discharged"
FATE_LOST = "lost"
FATE_SUSPENDED = "suspended"


@dataclass(frozen=True)
class Fate:
    """Where a liability ended up, and what backs the ending."""

    kind: str
    descendants: tuple[str, ...] = ()
    at_date: int | None = None
    backing: str | None = None

    def terminal(self) -> bool:
        return self.kind in (FATE_DISCHARGED, FATE_LOST)


def fate(trajectory: Trajectory, liability_id: str) -> Fate:
    """Fold the trajectory into one liability's fate.

    Descendants are chased through carry, refine and identify edges; a terminal
    edge on any descendant terminates that branch and records its backing.  The
    fold reads the record and nothing else, which is what makes the composite
    audit performable at the endpoint.
    """
    frontier = {liability_id}
    states = trajectory.states()
    terminal: tuple[str, int, str | None] | None = None
    suspended_at: tuple[int, str | None] | None = None

    for index, step in enumerate(trajectory.steps):
        state = states[index]
        for disposition in step.edit.dispositions:
            if disposition.liability_id not in frontier:
                continue
            if disposition.mode in (REFINE, IDENTIFY):
                frontier.discard(disposition.liability_id)
                frontier |= set(disposition.targets)
            elif disposition.mode == SUSPEND:
                suspended_at = (state.date, disposition.backing)
            elif disposition.mode == REINSTATE:
                suspended_at = None
            elif disposition.mode == DISCHARGE:
                frontier.discard(disposition.liability_id)
                if terminal is None:
                    terminal = (FATE_DISCHARGED, state.date, disposition.backing)
            elif disposition.mode == LOSE:
                frontier.discard(disposition.liability_id)
                if terminal is None:
                    terminal = (FATE_LOST, state.date, disposition.backing)

    if frontier:
        if suspended_at is not None:
            return Fate(FATE_SUSPENDED, tuple(sorted(frontier)),
                        suspended_at[0], suspended_at[1])
        return Fate(FATE_LIVE, tuple(sorted(frontier)))
    if terminal is not None:
        return Fate(terminal[0], (), terminal[1], terminal[2])
    return Fate(FATE_LIVE, ())


def fates(trajectory: Trajectory) -> Mapping[str, Fate]:
    """Every liability the trajectory starts with, folded."""
    return {liability_id: fate(trajectory, liability_id)
            for liability_id in sorted(trajectory.initial.ledger)}


# --------------------------------------------------------------------------
# Legitimacy
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class LegitimacyReport:
    rr: RRReport
    da: DAReport

    @property
    def legitimate(self) -> bool:
        return self.rr.responsive and self.da.answerable


def legitimate(trajectory: Trajectory,
               policy: Policy = DEFAULT_POLICY) -> LegitimacyReport:
    """The conjunction under test.  Whether it deserves the name is decided by
    what it entails and what it misses, not here."""
    return LegitimacyReport(reasons_responsive(trajectory, policy),
                            diachronically_answerable(trajectory))


# --------------------------------------------------------------------------
# The record
# --------------------------------------------------------------------------

def record(trajectory: Trajectory) -> tuple:
    """Everything a legitimacy verdict is a function of.

    Both conditions read exactly this: the initial state minus its cost, and each
    step's edit and reason context.  Every later state is derived from those by
    `apply_edit`, so nothing else is available to either check.  Isolating it is
    what makes the measurability statement — and therefore the limit the deference
    interface inherits — checkable rather than asserted.
    """
    rows = []
    for index, step in enumerate(trajectory.steps):
        edit = step.edit
        rows.append((
            edit.edit_id,
            tuple(sorted(edit.moves.items())),
            tuple(sorted((k, tuple(sorted(v))) for k, v in edit.standards_moves.items())),
            tuple(sorted(edit.vocabulary_add)), tuple(sorted(edit.vocabulary_drop)),
            edit.cited, edit.authority,
            tuple(sorted((d.liability_id, d.mode, d.targets, d.backing, d.disclosed)
                         for d in edit.dispositions)),
            tuple(sorted(g.ground_id for g in edit.files)),
            tuple(sorted(step.reasons.grounds, key=lambda g: g.ground_id)),
        ))
    initial = trajectory.initial
    return (tuple(sorted(initial.ledger)),
            tuple(sorted(initial.commitments.items())),
            tuple(sorted((k, tuple(sorted(v))) for k, v in initial.standards.items())),
            tuple(sorted(initial.vocabulary)),
            initial.date,
            tuple(rows))
