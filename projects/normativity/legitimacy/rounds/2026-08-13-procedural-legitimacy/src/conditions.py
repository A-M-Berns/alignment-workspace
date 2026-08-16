"""The four candidate conditions, and the prospectivity clause the round adds.

State, edit and trajectory are declared here rather than imported, because the
state has to be richer than the previous round's: the reasoner's *inquiry
generation rule*, its *entitlement rule*, its *bearing relation* and its
*adequacy relation* are all coordinates, so that a reasoner cannot evade a
condition by changing the machinery the condition reads.

There is no cost field anywhere in the state.  The previous round enforced
cost-blindness with a raising accessor; here the coordinate does not exist, which
is the same discipline taken one step further and is why no clause below can be
written to consult profitability.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Mapping, Sequence

from forest import (DISCHARGE, IDENTIFY, LOSE, REFINE, REINSTATE, SUSPEND,
                    Forest, Step, conservation_failures, descend)
from provenance import (CONFERRED, GroundStore, Ground, UNION,
                        provenance_valid)

BEARING = "bearing"
ADEQUACY = "adequacy"
GENERATION = "generation"
ENTITLEMENT = "entitlement"
MACHINERY = (BEARING, ADEQUACY, GENERATION, ENTITLEMENT)


@dataclass(frozen=True)
class Liability:
    """A demand the reasoner owes an answer to.

    `substances` is a set rather than a single token so that a merge can be made
    adjudicable: when two liabilities are identified, the survivor carries both
    burdens, and a discharge has to settle each of them.
    """

    liability_id: str
    substances: frozenset[str]
    filed_at: int
    status: str = "live"


@dataclass(frozen=True)
class Encounter:
    """Something the world puts in front of the reasoner at a date."""

    at: int
    kind: str


@dataclass(frozen=True)
class Inquiry:
    inquiry_id: str
    substance: str
    generated_at: int


@dataclass(frozen=True)
class State:
    """Commitments plus the machinery that judges them.

    `bearing` and `adequacy` are the reasoner's copies of two relations the
    environment also has.  Keeping both copies is what lets the round ask whether
    a procedure can tell that its own copy has drifted.
    """

    at: int
    commitments: Mapping[str, str] = field(default_factory=dict)
    bearing: Mapping[str, frozenset[str]] = field(default_factory=dict)
    adequacy: Mapping[str, frozenset[str]] = field(default_factory=dict)
    generation: Mapping[str, str] = field(default_factory=dict)
    entitlement: frozenset[str] = frozenset()
    liabilities: Mapping[str, Liability] = field(default_factory=dict)

    def machinery(self, coordinate: str):
        return {BEARING: self.bearing, ADEQUACY: self.adequacy,
                GENERATION: self.generation, ENTITLEMENT: self.entitlement}[coordinate]


@dataclass(frozen=True)
class Edit:
    edit_id: str
    moves: Mapping[str, str] = field(default_factory=dict)
    machinery_moves: Mapping[str, object] = field(default_factory=dict)
    cited: tuple[tuple[str, str], ...] = ()
    dispositions: Mapping[str, tuple[str, tuple[str, ...], str | None]] = \
        field(default_factory=dict)
    dockets: tuple[Inquiry, ...] = ()
    refusals: tuple[tuple[str, str], ...] = ()
    files_grounds: tuple[Ground, ...] = ()

    def touched(self) -> frozenset[str]:
        return frozenset(set(self.moves) | set(self.machinery_moves))


@dataclass(frozen=True)
class Trajectory:
    initial: State
    edits: tuple[Edit, ...]
    encounters: tuple[Encounter, ...] = ()
    grounds: GroundStore = GroundStore(())
    service_window: int = 1
    capacity: int = 2

    def store(self) -> GroundStore:
        store = self.grounds
        for edit in self.edits:
            for ground in edit.files_grounds:
                store = store.with_ground(ground)
        return store

    def states(self) -> tuple[State, ...]:
        states = [self.initial]
        for edit in self.edits:
            states.append(apply_edit(states[-1], edit))
        return tuple(states)

    def final(self) -> State:
        return self.states()[-1]

    def steps(self) -> tuple[Step, ...]:
        return tuple(Step(index, dict(edit.dispositions))
                     for index, edit in enumerate(self.edits))


def apply_edit(state: State, edit: Edit) -> State:
    commitments = dict(state.commitments)
    commitments.update(edit.moves)
    bearing = dict(edit.machinery_moves.get(BEARING, state.bearing))
    adequacy = dict(edit.machinery_moves.get(ADEQUACY, state.adequacy))
    generation = dict(edit.machinery_moves.get(GENERATION, state.generation))
    entitlement = frozenset(edit.machinery_moves.get(ENTITLEMENT, state.entitlement))
    liabilities = dict(state.liabilities)

    for inquiry in edit.dockets:
        liabilities[inquiry.inquiry_id] = Liability(
            inquiry.inquiry_id, frozenset({inquiry.substance}), state.at)

    for name, (mode, targets, backing) in edit.dispositions.items():
        current = liabilities.get(name)
        if current is None:
            continue
        if mode in (REFINE, IDENTIFY):
            liabilities[name] = replace(current, status="closed")
            for target in targets:
                existing = liabilities.get(target)
                if existing is None:
                    liabilities[target] = Liability(
                        target, current.substances, current.filed_at)
                else:
                    liabilities[target] = replace(
                        existing,
                        substances=existing.substances | current.substances,
                        filed_at=min(existing.filed_at, current.filed_at))
        elif mode == SUSPEND:
            liabilities[name] = replace(current, status="suspended")
        elif mode == REINSTATE:
            liabilities[name] = replace(current, status="live")
        elif mode in (DISCHARGE, LOSE):
            liabilities[name] = replace(current, status="closed")

    return State(state.at + 1, commitments, bearing, adequacy, generation,
                 entitlement, liabilities)


# --------------------------------------------------------------------------
# P — provenance
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class Report:
    codes: tuple[str, ...]

    @property
    def holds(self) -> bool:
        return not self.codes


def provenance(trajectory: Trajectory, discipline: str = UNION) -> Report:
    """Every citation is made by a ground entitled to bear on what it licenses."""
    store = trajectory.store()
    codes: list[str] = []
    for index, edit in enumerate(trajectory.edits):
        for ground_id, coordinate in edit.cited:
            verdict = provenance_valid(store, ground_id, coordinate, index,
                                       discipline=discipline)
            if not verdict.valid:
                codes.append(verdict.code)
    return Report(tuple(sorted(set(codes))))


# --------------------------------------------------------------------------
# RR — reasons-responsiveness against the provenance-valid context
# --------------------------------------------------------------------------

RR_UNLICENSED = "rr.unlicensed_coordinate"
RR_NO_BEARING = "rr.no_bearing"


def reasons_responsive(trajectory: Trajectory) -> Report:
    """Each moved coordinate is covered by a cited ground whose content the
    reasoner's own bearing relation says bears on it.

    The bearing relation is read from the state *before* the edit, so an edit
    cannot install the bearing that licenses itself.
    """
    store = trajectory.store()
    states = trajectory.states()
    codes: list[str] = []
    for index, edit in enumerate(trajectory.edits):
        state = states[index]
        covered = {coordinate for _g, coordinate in edit.cited}
        for coordinate in sorted(edit.touched()):
            if coordinate not in covered:
                codes.append(RR_UNLICENSED)
                continue
            supports = False
            for ground_id, licensed in edit.cited:
                if licensed != coordinate:
                    continue
                ground = store.get(ground_id)
                if ground is None:
                    continue
                if coordinate in state.bearing.get(ground.content, frozenset()):
                    supports = True
            if not supports:
                codes.append(RR_NO_BEARING)
    return Report(tuple(sorted(set(codes))))


# --------------------------------------------------------------------------
# I — inquiry adequacy: generation, entitlement, service
# --------------------------------------------------------------------------

I_UNSERVICED = "inquiry.entitled_unserviced"
I_OVER_CAPACITY = "inquiry.service_capacity_exceeded"
I_REFUSAL_UNBACKED = "inquiry.refusal_without_backing"


def generated(trajectory: Trajectory) -> tuple[Inquiry, ...]:
    """What the reasoner's own generation rule produces from what it encounters.

    Generation reads the rule in force at the encounter's date, so revising the
    rule changes what is generated from then on and not before.
    """
    states = trajectory.states()
    out: list[Inquiry] = []
    for encounter in trajectory.encounters:
        index = min(encounter.at, len(states) - 1)
        substance = states[index].generation.get(encounter.kind)
        if substance is None:
            continue
        out.append(Inquiry(f"q-{encounter.kind}-{encounter.at}", substance,
                           encounter.at))
    return tuple(out)


def inquiry_adequate(trajectory: Trajectory, prospective: bool = True) -> Report:
    """Every entitled generated inquiry is docketed or refused with backing,
    within the service window, and the service rate stays inside capacity.

    With `prospective` set, entitlement is read at the date the inquiry was
    generated; without it, at the date service falls due.  That switch is the
    fifth condition, and the difference is what attack D turns on.
    """
    states = trajectory.states()
    codes: list[str] = []
    serviced: dict[str, int] = {}
    refused: dict[str, str | None] = {}
    for index, edit in enumerate(trajectory.edits):
        for inquiry in edit.dockets:
            serviced.setdefault(inquiry.inquiry_id, index)
        for inquiry_id, backing in edit.refusals:
            refused.setdefault(inquiry_id, backing)
            serviced.setdefault(inquiry_id, index)
        load = len(edit.dockets) + len(edit.refusals)
        if load > trajectory.capacity:
            codes.append(I_OVER_CAPACITY)

    for inquiry in generated(trajectory):
        read_at = inquiry.generated_at if prospective else min(
            inquiry.generated_at + trajectory.service_window, len(states) - 1)
        entitlement = states[min(read_at, len(states) - 1)].entitlement
        if inquiry.substance not in entitlement:
            continue
        when = serviced.get(inquiry.inquiry_id)
        if when is None or when > inquiry.generated_at + trajectory.service_window:
            codes.append(I_UNSERVICED)
    for inquiry_id, backing in refused.items():
        if not backing:
            codes.append(I_REFUSAL_UNBACKED)
    return Report(tuple(sorted(set(codes))))


# --------------------------------------------------------------------------
# DA — branching-safe answerability
# --------------------------------------------------------------------------

def answerable(trajectory: Trajectory) -> Report:
    """Every branch of every liability is live, routed, or terminally backed."""
    codes: list[str] = []
    steps = trajectory.steps()
    roots = set(trajectory.initial.liabilities)
    for edit in trajectory.edits:
        roots |= {inquiry.inquiry_id for inquiry in edit.dockets}
    for root in sorted(roots):
        forest = descend(root, steps)
        codes.extend(conservation_failures(forest, steps))
    return Report(tuple(sorted(set(codes))))


def forests(trajectory: Trajectory) -> Mapping[str, Forest]:
    steps = trajectory.steps()
    roots = set(trajectory.initial.liabilities)
    for edit in trajectory.edits:
        roots |= {inquiry.inquiry_id for inquiry in edit.dockets}
    return {root: descend(root, steps) for root in sorted(roots)}


# --------------------------------------------------------------------------
# X — prospectivity, the candidate fifth condition
# --------------------------------------------------------------------------

X_RETROACTIVE_ADEQUACY = "prospectivity.adequacy_applied_retroactively"
X_RETROACTIVE_ENTITLEMENT = "prospectivity.entitlement_withdrawn_retroactively"


def prospective(trajectory: Trajectory) -> Report:
    """A liability is judged by the adequacy relation in force when it was filed,
    and an inquiry entitled when generated stays entitled.

    Standards may change; what they may not do is reach backwards. This is the
    generalization to standards of the refusal of successor ratification, which
    the substrate already applies to grounds.
    """
    states = trajectory.states()
    codes: list[str] = []

    for index, edit in enumerate(trajectory.edits):
        state = states[index]
        for name, (mode, _targets, backing) in edit.dispositions.items():
            if mode != DISCHARGE:
                continue
            liability = state.liabilities.get(name)
            if liability is None or backing is None:
                continue
            filed = min(liability.filed_at, len(states) - 1)
            then = states[filed].adequacy.get(backing, frozenset())
            now = state.adequacy.get(backing, frozenset())
            for substance in sorted(liability.substances):
                if substance in now and substance not in then:
                    codes.append(X_RETROACTIVE_ADEQUACY)

    for inquiry in generated(trajectory):
        born = min(inquiry.generated_at, len(states) - 1)
        entitled_then = inquiry.substance in states[born].entitlement
        later = min(inquiry.generated_at + trajectory.service_window,
                    len(states) - 1)
        entitled_later = inquiry.substance in states[later].entitlement
        if entitled_then and not entitled_later:
            codes.append(X_RETROACTIVE_ENTITLEMENT)

    return Report(tuple(sorted(set(codes))))


# --------------------------------------------------------------------------
# X' — disclosure, the repair that survives the positive control
# --------------------------------------------------------------------------

D_UNDISCLOSED = "disclosure.silent_revision_of_live_standard"


def disclosed(trajectory: Trajectory) -> Report:
    """A revision to the adequacy relation that reaches a live liability must
    name that liability in the same edit.

    Weaker than prospectivity on purpose. Prospectivity forbids the revision from
    reaching backwards, and cannot tell an improvement from a degradation because
    the two are the same operation; this only requires that when a standard
    governing a live demand changes, the demand is named where the change is
    made. It refuses nothing that prospectivity would allow. What it buys is that
    the drift is in the record rather than inferable from it — which is the form
    a later judge, or a counterfactual condition supplied from outside, can
    actually consume.
    """
    states = trajectory.states()
    codes: list[str] = []
    for index, edit in enumerate(trajectory.edits):
        if ADEQUACY not in edit.machinery_moves:
            continue
        before = states[index].adequacy
        after = edit.machinery_moves[ADEQUACY]
        changed: set[str] = set()
        for witness in set(before) | set(after):
            if before.get(witness, frozenset()) != after.get(witness, frozenset()):
                changed |= set(before.get(witness, frozenset())) ^ set(
                    after.get(witness, frozenset()))
        if not changed:
            continue
        named = set(edit.dispositions) | {q.inquiry_id for q in edit.dockets}
        for name, liability in sorted(states[index].liabilities.items()):
            if liability.status != "live":
                continue
            if liability.substances & changed and name not in named:
                codes.append(D_UNDISCLOSED)
    return Report(tuple(sorted(set(codes))))


# --------------------------------------------------------------------------
# The conjunction
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class FourReport:
    p: Report
    i: Report
    rr: Report
    da: Report
    x: Report
    d: Report

    @property
    def four(self) -> bool:
        return (self.p.holds and self.i.holds and self.rr.holds and self.da.holds)

    @property
    def five(self) -> bool:
        return self.four and self.x.holds

    @property
    def four_and_disclosed(self) -> bool:
        return self.four and self.d.holds

    def codes(self) -> tuple[str, ...]:
        return tuple(sorted(set(self.p.codes + self.i.codes + self.rr.codes
                                + self.da.codes + self.x.codes + self.d.codes)))


def evaluate(trajectory: Trajectory, discipline: str = UNION,
             prospective_entitlement: bool = True) -> FourReport:
    return FourReport(
        p=provenance(trajectory, discipline),
        i=inquiry_adequate(trajectory, prospective_entitlement),
        rr=reasons_responsive(trajectory),
        da=answerable(trajectory),
        x=prospective(trajectory),
        d=disclosed(trajectory),
    )


# --------------------------------------------------------------------------
# Projection into the target's vocabulary
# --------------------------------------------------------------------------

def project(trajectory: Trajectory):
    """Turn a trajectory into the uses, discharges and confrontations `L*` reads.

    Confrontation is keyed on **substance**, not on inquiry identity: taking up a
    narrowly-formulated question does not confront a demand whose substance it
    does not carry.  That choice is what makes attack E adjudicable.
    """
    from environment import Confrontation, Discharge, Use
    from provenance import ancestry

    store = trajectory.store()
    states = trajectory.states()
    uses: list[Use] = []
    discharges: list[Discharge] = []
    confrontations: list[Confrontation] = []

    for index, edit in enumerate(trajectory.edits):
        state = states[index]
        for ground_id, coordinate in edit.cited:
            ground = store.get(ground_id)
            if ground is None:
                continue
            roots, _failure = ancestry(store, ground_id)
            uses.append(Use(index, ground_id, ground.content, coordinate,
                            frozenset(ground.scope), roots))
        for name, (mode, _targets, backing) in edit.dispositions.items():
            if mode != DISCHARGE:
                continue
            liability = state.liabilities.get(name)
            if liability is None:
                continue
            for substance in sorted(liability.substances):
                discharges.append(Discharge(index, name, substance, backing or ""))
        for inquiry in edit.dockets:
            confrontations.append(Confrontation(inquiry.substance, index))
        for inquiry_id, _backing in edit.refusals:
            confrontations.append(Confrontation(inquiry_id, index))
    return tuple(uses), tuple(discharges), tuple(confrontations)
