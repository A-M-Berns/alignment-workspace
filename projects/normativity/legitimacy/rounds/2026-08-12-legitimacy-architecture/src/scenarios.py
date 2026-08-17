"""The prosecution fixtures: attacks, independence witnesses, and the latent pair.

Every scenario returns objects the checks in `abstract.py` decide.  Nothing here
asserts a verdict; the tests read the verdicts off the same functions a reader
can call.

The base fixture is deliberately small.  One occasion, two substantive
coordinates, one liability, and the reasoner's own standards and vocabulary as
coordinates in their own right — which is the least structure in which the
question "can the reasoner move the standard that judges it?" can be asked.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction as Q
from typing import Mapping, Sequence

from abstract import (CARRY, DISCHARGE, ENDOGENOUS, EXOGENOUS, IDENTIFY, LOSE,
                      REFINE, REINSTATE, SUSPEND, Disposition, Edit, Ground,
                      Liability, LIVE, Policy, ReasonContext, State, Step,
                      Trajectory, apply_edit, constrain, diachronically_answerable,
                      fate, legitimate, reasons_responsive, record)

VERDICT = "verdict"
TOLLED = "tolled"
STANDARDS = "standards"
VOCABULARY = "vocabulary"

NAIVE = Policy(reflexive_machinery=False, magnitude_coordinates=frozenset({TOLLED}))
REFLEXIVE = Policy(reflexive_machinery=True, magnitude_coordinates=frozenset({TOLLED}))


# --------------------------------------------------------------------------
# The base fixture
# --------------------------------------------------------------------------

def base_standards() -> Mapping[str, frozenset[str]]:
    return {
        "interval": frozenset({VERDICT}),
        "impediment": frozenset({TOLLED}),
        "authority": frozenset({STANDARDS, VOCABULARY}),
        "identification": frozenset(),
        "defeat": frozenset(),
    }


def base_state(liabilities: Sequence[str] = ("L1",)) -> State:
    return State(
        date=0,
        commitments={VERDICT: Q(0), TOLLED: Q(0)},
        standards=base_standards(),
        vocabulary=frozenset({"harm"}),
        ledger={name: Liability(name, "occ1", LIVE) for name in liabilities},
        cost=Q(0),
    )


def interval_ground(ground_id: str = "g-interval", filed_at: int = 0,
                    source: str = EXOGENOUS) -> Ground:
    return Ground(ground_id, filed_at, frozenset({VERDICT}), "interval", source,
                  bears_on=frozenset({VERDICT}))


def impediment_ground(ground_id: str = "g-impediment", filed_at: int = 0,
                      allowance: Q = Q(2), source: str = EXOGENOUS) -> Ground:
    return Ground(ground_id, filed_at, frozenset({TOLLED}), "impediment", source,
                  bears_on=frozenset({TOLLED}), allowance=allowance)


def authority_ground(ground_id: str = "g-authority", filed_at: int = 0,
                     source: str = EXOGENOUS) -> Ground:
    return Ground(ground_id, filed_at, frozenset({STANDARDS, VOCABULARY}),
                  "authority", source,
                  bears_on=frozenset({STANDARDS, VOCABULARY, VERDICT}))


def base_reasons(*extra: Ground, date: int = 0) -> ReasonContext:
    return ReasonContext(date, (interval_ground(), impediment_ground()) + extra)


# --------------------------------------------------------------------------
# A — standard laundering
# --------------------------------------------------------------------------

def standard_laundering(policy_ground_source: str | None = None) -> Trajectory:
    """The reasoner moves the standard that judges it, then closes the objection.

    With `policy_ground_source` unset the standards move cites nothing.  Set to
    `ENDOGENOUS` it cites an authority ground the reasoner itself filed one date
    earlier — which is the version the local condition cannot see.
    """
    extra: tuple[Ground, ...] = ()
    cited: tuple[str, ...] = ()
    if policy_ground_source is not None:
        extra = (authority_ground("g-self", 0, policy_ground_source),)
        cited = ("g-self",)

    reasons = base_reasons(*extra)
    widen = Edit(
        edit_id="widen-standards",
        standards_moves={"defeat": frozenset({VERDICT})},
        cited=cited,
        dispositions=(Disposition("L1", CARRY),),
    )
    close = Edit(
        edit_id="close-under-new-standard",
        cited=cited,
        dispositions=(Disposition("L1", DISCHARGE, backing="w-under-new-standard"),),
    )
    return Trajectory(base_state(), (Step(widen, reasons),
                                     Step(close, reasons.at(1))))


# --------------------------------------------------------------------------
# B — ontology laundering
# --------------------------------------------------------------------------

def ontology_migration(dispose: str = CARRY, backed: bool = True,
                       disclosed: bool = True) -> Trajectory:
    """The vocabulary the liability was first stated in is retired.

    `dispose` selects what the migration claims about the liability: carrying it
    forward under an opaque identifier, refining it onto new-vocabulary
    descendants, or terminally disposing of it.
    """
    reasons = base_reasons(authority_ground())
    if dispose == REFINE:
        disposition = Disposition("L1", REFINE, ("L1a", "L1b"), backing="w-refine")
    elif dispose == LOSE:
        disposition = Disposition("L1", LOSE,
                                  backing="auth-1" if backed else None,
                                  disclosed=disclosed)
    else:
        disposition = Disposition("L1", CARRY)

    migrate = Edit(
        edit_id="migrate-vocabulary",
        vocabulary_add=frozenset({"welfare"}),
        vocabulary_drop=frozenset({"harm"}),
        cited=("g-authority",),
        dispositions=(disposition,),
    )
    return Trajectory(base_state(), (Step(migrate, reasons),))


# --------------------------------------------------------------------------
# C — defeater laundering
# --------------------------------------------------------------------------

def defeater_laundering(rounds: int = 3, defeat_files_liability: bool = False
                        ) -> Trajectory:
    """A defeater is produced for each reason that would have told against the
    reasoner, and the objection is then closed on a witness the surviving reasons
    support.

    `defeat_files_liability` switches on the proposed repair: producing a
    defeater files a liability to defend the defeat.
    """
    grounds = [interval_ground(), impediment_ground(), authority_ground()]
    liabilities = {f"O{i}": Liability(f"O{i}", "occ1", LIVE) for i in range(rounds)}
    state = replace(base_state(), ledger={**base_state().ledger, **liabilities})

    steps: list[Step] = []
    for index in range(rounds):
        defeat = Ground(f"d{index}", index, frozenset({VERDICT}), "defeat",
                        ENDOGENOUS, bears_on=frozenset({VERDICT}),
                        defeats=f"O{index}")
        grounds.append(defeat)
        filed = ()
        if defeat_files_liability:
            filed = (Liability(f"D{index}", "occ1", LIVE),)
        carried = tuple(Disposition(name, CARRY) for name in sorted(liabilities)
                        if int(name[1:]) > index)
        steps.append(Step(
            Edit(edit_id=f"defeat-{index}",
                 cited=("g-interval",),
                 dispositions=carried + (
                     Disposition(f"O{index}", DISCHARGE, backing=f"d{index}"),),
                 files_liabilities=filed),
            ReasonContext(index, tuple(grounds))))
    return Trajectory(state, tuple(steps))


# --------------------------------------------------------------------------
# D — agenda manipulation and coverage
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class Demand:
    """A normative demand that arises in the world, whether or not it is filed."""

    demand_id: str
    arrives_at: int
    entitled: bool = True


def coverage(trajectory: Trajectory, demands: Sequence[Demand],
             within: int = 1) -> tuple[str, ...]:
    """Which entitled demands never reached the ledger in time.

    This is the condition neither of the two dynamic conditions can state: both
    quantify over what is on the record, and a demand that was never filed is not.
    """
    filed: dict[str, int] = {name: -1 for name in trajectory.initial.ledger}
    for index, step in enumerate(trajectory.steps):
        for liability in step.edit.files_liabilities:
            filed.setdefault(liability.liability_id, index)
    missed = []
    for demand in demands:
        if not demand.entitled:
            continue
        when = filed.get(demand.demand_id)
        if when is None or when > demand.arrives_at + within:
            missed.append(demand.demand_id)
    return tuple(sorted(missed))


def agenda(file_second: bool) -> Trajectory:
    """Two trajectories differing only in whether the second demand is docketed."""
    reasons = base_reasons()
    first = Edit(
        edit_id="answer-first",
        cited=("g-interval",),
        dispositions=(Disposition("L1", DISCHARGE, backing="w1"),),
        files_liabilities=(Liability("L2", "occ1", LIVE),) if file_second else (),
    )
    second_dispositions = (Disposition("L2", DISCHARGE, backing="w2"),) if file_second else ()
    second = Edit(edit_id="answer-second", cited=("g-interval",),
                  dispositions=second_dispositions)
    return Trajectory(base_state(), (Step(first, reasons), Step(second, reasons.at(1))))


AGENDA_DEMANDS = (Demand("L1", 0), Demand("L2", 0))


# --------------------------------------------------------------------------
# E — the latent pair: identical record, different counterfactual
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class CoupledRun:
    """A reasoner whose realized verdict is a mixture of its own deliberation and
    an advisor's quote.

    `autonomous` and `influence` are latent: a disposition and a mechanism, in no
    record.  `quote` is published.  The realized verdict is what the record shows.
    """

    autonomous: tuple[Q, ...]
    influence: tuple[Q, ...]
    quote: tuple[Q, ...]

    def realized(self) -> tuple[Q, ...]:
        return tuple((1 - b) * h + b * a for h, b, a
                     in zip(self.autonomous, self.influence, self.quote))

    def advisor_free(self) -> "CoupledRun":
        return CoupledRun(self.autonomous, tuple(Q(0) for _ in self.influence),
                          self.quote)

    def defect(self) -> Q:
        return abs(self.realized()[-1] - self.advisor_free().realized()[-1])


FAITHFUL = CoupledRun(
    autonomous=(Q(1, 2), Q(5, 8), Q(3, 4), Q(3, 4)),
    influence=(Q(0), Q(0), Q(0), Q(0)),
    quote=(Q(1, 2), Q(5, 8), Q(3, 4), Q(3, 4)),
)

STEERED = CoupledRun(
    autonomous=(Q(1, 2), Q(3, 8), Q(1, 4), Q(1, 4)),
    influence=(Q(1), Q(1), Q(1), Q(1)),
    quote=(Q(1, 2), Q(5, 8), Q(3, 4), Q(3, 4)),
)


def coupled_trajectory(run: CoupledRun) -> Trajectory:
    """The normative record a coupled run writes.

    Each date the reasoner moves its verdict coordinate to the realized value,
    citing the advisor's quote as an available ground, and carries its liability.
    The steps are what the record shows; the run's latent parameters never enter.
    """
    grounds = [interval_ground()]
    steps: list[Step] = []
    realized = run.realized()
    for index, value in enumerate(realized):
        grounds.append(Ground(f"q{index}", index, frozenset({VERDICT}), "interval",
                              EXOGENOUS, bears_on=frozenset({VERDICT})))
        last = index == len(realized) - 1
        dispositions = (
            (Disposition("L1", DISCHARGE, backing="w-final"),) if last
            else (Disposition("L1", CARRY),))
        steps.append(Step(
            Edit(edit_id=f"quote-{index}", moves={VERDICT: value},
                 cited=("g-interval", f"q{index}"), dispositions=dispositions),
            ReasonContext(index, tuple(grounds))))
    return Trajectory(base_state(), tuple(steps))


# --------------------------------------------------------------------------
# F — transformative learning that must be permitted
# --------------------------------------------------------------------------

def transformative(trajectory_only: bool = False) -> Trajectory:
    """A conceptual revision and a verdict reversal, both licensed at their own
    dates, whose endpoint the initial state's own constraint refuses."""
    reasons = base_reasons(authority_ground())
    migrate = Edit(
        edit_id="revise-concepts",
        vocabulary_add=frozenset({"welfare"}),
        vocabulary_drop=frozenset({"harm"}),
        standards_moves={"interval": frozenset({VERDICT, TOLLED})},
        cited=("g-authority",),
        dispositions=(Disposition("L1", REFINE, ("L1-welfare",), backing="w-refine"),),
    )
    reverse = Edit(
        edit_id="reverse-verdict",
        moves={VERDICT: Q(1)},
        cited=("g-interval",),
        dispositions=(Disposition("L1-welfare", DISCHARGE, backing="w-welfare"),),
    )
    return Trajectory(base_state(), (Step(migrate, reasons), Step(reverse, reasons.at(1))))


def endpoint_admissible_from_start() -> bool:
    """Whether the initial state's own constraint admits the endpoint move.

    A framework in which this had to be true would forbid the conceptual change
    it is supposed to license, so the answer wanted here is `False`.
    """
    trajectory = transformative()
    start = trajectory.initial
    reasons = base_reasons(authority_ground())
    final_edit = trajectory.steps[-1].edit
    return constrain(start, reasons, final_edit, REFLEXIVE).admitted


# --------------------------------------------------------------------------
# Composition of the constraint
# --------------------------------------------------------------------------

def repeated_tolling(steps: int = 2, per_step: Q = Q(2), allowance: Q = Q(2)
                     ) -> Trajectory:
    """One impediment, cited at every date, moving the magnitude coordinate by its
    whole declared allowance each time.

    The allowance is compared against the step's movement, so it is not consumed.
    A bounded impediment therefore licenses cumulative movement that grows with
    the number of dates.
    """
    reasons = base_reasons(impediment_ground(allowance=allowance))
    trajectory_steps = []
    for index in range(steps):
        trajectory_steps.append(Step(
            Edit(edit_id=f"toll-{index}", moves={TOLLED: per_step * (index + 1)},
                 cited=("g-impediment",), dispositions=(Disposition("L1", CARRY),)),
            reasons.at(index)))
    return Trajectory(base_state(), tuple(trajectory_steps))


def composite_of(trajectory: Trajectory) -> Edit:
    """The single edit that carries the initial state to the final one.

    Moves are the endpoint values, citations the union of what the steps cited,
    dispositions the steps' dispositions in order.  This is the object a
    composition statement is about.
    """
    moves: dict[str, Q] = {}
    standards_moves: dict[str, frozenset[str]] = {}
    cited: list[str] = []
    dispositions: list[Disposition] = []
    add: frozenset[str] = frozenset()
    drop: frozenset[str] = frozenset()
    for step in trajectory.steps:
        moves.update(step.edit.moves)
        standards_moves.update(step.edit.standards_moves)
        for ground_id in step.edit.cited:
            if ground_id not in cited:
                cited.append(ground_id)
        dispositions.extend(step.edit.dispositions)
        add = (add | step.edit.vocabulary_add) - step.edit.vocabulary_drop
        drop = (drop | step.edit.vocabulary_drop) - step.edit.vocabulary_add
    return Edit(edit_id="composite", moves=moves, standards_moves=standards_moves,
                vocabulary_add=add, vocabulary_drop=drop, cited=tuple(cited),
                dispositions=tuple(dispositions))


# --------------------------------------------------------------------------
# Charge: what makes laundering pay
# --------------------------------------------------------------------------

def charge(trajectory: Trajectory, unit: Q = Q(1)) -> Q:
    """Declared charge plus a carrying charge for every open liability.

    The carrying term is what makes the conditions testable: in a substrate where
    erasure were free, a check refusing erasure would have nothing to refuse.
    """
    total = Q(0)
    for index, state in enumerate(trajectory.states()[:-1]):
        total += trajectory.steps[index].edit.charge
        total += unit * len(state.open_live())
    return total


# --------------------------------------------------------------------------
# Independence witnesses
# --------------------------------------------------------------------------

def rr_without_da() -> Trajectory:
    """Every transition is licensed; a liability is closed with no witness."""
    reasons = base_reasons()
    close = Edit(edit_id="close-bare", cited=("g-interval",),
                 dispositions=(Disposition("L1", DISCHARGE),))
    return Trajectory(base_state(), (Step(close, reasons),))


def da_without_rr() -> Trajectory:
    """The bookkeeping is impeccable; the substantive move cites nothing."""
    reasons = base_reasons()
    move = Edit(edit_id="unlicensed-move", moves={VERDICT: Q(1)},
                dispositions=(Disposition("L1", CARRY),))
    return Trajectory(base_state(), (Step(move, reasons),))


def legitimate_and_covered() -> Trajectory:
    """Both conditions hold and every arising demand is docketed."""
    return agenda(file_second=True)


def maximal_charge() -> Trajectory:
    """Legitimate, covered, and as expensive as the constraint allows.

    Every step carries rather than answers, which the constraint permits and the
    carrying charge prices.  Performance is a separate question from legitimacy,
    and this is the witness that separates them.
    """
    reasons = base_reasons()
    steps = tuple(Step(Edit(edit_id=f"carry-{i}", cited=("g-interval",),
                            dispositions=(Disposition("L1", CARRY),)),
                       reasons.at(i))
                  for i in range(4))
    return Trajectory(base_state(), steps)


def prompt_answer() -> Trajectory:
    """The same demand, answered at the first date it can be."""
    reasons = base_reasons()
    steps = [Step(Edit(edit_id="answer", cited=("g-interval",),
                       dispositions=(Disposition("L1", DISCHARGE, backing="w1"),)),
                  reasons)]
    steps += [Step(Edit(edit_id=f"idle-{i}", cited=("g-interval",)), reasons.at(i))
              for i in range(1, 4)]
    return Trajectory(base_state(), tuple(steps))


def cheap_and_unlicensed() -> Trajectory:
    """Low charge bought by an unlicensed edit."""
    reasons = base_reasons()
    steps = [Step(Edit(edit_id="strike", moves={VERDICT: Q(1)},
                       dispositions=(Disposition("L1", DISCHARGE, backing="w1"),)),
                  reasons)]
    steps += [Step(Edit(edit_id=f"idle-{i}", cited=("g-interval",)), reasons.at(i))
              for i in range(1, 4)]
    return Trajectory(base_state(), tuple(steps))


def cheap_and_unanswerable() -> Trajectory:
    """Low charge bought by closing a liability with nothing behind it."""
    reasons = base_reasons()
    steps = [Step(Edit(edit_id="drop", cited=("g-interval",),
                       dispositions=(Disposition("L1", DISCHARGE),)), reasons)]
    steps += [Step(Edit(edit_id=f"idle-{i}", cited=("g-interval",)), reasons.at(i))
              for i in range(1, 4)]
    return Trajectory(base_state(), tuple(steps))


# --------------------------------------------------------------------------
# The filing gap
# --------------------------------------------------------------------------

def filing_extension(target_coordinate: str = STANDARDS) -> tuple[Trajectory, Trajectory]:
    """A move the constraint refuses, and the same move after one filing.

    The pair is the whole content of the filing observation: nothing in either
    condition constrains what may be put on the record, so any move some ground
    would license is one filing away from being licensed.
    """
    reasons = base_reasons()
    refused = Edit(edit_id="move-standards",
                   standards_moves={"defeat": frozenset({VERDICT})},
                   dispositions=(Disposition("L1", CARRY),))
    before = Trajectory(base_state(), (Step(refused, reasons),))

    filed = authority_ground("g-filed", 0, ENDOGENOUS)
    admitted = replace(refused, edit_id="move-standards-cited", cited=("g-filed",))
    after = Trajectory(base_state(), (Step(admitted, reasons.with_ground(filed)),))
    return before, after
