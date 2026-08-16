"""Conservation, non-laundering, and composition, checked by enumeration.

The statements are about what a trajectory's record determines regarding a
liability the trajectory started with.  They are proved by induction in
`THEOREM_MAP.md`; this module checks the inductive step exhaustively over a
declared finite scope, which is what makes the proof's case analysis auditable
rather than asserted.

Scope, stated rather than sampled: every disposition sequence of the declared
length over the seven modes, with the backing and target fields filled in the
canonical way for each mode, on a one-liability ledger.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from typing import Iterable, Sequence

from abstract import (CARRY, DISCHARGE, DISPOSITION_MODES, FATE_DISCHARGED,
                      FATE_LIVE, FATE_LOST, FATE_SUSPENDED, IDENTIFY, LOSE,
                      REFINE, REINSTATE, SUSPEND, Disposition, Edit, Fate,
                      Ground, Liability, LIVE, ReasonContext, State, Step,
                      Trajectory, diachronically_answerable, fate)

FATE_KINDS = (FATE_LIVE, FATE_DISCHARGED, FATE_LOST, FATE_SUSPENDED)


def canonical_disposition(liability_id: str, mode: str, tag: str,
                          well_formed: bool = True) -> Disposition:
    """The well-formed disposition of each mode, so that enumeration explores the
    modes rather than the ways of filling a field in wrongly.

    With `well_formed` off the backing is stripped, which is the sweep's null
    input: a run over unbacked dispositions must reject every sequence that
    terminates or suspends, or the sweep is confirming nothing.
    """
    if not well_formed:
        if mode in (DISCHARGE, LOSE, SUSPEND, REINSTATE):
            return Disposition(liability_id, mode, disclosed=(mode == LOSE))
    if mode == REFINE:
        return Disposition(liability_id, REFINE, (f"{liability_id}-{tag}a",
                                                  f"{liability_id}-{tag}b"),
                           backing=f"w-refine-{tag}")
    if mode == IDENTIFY:
        return Disposition(liability_id, IDENTIFY, (f"{liability_id}-{tag}m",),
                           backing=f"licence-{tag}")
    if mode == SUSPEND:
        return Disposition(liability_id, SUSPEND, backing=f"route-{tag}")
    if mode == REINSTATE:
        return Disposition(liability_id, REINSTATE, backing=f"basis-{tag}")
    if mode == DISCHARGE:
        return Disposition(liability_id, DISCHARGE, backing=f"witness-{tag}")
    if mode == LOSE:
        return Disposition(liability_id, LOSE, backing=f"authorization-{tag}",
                           disclosed=True)
    return Disposition(liability_id, CARRY)


def _ground() -> Ground:
    return Ground("g", 0, frozenset({"verdict"}), "interval",
                  bears_on=frozenset({"verdict"}))


def _state() -> State:
    return State(date=0, commitments={"verdict": Q(0)},
                 standards={"interval": frozenset({"verdict"})},
                 vocabulary=frozenset({"harm"}),
                 ledger={"L": Liability("L", "occ", LIVE)})


def trajectory_for(modes: Sequence[str], vocabulary_churn: bool = False,
                   well_formed: bool = True) -> Trajectory:
    """One liability, one disposition per date, in the given modes.

    `vocabulary_churn` adds a representation change at every step without
    touching the ledger — the move a non-laundering statement has to be immune to.
    """
    live = {"L"}
    steps: list[Step] = []
    reasons = ReasonContext(0, (_ground(),))
    for index, mode in enumerate(modes):
        targets = sorted(live)
        dispositions = tuple(canonical_disposition(name, mode, f"{index}", well_formed)
                             for name in targets)
        for disposition in dispositions:
            if disposition.mode in (REFINE, IDENTIFY):
                live.discard(disposition.liability_id)
                live |= set(disposition.targets)
            elif disposition.mode in (DISCHARGE, LOSE):
                live.discard(disposition.liability_id)
        edit = Edit(edit_id=f"e{index}", cited=("g",), dispositions=dispositions,
                    vocabulary_add=frozenset({f"v{index}"}) if vocabulary_churn else frozenset(),
                    vocabulary_drop=frozenset({f"v{index - 1}"})
                    if vocabulary_churn and index else frozenset())
        steps.append(Step(edit, reasons.at(index)))
        if not live:
            break
    return Trajectory(_state(), tuple(steps))


@dataclass(frozen=True)
class ConservationReport:
    checked: int
    answerable: int
    fate_total: int
    fate_unique: int
    terminal_backed: int
    laundered: tuple[str, ...]

    @property
    def clean(self) -> bool:
        return (self.answerable == self.fate_total == self.fate_unique
                and not self.laundered)


def sweep(length: int = 3, vocabulary_churn: bool = False,
          well_formed: bool = True) -> ConservationReport:
    """Every mode sequence of the declared length, checked for the three
    properties the conservation statement asserts."""
    checked = answerable = total = unique = backed = 0
    laundered: list[str] = []
    for modes in product(DISPOSITION_MODES, repeat=length):
        checked += 1
        trajectory = trajectory_for(modes, vocabulary_churn, well_formed)
        if not diachronically_answerable(trajectory).answerable:
            continue
        answerable += 1
        outcome = fate(trajectory, "L")
        if outcome.kind in FATE_KINDS:
            total += 1
        if sum(outcome.kind == kind for kind in FATE_KINDS) == 1:
            unique += 1
        if outcome.terminal():
            if outcome.backing:
                backed += 1
            else:
                laundered.append(",".join(modes))
        if vocabulary_churn and outcome.terminal():
            if not any(mode in (DISCHARGE, LOSE) for mode in modes):
                laundered.append("representation-only:" + ",".join(modes))
    return ConservationReport(checked, answerable, total, unique, backed,
                              tuple(laundered))


@dataclass(frozen=True)
class CompositionReport:
    pairs: int
    agreements: int
    disagreements: tuple[str, ...]

    @property
    def clean(self) -> bool:
        return not self.disagreements


def _fate_after(first_fate: Fate, second: Sequence[str]) -> str:
    """The fate class predicted from the first segment's fate and the second
    segment's modes, without re-reading the first segment."""
    if first_fate.terminal():
        return first_fate.kind
    for mode in second:
        if mode == DISCHARGE:
            return FATE_DISCHARGED
        if mode == LOSE:
            return FATE_LOST
    if first_fate.kind == FATE_SUSPENDED and REINSTATE not in second:
        return FATE_SUSPENDED
    if SUSPEND in second and not _reinstated_after(second):
        return FATE_SUSPENDED
    return FATE_LIVE


def _reinstated_after(modes: Sequence[str]) -> bool:
    last_suspend = max((i for i, m in enumerate(modes) if m == SUSPEND), default=-1)
    last_reinstate = max((i for i, m in enumerate(modes) if m == REINSTATE), default=-1)
    return last_reinstate > last_suspend


def composition_sweep(length: int = 2) -> CompositionReport:
    """The fate of a concatenation is determined by the first segment's fate and
    the second segment, over every pair of mode sequences of the given length."""
    pairs = agreements = 0
    disagreements: list[str] = []
    for first in product(DISPOSITION_MODES, repeat=length):
        for second in product(DISPOSITION_MODES, repeat=length):
            whole = trajectory_for(tuple(first) + tuple(second))
            if not diachronically_answerable(whole).answerable:
                continue
            head = trajectory_for(first)
            if not diachronically_answerable(head).answerable:
                continue
            pairs += 1
            observed = fate(whole, "L").kind
            predicted = _fate_after(fate(head, "L"), second)
            if observed == predicted:
                agreements += 1
            else:
                disagreements.append(
                    f"{','.join(first)} | {','.join(second)}: {observed} != {predicted}")
    return CompositionReport(pairs, agreements, tuple(disagreements))
