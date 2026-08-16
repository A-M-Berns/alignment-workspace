"""Branching-safe answerability: the conserved object is a forest, not a label.

The previous round's conservation statement gave each initial liability one fate
from `{live, discharged, lost, suspended}`.  That is correct when a liability
never splits and wrong as soon as it does: after

    l -> {l1, l2},   l1 discharged,   l2 still live

there is no single label, and a single-label fold has to pick one and silently
drop the other branch's backing.  This module replaces the label with the object
the situation actually has — the descent forest, with every leaf carrying its own
disposition — and re-states conservation and composition over it.

`LOSS_WITNESS` below exhibits the previous abstraction dropping a discharge.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Mapping, Sequence

CARRY = "carry"
REFINE = "refine"
IDENTIFY = "identify"
SUSPEND = "suspend"
REINSTATE = "reinstate"
DISCHARGE = "discharge"
LOSE = "lose"

MODES = (CARRY, REFINE, IDENTIFY, SUSPEND, REINSTATE, DISCHARGE, LOSE)
TERMINAL = (DISCHARGE, LOSE)

LEAF_LIVE = "live"
LEAF_SUSPENDED = "suspended"
LEAF_DISCHARGED = "discharged"
LEAF_LOST = "lost"


@dataclass(frozen=True)
class Step:
    """One date's dispositions, keyed by the liability each acts on."""

    at: int
    dispositions: Mapping[str, tuple[str, tuple[str, ...], str | None]]


@dataclass(frozen=True)
class Leaf:
    liability_id: str
    status: str
    at: int | None = None
    backing: str | None = None


@dataclass(frozen=True)
class Forest:
    """Every branch descending from one initial liability, with its disposition.

    `edges` is the descent relation, kept so composition can be stated as a
    relation composition rather than as a re-fold.
    """

    root: str
    leaves: tuple[Leaf, ...]
    edges: tuple[tuple[str, str], tuple, ...] = ()

    def live(self) -> tuple[Leaf, ...]:
        return tuple(l for l in self.leaves if l.status == LEAF_LIVE)

    def suspended(self) -> tuple[Leaf, ...]:
        return tuple(l for l in self.leaves if l.status == LEAF_SUSPENDED)

    def terminal(self) -> tuple[Leaf, ...]:
        return tuple(l for l in self.leaves
                     if l.status in (LEAF_DISCHARGED, LEAF_LOST))

    def label(self) -> str:
        """The previous round's single fate, for comparison only.

        Live branches win, then suspended, then terminal — which is what a fold
        returning one value has to do, and is exactly where the information goes.
        """
        if self.live():
            return LEAF_LIVE
        if self.suspended():
            return LEAF_SUSPENDED
        if self.terminal():
            return self.terminal()[0].status
        return LEAF_LIVE


def descend(root: str, steps: Sequence[Step],
            initial: tuple[str, int | None, str | None] = (LEAF_LIVE, None, None)
            ) -> Forest:
    """Fold a history into one initial liability's descent forest.

    Every branch is followed independently, so a split whose branches receive
    different dispositions produces one leaf per branch.  `initial` seeds the
    root's status, which composition needs so that a suspended branch stays
    suspended across a seam that does not reinstate it.
    """
    frontier: dict[str, tuple[str, int | None, str | None]] = {root: initial}
    closed: list[Leaf] = []
    edges: list[tuple[str, str]] = []

    for step in steps:
        nxt: dict[str, tuple[str, int | None, str | None]] = {}
        for name, state in frontier.items():
            given = step.dispositions.get(name)
            if given is None:
                nxt[name] = state
                continue
            mode, targets, backing = given
            if mode in (REFINE, IDENTIFY):
                for target in targets:
                    edges.append((name, target))
                    nxt[target] = (LEAF_LIVE, None, None)
            elif mode == SUSPEND:
                nxt[name] = (LEAF_SUSPENDED, step.at, backing)
            elif mode == REINSTATE:
                nxt[name] = (LEAF_LIVE, None, None)
            elif mode == DISCHARGE:
                closed.append(Leaf(name, LEAF_DISCHARGED, step.at, backing))
            elif mode == LOSE:
                closed.append(Leaf(name, LEAF_LOST, step.at, backing))
            else:
                nxt[name] = state
        frontier = nxt

    leaves = tuple(closed) + tuple(
        Leaf(name, status, at, backing)
        for name, (status, at, backing) in sorted(frontier.items()))
    return Forest(root, leaves, tuple(edges))


F_UNBACKED_TERMINAL = "forest.terminal_without_backing"
F_UNROUTED_SUSPENSION = "forest.suspension_without_route"
F_EMPTY_REFINEMENT = "forest.empty_refinement"
F_REUSED_IDENTIFIER = "forest.reused_identifier"
F_ACTS_ON_CLOSED = "forest.acts_on_closed"


def conservation_failures(forest: Forest, steps: Sequence[Step]) -> tuple[str, ...]:
    """The branching conservation condition.

    Every leaf is live, suspended with a route, or terminal with backing; every
    refinement names successors; identifiers are not reused; nothing acts on a
    branch already closed.
    """
    codes: list[str] = []
    for leaf in forest.leaves:
        if leaf.status in (LEAF_DISCHARGED, LEAF_LOST) and not leaf.backing:
            codes.append(F_UNBACKED_TERMINAL)
        if leaf.status == LEAF_SUSPENDED and not leaf.backing:
            codes.append(F_UNROUTED_SUSPENSION)

    seen = {forest.root}
    closed: set[str] = set()
    for step in steps:
        for name, (mode, targets, _backing) in sorted(step.dispositions.items()):
            if name in closed:
                codes.append(F_ACTS_ON_CLOSED)
            if mode in (REFINE, IDENTIFY):
                if not targets:
                    codes.append(F_EMPTY_REFINEMENT)
                for target in targets:
                    if target in seen and mode == REFINE:
                        codes.append(F_REUSED_IDENTIFIER)
                    seen.add(target)
            if mode in TERMINAL:
                closed.add(name)
    return tuple(sorted(set(codes)))


def compose(first: Forest, steps_second: Sequence[Step]) -> Forest:
    """`F_{0->T} = F_{s->T} . F_{0->s}`.

    The second segment is applied to the first forest's non-terminal leaves; the
    terminal leaves are carried through unchanged. Endpoint audit therefore needs
    the first forest and the second segment, not a replay of the first segment.
    """
    carried = tuple(l for l in first.leaves
                    if l.status in (LEAF_DISCHARGED, LEAF_LOST))
    open_leaves = [l for l in first.leaves
                   if l.status in (LEAF_LIVE, LEAF_SUSPENDED)]
    leaves: list[Leaf] = list(carried)
    edges = list(first.edges)
    for leaf in open_leaves:
        sub = descend(leaf.liability_id, steps_second,
                      (leaf.status, leaf.at, leaf.backing))
        leaves.extend(sub.leaves)
        edges.extend(sub.edges)
    return Forest(first.root, tuple(leaves), tuple(edges))


# --------------------------------------------------------------------------
# The witness that a single label is not enough
# --------------------------------------------------------------------------

LOSS_WITNESS = (
    Step(0, {"L": (REFINE, ("La", "Lb"), "w-split")}),
    Step(1, {"La": (DISCHARGE, (), "witness-a")}),
)


def label_loses_information() -> tuple[str, tuple[Leaf, ...]]:
    """A split whose branches end differently.

    The single-label fold reports `live` and carries no backing; the forest
    reports one discharged leaf with its witness and one live leaf.  The label is
    not wrong, it is incomplete, and the incompleteness is exactly the branch an
    audit would want.
    """
    forest = descend("L", LOSS_WITNESS)
    return forest.label(), forest.leaves


# --------------------------------------------------------------------------
# Sweeps
# --------------------------------------------------------------------------

def _canonical(name: str, mode: str, tag: str, well_formed: bool = True):
    if not well_formed and mode in (DISCHARGE, LOSE, SUSPEND, REINSTATE):
        return (mode, (), None)
    if mode == REFINE:
        return (mode, (f"{name}.{tag}a", f"{name}.{tag}b"), f"w-{tag}")
    if mode == IDENTIFY:
        return (mode, (f"{name}.{tag}m",), f"licence-{tag}")
    if mode in (SUSPEND, REINSTATE):
        return (mode, (), f"route-{tag}")
    if mode in TERMINAL:
        return (mode, (), f"backing-{tag}")
    return (mode, (), None)


def _history(modes: Sequence[str], well_formed: bool = True) -> tuple[Step, ...]:
    """One step per mode, with **branch-varying** dispositions after a split.

    Giving every live branch the same mode would make divergent fates
    unreachable, and divergent fates are the whole reason the object is a forest.
    Branch `k` at step `i` therefore takes mode `modes[(i + k) % len(modes)]`.
    """
    live = {"L"}
    steps: list[Step] = []
    for index, mode in enumerate(modes):
        dispositions = {}
        for offset, name in enumerate(sorted(live)):
            branch_mode = modes[(index + offset) % len(modes)]
            dispositions[name] = _canonical(name, branch_mode, str(index),
                                            well_formed)
        steps.append(Step(index, dispositions))
        produced: set[str] = set()
        for name, (m, targets, _b) in dispositions.items():
            if m in (REFINE, IDENTIFY):
                produced |= set(targets)
            elif m in TERMINAL:
                continue
            else:
                produced.add(name)
        live = produced
        if not live:
            break
    return tuple(steps)


@dataclass(frozen=True)
class SweepReport:
    checked: int
    accepted: int
    leaves_total: int
    mixed: int
    label_disagrees: int


def sweep(length: int = 3, well_formed: bool = True) -> SweepReport:
    """Every mode sequence of the declared length.

    `mixed` counts histories whose forest has leaves of more than one status —
    the cases a single label cannot represent — and `label_disagrees` counts
    those where the label omits a terminal branch's backing.
    """
    checked = accepted = leaves = mixed = disagrees = 0
    for modes in product(MODES, repeat=length):
        checked += 1
        steps = _history(modes, well_formed)
        forest = descend("L", steps)
        if conservation_failures(forest, steps):
            continue
        accepted += 1
        leaves += len(forest.leaves)
        statuses = {l.status for l in forest.leaves}
        if len(statuses) > 1:
            mixed += 1
        if forest.terminal() and forest.label() not in (LEAF_DISCHARGED, LEAF_LOST):
            disagrees += 1
    return SweepReport(checked, accepted, leaves, mixed, disagrees)


@dataclass(frozen=True)
class CompositionReport:
    pairs: int
    agreements: int
    disagreements: tuple[str, ...]


def composition_sweep(length: int = 2) -> CompositionReport:
    """Composing the first forest with the second segment agrees with folding the
    whole history, over every pair of mode sequences."""
    pairs = agreements = 0
    disagreements: list[str] = []
    for first_modes in product(MODES, repeat=length):
        first_steps = _history(first_modes)
        head = descend("L", first_steps)
        if conservation_failures(head, first_steps):
            continue
        for second_modes in product(MODES, repeat=length):
            live = {l.liability_id for l in head.leaves
                    if l.status in (LEAF_LIVE, LEAF_SUSPENDED)}
            second_steps = _segment(live, second_modes, offset=length)
            whole = descend("L", tuple(first_steps) + tuple(second_steps))
            if conservation_failures(whole, tuple(first_steps) + tuple(second_steps)):
                continue
            pairs += 1
            composed = compose(head, second_steps)
            if _signature(composed) == _signature(whole):
                agreements += 1
            else:
                disagreements.append(
                    f"{','.join(first_modes)} | {','.join(second_modes)}")
    return CompositionReport(pairs, agreements, tuple(disagreements))


def _segment(live: set[str], modes: Sequence[str], offset: int) -> tuple[Step, ...]:
    steps: list[Step] = []
    current = set(live)
    for index, mode in enumerate(modes):
        dispositions = {name: _canonical(name, mode, f"s{index}")
                        for name in sorted(current)}
        steps.append(Step(offset + index, dispositions))
        produced: set[str] = set()
        for name, (m, targets, _b) in dispositions.items():
            if m in (REFINE, IDENTIFY):
                produced |= set(targets)
            elif m in TERMINAL:
                continue
            else:
                produced.add(name)
        current = produced
        if not current:
            break
    return tuple(steps)


def _signature(forest: Forest) -> tuple:
    return tuple(sorted((l.liability_id, l.status, l.backing) for l in forest.leaves))
