"""Finite exact models for answerability carriers and semantic transfer.

Semantic content is represented by finite sets in one anchored denotation domain.  The
join is set union, so overlap is allowed and missing content remains observable.  These
fixtures test the proposed interface; they are not a registered checker.
"""

from dataclasses import dataclass
from itertools import chain, combinations
from typing import Dict, FrozenSet, Iterable, Mapping, Optional, Tuple


Atom = str
Issue = str
Load = FrozenSet[Atom]


def join(parts: Iterable[Load]) -> Load:
    return frozenset(chain.from_iterable(parts))


def powerset(items: Tuple[Atom, ...]) -> Tuple[Load, ...]:
    return tuple(
        frozenset(choice)
        for size in range(len(items) + 1)
        for choice in combinations(items, size)
    )


@dataclass(frozen=True)
class MatterState:
    """One matter's anchored content and its current issue-indexed realization."""

    anchor: Load
    live: FrozenSet[Issue]
    loads: Mapping[Issue, Load]
    satisfied: Load = frozenset()
    disposed: Load = frozenset()

    @property
    def carrier_frontier(self) -> FrozenSet[Issue]:
        return frozenset(q for q in self.live if self.loads.get(q, frozenset()))

    @property
    def unresolved(self) -> Load:
        return join(self.loads.get(q, frozenset()) for q in self.carrier_frontier)

    @property
    def accounted(self) -> Load:
        return self.satisfied | self.disposed | self.unresolved

    def realizes_anchor(self) -> bool:
        return self.accounted == self.anchor


@dataclass(frozen=True)
class TransferBatch:
    """Matter-indexed semantic certificate for one structural resolution batch."""

    resolved: FrozenSet[Issue]
    parents: Mapping[Issue, FrozenSet[Issue]]
    successor_loads: Mapping[Issue, Load]
    satisfy: Load = frozenset()
    dispose: Load = frozenset()
    disposition_authorized: bool = False

    @property
    def born(self) -> FrozenSet[Issue]:
        return frozenset(self.parents)

    def structural_ok(self, pre: MatterState) -> bool:
        if not self.resolved <= pre.live or self.born & pre.live:
            return False
        if set(self.successor_loads) != set(self.parents):
            return False
        return all(bool(ps) and ps <= self.resolved for ps in self.parents.values())

    def incoming(self, pre: MatterState) -> Load:
        return join(pre.loads.get(q, frozenset()) for q in self.resolved)

    def transfer_sound(self, pre: MatterState) -> bool:
        """Every child carries only content inherited from its actual parent set."""

        if not self.structural_ok(pre):
            return False
        for child, ps in self.parents.items():
            parent_content = join(pre.loads.get(p, frozenset()) for p in ps)
            if not self.successor_loads[child] <= parent_content:
                return False
        incoming = self.incoming(pre)
        return self.satisfy <= incoming and self.dispose <= incoming

    def transfer_complete(self, pre: MatterState) -> bool:
        """The successor set and terminal receipts jointly account for all input."""

        outgoing = self.satisfy | self.dispose | join(self.successor_loads.values())
        return outgoing == self.incoming(pre)

    def terminal_ok(self) -> bool:
        return not self.dispose or self.disposition_authorized

    def valid(self, pre: MatterState) -> bool:
        return (
            self.transfer_sound(pre)
            and self.transfer_complete(pre)
            and self.terminal_ok()
        )

    def apply(self, pre: MatterState) -> MatterState:
        if not self.valid(pre):
            raise ValueError("invalid semantic transfer")
        live = (pre.live - self.resolved) | self.born
        loads: Dict[Issue, Load] = {
            q: pre.loads.get(q, frozenset()) for q in pre.live - self.resolved
        }
        loads.update(self.successor_loads)
        return MatterState(
            pre.anchor,
            live,
            loads,
            pre.satisfied | self.satisfy,
            pre.disposed | self.dispose,
        )


def answerability_conserved(initial: MatterState, batches: Tuple[TransferBatch, ...]) -> bool:
    """Finite Answerability Conservation: induction over locally valid batches."""

    if not initial.realizes_anchor():
        return False
    state = initial
    for batch in batches:
        try:
            state = batch.apply(state)
        except ValueError:
            return False
        if not state.realizes_anchor():
            return False
    terminal = not state.unresolved
    return (terminal and state.satisfied | state.disposed == state.anchor) or (
        bool(state.carrier_frontier) and state.realizes_anchor()
    )


def terminal_closure_sound(pre: MatterState, batch: TransferBatch) -> bool:
    if batch.born:
        return True
    return batch.valid(pre) and batch.satisfy | batch.dispose == batch.incoming(pre)


@dataclass(frozen=True)
class Translation:
    """Representation translation authenticated against a stable semantic domain."""

    links: Mapping[str, FrozenSet[str]]
    source_meaning: Mapping[str, Load]
    target_meaning: Mapping[str, Load]

    def complete(self) -> bool:
        return set(self.links) == set(self.source_meaning) and all(self.links.values())

    def sound(self) -> bool:
        if not self.complete():
            return False
        return all(
            join(self.target_meaning[t] for t in targets) == self.source_meaning[source]
            for source, targets in self.links.items()
        )


def compose(first: Translation, second: Translation) -> Optional[Translation]:
    if not first.sound() or not second.sound():
        return None
    if set(first.target_meaning) != set(second.source_meaning):
        return None
    links = {
        source: frozenset(
            target
            for middle in middles
            for target in second.links[middle]
        )
        for source, middles in first.links.items()
    }
    result = Translation(links, first.source_meaning, second.target_meaning)
    return result if result.sound() else None


def response_structure_local(rule: Mapping[int, str], receipts: Tuple[int, int]) -> bool:
    """One rule object is held fixed even when its two realized actions differ."""

    return rule is rule and rule[receipts[0]] != rule[receipts[1]]


def exhaustive_two_atom_conservation() -> bool:
    """Enumerate all one-parent splits over two anchored atoms."""

    atoms = ("a", "b")
    anchor = frozenset(atoms)
    pre = MatterState(anchor, frozenset({"q"}), {"q": anchor})
    subsets = powerset(atoms)
    for left in subsets:
        for right in subsets:
            for sat in subsets:
                for disp in subsets:
                    batch = TransferBatch(
                        frozenset({"q"}),
                        {"l": frozenset({"q"}), "r": frozenset({"q"})},
                        {"l": left, "r": right},
                        sat,
                        disp,
                        bool(disp),
                    )
                    if batch.valid(pre):
                        post = batch.apply(pre)
                        if not post.realizes_anchor():
                            return False
    return True
