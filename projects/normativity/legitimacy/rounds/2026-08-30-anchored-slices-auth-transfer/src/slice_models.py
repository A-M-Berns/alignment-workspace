"""Finite fixtures for anchored slices and authenticated semantic Transfer.

All denotations are exact finite joins.  Generic accounting consumes supplied semantic
values; authentication separately checks representation meanings against an anchored
interpretation context.  This is test support, not a registered checker.
"""

from dataclasses import dataclass
from itertools import chain
from typing import Dict, FrozenSet, Iterable, Mapping, Optional, Tuple


Meaning = FrozenSet[str]


def join(parts: Iterable[Meaning]) -> Meaning:
    return frozenset(chain.from_iterable(parts))


@dataclass(frozen=True)
class Slice:
    name: str
    matter: str
    born: int
    anchor: Meaning
    admission_authenticated: bool = True


@dataclass(frozen=True)
class SliceState:
    slice: Slice
    time: int
    live: FrozenSet[str]
    loads: Mapping[str, Meaning]
    satisfied: Meaning = frozenset()
    disposed: Meaning = frozenset()

    @property
    def frontier(self) -> FrozenSet[str]:
        return frozenset(q for q in self.live if self.loads.get(q, frozenset()))

    @property
    def unresolved(self) -> Meaning:
        return join(self.loads.get(q, frozenset()) for q in self.frontier)

    def valid(self) -> bool:
        if self.time < self.slice.born or not self.slice.admission_authenticated:
            return False
        return self.satisfied | self.disposed | self.unresolved == self.slice.anchor


def admit(slice_: Slice, time: int, live: FrozenSet[str], loads: Mapping[str, Meaning]) -> SliceState:
    state = SliceState(slice_, time, live, loads)
    if not state.valid():
        raise ValueError("slice admission does not account for its anchor")
    return state


@dataclass(frozen=True)
class Interpretation:
    """Historically anchored interpretation into the slice's stable semantic domain."""

    name: str
    protocol: str
    meanings: Mapping[str, Meaning]
    authenticated: bool = True

    def denotes(self, labels: Iterable[str]) -> Meaning:
        return join(self.meanings[label] for label in labels)


@dataclass(frozen=True)
class ClaimedTransfer:
    """Claimed label accounting kept separate from anchored semantic authentication."""

    source: Tuple[str, ...]
    targets: Tuple[str, ...]
    claimed_source: Meaning
    claimed_targets: Mapping[str, Meaning]

    def accounting_valid(self) -> bool:
        return self.claimed_source == join(self.claimed_targets[t] for t in self.targets)

    def authenticated(self, old: Interpretation, new: Interpretation) -> bool:
        if not self.accounting_valid() or not old.authenticated or not new.authenticated:
            return False
        return old.denotes(self.source) == new.denotes(self.targets)


def compose(
    first: ClaimedTransfer,
    second: ClaimedTransfer,
    era0: Interpretation,
    era1_out: Interpretation,
    era1_in: Interpretation,
    era2: Interpretation,
) -> Optional[ClaimedTransfer]:
    if not first.authenticated(era0, era1_out):
        return None
    if not second.authenticated(era1_in, era2):
        return None
    if first.targets != second.source:
        return None
    # The intermediate labels must have one anchored interpretation, not merely one name.
    if era1_out.protocol != era1_in.protocol:
        return None
    if era1_out.denotes(first.targets) != era1_in.denotes(second.source):
        return None
    result = ClaimedTransfer(
        first.source,
        second.targets,
        era0.denotes(first.source),
        {target: era2.meanings[target] for target in second.targets},
    )
    return result if result.authenticated(era0, era2) else None


@dataclass(frozen=True)
class RevisionAccount:
    """Explicit witnesses for retained, disposed, and newly accrued content."""

    old: Meaning
    successor: Meaning
    retained: Meaning
    disposed: Meaning = frozenset()
    disposition_authorized: bool = False
    increment: Meaning = frozenset()
    fresh_slice: Optional[Slice] = None

    def valid(self) -> bool:
        if self.old != self.retained | self.disposed:
            return False
        if self.disposed and not self.disposition_authorized:
            return False
        if self.successor != self.retained | self.increment:
            return False
        if self.increment:
            return (
                self.fresh_slice is not None
                and self.fresh_slice.anchor == self.increment
                and self.fresh_slice.admission_authenticated
            )
        return self.fresh_slice is None


@dataclass(frozen=True)
class LocalEra:
    """Ontology-local meanings with a fixed map into an anchored metalanguage."""

    name: str
    representations: Mapping[str, Meaning]
    to_anchor: Mapping[str, Meaning]
    transport_authenticated: bool = True

    def anchored(self, label: str) -> Meaning:
        return join(self.to_anchor[token] for token in self.representations[label])


def commuting_transport(old: LocalEra, old_label: str, new: LocalEra, new_label: str) -> bool:
    return (
        old.transport_authenticated
        and new.transport_authenticated
        and old.anchored(old_label) == new.anchored(new_label)
    )


def late_accretion_on_frontier(
    old_slice: SliceState,
    new_slice: Slice,
    time: int,
    carrier: str,
) -> Tuple[SliceState, SliceState]:
    if carrier not in old_slice.live:
        raise ValueError("accretion carrier must already be structurally live")
    return old_slice, admit(new_slice, time, old_slice.live, {carrier: new_slice.anchor})


class M3:
    """Five-element nondistributive lattice; only its finite join is used."""

    ZERO = "0"
    ONE = "1"
    ATOMS = frozenset({"a", "b", "c"})

    @staticmethod
    def join(x: str, y: str) -> str:
        if x == M3.ZERO:
            return y
        if y == M3.ZERO or x == y:
            return x
        if x == M3.ONE or y == M3.ONE:
            return M3.ONE
        return M3.ONE


def growing_anchor_indistinguishable() -> bool:
    """Two histories share the same final anchor while differing on when b was incurred."""

    final_anchor_early = frozenset({"a", "b"})
    final_anchor_late = frozenset({"a", "b"})
    return final_anchor_early == final_anchor_late
