"""Exact finite models for semantic mutation, faithfulness, and slice admission.

The fixtures separate three interfaces.  Mutation accounting conserves anchored
finite-join values.  Slice faithfulness reflects a supplied answerability preorder
on admissible representations.  Admission combines semantic authentication with
independent grounded provenance.  This is test support, not a registered checker.
"""

from dataclasses import dataclass
from itertools import combinations
from typing import Callable, FrozenSet, Iterable, Mapping, Sequence


Meaning = FrozenSet[str]


def join(parts: Iterable[Meaning]) -> Meaning:
    out: set[str] = set()
    for part in parts:
        out.update(part)
    return frozenset(out)


@dataclass(frozen=True)
class Allocation:
    live: FrozenSet[str]
    loads: Mapping[str, Meaning]

    def load(self, carrier: str) -> Meaning:
        return self.loads.get(carrier, frozenset())


@dataclass(frozen=True)
class SemanticBatch:
    """Generalized Transfer over all structurally or semantically affected carriers."""

    before: Allocation
    after: Allocation
    old_affected: FrozenSet[str]
    new_affected: FrozenSet[str]
    satisfied: Meaning = frozenset()
    disposed: Meaning = frozenset()
    disposition_authorized: bool = False
    authenticated: bool = True

    def identity_frame(self) -> bool:
        all_carriers = self.before.live | self.after.live
        for q in all_carriers:
            old_in = q in self.before.live
            new_in = q in self.after.live
            changed = old_in != new_in or self.before.load(q) != self.after.load(q)
            covered = q in self.old_affected or q in self.new_affected
            if changed and not covered:
                return False
            if not covered and old_in and new_in and self.before.load(q) != self.after.load(q):
                return False
        return True

    def accounting_valid(self) -> bool:
        incoming = join(self.before.load(q) for q in self.old_affected)
        outgoing = (
            self.satisfied
            | self.disposed
            | join(self.after.load(q) for q in self.new_affected)
        )
        return incoming == outgoing

    def valid(self) -> bool:
        return (
            self.identity_frame()
            and self.accounting_valid()
            and self.authenticated
            and (not self.disposed or self.disposition_authorized)
        )


@dataclass(frozen=True)
class SliceSemantics:
    """A local language mapped to a stable anchor, with answerability relevance."""

    token_map: Mapping[str, Meaning]
    relevant_tokens: FrozenSet[str]
    admissible: FrozenSet[Meaning]

    def anchor(self, value: Meaning) -> Meaning:
        return join(self.token_map[token] for token in value)

    def relevant(self, value: Meaning) -> Meaning:
        return value & self.relevant_tokens

    def join_preserving(self) -> bool:
        values = list(self.admissible)
        if frozenset() not in self.admissible or self.anchor(frozenset()):
            return False
        for x in values:
            for y in values:
                if (x | y) in self.admissible:
                    if self.anchor(x | y) != self.anchor(x) | self.anchor(y):
                        return False
        return True

    def equality_reflecting(self) -> bool:
        return all(
            self.anchor(x) != self.anchor(y) or self.relevant(x) == self.relevant(y)
            for x in self.admissible for y in self.admissible
        )

    def order_reflecting(self) -> bool:
        return all(
            not (self.anchor(x) <= self.anchor(y))
            or self.relevant(x) <= self.relevant(y)
            for x in self.admissible for y in self.admissible
        )

    def adequate(self) -> bool:
        return self.join_preserving() and self.order_reflecting()


def powerset(tokens: Sequence[str]) -> FrozenSet[Meaning]:
    return frozenset(
        frozenset(c)
        for size in range(len(tokens) + 1)
        for c in combinations(tokens, size)
    )


def bridges_compose(
    first: SliceSemantics,
    second: SliceSemantics,
    shared_anchor_values: Iterable[Meaning],
    quotient_compatible: bool = True,
) -> bool:
    """Faithfulness composes only through one anchored relevance commitment."""

    return (
        quotient_compatible
        and first.adequate()
        and second.adequate()
        and all(value in first.admissible and value in second.admissible
                for value in shared_anchor_values)
    )


@dataclass(frozen=True)
class Admission:
    semantic_authenticated: bool
    grounds: FrozenSet[str]
    standing_authorizers: FrozenSet[str]
    origin_valid: bool
    seed: bool = False

    def grounded(self) -> bool:
        if self.seed:
            return self.origin_valid
        return (
            bool(self.grounds)
            and self.grounds <= self.standing_authorizers
            and self.origin_valid
        )

    def valid(self) -> bool:
        return self.semantic_authenticated and self.grounded()


def activated_due(
    was_due: bool,
    is_due: bool,
    semantic_authenticated: bool,
    authorizer: str,
    standing: FrozenSet[str],
    origin_valid: bool,
) -> Admission:
    """A Due rising edge realizes admission but does not generate its grounds."""

    return Admission(
        semantic_authenticated,
        frozenset({authorizer}) if is_due and not was_due else frozenset(),
        standing,
        origin_valid and is_due and not was_due,
    )
