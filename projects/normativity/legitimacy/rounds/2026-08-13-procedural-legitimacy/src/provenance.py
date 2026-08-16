"""Provenance: typed, non-circular authority ancestry.

The distinction the condition has to draw is between **deriving a reason** and
**manufacturing authority**.  A bounded reasoner must be able to do the first
freely — inference, proof, conceptual innovation, and genuine defeaters are all
new grounds it produces itself — and must not be able to do the second at all.

The separation is carried by two fields with different rules. `content` is free:
any ground may assert anything, and nothing here restricts what a reasoner may
think of. `scope` is not free: it is the set of coordinates a ground is entitled
to bear on, and a derived ground's scope is bounded by its parents'.

So authority flows downward and never upward, while content flows in any
direction the reasoner likes.

Two scope disciplines are implemented because the round found they differ:
`union` bounds a child by the union of its parents' scopes, `intersection` by
their intersection.  Which is right depends on whether the constraint being
licensed is coordinate-wise or joint, and the tests display a case that
separates them.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, Mapping, Sequence

CONFERRED = "conferred"
DERIVED = "derived"

UNION = "union"
INTERSECTION = "intersection"


@dataclass(frozen=True)
class Ground:
    """A reason on the record, with its authority ancestry.

    `basis` names the grounds this one was derived from.  A ground with no basis
    is a root, and a root's authority is legitimate only if an external source
    conferred it — the reasoner may write a root down, and doing so is exactly
    what the provenance condition refuses.
    """

    ground_id: str
    filed_at: int
    content: str
    scope: frozenset[str]
    basis: tuple[str, ...] = ()
    origin: str = DERIVED
    defeated_at: int | None = None
    filed_by: str = "reasoner"

    @property
    def is_root(self) -> bool:
        return not self.basis


P_UNKNOWN_BASIS = "provenance.unknown_basis"
P_CYCLE = "provenance.cyclic_basis"
P_UNCONFERRED_ROOT = "provenance.unconferred_root"
P_AMPLIFIED = "provenance.scope_amplified"
P_BASIS_NOT_EARLIER = "provenance.basis_not_earlier"
P_DEFEATED = "provenance.defeated"
P_OUT_OF_SCOPE = "provenance.out_of_scope"


@dataclass(frozen=True)
class ProvenanceVerdict:
    valid: bool
    code: str = ""
    detail: str = ""


@dataclass(frozen=True)
class GroundStore:
    grounds: tuple[Ground, ...]

    def get(self, ground_id: str) -> Ground | None:
        for ground in self.grounds:
            if ground.ground_id == ground_id:
                return ground
        return None

    def visible(self, at: int) -> tuple[Ground, ...]:
        return tuple(g for g in self.grounds if g.filed_at <= at)

    def with_ground(self, ground: Ground) -> "GroundStore":
        return GroundStore(self.grounds + (ground,))


def ancestry(store: GroundStore, ground_id: str) -> tuple[frozenset[str], str]:
    """Every root reachable from a ground, or the code for why there is none.

    Well-foundedness is decided here rather than assumed: the walk carries its
    own path and refuses a repeat, so a cycle is a verdict instead of a hang.
    """
    roots: set[str] = set()
    stack: list[tuple[str, tuple[str, ...]]] = [(ground_id, ())]
    while stack:
        current, path = stack.pop()
        if current in path:
            return frozenset(), P_CYCLE
        ground = store.get(current)
        if ground is None:
            return frozenset(), P_UNKNOWN_BASIS
        if ground.is_root:
            roots.add(current)
            continue
        for parent in ground.basis:
            stack.append((parent, path + (current,)))
    return frozenset(roots), ""


def _parent_bound(store: GroundStore, ground: Ground,
                  discipline: str) -> frozenset[str] | None:
    scopes = []
    for parent_id in ground.basis:
        parent = store.get(parent_id)
        if parent is None:
            return None
        scopes.append(set(parent.scope))
    if not scopes:
        return None
    bound = set(scopes[0])
    for other in scopes[1:]:
        bound = (bound | other) if discipline == UNION else (bound & other)
    return frozenset(bound)


def provenance_valid(store: GroundStore, ground_id: str, coordinate: str, at: int,
                     conferring_sources: Iterable[str] = ("settlement",),
                     discipline: str = UNION) -> ProvenanceVerdict:
    """`Pi_t(g, c)`: may this ground bear on this coordinate at this date?

    Six clauses.  The first three are about the ancestry as a graph, the next two
    about each derivation step, the last about this particular use.
    """
    sources = set(conferring_sources)
    roots, failure = ancestry(store, ground_id)
    if failure:
        return ProvenanceVerdict(False, failure, ground_id)

    for root_id in sorted(roots):
        root = store.get(root_id)
        if root is None:
            return ProvenanceVerdict(False, P_UNKNOWN_BASIS, root_id)
        if root.origin != CONFERRED or root.filed_by not in sources:
            return ProvenanceVerdict(
                False, P_UNCONFERRED_ROOT,
                f"{root_id} is a root the reasoner supplied itself")

    seen: set[str] = set()
    frontier = [ground_id]
    while frontier:
        current = frontier.pop()
        if current in seen:
            continue
        seen.add(current)
        ground = store.get(current)
        if ground is None:
            return ProvenanceVerdict(False, P_UNKNOWN_BASIS, current)
        if ground.is_root:
            continue
        bound = _parent_bound(store, ground, discipline)
        if bound is None:
            return ProvenanceVerdict(False, P_UNKNOWN_BASIS, current)
        outside = set(ground.scope) - set(bound)
        if outside:
            return ProvenanceVerdict(
                False, P_AMPLIFIED,
                f"{current} claims {sorted(outside)} no parent carries")
        for parent_id in ground.basis:
            parent = store.get(parent_id)
            if parent is not None and parent.filed_at >= ground.filed_at:
                return ProvenanceVerdict(
                    False, P_BASIS_NOT_EARLIER,
                    f"{current} cites {parent_id} filed at or after it")
            frontier.append(parent_id)

    ground = store.get(ground_id)
    assert ground is not None
    if ground.defeated_at is not None and ground.defeated_at <= at:
        return ProvenanceVerdict(False, P_DEFEATED, ground_id)
    if coordinate not in ground.scope:
        return ProvenanceVerdict(False, P_OUT_OF_SCOPE,
                                 f"{ground_id} has no scope over {coordinate}")
    return ProvenanceVerdict(True)


def valid_context(store: GroundStore, coordinate: str, at: int,
                  conferring_sources: Iterable[str] = ("settlement",),
                  discipline: str = UNION) -> tuple[Ground, ...]:
    """`R_valid`: the grounds entitled to bear on a coordinate at a date."""
    return tuple(g for g in store.visible(at)
                 if provenance_valid(store, g.ground_id, coordinate, at,
                                     conferring_sources, discipline).valid)


# --------------------------------------------------------------------------
# The no-amplification statement
# --------------------------------------------------------------------------

def conferred_bound(store: GroundStore, ground_id: str,
                    conferred: Mapping[str, frozenset[str]],
                    discipline: str = UNION) -> frozenset[str]:
    """The union of what this ground's roots were actually granted."""
    roots, failure = ancestry(store, ground_id)
    if failure:
        return frozenset()
    bound: set[str] = set()
    for root in roots:
        bound |= set(conferred.get(root, frozenset()))
    return frozenset(bound)


def amplifies(store: GroundStore, ground_id: str,
              conferred: Mapping[str, frozenset[str]],
              discipline: str = UNION) -> bool:
    """Whether a ground's scope exceeds what its roots were granted.

    The statement the condition is supposed to make true is that no
    provenance-valid ground amplifies.  This function computes the antecedent's
    negation so a sweep can check it rather than assert it.
    """
    ground = store.get(ground_id)
    if ground is None:
        return False
    return bool(set(ground.scope) - set(conferred_bound(store, ground_id,
                                                        conferred, discipline)))
