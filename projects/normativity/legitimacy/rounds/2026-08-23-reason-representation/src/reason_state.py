"""Finite reference model for the reason-state narrow-waist prosecution.

This is unregistered exploration code. It exists to keep six things apart under
adversarial tests: constitutive structure, reflective reason contents,
case/docket/transcript provenance, reason availability, stance, and historical
reliance. Everything is exact and finite; there is no search, no label store,
and no update rule. The substrate is a set of total queries over
(structure, stance, transcript); anything that chooses what to believe lives in
the explicitly named policy layer at the bottom of this file.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, Mapping, Union


# ---------------------------------------------------------------------------
# Content language.
#
# Claims are the possible members of a stance and the possible claim-sources
# and targets of reason occurrences. The constructors are deliberately few:
# Atom, Neg (constitutive contradiction floor), App (staged applicability),
# Inst (schema membership), Incomp (reified n-ary incompatibility). There are
# no Hold/Do/May/Must/Supported/Live constructors.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Atom:
    name: str


@dataclass(frozen=True)
class Neg:
    body: "Claim"


@dataclass(frozen=True)
class App:
    schema: str
    case: str
    stage: int


@dataclass(frozen=True)
class Inst:
    occurrence: str
    schema: str


@dataclass(frozen=True)
class Incomp:
    members: frozenset


Claim = Union[Atom, Neg, App, Inst, Incomp]


def neg(claim: Claim) -> Claim:
    """Involutive negation: neg(neg(x)) is x."""
    if isinstance(claim, Neg):
        return claim.body
    return Neg(claim)


def contradicts(a: Claim, b: Claim) -> bool:
    return neg(a) == b


@dataclass(frozen=True)
class Receipt:
    """A reference to a transcript event used as a source element."""

    ident: str


SourceRef = Union[Claim, Receipt]


# ---------------------------------------------------------------------------
# Constitutive structure: occurrences, schemas, cases, docket, transcript.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Occurrence:
    """A particular reason application. Sources and target are constitutive:
    they are fixed at minting and are not revisable content."""

    ident: str
    sources: frozenset  # frozenset[SourceRef]
    target: Claim

    def claim_sources(self) -> frozenset:
        return frozenset(s for s in self.sources if not isinstance(s, Receipt))

    def receipt_sources(self) -> frozenset:
        return frozenset(s.ident for s in self.sources if isinstance(s, Receipt))


class ReasonState:
    """Append-only store of occurrences and schema identities.

    There is no removal operation: an occurrence is disabled by its sources
    leaving the stance, never by deletion. Identifiers are never reused, so
    record-side reliance references stay resolvable forever.
    """

    def __init__(self) -> None:
        self._occurrences: dict[str, Occurrence] = {}
        self._schemas: set[str] = set()

    def add_schema(self, ident: str) -> None:
        self._schemas.add(ident)

    def schemas(self) -> frozenset:
        return frozenset(self._schemas)

    def mint(self, ident: str, sources: Iterable[SourceRef], target: Claim) -> Occurrence:
        if ident in self._occurrences:
            raise ValueError(f"occurrence identifier reused: {ident}")
        if isinstance(target, Receipt):
            raise TypeError("targets are claims; receipts cannot be targets")
        occ = Occurrence(ident, frozenset(sources), target)
        self._occurrences[ident] = occ
        return occ

    def occurrence(self, ident: str) -> Occurrence:
        return self._occurrences[ident]

    def occurrences(self) -> tuple[Occurrence, ...]:
        return tuple(self._occurrences.values())


@dataclass(frozen=True)
class Practice:
    """Case, docket, and transcript provenance around one reason state.

    Cases are opaque identities. Docket items are obligations *about* cases.
    The transcript is the set of receipt identifiers so far. `provenance` is
    the procedural relation T: receipt r arose in working on case c. Nothing
    here generates reasons; the adversarial tests check that.
    """

    cases: frozenset = frozenset()
    docket_about: Mapping[str, str] = field(default_factory=dict)
    open_docket: frozenset = frozenset()
    transcript: frozenset = frozenset()
    provenance: frozenset = frozenset()  # frozenset[tuple[case, receipt]]


# ---------------------------------------------------------------------------
# The narrow-waist queries. All are total functions of
# (state, stance B, transcript L); none stores or mutates anything, so a
# hypothetical query is the same function at another argument.
# ---------------------------------------------------------------------------


def enabled(state: ReasonState, ident: str, stance: frozenset, transcript: frozenset) -> bool:
    occ = state.occurrence(ident)
    return occ.claim_sources() <= stance and occ.receipt_sources() <= transcript


def reasons(state: ReasonState, target: Claim, stance: frozenset, transcript: frozenset) -> tuple[str, ...]:
    return tuple(
        occ.ident
        for occ in state.occurrences()
        if occ.target == target and enabled(state, occ.ident, stance, transcript)
    )


def bearing(state: ReasonState, stance: frozenset, transcript: frozenset) -> frozenset:
    return frozenset(
        occ.target
        for occ in state.occurrences()
        if enabled(state, occ.ident, stance, transcript)
    )


def dependents(state: ReasonState, source: SourceRef) -> tuple[str, ...]:
    """Which occurrences would a change in this source's standing touch."""
    return tuple(occ.ident for occ in state.occurrences() if source in occ.sources)


def explain(state: ReasonState, ident: str) -> tuple[frozenset, Claim]:
    occ = state.occurrence(ident)
    return occ.sources, occ.target


# Derived attack relations. Neither is structure: both are computed from
# constitutive sources/targets plus the stance, and both are stance-relative
# because substantive incompatibility is adopted content.


def undercuts(state: ReasonState, attacker: str, victim: str, stance: frozenset, transcript: frozenset) -> bool:
    if not enabled(state, attacker, stance, transcript):
        return False
    target = state.occurrence(attacker).target
    return any(
        isinstance(src, App) and contradicts(target, src)
        for src in state.occurrence(victim).claim_sources()
    )


def incompatible(a: Claim, b: Claim, stance: frozenset) -> bool:
    if contradicts(a, b):
        return True
    return any(
        isinstance(claim, Incomp) and {a, b} <= set(claim.members)
        for claim in stance
    )


def rebuts(state: ReasonState, one: str, other: str, stance: frozenset, transcript: frozenset) -> bool:
    if not (enabled(state, one, stance, transcript) and enabled(state, other, stance, transcript)):
        return False
    return incompatible(
        state.occurrence(one).target, state.occurrence(other).target, stance
    )


# ---------------------------------------------------------------------------
# Record-side reliance stub. Reliance is a historical fact in the normative
# record, not a claim in V: the entries are append-only and a currently valid
# alternative support never removes one.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Reliance:
    move: str
    occurrence: str
    stage: int


def lost_basis(
    state: ReasonState,
    log: tuple,
    stance: frozenset,
    transcript: frozenset,
) -> tuple:
    """Reliances whose occurrence is not enabled under the current stance.

    This is the report the record's basis-loss review machinery consumes. The
    substrate reports; whether to reaffirm, revise, or review is not decided
    here.
    """
    return tuple(
        entry
        for entry in log
        if not enabled(state, entry.occurrence, stance, transcript)
    )


# ---------------------------------------------------------------------------
# Policy layer. Everything below is explicitly NOT the substrate: it is one
# possible stance policy (credulous closure) plus the label machinery an
# ATMS-style backend would cache for it. It exists to witness that JTMS/ATMS
# functionality is (policy + caching) over the queries above, and that
# nogood-hood is policy-relative once incompatibility is adopted content.
# ---------------------------------------------------------------------------


def support_closure(
    state: ReasonState,
    assumptions: frozenset,
    transcript: frozenset,
) -> frozenset:
    """The credulous policy: adopt every claim some live reason bears on.

    This is the rule `Reasons_B(v) != {} implies v in B` that the substrate
    itself must never apply. It is a legitimate *policy* when named as one.
    """
    stance = frozenset(assumptions)
    while True:
        new = frozenset(
            occ.target
            for occ in state.occurrences()
            if enabled(state, occ.ident, stance, transcript)
        )
        grown = stance | new
        if grown == stance:
            return stance
        stance = grown


def _minimal_antichain(sets: Iterable[frozenset]) -> frozenset:
    pool = set(sets)
    return frozenset(
        s for s in pool if not any(t < s for t in pool)
    )


def labels_by_enumeration(
    state: ReasonState,
    universe: frozenset,
    transcript: frozenset,
    target: Claim,
) -> frozenset:
    """Minimal assumption environments whose closure adopts the target."""
    universe_list = sorted(universe, key=repr)
    hits = []
    for mask in range(1 << len(universe_list)):
        env = frozenset(
            claim for i, claim in enumerate(universe_list) if mask >> i & 1
        )
        if target in support_closure(state, env, transcript):
            hits.append(env)
    return _minimal_antichain(hits)


def labels_by_propagation(
    state: ReasonState,
    universe: frozenset,
    transcript: frozenset,
) -> dict:
    """ATMS-style label propagation: for each claim, the minimal environments
    supporting it under the credulous policy. A distinct backend for the same
    queries; the tests check extensional agreement with enumeration."""
    labels: dict[Claim, frozenset] = {claim: frozenset({frozenset({claim})}) for claim in universe}

    def label_of(claim: Claim) -> frozenset:
        return labels.get(claim, frozenset())

    changed = True
    while changed:
        changed = False
        for occ in state.occurrences():
            if not occ.receipt_sources() <= transcript:
                continue
            source_labels = [label_of(c) for c in occ.claim_sources()]
            if any(not lab for lab in source_labels):
                continue
            combos = [frozenset()]
            for lab in source_labels:
                combos = [env | pick for env in combos for pick in lab]
            candidate = _minimal_antichain(set(combos) | set(label_of(occ.target)))
            if candidate != label_of(occ.target):
                labels[occ.target] = candidate
                changed = True
    return labels


def nogoods(
    state: ReasonState,
    universe: frozenset,
    transcript: frozenset,
    closure_policy,
) -> frozenset:
    """Environments whose stance under the given policy violates an
    incompatibility that the same stance adopts. Nogood-hood depends on the
    policy argument: it is not a fact about the structure alone."""
    universe_list = sorted(universe, key=repr)
    bad = []
    for mask in range(1 << len(universe_list)):
        env = frozenset(
            claim for i, claim in enumerate(universe_list) if mask >> i & 1
        )
        stance = closure_policy(state, env, transcript)
        conflict = any(
            isinstance(claim, Incomp) and set(claim.members) <= stance
            for claim in stance
        ) or any(neg(claim) in stance for claim in stance)
        if conflict:
            bad.append(env)
    return _minimal_antichain(bad)
