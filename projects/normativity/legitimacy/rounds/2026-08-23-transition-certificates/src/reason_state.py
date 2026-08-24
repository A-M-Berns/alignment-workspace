"""Repaired finite reference model of the reason-state substrate.

This is unregistered exploration code. It adapts the PR #48 reference model
with the Part I repairs of this round's dispatch: negation is canonical by
construction, incompatibility is genuinely n-ary through a set-level Conflict
query, occurrences carry a birth index and constitutive instantiation
declarations with the applicability-in-source condition enforced at minting,
and staged case views receive an explicit prefix-determined semantics. The
substrate remains a family of total stateless queries; nothing here stores a
stance or runs an update rule.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Mapping, Union


# ---------------------------------------------------------------------------
# Content language: Atom, canonical Neg, staged App, Inst, n-ary Incomp.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Atom:
    name: str


@dataclass(frozen=True)
class Neg:
    body: "Claim"

    def __post_init__(self) -> None:
        # Canonical form: negation wraps only unnegated claims, so ¬¬x is
        # unconstructible rather than merely discouraged. neg() below is the
        # involution.
        if isinstance(self.body, Neg):
            raise TypeError("double negation is not constructible; use neg()")


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
    """The members are jointly unadoptable. Nothing follows about any proper
    subset: a ternary conflict does not induce pairwise conflict."""

    members: frozenset

    def __post_init__(self) -> None:
        if len(self.members) < 2:
            raise ValueError("an incompatibility claim needs at least two members")


Claim = Union[Atom, Neg, App, Inst, Incomp]


def neg(claim: Claim) -> Claim:
    if isinstance(claim, Neg):
        return claim.body
    return Neg(claim)


@dataclass(frozen=True)
class Receipt:
    ident: str


SourceRef = Union[Claim, Receipt]


# ---------------------------------------------------------------------------
# Constitutive structure.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Occurrence:
    """A particular reason application.

    `applied_as` is constitutive schema-use provenance: the historical fact
    that this occurrence was minted as an application of these schemas to
    these staged case views. It is distinct from the revisable classification
    claim `Inst(e, σ)` and never revised; the well-formedness condition below
    ties it to the sources. It cannot be recovered from the sources alone —
    an occurrence may cite an `App` claim as an ordinary premise without
    presenting itself as that schema's application — which is why it is data
    rather than a derived view. Occurrences with empty `applied_as` are
    permitted (a seed or brute reason applies no schema); whether a cited
    basis may contain them is record-side policy, not grammar.

    When an occurrence entered the practice is deliberately *not* a field:
    temporal provenance belongs to the append-only ledger, and consumers ask
    the prefix question through `ReasonState.existed_before`.
    """

    ident: str
    sources: frozenset  # frozenset[SourceRef]
    target: Claim
    applied_as: frozenset  # frozenset[tuple[schema, case, stage]]

    def claim_sources(self) -> frozenset:
        return frozenset(s for s in self.sources if not isinstance(s, Receipt))

    def receipt_sources(self) -> frozenset:
        return frozenset(s.ident for s in self.sources if isinstance(s, Receipt))


class ReasonState:
    """Append-only ledger of occurrences and schema identities.

    The ledger's own history carries temporal provenance: each minting is
    stamped with the record index at which it happened, held by the store
    rather than the occurrence. The public temporal query is the prefix
    predicate `existed_before`; the stamp itself is an implementation detail
    outside the frozen interface.
    """

    def __init__(self) -> None:
        self._occurrences: dict[str, Occurrence] = {}
        self._minted_at: dict[str, int] = {}
        self._schemas: set[str] = set()

    def add_schema(self, ident: str) -> None:
        self._schemas.add(ident)

    def schemas(self) -> frozenset:
        return frozenset(self._schemas)

    def mint(
        self,
        ident: str,
        sources: Iterable[SourceRef],
        target: Claim,
        at: int,
        applied_as: Iterable = (),
    ) -> Occurrence:
        if ident in self._occurrences:
            raise ValueError(f"occurrence identifier reused: {ident}")
        if isinstance(target, Receipt):
            raise TypeError("targets are claims; receipts cannot be targets")
        occ = Occurrence(ident, frozenset(sources), target, frozenset(applied_as))
        # Applicability-in-source, enforced as well-formedness: every declared
        # schema use names its staged applicability claim among the sources.
        # The check is grammar — it never judges whether the schema in fact
        # applies, only that the occurrence says what its application depends
        # on.
        for schema, case, stage in occ.applied_as:
            if App(schema, case, stage) not in occ.claim_sources():
                raise ValueError(
                    f"occurrence {ident} is applied as {schema} at "
                    f"{case}@{stage} but does not carry App({schema},{case},"
                    f"{stage}) among its sources"
                )
        self._occurrences[ident] = occ
        self._minted_at[ident] = at
        return occ

    def mint_schema_use(
        self,
        ident: str,
        grounds: Iterable[SourceRef],
        schema: str,
        case: str,
        stage: int,
        target: Claim,
        at: int,
    ) -> Occurrence:
        """The enforcing constructor for schema applications: the staged
        applicability source and the schema-use provenance cannot come apart
        because both are inserted here."""
        return self.mint(
            ident,
            frozenset(grounds) | {App(schema, case, stage)},
            target,
            at,
            applied_as={(schema, case, stage)},
        )

    def occurrence(self, ident: str) -> Occurrence:
        return self._occurrences[ident]

    def has(self, ident: str) -> bool:
        return ident in self._occurrences

    def existed_before(self, ident: str, index: int) -> bool:
        """Whether the occurrence entered the practice strictly before the
        given record index. The prefix question is the public temporal fact;
        consumers never read a birth stamp off the occurrence."""
        return ident in self._minted_at and self._minted_at[ident] < index

    def occurrences(self) -> tuple[Occurrence, ...]:
        return tuple(self._occurrences.values())


# ---------------------------------------------------------------------------
# Case views: the smallest explicit semantics for c@n. The view is determined
# by the case identity and the prefix of arrivals procedurally tied to it; it
# lives outside the reason state, and App claims keep bare (σ, c, n) identity.
# ---------------------------------------------------------------------------


def case_view(
    case: str,
    stage: int,
    arrivals: Mapping[str, int],
    provenance: frozenset,
) -> frozenset:
    """The receipts procedurally tied to `case` that had arrived by `stage`.

    `arrivals` maps receipt identity to its record arrival index and
    `provenance` is the T relation as (case, receipt) pairs. Views are
    prefix-determined and monotone in `stage`: later arrivals extend later
    views and never rewrite earlier ones, so delayed evidence grounds
    corrections about old staged claims without retroactive view change.
    """
    return frozenset(
        receipt
        for (c, receipt) in provenance
        if c == case and receipt in arrivals and arrivals[receipt] <= stage
    )


# ---------------------------------------------------------------------------
# The narrow-waist queries. Total and stateless.
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
    return tuple(occ.ident for occ in state.occurrences() if source in occ.sources)


def explain(state: ReasonState, ident: str) -> tuple:
    """All constitutive occurrence data, as the frozen contract promises:
    sources, target, and schema-use provenance."""
    occ = state.occurrence(ident)
    return occ.sources, occ.target, occ.applied_as


# Conflict is the set-level notion; binary incompatibility is its two-element
# special case and is deliberately not complete for conflict.


def conflict(members: frozenset, stance: frozenset) -> bool:
    if any(neg(x) in members for x in members):
        return True
    return any(
        isinstance(claim, Incomp) and claim.members <= members
        for claim in stance
    )


def incompatible(a: Claim, b: Claim, stance: frozenset) -> bool:
    return conflict(frozenset({a, b}), stance)


def criticizable(stance: frozenset) -> bool:
    """A stance violating the floor or an incompatibility it itself adopts.
    Representable — the queries stay total on it — but exposed."""
    return conflict(stance, stance)


def undercuts(state: ReasonState, attacker: str, victim: str, stance: frozenset, transcript: frozenset) -> bool:
    if not enabled(state, attacker, stance, transcript):
        return False
    target = state.occurrence(attacker).target
    return any(
        isinstance(src, App) and neg(target) == src
        for src in state.occurrence(victim).claim_sources()
    )


def rebuts(state: ReasonState, one: str, other: str, stance: frozenset, transcript: frozenset) -> bool:
    if not (enabled(state, one, stance, transcript) and enabled(state, other, stance, transcript)):
        return False
    return incompatible(
        state.occurrence(one).target, state.occurrence(other).target, stance
    )


def joint_conflicts(
    state: ReasonState,
    idents: Iterable[str],
    stance: frozenset,
    transcript: frozenset,
) -> bool:
    """Whether the targets of the given live occurrences are jointly
    unadoptable at this stance. The n-ary exposure that binary rebuttal
    cannot supply."""
    live = [i for i in idents if enabled(state, i, stance, transcript)]
    targets = frozenset(state.occurrence(i).target for i in live)
    return conflict(targets, stance)


# ---------------------------------------------------------------------------
# Reliance reporting, unchanged from PR #48.
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
    return tuple(
        entry
        for entry in log
        if not enabled(state, entry.occurrence, stance, transcript)
    )


def provenance_manifest(state: ReasonState, cited: Iterable[str]) -> tuple:
    """The two-sorted direct dependencies of a cited occurrence set.

    Returns `(receipt_deps, direct_claim_deps)`: every receipt source and
    every claim source of a cited occurrence. Cited targets are deliberately
    NOT subtracted: a cited occurrence targeting `v` exposes support for `v`
    but does not put `v` into any stance, so `v` remains a live stance
    dependency of every cited occurrence that consumes it — subtracting it
    would import the support-implies-endorsement closure the substrate
    forbids. Discharging a claim dependency requires record-side evidence of
    an accountable endorsement transition, which is a frontier-side notion
    over the diary, not a ledger computation. Purely syntactic and
    computable; it claims nothing about fundability or settlement safety."""
    cited_set = frozenset(cited)
    receipts: set = set()
    claims: set = set()
    for ident in cited_set:
        if not state.has(ident):
            continue
        occ = state.occurrence(ident)
        receipts |= set(occ.receipt_sources())
        claims |= set(occ.claim_sources())
    return frozenset(receipts), frozenset(claims)
