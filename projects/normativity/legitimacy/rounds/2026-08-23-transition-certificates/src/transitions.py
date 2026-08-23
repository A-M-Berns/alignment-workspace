"""Reason-accounted transition certificates over the repaired substrate.

This is unregistered exploration code. A certificate says: this transition
cites these particular reason occurrences as grounds, this prior authority act
as its normative license, and these existing commitments as its account
lineage. The checker enforces strict pre-state citation; it never judges
whether the cited applicability judgments are true or whether the practice's
authority is substantively apt. Account conservation and review minting stay
in the record layer — the certificate supplies the frozen citation those
mechanisms consume, and `transition_lost_basis` is the detection query.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping

from reason_state import App, ReasonState, enabled, explain


KINDS = (
    "belief-revision",
    "practical-undertaking",
    "schema-reclassification",
    "rule-amendment",
    "inquiry-launch",
)


@dataclass(frozen=True)
class AuthorityAct:
    """Minimal record-side authority: an act with strict pre-state license
    parents and a typed scope of transition kinds it can license. A stand-in
    for the record's rule machinery, kept exactly rich enough to test the
    certificate discipline against the seed-terminating genealogy rule."""

    ident: str
    index: int
    seed: bool = False
    license_parents: tuple = ()
    scope: frozenset = frozenset()


def genealogy_errors(acts: Mapping[str, AuthorityAct]) -> tuple:
    """Seed-only roots and strictly earlier license parents, after the
    afoundational-inquiry discipline, over an entire authority record. With
    no errors, every maximal backward license path terminates at a seed.
    This is the record layer's global invariant; certificate checking uses
    the ancestral form below, so an unrelated malformed act cannot fail an
    otherwise sound certificate."""
    return ancestral_errors(acts, tuple(acts))


def ancestral_errors(acts: Mapping[str, AuthorityAct], roots) -> tuple:
    """The genealogy discipline restricted to the ancestral closure of the
    given acts: the acts a certificate's cited license actually rests on."""
    errors = []
    seen: set = set()
    frontier = [r for r in roots if r in acts]
    while frontier:
        ident = frontier.pop()
        if ident in seen:
            continue
        seen.add(ident)
        act = acts[ident]
        if act.seed:
            if act.license_parents:
                errors.append(f"seed-with-parents:{act.ident}")
        elif not act.license_parents:
            errors.append(f"new-root:{act.ident}")
        for parent_id in act.license_parents:
            parent = acts.get(parent_id)
            if parent is None:
                errors.append(f"unknown-parent:{act.ident}:{parent_id}")
            elif parent.index >= act.index:
                errors.append(f"non-prior-parent:{act.ident}:{parent_id}")
            else:
                frontier.append(parent_id)
    return tuple(errors)


@dataclass(frozen=True)
class Certificate:
    """The candidate narrow waist for a reason-accounted transition.

    `basis` cites particular occurrence identities (grounds: why this
    content). `license` cites one authority act (normative license: what
    entitled this kind of act). `consumed` cites the existing commitment
    identities the transition disposes of or transforms (account lineage:
    what is being answered). The three are separate fields on purpose; the
    conflation kill test fails any checker that pools them.
    """

    move: str
    kind: str
    index: int
    basis: tuple
    license: str
    consumed: tuple = ()


@dataclass(frozen=True)
class CheckResult:
    valid: bool
    failures: tuple
    receipt: frozenset  # frozen snapshot of the cited constitutive structure


def pre_transcript(arrivals: Mapping[str, int], index: int) -> frozenset:
    """The receipts available strictly before the transition's index."""
    return frozenset(r for r, at in arrivals.items() if at < index)


def check_certificate(
    state: ReasonState,
    acts: Mapping[str, AuthorityAct],
    commitments: Mapping[str, int],
    cert: Certificate,
    pre_stance: frozenset,
    arrivals: Mapping[str, int],
) -> CheckResult:
    """Strict pre-state citation, with explanatory failures.

    Every failure names the offending citation, so a verdict change is
    inspectable without a global diff. The returned receipt freezes the cited
    occurrences' constitutive data; because occurrences are immutable and
    append-only, re-deriving it later must reproduce it, which is the
    checkable form of `the claimed historical basis cannot be rewritten`.
    """
    failures = []
    transcript = pre_transcript(arrivals, cert.index)

    if cert.kind not in KINDS:
        failures.append(("unknown-kind", cert.kind))
    if not cert.basis:
        failures.append(("empty-basis", cert.move))
    for ident in cert.basis:
        if not state.has(ident):
            failures.append(("unknown-basis", ident))
            continue
        occ = state.occurrence(ident)
        if not state.existed_before(ident, cert.index):
            failures.append(("posterior-basis", ident))
        if not enabled(state, ident, pre_stance, transcript):
            missing_claims = occ.claim_sources() - pre_stance
            missing_receipts = occ.receipt_sources() - transcript
            witness = next(iter(missing_claims), None) or next(
                iter(missing_receipts), None
            )
            failures.append(("basis-not-enabled", (ident, witness)))

    act = acts.get(cert.license)
    if act is None:
        failures.append(("unknown-license", cert.license))
    else:
        if act.index >= cert.index:
            failures.append(("posterior-license", cert.license))
        if cert.kind not in act.scope:
            failures.append(("license-scope", (cert.license, cert.kind)))
        # Locality: only the cited license's ancestral closure is validated.
        # An unrelated malformed authority act elsewhere in the record is the
        # record layer's problem (its global invariant is genealogy_errors),
        # never a local certificate failure.
        for err in ancestral_errors(acts, (cert.license,)):
            failures.append(("license-genealogy", err))

    for ident in cert.consumed:
        if ident not in commitments:
            failures.append(("unknown-lineage", ident))
        elif commitments[ident] >= cert.index:
            failures.append(("posterior-lineage", ident))

    # The receipt freezes every constitutive fact about each cited
    # occurrence — sources, target, and schema-use provenance — so what the
    # certificate relied on is reproducible later without consulting any
    # revisable interpretation. Reclassification moves Inst claims only; it
    # cannot reach this snapshot.
    receipt = frozenset(
        (ident,) + explain(state, ident)
        for ident in cert.basis
        if state.has(ident)
    )
    return CheckResult(not failures, tuple(failures), receipt)


def applicability_provenance(state: ReasonState, cert: Certificate) -> frozenset:
    """The App claims actually present among the cited constitutive sources.
    Derived from structure — the certificate never restates applicability, so
    it cannot misstate it."""
    apps = set()
    for ident in cert.basis:
        if state.has(ident):
            apps |= {
                src
                for src in state.occurrence(ident).claim_sources()
                if isinstance(src, App)
            }
    return frozenset(apps)


def transition_lost_basis(
    state: ReasonState,
    cert: Certificate,
    stance: frozenset,
    transcript: frozenset,
) -> tuple:
    """Cited occurrences no longer enabled under the current stance. The
    frozen citation makes this well-defined: an alternative reason for the
    same conclusion never silences it. The record's review machinery, not
    this query, decides what follows."""
    return tuple(
        ident
        for ident in cert.basis
        if state.has(ident) and not enabled(state, ident, stance, transcript)
    )


def licensed(
    state: ReasonState,
    acts: Mapping[str, AuthorityAct],
    commitments: Mapping[str, int],
    cert: Certificate,
    pre_stance: frozenset,
    arrivals: Mapping[str, int],
) -> bool:
    """The certificate-witnessed Licensed predicate: licensed within the
    current accountable practice, nothing more."""
    return check_certificate(state, acts, commitments, cert, pre_stance, arrivals).valid
