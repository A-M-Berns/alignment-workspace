"""The lawful-edit certificate and the checks that decide it.

The interface takes an actual prefix, the actual response, and a proposed
replacement, and returns `ADMITTED`, `REJECTED` with an obstruction code, or
`UNRESOLVED` where a supplied policy relation declines to rule. It is deliberately
not a theory of reasons: what is substantively normative is a named parameter in
`PolicySuite`, and what is mechanical is checked here.

The one thing the interface is not allowed to be is a function of cost. That is
enforced by the reader's footprint rather than by discipline: `check` runs
against a `PrefixReader` that raises on the charge table, so a check that tried
to consult profitability would fail loudly instead of quietly succeeding.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction as Q
from typing import Callable, Mapping, Sequence

from src.model import (
    BASIS_DECLINE,
    BASIS_DEFAULT,
    BASIS_MERITS,
    CERTIFIER_FOOTPRINT,
    CLOSURE_DISCHARGE,
    CLOSURE_PROCEDURAL,
    KIND_IMPEDIMENT,
    KIND_INTERVAL,
    KIND_RATIFICATION,
    LedgerEffect,
    Occasion,
    PrefixReader,
    ReasonRecord,
    Response,
    changed_fields,
    derived_ledger_effect,
)

ADMITTED = "admitted"
REJECTED = "rejected"
UNRESOLVED = "unresolved"


@dataclass(frozen=True)
class LawfulEditCertificate:
    """What an edit offers in support of itself.

    There is no field for charge, saving, or advantage, and adding one would not
    help: the checker cannot read the charge table.
    """

    edit_id: str
    occasion_id: str
    at_date: int
    replaced: Response
    replacement: Response
    grounds: tuple[str, ...]
    authority: str


@dataclass(frozen=True)
class CertificateVerdict:
    status: str
    code: str = ""
    detail: str = ""
    cited: tuple[str, ...] = ()
    read: tuple[str, ...] = ()

    @property
    def admitted(self) -> bool:
        return self.status == ADMITTED


# ---------------------------------------------------------------------------
# The parametric residue
# ---------------------------------------------------------------------------

BearsOn = Callable[[ReasonRecord, str, Occasion], bool]
MagnitudeOK = Callable[[Sequence[ReasonRecord], Response, Response], str]
AddressOK = Callable[[Sequence[ReasonRecord], Response, Response, Occasion], bool]
AuthorityOK = Callable[[str, Sequence[ReasonRecord], Occasion], bool]
ReasonCompatible = Callable[[Sequence[ReasonRecord]], bool]


def bears_on_by_subject(reason: ReasonRecord, coordinate: str,
                        occasion: Occasion) -> bool:
    """The supplied default: a ground bears on a coordinate of an occasion when
    it names that occasion or its target and declares the coordinate.

    Weak on purpose. A stronger relation is a normative commitment and belongs to
    whoever is willing to make it.
    """
    if coordinate not in reason.licenses:
        return False
    return reason.subject in (occasion.occasion_id, occasion.target)


def magnitude_by_impediment(grounds: Sequence[ReasonRecord], old: Response,
                            new: Response) -> str:
    """The supplied default for the one magnitude coordinate this substrate has.

    Cited impediments each declare how many dates they account for. Their sum is
    what licenses a tolling endpoint; a proposal beyond it has directional
    support and no endpoint support, and is `UNRESOLVED` rather than `REJECTED`
    because whether directional support ever licenses an unbacked endpoint is
    exactly the question this predicate is a placeholder for.
    """
    if new.tolled == old.tolled:
        return ADMITTED
    if new.tolled < old.tolled:
        return ADMITTED
    allowance = sum(int(r.payload.get("dates", 0)) for r in grounds
                    if r.kind == KIND_IMPEDIMENT)
    if new.tolled - old.tolled <= allowance:
        return ADMITTED
    return UNRESOLVED


def address_by_basis(grounds: Sequence[ReasonRecord], old: Response,
                     new: Response, occasion: Occasion) -> bool:
    """A merits replacement must cite an interval that clears the threshold in
    the direction it claims.

    This is where reason connection stops being generic and says something about
    this response family: a merits ruling is licensed by an available interval
    separating the bound threshold, and by nothing else (`CD-J2`).
    """
    if new.basis != BASIS_MERITS:
        return True
    threshold = Q(occasion.schedule.threshold)
    for reason in grounds:
        if reason.kind != KIND_INTERVAL or reason.subject != occasion.target:
            continue
        lower = Q(reason.payload.get("lower", 0))
        upper = Q(reason.payload.get("upper", 1))
        if lower > upper:
            continue
        if lower >= threshold and new.verdict == occasion.schedule.positive_verdict:
            return True
        if upper < threshold and new.verdict == occasion.schedule.negative_verdict:
            return True
    return False


def authority_declared(authority: str, grounds: Sequence[ReasonRecord],
                       occasion: Occasion) -> bool:
    """An edit needs a named authorization, and a cited authority ground must
    cover the occasion. Absent any authority ground the check is the presence of
    the name, which is the weakest form that is not vacuous."""
    if not authority:
        return False
    covering = [r for r in grounds if r.kind == "authority"]
    if not covering:
        return True
    return any(occasion.occasion_id in tuple(r.payload.get("scope", ()))
               or r.subject == occasion.target for r in covering)


def reasons_compatible(grounds: Sequence[ReasonRecord]) -> bool:
    """The supplied default rules out citing a ground together with a ground
    that declares it incompatible. Nothing subtler is claimed."""
    identifiers = {r.reason_id for r in grounds}
    for reason in grounds:
        conflicting = set(tuple(reason.payload.get("incompatible_with", ())))
        if conflicting & identifiers:
            return False
    return True


@dataclass(frozen=True)
class PolicySuite:
    """The normative parameters, gathered so a reader can see all of them at once.

    Every field is a relation this round declines to settle. Replacing one is how
    a later round makes a normative commitment, and the commitment is then
    visible as a diff to a named function rather than as a changed sentence.
    """

    bears_on: BearsOn = bears_on_by_subject
    magnitude_ok: MagnitudeOK = magnitude_by_impediment
    address_ok: AddressOK = address_by_basis
    authority_ok: AuthorityOK = authority_declared
    reason_compatible: ReasonCompatible = reasons_compatible
    name: str = "v1-defaults"


DEFAULT_POLICY = PolicySuite()


# ---------------------------------------------------------------------------
# Burden discipline
# ---------------------------------------------------------------------------


def burden_obstruction(effect: LedgerEffect, occasion: Occasion, basis: str,
                       inherited: Sequence[str]) -> str:
    """Whether a ledger effect launders rather than discharges.

    Three things are refused: dropping an obligation outright; closing anything
    other than this occasion's own decision obligation; and closing that one
    under a kind the basis does not derive. Retargeting an inherited obligation
    is refused for the same reason as dropping it — the burden survives the
    rename, and a record that cannot show it is a record that lost it.
    """
    identifier = f"d:{occasion.occasion_id}"
    if effect.drops:
        return "burden.dropped"
    for target, _ in effect.retargets:
        if target in inherited or target != identifier:
            return "burden.retargeted"
    derived = dict(derived_ledger_effect(occasion, basis).closes)
    for target, kind in effect.closes:
        if target != identifier:
            return "burden.foreign_closure"
        if derived.get(target) != kind:
            return "burden.unlicensed_closure_kind"
    if set(derived) - {t for t, _ in effect.closes}:
        return "burden.closure_not_recorded"
    return ""


# ---------------------------------------------------------------------------
# The check
# ---------------------------------------------------------------------------


def check(certificate: LawfulEditCertificate, reader: PrefixReader, *,
          policy: PolicySuite = DEFAULT_POLICY) -> CertificateVerdict:
    """Decide a proposed edit against the prefix the reader exposes.

    Order matters only for which obstruction a reader is told about first; every
    check below is independent, and the caller gets the first that fires.
    """
    if tuple(reader.footprint) != tuple(CERTIFIER_FOOTPRINT):
        return CertificateVerdict(REJECTED, "interface.footprint_not_declared",
                                  "the certifier ran under another declaration")
    if reader.date != certificate.at_date:
        return CertificateVerdict(REJECTED, "interface.prefix_date_mismatch",
                                  "the reader is not at the edit's date")

    occasion = reader.occasion(certificate.occasion_id)
    if occasion is None:
        return CertificateVerdict(REJECTED, "interface.occasion_not_in_prefix",
                                  "the occasion is not on the record at this date")
    if not certificate.replacement.well_formed():
        return CertificateVerdict(REJECTED, "edit.malformed_replacement",
                                  "the replacement is not a well-formed response")
    if certificate.replacement == certificate.replaced:
        return CertificateVerdict(REJECTED, "edit.null",
                                  "the replacement is the actual response")
    if not certificate.grounds:
        return CertificateVerdict(REJECTED, "edit.no_grounds",
                                  "an edit cites at least one ground")

    # A. Historical availability. A ground filed after the prefix is invisible to
    # the reader, so importing a later fact is not something the check has to
    # remember to refuse — there is nothing there to cite.
    cited: list[ReasonRecord] = []
    for reason_id in certificate.grounds:
        record = reader.reason(reason_id)
        if record is None:
            return CertificateVerdict(
                REJECTED, "certificate.not_historically_available",
                f"ground {reason_id!r} is not on the record at date "
                f"{certificate.at_date}", certificate.grounds, tuple(reader.log))
        cited.append(record)

    # G. Successor ratification. Availability already refuses the ordinary case,
    # in which the endorsement is filed later. This refuses the residue: an
    # endorsement present in the prefix is still an endorsement, and an
    # endorsement is not a ground.
    for record in cited:
        if record.kind == KIND_RATIFICATION:
            return CertificateVerdict(
                REJECTED, "certificate.successor_ratification",
                f"ground {record.reason_id!r} endorses a disposition rather than "
                "licensing one", certificate.grounds, tuple(reader.log))

    # C. Defeater discipline.
    for record in cited:
        if not record.live_at(certificate.at_date):
            return CertificateVerdict(
                REJECTED, "certificate.defeated_ground",
                f"ground {record.reason_id!r} is not live at date "
                f"{certificate.at_date}", certificate.grounds, tuple(reader.log))

    if not policy.reason_compatible(cited):
        return CertificateVerdict(REJECTED, "certificate.incompatible_grounds",
                                  "the cited grounds are declared incompatible",
                                  certificate.grounds, tuple(reader.log))

    moved = changed_fields(certificate.replaced, certificate.replacement)
    if not moved:
        return CertificateVerdict(REJECTED, "edit.null", "nothing moves",
                                  certificate.grounds, tuple(reader.log))

    # D. Scope discipline, and B. reason connection, coordinate by coordinate.
    licensed: set[str] = set()
    for record in cited:
        licensed.update(record.licenses)
    # `ledger` follows from `basis`, and so does `verdict` when the basis moves;
    # neither carries a licence of its own. A verdict changed at a fixed basis is
    # a substantive move and is checked as one.
    substantive = set(moved) - {"ledger"}
    if "basis" in substantive:
        substantive.discard("verdict")
    outside = substantive - licensed
    if outside:
        return CertificateVerdict(
            REJECTED, "edit.out_of_scope",
            f"no cited ground licenses {sorted(outside)}",
            certificate.grounds, tuple(reader.log))
    for coordinate in sorted(substantive):
        if not any(policy.bears_on(record, coordinate, occasion)
                   for record in cited):
            return CertificateVerdict(
                REJECTED, "certificate.no_reason_connection",
                f"no cited ground bears on {coordinate!r} of this occasion",
                certificate.grounds, tuple(reader.log))

    if not policy.authority_ok(certificate.authority, cited, occasion):
        return CertificateVerdict(REJECTED, "certificate.authority",
                                  "the edit is not authorized for this occasion",
                                  certificate.grounds, tuple(reader.log))

    if not policy.address_ok(cited, certificate.replaced, certificate.replacement,
                             occasion):
        return CertificateVerdict(
            REJECTED, "certificate.replacement_unsupported",
            "the cited grounds do not support the replacement this edit proposes",
            certificate.grounds, tuple(reader.log))

    # E. Magnitude, which may decline to rule.
    magnitude = policy.magnitude_ok(cited, certificate.replaced,
                                    certificate.replacement)
    if magnitude == UNRESOLVED:
        return CertificateVerdict(
            UNRESOLVED, "certificate.magnitude_unresolved",
            "the cited grounds support the direction and not the endpoint",
            certificate.grounds, tuple(reader.log))
    if magnitude != ADMITTED:
        return CertificateVerdict(REJECTED, "certificate.magnitude",
                                  "the endpoint exceeds what the grounds allow",
                                  certificate.grounds, tuple(reader.log))

    # F. Burden and history preservation.
    inherited = tuple(o.obligation_id for o in reader.obligations()
                      if o.owner_occasion != occasion.occasion_id or o.lineage)
    obstruction = burden_obstruction(certificate.replacement.ledger, occasion,
                                     certificate.replacement.basis, inherited)
    if obstruction:
        return CertificateVerdict(REJECTED, obstruction,
                                  "the edit alters the burden record beyond the "
                                  "closure its own basis derives",
                                  certificate.grounds, tuple(reader.log))

    return CertificateVerdict(ADMITTED, "", "", certificate.grounds,
                              tuple(reader.log))
