# Boundary contract

Status: **handoff note; unregistered**. What the service layer consumes
and produces; enforced by `tests/test_composition.py` on the reference
model.

## Upstream must provide

- Liability occurrences `(id, accruedAt, specId, origin-data)`:
  identity-bearing, spec pinned at accrual, origin opaque. Occurrences
  from different generators (answerability-generated,
  decision-relevance-generated) must arrive as the same type; the
  fixture shows the service run is bitwise identical under origin
  swaps (`test_origins_indistinguishable_to_service`).
- The pinned specification table `specId -> (C_sigma, Check_sigma)`.
  Spec migration for an open occurrence is an upstream record act; the
  service layer has no operation for it.
- Append access to the shared transcript `L` (receipts are minted by
  interaction, never edited).

## Downstream receives

`ServiceOutcome(liability id, certificate, cited receipts)` — nothing
else. The assessment stub in the fixture consumes exactly this and
needs no `Gamma`, no scheduling internals, no capability assumptions.
Whether serviced evidence changes any stance, and what it bears on,
is downstream's question; a certificate asserts adequacy of the
investigation against its pinned spec, not any object-language claim.

## The service layer must never need

Stance contents; reason-ledger internals; authority structure; why an
occurrence accrued. The reference sources are scanned for this
vocabulary (`test_service_sources_do_not_touch_upstream_or_downstream`).

## Guarantees the layer gives the record

- Certificates are finite, cite receipts by index, and re-check
  against the transcript at any later time (L1, L2).
- Certified service events are historically stable under trace
  extension; later revision can trigger upstream review but cannot
  make the event unperformed (L2).
- Distinct occurrences are never coalesced by the layer, whatever
  their spec content; evidence sharing across occurrences is governed
  by the pinned specs, not by the layer (microcases 4, 5).
