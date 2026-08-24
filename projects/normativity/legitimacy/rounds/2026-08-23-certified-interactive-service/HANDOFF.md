# Boundary contract

Status: **handoff note; unregistered**. The full-stack contract around
the service layer; enforced by `tests/test_composition.py` on the
reference model.

```text
o : ObligationId, task(o) = Investigate(q, eta)
        |
        v
   InquiryRequest(o, eta)
        |
        v
 Certified Interactive Service
   reads Gamma and L; chooses actions; appends receipts to L
        |
        v
kappa : ServiceCertificate_eta          (cites ReceiptIds in L)
        |
        v
 record/account boundary:
   ValidCert(eta, L, kappa)  AND  MayClose(N, L, o, kappa, now)
        |
        v
 s : ServiceEvent in N                  (o accounted as serviced by kappa)
        |
        v
   Assess(S, s)
```

Slogans: CIS does not close obligations; it produces evidence of
adequate service. The certificate proves procedural adequacy; the
normative record decides what that certificate accounts for.

## Upstream must provide

- `InquiryRequest(obligation_id, spec_id)`: an identity-bearing
  obligation reference plus its pinned spec — nothing else. Origin,
  accrual grounds, authority provenance, and discharge rules are
  excluded by type (`test_origin_excluded_by_type`). Distinct
  equal-content obligations remain distinct via `obligation_id`.
- The pinned specification table `specId -> (C_sigma, Check_sigma)`.
  Spec migration for an open obligation is an upstream record act; the
  service layer has no operation for it.
- Append access to the shared transcript `L` (receipts are minted by
  interaction, never edited).

## CIS produces

A valid `ServiceCertificate` per serviceable request — or nothing.
That is the entire output type: no closure, no status, no
interpretation (`serve`, `test_cis_produces_certificates_not_closures`).
A certificate is returned even when every current discharge policy
would refuse it (`test_record_refuses_when_may_close_false`).

## The record decides discharge

`record_service` (stub): mints `ServiceEvent(o, kappa)` — the
historical fact that obligation `o` was accounted as serviced by
`kappa` — iff `ValidCert` holds for the pinned spec AND the discharge
policy `MayClose(N, L, o, kappa, now)` presently admits it. Refusal
leaves the certificate's validity and the obligation's openness
untouched (`test_same_certificate_accepted_or_refused_by_policy`).
Freshness/lapse windows are discharge policy, never spec content.

## Downstream receives

Assessment consumes the RECORDED `ServiceEvent`, not a raw controller
claim (`test_assessment_requires_recorded_event`), and needs no
`Gamma`, no scheduling internals, no capability assumptions. Whether
serviced evidence changes any stance, and what it bears on, is
downstream's question — a recorded service with `NoBearing` assessment
is coherent (`test_valid_service_with_no_bearing`).

Provenance split, tested as the canonical fixture
(`TestThreeProvenance`): reason occurrences cite RECEIPTS (and
contents) as evidential grounds; the CERTIFICATE is consumed by the
record's ServiceEvent as procedural adequacy; the event itself is the
accounting license. A reason never cites the certificate; claims like
"the experiment followed protocol P" are ordinary contents supported
by receipts, so the frozen `V ⊔ L` source sorts suffice.

## The service layer must never need

Stance contents; reason-ledger internals; authority structure;
discharge policy; why an obligation accrued. The service core is
scanned at the AST level for record-side and downstream identifiers
(`test_service_core_blind_to_record_and_downstream`).

## Guarantees the layer gives the record

- Certificates are finite, cite receipts by stable identity (indices
  in the reference model), and re-check against the transcript at any
  later time.
- Valid certificates remain valid records of their historical service
  events under every trace extension; later revision can trigger
  upstream review but cannot make the event unperformed
  (`test_contradictory_receipt_yields_review_not_invalidation`).
- Distinct obligation references are never coalesced by the layer;
  evidence sharing across obligations is governed by the pinned specs
  and the record's account rules, not by the layer
  (`test_shared_evidence_two_obligations_two_events`).
