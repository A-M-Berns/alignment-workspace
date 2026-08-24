You are performing the FINAL CLOSEOUT PASS on PR #51:

    “Certified interactive service: the waist survives revision”

Repository:
    A-M-Berns/alignment-workspace

Existing branch:
    round/2026-08-23-certified-interactive-service

Work on that branch only.

This is not a new research round. Do not reopen the core CIS research question unless the cleanup exposes an actual contradiction.

The current substantive verdict is:

    REQUIRES-REVISION — SURVIVES

The round has already established, provisionally but with substantial support, that:

1. Certified Interactive Service survives as a narrow interface rather than a contentful theory by itself.
2. The public service object is approximately:

       I = (A, Y, Gamma, Sigma)

   with:
   - Gamma an observable-history / epistemically-possible response relation;
   - hidden state external/analytic, not public interface structure;
   - liabilities supplied externally;
   - costs/objectives external annotations;
   - mathematical guarantees obtained from structural capability assumptions.

3. Historical certification has been cleaned up:

       ValidCert
       Certifiable
       MayClose
       ProverFinds

   are distinct.

   In particular:
   - `Certifiable` is extension-closed by theorem from citation-local checking and append-only receipts;
   - certificate discovery is not constitutive semantics;
   - freshness / lapse belongs to present discharge semantics rather than historical validity.

4. The online-timing issue has been repaired by requiring embeddings to preserve source observation/action order, using a tick/observation convention when necessary.

5. The service interface composes cleanly with the frozen reason representation:

       reason sources = V ⊔ L

   and ServiceCertificates are NOT epistemic reason sources.

6. The canonical provenance split is:

       evidential grounds
       != procedural service adequacy
       != normative/accounting license.

The purpose of this final pass is to integrate those findings with the now-clearer full-stack architecture and leave PR #51 semantically clean, internally consistent, and ready to merge.

DO NOT merge it yourself.

# 1. Main closeout correction: move discharge semantics out of CIS

The current cleanup correctly identifies `MayClose` / `Admit_sigma` as closure-policy semantics, but it still places:

    sigma = (C_sigma, Check_sigma, Admit_sigma)

inside `ServiceSpec`, and the reference `run_service` checks admissibility before emitting a `ServiceOutcome`.

This is now typed at the wrong layer.

The full architecture uses three persistent ledgers:

    L : ReceiptLedger
    R : ReasonLedger
    N : NormativeRecord

and the governing principle is:

    modules produce witnesses/proposals;
    ledgers own historical normative facts.

Therefore CIS should establish only:

    “there exists / here is a valid certificate that the pinned
     investigation standard was historically satisfied.”

Whether that certificate may PRESENTLY discharge an obligation is a normative-record/accounting question.

## Target factoring

Prefer something like:

    ServiceSpec sigma = (C_sigma, Check_sigma)

with:

    ValidCert(sigma, L, c)
    Certifiable(sigma, L) := exists c. ValidCert(sigma, L, c)

Then separately, upstream / record-side:

    MayClose(N, L, obligation, c, now)

or an equivalently clean typed discharge-policy interface.

Do not blindly use these exact names if a better minimal factoring falls out.

The important separation is:

    historical service validity
    !=
    present obligation discharge.

`Admit_sigma` should not remain constitutive CIS structure merely because
the earlier cleanup introduced it there.

If some admissibility rule genuinely belongs to a service standard rather
than normative accounting, identify a concrete counterexample. Otherwise
factor it out.

# 2. CIS should produce a certificate, not close a liability

The current fixture still effectively does:

    CIS -> ServiceOutcome(liability, certificate, cited receipts)

only after both validity and admissibility succeed.

Refactor the conceptual interface so that CIS owns:

    InquiryRequest -> ServiceCertificate

where the certificate cites immutable ReceiptIds in L.

Then an upstream record/account layer owns something like:

    RecordService(
        S,
        obligation,
        certificate
    )
    ->
        ServiceEventId

subject to:

    certificate is ValidCert for the pinned service spec
    AND
    record-side MayClose / discharge conditions hold.

The ServiceEvent is the historical normative fact:

    “this obligation was accounted as serviced by this certificate.”

Assessment should conceptually consume that recorded event, not a raw
claim by the service controller that the investigation is complete:

    Assess(S, ServiceEventId)
        -> AssessmentProposal

This does NOT require building the whole NormativeRecord implementation in
this PR.

A minimal isolated stub / handoff type is enough.

But the documentation and executable composition fixture should reflect
the correct ownership boundary.

# 3. Minimize what crosses into CIS

The current `Liability` contains fields such as:

    id
    accrued_at
    spec_id
    origin

and tests establish that origin does not matter to service.

Prefer making that fact true by typing rather than by convention.

Define the minimal service-facing request, e.g.:

    InquiryRequest(
        obligation_id,
        service_spec_id,
        [only genuinely service-relevant parameters]
    )

The CIS layer should not receive:

- why the obligation arose;
- answerability vs decision-relevance origin;
- normative authority provenance;
- stance state;
- reason-ledger contents;
- discharge rules.

If some field is needed operationally, justify it explicitly.

Keep the identity-bearing obligation reference: distinct equal-content
obligations must remain distinct.

# 4. Canonical full-stack boundary to leave behind

By the end of this pass, PR #51 should endorse approximately this contract:

    o : ObligationId
    task(o) = Investigate(q, eta)

              |
              v

       InquiryRequest(o, eta)

              |
              v

     Certified Interactive Service
       reads Gamma and L
       chooses actions A
       causes receipts to append to L

              |
              v

    kappa_S : ServiceCertificate_eta

              |
              v

       record/account boundary

    ValidCert(eta, L, kappa_S)
    MayClose(N, L, o, kappa_S, now)

              |
              v

      s : ServiceEventId in N

              |
              v

          Assess(S, s)

The key slogans should be explicit:

    CIS does not close obligations.
    CIS produces evidence of adequate service.

and:

    The service certificate proves procedural adequacy.
    The normative record decides what that certificate accounts for.

# 5. Preserve the certification theorem

Do NOT regress the important cleanup result.

Maintain:

    ValidCert(sigma, L, c)

as citation-local.

Maintain:

    Certifiable(sigma, L)
      := exists c. ValidCert(sigma, L, c)

and retain the theorem:

    Certifiable(sigma, L)
        =>
    Certifiable(sigma, L ++ L')

under immutable stable receipt identities.

Certificate discovery remains an algorithm:

    ProverFinds

not semantics.

If the code still uses receipt indices rather than abstract ReceiptIds,
that is acceptable for the finite reference implementation, but clearly
label it as an implementation representation of stable receipt identity.

# 6. Re-type the capability lattice

Audit the current capability table after moving discharge semantics out of CIS.

In particular:

- `LapseFree` should no longer appear as a property of a ServiceSpec if
  lapse is record-side discharge policy.
- Keep it only if useful, but type it explicitly as a property of
  `DischargePolicy` / account semantics.
- `CoalescingRequests` remains upstream minting-policy structure.
- `KnownPrior` remains environment/objective annotation.
- `MonotoneEvidence` remains deleted because historical certifiability is
  monotone by theorem.
- No capability should accidentally depend on the attached prover.

Do not proliferate new capabilities.

# 7. Recheck serviceability terminology

The current cleanup distinguishes:

    ever-certifiable
    forceable
    timely-closable
    eventually-closed
    bounded-latency

Preserve the distinction, but re-type it after discharge moves upstream.

Likely:

SERVICE/CIS SIDE:
    EverCertifiable
    ForceableCertifiability / Servable

RECORD/SCHEDULING/ACCOUNT SIDE:
    TimelyClosable
    EventuallyClosed
    DeadlineSatisfied

QUANTITATIVE ANNOTATIONS:
    bounded latency
    cost

Do not let `Servable` secretly mean “record will close the obligation.”

The finite reachability solver should continue to target historical
certifiability unless there is a compelling reason otherwise.

# 8. Preserve reason-waist composition exactly

The following should survive untouched:

    reason occurrence:
        e = (id, sources, target, applied_as)

    sources ⊆ V ⊔ L

A reason should not cite ServiceCertificate merely because the
investigation was procedurally adequate.

Keep / sharpen the canonical three-provenance fixture:

1. receipts in L are evidential grounds;
2. ServiceCertificate is procedural adequacy;
3. ServiceEvent/account event in N is accounting/normative license.

Canonical microhistory:

    obligation o
        ->
    CIS interaction
        ->
    receipts l1,l2 in L
        ->
    certificate kappa_S
        ->
    record accounts o using kappa_S
        ->
    ServiceEvent s in N
        ->
    assessment of s
        ->
    OccurrenceSpec citing l1,l2
        ->
    ReasonOccurrence in R

The ReasonOccurrence MUST NOT cite kappa_S merely as a procedural
certificate.

Keep the test showing:

    valid service + NoBearing

is coherent.

That case is especially important: service adequacy does not entail
epistemic bearing.

# 9. Terminology cleanup

The current files use several overlapping phrases:

    certified service
    service outcome
    closure
    service event
    certifiable
    admissible
    serviced
    closed

Make them globally consistent.

Suggested discipline:

- `ValidCert`: historical certificate validity.
- `Certifiable`: existential historical service predicate.
- `ServiceCertificate`: finite witness produced/discovered by CIS.
- `MayClose`: upstream current discharge predicate.
- `ServiceEvent`: record-side historical account that an obligation was
  discharged/serviced using a certificate.
- `Assessment`: downstream interpretation of the recorded serviced evidence.

Avoid saying “CIS closes the liability.”

Avoid using “certified” alone when it is ambiguous between certificate
validity and record-side closure.

# 10. Audit the prior-art claims only for fallout

Do not rerun the literature round.

Check only whether removing `Admit` from ServiceSpec changes any stated
embedding claim.

Expected:

- SCD: historical coverage certificate unchanged; deadlines/delay remain
  scheduling/objective/account annotations.
- SR/MLSC: unchanged.
- Adaptive Submodularity: unchanged.
- ISSC: unchanged.
- Request-Response: corresponds to eventual historical
  request-response/service, not record-side discharge policy.

If wording needs qualification, make minimal edits.

# 11. Update the executable reference model

Refactor only enough to make the architecture truthful.

Likely useful types/functions:

    ServiceSpec
    ServiceCertificate
    InquiryRequest

and minimal test-only or composition-layer stubs:

    Obligation
    DischargePolicy / may_close
    ServiceEvent

Do NOT build the full normative record system.

The service core should remain independently usable.

A good sign is that `service_core.py` knows nothing about:

    MayClose
    NormativeRecord
    ServiceEvent
    stance
    reason ledger
    authority.

The composition fixture may contain the minimal record-side stubs needed
to demonstrate the boundary.

# 12. Tests

Preserve all existing tests and add/update tests for:

1. CIS can return a valid certificate even when upstream MayClose is false.
2. A lapsed certificate remains ValidCert.
3. The record refuses to create a ServiceEvent when MayClose is false.
4. The same historical certificate may later be used or rejected according
   to the pinned/account discharge policy without changing ValidCert.
5. Assessment accepts ServiceEventId / recorded service, not raw CIS
   completion authority.
6. Service code cannot inspect origin / stance / reason ledger / authority /
   discharge policy.
7. Shared evidence can account for multiple obligations according to
   upstream account rules while preserving distinct obligation identities.
8. The three-provenance composition fixture remains green.
9. `Valid service -> NoBearing` remains green.
10. all previous prior-art, microcase, timing, RR, and serviceability tests
    remain green.

Run the round test suite and all repository-required governance tests.

Check GitHub Actions before closeout.

# 13. Administrative cleanup

The PR body currently contains stale test-count language from the first
pass alongside the newer cleanup count.

Update the PR body so that:

- the current test count is correct;
- the final closeout semantics are summarized;
- the validity/discharge factoring is reflected;
- no superseded name such as `ServiceOutcome` is advertised as canonical
  if the final interface replaces it;
- the verdict remains clearly stated.

Also update:

    README.md
    INTERACTIVE_SERVICE_INTERFACE.md
    HANDOFF.md
    CERTIFICATION_CLEANUP.md
    SERVICEABILITY.md
    OPEN_QUESTIONS.md
    REPORT.md

only as needed for consistency.

Do not create speculative new open questions merely because the round is
ending.

# 14. Final closeout document

Add a short final section/document that states the surviving interface
without historical narrative.

It should answer:

## Core CIS

What is the final minimal public object?

Expected rough form:

    I = (A, Y, Gamma, Sigma)

    sigma = (C_sigma, Check_sigma)

    Gamma : H x A -> P+(Y)

    Certifiable(sigma,L)
      := exists c. ValidCert(sigma,L,c)

with liabilities / requests external.

## Upstream contract

What must the normative record supply?

## Output contract

Exactly what can CIS produce?

## Accounting contract

Who decides whether a certificate discharges an obligation?

## Downstream contract

Exactly what does assessment consume?

## Core theorem

State certificate persistence / extension-closure cleanly.

## Capability story

Where does the nontrivial mathematics live?

## Reason compatibility

Why does V ⊔ L remain sufficient?

# 15. Required final verdict

The closeout should choose one:

    READY-TO-MERGE
    NEEDS-ANOTHER-PASS
    CIS-WAIST-FAILED

`READY-TO-MERGE` requires:

- discharge/account semantics factored to the correct layer;
- historical certification semantics unambiguous;
- online timing convention retained;
- full-stack handoff clean;
- reason-waist compatibility preserved;
- prior-art claims still supportable;
- test suite green;
- CI green;
- docs internally consistent.

If a genuine contradiction emerges, do not force READY-TO-MERGE.

# 16. Scope discipline

Do NOT:

- redesign reason representation;
- implement the full NormativeRecord;
- solve assessment theory;
- solve review-trigger theory;
- work on R -> O;
- work on regret/loss;
- build decision theory;
- modify traderization;
- start another round;
- merge PR #51.

This is a final factoring, consistency, and closeout pass.

# 17. Stop rule

Stop immediately once:

1. CIS owns only interaction + historical service certification;
2. the record owns discharge/accounting;
3. assessment consumes a recorded service event;
4. the three-provenance distinction is preserved;
5. all docs and tests agree on the types;
6. CI is green;
7. the PR body is current;
8. the final verdict is recorded.

At that point PR #51 has done its job.
