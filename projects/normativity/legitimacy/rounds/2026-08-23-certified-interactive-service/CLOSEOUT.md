# Closeout: the surviving interface

Status: **research memo; unregistered**. The final types, stated
without narrative. All names remain provisional.

## Core CIS

```text
I = (A, Y, Gamma, Sigma)

Gamma : H x A -> P+(Y)        epistemically possible responses given
                              the public history; hidden state is
                              analytic, never public interface
sigma = (C_sigma, Check_sigma)
                              certificate type + citation-local judge

ValidCert(sigma, L, c)        Check accepts c over the receipts c
                              cites (indices in the reference model
                              represent stable ReceiptIds)
Certifiable(sigma, L)         := exists c, ValidCert(sigma, L, c)
```

Requests are external: `InquiryRequest(obligation_id, spec_id)` —
identity-bearing obligation reference plus pinned spec, and by type
nothing else. Certificate discovery (`ProverFinds`) is an algorithm,
not semantics. Costs and objectives are annotations on problems over
`I`.

## Upstream contract

The record supplies the request, the pinned spec table, and append
access to the transcript `L`. It keeps to itself: why the obligation
accrued, its origin, authority provenance, discharge rules, and every
stance- or reason-facing fact.

## Output contract

CIS produces at most one thing per request: a `ServiceCertificate`
citing receipts in `L`. It closes nothing, marks nothing, interprets
nothing.

## Accounting contract

The record decides discharge:

```text
RecordService(N, o, kappa) -> ServiceEvent
    iff ValidCert(sigma_o, L, kappa) AND MayClose(N, L, o, kappa, now)
```

`MayClose` may read the present (freshness windows live here) and can
refuse a certificate whose historical validity is untouched. The
`ServiceEvent` is the historical normative fact that `o` was
accounted as serviced by `kappa`.

    CIS does not close obligations.
    CIS produces evidence of adequate service.

    The service certificate proves procedural adequacy.
    The normative record decides what that certificate accounts for.

## Downstream contract

Assessment consumes the recorded `ServiceEvent` — never a raw
controller claim — reads the cited receipts, and mints reason
occurrences or returns no bearing. Service adequacy does not entail
epistemic bearing.

## Core theorem

Under citation-local checking and append-only, identity-stable
receipts:

```text
ValidCert(sigma, L, c)  =>  ValidCert(sigma, L ++ L', c)
Certifiable(sigma, L)   =>  Certifiable(sigma, L ++ L')
```

DERIVED, finite-tested. Consequences: absorbing acceptance in
monitors is the theorem in implementation form, and no
`MonotoneEvidence`-style capability exists — historical certifiability
is monotone for every spec.

## Capability story

The bare object proves nothing; each imported guarantee names its
capabilities (taxonomy in `INTERACTIVE_SERVICE_INTERFACE.md`, typed
by layer: spec family, environment presentation, objective
annotation, record-side discharge policy, upstream minting policy —
never the prover). Embeddings must additionally preserve the source
model's observation/action order (the tick convention), which is a
requirement on translations, not new core structure.

## Reason compatibility

`V ⊔ L` suffices for reason sources: evidential grounds are receipts
(and contents), procedural adequacy is the certificate consumed by
the ServiceEvent, accounting license is the event itself. On all
tested cases — no bearing, divergent applications, shared evidence,
protocol-compliance claims — no reason needs to cite a certificate,
so no new source sort is required.

## Verdict

**READY-TO-MERGE.** Discharge/account semantics sit at the record
layer; historical certification is unambiguous and theorem-backed;
the timing convention is explicit; the full-stack handoff and the
three-provenance fixture are executable; prior-art claims stand under
the final types; round suite and repository gates are green.
