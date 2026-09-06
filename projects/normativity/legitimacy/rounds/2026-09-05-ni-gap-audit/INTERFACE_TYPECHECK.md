# Composition input interfaces

These are proposed interfaces. They state only what the composition consumes.

## History / Integrity output

```text
O_P = {
  exposures : finite set of immutable obligation identities,
  live      : finite subset of exposures,
  spec      : obligation identity -> anchored specification,
  status    : obligation identity -> {live, answered, disposed(successor), settled(receipt)} -> Prop
}
```

Required certificate: every exposure has one fate; every live item is exposed; every exposure has a live descendant or a prior answer/settlement discharge; every disposal names a successor. The Lean adapter proves these structural clauses for `DefeatTrace`. Authentication of births, specifications, authority, lineage, and semantic carry remains the Integrity provider's contract.

Answerability type-checks as a consequence of Integrity only if Integrity includes lifecycle conservation and faithful carry. A weaker append-only/audit-log Integrity certificate does not imply it. The implication is therefore a proposed theorem between two separately stated predicates, not a definitional identification.

## Settlement output

```text
SettlementTrusted(H) := authenticated, append-only availability of receipts through the declared boundary
Closes(H, receipt, obligation) := internal judgment under the rules and reasons in force at H
Discharge(H, receipt, obligation) requires SettlementTrusted(H), receipt in SetView(H),
  Closes(H, receipt, obligation), and Integrity-authorized provenance.
```

`SettlementTrusted` does not output `Closes`. A later history may reject an earlier closure rationale by adding a reconsideration obligation; the append-only receipt is unchanged. This round does not define the reconsideration protocol.

## Robust Openness / Non-Capture output

```text
NonCaptureCertificate(scope, interventions, H) supplies:
  scoped coverage under each declared intervention,
  preservation of required standing/challenge access,
  preservation of corrective-channel efficacy,
  evaluator/settlement independence clauses named by the application.
```

The generic composition consumes `RobustOpenness H` opaquely. Counterfactual semantics, scope selection, and satisfiability are intentionally external.

## Compiler output

For each service occurrence: canonical coordinate identities, cited rational rows, a checked rational feasible point or a sound conflict certificate or `Unknown`, and—on success—an effective rational-polytope representation equal to the row region. `Conflict` and `Unknown` retain the original cited bundle; only a licensed upstream rule may create an adjudication obligation or discard a row.

Representability belongs to the obligation/schema pair. Compiler completeness is relative to the declared schema. Joint feasibility is nonempty intersection. No interior assumption is needed for projection.

## Practical-response and edge output

For every positive transport edge `(e,s)` against the one distribution realized at `s`:

```text
EdgeCertificate(e,s,Pi_s): loss(e,Pi_s) <= M(e,s) * d(s) + epsilon(e,s).
```

One sufficient witness has authenticated value ambiguity `zeta(e,s)`, optimizer error `eta(s)`, and response constant `L(e,s)`, giving

```text
M(e,s) = 2 * L(e,s)
epsilon(e,s) = L(e,s) * (2*zeta(e,s) + eta(s)) + epsilon_resp(e,s).
```

Joint price-space feasibility supplies none of this. A bundle is practically compatible exactly when every matched edge has this certificate against the same `Pi_s`; otherwise separate, adjudicate under a licensed rule, or leave mass residual.

## Final package

Lean's provisional `EndToEndHypotheses History E S` contains opaque predicates and inhabitants for Integrity, Robust Openness, settlement trust, export, compilation, and affordability, followed by the independently checkable LI and finite Progress hypotheses. `end_to_end` returns all six certificates unchanged, the ordinary LI conclusion, and the quadratic Progress bound. No semantic or causal premise is an axiom declaration.
