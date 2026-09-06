# Interface type-check: Non-Capture and practical semantics

This review compares only the stated outputs of worker C and worker D with the inputs of `EndToEndHypotheses` and `progress_bound`.

## C — Non-Capture certificate

| Issue | Classification | Type-check result |
|---|---|---|
| `CoverageActual + ClauseS + ClauseRPlus + ClauseP -> RobustOpen` | sufficient | Instantiate the composition's opaque `RobustOpenness : History -> Prop` by `fun H => RobustOpen(P,sigma,J,I)` at the fixed history. C's `robustOpen_of_certPlus` supplies the required inhabitant. |
| Fixed concern identity, target, relevance/applicability meaning, intervention coupling, and protected carrier | sufficient | C states these as ambient typing assumptions on `I`. The composition does not need a stronger Boolean certificate clause. |
| Actual Coverage outside `NonCaptureCert` | sufficient | The constructor requires both `CoverageActual` and the three counterfactual clauses. The composition must not treat `NonCaptureCert` alone as `RobustOpen`; C states the dependency explicitly. |
| Protected-principal parameter | sufficient | It is a declared parameter. Whether canonical legitimacy may name one remains open, but no type is missing from the conditional theorem. |
| Settlement generation/timing and evaluator correctness | misplaced | C correctly excludes these from the minimal `RobustOpen` conclusion. Settlement trust belongs to the separate settlement field; evaluator fidelity belongs to Integrity or practical semantics. |
| Disposition authorization and faithful transfer | misplaced | C correctly leaves these to Integrity/Answerability. `ClauseP` consumes the resulting carrier rather than authorizing its creation. |

Verdict for C: **sufficient**. The exact output consumed is a proof of

```text
RobustOpen(P, sigma, J, I) at the same historyState and transported concern identities
```

derived from `CoverageActual`, `(S)`, `(R+)`, and `(P)`. No additional Non-Capture clause is required.

## D — practical-semantics certificate

| Issue | Classification | Type-check result |
|---|---|---|
| `PracticalCert(e,s,Pi_s;M_es,epsilon_es)` | sufficient | Its inequality has exactly the right-hand side consumed by a positive transport edge: `M(e,s) * d(s) + epsilon(e,s)`. |
| `JointPracticalAdequacy(s,E_s,Pi_s)` and `T(e,s)>0 -> Admissible(e,s,responseReceipt(s))` | sufficient | This is exactly the needed same-response-receipt support condition. It rules out separate existential responses per edge. |
| Identification of the theorem's `ell(e)` with D's `Lambda_es(Pi_s)` | missing | `progress_bound` assumes one horizon loss `ell : E -> Real` and needs `ell(e) <= M(e,s)d(s)+epsilon(e,s)` on every positive edge. D certifies an edge-indexed `Lambda_es(Pi_s)`. The certificate cannot instantiate `hedge` until the two are related. |
| Uniform bound used for residual mass | missing | `progress_bound` requires `0 <= ell(e) <= D`. D says boundedness belongs to the external bill but does not expose the proofs for the headline `ell(e)` that the finite theorem uses. |
| Receipt/anchor/provenance metadata | sufficient | D supplies the correct semantic indexing. The present Lean algebra erases this metadata after certificate checking; the realization layer should retain it in the independently audited edge certificate. |
| Uniform pre-response adapter theorem | misplaced | It is a plugin/realization audit obligation preventing post-selection. The finite Progress algebra consumes the resulting recorded edge certificates, not the adapter implementation. |
| Finite-menu decision procedures and adequate-set witnesses | misplaced | They are sufficient constructors/refutations for particular ecologies, not fields required by the public Progress theorem. |

Verdict for D: **missing one loss-interface output**. The smallest output to send back is

```text
For the headline loss ell : E -> Real and every supported edge (e,s):
  ell(e) <= Lambda_es(Pi_s),
and for every evaluated exposure e:
  0 <= ell(e) <= D.
```

Equality `ell(e) = Lambda_es(Pi_s)` is sufficient but stronger than needed. Combined with `PracticalCert`, the comparison gives the exact `hedge` premise. If the intended headline is instead an edge-weighted loss, the smallest repair is to restate the Progress theorem with that edge-indexed left-hand side; that is a change to the composition interface, not an expansion of D's semantic bill.

## Resulting composition boundary

C needs no returned amendment. D should expose the loss comparison and bound as part of the certificate's theorem-facing output, or the synthesis must change the Progress statistic to the edge-indexed quantity D already certifies. No compiler, scheduler, causal model, finite-menu calculus, or settlement-timing implementation belongs in either requested amendment.
