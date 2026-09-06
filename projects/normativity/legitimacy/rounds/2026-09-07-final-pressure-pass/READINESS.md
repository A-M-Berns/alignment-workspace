# Final readiness: the legitimacy / normative-induction spine

Supersedes the object graph and theorem spine of the mathematical-consolidation round's
`CONSOLIDATION.md` where they differ; its external bill, research frontier and
migration map stand except as amended in §§4–6 below. All names are provisional.

## 1. What the pressure pass changed

| pressure point | finding | repair |
|---|---|---|
| endpoint state | `Segment A B` relates boundaries; a consumer needs the account, and an intermediate state is not `Initial` | `ObligationState = (boundary, account)`; `Evolution O₀ O₁` with every intermediate state explicit and each target account equal to the propagation of its source; `Initial.state` is one constructor of a first state |
| endpoint-only openness | open at `m`, live concern with no route at `m+1`, restored at `n`: endpoint-only accepts it | openness at every state of the evolution (`AllStates`); exact counterexample `Witness.endpoint_only_insufficient` |
| null intervention | `Scenario.RobustOpen` quantifies over `J` only; the actual prefix was never formally included | `RobustOpenActual := ActualOpen ∧ RobustOpen`, `J` indexes proper interventions; `Witness.counterfactual_open_not_actual` shows the gap was real |
| answer versus closure | `Evidence r` was answer evidence and a closure receipt produced it, so a valid closure typed as an answer | renamed to `Resolution r`, "legitimately accounted for"; `answer_resolves`, `closure_resolves`; fates stay distinct |
| merge | `LocalLaw` is unary in the parent; a genuine `(r₁, r₂) ↦ c` needs a joint no-growth map that unary laws cannot state | claim corrected to carry / split / refinement / re-representation; aggregation is a deferred extension |
| NI typing | `Evaluation` took a boundary and an anchor | `Evaluation (O : ObligationState S anchor)`; the theorems read `O.boundary.exposed` and `anchor` only |

## 2. Final canonical object graph

```text
Protocol S, anchor                        OpennessSemantics sem          (external)
        |                                          |
        v                                          |
ObligationState S anchor   O = (boundary, account) |
        |                                          |
        v                                          v
Evolution O₀ O₁  ──conservation──▶ Conservation O₀ O₁
        |                                          |
        +──── AllStates (OpenAt sem) ◀─────────────+
        |
        v
LegitimateSegment sem O₀ O₁       (certificate; Legitimate = Nonempty)
        |
        v  project (boundary.exposed, anchor)
Evaluation O Service  ── PracticalUptake ──▶ progress bound
        |
        v
conditional / deductive Normative Inductor
```

## 3. Theorem spine

| declaration | type | hypotheses | conclusion | evidence |
|---|---|---|---|---|
| `Evolution.trans` | `Evolution O₀ O₁ → Evolution O₁ O₂ → Evolution O₀ O₂` | shared middle state | composite certificate | Lean (def) |
| `Evolution.propagate_toSegment` | theorem | `ev : Evolution O₀ O₁` | `ev.toSegment.propagate O₀.account = O₁.account` | Lean |
| `Evolution.ofSegment` | def | segment, any source account | evolution to the propagated state | Lean |
| `Conservation` | Prop on states | — | exposure grows; receipts persist; denotation transported | definition |
| `Evolution.conservation` | theorem | `Evolution O₀ O₁` | `Conservation O₀ O₁` | Lean |
| `Conservation.trans`, `.refl` | theorem | — | preorder | Lean |
| `AllStates.trans/.head/.last` | theorem | state predicate on both parts | on the composite; at both endpoints | Lean |
| `LegitimateSegment` | structure | evolution + `AllStates (OpenAt sem)` | — | definition |
| `LegitimateSegment.trans`, `.refl` | def | shared state; openness at `O` | composite; identity | Lean |
| `LegitimateSegment.answerable` | theorem | legitimate segment | `Conservation ∧ OpenAt sem O₀ ∧ OpenAt sem O₁` | Lean |
| `Legitimate.trans` | theorem | `Nonempty` witnesses | transitive endpoint relation | Lean |
| `Scenario.RobustOpenActual` | Prop | — | actual branch and every counterfactual | definition |
| `Scenario.robustOpenActual_of_persistence` | theorem | actual coverage in `W`, actual standing, `(S)`, `(Ra)`, `(Rb)`, `(Rc)`, `(P)` | `RobustOpenActual` | Lean |
| `Scenario.certPlus_iff_robustOpen` | theorem | actual coverage | `(S ∧ R+ ∧ P) ↔ RobustOpen` | Lean (prior round) |
| `Witness.endpoint_only_insufficient` | witness | — | endpoints open, middle not, not legitimate | Lean, exact |
| `Witness.composed` | witness | — | two legitimate segments compose; fates `{answered}`, `{live}` | Lean, exact |
| `Witness.counterfactual_open_not_actual` | witness | — | `RobustOpen ∧ ¬ ActualOpen` | Lean, exact |
| `Evaluation.progress_bound` | theorem | `PracticalUptake` at the market | three-term bound on `O` | Lean |
| `Evaluation.conditional_normative_inductor` | theorem | bounded liability, computable market, `PracticalUptake` | LI ∧ bound | Lean; LI half unverified-nonvacuous |
| `Evaluation.deductive_normative_inductor` | theorem | registered effective end-to-end hypotheses, `DefectDominated`, edge certificates, amplification | LI ∧ bound | Lean |
| `OccurrenceIntegrity` results of the prior round | | | | unchanged up to the `Resolution` rename |

**Answerability Conservation, stated.** For accounted states `O₀`, `O₁`:
`O₀.exposed ⊆ O₁.exposed` (no occurrence disappears; occurrences are elements of a
`Finset`, so distinct ones stay distinct); for every `o` exposed at `O₀`, the terminal
receipts of its account at `O₀` are a sub-multiset of those at `O₁` (answer and
closure receipts immutable); and there is a transport of live-port resolutions from
`O₁` to `O₀` under which every account at `O₁` denotes what the account at `O₀`
denoted (live content faithfully transformed); anchoring is by the type
`Program S B (anchor o)`.

**Diachronic Answerability to `P`**, decomposed: `LegitimateSegment.answerable` gives
`Conservation` from Integrity and `OpenAt sem` — coverage of every live concern and
`P`'s standing on the carrier of every applicable one, on the actual branch and each
declared counterfactual — at every state, from Robust Openness.

**Legitimate Evolution** is reflexive at open states, composes at a shared state,
places no condition on `O₀` beyond openness at its own prefix (initial-state
neutrality), and its certificate lists every intermediate state (history sensitivity);
`Legitimate` hides the certificate for consumers.

## 4. External contracts

| contract | typed as |
|---|---|
| semantic authentication: `Resolution`, `answer_resolves`, `closure_resolves`, `Admitted`, `Live`, and each `LocalLaw`'s two maps | `Protocol`, `LocalLaw` |
| settlement: interface authenticity and source trust | `Protocol.SetView`; item truth never consumed |
| settlement: receipt immutability, internal `Closes`, authorization | stored fields of `ClosureReceipt`, conserved by `Conservation.receipts` |
| settlement: counterfactual anti-suppression | a route's adequacy in `sem`, when the application routes through settlement |
| Non-Capture: a certified `RobustOpenActual` at each prefix, under declared `Γ`, `J`, coupling, protected relation | `OpennessSemantics`; componentwise persistence is one sufficient way to produce it (`robustOpenActual_of_persistence`), strictly stronger than needed (`persistence_not_necessary`) |
| how concerns `Γ` relate to the docket's ports | part of `OpennessSemantics`'s type |
| practical semantics: `PracticalCert(e, s, Π_s)` against the one realized response | `Evaluation.PracticalUptake.practical` |
| evaluation protocol: `μ`, `T` committed before responses, `D` | `Evaluation` |
| computability of the augmented market (general assessment); admissibility of compiled rows by plausible worlds (deductive) | hypotheses of the two NI theorems |

None of these is an unfinished theorem of the generic theory.

## 5. Research problems

Unchanged from the consolidation round's §9: convex representability and compiler
completeness (item 79); affordable service on adaptive dockets (item 80); quantitative
semantic-transport constants (item 76); a jointly compatible practical-response
ecology (item 81); liveness under endogenous contest. One deferred extension, not a
research problem: aggregation laws with several parents (item 82).

## 6. Amendments to the migration map

- Legitimacy: `Leg_P = Segment × RobustOpen_P(H_n)` becomes `LegitimateSegment sem O₀ O₁`
  with openness at every state; the endpoint relation is `Legitimate`.
- Integrity: the public object is `ObligationState`; `Segment` is the certificate
  underlying `Evolution`; `Initial` is a constructor, not a premise.
- Openness: "persistence bill" is a sufficient plugin; the external contract is
  `RobustOpenActual` under a declared semantics. `(P)` is read on the actual branch by
  definition, not by convention on `J`.
- Diachronic Answerability: `Conservation` plus `OpenAt` at every state.
- Glossary: "evidence" → "resolution witness"; "merge" → "carry / split / refinement /
  re-representation", aggregation deferred.

## 7. Verdict

**READY FOR FULL CANONICALIZATION.** The endpoint state, the trajectory relation,
openness over time, the settlement/closure semantics and the NI handoff each have a
stable type, every generic theorem is Lean-proved with a nonvacuity witness, and the
external contracts are typed inputs. Subsequent work is realization (items 79–81),
instantiation of a `Protocol` and an `OpennessSemantics`, or downstream
deference/corrigibility research consuming `Legitimate` or `LegitimateSegment`.
