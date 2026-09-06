# Theorem ledger

Every declaration is sorry-free and audits to a subset of
`[propext, Classical.choice, Quot.sound]`. Nothing is registered by this round.

## `Workspace.Normativity.Contrib.LegitimateEvolution` (new)

| declaration | statement | class |
|---|---|---|
| `ObligationState` | `(boundary, account)` | definition |
| `Initial.state` | a first accounted state from authenticated initial exposure | definition |
| `Evolution` | chain of transitions, each target account the propagation of its source; intermediate states explicit | definition |
| `Evolution.trans` | composition at a shared state | lean-proved (def) |
| `Evolution.propagate_toSegment` | `ev.toSegment.propagate O₀.account = O₁.account` | lean-proved |
| `Evolution.ofSegment` | any segment and source account give an evolution to the propagated state | lean-proved (def) |
| `Evolution.AllStates.head/last/trans` | a state predicate on an evolution holds at both endpoints and composes | lean-proved |
| `Conservation` | exposure grows; receipts persist; denotation transported | definition |
| `Conservation.refl/trans/ofStep` | preorder; one transition conserves | lean-proved |
| `Evolution.conservation` | `Evolution O₀ O₁ → Conservation O₀ O₁` | lean-proved |
| `OpennessSemantics`, `OpenAt` | per-prefix, per-concern scenarios; `RobustOpenActual` for every concern | definition |
| `LegitimateSegment` | evolution with `OpenAt` at every state | definition |
| `LegitimateSegment.refl/trans` | reflexive at open states; composes | lean-proved (def) |
| `LegitimateSegment.answerable` | `Conservation ∧ OpenAt O₀ ∧ OpenAt O₁` | lean-proved |
| `Legitimate`, `Legitimate.trans` | endpoint relation; transitive | lean-proved |
| `Witness.composed` | two legitimate segments compose; fates `{answered}`, `{live}` | lean-proved; nonvacuity |
| `Witness.endpoint_only_insufficient` | endpoints open, middle state not, evolution not legitimate | lean-proved; exact counterexample |

## `Workspace.Normativity.Contrib.NonCaptureCertificate` (extended)

| declaration | statement | class |
|---|---|---|
| `Scenario.ActualOpen`, `RobustOpenActual` | actual branch; actual and every counterfactual | definition |
| `Scenario.actualOpen_of_coverage` | actual coverage in `W` and actual standing give `ActualOpen` | lean-proved |
| `Scenario.robustOpenActual_of_persistence` | the persistence bill plus actual standing gives `RobustOpenActual` | lean-proved |
| `Witness.counterfactual_open_not_actual` | `RobustOpen ∧ ¬ ActualOpen ∧ ¬ RobustOpenActual` | lean-proved; exact witness |

## `Workspace.Normativity.Contrib.OccurrenceIntegrity` (retyped)

`Evidence` → `Resolution`; `answer_sound` → `answer_resolves`; `closure_sound` →
`closure_resolves`; `LocalLaw` docstring corrected to unary-parent transformations.
Every theorem of the consolidation round is unchanged up to the rename.

## `Workspace.Normativity.Contrib.NormativeInductionInterface` (retyped)

`Evaluation (O : ObligationState S anchor) Service`; `residual_bounds`, `progress_bound`,
`conditional_normative_inductor`, `deductive_normative_inductor`, `Witness.uptake`,
`Witness.bound` re-proved at the new type, the witness at `LegitimateEvolution.Witness.state₁`.

## Verification

From `lean/`: `lake build` and `python3 ../tests/audit_axioms.py`. From the repository
root: `python3 tests/run.py`.
