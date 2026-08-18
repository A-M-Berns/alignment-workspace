# What this round depends on, by path and by class

Read from the tree at this branch's base, `4b0e17d`, not from memory. Classes:
**Lean-proved** — a declaration the `lean` gate builds and audits;
**test-supported** — a Python check in a round runner;
**definition/interface** — a semantic object with no theorem attached;
**refuted** — a statement the repository records as false;
**conjectural** — believed on displayed evidence;
**merely proposed** — named, not built.

## Consumed as running code

| path | object | class | how used |
|---|---|---|---|
| `projects/normativity/legitimacy/rounds/2026-08-17-counterfactual-legitimacy/src/response.py` | `process_projection`, `alphabet_of` — the protected normative response function | definition/interface | imported; the selector is composed with it |
| same round, `src/noncapture.py` | clause 1, `non_capture` over a variation class | test-supported | imported; run on 27 of that round's scenarios |
| same round, `src/coverage.py` | the coverage clause | test-supported | imported; decides attack 18 |
| same round, `src/trust.py` | `grade_of`, `judgment_of`, `grade_of_outside` | test-supported | the selector **is** `judgment_of ∘ grade_of`; the outside-reading grade is the necessity witness |
| same round, `src/scenarios.py`, `src/fixture.py` | the paired-run model and its 27 scenarios | test-supported | every composition statement is quantified over them |
| `projects/normativity/legitimacy/rounds/2026-08-13-procedural-legitimacy/src/` | `Trajectory`, the four record-internal conditions, the target `L*` | test-supported | transitively required by the above |

## Consumed as statements, not run

| path | statement | class |
|---|---|---|
| `lean/Workspace/Deference/Contrib/DelegationBridge.lean:52` | `GradeTrust EX W η` | definition; **imported hypothesis**, and its own docstring says no settlement instantiation in the skeleton produces it |
| same, `:71` | `delegation_bridge` | Lean-proved |
| same, `:97` | `delegation_bridge_unconditional` — deficit at most `2B` on the disagreement region | Lean-proved |
| `lean/Workspace/Deference/Contrib/StaticViewFactorization.lean:24,33` | a value factoring through price and realization is constant on the fibre | Lean-proved |
| `lean/Workspace/Deference/Contrib/CartesianFrameBridge.lean:278` | `AgentInert`, and its invariance under biextensional equivalence | Lean-proved |
| same, `:362,376` | `pin_delegated_eq_pin_simulated`; `delegated_not_biextEquiv_simulated` | Lean-proved |
| same, `:506` | `simRead_not_homotopyEquiv_delegated` — a process executing the **negation** of the principal's disposition is homotopy equivalent to delegation | Lean-proved, and it is the negative result this round routes around |
| same, `:521,528,535,552,557` | `preserve`, `foreclose`, `transfer` and their separations | Lean-proved |
| `lean/Workspace/Deference/Contrib/ReachableCorrectiveControl.lean:641` | `principal_has_no_exclusive_effect` | Lean-proved, and it is a **refutation** of that file's own protection reading |
| `projects/deference/rounds/2026-08-12-reachable-corrective-control/REVIEW.md` | the two successor requirements | definition/interface; both treated here as specifications |
| `projects/deference/notes/FINITE_MODEL_SKELETON.md` §2, §3, §4, §4a, §8.5, §8.6 | the carriers, the execution layer, the declared holes | definition/interface |
| `prompts/2026-08-11-deference-channel/REPORT.md` §1.2, §1.3, §6, §9.1, §9.2 | Propositions 1, 5, 6, 7, 8; token responsiveness; the responsiveness squeeze; the report-coordinate patch | test-supported and argued; Proposition 8 is the fence this round respects |
| `projects/deference/notes/LI_NATIVE_DEFERENCE.md` §4, §5, §7 | naming a future quote as a present sentence; `lic_wub_ofComputation_unconditional` giving weighted **signed**-bias convergence | proved in the pinned dependency; the mismatch is §3 of `LI_PREDICTION_INTERFACE.md` |
| `PRIORITIES.md` item 21 | signed versus magnitude control of grade error, with a witness that signed error can be exactly zero while the recommendation is misidentified on half the credence | open, with the separating instance recorded |
| `projects/normativity/legitimacy/rounds/2026-08-13-relational-scorekeeping-bridge/src/corrigibility.py` | `capability_survives_every_advisor_policy`, `principal_exclusive_effects`, `has_normative_standing` | test-supported; that round's own verdict calls the protection "a favourable arrangement of a coordinate the round supplied" |
| same round, `TWO_ARC_INTERFACE.md` §6 | normative standing and effective causal access are independent in both directions | test-supported |

## Read and found orthogonal

| path | why |
|---|---|
| `projects/normativity/rounds/2026-08-16-traderized-enforcement/` on `origin/traderized-enforcement` at `5fc434d` | `INTEGRATION_MAP.md` §7 states the separation itself and derives it from `StaticViewFactorization`. Nothing is taken. |

## Named and not used

`FU[g]` (`FINITE_MODEL_SKELETON.md` §8.1) is a declared hole needing a
time-indexed family of `A`-valuations. This round builds the **substitution**
half of a fully updated competitor and says so at
`src/repair.py:fully_updated_substitution`; the hole is not filled.

`EffectiveAuthority` (`LEGITIMACY_INTERFACE.md` §8) is named there as a third
input the downstream architecture is allowed to need. This round's efficacy
clause is a candidate for it and is not proposed as one.
