# Theorem and counterexample ledger

All Lean declarations are in `Workspace.Normativity.Contrib.NormativeInductorComposition` and audit to the allowed axioms only.

| ID | Declaration/result | Evidence | Content |
|---|---|---|---|
| NIC-L1 | `not_out_of_res`, `res_unique`, `out_or_res_of_born` | lean-proved | issue resolution is terminal and unique; every prior birth is live or resolved |
| NIC-L2 | `live_subset_exposures`, `exposures_mono` | lean-proved | historical exposure contains the live docket and is monotone |
| NIC-L3 | `status_total`, `fate_unique`, `carry` | lean-proved | every exposure has one structural fate and a live/discharged descendant |
| NIC-L4 | `export_sound`, `failure_conserves` | lean-proved | qualitative export and compiler-failure conservation |
| NIC-N1 | `carry_needs_successor` | exact witness/counterexample supported | the landed witness with a successor-free disposal fails carry |
| NIC-N2 | `carry_witness` | lean-proved | landed defeat trace inhabits carry |
| NIC-L5 | `checkCompiled_iff`, `region_nonempty_of_check` | lean-proved | exact rational witness checking implies nonempty joint region |
| NIC-L6 | `farkas_sound`, `conflict_sound`, `compile_sound` | lean-proved | sound rational-row conflict and three-way result interface |
| NIC-L7 | `CompiledSchedule.regionPred_of_rows`, `compiled_end_to_end` | lean-proved | represented rows instantiate effective projection/LI theorem |
| NIC-L8 | `Workload.liability_le`, `adapted`, `residual_zero`, `total_service_eq_total_claim` | lean-proved | cheapest-window finite schedule has its declared liability, is adapted, and fully transports mass |
| NIC-W1 | `sampleWorkload_affordable` | lean-proved | nonempty two-claim scheduler witness |
| NIC-L9 | `anchored_response_transport` | lean-proved | authenticated value and response premises produce `(M,epsilon)` |
| NIC-L10 | `chain_transport`, `chainCert_exact_carry` | lean-proved | finite affine semantic transport fold and exact-carry identity |
| NIC-L11 | `work_of_calibrated`, `work_ratio_le`, `mean_le_sqrt_mean_sq` | lean-proved | per-date work, aggregate uptake, and quadratic modulus |
| NIC-L12 | `progress_bound`, `progress_bound_quadratic` | lean-proved | finite shared-service three-term Progress bound and quadratic specialization |
| NIC-L13 | `EndToEndHypotheses.end_to_end` | lean-proved | named opaque contracts plus computable bounded-liability enforcer imply retained certificates, ordinary LI, and Progress |
| NIC-W2 | `progress_witness` | lean-proved | one-edge inhabitant of all finite Progress premises |
| NIC-X1 | `tests/run.py`: empty intersection | exact witness/counterexample supported | two individually feasible rows conflict jointly |
| NIC-X2 | `tests/run.py`: uncertified edge | exact witness/counterexample supported | zero defect permits positive loss without a response certificate |

## Proposed and ambient interfaces

- Full authenticated event-history export: proposed definition/interface.
- `Integrity -> DiachronicAnswerability`: proposed theorem, valid only for the full lifecycle/faithful-carry bill; open for weaker Integrity.
- Settlement integrity, robust non-capture, causal/value identification: ambient assumption.
- General convex representability, compiler completeness, online scheduling, semantic-certificate generation, and concrete joint response compatibility: open.

## Necessity limits

`carry_needs_successor` isolates `dispose_successor`. The finite tests isolate joint feasibility and practical-response authentication. Necessity of every algebraic sign, normalization, and bounded-liability premise was not re-audited; the imported theorem ledgers record their own witnesses.
