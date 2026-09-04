# Local theorem and witness ledger

These statements are local contribution results.  They do not by themselves prove the
conditional end-to-end theorem in the realization report.

| ID | Statement of record | Status | Test / necessity witness |
|---|---|---|---|
| NI-B1 | `Workspace.Normativity.Contrib.NormativeInductor.approximate_argmax_transfer` | Lean-proved | `test_approximate_argmax_value_bridge`; factor 2 is attained when the two calibration errors oppose |
| NI-B2 | `Workspace.Normativity.Contrib.NormativeInductor.practical_response_compose` | Lean-proved | algebraic composition; `L>=0` is necessary for monotonic multiplication |
| NI-B3 | `Workspace.Normativity.Contrib.NormativeInductor.affine_transport_compose` | Lean-proved | `test_affine_transport_composition_and_exact_carry` |
| NI-B4 | `Workspace.Normativity.Contrib.NormativeInductor.exact_carry_left` | Lean-proved | same test; realizes defeat/disposition `(1,0)` |
| NI-W1 | `src.realization.progress_certificate` | witness-checked finite instance, not a general proof | `test_contract_progress_algebra_with_shared_service` |
| NI-W2 | `src.realization.approximate_argmax_regret` | witness-checked finite instance | `test_approximate_argmax_value_bridge` |
| NI-C1 | independent individually feasible strict comparisons need not have feasible conjunction | counterexample, exact checker | `test_individually_feasible_reasons_can_conflict_jointly` |
| NI-C2 | zero operative belief defect does not bound action loss without a response certificate | counterexample, exact checker | `test_belief_only_does_not_entail_response` |

## What is not shown

- No finite witness certifies legitimacy, Coverage, settlement integrity, or semantic
  truth.
- No general joint compiler or scheduler is implemented here.
- No theorem says ordinary LI beliefs determine correct action values.
- No theorem upgrades the paper/test serviceability results to Lean.
- The contract's general sum inequality is instantiated by exact arithmetic but is not
  newly claimed as a Lean theorem.
