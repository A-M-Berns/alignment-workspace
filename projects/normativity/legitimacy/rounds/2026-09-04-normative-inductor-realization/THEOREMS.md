# Local theorem and witness ledger

These are local contribution results. They do not by themselves prove the conditional
end-to-end theorem in the realization report.

| ID | Statement of record | Status | Boundary / witness |
|---|---|---|---|
| NI-B1 | `approximate_argmax_transfer` | **Lean-proved** | deterministic uniform-calibration transfer; factor 2 is attained |
| NI-B2 | `randomized_approximate_argmax_transfer` | **Lean-proved** | finite policy alphabet; arbitrary probability weights and tie breaking |
| NI-B3 | `calibration_through_value_correspondence` | **Lean-proved** | composes quote-to-admissible and admissible-to-authenticated-value radii; does not establish the semantic premise |
| NI-B4 | `public_work_le_projection_work` | **Lean-proved** | transfers the existing Euclidean projection-work upper bound to any smaller nonnegative public defect, in particular sup-distance |
| NI-B5 | `normalized_euclidean_padding_changes` | **Lean-proved** | positive redundant padding strictly lowers old normalized squared defect and raises old declared service |
| NI-B6 | `practical_response_compose` | **Lean-proved** | algebraic decision-to-response composition; requires nonnegative multiplier |
| NI-B7 | `affine_transport_compose` | **Lean-proved** | affine semantic certificate composition |
| NI-B8 | `exact_carry_left` | **Lean-proved algebra only** | an already certified `(1,0)` edge is identity; does **not** prove defeat/disposition has that semantic certificate |
| NI-B9 | `old_service_implies_amplification` | **Lean-proved normalization bridge** | consumes aggregated old column-cap and parsimony hypotheses to prove the new `LK` column bound; does not re-prove the old service theorem |
| NI-W1 | `src.realization.progress_certificate` | **Witness-checked finite instance, not a general proof** | `test_contract_progress_algebra_with_shared_service` |
| NI-W2 | `src.realization.approximate_argmax_regret` | **Witness-checked finite instance** | deterministic value bridge including sharpness |
| NI-W3 | `src.realization.old_service_amplification` | **Witness-checked finite instance** | exact old-service-to-new-`Gamma` arithmetic |
| NI-C1 | independent individually feasible strict comparisons need not have feasible conjunction | **Counterexample, exact checker** | `test_individually_feasible_reasons_can_conflict_jointly` |
| NI-C2 | zero operative belief defect does not bound action loss without a response certificate | **Counterexample, exact checker** | `test_belief_only_does_not_entail_response` |
| NI-C3 | old `dist_2/sqrt(m), m lambda` public interface is padding invariant | **False; counterexample and Lean inequality** | `test_old_normalization_fails_padding_invariance_exactly` |
| NI-C4 | admissibility/projection certifies counterfactual values | **False; exact projection/value counterexample** | `test_projection_admissibility_is_not_value_truth` |
| NI-P1 | `dist_infinity, lambda` is invariant under enforcement-null product padding | **New paper proof plus exact checker** | `test_sup_defect_and_lambda_service_are_padding_invariant` |

All Lean declarations live in namespace
`Workspace.Normativity.Contrib.NormativeInductor`.

## What is not shown

- No finite witness certifies legitimacy, Coverage, settlement integrity, robust
  non-capture, counterfactual identification, or semantic truth.
- No general joint compiler or adversarial closed-loop scheduler is implemented here.
- No theorem says ordinary LI beliefs or projection admissibility determine correct
  action values.
- No theorem upgrades the paper/test serviceability results themselves to Lean.
- The contract's general Progress inequality is instantiated by exact arithmetic but is
  not newly claimed as a Lean theorem.
