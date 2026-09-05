# Theorem and countermodel ledger

All names are provisional. Nothing in this round is registered.

| id | statement | evidence |
|---|---|---|
| NC-T1 | `CoverageActual W -> ClauseS -> ClauseR W -> ClauseP -> RobustOpen` | lean-proved: `Scenario.robustOpen_of_cert` |
| NC-T2 | replace `ClauseR` in NC-T1 by `ClauseRPlus` | lean-proved: `Scenario.robustOpen_of_certPlus` |
| NC-T3 | `ClauseRa ∧ ClauseRb ∧ ClauseRc -> ClauseR` | lean-proved: `Scenario.clauseR_of_components` |
| NC-T4 | `ClauseR ->` all three components when every route in `W` is actually adequate | lean-proved: `Scenario.components_of_clauseR` |
| NC-W0 | all NC-T1 hypotheses are inhabited and one counterfactual is live with an adequate route | lean-proved: `Witness.nonvacuity`; exact-witness: `F0` |
| NC-X-S1 | activation defeats Robust Openness when `(S)` is dropped | lean-proved: `Witness.attackS_activate`; exact-witness: `A_S_ACTIVATE` |
| NC-X-S2 | de-representation defeats Robust Openness when `(S)` is dropped | lean-proved: `Witness.attackS_derepresent`; exact-witness: `A_S_DEREPRESENT` |
| NC-X-Ra | loss of admissibility defeats Robust Openness | lean-proved: `Witness.attackRa`; exact-witness: `A_RA` |
| NC-X-Rb | loss of target exposure defeats Robust Openness | lean-proved: `Witness.attackRb`; exact-witness: `A_RB` |
| NC-X-Rc | loss of registration defeats Robust Openness | lean-proved: `Witness.attackRc`; exact-witness: `A_RC` |
| NC-X-P | loss of principal standing defeats Robust Openness while counterfactual Coverage holds | lean-proved: `Witness.attackP`; exact-witness: `A_P` |
| NC-X-OFF | route persistence does not imply component preservation off the actually adequate set | lean-proved: `Witness.offAdequate` |
| NC-X-ID | re-anchoring a destroyed target to a constant creates false efficacy | exact-witness: `REANCHOR`, `DESTROY_ANCHORED` |
| NC-X-REL | internal recognition makes forgetting the concern vacuously open | exact-witness: `FORGET` |
| NC-X-SET | settlement timing can vary without changing Robust Openness | exact-witness: `SETTLEMENT` |
| NC-X-EVAL | evaluator fidelity can fail while Robust Openness holds | exact-witness: `EVALUATOR` |
| NC-X-EXT | varying the exterior can blame a null intervention or excuse destruction | exact-witness: `EXTERIOR_VARIED_NULL`, `EXTERIOR_VARIED_DESTROY` |

The Python runner recomputes all tables with exact values. Its finite fixtures are not
proofs of general statements. The Lean module is sorry-free and prints axioms for every
theorem; the expected output is `[]` or a subset of the repository allowance.

## Paper-derived and proposed items

- The interpretation of `(S)` and `(R+)` as the exact external bill is a proposed
  interface, supported by NC-T2 and the attacks.
- The three-semantics comparison is paper-derived from the cited landed round artifacts.
- Stable concern/target typing, applicability transport, agency-boundary authentication,
  and fixed exterior response policy are ambient assumptions.
- Whether a protected principal may be named in the canonical legitimacy interface is
  open.
- Construction of any accepted intervention semantics satisfying the certificate is
  open.
