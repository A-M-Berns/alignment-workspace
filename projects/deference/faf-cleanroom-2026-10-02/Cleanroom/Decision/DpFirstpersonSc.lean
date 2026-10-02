import Cleanroom.Decision.DpFirstpersonSc.Bridge
import Cleanroom.Decision.DpFirstpersonSc.Stamp
import Cleanroom.Decision.DpFirstpersonSc.Audit
import Cleanroom.Decision.DpFirstpersonSc.License
import Cleanroom.Decision.DpFirstpersonSc.Lift
import Cleanroom.Decision.DpFirstpersonSc.Grades
import Cleanroom.Decision.DpFirstpersonSc.Dogmatic
import Cleanroom.Decision.DpFirstpersonSc.Refinement
import Cleanroom.Decision.DpFirstpersonSc.Stages
import Cleanroom.Decision.DpFirstpersonSc.Dictionary
import Cleanroom.Decision.DpFirstpersonSc.WitnessesAudit
import Cleanroom.Decision.DpFirstpersonSc.WitnessesLift
import Cleanroom.Decision.DpFirstpersonSc.WitnessesLicense
import Cleanroom.Decision.DpFirstpersonSc.WitnessesNewcomb
import Cleanroom.Decision.DpFirstpersonSc.WitnessesDogmatic
import Cleanroom.Decision.DpFirstpersonSc.PredictorLabel
import Cleanroom.Decision.DpFirstpersonSc.WitnessesPredictor
import Cleanroom.Decision.DpFirstpersonSc.SlItems
import Cleanroom.Decision.DpFirstpersonSc.WitnessesAn3
import Cleanroom.Decision.DpFirstpersonSc.OccValue
import Cleanroom.Decision.DpFirstpersonSc.WitnessesPermissive
import Cleanroom.Decision.DpFirstpersonSc.ShadowFactor
import Cleanroom.Decision.DpFirstpersonSc.LimitGrade
import Cleanroom.Decision.DpFirstpersonSc.Realizable
import Cleanroom.Decision.DpFirstpersonSc.MaskedReferent
import Cleanroom.Decision.DpFirstpersonSc.WitnessesStage

/-!
# `dp-firstperson-sc`: the first-personal audit and the superconditioning bridge

Root module of the package `Cleanroom.Decision.DpFirstpersonSc` (area `decision`, level 5, no
dependents). Over `dp-faithful-udt` (and transitively `dp-core-tree`, `dp-calibration`,
`dp-local-opt`, `dp-fairness-reloc`, `dp-edt-udt-fair`) and `udt-supercondition`, imported file by
file; no definition of record of either library is restated. See `run/wp/dp-firstperson-sc/`.

**Definitions of record (decisions 1–5 of the mandate):**
* `Bridge`: the exact `ℚ → PMF` bridge `toPMF` (`mass_toPMF`, `toPMF_map`, `condOn_toPMF`), the run
  law as a `PMF` (`runPMF`).
* `Stamp`: the stamped problem `stamp U B` over `SW Ω acts U = Ω × ((d : ↥U) → Option (acts d))`
  with `lastDraw`, the occurrence event `occW` (`{pol_d ≠ ⊥}`; `mem_worldEv_stamp_occW`: it *is*
  `occ(d)`), the base-event reading `obsW`, and the mass transports.
* `Audit`: `auditRef`, `pushState`, **`AuditPassAt`** (D7′), T1(a) `audit_iff_perRunClausesAt` /
  `auditAll_iff_perRunSSC` (Proposition 1′), T1(b) `obsAudit_ref_agree_calibratedState`.
* `License`: T2(a) `audit_license_iff_nullDiff` / `audit_license_iff_bridge` (FP-22′),
  `License`/`CoversAS`/`VeridicalASAt`, T2(b) `auditBase_of_bridge`, T3 `OccExpressible`,
  `perRunClausesAt_iff_strictClausesAt_of_nullDiff`, `occState_P_eq_nuCondDistr_iff` (AN-3′).
* `Lift`: T4 `liftModelA`, `liftModelA_post_iff`, `lambdaCI`, `liftModelB_iff`,
  `perRunClause1_boundedDensity` (AN-2), `liftSameOntology` (AN-13).
* `Grades`: T5 `evAtom`, `audit_jeffreyOnA` (AN-6), `reachable_iff_ac` (grade (i)),
  `strictClausesAt_ac_priorState` (AN-7), `ocState_boundedDensity_iff` (grade (ii)).
* `Dogmatic`: T6 `Reachable`, `DogmaticEpistemology` (Definition 19), `dogmatic_downstream`,
  `dogmatic_epistemicallyCoherent`, `strictOC_imp_dogmatic`, `dogmatic_imp_strictOC`,
  `strictOC_iff_dogmatic`, `dogmatic_value_clause`, `dogmatic_calibratedRefinement`; T7
  `OccOnlyPosterior`, `occOnly_posteriors` (AN-9), `worldCI`, `an10_compatible_iff_ac` (AN-10).
* `Refinement`: T10 `obsAtom`, `OccUnionOfObsAtoms`, `density_const_iff_occ_union` (AN-15(b′)).
* `Stages`: T9 `stageCI`, `stagePrior`, `stage_boundedDensity`, `stage_no_compatible_model`,
  `stage_gap` (AN-22′ stage instance; AN-21).
* `Dictionary`: T11's T20 `value_ofFun_eq_value'`; T16(a) `FiniteDependence`,
  `not_realizable_of_not_finiteDependence`, `infiniteFamily_not_finiteDependence`.
* `Witnesses*`: `B₁` (T1, T4, T8), Told-You-So (T1(c), T5(b), T6), the coverage-failure tree
  (T2(b)), the radical-label tree (T10), TN-V1/V2 (T2(c), T5(e), T6(c)).
* `PredictorLabel` (continuation 1): T14 GR-D2 node classes (`LiveAt`/`RoutingAt`/`PredictorAt`,
  `Live`/`Routing`/`Predictor`, `live_iff_subtreeVeridical`, `RoutingFree`), `replacePred` (`B_θ`)
  with its leaf bijection, GR-2 `leafLaw/value/nu_replacePred_self` (every tree), GR-4
  `value_replacePred_sub_le` with `usePred`/`usePred_eq_expectation`; `WitnessesPredictor`: TN-V2
  classification, GR-2's `9427/4900` vs the shared-seed `269/140` (`tnV2_seed_failure`), the GR-4
  cell.
* `SlItems` (continuation 1): T17 `CEDT`/`CEDTSelfTransparent`, `cedt_selfTransparent_of_recordsFor`,
  the miniature's forcing referent and `miniature_cedt_iff` (`= {2/3}`); the pennies tree,
  `limitVal_of_factor`, `pennies_adviceEdt_iff` (the `2×2` best-reply tie), `mp_adviceEdt_iff`
  (`q = 1/2` for `p < 1`), `mp_value`, `mp_adviceEdt_of_p_one`.
* `WitnessesAn3` (continuation 1): T3(c), AN-3′'s trees (i)–(iii) in one shape (`anTree`): the
  instance-blind tree (`P` agrees, `V` differs, the `V`-criterion fails), (ii) non-expressible yet
  SSC = OC (Dead 1 confirmed), (iii) `ν = (¾, ¼)`, per-run `P = (½, ½)`, no `ν`-conditional
  (`three_no_nuCond`).
* `OccValue` (continuation 1): T3(b)'s `V`-clause criterion `occState_V_eq_calibratedState_iff`
  (under the `P`-clause, per-run `V` = strict `V` at the support iff `occPay{w}·ν{w} =
  paySum{w}·μ(occEv{w})` on the support).
* `WitnessesPermissive` (continuation 1): T7's "too permissive" mechanism `occOnly_compl_reaches`
  (if `occ(d)ᶜ = λ⁻¹O` with `ν(O) > 0`, the occurrence-only refinement at `d` reaches the strict
  state at `O`) and its TN-V1 package `tnV1_half_occOnly_package` (`occ(d_E)ᶜ = λ⁻¹O_F`); the
  Told-You-So cell `tys_occOnly_package` (`occ(d₁₀)ᶜ = λ⁻¹O₅`; continuation 2).
* `ShadowFactor` (continuation 2): the extension of record — the strict-grade verdict, the
  license and the per-run clauses are functionals of the **stamped** shadow
  (`priorState_agree_of_shadow_eq`, `audit_stamped_shadow_functional`,
  `license_stamped_shadow_functional`, `perRunClausesAt_stamped_shadow_functional`), not of the
  base shadow (`coverOk` vs `coverFail`: `license_not_base_shadow_functional`,
  `stamped_verdict_not_base_shadow_functional`); the limit grade through no strict shadow
  (`limitOC_not_shadow_functional`, `tys_occ_ten_eq`).
* `LimitGrade` (continuation 2): T13(a) — the limit-grade audit of record `LimitAuditPassAt`
  (Definition 10's algebraic limit on the occurrence evidence; tremble polynomials transported
  along the stamping, `leafLawPoly_relabel`, `nuPoly_stamp_eq_sum`), `limitAudit_iff_limitOCAt_of_occ_eq`
  (when `occ(d) = λ⁻¹O`), `limitAudit_P_iff_strict_of_pos` (nested with the strict grade at
  `μ(occ(d)) > 0`); the literal per-`ε` audit `AuditLimitOfEps` and its emptiness
  (`tys_take5_auditLimitOfEps_empty`); the null-observation separation
  (`tys_take5_limit_separation`) and `limitAudit_not_shadow_functional`.
* `Realizable` (continuation 2): T16(b) — the coordinate topology on `FinDistr` (scoped
  instance `finDistrTopology`), `continuous_leafLaw`, `continuous_value`, `continuous_mass`,
  `continuous_nu`, and over `ℚ` `value_continuous_rat`/`nu_continuous_rat` (Q11's continuity
  condition on tree-realizable functionals).
* `MaskedReferent` (continuation 2): T13(b) — on `seqStag` at `d₁` the local mask reproduces
  Theorem 2's evaluator (`seqStag_local_mask_V`: `(0, 1)`) and the global full-support mask
  misstates the continuation (`seqStag_global_mask_V`: `(1, ½)`); the local mask stays undefined
  at `d_{2S}` (`seqStag_local_mask_d2S_undefined`) while the global one audits it
  (`seqStag_global_mask_d2S_pos`); one instance, the generalization left UNREVIEWED (F20).
* `WitnessesStage` (repair round 1): AN-25 on a tree — the stage problem as `stageTree p`
  (trivial root query, digit coin, fair coin), its prior state `stagePriorQ p`
  (`stageTree_priorState_P`), and the pulled-back post-computation state `(½, ½, 0, 0)`
  failing per-run clause 1 at `X₇` and the audit at `d` for `p < 1`
  (`stagePostState_not_perRunClause1`, `stagePostState_fails_audit`).
-/
