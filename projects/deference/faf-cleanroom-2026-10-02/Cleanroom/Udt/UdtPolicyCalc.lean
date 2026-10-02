import Cleanroom.Udt.UdtPolicyCalc.Defs
import Cleanroom.Udt.UdtPolicyCalc.LocalGlobal
import Cleanroom.Udt.UdtPolicyCalc.Determination
import Cleanroom.Udt.UdtPolicyCalc.Newcomb
import Cleanroom.Udt.UdtPolicyCalc.TransparentNewcomb
import Cleanroom.Udt.UdtPolicyCalc.Games
import Cleanroom.Udt.UdtPolicyCalc.Tree
import Cleanroom.Udt.UdtPolicyCalc.Simplification
import Cleanroom.Udt.UdtPolicyCalc.Update
import Cleanroom.Udt.UdtPolicyCalc.Toys
import Cleanroom.Udt.UdtPolicyCalc.SelfSealing

/-!
# `Cleanroom.Udt.UdtPolicyCalc`: the policy-modification calculus and the UDT separations

Root module of the `udt-policy-calc` work package (faf-cleanroom run, 2026-09-29/30).
Dependents (`udt-paper-tiling`, `udt-comm-trust`, `udt-influence-101`) import this one name.
Sources: `research/udt-representation-theorem/` (the `lean/UDT/*.lean` files, untrusted and not
over FAF; the notes named per declaration) and Diffractor's UDT1.01 Posts 1, 3 and 4.

* `Defs`: `Policy`, `Function.update` as modification, `IsOptimal`, `IsLocallyOptimal`,
  `IsLocalOptimum`, `IsArgmax`, `LocalGlobal`; `Separable`, `CrossSituationDependence`, `RTest`,
  `FSADependence`, `OrdSep`; `FinDist`, `mass`, `condExpJunk`, `condProbJunk`, `event`.
* `LocalGlobal`: T2 (`isLocalOptimum_of_isOptimal`, Kind T), T3 Coordinated Buttons, T4
  (separability: `separable_of_rtest`, `fsaDependence_iff_nonconstant`, the lookup-table identity
  `weighted_sum_sup'_eq_sup'_sum`, `Separable.isOptimal_of_isLocalOptimum`,
  `sup'_eq_sum_sup'_of_separable`), T5 (`Separable.ordSep`, `OrdSep.localGlobal`, the witnesses
  `U5a`, `U5b`).
* `Determination`: T6 `PolicyDetermined`, `derivedPolicyUtility`, `exists_policyUtility` (Hyps (c));
  T7 `policyDetermined_of_factors`.
* `Newcomb`: T8 opaque Newcomb, `cdt_udt_differ` with the policy utility derived;
  `edt_oneBoxes_opaque`.
* `TransparentNewcomb`: T9 (`V_*`, `isOptimal_oneTwo_iff`, `oneTwo_strictArgmax`), T10
  (`edt_ne_udt_transparent`, `separation_vanishes_of_null_event`,
  `edt_rule_oneBoxes_on_full_of_eps_zero`, `ctScore_eq`, `ctRule_oneBoxes_on_full_of_lt`,
  `ctRule_disagrees_with_udt11_on_empty`, `condProb_empty_given_full_one`).
* `Games`: `instanceGame` over FAF's `SafeParetoImprovements.Game`, `directGame`,
  `isNashEquilibrium_instanceGame_iff` (T12(b)).
* `Tree`: Post 1's setup (`Leaf`, `Node`, `Pol`, `Env`, `runLaw`, `V`), `runLaw_sum_one`,
  T12(c) `exists_env_of_policyUtility`, T12(d) `perverse_V`, T12(e) counts,
  `exists_nash_not_optimal_policySelection`.
* `Simplification`: T13 `rhs_argmax_ne_lhs_argmax` (refutation), `rhs_eq_lhs_of_concentrated`.
* `Update`: T14 `ActionEnv`, `score`, `score_eq_V`, `score_argmax_iff`, `pH_eq_of_agreesOff`.
* `Toys`: depth-two machinery, Counterfactual Mugging / Parfit / XOR Blackmail (udt-rep-2-020),
  T14's N+ witness `t14_witness` and the policy-dependent failure `cm_score_ne_V`.
* `SelfSealing`: T15 `uncorrected_eq`, `mean_correction_time`, `statDecay_stationary`,
  `perEpisodeValue`.
-/
