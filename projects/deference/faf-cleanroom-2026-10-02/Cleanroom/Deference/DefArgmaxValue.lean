import Cleanroom.Deference.DefArgmaxValue.Selector
import Cleanroom.Deference.DefArgmaxValue.AtomCode
import Cleanroom.Deference.DefArgmaxValue.CondStable
import Cleanroom.Deference.DefArgmaxValue.Calc
import Cleanroom.Deference.DefArgmaxValue.Pin
import Cleanroom.Deference.DefArgmaxValue.Witness
import Cleanroom.Deference.DefArgmaxValue.LiarProbe
import Cleanroom.Deference.DefArgmaxValue.Refuted
import Cleanroom.Deference.DefArgmaxValue.Punishing
import Cleanroom.Deference.DefArgmaxValue.Lemmas
import Cleanroom.Deference.DefArgmaxValue.Endorse
import Cleanroom.Deference.DefArgmaxValue.Concentration
import Cleanroom.Deference.DefArgmaxValue.Theorem
import Cleanroom.Deference.DefArgmaxValue.Instance
import Cleanroom.Deference.DefArgmaxValue.Averaged
import Cleanroom.Deference.DefArgmaxValue.Open
import Cleanroom.Deference.DefArgmaxValue.Hedged
import Cleanroom.Deference.DefArgmaxValue.Finite
import Cleanroom.Deference.DefArgmaxValue.Decisive
import Cleanroom.Deference.DefArgmaxValue.PunishingTie
import Cleanroom.Deference.DefArgmaxValue.Characterize
import Cleanroom.Deference.DefArgmaxValue.NotImplied
import Cleanroom.Deference.DefArgmaxValue.TruthTeller
import Cleanroom.Deference.DefArgmaxValue.WorldOnlyRefuted

/-!
# `def-argmax-value`: Argmax Value in the true-LI setting — the punishing menu and its scope conditions

Root module (package `def-argmax-value`, area `deference`, 2026-10-01). Mandate:
`run/wp/def-argmax-value/def-argmax-value-mandate.md`; report, findings, ledger and open list
beside it.

| file | target | headlines |
|---|---|---|
| `Selector` | 1, 3 (template) | `argmaxList`, `Menu.argmax_eq_iff`, `argmax_eq_argmaxList`, `selectorCode`, `selectorQuoteCode`, `selectorAtom_holds_iff` |
| `AtomCode` | infra | `quoteAtom_encode_primrec`, `quote_of_atom_computable` |
| `CondStable` | 4a–4b | `SelectionPackage`, `CondStableOn`, `CondStable`, `SelectionPackagesAvailable` |
| `Calc` | infra | `not_asympGE_of_tendsto_neg`, `expect_constLUV_asympEq`, `expect_deferred_const_mul`, `expect_deferred_const`, `deferred_neg_coherence` |
| `Pin` | 1b | `selfEstimate_eventually_lt_of_link`, `liarPrice_tendsto` |
| `Witness` | 4d | `argmaxBit`, `selI`, `selQ`, `selectionPackage_self`, `selectionPackagesAvailable_self` |
| `LiarProbe` | 1a–1b | `probeThreshold`, `liarSentence`, `liarSentence_holds_iff`, `probeMenu`, `probeMenu_argmax_iff`, `probeFollower`, `probeFollower_follows`, `liarPrice_tendsto_s`, `liarPresentPrice_tendsto_s`, `probePackage` |
| `Refuted` | 1c–1d, 2 | `probe_condStable_deficit_tendsto`, `condStableOn_probe_refuted`, `condStable_refuted`, `value_refuted`, `selfEndorseGE_instance_refuted`, `selfEndorsesGE_refuted`, `selfEndorses_refuted`, `exactF1_refuted`, `hardAbove_probe_tendsto`, `softTotalTrust_probe`, `mart_implies_value_refuted`, `all_epistemic_notions_hold_and_value_fails` |
| `Punishing` | 3 | `punishingMenu`, `punishAtom_holds_iff`, `punishingMenu_valuesAt`, `constZero_follows`, `punishing_sum_expect`, `punishing_value_refuted`, `punishing_maxQuote_ge`, `punishing_selfEndorsesGE_refuted`, `punishPackage`, `punishing_h3_deficit` |
| `Lemmas` | 5 | `perIndex_iff_sequence`, `sharp_iff_ramp`, `massWeighted_eq_denomFree_of_ne_zero`, `massWeighted_junk`, `cancellation_admitted`, the test-case sums |
| `Endorse` | 6 | `Concentrates`, `endorse_step1`, `endorse_step2`, `sum_estimate_I`, `massWeighted_asympGE_max`, `endorse_of_concentrates` |
| `Concentration` | 7 | `PairFold`, `ConcentrationFolds`, `concentrates_of_folds`, `pairRampWeight_pgenerable`, `concentrationFolds_self`, `concentrates_self` |
| `Theorem` | 8 | `Composite`, `value_of_selfEndorse_instance`, `scoped_value`, `ValueOnStable`, `valueOnStable_of_totalTrust`, `value_of_valueOnStable_of_condStable`, `scoped_value_paperExpert` |
| `Instance` | 4c N+, 8 N+, 8b self | `condStableOn_of_eventually_decisive`, `condStableOn_probe_self`, `probeComposite_zero/one`, `scoped_value_witness`, `valueOnStable_self` |
| `Averaged` | 11a | `averaged_value_probe_refuted`, `averaged_value_probe_refuted_bare` |
| `Open` | 12 (predicate of record), open problem 3 | `WorldOnly`, `worldOnly_atomMenu`, `truthPrice_frequently_interior` (OPEN; the former `condStableOn_of_worldOnly` and `selfOpaque_perIndex` are refuted in `WorldOnlyRefuted`) |
| `Hedged` | 9 | `blendWeight_pgenerable`, `blend_estimate`, `softSelfEndorse`, `softSelfEndorse_self`, `hedgedValue_of_totalTrust`, `rampBlend_eq_of_decisive`, `selfEndorseGE_instance_of_margin` |
| `Finite` | 10 (finite-exact) | `hedgedOneShot_mem`, `hardOneShot_eq_max`, `oneShot_claimA`, `hardChain_eq_runMax`, `hedgedChain_mem`, `oneShotHedge_value_iff`, `oneShotHard_value_iff`, `hardChainFrame_value`, `hedgedChainFrame_value`, `est_hedgedChainFrame_mem` |
| `Decisive` | 9d (2-018, novice level), 11b (OP17 margins case), repair r1 | `DecisiveData`, `value_instance_of_decisive`, `weightedAverage_asympGE`, `averaged_value_of_decisive`, `witnessMenu_decisive_margin`, `value_instance_of_eventually_constant`, `value_witness_of_eventually_constant`, `witness_value_one_without_hypotheses` |
| `PunishingTie` | 3b(iv) (repair r1, audit N1) | `punishing_quotes_tie`, `punishing_quote_tendsto`, `punishing_mass_tendsto`, `punishing_masses_interior` (proved), `punishing_h3_deficit_tendsto`, `condStableOn_punishing_refuted` |
| `Characterize` | repair r1 (audit fidelity 3); repair r2 (fidelity N4) | `condStableOn_of_selfEndorseGE_instance`, `condStableOn_iff_selfEndorseGE_instance`, `selfEndorseGE_instance_follower_indep`, `condStableOn_iff_selfEndorseGE_instance_self`, `condStableOn_iff_of_packages`, `condStableOn_iff_of_packages_self` |
| `NotImplied` | repair r1 (audit fidelity 4; 2-025); repair r2 | `probeComposite`, `probe_value_instance_refuted`, `h3_not_implied_by_rest`, `scoped_value_probe_of_h3`, `condStableOn_probe_refuted'`, `condStableOn_probe_refuted_any_package` |
| `TruthTeller` | repair r1 (audit B1: a second H3 witness); repair r2 (audit r2 B1: the dominance stratum; fidelity N1: the surplus) | `truthSentence`, `truthSentence_holds_iff`, `truthMenu`, `truthMenu_argmax_zero_iff`, `truthFollower_follows`, `truthFollower_estimate`, `truth_selfEndorseGE_instance`, `condStableOn_truth_self`, `truthComposite_zero/one`, `scoped_value_truth`; `truthFollower_dominates`, `value_of_dominates`, `truth_value_without_hypotheses`, `truth_selfEndorseGE_instance_by_domination`, `condStableOn_truth_any_package`, `truth_h3_surplus`, `truth_massVariance_estimate`, `truth_masses_interior_iff_price_interior` |
| `WorldOnlyRefuted` | repair r2 (audit r2 adversarial B2: both world-only OPENs refuted as stated) | `foAtomZ`, `foLiar`, `foLiar_holds_iff_truth`, `foLiar_holds_iff`, `foMenu`, `foMenu_worldOnly`, `foFollower_follows`, `foLiarPrice_tendsto_s`, `condStableOn_foMenu_refuted`, `condStableOn_of_worldOnly_refuted`, `fo_perIndex_gap_tendsto`, `selfOpaque_perIndex_refuted` |
-/
