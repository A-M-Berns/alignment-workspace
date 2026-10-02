import Cleanroom.Deference.DefSqueezeDiamond.Reindex
import Cleanroom.Deference.DefSqueezeDiamond.SelfPins
import Cleanroom.Deference.DefSqueezeDiamond.HardRefuted
import Cleanroom.Deference.DefSqueezeDiamond.PaperExpert
import Cleanroom.Deference.DefSqueezeDiamond.PaperArrows
import Cleanroom.Deference.DefSqueezeDiamond.Diamond
import Cleanroom.Deference.DefSqueezeDiamond.Fragment
import Cleanroom.Deference.DefSqueezeDiamond.GapIndicator
import Cleanroom.Deference.DefSqueezeDiamond.GapMesh
import Cleanroom.Deference.DefSqueezeDiamond.ProbeFollower
import Cleanroom.Deference.DefSqueezeDiamond.SelfInstance
import Cleanroom.Deference.DefSqueezeDiamond.Witness

/-!
# `def-squeeze-diamond`: the squeeze and the diamond in the LI setting — over FAF

Root module (package `def-squeeze-diamond`, area `deference`, 2026-10-01). The discharge of the
expert-side bill of `def-lattice-arrows` for the self-expert and for the paper expert read by
a distinct novice, the refutation of hard Total Trust toward the future self, and the diamond
as one composition. Mandate: `run/wp/def-squeeze-diamond/def-squeeze-diamond-mandate.md`;
report, findings and ledger beside it.

| file | target | headlines |
|---|---|---|
| `Reindex` | 1 | `reindexLUV_codes`, `gateFeat_pgenerable`, `deferredCombSyntax`, `expect_deferred_asympLE/GE_of_eventually`, `expect_deferred_asympEq_zero_of_eventually_abs_le`, `…_of_slack` |
| `SelfPins` | 2a–2d | `ExpertPinsGapsEc`, `ExpertFoldsCondOver`, `selfFold_core`, `selfPinGap`, `selfPinsGapsEc`, `selfFoldsAt_rampAbove/Below/ramps/band`, `selfFoldsCondOver`, `selfPinFollower`, `selfEndorse_probe_self`; the arrows restated: `towerValued_of_softTotalTrust_gapBets_ec`, `towerValued_of_value_of_probes_ec`, `condTower_of_towerValued_over` |
| `HardRefuted` | 7 | `DeferredLiar`, `hardAboveQuote`/`hardBelowQuote`, `hard_faces_refuted_core`, `hardTotalTrust_refuted`, `deferredMarket`, `deferredLiarOfDiagonal`, `hardTotalTrust_refuted_paper`, `hardTotalTrust_false`, `sameDay_hard_faces_refuted` |
| `PaperExpert` | 4a–4b, 2e | `ExtendsBase`, `paperExpert`, `paperExpert_quotesAvailable/productQuotesAvailable/condQuotesReflected/rampQuotesAvailable`, `paperRampQuote(Below)`, `paperBandQuote`; `softTotalTrustAbove/Below_self`, `totalTrust_self_via_arrows`, `condTower_self_via_arrows`, `bandReflection_self`, `squeeze_self_of_gapQuotes` |
| `PaperArrows` | 4c | `TowerValuedBase`, `TotalTrustBase`, `totalTrustBase_of_towerValuedBase`, `PinnedGapPackagesBase`, `towerValuedBase_of_totalTrustBase` |
| `Diamond` | 5, 6a | `SelfEndorsesGE`, `value_instance_of_tower_of_selfEndorseGE`, `value_of_towerValued_of_selfEndorseGE`, `PinnedGapPackages`, `PinnedProbeMenus`, `diamond`, `diamond_self` |
| `Fragment` | 3 | `IsGapSource`, `GapFragment`, `gapFragment_of_totalTrust`, `towerValued_of_gapFragment` |
| `GapIndicator` | 4b (indicator class) | `selectLUV`, `indicatorGap`, `gapQuote_indicator`, `pinnedGapPackages_indicator`, `squeeze_self_indicator` |
| `GapMesh` | 4b (general class; repair r1) | `meshSelectLUV`, `meshSelectLUV_valuesAt`, `meshSelectLUV_codes`, `meshGapVal`, `binPlus`/`binMinus`, `meshGapPlus`/`meshGapMinus`, `meshGapPlus_reflected`/`meshGapMinus_reflected`, `gapQuote_meshPlus`/`gapQuote_meshMinus` |
| `ProbeFollower` | 4b (probe package; repair r1) | `followBit`, `followSentence`, `followSentence_holds_iff`, `probeFollower`, `probeFollower_follows`, `probeData_self` |
| `SelfInstance` | 5 witness, 4c (repair r1) | `pinnedGapPackages_self`, `pinnedProbeMenus_self`, `diamond_self_instance`, `squeeze_self`, `towerValued_self_via_pinned`, `towerValued_self_via_fragment`, `pinnedGapPackagesBase_paperExpert`, `towerValuedBase_of_totalTrustBase'`, `towerValuedBase_of_totalTrust` |
| `Witness` | non-vacuity | `diagFamily`, `witness_reindex`, `witness_pin_diagonal`, `witness_fold_diagonal` |
-/
