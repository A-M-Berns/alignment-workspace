import Cleanroom.Decision.DpSmokingLesion.Lemma3

/-!
# dp-smoking-lesion — audit round 2, adversarial lens: probe `CexAS2`

Not imported by the library. `prop14_only_if_catalogue`'s first conjunct is
`StrictOCAt s slObs C cexA₀ () → S2 (s ()) → ¬ RecordsFor slObs slActEv C cexA₀ ()`; the package
proves (S2) at the calibrated state on E2a (every `C`) and E13 (`C(d)(smoke) < 1`) but on
counterexample A only the inequality `≠` (`lemma3_printed_refuted_coverage`), never the
directed (S2). This probe checks that the antecedent is satisfiable on `cexA₀`: at
`δ_refrain` the strictly calibrated state has (S2) (`101/400 · ¼ < 99/400 · ¾`, both act
probabilities positive), so the cexA conjunct is not vacuous.
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

/-- (S2) at the strictly calibrated state of counterexample A at `δ_refrain`. -/
theorem cexA_S2_refrain : S2 (calibratedState procRefrain cexA₀ Finset.univ (nu_univ_pos _ _)) := by
  obtain ⟨h1, h2, h3, h4⟩ := cexA_nu_values
  unfold S2
  simp only [calibratedState_pr, Finset.inter_univ, nu_univ, div_one]
  rw [h1, h2, h3, h4]; norm_num

end Cleanroom.Decision.DpSmokingLesion
