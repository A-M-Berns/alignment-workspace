import Cleanroom.Corrigibility.CorrLegitGeneral.WitnessesFn50
import Cleanroom.Corrigibility.CorrLegitGeneral.Transfer
import Cleanroom.Found.LitDdbFrames.ExamplesFact21

/-!
# corr-legit-modif — T4: accuracy increase delivers deference only under the universal quantifier

[[ddb-mm-authors]] C4 l. 91: "Any implemented legitimacy detector scores with one loss. A
modification that is 'accuracy-inducing' under that loss need not be one the agent should defer
to." Both halves exist in `corr-legit-general`: `legitTotalTrustWrt_iff_epistemicValueOn` (accuracy
on *every* gsp score ⟺ the local criterion) and `fn50_single_score_not_local_tt` (on DDB's fn 50
frame the Brier score about `q` improves while local Total Trust on `q`'s question fails). Here the
detector vocabulary: `SingleScoreDetector π F q` is "the frame's Brier about `q` is at most the
prior's", as a predicate on frames; `detector_admits_untrusted` is the implemented detector with
one loss calling accuracy-inducing a modification the agent should not defer to;
`detector_forall_scores_iff` is the universally quantified form (one line from Transfer). C7
(frames no coherent deferrer totally trusts): `fig5F2_untrusted_by_all` — no deferrer that
anticipates `fig5F2`'s row `P_1` totally trusts `fig5F2`, from `fig5F2_not_modestlyInformed` and
Theorem 4.1's hull-and-modest-informedness form.
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames
  Cleanroom.Corrigibility.CorrLegitGeneral Cleanroom.Lit.LitDdbAccuracyMm
  Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

set_option linter.unusedSectionVars false

variable {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]

/-- **A single-score detector**: the modification (frame) is called accuracy-inducing about `q`
when the expert's Brier score about `q` is expected no worse than the prior forecast's.
Source: [[ddb-mm-authors]] C4 l. 91 ("merely requiring that `π` expects `P` to be more accurate
than itself according to (say) the propositional Brier score"); DDB §3.1
Kind: D
Fidelity: exact (one proper score, the Brier, about one proposition) -/
def SingleScoreDetector (π : W → ℝ) (F : Frame W) (q : Finset W) : Prop :=
  expInaccP π F (ind q) brier ≤ expInacc π (ind q) brier (E π (ind q))

/-- **`detector_admits_untrusted`**: on DDB's fn 50 frame the single-score detector admits the
modification (Brier about `q₅₀` improves, `33/200 < 6/25`) while local Total Trust on `q₅₀`'s own
question fails, both cells of positive mass — an implemented detector with one loss calls
accuracy-inducing a modification the agent should not defer to.
Source: [[ddb-mm-authors]] C4 l. 91; DDB §3.1, fn 50; corr-wf13-2-064
Kind: N+ (cited (a): `fn50_single_score_not_local_tt`)
Fidelity: exact
Hyps: (a) none -/
theorem detector_admits_untrusted :
    SingleScoreDetector π50 fn50 q50 ∧ ¬ TotalTrustWrt (questionOf q50) π50 fn50 ∧
    0 < mass π50 q50 ∧ 0 < mass π50 q50ᶜ := by
  obtain ⟨-, h1, h2, h3, h4⟩ := fn50_single_score_not_local_tt
  exact ⟨h3.le, h4, h1, h2⟩

/-- **`detector_forall_scores_iff`**: with the universal quantifier over gsp scores the detector
*is* the local criterion (Theorem 3.2 for `π_L`, `corr-legit-general`'s
`legitTotalTrustWrt_iff_epistemicValueOn`).
Source: [[ddb-mm-authors]] C4 l. 91 ("unless it is read as our Epistemic Value, universally
quantified"); DDB Theorem 3.2
Kind: L (cited (a))
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, `0 < mass π L` -/
theorem detector_forall_scores_iff {Q : W → C} {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    {L : Finset W} (hL : 0 < mass π L) :
    LegitTotalTrustWrt Q π F L ↔
      ∀ X, MeasurableWrt Q X → EpistemicValueOn X ((mass π L)⁻¹ • restrict π L) F :=
  legitTotalTrustWrt_iff_epistemicValueOn hπ hL

/-- **C7**: no deferrer that anticipates `fig5F2`'s second row totally trusts `fig5F2` — the row is
not modestly informed, and Theorem 4.1 (hull + modest informedness of every candidate) forbids it.
Source: [[ddb-mm-authors]] C7 (frames no coherent `π` totally trusts); DDB Fig. 5;
`fig5F2_not_modestlyInformed`, `legitimizingTT_iff_hullAndModestlyInformed`
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, `0 < mass π univ`, `fig5F2.P 1 ∈ fig5F2.cands π` -/
theorem fig5F2_untrusted_by_all {π : Fin 3 → ℝ} (hπ : ∀ w, 0 ≤ π w) (hpos : 0 < mass π univ)
    (h : fig5F2.P 1 ∈ fig5F2.cands π) : ¬ TotalTrust π fig5F2 := by
  intro hT
  have hL : LegitimizingTT π fig5F2 univ := by unfold LegitimizingTT; rw [restrict_univ]; exact hT
  rw [legitimizingTT_iff_hullAndModestlyInformed hπ hpos] at hL
  unfold HullAndModestlyInformed at hL
  rw [restrict_univ, cands_smul _ (inv_pos.2 hpos)] at hL
  exact fig5F2_not_modestlyInformed (hL.2 _ h)

end

end Cleanroom.Corrigibility.CorrLegitModif
