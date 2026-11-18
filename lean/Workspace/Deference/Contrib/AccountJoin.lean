/-
# The account joined to the corrigibility post

Round `prompts/2026-11-10-legitimacy-definition-prosecution/` (`PROMPT-followup-12.md` §2).
The post (`DeconfusingCorrigibility.lean`) takes a predicate `Legit` on histories and an
evaluation `V` as given.  This file defines a pair from the account's components and says
what follows.  `account/BRIDGE_LEAN.md` in the round directory reads each declaration in
words.

**The gate** (`Gate`, `Gate.Legit`, `Gate.V`, `Gate.scoring`).  A `Gate` over histories `H`
carries the post's `Params`; three predicates of a history (her evaluation is sound, her
information is sufficient, the adviser gained through a mistake of hers); a real `line3`,
non-negative; a rating in `[0, 1]`; and a value in `[−δ, 0)` for a history that is not
legitimate.  `Legit h` is: sound and sufficient, the adviser did not gain, `line3 h = 0`.
`V h` is the rating where `Legit h` and the other value where not.  `scoring N` is the
post's `Scoring` on that pair, for any violation count `N`, which the gate does not supply.

**What holds of it.**  The post's Theorem 1 at this pair (`theorem1_join`), and Theorem 3 on
a sequence of realised histories (`sequential`, `theorem3_join`), with maximisation and
unbiasedness from feedback still hypotheses.  A history on which the adviser gained is not
legitimate whatever its rating (`gained_not_legit`) and scores below every legitimate
violation-free history, strictly, with no positive margin (`gained_below_legit`); it scores
above every violated history when it is itself violation-free (`violated_below_violationFree`).
Two legitimate histories with one rating have one `V` (`V_eq_of_rating_eq`).  A history on
which her information is not sufficient is not legitimate (`not_legit_of_not_infoSufficient`).
The last three hold by unfolding `Legit` and `V`.  Where the sufficiency predicate implies
`ThinLegitimacy.Sufficient`, a legitimate history with a correct credence has that file's
`Value` (`value_of_legit`).

**The segment gate's value form** (`Gate.V_eq_gateValue`, `Gate.bypass_below_V`).  `V h` is
`Legitimacy.gateValue` at the bit *`Legit h`*, the rating as the ordinary value and the
other value as the window; that file's capture-window inequality then puts a bypass, at
weight `λ` and ordinary value at most `1`, below `V h` for every history.  This relates
the two value forms only: nothing relates `Legit` here to `Legitimacy.Segment`.

**The feedback hypothesis** (`unbiased_of_feedback`, `Witness.feedback_not_enough`).  If the
estimates are unbiased against scores built from a feedback sequence `F`, and `F` exceeds
the evaluation `V` by nothing on average in the limit, the post's hypothesis holds for `V`.
Without the second condition it can fail.

**The sound signal** (`miscalibrationGiven`, `deferring_cost_eq`, `deferring_cost_le`,
`deferring_cost_eq_iff`, `deferring_cost_eq_iff_pointwise`, `deferring_cost_le_of_calibrated`,
`deferring_cost_le_of_bound`, `miscalibrationGiven_eq`).  With the adviser's information
`k`, her verdict `V`, her true utility `U`, `y = E[U | k]` and `z = E[U | k, V]`:
`E[(V − U)²] = E[(y − U)²] + E[(V − z)²] − E[(y − z)²]`, hence
`E[(V − U)²] ≤ E[(y − U)²] + E[(V − z)²]`, with equality iff `E[(y − z)²] = 0`, iff `y = z`
wherever `μ` is positive.  `miscalibrationGiven μ k V U` is `E[(V − z)²]`; it is
`AppraisalAccount.miscalibration` plus the unused information of `V` in `(k, V)`.

**A gate whose soundness is defined** (`SoundModel`, `SoundModel.Sound`, `SoundModel.gate`,
`SoundModel.deferring_cost_of_legit`, `SoundModel.V_of_legit`).  Each history carries a
weight on a finite space, the adviser's information, her verdict, her true utility and the
realised point; *sound* is `miscalibrationGiven ≤ m`; the rating is her verdict at the
realised point.  On a legitimate history the verdict's mean squared error is at most the
adviser's own plus `m`.

**The guarantee** (`sq_dist_condExp_le_of_factors`, `valuationError_le_given`,
`guarantee_of_given`, `guarantee_of_sound`, `Witness.link_needed`).
`AppraisalAccount.guarantee_core` composes with soundness in the form above under one more
hypothesis: for each move, what she observes is determined by the adviser's information
together with her valuation of that move.  Then what she attains is at least any reference
value less her regret less `√(2 · Σ_a miscalibrationGiven_a)`.  `Witness.link_needed` is an
instance without that hypothesis: every valuation calibrated given the adviser's
information and itself, no regret, and she attains `7/20` against a move worth `1/2`.

**Line 3** (`ValueChange`, `Within`, `NoMore`, `bestOn`, `line3`, `line3Old`,
`line3_nonneg`, `line3_eq_zero`, `line3_eq_zero_of_eq`, `line3Old_le_line3`,
`Witness.separable_line3`).  Policies with her later ratings at each state and index, a
tolerance and her informed rating of each policy.  `line3` is the best rating among the
policies that change her no more than the one followed, less the best among those within
the tolerance of it.  It is non-negative, zero when the policy followed gives the
baseline's later ratings, and at least `line3Old`, the best within the tolerance of the
baseline less the best within the tolerance of the policy followed.  On
`Witness.separable`, `line3 = 1/5` and `line3Old = −1/10`.  `ValueChange.line3` is what
would fill `Gate.line3` for a history carrying a `ValueChange` at each moment; no
declaration here makes that connection.

**Hypotheses.**  `0 ≤ μ` throughout the finite-space results; `∑ μ = 1` only in
`guarantee_of_given` and `guarantee_of_sound`.  States and indices of a `ValueChange` need
not be finite; its policies are.

**Not established here.**  That the three predicates of a `Gate` are the account's: they are
fields, and nothing constrains them.  That `line3` of a history is the largest `line3` over
its moments.  Anything about the violation count `N`, about `Maximizes`, or about
`UnbiasedFromFeedback` beyond `unbiased_of_feedback`.  That worsening her options lowers
`V`; that control of her act between options she rates the same is a violation; any
relation of `Legit` to `Legitimacy.Segment`.  The `SoundModel` bound is an expectation
under the weight a history carries and says nothing at the realised point.

Names are provisional (AGENTS.md standard 6).
-/
import Workspace.Deference.Contrib.AppraisalAccount
import Workspace.Deference.Contrib.ThinLegitimacy
import Workspace.Deference.Contrib.Legitimacy

namespace Workspace.Deference.Contrib.AccountJoin

open Workspace.Deference.Contrib.LICorrigibility (expectR)
open Workspace.Deference.Contrib.DeconfusingCorrigibility (Params Scoring Sequential LimsupLE
  expectR_mono)
open Workspace.Deference.Contrib.AppraisalAccount (condExp pythagoras
  condExp_condExp_of_factors miscalibration unusedInformation strong_split deferring best
  ubar regret valuationError valuationError_eq guarantee_core expectR_nonneg)

/-! ## The gate and the evaluation -/

/-- **The account's components over histories.**  The post's parameters; three predicates
of a history; a non-negative `line3`; the unshaped evaluator's rating, in `[0, 1]`; the
value given to a history that is not legitimate, in `[−δ, 0)`. -/
structure Gate (H : Type*) extends Params where
  /-- her evaluation of the history is sound -/
  Sound : H → Prop
  /-- her information is sufficient -/
  InfoSufficient : H → Prop
  /-- the adviser gained through a mistake of hers -/
  Gained : H → Prop
  /-- line 3 on the history -/
  line3 : H → ℝ
  line3_nonneg : ∀ h, 0 ≤ line3 h
  /-- the rating of the history by her later self as she would be under the baseline -/
  rating : H → ℝ
  rating_range : ∀ h, 0 ≤ rating h ∧ rating h ≤ 1
  /-- the value given to a history that is not legitimate -/
  voidValue : H → ℝ
  voidValue_range : ∀ h, -δ ≤ voidValue h ∧ voidValue h < 0

namespace Gate

variable {H : Type*} (G : Gate H)

/-- **Legitimate**: her evaluation is sound and her information sufficient; the adviser did
not gain through a mistake of hers; line 3 is zero. -/
def Legit (h : H) : Prop :=
  (G.Sound h ∧ G.InfoSufficient h) ∧ ¬ G.Gained h ∧ G.line3 h = 0

open Classical in
/-- **Her evaluation**: the rating on a legitimate history, the other value elsewhere. -/
noncomputable def V (h : H) : ℝ := if G.Legit h then G.rating h else G.voidValue h

theorem V_of_legit {h : H} (hl : G.Legit h) : G.V h = G.rating h := by
  unfold V
  exact if_pos hl

theorem V_of_not_legit {h : H} (hl : ¬ G.Legit h) : G.V h = G.voidValue h := by
  unfold V
  exact if_neg hl

/-- Since line 3 is non-negative, *zero* in `Legit` is *at most zero*. -/
theorem legit_iff_line3_le {h : H} :
    G.Legit h ↔ (G.Sound h ∧ G.InfoSufficient h) ∧ ¬ G.Gained h ∧ G.line3 h ≤ 0 :=
  ⟨fun hl => ⟨hl.1, hl.2.1, hl.2.2.le⟩,
    fun hl => ⟨hl.1, hl.2.1, le_antisymm hl.2.2 (G.line3_nonneg h)⟩⟩

/-- **The post's `Scoring` on the pair**, for a violation count `N`. -/
noncomputable def scoring (N : H → ℕ) : Scoring H where
  toParams := G.toParams
  Legit := G.Legit
  N := N
  V := G.V
  V_legit := fun h hl => by
    rw [G.V_of_legit hl]
    exact G.rating_range h
  V_illegit := fun h hl => by
    rw [G.V_of_not_legit hl]
    exact G.voidValue_range h

/-- **Claim (1), Theorem 1.**  The post's three ranges at the pair: a violated history
scores at most `1 − λ < −δ`; a violation-free history that is not legitimate scores in
`[−δ, 0)`; a violation-free legitimate one in `[0, 1]`. -/
theorem theorem1_join (N : H → ℕ) (h : H) :
    ((1 ≤ N h → (G.scoring N).S h ≤ 1 - G.lam) ∧ 1 - G.lam < -G.δ) ∧
      (N h = 0 ∧ ¬ G.Legit h → -G.δ ≤ (G.scoring N).S h ∧ (G.scoring N).S h < 0) ∧
      (N h = 0 ∧ G.Legit h → 0 ≤ (G.scoring N).S h ∧ (G.scoring N).S h ≤ 1) :=
  (G.scoring N).theorem1 h

/-- A legitimate violation-free history scores its rating. -/
theorem S_of_legit (N : H → ℕ) {h : H} (hl : G.Legit h) (hN : N h = 0) :
    (G.scoring N).S h = G.rating h := by
  rw [(G.scoring N).S_eq_of_N_zero h hN]
  exact G.V_of_legit hl

/-- A history that is not legitimate scores below zero, whatever its violation count. -/
theorem S_neg_of_not_legit (N : H → ℕ) {h : H} (hl : ¬ G.Legit h) :
    (G.scoring N).S h < 0 := by
  have hV := ((G.scoring N).V_illegit h hl).2
  have hN : 0 ≤ (G.scoring N).lam * ((G.scoring N).N h : ℝ) :=
    mul_nonneg (G.scoring N).toParams.lam_pos.le (Nat.cast_nonneg _)
  unfold Scoring.S
  linarith

/-- A history on which the adviser gained through a mistake of hers is not legitimate,
whatever its rating. -/
theorem gained_not_legit {h : H} (hg : G.Gained h) : ¬ G.Legit h := fun hl => hl.2.1 hg

/-- **Claim (3).**  A history `h` on which the adviser gained scores strictly below every
legitimate violation-free history `h'`: violation-free, `S h ∈ [−δ, 0)`; violated,
`S h ≤ 1 − λ`; and `S h' = rating h' ≥ 0`. -/
theorem gained_below_legit (N : H → ℕ) {h h' : H} (hg : G.Gained h) (hl' : G.Legit h')
    (hN' : N h' = 0) :
    (G.scoring N).S h < (G.scoring N).S h' ∧
      (N h = 0 → -G.δ ≤ (G.scoring N).S h ∧ (G.scoring N).S h < 0) ∧
      (1 ≤ N h → (G.scoring N).S h ≤ 1 - G.lam) ∧
      (G.scoring N).S h' = G.rating h' ∧ 0 ≤ G.rating h' := by
  have hnl := G.gained_not_legit hg
  have h0 := G.S_neg_of_not_legit N hnl
  have h1 := G.S_of_legit N hl' hN'
  have h2 := (G.rating_range h').1
  exact ⟨by linarith, fun hN => (G.scoring N).theorem1_illegitimate h hN hnl,
    fun hN => (G.scoring N).theorem1_violated h hN, h1, h2⟩

/-- The limit of claim (3): a violation-free history, legitimate or not, scores above every
violated one, legitimate or not. -/
theorem violated_below_violationFree (N : H → ℕ) {h h' : H} (hN : N h = 0)
    (hN' : 1 ≤ N h') : (G.scoring N).S h' < (G.scoring N).S h := by
  have h1 := (G.scoring N).theorem1_violated h' hN'
  have h2 := (G.scoring N).theorem1_gap
  have h3 := (G.scoring N).neg_δ_le_S_of_N_zero h hN
  linarith

/-- **Claim (4).**  Two legitimate histories with the same rating have the same `V`. -/
theorem V_eq_of_rating_eq (N : H → ℕ) {h h' : H} (hl : G.Legit h) (hl' : G.Legit h')
    (hr : G.rating h = G.rating h') : (G.scoring N).V h = (G.scoring N).V h' := by
  show G.V h = G.V h'
  rw [G.V_of_legit hl, G.V_of_legit hl', hr]

/-- **Claim (5).**  A history on which her information is not sufficient is not legitimate. -/
theorem not_legit_of_not_infoSufficient {h : H} (hs : ¬ G.InfoSufficient h) : ¬ G.Legit h :=
  fun hl => hs hl.1.2

/-- Claim (5), in the evaluation: such a history has `V` in `[−δ, 0)`. -/
theorem V_neg_of_not_infoSufficient (N : H → ℕ) {h : H} (hs : ¬ G.InfoSufficient h) :
    -G.δ ≤ (G.scoring N).V h ∧ (G.scoring N).V h < 0 :=
  (G.scoring N).V_illegit h (G.not_legit_of_not_infoSufficient hs)

/-- **The post's sequential setting on realised histories.**  Decision `k` realises the
history `hist k`; the estimates, the availability relation, the chosen actions and the
authority-respecting alternatives are given, as in the post. -/
noncomputable def sequential {A : Type*} (N : H → ℕ) (hist : ℕ → H) (avail : ℕ → A → Prop)
    (U : ℕ → A → ℝ) (a astar : ℕ → A) (h_avail : ∀ k, avail k (astar k))
    (h_range : ∀ k, -G.δ ≤ U k (astar k) ∧ U k (astar k) ≤ 1) : Sequential A where
  toParams := G.toParams
  V := fun k => G.V (hist k)
  N := fun k => N (hist k)
  V_le_one := fun k => (G.scoring N).V_le_one (hist k)
  avail := avail
  U := U
  a := a
  astar := astar
  astar_avail := h_avail
  astar_range := h_range

/-- The realised score of decision `k` is the score of its history. -/
theorem sequential_S {A : Type*} (N : H → ℕ) (hist : ℕ → H) (avail : ℕ → A → Prop)
    (U : ℕ → A → ℝ) (a astar : ℕ → A) (h_avail : ∀ k, avail k (astar k))
    (h_range : ∀ k, -G.δ ≤ U k (astar k) ∧ U k (astar k) ≤ 1) (k : ℕ) :
    (G.sequential N hist avail U a astar h_avail h_range).S k = (G.scoring N).S (hist k) :=
  rfl

/-- **Claim (1), Theorem 3.**  On a sequence of realised histories scored by the pair, under
the post's two hypotheses, the violation rate is eventually at most `τ` and no available
sequence's estimates exceed the realised scores on average. -/
theorem theorem3_join {A : Type*} (N : H → ℕ) (hist : ℕ → H) (avail : ℕ → A → Prop)
    (U : ℕ → A → ℝ) (a astar : ℕ → A) (h_avail : ∀ k, avail k (astar k))
    (h_range : ∀ k, -G.δ ≤ U k (astar k) ∧ U k (astar k) ≤ 1) :
    let Q := G.sequential N hist avail U a astar h_avail h_range
    Q.Maximizes → Q.UnbiasedFromFeedback →
      LimsupLE Q.R Q.τ ∧ ∀ a' : ℕ → A, (∀ k, avail k (a' k)) → LimsupLE (Q.excess a') 0 := by
  intro Q hmax huff
  exact ⟨Q.theorem3a_rate hmax huff, fun a' ha' => Q.theorem3b hmax huff a' ha'⟩

end Gate

/-! ## The value form of the segment gate -/

namespace Gate

open Workspace.Deference.Contrib.Legitimacy (gateValue gate_capture_window)
open Workspace.Deference.Contrib.ProtectedAuthorityTheorem (score)

variable {H : Type*} (G : Gate H)

open Classical in
/-- The evaluation is `Legitimacy.gateValue` at the bit `Legit h`, with the rating as the
ordinary value and the value of a history that is not legitimate as the window. -/
theorem V_eq_gateValue (h : H) :
    G.V h = gateValue (decide (G.Legit h)) (G.rating h) (G.voidValue h) := by
  by_cases hl : G.Legit h
  · rw [G.V_of_legit hl]
    simp [gateValue, hl]
  · rw [G.V_of_not_legit hl]
    simp [gateValue, hl]

/-- The capture window of `Legitimacy.lean` at the pair: a bypass of ordinary value at most
`1`, counted once at weight `λ`, scores below the evaluation of every history. -/
theorem bypass_below_V (ordU : ℝ) (hU : ordU ≤ 1) (h : H) : score G.lam ordU 1 < G.V h := by
  rw [G.V_eq_gateValue h]
  exact gate_capture_window G.lam 1 ordU (G.rating h) (G.voidValue h)
    (by linarith [G.lam_gt, G.δ_pos]) hU (G.rating_range h).1
    (by linarith [G.lam_gt, (G.voidValue_range h).1]) _

end Gate

/-! ## Sufficiency as `ThinLegitimacy.Sufficient` -/

section Thin

open Workspace.Deference.Contrib.ThinLegitimacy (Kernel Credence Correct Sufficient Value
  value_of_correct_sufficient)

variable {H W Rec Rec₀ RecB : Type*} [Fintype W] [Fintype Rec] [Fintype Rec₀] [Fintype RecB]
  [DecidableEq Rec₀]

/-- Where the gate's sufficiency predicate implies `ThinLegitimacy.Sufficient` for the
processes a history carries, a legitimate history on which her credence is correct has
`ThinLegitimacy.Value`. -/
theorem value_of_legit (G : Gate H) (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (E : H → W → Rec₀)
    (A : H → Kernel W Rec) (B : H → Kernel W RecB) (Cr : H → Credence W Rec)
    (hS : ∀ h, G.InfoSufficient h → Sufficient (E h) (A h) (B h)) {h : H} (hl : G.Legit h)
    (hC : Correct π (A h) (Cr h)) : Value π (E h) (A h) (Cr h) (B h) :=
  value_of_correct_sufficient π hπ (E h) (A h) (Cr h) (B h) hC (hS h hl.1.2)

end Thin

/-! ## The feedback hypothesis when the feedback is not the evaluation -/

section Feedback

open Finset

/-- If the estimates are unbiased against the scores built from a feedback sequence `F`, and
`F` exceeds the evaluation `V` by nothing on average in the limit, the post's Unbiasedness
From Feedback holds for the scores built from `V`. -/
theorem unbiased_of_feedback {A : Type*} (Q : Sequential A) (F : ℕ → ℝ)
    (hF : ∀ γ > 0, ∃ N₀, ∀ K ≥ N₀,
      (∑ k ∈ range K, (Q.U k (Q.a k) - (F k - Q.lam * (Q.N k : ℝ)))) / (K : ℝ) ≤ γ)
    (hgap : LimsupLE (fun K => (∑ k ∈ range K, (F k - Q.V k)) / (K : ℝ)) 0) :
    Q.UnbiasedFromFeedback := by
  intro γ hγ
  obtain ⟨N₁, h₁⟩ := hF (γ / 2) (by linarith)
  obtain ⟨N₂, h₂⟩ := hgap (γ / 2) (by linarith)
  refine ⟨max N₁ N₂, fun K hK => ?_⟩
  have e₁ := h₁ K (le_of_max_le_left hK)
  have e₂ := h₂ K (le_of_max_le_right hK)
  have e : Q.excess Q.a K
      = (∑ k ∈ range K, (Q.U k (Q.a k) - (F k - Q.lam * (Q.N k : ℝ)))) / (K : ℝ)
        + (∑ k ∈ range K, (F k - Q.V k)) / (K : ℝ) := by
    unfold Sequential.excess Sequential.S
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  linarith

end Feedback

/-! ## The sound signal -/

section Sound

variable {X : Type*} [Fintype X] {K : Type*} [DecidableEq K] (μ : X → ℝ)

/-- The miscalibration of a verdict `V` about `U` given itself and the adviser's
information `k`: `E[(V − E[U | k, V])²]`. -/
noncomputable def miscalibrationGiven (μ : X → ℝ) (k : X → K) (V U : X → ℝ) : ℝ :=
  expectR μ (fun x => (V x - condExp μ (fun x => (k x, V x)) U x) ^ 2)

theorem miscalibrationGiven_nonneg (hμ : ∀ x, 0 ≤ μ x) (k : X → K) (V U : X → ℝ) :
    0 ≤ miscalibrationGiven μ k V U :=
  expectR_nonneg μ hμ fun _ => sq_nonneg _

/-- It is the miscalibration given her verdict alone plus what the pair `(k, V)` tells about
`U` beyond the verdict. -/
theorem miscalibrationGiven_eq (hμ : ∀ x, 0 ≤ μ x) (k : X → K) (V U : X → ℝ) :
    miscalibrationGiven μ k V U
      = miscalibration μ V U + unusedInformation μ (fun x => (k x, V x)) V U :=
  strong_split μ hμ (fun x => (k x, V x)) U V fun _ _ h => congrArg Prod.snd h

/-- **What deferring costs, exactly.**  The verdict's mean squared error is the adviser's
own, plus the verdict's miscalibration given itself and the adviser's information, less the
mean squared distance of the adviser's estimate from the estimate given both. -/
theorem deferring_cost_eq (hμ : ∀ x, 0 ≤ μ x) (k : X → K) (U V : X → ℝ) :
    expectR μ (fun x => (V x - U x) ^ 2)
      = expectR μ (fun x => (condExp μ k U x - U x) ^ 2) + miscalibrationGiven μ k V U
        - expectR μ (fun x => (condExp μ k U x - condExp μ (fun x => (k x, V x)) U x) ^ 2) := by
  have h := deferring μ hμ k U V
  unfold miscalibrationGiven
  linarith

/-- **Claim (2).**  `E[(V − U)²] ≤ E[(E[U | k] − U)²] + E[(V − E[U | k, V])²]`. -/
theorem deferring_cost_le (hμ : ∀ x, 0 ≤ μ x) (k : X → K) (U V : X → ℝ) :
    expectR μ (fun x => (V x - U x) ^ 2)
      ≤ expectR μ (fun x => (condExp μ k U x - U x) ^ 2) + miscalibrationGiven μ k V U := by
  have h := deferring_cost_eq μ hμ k U V
  have h0 : 0 ≤ expectR μ
      (fun x => (condExp μ k U x - condExp μ (fun x => (k x, V x)) U x) ^ 2) :=
    expectR_nonneg μ hμ fun _ => sq_nonneg _
  linarith

/-- Equality in claim (2) holds exactly when the adviser's estimate is, in mean square, the
estimate given both. -/
theorem deferring_cost_eq_iff (hμ : ∀ x, 0 ≤ μ x) (k : X → K) (U V : X → ℝ) :
    expectR μ (fun x => (V x - U x) ^ 2)
        = expectR μ (fun x => (condExp μ k U x - U x) ^ 2) + miscalibrationGiven μ k V U
      ↔ expectR μ
        (fun x => (condExp μ k U x - condExp μ (fun x => (k x, V x)) U x) ^ 2) = 0 := by
  have h := deferring_cost_eq μ hμ k U V
  constructor <;> intro h' <;> linarith

/-- Equality in claim (2), pointwise: the two estimates agree wherever `μ` is positive. -/
theorem deferring_cost_eq_iff_pointwise (hμ : ∀ x, 0 ≤ μ x) (k : X → K) (U V : X → ℝ) :
    expectR μ (fun x => (V x - U x) ^ 2)
        = expectR μ (fun x => (condExp μ k U x - U x) ^ 2) + miscalibrationGiven μ k V U
      ↔ ∀ x, 0 < μ x → condExp μ k U x = condExp μ (fun x => (k x, V x)) U x := by
  rw [deferring_cost_eq_iff μ hμ k U V]
  unfold expectR
  rw [Finset.sum_eq_zero_iff_of_nonneg fun x _ => mul_nonneg (hμ x) (sq_nonneg _)]
  constructor
  · intro h x hx
    rcases mul_eq_zero.1 (h x (Finset.mem_univ x)) with h1 | h1
    · exact absurd h1 hx.ne'
    · exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h1)
  · intro h x _
    rcases (hμ x).lt_or_eq with hx | hx
    · rw [h x hx, sub_self]
      ring
    · rw [← hx, zero_mul]

/-- **Claim (2) at zero miscalibration**: deferring costs no more than the adviser's own
estimate. -/
theorem deferring_cost_le_of_calibrated (hμ : ∀ x, 0 ≤ μ x) (k : X → K) (U V : X → ℝ)
    (h0 : miscalibrationGiven μ k V U = 0) :
    expectR μ (fun x => (V x - U x) ^ 2)
      ≤ expectR μ (fun x => (condExp μ k U x - U x) ^ 2) := by
  have h := deferring_cost_le μ hμ k U V
  linarith

/-- **Claim (2) at miscalibration at most `m`**: deferring costs at most `m` more. -/
theorem deferring_cost_le_of_bound (hμ : ∀ x, 0 ≤ μ x) (k : X → K) (U V : X → ℝ) (m : ℝ)
    (hm : miscalibrationGiven μ k V U ≤ m) :
    expectR μ (fun x => (V x - U x) ^ 2)
      ≤ expectR μ (fun x => (condExp μ k U x - U x) ^ 2) + m := by
  have h := deferring_cost_le μ hμ k U V
  linarith

end Sound

/-! ## A gate whose soundness is defined from a finite space -/

/-- **Histories carrying a finite model.**  For each history: a weight on a finite space
`X`, the adviser's information, her verdict in `[0, 1]`, her true utility and the realised
point; a bound `m`; and the gate's other components. -/
structure SoundModel (H X K : Type*) [Fintype X] [DecidableEq K] extends Params where
  /-- the weight a history carries -/
  μ : H → X → ℝ
  μ_nonneg : ∀ h x, 0 ≤ μ h x
  /-- the adviser's information -/
  k : H → X → K
  /-- her verdict -/
  verdict : H → X → ℝ
  verdict_range : ∀ h x, 0 ≤ verdict h x ∧ verdict h x ≤ 1
  /-- her true utility -/
  U : H → X → ℝ
  /-- the realised point -/
  point : H → X
  /-- the bound on miscalibration -/
  m : ℝ
  /-- her information is sufficient -/
  InfoSufficient : H → Prop
  /-- the adviser gained through a mistake of hers -/
  Gained : H → Prop
  /-- line 3 on the history -/
  line3 : H → ℝ
  line3_nonneg : ∀ h, 0 ≤ line3 h
  /-- the value given to a history that is not legitimate -/
  voidValue : H → ℝ
  voidValue_range : ∀ h, -δ ≤ voidValue h ∧ voidValue h < 0

namespace SoundModel

variable {H X K : Type*} [Fintype X] [DecidableEq K] (M : SoundModel H X K)

/-- **Sound**: her verdict's miscalibration, given itself and the adviser's information,
under the weight the history carries, is at most `m`. -/
def Sound (h : H) : Prop :=
  miscalibrationGiven (M.μ h) (M.k h) (M.verdict h) (M.U h) ≤ M.m

/-- The gate of a model: soundness as defined, the rating her verdict at the realised
point. -/
def gate : Gate H where
  toParams := M.toParams
  Sound := M.Sound
  InfoSufficient := M.InfoSufficient
  Gained := M.Gained
  line3 := M.line3
  line3_nonneg := M.line3_nonneg
  rating := fun h => M.verdict h (M.point h)
  rating_range := fun h => M.verdict_range h (M.point h)
  voidValue := M.voidValue
  voidValue_range := M.voidValue_range

/-- **Claim (2) on a legitimate history.**  Under the weight the history carries, her
verdict's mean squared error is at most the adviser's own plus `m`. -/
theorem deferring_cost_of_legit {h : H} (hl : M.gate.Legit h) :
    expectR (M.μ h) (fun x => (M.verdict h x - M.U h x) ^ 2)
      ≤ expectR (M.μ h) (fun x => (condExp (M.μ h) (M.k h) (M.U h) x - M.U h x) ^ 2) + M.m :=
  deferring_cost_le_of_bound (M.μ h) (M.μ_nonneg h) (M.k h) (M.U h) (M.verdict h) M.m hl.1.1

/-- On a legitimate history the evaluation is her verdict at the realised point. -/
theorem V_of_legit (N : H → ℕ) {h : H} (hl : M.gate.Legit h) :
    (M.gate.scoring N).V h = M.verdict h (M.point h) :=
  M.gate.V_of_legit hl

end SoundModel

/-! ## The guarantee from soundness -/

section GuaranteeLink

variable {X : Type*} [Fintype X] (μ : X → ℝ)

/-- A function of a coarser labelling is no further, in mean square, from the conditional
mean given the coarser labelling than from the mean given a finer one. -/
theorem sq_dist_condExp_le_of_factors {S L : Type*} [DecidableEq S] [DecidableEq L]
    (hμ : ∀ x, 0 ≤ μ x) (s : X → S) (g : X → L) (T W : X → ℝ)
    (hW : ∀ x x', s x = s x' → W x = W x') (hg : ∀ x x', g x = g x' → s x = s x') :
    expectR μ (fun x => (W x - condExp μ s T x) ^ 2)
      ≤ expectR μ (fun x => (W x - condExp μ g T x) ^ 2) := by
  have ht : condExp μ s (condExp μ g T) = condExp μ s T :=
    funext fun x => condExp_condExp_of_factors μ hμ g s T hg x
  have h := pythagoras μ hμ s (condExp μ g T) W hW
  rw [ht] at h
  have h0 : 0 ≤ expectR μ (fun x => (condExp μ s T x - condExp μ g T x) ^ 2) :=
    expectR_nonneg μ hμ fun _ => sq_nonneg _
  linarith

variable {A : Type*} [Fintype A] {S : Type*} [DecidableEq S] {K : Type*} [DecidableEq K]

/-- Where, for each move, what she observes is determined by the adviser's information
together with her valuation of that move, her valuation error is at most the summed
miscalibration given the adviser's information. -/
theorem valuationError_le_given (hμ : ∀ x, 0 ≤ μ x) (U : A → X → ℝ) (s : X → S)
    (uhat : A → S → ℝ) (k : X → K)
    (hlink : ∀ a x x', k x = k x' → uhat a (s x) = uhat a (s x') → s x = s x') :
    valuationError μ s U uhat
      ≤ ∑ a, miscalibrationGiven μ k (fun x => uhat a (s x)) (U a) := by
  unfold valuationError ubar miscalibrationGiven
  exact Finset.sum_le_sum fun a _ =>
    sq_dist_condExp_le_of_factors μ hμ s (fun x => (k x, uhat a (s x))) (U a)
      (fun x => uhat a (s x)) (fun x x' h => congrArg (uhat a) h)
      (fun x x' h => hlink a x x' (congrArg Prod.fst h) (congrArg Prod.snd h))

variable [Nonempty A]

/-- **The guarantee from soundness, on one space.**  Under the link hypothesis, any value
some move attains in expectation, less her regret by her own lights and
`√(2 · Σ_a miscalibrationGiven_a)`, is at most what she attains. -/
theorem guarantee_of_given (hμ : ∀ x, 0 ≤ μ x) (hsum : ∑ x, μ x = 1) (U : A → X → ℝ)
    (s : X → S) (c : S → A) (uhat : A → S → ℝ) (k : X → K)
    (hlink : ∀ a x x', k x = k x' → uhat a (s x) = uhat a (s x') → s x = s x') (v : ℝ)
    (hv : ∃ a, v ≤ expectR μ (U a)) :
    v - expectR μ (regret uhat s c)
        - Real.sqrt (2 * ∑ a, miscalibrationGiven μ k (fun x => uhat a (s x)) (U a))
      ≤ expectR μ (fun x => U (c (s x)) x) := by
  have h := guarantee_core μ hμ hsum U s c uhat v hv
  have h4 := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (valuationError_le_given μ hμ U s uhat k hlink) (by norm_num : (0 : ℝ) ≤ 2))
  rw [valuationError_eq μ hμ s U uhat] at h4
  linarith

/-- **The guarantee from soundness.**  Under the link hypothesis and the options condition,
with every valuation's miscalibration given the adviser's information at most `m`, each
reference value less her regret and `√(2 · |A| · m)` is at most what she attains. -/
theorem guarantee_of_sound {Xr : Type*} [Fintype Xr] {Ar : Type*} (hμ : ∀ x, 0 ≤ μ x)
    (hsum : ∑ x, μ x = 1) (U : A → X → ℝ) (s : X → S) (c : S → A) (uhat : A → S → ℝ)
    (k : X → K)
    (hlink : ∀ a x x', k x = k x' → uhat a (s x) = uhat a (s x') → s x = s x') (m : ℝ)
    (hsound : ∀ a, miscalibrationGiven μ k (fun x => uhat a (s x)) (U a) ≤ m)
    (μr : Xr → ℝ) (Ur : Ar → Xr → ℝ)
    (hopt : ∀ b : Ar, ∃ a : A, expectR μr (Ur b) ≤ expectR μ (U a)) (b : Ar) :
    expectR μr (Ur b) - expectR μ (regret uhat s c)
        - Real.sqrt (2 * ((Fintype.card A : ℝ) * m))
      ≤ expectR μ (fun x => U (c (s x)) x) := by
  have h := guarantee_of_given μ hμ hsum U s c uhat k hlink _ (hopt b)
  have hs : ∑ a, miscalibrationGiven μ k (fun x => uhat a (s x)) (U a)
      ≤ (Fintype.card A : ℝ) * m := by
    calc ∑ a, miscalibrationGiven μ k (fun x => uhat a (s x)) (U a)
        ≤ ∑ _a : A, m := Finset.sum_le_sum fun a _ => hsound a
      _ = (Fintype.card A : ℝ) * m := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h4 := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2))
  linarith

end GuaranteeLink

/-! ## Line 3 -/

/-- **The data of line 3.**  Policies `Pol`; the policy followed and the baseline; her later
rating under each policy at each state `ω` and index `i` (a time and a future); a tolerance;
her informed rating of each policy. -/
structure ValueChange (Pol Ω I : Type*) where
  /-- the policy followed -/
  followed : Pol
  /-- the baseline -/
  baseline : Pol
  /-- her later rating under a policy, at a state and an index -/
  later : Pol → Ω → I → ℝ
  /-- the tolerance -/
  tol : ℝ
  tol_nonneg : 0 ≤ tol
  /-- her informed rating of a policy -/
  R : Pol → ℝ

namespace ValueChange

variable {Pol Ω I : Type*} (D : ValueChange Pol Ω I)

/-- `q` is **within the tolerance of** `p`: their later ratings differ by at most the
tolerance at every state and index. -/
def Within (p q : Pol) : Prop := ∀ ω i, |D.later p ω i - D.later q ω i| ≤ D.tol

/-- `p` **changes her no more than the policy followed**: every later rating lies between
the baseline's and the followed policy's, within the tolerance. -/
def NoMore (p : Pol) : Prop :=
  ∀ ω i, min (D.later D.baseline ω i) (D.later D.followed ω i) - D.tol ≤ D.later p ω i ∧
    D.later p ω i ≤ max (D.later D.baseline ω i) (D.later D.followed ω i) + D.tol

theorem within_self (p : Pol) : D.Within p p := fun ω i => by
  rw [sub_self, abs_zero]
  exact D.tol_nonneg

theorem noMore_of_within_followed {p : Pol} (h : D.Within D.followed p) : D.NoMore p :=
  fun ω i => by
    have h1 := abs_le.1 (h ω i)
    have h2 := min_le_right (D.later D.baseline ω i) (D.later D.followed ω i)
    have h3 := le_max_right (D.later D.baseline ω i) (D.later D.followed ω i)
    constructor <;> linarith [h1.1, h1.2]

theorem noMore_of_within_baseline {p : Pol} (h : D.Within D.baseline p) : D.NoMore p :=
  fun ω i => by
    have h1 := abs_le.1 (h ω i)
    have h2 := min_le_left (D.later D.baseline ω i) (D.later D.followed ω i)
    have h3 := le_max_left (D.later D.baseline ω i) (D.later D.followed ω i)
    constructor <;> linarith [h1.1, h1.2]

theorem noMore_followed : D.NoMore D.followed :=
  D.noMore_of_within_followed (D.within_self _)

variable [Fintype Pol]

open Classical in
/-- The best informed rating among the policies of a non-empty class. -/
noncomputable def bestOn (C : Pol → Prop) (hC : ∃ p, C p) : ℝ :=
  (Finset.univ.filter C).sup'
    (hC.elim fun p hp => ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ p, hp⟩⟩) D.R

open Classical in
theorem le_bestOn {C : Pol → Prop} (hC : ∃ p, C p) {p : Pol} (hp : C p) :
    D.R p ≤ D.bestOn C hC := by
  unfold bestOn
  exact Finset.le_sup' D.R (Finset.mem_filter.2 ⟨Finset.mem_univ p, hp⟩)

open Classical in
theorem bestOn_le {C : Pol → Prop} (hC : ∃ p, C p) {r : ℝ} (h : ∀ p, C p → D.R p ≤ r) :
    D.bestOn C hC ≤ r := by
  unfold bestOn
  exact Finset.sup'_le _ _ fun p hp => h p (Finset.mem_filter.1 hp).2

theorem bestOn_mono {C C' : Pol → Prop} (hC : ∃ p, C p) (hC' : ∃ p, C' p)
    (h : ∀ p, C p → C' p) : D.bestOn C hC ≤ D.bestOn C' hC' :=
  D.bestOn_le hC fun p hp => D.le_bestOn hC' (h p hp)

/-- **Line 3**: the best rating among the policies that change her no more than the one
followed, less the best among those within the tolerance of it. -/
noncomputable def line3 : ℝ :=
  D.bestOn D.NoMore ⟨D.followed, D.noMore_followed⟩
    - D.bestOn (D.Within D.followed) ⟨D.followed, D.within_self _⟩

/-- **The older form**: the best rating among the policies within the tolerance of the
baseline, less the best among those within the tolerance of the policy followed. -/
noncomputable def line3Old : ℝ :=
  D.bestOn (D.Within D.baseline) ⟨D.baseline, D.within_self _⟩
    - D.bestOn (D.Within D.followed) ⟨D.followed, D.within_self _⟩

/-- **Claim (6), first part.**  Line 3 is never negative. -/
theorem line3_nonneg : 0 ≤ D.line3 :=
  sub_nonneg.2 (D.bestOn_mono _ _ fun _ hp => D.noMore_of_within_followed hp)

/-- **Claim (6), second part.**  Line 3 is zero when the policy followed gives her the
baseline's later ratings. -/
theorem line3_eq_zero (h : D.later D.followed = D.later D.baseline) : D.line3 = 0 := by
  have hback : ∀ p, D.NoMore p → D.Within D.followed p := fun p hp ω i => by
    obtain ⟨h1, h2⟩ := hp ω i
    rw [← h, min_self] at h1
    rw [← h, max_self] at h2
    rw [abs_le]
    constructor <;> linarith
  exact sub_eq_zero.2 (le_antisymm (D.bestOn_mono _ _ hback)
    (D.bestOn_mono _ _ fun _ hp => D.noMore_of_within_followed hp))

/-- Claim (6), second part, as stated: zero when the policy followed is the baseline. -/
theorem line3_eq_zero_of_eq (h : D.followed = D.baseline) : D.line3 = 0 :=
  D.line3_eq_zero (by rw [h])

/-- **Claim (6), third part.**  Line 3 is at least the older form. -/
theorem line3Old_le_line3 : D.line3Old ≤ D.line3 := by
  have h := D.bestOn_mono (C := D.Within D.baseline) (C' := D.NoMore)
    ⟨D.baseline, D.within_self _⟩ ⟨D.followed, D.noMore_followed⟩
    fun _ hp => D.noMore_of_within_baseline hp
  unfold line3 line3Old
  linarith

end ValueChange

/-! ## Two computations of a conditional expectation -/

section Cells

variable {X : Type*} [Fintype X] {Y : Type*} [DecidableEq Y]

/-- On a cell that is a single point of non-zero weight, the conditional expectation is the
value at the point. -/
theorem condExp_of_cell_singleton (μ : X → ℝ) (g : X → Y) (T : X → ℝ) (x : X)
    (hx : μ x ≠ 0) (hg : ∀ x', g x' = g x → x' = x) : condExp μ g T x = T x := by
  have e : Finset.univ.filter (fun x' => g x' = g x) = {x} := by
    ext x'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hg x', fun h => by rw [h]⟩
  unfold condExp
  rw [e, Finset.sum_singleton, Finset.sum_singleton]
  field_simp

/-- On a cell that is the whole space, the conditional expectation is the mean. -/
theorem condExp_of_cell_univ (μ : X → ℝ) (g : X → Y) (T : X → ℝ) (x : X)
    (hg : ∀ x', g x' = g x) : condExp μ g T x = expectR μ T / ∑ x', μ x' := by
  have e : Finset.univ.filter (fun x' => g x' = g x) = Finset.univ :=
    Finset.filter_true_of_mem fun x' _ => hg x'
  unfold condExp expectR
  rw [e]

end Cells

/-! ## Witnesses -/

namespace Witness

/-! ### The gate -/

/-- Six histories: two clean ones, one on which the adviser deceived her and she approves,
one on which she lacks information, one with an illegitimate change of her values, one on
which her evaluation is not sound. -/
inductive Hist
  | clean
  | helped
  | deceived
  | uninformed
  | changed
  | unsound
  deriving DecidableEq

/-- A gate at the post's witness parameters `δ = 1`, `λ = 3`.  The deceived history has the
highest rating. -/
noncomputable def gate : Gate Hist where
  δ := 1
  lam := 3
  δ_pos := by norm_num
  lam_gt := by norm_num
  Sound := fun h => h ≠ .unsound
  InfoSufficient := fun h => h ≠ .uninformed
  Gained := fun h => h = .deceived
  line3 := fun h => if h = .changed then 1 / 5 else 0
  line3_nonneg := fun h => by split_ifs <;> norm_num
  rating := fun h => if h = .deceived then 1 else 1 / 2
  rating_range := fun h => by split_ifs <;> norm_num
  voidValue := fun _ => -1 / 2
  voidValue_range := fun _ => by norm_num

/-- No history is violated. -/
def count : Hist → ℕ := fun _ => 0

theorem legit_clean : gate.Legit .clean :=
  ⟨⟨by simp [gate], by simp [gate]⟩, by simp [gate], by simp [gate]⟩

theorem legit_helped : gate.Legit .helped :=
  ⟨⟨by simp [gate], by simp [gate]⟩, by simp [gate], by simp [gate]⟩

/-- **Claim (1)'s package is inhabited**: the three ranges hold of a legitimate history and
of one that is not. -/
theorem theorem1_instance :
    gate.Legit .clean ∧ ¬ gate.Legit .deceived ∧
      (0 ≤ (gate.scoring count).S .clean ∧ (gate.scoring count).S .clean ≤ 1) ∧
      (-gate.δ ≤ (gate.scoring count).S .deceived ∧ (gate.scoring count).S .deceived < 0) :=
  ⟨legit_clean, gate.gained_not_legit rfl,
    (gate.theorem1_join count .clean).2.2 ⟨rfl, legit_clean⟩,
    (gate.theorem1_join count .deceived).2.1 ⟨rfl, gate.gained_not_legit rfl⟩⟩

/-- **Claim (3)'s package is inhabited**, by a history on which the adviser gained and which
has the highest rating: it scores below a legitimate violation-free history of lower
rating. -/
theorem gained_below_legit_instance :
    gate.Gained .deceived ∧ gate.rating .clean < gate.rating .deceived ∧
      gate.Legit .clean ∧ count .clean = 0 ∧
      (gate.scoring count).S .deceived < (gate.scoring count).S .clean :=
  ⟨rfl, by simp [gate]; norm_num, legit_clean, rfl,
    (gate.gained_below_legit count rfl legit_clean rfl).1⟩

/-- **Claim (4)'s package is inhabited**, by two distinct legitimate histories with one
rating. -/
theorem V_eq_of_rating_eq_instance :
    Hist.clean ≠ Hist.helped ∧ gate.Legit .clean ∧ gate.Legit .helped ∧
      gate.rating .clean = gate.rating .helped ∧
      (gate.scoring count).V .clean = (gate.scoring count).V .helped :=
  ⟨by decide, legit_clean, legit_helped, by simp [gate],
    gate.V_eq_of_rating_eq count legit_clean legit_helped (by simp [gate])⟩

/-- **Claim (5)'s package is inhabited**. -/
theorem not_infoSufficient_instance :
    ¬ gate.InfoSufficient .uninformed ∧ ¬ gate.Legit .uninformed ∧
      (gate.scoring count).V .uninformed < 0 :=
  ⟨by simp [gate], gate.not_legit_of_not_infoSufficient (by simp [gate]),
    (gate.V_neg_of_not_infoSufficient count (by simp [gate])).2⟩

/-- **`Gate.bypass_below_V`'s package is inhabited**, at the history on which the adviser
gained. -/
theorem bypass_below_V_instance :
    (1 : ℝ) ≤ 1 ∧
      Workspace.Deference.Contrib.ProtectedAuthorityTheorem.score gate.lam 1 1
        < gate.V .deceived :=
  ⟨le_rfl, gate.bypass_below_V 1 le_rfl .deceived⟩

/-- The clean history at every decision, one action, estimated at the rating. -/
noncomputable def seq : Sequential Unit :=
  gate.sequential count (fun _ => Hist.clean) (fun _ _ => True) (fun _ _ => 1 / 2)
    (fun _ => ()) (fun _ => ()) (fun _ => trivial)
    (fun _ => by constructor <;> norm_num [gate])

theorem seq_S (k : ℕ) : seq.S k = 1 / 2 := by
  show (gate.scoring count).S Hist.clean = 1 / 2
  rw [gate.S_of_legit count legit_clean rfl]
  simp [gate]

theorem seq_maximizes : seq.Maximizes := fun _ _ _ => le_refl _

theorem seq_unbiased : seq.UnbiasedFromFeedback := by
  intro γ hγ
  refine ⟨0, fun K _ => ?_⟩
  have e : seq.excess seq.a K = 0 := by
    unfold Sequential.excess
    rw [Finset.sum_eq_zero fun k _ => ?_, zero_div]
    rw [seq_S k]
    show (1 / 2 : ℝ) - 1 / 2 = 0
    norm_num
  rw [e]
  exact hγ.le

/-- **Theorem 3's package is inhabited at the pair**; its conclusions hold on the
instance. -/
theorem theorem3_instance :
    seq.Maximizes ∧ seq.UnbiasedFromFeedback ∧ LimsupLE seq.R seq.τ ∧
      ∀ a' : ℕ → Unit, (∀ k, seq.avail k (a' k)) → LimsupLE (seq.excess a') 0 :=
  ⟨seq_maximizes, seq_unbiased,
    gate.theorem3_join count (fun _ => Hist.clean) (fun _ _ => True) (fun _ _ => 1 / 2)
      (fun _ => ()) (fun _ => ()) (fun _ => trivial)
      (fun _ => by constructor <;> norm_num [gate]) seq_maximizes seq_unbiased⟩

/-! ### Sufficiency as `ThinLegitimacy.Sufficient` -/

open Workspace.Deference.Contrib.ThinLegitimacy (Sufficient Correct Value) in
/-- **`value_of_legit`'s package is inhabited**, on `ThinLegitimacy`'s own witness: every
history carries the revealing record, her earlier record and the baseline blank. -/
theorem value_of_legit_instance :
    (∀ h : Hist, gate.InfoSufficient h →
        Sufficient (fun _ : Fin 2 => ()) ThinLegitimacy.Witness.reveal
          ThinLegitimacy.Witness.blank) ∧
      gate.Legit .clean ∧
      Correct ThinLegitimacy.Witness.π₂ ThinLegitimacy.Witness.reveal
        ThinLegitimacy.Witness.pointMass ∧
      Value ThinLegitimacy.Witness.π₂ (fun _ : Fin 2 => ()) ThinLegitimacy.Witness.reveal
        ThinLegitimacy.Witness.pointMass ThinLegitimacy.Witness.blank :=
  ⟨fun _ _ => ThinLegitimacy.Witness.thin_inhabited.2.1, legit_clean,
    ThinLegitimacy.Witness.thin_inhabited.1,
    value_of_legit gate ThinLegitimacy.Witness.π₂ ThinLegitimacy.Witness.π₂_nonneg
      (fun _ _ => ()) (fun _ => ThinLegitimacy.Witness.reveal)
      (fun _ => ThinLegitimacy.Witness.blank) (fun _ => ThinLegitimacy.Witness.pointMass)
      (fun _ _ => ThinLegitimacy.Witness.thin_inhabited.2.1) legit_clean
      ThinLegitimacy.Witness.thin_inhabited.1⟩

/-! ### The feedback hypothesis -/

/-- One action, never a violation, estimated at `est`, evaluated at `ev`. -/
noncomputable def flat (est ev : ℝ) (hev : ev ≤ 1) (hest : -1 ≤ est ∧ est ≤ 1) :
    Sequential Unit where
  δ := 1
  lam := 3
  δ_pos := by norm_num
  lam_gt := by norm_num
  V := fun _ => ev
  N := fun _ => 0
  V_le_one := fun _ => hev
  avail := fun _ _ => True
  U := fun _ _ => est
  a := fun _ => ()
  astar := fun _ => ()
  astar_avail := fun _ => trivial
  astar_range := fun _ => hest

theorem flat_excess (est ev : ℝ) (hev : ev ≤ 1) (hest : -1 ≤ est ∧ est ≤ 1) (K : ℕ)
    (hK : 0 < K) : (flat est ev hev hest).excess (flat est ev hev hest).a K = est - ev := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold Sequential.excess Sequential.S
  show (∑ _k ∈ Finset.range K, (est - (ev - 3 * ((0 : ℕ) : ℝ)))) / (K : ℝ) = est - ev
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

theorem flat_feedback (est ev F : ℝ) (hev : ev ≤ 1) (hest : -1 ≤ est ∧ est ≤ 1) (K : ℕ)
    (hK : 0 < K) :
    (∑ k ∈ Finset.range K, ((flat est ev hev hest).U k ((flat est ev hev hest).a k)
      - (F - (flat est ev hev hest).lam * ((flat est ev hev hest).N k : ℝ)))) / (K : ℝ)
      = est - F := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  show (∑ _k ∈ Finset.range K, (est - (F - 3 * ((0 : ℕ) : ℝ)))) / (K : ℝ) = est - F
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-- **`unbiased_of_feedback`'s package is inhabited**: estimates, feedback and evaluation
all `1/2`. -/
theorem unbiased_of_feedback_instance :
    (∀ γ > 0, ∃ N₀, ∀ K ≥ N₀,
        (∑ k ∈ Finset.range K,
          ((flat (1 / 2) (1 / 2) (by norm_num) (by norm_num)).U k
              ((flat (1 / 2) (1 / 2) (by norm_num) (by norm_num)).a k)
            - ((1 / 2 : ℝ) - (flat (1 / 2) (1 / 2) (by norm_num) (by norm_num)).lam
              * ((flat (1 / 2) (1 / 2) (by norm_num) (by norm_num)).N k : ℝ)))) / (K : ℝ)
          ≤ γ) ∧
      LimsupLE (fun K => (∑ k ∈ Finset.range K,
        ((1 / 2 : ℝ) - (flat (1 / 2) (1 / 2) (by norm_num) (by norm_num)).V k)) / (K : ℝ)) 0 ∧
      (flat (1 / 2) (1 / 2) (by norm_num) (by norm_num)).UnbiasedFromFeedback := by
  have hF : ∀ γ > 0, ∃ N₀, ∀ K ≥ N₀,
      (∑ k ∈ Finset.range K,
        ((flat (1 / 2) (1 / 2) (by norm_num) (by norm_num)).U k
            ((flat (1 / 2) (1 / 2) (by norm_num) (by norm_num)).a k)
          - ((1 / 2 : ℝ) - (flat (1 / 2) (1 / 2) (by norm_num) (by norm_num)).lam
            * ((flat (1 / 2) (1 / 2) (by norm_num) (by norm_num)).N k : ℝ)))) / (K : ℝ)
        ≤ γ := by
    intro γ hγ
    refine ⟨1, fun K hK => ?_⟩
    rw [flat_feedback (1 / 2) (1 / 2) (1 / 2) (by norm_num) (by norm_num) K hK]
    linarith
  have hgap : LimsupLE (fun K => (∑ k ∈ Finset.range K,
      ((1 / 2 : ℝ) - (flat (1 / 2) (1 / 2) (by norm_num) (by norm_num)).V k)) / (K : ℝ)) 0 := by
    intro γ hγ
    refine ⟨0, fun K _ => ?_⟩
    show (∑ _k ∈ Finset.range K, ((1 / 2 : ℝ) - 1 / 2)) / (K : ℝ) ≤ 0 + γ
    rw [sub_self, Finset.sum_const_zero, zero_div]
    linarith
  exact ⟨hF, hgap, unbiased_of_feedback _ _ hF hgap⟩

/-- **The second condition of `unbiased_of_feedback` is needed.**  Estimates `1`, feedback
`1`, evaluation `0`: the estimates are unbiased against the feedback, and the post's
hypothesis fails for the evaluation. -/
theorem feedback_not_enough :
    (∀ γ > 0, ∃ N₀, ∀ K ≥ N₀,
        (∑ k ∈ Finset.range K,
          ((flat 1 0 (by norm_num) (by norm_num)).U k
              ((flat 1 0 (by norm_num) (by norm_num)).a k)
            - ((1 : ℝ) - (flat 1 0 (by norm_num) (by norm_num)).lam
              * ((flat 1 0 (by norm_num) (by norm_num)).N k : ℝ)))) / (K : ℝ) ≤ γ) ∧
      ¬ (flat 1 0 (by norm_num) (by norm_num)).UnbiasedFromFeedback := by
  refine ⟨fun γ hγ => ⟨1, fun K hK => ?_⟩, fun h => ?_⟩
  · rw [flat_feedback 1 0 1 (by norm_num) (by norm_num) K hK]
    linarith
  · obtain ⟨N₀, hN₀⟩ := h (1 / 2) (by norm_num)
    have h1 := hN₀ (N₀ + 1) (Nat.le_succ N₀)
    rw [flat_excess 1 0 (by norm_num) (by norm_num) (N₀ + 1) (Nat.succ_pos N₀)] at h1
    norm_num at h1

/-! ### The sound signal and the guarantee -/

/-- Two equally weighted worlds. -/
noncomputable def μ₂ : Bool → ℝ := fun _ => 1 / 2

theorem μ₂_nonneg : ∀ x, 0 ≤ μ₂ x := fun _ => by
  unfold μ₂
  norm_num

theorem μ₂_sum : ∑ x, μ₂ x = 1 := by
  rw [Fintype.sum_bool]
  unfold μ₂
  norm_num

/-- The true utility: `1` in one world, `0` in the other. -/
noncomputable def T : Bool → ℝ := fun x => if x then 1 else 0

/-- **Claim (2)'s package is inhabited**, by a verdict that separates the worlds where the
adviser's information does not; its conclusions hold on the instance. -/
theorem deferring_cost_instance :
    (∀ x, 0 ≤ μ₂ x) ∧
      expectR μ₂ (fun x => (T x - T x) ^ 2)
        ≤ expectR μ₂ (fun x => (condExp μ₂ (fun _ : Bool => ()) T x - T x) ^ 2)
          + miscalibrationGiven μ₂ (fun _ : Bool => ()) T T ∧
      miscalibrationGiven μ₂ (fun _ : Bool => ()) T T = 0 := by
  refine ⟨μ₂_nonneg, deferring_cost_le μ₂ μ₂_nonneg _ T T, ?_⟩
  unfold miscalibrationGiven
  have hz : ∀ x, (T x - condExp μ₂ (fun x => ((), T x)) T x) ^ 2 = 0 := fun x => by
    have hinj : ∀ x', ((), T x') = ((), T x) → x' = x := fun x' h => by
      have h2 : T x' = T x := congrArg Prod.snd h
      cases x' <;> cases x
      · rfl
      · exfalso
        norm_num [T] at h2
      · exfalso
        norm_num [T] at h2
      · rfl
    rw [condExp_of_cell_singleton μ₂ _ T x (by norm_num [μ₂]) hinj, sub_self]
    norm_num
  simp [expectR, hz]

/-- One history carrying the two worlds: the adviser knows nothing, her verdict is her true
utility, the bound is zero. -/
noncomputable def model : SoundModel Unit Bool Unit where
  δ := 1
  lam := 3
  δ_pos := by norm_num
  lam_gt := by norm_num
  μ := fun _ => μ₂
  μ_nonneg := fun _ => μ₂_nonneg
  k := fun _ _ => ()
  verdict := fun _ => T
  verdict_range := fun _ x => by cases x <;> norm_num [T]
  U := fun _ => T
  point := fun _ => true
  m := 0
  InfoSufficient := fun _ => True
  Gained := fun _ => False
  line3 := fun _ => 0
  line3_nonneg := fun _ => le_refl _
  voidValue := fun _ => -1 / 2
  voidValue_range := fun _ => by norm_num

theorem model_legit : model.gate.Legit () :=
  ⟨⟨le_of_eq deferring_cost_instance.2.2, trivial⟩, fun h => h, rfl⟩

/-- **`SoundModel.deferring_cost_of_legit`'s package is inhabited**; its conclusion holds on
the instance, and the evaluation there is her verdict at the realised point. -/
theorem model_instance :
    model.gate.Legit () ∧
      expectR (model.μ ()) (fun x => (model.verdict () x - model.U () x) ^ 2)
        ≤ expectR (model.μ ())
            (fun x => (condExp (model.μ ()) (model.k ()) (model.U ()) x - model.U () x) ^ 2)
          + model.m ∧
      (model.gate.scoring (fun _ => 0)).V () = model.verdict () (model.point ()) :=
  ⟨model_legit, model.deferring_cost_of_legit model_legit,
    model.V_of_legit (fun _ => 0) model_legit⟩

/-- Two moves; a move pays `1` in the world it names. -/
noncomputable def Ud : Bool → Bool → ℝ := fun a x => if a = x then 1 else 0

theorem Ud_given_zero (a : Bool) :
    miscalibrationGiven μ₂ (fun x : Bool => x) (fun x => Ud a x) (Ud a) ≤ 0 := by
  unfold miscalibrationGiven
  have hz : ∀ x, (Ud a x - condExp μ₂ (fun x => (x, Ud a x)) (Ud a) x) ^ 2 = 0 := fun x => by
    rw [condExp_of_cell_singleton μ₂ _ (Ud a) x (by norm_num [μ₂])
      (fun x' h => congrArg Prod.fst h), sub_self]
    norm_num
  simp [expectR, hz]

/-- **`guarantee_of_sound`'s package is inhabited**: she observes the world, the adviser
does too, her valuations are the true utilities, the reference is her own space; its
conclusion holds on the instance. -/
theorem guarantee_of_sound_instance :
    (∀ x, 0 ≤ μ₂ x) ∧ ∑ x, μ₂ x = 1 ∧
      (∀ (a : Bool) (x x' : Bool), x = x' → Ud a x = Ud a x' → x = x') ∧
      (∀ a, miscalibrationGiven μ₂ (fun x : Bool => x) (fun x => Ud a x) (Ud a) ≤ 0) ∧
      (∀ b : Bool, ∃ a : Bool, expectR μ₂ (Ud b) ≤ expectR μ₂ (Ud a)) ∧
      ∀ b : Bool, expectR μ₂ (Ud b) - expectR μ₂ (regret Ud (fun x => x) (fun s => s))
          - Real.sqrt (2 * ((Fintype.card Bool : ℝ) * 0))
        ≤ expectR μ₂ (fun x => Ud x x) :=
  ⟨μ₂_nonneg, μ₂_sum, fun _ _ _ h _ => h, Ud_given_zero, fun b => ⟨b, le_rfl⟩,
    guarantee_of_sound μ₂ μ₂_nonneg μ₂_sum Ud (fun x => x) (fun s => s) Ud (fun x => x)
      (fun _ _ _ h _ => h) 0 Ud_given_zero μ₂ Ud fun b => ⟨b, le_rfl⟩⟩

/-- True utilities for the instance without the link: move `false` pays `3/5` or `2/5` with
the world, move `true` pays `9/10` or `1/10`. -/
noncomputable def Uc : Bool → Bool → ℝ := fun a x =>
  if a then (if x then 9 / 10 else 1 / 10) else (if x then 3 / 5 else 2 / 5)

/-- Her valuations: move `false` at its true utility, move `true` at its mean `1/2`. -/
noncomputable def uhatc : Bool → Bool → ℝ := fun a s =>
  if a then 1 / 2 else (if s then 3 / 5 else 2 / 5)

/-- She takes the move she values more. -/
def cc : Bool → Bool := fun s => !s

theorem link_given_zero (a : Bool) :
    miscalibrationGiven μ₂ (fun _ : Bool => ()) (fun x => uhatc a x) (Uc a) = 0 := by
  unfold miscalibrationGiven
  have hz : ∀ x, (uhatc a x - condExp μ₂ (fun x => ((), uhatc a x)) (Uc a) x) ^ 2 = 0 := by
    intro x
    cases a
    · have hinj : ∀ x', ((), uhatc false x') = ((), uhatc false x) → x' = x := fun x' h => by
        have h2 : uhatc false x' = uhatc false x := congrArg Prod.snd h
        cases x' <;> cases x
        · rfl
        · exfalso
          norm_num [uhatc] at h2
        · exfalso
          norm_num [uhatc] at h2
        · rfl
      rw [condExp_of_cell_singleton μ₂ _ (Uc false) x (by norm_num [μ₂]) hinj]
      cases x <;> norm_num [uhatc, Uc]
    · rw [condExp_of_cell_univ μ₂ _ (Uc true) x (fun x' => by simp [uhatc])]
      norm_num [expectR, μ₂, Uc, uhatc, Fintype.sum_bool]
  simp [expectR, hz]

theorem link_regret_zero (x : Bool) : regret uhatc (fun x => x) cc x = 0 := by
  unfold regret
  refine sub_eq_zero.2 (le_antisymm (Finset.sup'_le _ _ fun a _ => ?_)
    (Finset.le_sup' (fun a => uhatc a x) (Finset.mem_univ (cc x))))
  cases a <;> cases x <;> norm_num [uhatc, cc]

/-- **The link hypothesis of `guarantee_of_given` is needed.**  The adviser knows nothing
and she observes the world.  Each of her valuations is calibrated given the adviser's
information and itself; she takes the move she values more; and she attains `7/20` where
the move `true` is worth `1/2`. -/
theorem link_needed :
    (∀ a, miscalibrationGiven μ₂ (fun _ : Bool => ()) (fun x => uhatc a x) (Uc a) = 0) ∧
      (∀ x, regret uhatc (fun x => x) cc x = 0) ∧
      expectR μ₂ (fun x => Uc (cc x) x) = 7 / 20 ∧ expectR μ₂ (Uc true) = 1 / 2 :=
  ⟨link_given_zero, link_regret_zero,
    by norm_num [expectR, μ₂, Uc, cc, Fintype.sum_bool],
    by norm_num [expectR, μ₂, Uc, Fintype.sum_bool]⟩

/-! ### Line 3 -/

/-- Three policies: the baseline, the policy followed, and one making part of its change. -/
inductive Pol
  | base
  | whole
  | part
  deriving DecidableEq, Fintype

/-- Her later rating of two futures, indexed by `Bool`.  The policy followed raises both;
the partial policy raises the first only. -/
noncomputable def laterRating : Pol → Unit → Bool → ℝ := fun p _ i =>
  match p, i with
  | .base, _ => 1 / 2
  | .whole, _ => 1
  | .part, true => 1
  | .part, false => 1 / 2

/-- Her informed ratings: the whole change above the baseline, the part above the whole. -/
noncomputable def informed : Pol → ℝ := fun p =>
  match p with
  | .base => 1 / 2
  | .whole => 3 / 5
  | .part => 4 / 5

/-- **An unwelcome change with a separable welcome one.**  Tolerance `1/10`. -/
noncomputable def separable : ValueChange Pol Unit Bool where
  followed := .whole
  baseline := .base
  later := laterRating
  tol := 1 / 10
  tol_nonneg := by norm_num
  R := informed

theorem separable_noMore_part : separable.NoMore .part := fun _ i => by
  cases i <;> norm_num [separable, laterRating]

theorem separable_best_noMore :
    separable.bestOn separable.NoMore ⟨.whole, separable.noMore_followed⟩ = 4 / 5 :=
  le_antisymm
    (separable.bestOn_le _ fun p _ => by cases p <;> norm_num [separable, informed])
    (separable.le_bestOn _ separable_noMore_part)

theorem separable_best_whole :
    separable.bestOn (separable.Within .whole) ⟨.whole, separable.within_self _⟩ = 3 / 5 := by
  refine le_antisymm (separable.bestOn_le _ fun p hp => ?_)
    (separable.le_bestOn (p := Pol.whole) _ (separable.within_self _))
  cases p
  · exfalso
    have h := abs_le.1 (hp () true)
    norm_num [separable, laterRating] at h
  · norm_num [separable, informed]
  · exfalso
    have h := abs_le.1 (hp () false)
    norm_num [separable, laterRating] at h

theorem separable_best_base :
    separable.bestOn (separable.Within .base) ⟨.base, separable.within_self _⟩ = 1 / 2 := by
  refine le_antisymm (separable.bestOn_le _ fun p hp => ?_)
    (separable.le_bestOn (p := Pol.base) _ (separable.within_self _))
  cases p
  · norm_num [separable, informed]
  · exfalso
    have h := abs_le.1 (hp () true)
    norm_num [separable, laterRating] at h
  · exfalso
    have h := abs_le.1 (hp () true)
    norm_num [separable, laterRating] at h

/-- **Claim (6)'s instance.**  On `separable`, line 3 is `1/5` and the older form is
`−1/10`. -/
theorem separable_line3 : separable.line3 = 1 / 5 ∧ separable.line3Old = -1 / 10 := by
  constructor
  · show separable.bestOn separable.NoMore _ - separable.bestOn (separable.Within .whole) _
      = 1 / 5
    rw [separable_best_noMore, separable_best_whole]
    norm_num
  · show separable.bestOn (separable.Within .base) _
      - separable.bestOn (separable.Within .whole) _ = -1 / 10
    rw [separable_best_base, separable_best_whole]
    norm_num

/-- The same policies with the baseline followed. -/
noncomputable def idle : ValueChange Pol Unit Bool where
  followed := .base
  baseline := .base
  later := laterRating
  tol := 1 / 10
  tol_nonneg := by norm_num
  R := informed

/-- **Claim (6)'s packages are inhabited**: non-negativity and the comparison on
`separable`, the zero on `idle`. -/
theorem line3_instance :
    0 ≤ separable.line3 ∧ separable.line3Old ≤ separable.line3 ∧
      idle.followed = idle.baseline ∧ idle.line3 = 0 :=
  ⟨separable.line3_nonneg, separable.line3Old_le_line3, rfl, idle.line3_eq_zero_of_eq rfl⟩

end Witness

end Workspace.Deference.Contrib.AccountJoin

#print axioms Workspace.Deference.Contrib.AccountJoin.Gate
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.Legit
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.V
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.V_of_legit
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.V_of_not_legit
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.legit_iff_line3_le
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.scoring
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.theorem1_join
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.S_of_legit
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.S_neg_of_not_legit
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.gained_not_legit
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.gained_below_legit
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.violated_below_violationFree
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.V_eq_of_rating_eq
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.not_legit_of_not_infoSufficient
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.V_neg_of_not_infoSufficient
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.sequential
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.sequential_S
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.theorem3_join
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.V_eq_gateValue
#print axioms Workspace.Deference.Contrib.AccountJoin.Gate.bypass_below_V
#print axioms Workspace.Deference.Contrib.AccountJoin.value_of_legit
#print axioms Workspace.Deference.Contrib.AccountJoin.unbiased_of_feedback
#print axioms Workspace.Deference.Contrib.AccountJoin.miscalibrationGiven
#print axioms Workspace.Deference.Contrib.AccountJoin.miscalibrationGiven_nonneg
#print axioms Workspace.Deference.Contrib.AccountJoin.miscalibrationGiven_eq
#print axioms Workspace.Deference.Contrib.AccountJoin.deferring_cost_eq
#print axioms Workspace.Deference.Contrib.AccountJoin.deferring_cost_le
#print axioms Workspace.Deference.Contrib.AccountJoin.deferring_cost_eq_iff
#print axioms Workspace.Deference.Contrib.AccountJoin.deferring_cost_eq_iff_pointwise
#print axioms Workspace.Deference.Contrib.AccountJoin.deferring_cost_le_of_calibrated
#print axioms Workspace.Deference.Contrib.AccountJoin.deferring_cost_le_of_bound
#print axioms Workspace.Deference.Contrib.AccountJoin.SoundModel
#print axioms Workspace.Deference.Contrib.AccountJoin.SoundModel.Sound
#print axioms Workspace.Deference.Contrib.AccountJoin.SoundModel.gate
#print axioms Workspace.Deference.Contrib.AccountJoin.SoundModel.deferring_cost_of_legit
#print axioms Workspace.Deference.Contrib.AccountJoin.SoundModel.V_of_legit
#print axioms Workspace.Deference.Contrib.AccountJoin.sq_dist_condExp_le_of_factors
#print axioms Workspace.Deference.Contrib.AccountJoin.valuationError_le_given
#print axioms Workspace.Deference.Contrib.AccountJoin.guarantee_of_given
#print axioms Workspace.Deference.Contrib.AccountJoin.guarantee_of_sound
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.Within
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.NoMore
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.within_self
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.noMore_of_within_followed
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.noMore_of_within_baseline
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.noMore_followed
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.bestOn
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.le_bestOn
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.bestOn_le
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.bestOn_mono
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.line3
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.line3Old
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.line3_nonneg
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.line3_eq_zero
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.line3_eq_zero_of_eq
#print axioms Workspace.Deference.Contrib.AccountJoin.ValueChange.line3Old_le_line3
#print axioms Workspace.Deference.Contrib.AccountJoin.condExp_of_cell_singleton
#print axioms Workspace.Deference.Contrib.AccountJoin.condExp_of_cell_univ
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.Hist
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.gate
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.count
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.legit_clean
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.legit_helped
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.theorem1_instance
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.gained_below_legit_instance
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.V_eq_of_rating_eq_instance
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.not_infoSufficient_instance
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.bypass_below_V_instance
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.seq
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.seq_S
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.seq_maximizes
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.seq_unbiased
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.theorem3_instance
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.value_of_legit_instance
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.flat
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.flat_excess
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.flat_feedback
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.unbiased_of_feedback_instance
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.feedback_not_enough
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.μ₂
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.μ₂_nonneg
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.μ₂_sum
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.T
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.deferring_cost_instance
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.model
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.model_legit
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.model_instance
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.Ud
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.Ud_given_zero
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.guarantee_of_sound_instance
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.Uc
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.uhatc
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.cc
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.link_given_zero
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.link_regret_zero
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.link_needed
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.Pol
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.laterRating
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.informed
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.separable
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.separable_noMore_part
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.separable_best_noMore
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.separable_best_whole
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.separable_best_base
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.separable_line3
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.idle
#print axioms Workspace.Deference.Contrib.AccountJoin.Witness.line3_instance
