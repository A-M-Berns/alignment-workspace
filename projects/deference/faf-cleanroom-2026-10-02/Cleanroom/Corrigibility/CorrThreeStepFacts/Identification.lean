import Cleanroom.Corrigibility.CorrThreeStepFacts.StopWorld
import Mathlib.Tactic.LinearCombination

/-!
# T5–T6: non-identification from the compliance record; proportional versus targeted suppression

* **T5** (Prop. 15.1): the compliance record is the pair of silent cells
  `rec ε α β = ((1 − ε)(1 − α), ε(1 − β))`; every `ε ∈ [B, 1 − A]` lifts to a sensor reproducing
  a given record (`record_fibre`), and along that fibre the D1-relevant conditional
  `P(W | Pr) = (ε − B)/(1 − A − B)` sweeps all of `[0, 1]` (`fibre_posterior`,
  `record_nonidentification`). Model M's press *rate* is likewise one number for three
  parameters (`pressRate_fibre`).
* **T6** (R7): scaling the sensor by `λ > 0` leaves the below-threshold inequality, the press
  posterior and D1 unchanged (`belowThresholdIneq_scaled_iff`, `posteriorPress_scaled`,
  `d1At_scaled_iff`) while the silence posterior rises (`silentPosterior_strictAnti`); targeted
  suppression (lowering `β` alone) breaks D1 (`WitnessesB`); the total-expectation theorem
  (`pressMass_eq_or_condExp_eq`): an `a₁`-blind conditional model with a varying press mass
  forces an inert channel; the mixed sensor `(1 − d)·press + d·k` has `Δ₋` affine and
  non-increasing in `d` (`mixed_deltaMinus`, `mixed_deltaMinus_antitone`).

Sources: `miri.md` Prop. 15.1 (I15.1); `filler.md` R4.4, R7; `cirl.md` S8(b) (Model M);
`selection.md` R2.2(iii).
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

/-! ## T5 — the compliance record -/

/-- **The compliance record**: the two observable silent cells `A = P(¬Pr, R) = (1 − ε)(1 − α)`
and `B = P(¬Pr, W) = ε(1 − β)`; the press mass `C = P(Pr) = 1 − A − B` is not a third number.
Source: [[corr-wf13-inventory]] 007 / miri.md I15.1; [[corr-wf14-inventory]] 009 / filler.md R4.4
Kind: D
Fidelity: exact -/
noncomputable def record (ε α β : ℝ) : ℝ × ℝ := ((1 - ε) * (1 - α), ε * (1 - β))

/-- The false-press rate on the fibre over `(A, ·)` at `ε`: `1 − A/(1 − ε)`.
Source: miri.md Prop. 15.1 (proof). Kind: D. Fidelity: exact -/
noncomputable def fibreAlpha (A ε : ℝ) : ℝ := 1 - A / (1 - ε)

/-- The true-press rate on the fibre over `(·, B)` at `ε`: `1 − B/ε`.
Source: miri.md Prop. 15.1 (proof). Kind: D. Fidelity: exact -/
noncomputable def fibreBeta (B ε : ℝ) : ℝ := 1 - B / ε

/-- The fibre's false-press rate lies in `[0, 1]` when `0 ≤ A`, `ε < 1`, `ε ≤ 1 − A`.
Source: miri.md Prop. 15.1 (proof: "both in `[0, 1]`"). Kind: L. Fidelity: exact -/
lemma fibreAlpha_mem {A ε : ℝ} (hA : 0 ≤ A) (hε1 : ε < 1) (hεA : ε ≤ 1 - A) :
    fibreAlpha A ε ∈ Set.Icc (0 : ℝ) 1 := by
  unfold fibreAlpha
  have h1 : 0 < 1 - ε := by linarith
  constructor
  · rw [sub_nonneg, div_le_one h1]; linarith
  · linarith [div_nonneg hA h1.le]

/-- The fibre's true-press rate lies in `[0, 1]` when `0 ≤ B`, `0 < ε`, `B ≤ ε`.
Source: miri.md Prop. 15.1 (proof). Kind: L. Fidelity: exact -/
lemma fibreBeta_mem {B ε : ℝ} (hB : 0 ≤ B) (hε0 : 0 < ε) (hεB : B ≤ ε) :
    fibreBeta B ε ∈ Set.Icc (0 : ℝ) 1 := by
  unfold fibreBeta
  constructor
  · rw [sub_nonneg, div_le_one hε0]; exact hεB
  · linarith [div_nonneg hB hε0.le]

/-- **T5(i), the fibre reproduces the record.** For `0 < ε < 1`,
`rec ε (fibreAlpha A ε) (fibreBeta B ε) = (A, B)`.
Source: [[corr-wf13-inventory]] 007 / miri.md Prop. 15.1 ("reproducing `(A, B, C)`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem record_fibre (A B ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    record ε (fibreAlpha A ε) (fibreBeta B ε) = (A, B) := by
  unfold record fibreAlpha fibreBeta
  have h1 : (1 - ε) ≠ 0 := by linarith
  have h2 : ε ≠ 0 := hε0.ne'
  ext <;> simp only
  · rw [sub_sub_cancel, mul_div_cancel₀ _ h1]
  · rw [sub_sub_cancel, mul_div_cancel₀ _ h2]

/-- **T5(ii), the posterior along the fibre.** On the fibre over `(A, B)` at `ε`, the
D1-relevant conditional is `P(W | Pr) = (ε − B)/(1 − A − B)`.
Source: [[corr-wf13-inventory]] 007 / miri.md Prop. 15.1 (`P(W | Pr) = (ε − B)/C`)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem fibre_posterior (A B ε c h : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hε hα hβ) :
    (twoState ε (fibreAlpha A ε) (fibreBeta B ε) c h hε hα hβ).posteriorPress () .wrong =
      (ε - B) / (1 - A - B) := by
  rw [twoState_posteriorPress_wrong]
  unfold fibreAlpha fibreBeta
  have h1 : (1 - ε) ≠ 0 := by linarith
  have h2 : ε ≠ 0 := hε0.ne'
  have e1 : (1 - ε) * (1 - A / (1 - ε)) = 1 - ε - A := by
    rw [mul_sub, mul_one, mul_div_cancel₀ _ h1]
  have e2 : ε * (1 - B / ε) = ε - B := by rw [mul_sub, mul_one, mul_div_cancel₀ _ h2]
  rw [e1, e2]
  congr 1; ring

/-- **T5(ii), the sweep.** For a record with `0 < A`, `0 < B`, `A + B < 1` and any target
`t ∈ [0, 1]` there is a parameter triple reproducing the record whose two-state posterior
`P(W | Pr)` equals `t`: the D1-relevant conditional is completely unidentified by the record.
(Surjectivity onto `[0, 1]`, not two sample points; the endpoints `t = 0`, `t = 1` are attained
at `ε = B` and `ε = 1 − A`, where `0 < A, B` keeps both fibre rates well-defined.)
Source: [[corr-wf13-inventory]] 007 / miri.md Prop. 15.1; [[corr-wf14-inventory]] 009 / filler.md R4.4
Kind: P
Fidelity: exact on the closed interval for `0 < A`, `0 < B` (at `B = 0` the `ε = 0` endpoint has `β` undetermined; at `A = 0` the `ε = 1` endpoint has `α` undetermined: junk excluded by hypothesis)
Hyps: (a) only -/
theorem record_nonidentification (A B c h : ℝ) (hA : 0 < A) (hB : 0 < B) (hAB : A + B < 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ ε α β : ℝ, ∃ (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
      (hβ : β ∈ Set.Icc (0 : ℝ) 1), record ε α β = (A, B) ∧
      (twoState ε α β c h hε hα hβ).posteriorPress () .wrong = t := by
  set C := 1 - A - B with hC
  have hCpos : 0 < C := by rw [hC]; linarith
  set ε := B + t * C with hεdef
  have hε0 : 0 < ε := by rw [hεdef]; nlinarith [ht.1]
  have hεB : B ≤ ε := by rw [hεdef]; nlinarith [ht.1]
  have hεA : ε ≤ 1 - A := by rw [hεdef]; nlinarith [ht.2]
  have hε1 : ε < 1 := by linarith
  refine ⟨ε, fibreAlpha A ε, fibreBeta B ε, ⟨hε0.le, hε1.le⟩, fibreAlpha_mem hA.le hε1 hεA,
    fibreBeta_mem hB.le hε0 hεB, record_fibre A B ε hε0 hε1, ?_⟩
  rw [fibre_posterior A B ε c h hε0 hε1, ← hC, hεdef]
  field_simp
  ring

/-- **T5(iv), Model M.** The press *rate* `p = (1 − ε)α + εβ` is one number for three parameters:
`α' := (p − εβ)/(1 − ε)` reproduces it, and lies in `[0, 1]` exactly when
`εβ ≤ p ≤ εβ + (1 − ε)`.
Source: [[corr-wf13-inventory]] 007 (caution S8b) / cirl.md S8 ("Model M")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem pressRate_fibre (ε β p : ℝ) (hε1 : ε < 1) :
    (1 - ε) * ((p - ε * β) / (1 - ε)) + ε * β = p ∧
      ((p - ε * β) / (1 - ε) ∈ Set.Icc (0 : ℝ) 1 ↔ ε * β ≤ p ∧ p ≤ ε * β + (1 - ε)) := by
  have h1 : 0 < 1 - ε := by linarith
  refine ⟨by rw [mul_div_cancel₀ _ h1.ne']; ring, ?_⟩
  constructor
  · rintro ⟨h0, hle⟩
    rw [div_le_one h1] at hle
    rw [div_nonneg_iff] at h0
    rcases h0 with ⟨h0, _⟩ | ⟨_, h0⟩
    · exact ⟨by linarith, by linarith⟩
    · exact absurd h0 (not_le.mpr h1)
  · rintro ⟨hlo, hhi⟩
    exact ⟨div_nonneg (by linarith) h1.le, by rw [div_le_one h1]; linarith⟩

/-- The press mass of a triple reproducing the record `(A, B)` is `1 − A − B`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressMass_of_record {ε α β A B : ℝ} (hrec : record ε α β = (A, B)) :
    (1 - ε) * α + ε * β = 1 - A - B := by
  unfold record at hrec
  simp only [Prod.mk.injEq] at hrec
  obtain ⟨hr1, hr2⟩ := hrec
  linear_combination -(hr1 + hr2)

/-- **T5(iii), general stakes.** For any stakes `c, h > 0` and any record `(A, B)` with
`0 < A, B`, `A + B < 1`, one triple reproducing the record satisfies desideratum 1 and another
does not: D1 at *any* `h/c` is undecided by the record (the `h/c = 20` pair `w_flip_low` /
`w_flip_high` is the instance). From `record_nonidentification` at `t = 0` and `t = 1`.
Source: miri.md Prop. 15.1; filler.md R4.4; audit r1 (adversarial) N4
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem record_undecides_d1 (A B c h : ℝ) (hA : 0 < A) (hB : 0 < B) (hAB : A + B < 1)
    (hc : 0 < c) (hh : 0 < h) :
    (∃ ε α β : ℝ, ∃ (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
      (hβ : β ∈ Set.Icc (0 : ℝ) 1), record ε α β = (A, B) ∧ (twoState ε α β c h hε hα hβ).D1At ()) ∧
    (∃ ε α β : ℝ, ∃ (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
      (hβ : β ∈ Set.Icc (0 : ℝ) 1), record ε α β = (A, B) ∧ ¬ (twoState ε α β c h hε hα hβ).D1At ()) := by
  have hC : 0 < 1 - A - B := by linarith
  constructor
  · obtain ⟨ε, α, β, hε, hα, hβ, hrec, hpost⟩ :=
      record_nonidentification A B c h hA hB hAB 1 ⟨by norm_num, le_refl _⟩
    refine ⟨ε, α, β, hε, hα, hβ, hrec, ?_⟩
    rw [twoState_d1At_iff]
    rw [twoState_posteriorPress_wrong, pressMass_of_record hrec, div_eq_one_iff_eq hC.ne'] at hpost
    have hpm := pressMass_of_record hrec
    have h0 : (1 - ε) * α = 0 := by linarith
    rw [h0, zero_mul, hpost]
    exact mul_nonneg hC.le hh.le
  · obtain ⟨ε, α, β, hε, hα, hβ, hrec, hpost⟩ :=
      record_nonidentification A B c h hA hB hAB 0 ⟨le_refl _, by norm_num⟩
    refine ⟨ε, α, β, hε, hα, hβ, hrec, ?_⟩
    rw [twoState_d1At_iff]
    rw [twoState_posteriorPress_wrong, pressMass_of_record hrec, div_eq_zero_iff] at hpost
    have hpm := pressMass_of_record hrec
    rcases hpost with h0 | h0
    · rw [h0, zero_mul]
      have : (1 - ε) * α = 1 - A - B := by linarith
      rw [this]
      exact not_le.mpr (mul_pos hC hc)
    · exact absurd h0 hC.ne'

/-! ## T6(i) — scale invariance of the press branch -/

section Scaled

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep Ω A₁ A₂) (a a' : A₁) (l : ℝ)
  (hpress : ∀ ω, S.press a' ω = l * S.press a ω) (hμ : S.μ a' = S.μ a)

include hpress hμ in
/-- Scaling the sensor scales the press-weighted expectation.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsExpect_press_scaled (X : Ω → ℝ) :
    S.obsExpect a' .press X = l * S.obsExpect a .press X := by
  simp only [obsExpect, obsWeight_press, hpress, hμ, mul_sum]
  exact sum_congr rfl fun ω _ => by ring

include hpress hμ in
/-- Scaling the sensor scales the press mass. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressMass_scaled : S.pressMass a' = l * S.pressMass a := by
  simp only [pressMass, hpress, hμ, mul_sum]
  exact sum_congr rfl fun ω _ => by ring

include hpress hμ in
/-- **T6(i), the inequality.** Proportional suppression `press ↦ λ·press` (`λ > 0`, same prior)
leaves the below-threshold inequality unchanged.
Source: [[corr-wf14-inventory]] 010 / filler.md R7 ("proportional suppression leaves `P(W | Pr)` unchanged — D1 survives")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem belowThresholdIneq_scaled_iff (hl : 0 < l) (X : Ω → ℝ) :
    S.belowThresholdIneq a' X ↔ S.belowThresholdIneq a X := by
  unfold belowThresholdIneq
  rw [obsExpect_press_scaled S a a' l hpress hμ]
  constructor
  · intro h; exact nonpos_of_mul_nonpos_right h hl
  · intro h; exact mul_nonpos_of_nonneg_of_nonpos hl.le h

include hpress hμ in
/-- **T6(i), the posterior.** Proportional suppression leaves the press posterior unchanged
(`λ ≠ 0`; both sides junk at press mass zero, equally).
Source: [[corr-wf14-inventory]] 010 / filler.md R7
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem posteriorPress_scaled (hl : l ≠ 0) (ω : Ω) :
    S.posteriorPress a' ω = S.posteriorPress a ω := by
  unfold posteriorPress
  rw [pressMass_scaled S a a' l hpress hμ, hpress, hμ]
  rw [show (S.μ a).mass ω * (l * S.press a ω) = l * ((S.μ a).mass ω * S.press a ω) by ring,
    mul_div_mul_left _ _ hl]

include hpress hμ in
/-- **T6(i), desideratum 1.** Proportional suppression (same prior, same values) leaves D1
unchanged.
Source: [[corr-wf14-inventory]] 010 / filler.md R7
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem d1At_scaled_iff (hl : 0 < l) (hV : S.V a' = S.V a) : S.D1At a' ↔ S.D1At a := by
  unfold D1At PosteriorOptimalAt
  simp only [obsExpect_press_scaled S a a' l hpress hμ, hV]
  constructor
  · rintro ⟨b, hb, hopt⟩
    exact ⟨b, hb, fun b' => le_of_mul_le_mul_left (hopt b') hl⟩
  · rintro ⟨b, hb, hopt⟩
    exact ⟨b, hb, fun b' => mul_le_mul_of_nonneg_left (hopt b') hl.le⟩

end Scaled

/-- The silence posterior of the two-state instance under proportional suppression by `λ`:
`P(W | ¬Pr) = ε(1 − λβ)/(ε(1 − λβ) + (1 − ε)(1 − λα))`.
Source: [[corr-wf14-inventory]] 010 / filler.md R7 ("`P(W | ¬Pr)` rises")
Kind: D
Fidelity: exact -/
noncomputable def silentPosterior (ε α β l : ℝ) : ℝ :=
  ε * (1 - l * β) / (ε * (1 - l * β) + (1 - ε) * (1 - l * α))

/-- **T6(i), the silence side.** For `0 < ε < 1` and `α < β ≤ 1` the silence posterior is
strictly decreasing in the suppression factor on `[0, 1]`: suppressing presses makes silence
*less* reassuring than an `a₁`-blind model believes.
Source: [[corr-wf14-inventory]] 010 / filler.md R7 (`0.0055 → 0.0288`)
Kind: P
Fidelity: stronger: strictly monotone on `(−∞, 1]` where the source has one pair of numbers on `[0, 1]`
Hyps: (a) only -/
theorem silentPosterior_strictAnti (ε α β : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hα0 : 0 ≤ α)
    (hαβ : α < β) (hβ1 : β ≤ 1) {l₁ l₂ : ℝ} (hlt : l₁ < l₂) (h1 : l₂ ≤ 1) :
    silentPosterior ε α β l₂ < silentPosterior ε α β l₁ := by
  unfold silentPosterior
  have hα1 : α < 1 := by linarith
  have d1 : 0 < ε * (1 - l₁ * β) + (1 - ε) * (1 - l₁ * α) := by
    have : 0 ≤ ε * (1 - l₁ * β) := mul_nonneg hε0.le (by nlinarith)
    have : 0 < (1 - ε) * (1 - l₁ * α) := mul_pos (by linarith) (by nlinarith)
    linarith
  have d2 : 0 < ε * (1 - l₂ * β) + (1 - ε) * (1 - l₂ * α) := by
    have : 0 ≤ ε * (1 - l₂ * β) := mul_nonneg hε0.le (by nlinarith)
    have : 0 < (1 - ε) * (1 - l₂ * α) := mul_pos (by linarith) (by nlinarith)
    linarith
  rw [div_lt_div_iff₀ d2 d1]
  have key : ε * (1 - l₂ * β) * (ε * (1 - l₁ * β) + (1 - ε) * (1 - l₁ * α)) -
      ε * (1 - l₁ * β) * (ε * (1 - l₂ * β) + (1 - ε) * (1 - l₂ * α)) =
      ε * (1 - ε) * (l₂ - l₁) * (α - β) := by ring
  have : ε * (1 - ε) * (l₂ - l₁) * (α - β) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (mul_pos hε0 (by linarith)) (by linarith)) (by linarith)
  linarith

/-! ## T6(iii) — the total-expectation theorem -/

section TotalExpectation

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep Ω A₁ A₂)

/-- At positive press mass `E_P[X 1_Pr] = P(Pr) · E_P[X | Pr]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsExpect_press_eq_mul_condExp (a : A₁) (X : Ω → ℝ) (h : 0 < S.pressMass a) :
    S.obsExpect a .press X = S.pressMass a * S.condExpPress a X := by
  rw [condExpPress, mul_div_cancel₀ _ h.ne']

/-- At press mass below one `E_P[X 1_¬Pr] = (1 − P(Pr)) · E_P[X | ¬Pr]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsExpect_silent_eq_mul_condExp (a : A₁) (X : Ω → ℝ) (h : S.pressMass a < 1) :
    S.obsExpect a .silent X = (1 - S.pressMass a) * S.condExpSilent a X := by
  rw [condExpSilent, mul_div_cancel₀ _ (by linarith)]

/-- **T6(iii), the total-expectation theorem.** Two first actions with the same prior, both
nondegenerate, whose press- and silence-conditionals of `X` agree (an `a₁`-blind conditional
model): then either their press masses agree or the channel is inert
(`E[X | Pr] = E[X | ¬Pr]`). An `a₁`-blind model with a *varying* press mass forces an inert
channel — R7's "requiring the same `E_P[X | o; a₁]` for every `a₁` while `p(Pr; a₁)` varies
violates the law of total expectation".
Source: [[corr-wf14-inventory]] 010 / filler.md R7 (last paragraph); thornley §2.1 item 4 (reported there)
Kind: P
Fidelity: exact
Hyps: (a) nondegeneracy names where the conditionals are defined; the equal prior is A0 at the pair -/
theorem pressMass_eq_or_condExp_eq (a a' : A₁) (X : Ω → ℝ) (hμ : S.μ a = S.μ a')
    (hnd : S.Nondegenerate a) (hnd' : S.Nondegenerate a')
    (hP : S.condExpPress a X = S.condExpPress a' X)
    (hS : S.condExpSilent a X = S.condExpSilent a' X) :
    S.pressMass a = S.pressMass a' ∨ S.condExpPress a X = S.condExpSilent a X := by
  have e1 := S.obsExpect_press_add_silent a X
  have e2 := S.obsExpect_press_add_silent a' X
  rw [obsExpect_press_eq_mul_condExp S a X hnd.1, obsExpect_silent_eq_mul_condExp S a X hnd.2] at e1
  rw [obsExpect_press_eq_mul_condExp S a' X hnd'.1, obsExpect_silent_eq_mul_condExp S a' X hnd'.2,
    ← hP, ← hS, ← hμ] at e2
  have : (S.pressMass a - S.pressMass a') * (S.condExpPress a X - S.condExpSilent a X) = 0 := by
    linear_combination e1 - e2
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

end TotalExpectation

/-! ## T6(iv) — the mixed sensor: source-aware deception is dominated -/

/-- The mixed press rate `(1 − d)·x + d·k` stays in `[0, 1]` for `x, k, d ∈ [0, 1]`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mixed_mem {x k d : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hk : k ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) : (1 - d) * x + d * k ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · have := mul_nonneg (by linarith [hd.2] : (0:ℝ) ≤ 1 - d) hx.1
    have := mul_nonneg hd.1 hk.1
    linarith
  · nlinarith [hx.2, hk.2, hd.1, hd.2]

/-- **T6(iv), `Δ₋` of the mixed sensor.** With `press_d = (1 − d)·press + d·k` (`k` a constant
press rate) on the two-state instance, `Δ₋ = (1 − d)·Δ₋(press) − d·k·E_μ[X]`: affine in `d`.
Source: [[corr-wf14-inventory]] 010 / selection.md R2.2(iii) ("value of information falls monotonically … as `d` runs")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem mixed_deltaMinus (ε α β k d c h : ℝ) (hε hα hβ) (hk : k ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    (twoState ε ((1 - d) * α + d * k) ((1 - d) * β + d * k) c h hε (mixed_mem hα hk hd)
        (mixed_mem hβ hk hd)).deltaMinus () .cont .stop =
      (1 - d) * (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop -
        d * k * ((1 - ε) * c - ε * h) := by
  rw [twoState_deltaMinus, twoState_deltaMinus]; ring

/-- **T6(iv), monotonicity.** When desideratum 1 holds (`Δ₋ ≥ 0`) and the prior favours
continuing (`E_μ[X] ≥ 0`), `Δ₋` of the mixed sensor is non-increasing in the mixing weight `d`
(for `k ≥ 0`): a source-aware deceiver only loses button value — dominated.
Source: [[corr-wf14-inventory]] 010 / selection.md R2.2(iii)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem mixed_deltaMinus_antitone (ε α β k c h : ℝ) (hε hα hβ) (hk : k ∈ Set.Icc (0 : ℝ) 1)
    {d₁ d₂ : ℝ} (hd₁ : d₁ ∈ Set.Icc (0 : ℝ) 1) (hd₂ : d₂ ∈ Set.Icc (0 : ℝ) 1) (hle : d₁ ≤ d₂)
    (hD1 : 0 ≤ (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop)
    (hprior : 0 ≤ (1 - ε) * c - ε * h) :
    (twoState ε ((1 - d₂) * α + d₂ * k) ((1 - d₂) * β + d₂ * k) c h hε (mixed_mem hα hk hd₂)
        (mixed_mem hβ hk hd₂)).deltaMinus () .cont .stop ≤
      (twoState ε ((1 - d₁) * α + d₁ * k) ((1 - d₁) * β + d₁ * k) c h hε (mixed_mem hα hk hd₁)
        (mixed_mem hβ hk hd₁)).deltaMinus () .cont .stop := by
  rw [mixed_deltaMinus ε α β k d₁ c h hε hα hβ hk hd₁, mixed_deltaMinus ε α β k d₂ c h hε hα hβ hk hd₂]
  have := mul_nonneg hk.1 hprior
  nlinarith

/-- **T6(iv), the regime at every `d`.** On the mixed instance, when the prior favours continuing
(`E_μ[X] ≥ 0`) and desideratum 1 holds at `d` (`Δ₋ ≥ 0`), the two-option button value is `Δ₋`
itself: `voiButton2 = Δ₋(d)`. So wherever D1 survives along the path, `mixed_deltaMinus_antitone`
is a statement about the *value of information*, which is the source's claim (audit r1 N13).
Source: selection.md R2.2(iii) ("value of information falls monotonically … as `d` runs")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem mixed_voiButton2 (ε α β k d c h : ℝ) (hε hα hβ) (hk : k ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) (hprior : 0 ≤ (1 - ε) * c - ε * h)
    (hD1 : 0 ≤ (twoState ε ((1 - d) * α + d * k) ((1 - d) * β + d * k) c h hε (mixed_mem hα hk hd)
        (mixed_mem hβ hk hd)).deltaMinus () .cont .stop) :
    (twoState ε ((1 - d) * α + d * k) ((1 - d) * β + d * k) c h hε (mixed_mem hα hk hd)
        (mixed_mem hβ hk hd)).voiButton2 () .press .cont .stop =
      (twoState ε ((1 - d) * α + d * k) ((1 - d) * β + d * k) c h hε (mixed_mem hα hk hd)
        (mixed_mem hβ hk hd)).deltaMinus () .cont .stop := by
  rw [voiButton2_eq_max_deltaMinus _ (twoState_A1 _ _ _ _ _ _ _ _) () .press .cont .stop
    (by rw [show (twoState ε ((1 - d) * α + d * k) ((1 - d) * β + d * k) c h hε (mixed_mem hα hk hd)
        (mixed_mem hβ hk hd)).μ () = twoPoint ε hε from rfl, twoState_expect_Xo]; exact hprior)
    (by rw [twoState_deltaPlus]; rw [twoState_deltaMinus] at hD1; nlinarith), max_eq_left hD1]

/-- **T6(iv), the source's instance (`k = 0`).** Mixing toward a *silent* sensor keeps D1 along
the whole path and the button value is `(1 − d)·Δ₋(0)`: the value of information falls linearly
to `0` at `d = 1`.
Source: selection.md R2.2(iii) (the `k = 0` numerics `3/20, 9/80, 3/40, 3/80, 0`)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem mixed_voiButton2_k_zero (ε α β d c h : ℝ) (hε hα hβ) (hd : d ∈ Set.Icc (0 : ℝ) 1)
    (hprior : 0 ≤ (1 - ε) * c - ε * h)
    (hD1 : 0 ≤ (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop) :
    (twoState ε ((1 - d) * α + d * 0) ((1 - d) * β + d * 0) c h hε (mixed_mem hα mem_Icc_zero hd)
        (mixed_mem hβ mem_Icc_zero hd)).voiButton2 () .press .cont .stop =
      (1 - d) * (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop := by
  have hD1d : 0 ≤ (twoState ε ((1 - d) * α + d * 0) ((1 - d) * β + d * 0) c h hε
      (mixed_mem hα mem_Icc_zero hd) (mixed_mem hβ mem_Icc_zero hd)).deltaMinus () .cont .stop := by
    rw [mixed_deltaMinus ε α β 0 d c h hε hα hβ mem_Icc_zero hd]
    have := mul_nonneg (by linarith [hd.2] : (0 : ℝ) ≤ 1 - d) hD1
    linarith
  rw [mixed_voiButton2 ε α β 0 d c h hε hα hβ mem_Icc_zero hd hprior hD1d,
    mixed_deltaMinus ε α β 0 d c h hε hα hβ mem_Icc_zero hd]
  ring

end Cleanroom.Corrigibility.CorrThreeStepFacts
