import Cleanroom.Corrigibility.CorrReflectFrames.Legit
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# corr-reflect-frames — T5: proposition-wise accuracy is strictly weaker than reflection

Radical Theorem I4.2 / Armstrong I4.2(i). (a) Value-form reflection for `φ` implies Brier
accuracy non-decrease for `φ`, via the finite conditional-variance identity
`E[(𝟙_φ − Q)²] = E[𝟙_φ] − E[Q²]` (the content). (b) The `s6` model (`Witnesses.lean`): an
immodest, informative-but-underconfident expert that beats the constant forecast under Brier and
log loss while failing value-form reflection and Total Trust. (c) The recalibration reading is
`valueReflectsOn_iff_ratio` (`Legit.lean`, kind L).

Local scoring definitions only — nothing here is `lit-ddb-accuracy-mm`'s `Rule`/`expInacc`
(not a dependency); names avoid `EpistemicValue`, `IsGsp`.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The Brier (quadratic) loss of forecast `p` against outcome `y`.
Source: [[radical]] Theorem I4.2(b) l. 135
Kind: D
Fidelity: exact -/
def brier (p y : ℝ) : ℝ := (p - y) ^ 2

/-- The logarithmic loss of forecast `p` against outcome `y ∈ {0, 1}`. **Junk value at the
endpoints**: Mathlib's `Real.log 0 = 0`, so a forecast of `0` on a hit (or `1` on a miss) scores
`0` where the proper log loss is `+∞`. Exact on `p ∈ (0, 1)`; the only consumer is the `s6`
instance (forecasts `3/5`, `2/5`), and any general theorem over this definition must carry a
`0 < p < 1` guard or move to an `EReal` codomain (audit r1, adversarial 2).
Source: [[radical]] Theorem I4.2(b) l. 135
Kind: D
Fidelity: exact on `(0, 1)`; junk (`Real.log 0 = 0`) at the endpoints -/
def logLoss (p y : ℝ) : ℝ := -Real.log (if y = 1 then p else 1 - p)

/-- The `π`-expected loss of the expert's forecast `P_w(φ)` of `φ` under a loss `ℓ`.
Source: [[radical]] S3 (Acc_φ) l. 27
Kind: D
Fidelity: exact -/
def expLoss (π : W → ℝ) (F : Frame W) (φ : Finset W) (ℓ : ℝ → ℝ → ℝ) : ℝ :=
  ∑ w, π w * ℓ (mass (F.P w) φ) (ind φ w)

/-- The `π`-expected loss of the constant forecast `π(φ)`.
Source: [[radical]] S3 (Acc_φ) l. 27
Kind: D
Fidelity: exact -/
def constLoss (π : W → ℝ) (φ : Finset W) (ℓ : ℝ → ℝ → ℝ) : ℝ :=
  ∑ w, π w * ℓ (mass π φ) (ind φ w)

/-- A weighted sum grouped by the announced value of `φ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_valCells (π : W → ℝ) (F : Frame W) (φ : Finset W) (g : W → ℝ) :
    ∑ w, π w * g w =
      ∑ c ∈ univ.image (fun w => mass (F.P w) φ), ∑ w ∈ valCell F φ c, π w * g w := by
  have hmaps : ∀ w ∈ (univ : Finset W), mass (F.P w) φ ∈ univ.image (fun w => mass (F.P w) φ) :=
    fun w _ => mem_image_of_mem _ (mem_univ w)
  rw [← sum_fiberwise_of_maps_to hmaps (fun w => π w * g w)]
  apply sum_congr rfl
  intro c _
  apply sum_congr _ (fun _ _ => rfl)
  ext w; simp [mem_valCell]

/-- **The two moments under value-form reflection.** Writing `Q w := P_w(φ)`:
`∑ π w · Q w = π(φ)` and `∑ π w · 𝟙_φ w · Q w = ∑ π w · Q w²`.
Source: [[armstrong]] I4.2(i) l. 121 (`ρ_j(A)` is the conditional expectation of `𝟙_A`)
Kind: L
Fidelity: n/a -/
theorem valueReflectsOn_moments {π : W → ℝ} {F : Frame W} {φ : Finset W}
    (h : ValueReflectsOn π F φ) :
    (∑ w, π w * mass (F.P w) φ = mass π φ) ∧
      (∑ w, π w * (ind φ w * mass (F.P w) φ) = ∑ w, π w * mass (F.P w) φ ^ 2) := by
  constructor
  · rw [sum_valCells π F φ]
    have e : ∀ c ∈ univ.image (fun w => mass (F.P w) φ),
        ∑ w ∈ valCell F φ c, π w * mass (F.P w) φ = mass π (φ ∩ valCell F φ c) := by
      intro c _
      rw [h c]
      show ∑ w ∈ valCell F φ c, π w * mass (F.P w) φ = c * ∑ w ∈ valCell F φ c, π w
      rw [mul_sum]
      apply sum_congr rfl
      intro w hw
      rw [mem_valCell.1 hw]; ring
    rw [sum_congr rfl e, ← mass_eq_sum_valCells]
  · rw [sum_valCells π F φ, sum_valCells π F φ (fun w => mass (F.P w) φ ^ 2)]
    apply sum_congr rfl
    intro c _
    have e0 : ∀ w ∈ valCell F φ c, π w * (ind φ w * mass (F.P w) φ) = π w * (ind φ w * c) :=
      fun w hw => by rw [mem_valCell.1 hw]
    have e1 : ∑ w ∈ valCell F φ c, π w * (ind φ w * mass (F.P w) φ) =
        c * mass π (φ ∩ valCell F φ c) := by
      rw [sum_congr rfl e0, mass, mul_sum]
      simp only [ind, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
      rw [sum_ite_mem, inter_comm]
      apply sum_congr rfl; intro w _; ring
    have e2 : ∀ w ∈ valCell F φ c, π w * mass (F.P w) φ ^ 2 = π w * c ^ 2 :=
      fun w hw => by rw [mem_valCell.1 hw]
    rw [e1, h c, sum_congr rfl e2, mass, mul_sum, mul_sum]
    apply sum_congr rfl
    intro w _
    ring

/-- **Theorem I4.2(a) / Armstrong I4.2(i): value-form reflection for `φ` implies Brier accuracy
non-decrease for `φ`.** With `Q w := P_w(φ)` and `p := π(φ)`: `E[(𝟙_φ − Q)²] = p − E[Q²]` and
`E[(𝟙_φ − p)²] = p − p²`, and `E[Q²] ≥ (E Q)² = p²` — the conditional-variance decomposition.
Source: [[radical]] Theorem I4.2(a) l. 135; [[armstrong]] I4.2(i) l. 121
Kind: P
Fidelity: weaker: Brier only (radical I4.2(a) claims every strictly proper score; the
all-proper-scores form is the `extension`, not built)
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem brier_expLoss_le_constLoss {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    {φ : Finset W} (h : ValueReflectsOn π F φ) :
    expLoss π F φ brier ≤ constLoss π φ brier := by
  obtain ⟨hQ, hQI⟩ := valueReflectsOn_moments h
  have hI : ∑ w, π w * ind φ w = mass π φ := by
    rw [mass_eq_E_ind]; rfl
  have hI2 : ∑ w, π w * ind φ w ^ 2 = mass π φ := by
    rw [← hI]; apply sum_congr rfl; intro w _; simp only [ind]; split_ifs <;> ring
  have hsum : ∑ w, π w = 1 := hπ.2
  have hvar : 0 ≤ ∑ w, π w * (mass (F.P w) φ - mass π φ) ^ 2 :=
    sum_nonneg (fun w _ => mul_nonneg (hπ.1 w) (sq_nonneg _))
  have hexp : expLoss π F φ brier =
      ∑ w, π w * mass (F.P w) φ ^ 2 - 2 * ∑ w, π w * (ind φ w * mass (F.P w) φ) +
        ∑ w, π w * ind φ w ^ 2 := by
    unfold expLoss brier
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro w _; ring
  have hconst : constLoss π φ brier =
      mass π φ ^ 2 * ∑ w, π w - 2 * mass π φ * ∑ w, π w * ind φ w + ∑ w, π w * ind φ w ^ 2 := by
    unfold constLoss brier
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro w _; ring
  have hvar' : ∑ w, π w * (mass (F.P w) φ - mass π φ) ^ 2 =
      ∑ w, π w * mass (F.P w) φ ^ 2 - 2 * mass π φ * ∑ w, π w * mass (F.P w) φ +
        mass π φ ^ 2 * ∑ w, π w := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro w _; ring
  rw [hexp, hconst, hQI, hI2, hI, hsum]
  rw [hvar', hQ, hsum] at hvar
  nlinarith

end

end Cleanroom.Corrigibility.CorrReflectFrames
