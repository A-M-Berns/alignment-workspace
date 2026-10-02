import Cleanroom.Lit.LitWeathersonFrames.CFrame

/-!
Audit round 1, adversarial lens — probe: on a countable carrier the product-form `TotalTrustC`
is the paper's ratio form on positive-mass threshold events.

The package's fidelity claim "exact (product form)" rests, on the countable side, on the
identification `∑' π (X − t) 𝟙 ≥ 0 ⟺ (mass > 0 → t ≤ E_π(X | event))` — the countable analogue
of the dependency's `totalTrust_iff_cond`, which the package cites but does not restate for
`tsum`s. This probe proves it (bounded `X`, distribution `π`): the product sum is
`s − t · m`; if `m > 0` the two sides are `t ≤ s / m`; if `m = 0` every summand vanishes (a
nonnegative series summing to zero is zero), so the product inequality holds trivially — which is
exactly the positive-mass convention. Not imported by the library.
-/

namespace Cleanroom.Lit.LitWeathersonFrames.AuditR1Adv

open Cleanroom.Lit.LitWeathersonFrames

variable {W : Type}

theorem summable_ind {π : W → ℝ} (hπ : IsDist π) (c : W → Prop) [DecidablePred c] :
    Summable (fun w => π w * (if c w then (1:ℝ) else 0)) := by
  refine Summable.of_nonneg_of_le (fun w => ?_) (fun w => ?_) hπ.summable
  · split_ifs <;> simp [hπ.1 w]
  · split_ifs <;> simp [hπ.1 w]

theorem summable_X_ind {π X : W → ℝ} (hπ : IsDist π) (hX : Bdd X) (c : W → Prop)
    [DecidablePred c] : Summable (fun w => π w * X w * (if c w then (1:ℝ) else 0)) := by
  obtain ⟨M, hM⟩ := hX
  refine Summable.of_norm_bounded (hπ.summable.mul_right M) (fun w => ?_)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (X w)) (hM w)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hπ.1 w)]
  split_ifs
  · simp only [abs_one, mul_one]
    exact mul_le_mul_of_nonneg_left (hM w) (hπ.1 w)
  · simp only [abs_zero, mul_zero]
    exact mul_nonneg (hπ.1 w) hM0

/-- The product inequality on a threshold event `c` is the ratio inequality on positive mass. -/
theorem prod_nonneg_iff_cond {π X : W → ℝ} (hπ : IsDist π) (hX : Bdd X) (t : ℝ)
    (c : W → Prop) [DecidablePred c] :
    0 ≤ ∑' w, π w * (X w - t) * (if c w then (1:ℝ) else 0) ↔
      (0 < ∑' w, π w * (if c w then (1:ℝ) else 0) →
        t ≤ (∑' w, π w * X w * (if c w then (1:ℝ) else 0)) /
              ∑' w, π w * (if c w then (1:ℝ) else 0)) := by
  have hnn : ∀ w, 0 ≤ π w * (if c w then (1:ℝ) else 0) := fun w =>
    mul_nonneg (hπ.1 w) (by split_ifs <;> norm_num)
  have key : ∑' w, π w * (X w - t) * (if c w then (1:ℝ) else 0) =
      (∑' w, π w * X w * (if c w then (1:ℝ) else 0)) -
        t * ∑' w, π w * (if c w then (1:ℝ) else 0) := by
    rw [← tsum_mul_left, ← (summable_X_ind hπ hX c).tsum_sub ((summable_ind hπ c).mul_left t)]
    congr 1; funext w; ring
  rw [key]
  have hm0 : 0 ≤ ∑' w, π w * (if c w then (1:ℝ) else 0) := tsum_nonneg hnn
  constructor
  · intro h hm
    rw [le_div_iff₀ hm]; linarith
  · intro h
    rcases hm0.lt_or_eq with hm | hm
    · have := h hm
      rw [le_div_iff₀ hm] at this; linarith
    · have hsum : HasSum (fun w => π w * (if c w then (1:ℝ) else 0)) 0 := by
        have h' := (summable_ind hπ c).hasSum
        rwa [← hm] at h'
      have hf := (hasSum_zero_iff_of_nonneg hnn).mp hsum
      have hterm : ∀ w, π w * X w * (if c w then (1:ℝ) else 0) = 0 := fun w => by
        have h0 : π w * (if c w then (1:ℝ) else 0) = 0 := by
          have := congrFun hf w; simpa using this
        calc π w * X w * (if c w then (1:ℝ) else 0)
            = X w * (π w * (if c w then (1:ℝ) else 0)) := by ring
          _ = 0 := by rw [h0, mul_zero]
      simp only [hterm, tsum_zero, ← hm, mul_zero, sub_zero, le_refl]

/-- **`TotalTrustC` is the ratio form on positive-mass events** (bounded variables). -/
theorem totalTrustC_iff_cond {π : W → ℝ} (hπ : IsDist π) (F : CFrame W) :
    TotalTrustC π F ↔ ∀ X, Bdd X → ∀ t,
      0 < ∑' w, π w * (if t ≤ Eℕ (F.P w) X then (1:ℝ) else 0) →
      t ≤ (∑' w, π w * X w * (if t ≤ Eℕ (F.P w) X then (1:ℝ) else 0)) /
            ∑' w, π w * (if t ≤ Eℕ (F.P w) X then (1:ℝ) else 0) :=
  forall_congr' fun X => forall_congr' fun hX => forall_congr' fun t =>
    prod_nonneg_iff_cond hπ hX t (fun w => t ≤ Eℕ (F.P w) X)

end Cleanroom.Lit.LitWeathersonFrames.AuditR1Adv
