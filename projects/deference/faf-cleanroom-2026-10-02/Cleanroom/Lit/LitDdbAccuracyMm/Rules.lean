import Cleanroom.Lit.LitDdbAccuracyMm.Basic

/-!
# The step class of rules is gsp, value-directed and continuous (Targets 6(i)–(iii), 9(b))

The integral-free recipe. For `ρ` a distribution with `e := E_ρ(X)`:
`E_ρ(I_X(x)) = c (x − e)^2 + ∑ i, d i (clamp_i x − e)^2 + const_ρ` for the step rule
`I = c·Brier + ∑ i, d i · Λ_i` (`expInacc_stepRule`), by `E_ρ[(y − X)^2] = (y − e)^2 + Var_ρ X`
at `y = x` and `y = clamp_i x`. The first term is strictly minimised at `x = e`, each clamp term is
weakly minimised there because `clamp` is monotone and `clamp e` is the nearest point of
`[a, b]` to `e` — so the rule is gsp for `0 < c`, `0 ≤ d i`, on every frame and for every `X`.
Value-directedness: `x ↦ (x − k)^2` is strictly monotone away from `k`, each clamp term weakly
(`sq_clamp_sub_le_of_le`). Continuity: `clamp` is continuous. DDB leave the gsp-ness of their
six-case rule "to the reader" (l. 728); this file is that verification, for the whole class.
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## `clamp` -/

/-- `clamp` is monotone.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem clamp_mono {α β x y : ℝ} (h : x ≤ y) : clamp α β x ≤ clamp α β y :=
  max_le_max_left α (min_le_min_left β h)

/-- `α ≤ clamp α β x`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem le_clamp (α β x : ℝ) : α ≤ clamp α β x := le_max_left _ _

/-- `clamp α β x ≤ β` when `α ≤ β`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem clamp_le {α β : ℝ} (h : α ≤ β) (x : ℝ) : clamp α β x ≤ β :=
  max_le h (min_le_left _ _)

/-- `clamp α β x = α` when `x ≤ α`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem clamp_eq_left {α β x : ℝ} (h : x ≤ α) : clamp α β x = α := by
  unfold clamp
  exact max_eq_left (le_trans (min_le_right _ _) h)

/-- `clamp α β x = β` when `β ≤ x` and `α ≤ β`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem clamp_eq_right {α β x : ℝ} (hαβ : α ≤ β) (h : β ≤ x) : clamp α β x = β := by
  unfold clamp
  rw [min_eq_left h]
  exact max_eq_right hαβ

/-- `clamp α β x = x` when `α ≤ x ≤ β`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem clamp_eq_self {α β x : ℝ} (hα : α ≤ x) (hβ : x ≤ β) : clamp α β x = x := by
  unfold clamp
  rw [min_eq_right hβ]
  exact max_eq_right hα

/-- `clamp α β x ≤ x` when `α ≤ x`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem clamp_le_self {α β x : ℝ} (hα : α ≤ x) : clamp α β x ≤ x :=
  max_le hα (min_le_right _ _)

/-- `x ≤ clamp α β x` when `x ≤ β`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem self_le_clamp {α β x : ℝ} (hβ : x ≤ β) : x ≤ clamp α β x :=
  le_trans (le_min hβ le_rfl) (le_max_right _ _)

/-- `clamp` is continuous.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem continuous_clamp (α β : ℝ) : Continuous (clamp α β) :=
  continuous_const.max (continuous_const.min continuous_id)

/-- **The nearest-point inequality.** `(clamp e − e)^2 ≤ (clamp x − e)^2` for every `x`:
`clamp e` is the point of `[α, β]` nearest to `e`, and `clamp x ∈ [α, β]`.
Source: none: infrastructure (Target 6(i))
Kind: L
Fidelity: n/a -/
theorem sq_clamp_sub_self_le {α β : ℝ} (hαβ : α ≤ β) (e x : ℝ) :
    (clamp α β e - e) ^ 2 ≤ (clamp α β x - e) ^ 2 := by
  rcases le_or_gt e α with h | h
  · rw [clamp_eq_left h]
    have h1 : α - e ≤ clamp α β x - e := by linarith [le_clamp α β x]
    have h0 : 0 ≤ α - e := by linarith
    exact pow_le_pow_left₀ h0 h1 2
  rcases le_or_gt e β with h' | h'
  · rw [clamp_eq_self h.le h', sub_self, zero_pow (by norm_num)]
    positivity
  · rw [clamp_eq_right hαβ h'.le]
    have h1 : e - clamp α β x ≥ e - β := by linarith [clamp_le hαβ x]
    have h0 : 0 ≤ e - β := by linarith
    have : (β - e) ^ 2 = (e - β) ^ 2 := by ring
    rw [this, show (clamp α β x - e) ^ 2 = (e - clamp α β x) ^ 2 by ring]
    exact pow_le_pow_left₀ h0 h1 2

/-- **Weak monotonicity of the clamp term toward the true value, from below:**
`e₁ ≤ e₂ ≤ k → (clamp e₂ − k)^2 ≤ (clamp e₁ − k)^2`.
Source: none: infrastructure (Target 6(ii))
Kind: L
Fidelity: n/a -/
theorem sq_clamp_sub_le_of_le {α β e₁ e₂ k : ℝ} (h12 : e₁ ≤ e₂) (h2k : e₂ ≤ k) :
    (clamp α β e₂ - k) ^ 2 ≤ (clamp α β e₁ - k) ^ 2 := by
  have hc : clamp α β e₁ ≤ clamp α β e₂ := clamp_mono h12
  rcases le_or_gt (clamp α β e₂) k with h | h
  · have : (clamp α β e₁ - k) ^ 2 - (clamp α β e₂ - k) ^ 2 =
        (clamp α β e₂ - clamp α β e₁) * (2 * k - clamp α β e₁ - clamp α β e₂) := by ring
    nlinarith [mul_nonneg (sub_nonneg.2 hc) (by linarith : 0 ≤ 2 * k - clamp α β e₁ - clamp α β e₂)]
  · -- `clamp e₂ > k ≥ e₂` forces `e₂ < α`, so both clamps are `α`
    have h2α : e₂ < α := by
      by_contra hcon
      have := clamp_le_self (α := α) (β := β) (not_lt.1 hcon)
      linarith
    rw [clamp_eq_left h2α.le, clamp_eq_left (by linarith : e₁ ≤ α)]

/-- **Weak monotonicity of the clamp term toward the true value, from above:**
`k ≤ e₂ ≤ e₁ → (clamp e₂ − k)^2 ≤ (clamp e₁ − k)^2` (needs `α ≤ β`).
Source: none: infrastructure (Target 6(ii))
Kind: L
Fidelity: n/a -/
theorem sq_clamp_sub_le_of_ge {α β e₁ e₂ k : ℝ} (hαβ : α ≤ β) (h12 : e₂ ≤ e₁) (hk2 : k ≤ e₂) :
    (clamp α β e₂ - k) ^ 2 ≤ (clamp α β e₁ - k) ^ 2 := by
  have hc : clamp α β e₂ ≤ clamp α β e₁ := clamp_mono h12
  rcases le_or_gt k (clamp α β e₂) with h | h
  · have : (clamp α β e₁ - k) ^ 2 - (clamp α β e₂ - k) ^ 2 =
        (clamp α β e₁ - clamp α β e₂) * (clamp α β e₁ + clamp α β e₂ - 2 * k) := by ring
    nlinarith [mul_nonneg (sub_nonneg.2 hc) (by linarith : 0 ≤ clamp α β e₁ + clamp α β e₂ - 2 * k)]
  · -- `clamp e₂ < k ≤ e₂` forces `β < e₂`, so both clamps are `β`
    have h2β : β < e₂ := by
      by_contra hcon
      have := self_le_clamp (α := α) (β := β) (not_lt.1 hcon)
      linarith
    rw [clamp_eq_right hαβ h2β.le, clamp_eq_right hαβ (by linarith : β ≤ e₁)]

/-! ## The expected-inaccuracy identity -/

/-- `∑ w, ρ w (y − X w)^2 = (y − E_ρ(X))^2 + ∑ w, ρ w (X w − E_ρ(X))^2` for a distribution `ρ`.
Source: none: infrastructure (Target 6(i))
Kind: L
Fidelity: n/a -/
theorem sum_sq_sub_eq {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) (X : W → ℝ) (y : ℝ) :
    ∑ w, ρ w * (y - X w) ^ 2 = (y - E ρ X) ^ 2 + ∑ w, ρ w * (X w - E ρ X) ^ 2 := by
  have hz : ∑ w, ρ w * (X w - E ρ X) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hρ.2, one_mul, E, sub_self]
  have h1 : ∑ w, ρ w * (y - X w) ^ 2 =
      ∑ w, (ρ w * (y - E ρ X) ^ 2 + ρ w * (X w - E ρ X) ^ 2 -
        2 * (y - E ρ X) * (ρ w * (X w - E ρ X))) := by
    apply sum_congr rfl
    intro w _
    ring
  rw [h1, sum_sub_distrib, sum_add_distrib, ← sum_mul, ← mul_sum, hz, hρ.2]
  ring

/-- **The identity of record for the step class.** For a distribution `ρ` with `e := E_ρ(X)`:
`E_ρ(I_X(x)) = c (x − e)^2 + ∑ i, d i (clamp_i x − e)^2 + K_ρ`, where
`K_ρ = c·Var_ρ X + ∑ i, d i (Var_ρ X − ∑ w, ρ w (clamp_i (X w) − X w)^2)` does not depend on `x`.
Source: none: infrastructure (mandate Target 6(i), generalised to the step class, Target 9(b))
Kind: L
Fidelity: n/a -/
theorem expInacc_stepRule {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) (X : W → ℝ) (c : ℝ) {n : ℕ}
    (a b d : Fin n → ℝ) (x : ℝ) :
    expInacc ρ X (stepRule c a b d) x =
      c * (x - E ρ X) ^ 2 + ∑ i, d i * (clamp (a i) (b i) x - E ρ X) ^ 2 +
      (c * ∑ w, ρ w * (X w - E ρ X) ^ 2 +
        ∑ i, d i * (∑ w, ρ w * (X w - E ρ X) ^ 2 -
          ∑ w, ρ w * (clamp (a i) (b i) (X w) - X w) ^ 2)) := by
  unfold expInacc stepRule clampTerm
  have h1 : ∑ w, ρ w * (c * (x - X w) ^ 2 +
      ∑ i, d i * ((clamp (a i) (b i) x - X w) ^ 2 - (clamp (a i) (b i) (X w) - X w) ^ 2)) =
      c * ∑ w, ρ w * (x - X w) ^ 2 +
      ∑ i, d i * (∑ w, ρ w * (clamp (a i) (b i) x - X w) ^ 2 -
        ∑ w, ρ w * (clamp (a i) (b i) (X w) - X w) ^ 2) := by
    have e1 : ∀ w, ρ w * (c * (x - X w) ^ 2 +
        ∑ i, d i * ((clamp (a i) (b i) x - X w) ^ 2 - (clamp (a i) (b i) (X w) - X w) ^ 2)) =
        c * (ρ w * (x - X w) ^ 2) +
        ∑ i, d i * (ρ w * (clamp (a i) (b i) x - X w) ^ 2 -
          ρ w * (clamp (a i) (b i) (X w) - X w) ^ 2) := by
      intro w
      rw [mul_add, mul_sum]
      congr 1
      · ring
      · apply sum_congr rfl; intro i _; ring
    simp only [e1]
    rw [sum_add_distrib, ← mul_sum, sum_comm]
    congr 1
    apply sum_congr rfl
    intro i _
    rw [← mul_sum, sum_sub_distrib]
  rw [h1, sum_sq_sub_eq hρ X x]
  have h2 : ∀ i, ∑ w, ρ w * (clamp (a i) (b i) x - X w) ^ 2 =
      (clamp (a i) (b i) x - E ρ X) ^ 2 + ∑ w, ρ w * (X w - E ρ X) ^ 2 :=
    fun i => sum_sq_sub_eq hρ X _
  simp only [h2]
  rw [show ∑ i, d i * ((clamp (a i) (b i) x - E ρ X) ^ 2 + ∑ w, ρ w * (X w - E ρ X) ^ 2 -
      ∑ w, ρ w * (clamp (a i) (b i) (X w) - X w) ^ 2) =
      ∑ i, (d i * (clamp (a i) (b i) x - E ρ X) ^ 2 +
        d i * (∑ w, ρ w * (X w - E ρ X) ^ 2 - ∑ w, ρ w * (clamp (a i) (b i) (X w) - X w) ^ 2))
      from sum_congr rfl (fun i _ => by ring)]
  rw [sum_add_distrib]
  ring

/-! ## The step class is gsp, value-directed, continuous -/

/-- **Target 9(b) / 6(i).** Every step rule with `0 < c` and nonnegative increments is gsp, on
every frame, for every `X`, at every real estimate.
Source: [[Deference Done Better]] App. B l. 728 ("we leave it to the reader to verify that
`I_X` is a gsp"), fn 67; mandate Targets 6(i), 9(b)
Kind: P
Fidelity: exact (the class of step densities with positive base level)
Hyps: (a) none -/
theorem isGsp_stepRule {c : ℝ} (hc : 0 < c) {n : ℕ} {a b d : Fin n → ℝ}
    (hab : ∀ i, a i ≤ b i) (hd : ∀ i, 0 ≤ d i) (X : W → ℝ) : IsGsp X (stepRule c a b d) := by
  intro ρ hρ s hs
  rw [expInacc_stepRule hρ, expInacc_stepRule hρ]
  have hne : s - E ρ X ≠ 0 := sub_ne_zero.2 hs
  have h1 : 0 < c * (s - E ρ X) ^ 2 := by positivity
  have h2 : ∑ i, d i * (clamp (a i) (b i) (E ρ X) - E ρ X) ^ 2 ≤
      ∑ i, d i * (clamp (a i) (b i) s - E ρ X) ^ 2 :=
    sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (sq_clamp_sub_self_le (hab i) _ _) (hd i)
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_add]
  linarith

/-- **Target 9(b) / 6(ii).** Every step rule with `0 < c` and nonnegative increments is
value-directed (for every `X`).
Source: [[Deference Done Better]] App. B l. 650 (value-directedness), fn 67; mandate Target 6(ii)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem valueDirected_stepRule {c : ℝ} (hc : 0 < c) {n : ℕ} {a b d : Fin n → ℝ}
    (hab : ∀ i, a i ≤ b i) (hd : ∀ i, 0 ≤ d i) (X : W → ℝ) :
    ValueDirected X (stepRule c a b d) := by
  intro w e₁ e₂
  unfold stepRule clampTerm
  constructor
  · rintro ⟨h12, h2k⟩
    have hb : c * (e₂ - X w) ^ 2 < c * (e₁ - X w) ^ 2 := by
      apply mul_lt_mul_of_pos_left _ hc
      rw [show (e₂ - X w) ^ 2 = (X w - e₂) ^ 2 by ring, show (e₁ - X w) ^ 2 = (X w - e₁) ^ 2 by ring]
      exact pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num)
    have hs : ∑ i, d i * ((clamp (a i) (b i) e₂ - X w) ^ 2 - (clamp (a i) (b i) (X w) - X w) ^ 2) ≤
        ∑ i, d i * ((clamp (a i) (b i) e₁ - X w) ^ 2 - (clamp (a i) (b i) (X w) - X w) ^ 2) := by
      apply sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hd i)
      linarith [sq_clamp_sub_le_of_le (α := a i) (β := b i) h12.le h2k]
    linarith
  · rintro ⟨hk2, h21⟩
    have hb : c * (e₂ - X w) ^ 2 < c * (e₁ - X w) ^ 2 := by
      apply mul_lt_mul_of_pos_left _ hc
      exact pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num)
    have hs : ∑ i, d i * ((clamp (a i) (b i) e₂ - X w) ^ 2 - (clamp (a i) (b i) (X w) - X w) ^ 2) ≤
        ∑ i, d i * ((clamp (a i) (b i) e₁ - X w) ^ 2 - (clamp (a i) (b i) (X w) - X w) ^ 2) := by
      apply sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hd i)
      linarith [sq_clamp_sub_le_of_ge (hab i) h21.le hk2]
    linarith

/-- **Target 6(iii).** Every step rule is continuous in the estimate.
Source: none: infrastructure (DDB fn 45's continuity, for the witness)
Kind: L
Fidelity: n/a -/
theorem continuous_stepRule (c : ℝ) {n : ℕ} (a b d : Fin n → ℝ) (k : ℝ) :
    Continuous (fun x => stepRule c a b d x k) := by
  unfold stepRule clampTerm
  apply Continuous.add
  · exact continuous_const.mul ((continuous_id.sub continuous_const).pow 2)
  · apply continuous_finsetSum
    intro i _
    exact continuous_const.mul
      ((((continuous_clamp (a i) (b i)).sub continuous_const).pow 2).sub continuous_const)

/-! ## The one-piece and Brier instances -/

/-- `mixRule` is the one-piece step rule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mixRule_eq_stepRule (α β c d : ℝ) :
    mixRule α β c d = stepRule c ![α] ![β] ![d] := by
  funext x k
  simp [mixRule, stepRule]

/-- `mixRule α β c d` is gsp for `α ≤ β`, `0 < c`, `0 ≤ d`.
Source: [[Deference Done Better]] fn 67; mandate Target 6(i)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem isGsp_mixRule {α β c d : ℝ} (hαβ : α ≤ β) (hc : 0 < c) (hd : 0 ≤ d) (X : W → ℝ) :
    IsGsp X (mixRule α β c d) := by
  rw [mixRule_eq_stepRule]
  exact isGsp_stepRule hc (fun i => by fin_cases i; exact hαβ) (fun i => by fin_cases i; exact hd) X

/-- `mixRule α β c d` is value-directed for `α ≤ β`, `0 < c`, `0 ≤ d`.
Source: [[Deference Done Better]] App. B l. 650; mandate Target 6(ii)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem valueDirected_mixRule {α β c d : ℝ} (hαβ : α ≤ β) (hc : 0 < c) (hd : 0 ≤ d)
    (X : W → ℝ) : ValueDirected X (mixRule α β c d) := by
  rw [mixRule_eq_stepRule]
  exact valueDirected_stepRule hc (fun i => by fin_cases i; exact hαβ)
    (fun i => by fin_cases i; exact hd) X

/-- `mixRule` is continuous in the estimate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem continuous_mixRule (α β c d k : ℝ) : Continuous (fun x => mixRule α β c d x k) := by
  rw [mixRule_eq_stepRule]
  exact continuous_stepRule c _ _ _ k

/-- **DDB's six-case rule is gsp** for `α ≤ β` and `C ≥ 1` — the verification DDB leave to the
reader (l. 728).
Source: [[Deference Done Better]] App. B l. 720–728, fn 67
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem isGsp_ruleC {α β C : ℝ} (hαβ : α ≤ β) (hC : 1 ≤ C) (X : W → ℝ) : IsGsp X (ruleC α β C) :=
  isGsp_mixRule hαβ one_pos (by linarith) X

/-- **DDB's six-case rule is value-directed** for `α ≤ β` and `C ≥ 1`.
Source: [[Deference Done Better]] App. B l. 650, l. 720
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem valueDirected_ruleC {α β C : ℝ} (hαβ : α ≤ β) (hC : 1 ≤ C) (X : W → ℝ) :
    ValueDirected X (ruleC α β C) :=
  valueDirected_mixRule hαβ one_pos (by linarith) X

/-- The six-case rule is continuous in the estimate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem continuous_ruleC (α β C k : ℝ) : Continuous (fun x => ruleC α β C x k) :=
  continuous_mixRule α β 1 (C - 1) k

/-- The Brier rule is the step rule with no pieces, hence gsp and value-directed.
Source: [[Deference Done Better]] App. B l. 770
Kind: L
Fidelity: exact -/
theorem brier_eq_stepRule : brier = stepRule 1 (![] : Fin 0 → ℝ) ![] ![] := by
  funext x k
  simp [brier, stepRule]

/-- Brier is gsp.
Source: [[Deference Done Better]] App. B l. 770
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem isGsp_brier (X : W → ℝ) : IsGsp X brier := by
  rw [brier_eq_stepRule]
  exact isGsp_stepRule one_pos (fun i => i.elim0) (fun i => i.elim0) X

/-- **Fn 46's rule is gsp** (the mandate's Target 9(b) instance for Target 10).
Source: [[Deference Done Better]] fn 46
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem isGsp_fn46Rule (X : W → ℝ) : IsGsp X fn46Rule :=
  isGsp_mixRule (by norm_num) (by norm_num) (by norm_num) X

/-- Fn 46's rule is value-directed.
Source: [[Deference Done Better]] fn 46
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem valueDirected_fn46Rule (X : W → ℝ) : ValueDirected X fn46Rule :=
  valueDirected_mixRule (by norm_num) (by norm_num) (by norm_num) X

end

end Cleanroom.Lit.LitDdbAccuracyMm
