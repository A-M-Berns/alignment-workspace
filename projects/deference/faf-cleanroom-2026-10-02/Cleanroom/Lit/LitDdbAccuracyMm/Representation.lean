import Cleanroom.Lit.LitDdbAccuracyMm.Accuracy

/-!
# The representation story, integral-free (Target 9)

(a) **The transcriber's `(x − t)` form is refuted** (`xt_rule_not_isGspOn`): Theorem 7.9 prints
`I_X(x, k) = ∫_k^x (k − x) λ(dt)` (a typo), and the transcription's note (l. 9) "corrects" it to
`∫_k^x (x − t) λ(dt)`. With `λ(dt) = (1 + t) dt` on `[0, 2]` that rule has the closed form
`I x k = F x x − F x k`, `F x t = x(t + t²/2) − (t²/2 + t³/3)`; on `W = Fin 2` with
`π = (3/4, 1/4)`, `X = (0, 2)`, `e = 1/2`: `E_π(I(7/10)) = 4613/6000 < 13/16 = E_π(I(1/2))`, so
it is not gsp (not even on the value range). The gsp family is `∫_k^x (t − k) λ(dt)`, whose
step-density instances are `Rules.lean`'s `stepRule` (Target 9(b), proved gsp and value-directed
there). Remark, not a theorem: the exact minimiser of `s ↦ E_π(I(s))` is `√3 − 1` (the root of
`s² + 2s − 2`), not `e`.

(c) **Lemma 7.11, finite form.** For a step rule the difference `E_π(I_X(P)) − E_π(I_X(e))`
decomposes over the pieces as `c·Γ(−∞, ∞) + ∑ d_i Γ(a_i, b_i)` with
`Γ(a, b) := ∑ w, π w ((clamp_{a,b} E_w(X) − X w)² − (clamp_{a,b} e − X w)²)` (`stepRule_diff`),
the finite analogue of DDB's (22) `∫ h · g` over pieces. Each piece term is `≤ 0` under Total Trust
with respect to `X` (`clampTerm_diff_nonpos_of_totalTrustOn`, by Theorem 3.2 (⟹) applied to the
gsp rules `mixRule a b c 1` and `c → 0⁺`), and on a failure interval the piece term is `> 0`
(`clampTerm_diff_pos_of_failure`, from `Witness.lean`'s `failure_data`). The measure-theoretic
Fubini identity (22) itself is not formalised: the core is integral-free by design.
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## (a) The `(x − t)` form refuted -/

/-- The antiderivative `F x t = ∫ (x − t)(1 + t) dt = x(t + t²/2) − (t²/2 + t³/3)`.
Source: [[Deference Done Better]] l. 9 (transcriber's note), Thm 7.9 l. 766; item 2-016 (ii)
Kind: D
Fidelity: n/a -/
def Fxt (x t : ℝ) : ℝ := x * (t + t ^ 2 / 2) - (t ^ 2 / 2 + t ^ 3 / 3)

/-- The transcriber's rule `I x k = ∫_k^x (x − t)(1 + t) dt = F x x − F x k`, in closed form.
Source: [[Deference Done Better]] l. 9 (transcriber's note); item 2-016 (ii)
Kind: D
Fidelity: exact (closed form of the transcription's formula with `λ(dt) = (1 + t) dt`) -/
def xtRule : Rule := fun x k => Fxt x x - Fxt x k

/-- The refuting instance: `π = (3/4, 1/4)`, `X = (0, 2)`.
Source: mandate Target 9(a)
Kind: D
Fidelity: n/a -/
def πxt : Fin 2 → ℝ := ![3 / 4, 1 / 4]

/-- `πxt` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πxt_mem : πxt ∈ stdSimplex ℝ (Fin 2) :=
  Examples.simplex2 _ _ (by norm_num) (by norm_num) (by norm_num)

/-- The variable `X = (0, 2)`.
Source: mandate Target 9(a)
Kind: D
Fidelity: n/a -/
def Xxt : Fin 2 → ℝ := ![0, 2]

/-- The values: `E_π(X) = 1/2`, `E_π(I(1/2)) = 13/16`, `E_π(I(7/10)) = 4613/6000`.
Source: mandate Target 9(a)
Kind: L
Fidelity: exact -/
theorem xt_values : E πxt Xxt = 1 / 2 ∧ expInacc πxt Xxt xtRule (1 / 2) = 13 / 16 ∧
    expInacc πxt Xxt xtRule (7 / 10) = 4613 / 6000 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [E, expInacc, Fin.sum_univ_two, πxt, Xxt, xtRule, Fxt]

/-- **Target 9(a): the transcription's `(x − t)` rule is not gsp** — a fixed estimate `7/10`
(in the value range `[0, 2]`) beats the deferrer's own estimate `1/2`. The gsp family of
Theorem 7.9 is `∫_k^x (t − k) λ(dt)`.
Source: [[Deference Done Better]] l. 9, Thm 7.9 l. 766; item 2-016 (ii)
Kind: N+
Fidelity: exact (refutes the transcriber's correction, not DDB's theorem)
Hyps: (a) none -/
theorem xt_rule_not_isGspOn : ¬ IsGspOn Xxt xtRule := by
  intro h
  obtain ⟨he, h1, h2⟩ := xt_values
  have := h πxt πxt_mem (7 / 10) ⟨0, by norm_num [Xxt]⟩ ⟨1, by norm_num [Xxt]⟩
    (by rw [he]; norm_num)
  rw [he, h1, h2] at this
  norm_num at this

/-- The `(x − t)` rule is not gsp (a fortiori).
Source: item 2-016 (ii)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem xt_rule_not_isGsp : ¬ IsGsp Xxt xtRule := fun h => xt_rule_not_isGspOn h.isGspOn

/-- The `(x − t)` rule vanishes on the diagonal — Theorem 7.9's hypothesis `I_X(x, x) = 0`.
Source: [[Deference Done Better]] Thm 7.9 l. 766 (hypothesis); audit r1 (fidelity) N5
Kind: L
Fidelity: n/a -/
theorem xtRule_diag (x : ℝ) : xtRule x x = 0 := by simp [xtRule]

/-- On the value range `[0, 2]` the `(x − t)` rule is strictly increasing in `|x − k|` for both
values `k ∈ {0, 2}` — Theorem 7.9's monotonicity hypothesis, in the form `ValueDirectedOn`:
`I(s, 0) = s²/2 + s³/6` is increasing and `I(s, 2) = s²/2 + s³/6 − 4s + 14/3` decreasing on
`[0, 2]` (derivative `s + s²/2 − 4 ≤ 0` there).
Source: [[Deference Done Better]] Thm 7.9 l. 766 (hypothesis); audit r1 (fidelity) N5
Kind: P
Fidelity: exact (the hypothesis on the value range)
Hyps: (a) none -/
theorem xtRule_valueDirectedOn : ValueDirectedOn Xxt xtRule := by
  have hX : ∀ v : Fin 2, Xxt v = 0 ∨ Xxt v = 2 := by
    intro v; fin_cases v <;> simp [Xxt]
  intro w e₁ e₂
  constructor
  · rintro ⟨w₀, hw₀⟩ h12 h2
    rcases hX w₀ with h0 | h0 <;> rcases hX w with h | h <;> rw [h0] at hw₀ <;> rw [h] at h2 ⊢
    · linarith
    · -- `0 ≤ e₁ < e₂ ≤ 2`: `I(·, 2)` decreases
      have hfac : xtRule e₁ 2 - xtRule e₂ 2 =
          (e₂ - e₁) * (4 - (e₁ + e₂) / 2 - (e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2) / 6) := by
        simp only [xtRule, Fxt]; ring
      have he₂ : 0 ≤ e₂ := hw₀.trans h12.le
      have hpos : 0 < 4 - (e₁ + e₂) / 2 - (e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2) / 6 := by
        nlinarith [mul_le_mul_of_nonneg_right (h12.le.trans h2) hw₀,
          mul_le_mul_of_nonneg_right (h12.le.trans h2) he₂, mul_le_mul_of_nonneg_right h2 he₂]
      have := mul_pos (sub_pos.2 h12) hpos
      linarith
    · linarith
    · linarith
  · rintro ⟨w₀, hw₀⟩ h2 h21
    rcases hX w₀ with h0 | h0 <;> rcases hX w with h | h <;> rw [h0] at hw₀ <;> rw [h] at h2 ⊢
    · linarith
    · linarith
    · -- `0 ≤ e₂ < e₁ ≤ 2`: `I(·, 0)` increases
      have hfac : xtRule e₁ 0 - xtRule e₂ 0 =
          (e₁ - e₂) * ((e₁ + e₂) / 2 + (e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2) / 6) := by
        simp only [xtRule, Fxt]; ring
      have he₁ : 0 < e₁ := h2.trans_lt h21
      have hpos : 0 < (e₁ + e₂) / 2 + (e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2) / 6 := by
        nlinarith [mul_nonneg h2 h2, mul_nonneg he₁.le h2, mul_pos he₁ he₁]
      have := mul_pos (sub_pos.2 h21) hpos
      linarith
    · linarith

/-- **Theorem 7.9 with the transcriber's integrand is false even under the theorem's own
hypotheses.** The `(x − t)` rule with `λ = (1 + t) dt` vanishes on the diagonal, is strictly
increasing in `|x − k|` on the value range, and is polynomial in `x` (so absolutely continuous),
yet it is not gsp on the range. So the refutation is not dodged by Theorem 7.9's side conditions:
the integrand must be `(t − k)` (eq. (24)), as `isGsp_stepRule` shows.
Source: [[Deference Done Better]] l. 9 (transcriber's note), Thm 7.9 l. 766; item 2-016 (ii);
audit r1 (fidelity) N5
Kind: N+
Fidelity: exact (refutes the transcriber's correction with Theorem 7.9's hypotheses checked)
Hyps: (a) none -/
theorem xt_rule_thm79_refuted :
    (∀ x, xtRule x x = 0) ∧ ValueDirectedOn Xxt xtRule ∧ ¬ IsGspOn Xxt xtRule :=
  ⟨xtRule_diag, xtRule_valueDirectedOn, xt_rule_not_isGspOn⟩

/-! ## (c) Lemma 7.11, finite form -/

/-- The piece term `Γ(a, b) = ∑ w, π w ((clamp_{a,b} E_w(X) − X w)² − (clamp_{a,b} e − X w)²)`
— the finite analogue of `∫_a^b g` for DDB's (22).
Source: [[Deference Done Better]] App. B Lemma 7.11 l. 794 (eq. (22)); mandate Target 9(c)
Kind: D
Fidelity: variant: finite closed form of the piece integral -/
def pieceTerm (π : W → ℝ) (F : Frame W) (X : W → ℝ) (a b : ℝ) : ℝ :=
  ∑ w, π w * ((clamp a b (E (F.P w) X) - X w) ^ 2 - (clamp a b (E π X) - X w) ^ 2)

/-- **Lemma 7.11, finite form.** For a step rule,
`E_π(I_X(P)) − E_π(I_X(e)) = c · Γ_Brier + ∑ i, d i · Γ(a i, b i)`, where
`Γ_Brier = ∑ w, π w ((E_w(X) − X w)² − (e − X w)²)`.
Source: [[Deference Done Better]] App. B Lemma 7.11 l. 794; mandate Target 9(c)
Kind: L
Fidelity: variant: finite sum over pieces in place of the integral (22) -/
theorem stepRule_diff (π : W → ℝ) (F : Frame W) (X : W → ℝ) (c : ℝ) {n : ℕ} (a b d : Fin n → ℝ) :
    expInaccP π F X (stepRule c a b d) - expInacc π X (stepRule c a b d) (E π X) =
      c * ∑ w, π w * ((E (F.P w) X - X w) ^ 2 - (E π X - X w) ^ 2) +
      ∑ i, d i * pieceTerm π F X (a i) (b i) := by
  rw [expInaccP_sub_expInacc]
  unfold pieceTerm stepRule clampTerm
  simp only [mul_sum]
  rw [sum_comm, ← sum_add_distrib]
  apply sum_congr rfl
  intro w _
  rw [show ∑ i, d i * (π w * ((clamp (a i) (b i) (E (F.P w) X) - X w) ^ 2 -
      (clamp (a i) (b i) (E π X) - X w) ^ 2)) =
      π w * ∑ i, d i * ((clamp (a i) (b i) (E (F.P w) X) - X w) ^ 2 -
        (clamp (a i) (b i) (E π X) - X w) ^ 2) by
    rw [mul_sum]; apply sum_congr rfl; intro i _; ring]
  rw [show ∑ i, d i * ((clamp (a i) (b i) (E (F.P w) X) - X w) ^ 2 -
      (clamp (a i) (b i) (E π X) - X w) ^ 2) =
      ∑ i, d i * ((clamp (a i) (b i) (E (F.P w) X) - X w) ^ 2 -
        (clamp (a i) (b i) (X w) - X w) ^ 2) -
      ∑ i, d i * ((clamp (a i) (b i) (E π X) - X w) ^ 2 -
        (clamp (a i) (b i) (X w) - X w) ^ 2) by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _; ring]
  ring

/-- **The piece terms are `≤ 0` under Total Trust** (the finite form of "`g ≤ 0`" in (22)):
apply Theorem 3.2 (⟹) to the gsp rules `mixRule a b c 1` for every `c > 0` and let `c → 0⁺`
(a midpoint argument, no limit).
Source: [[Deference Done Better]] App. B l. 886 (the (⟹) of the Schervish-style proof); mandate
Target 9(c)
Kind: C
Fidelity: variant: finite piece terms
Hyps: (a) `hπ`, `TotalTrustOn`, `a ≤ b` -/
theorem clampTerm_diff_nonpos_of_totalTrustOn {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    {F : Frame W} (htt : TotalTrustOn X π F) {a b : ℝ} (hab : a ≤ b) :
    pieceTerm π F X a b ≤ 0 := by
  -- for every `c > 0`, `c · Γ_Brier + Γ(a, b) ≤ 0`
  have key : ∀ c : ℝ, 0 < c →
      c * ∑ w, π w * ((E (F.P w) X - X w) ^ 2 - (E π X - X w) ^ 2) + pieceTerm π F X a b ≤ 0 := by
    intro c hc
    have h := (totalTrustOn_expInaccP_le hπ htt (isGsp_mixRule hab hc zero_le_one X).isGspOn).1
    have e := stepRule_diff π F X c ![a] ![b] ![1]
    rw [← mixRule_eq_stepRule] at e
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero, one_mul] at e
    linarith
  by_contra hcon
  rw [not_le] at hcon
  set G := ∑ w, π w * ((E (F.P w) X - X w) ^ 2 - (E π X - X w) ^ 2) with hG
  set P := pieceTerm π F X a b with hP
  -- pick `c` small enough that `|c · G| ≤ Γ(a, b) / 2`
  rcases lt_trichotomy G 0 with hG0 | hG0 | hG0
  · have hc : 0 < P / (2 * -G) := div_pos hcon (by linarith)
    have := key _ hc
    have e : P / (2 * -G) * G = -(P / 2) := by
      rw [div_mul_eq_mul_div, div_eq_iff (by linarith)]
      ring
    rw [e] at this
    linarith
  · have := key 1 one_pos
    rw [hG0] at this
    linarith
  · have hc : 0 < P / (2 * G) := div_pos hcon (by linarith)
    have := key _ hc
    have e : P / (2 * G) * G = P / 2 := by
      rw [div_mul_eq_mul_div, div_eq_iff (by linarith)]
      ring
    rw [e] at this
    linarith

/-- **The piece term of a failure interval is `> 0`** (the finite form of "`g > 0` on `[x, y]`"
in DDB's (⟸)): for a clause-1 failure above `e`, `failure_data`'s `(α, β)` has
`Γ(α, β) = (β − α)((α + β) π(U) − 2 ∑_U π X) > 0` — the coefficient of `C` in the witness.
Source: [[Deference Done Better]] App. B l. 748 (eq. (19)), l. 898; mandate Target 9(c)
Kind: P
Fidelity: variant: finite piece term
Hyps: (a) `hπ`, the failure -/
theorem clampTerm_diff_pos_of_failure {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    {t₀ : ℝ} (ht : E π X < t₀) (hfail : ∑ w ∈ F.estEvent X t₀, π w * (X w - t₀) < 0) :
    ∃ α β : ℝ, α < β ∧ 0 < pieceTerm π F X α β := by
  obtain ⟨α, β, hαβ, heα, hm, hout, hS⟩ := failure_data hπ ht hfail
  refine ⟨α, β, hαβ, ?_⟩
  unfold pieceTerm
  rw [clamp_eq_left heα]
  have hBU : ∑ w, π w * ((clamp α β (E (F.P w) X) - X w) ^ 2 - (α - X w) ^ 2) =
      ∑ w ∈ F.estEvent X β, π w * ((β - X w) ^ 2 - (α - X w) ^ 2) := by
    rw [← sum_filter_add_sum_filter_not univ (fun w => w ∈ F.estEvent X β)]
    have h1 : univ.filter (fun w => w ∈ F.estEvent X β) = F.estEvent X β := by ext w; simp
    have h2 : ∑ w ∈ univ.filter (fun w => ¬ w ∈ F.estEvent X β),
        π w * ((clamp α β (E (F.P w) X) - X w) ^ 2 - (α - X w) ^ 2) = 0 := by
      apply sum_eq_zero
      intro w hw
      rw [clamp_eq_left (hout w (mem_filter.1 hw).2)]
      ring
    rw [h1, h2, add_zero]
    apply sum_congr rfl
    intro w hw
    rw [clamp_eq_right hαβ.le (Frame.mem_estEvent.1 hw)]
  rw [hBU]
  have hval : ∑ w ∈ F.estEvent X β, π w * ((β - X w) ^ 2 - (α - X w) ^ 2) =
      (β - α) * ((α + β) * mass π (F.estEvent X β) - 2 * ∑ w ∈ F.estEvent X β, π w * X w) := by
    have : ∀ w, π w * ((β - X w) ^ 2 - (α - X w) ^ 2) =
        (β - α) * (α + β) * π w - (β - α) * 2 * (π w * X w) := by
      intro w; ring
    simp only [this]
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum]
    simp only [mass]
    ring
  rw [hval]
  apply mul_pos (by linarith)
  have : ∑ w ∈ F.estEvent X β, π w * X w < β * mass π (F.estEvent X β) :=
    lt_of_lt_of_le hS (mul_le_mul_of_nonneg_right hαβ.le hm.le)
  linarith

end

end Cleanroom.Lit.LitDdbAccuracyMm
