import Cleanroom.Corrigibility.CorrCautionPower.Witnesses

/-!
# `corr-caution-power` — composition: Taylor §3.3, additive cost, compounding `q⁻ⁿ`

* `Distr.prod2` — the binary product distribution (infrastructure; FAF's `Distr.prod` is over a
  factored space `Pt Ω`, used for the `n`-fold form).
* **(a) Additive cost composes** `prod2_quantilize_additive_cost_bound`: Taylor's Cost
  Independence bound, `E_{Q₁⊗Q₂}[c₁ + c₂] ≤ (1/q) E_{γ₁⊗γ₂}[c₁ + c₂]`.
* **(b) Compounding** `prod2_cost_bound_compound` (binary, any nonnegative cost, factor
  `1/(q₁q₂)`), `prod_cost_bound_compound` (`n`-fold over FAF's `Distr.prod`, factor `∏ 1/qᵢ`).
* **(c) Taylor's two-game example** (`twoGame_*`): independent `1/3`-quantilizers give
  `δ₂ ⊗ δ₂`, cost `1`; the base pays `1/9`; the joint `1/3`-quantilizer of `γ ⊗ γ` ranked by
  `a₁ + a₂` under *any* compatible tie-break is uniform on `{(2,2), (2,1), (1,2)}` and pays
  `1/3`; the cost has no additive decomposition (`twoGame_cost_not_additive`); `1 = 9 · (1/9)`
  shows (b) tight at `n = 2`.
* **(d1) Sharpness for every `n`** `nGame_sharp`: the `n`-game family attains `q⁻ⁿ` (`3ⁿ`).
* **(d2)** `prod2_quantilize_not_quantilizer`: `Q_{3/4}[uniform Fin 2] ⊗ Q_{3/4}[…]` is not a
  quantilizer of the product base under any tie-break at any level.
* **(d3), the "if" direction refuted** `d3_no_split_not_joint`: with `U = (0, 1, 10)`, uniform,
  `q = 2/3` (no atom split — the boundary is an atom edge), `Q ⊗ Q` is not the `q²`-quantilizer
  of `γ ⊗ γ` under any order compatible with `U(a₁) + U(a₂)`.

Sources: [[corr-wf14-inventory]] 097, 112; [[corr-wf14-2-inventory]] 2-038, 2-088 →
Taylor 2016 §3.3 (l. 171–191); `caution-final.md` S5(a) (l. 69), proof §5 (l. 129);
`caution-adversary.md` A5.1 (l. 47); `plan/formal.md` l. 209.
-/

namespace Cleanroom.Corrigibility.CorrCautionPower

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect expect_const

/-! ## The binary product distribution -/

/-- The product `μ ⊗ ν` of two finite distributions (binary form of FAF's `Distr.prod`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def Distr.prod2 {A B : Type*} [Fintype A] [Fintype B] (μ : Distr A) (ν : Distr B) :
    Distr (A × B) where
  mass p := μ.mass p.1 * ν.mass p.2
  nonneg p := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, ν.sum_eq_one, mul_one, μ.sum_eq_one]

section Prod2

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Mass of the product. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma Distr.prod2_mass (μ : Distr A) (ν : Distr B) (p : A × B) :
    (Distr.prod2 μ ν).mass p = μ.mass p.1 * ν.mass p.2 := rfl

/-- Marginalizing a first-coordinate function. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_prod2_fst (μ : Distr A) (ν : Distr B) (c : A → ℝ) :
    expect (Distr.prod2 μ ν) (fun p => c p.1) = expect μ c := by
  unfold expect
  rw [Fintype.sum_prod_type]
  simp only [Distr.prod2_mass]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_mul, ← mul_sum, ν.sum_eq_one]; ring

/-- Marginalizing a second-coordinate function. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_prod2_snd (μ : Distr A) (ν : Distr B) (c : B → ℝ) :
    expect (Distr.prod2 μ ν) (fun p => c p.2) = expect ν c := by
  unfold expect
  rw [Fintype.sum_prod_type_right]
  simp only [Distr.prod2_mass]
  refine sum_congr rfl fun b _ => ?_
  rw [← sum_mul, ← sum_mul, μ.sum_eq_one]; ring

/-- An additive cost has additive expectation under a product.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 §3.3 Cost Independence (l. 183)
Kind: L
Fidelity: exact -/
lemma expect_prod2_add (μ : Distr A) (ν : Distr B) (c₁ : A → ℝ) (c₂ : B → ℝ) :
    expect (Distr.prod2 μ ν) (fun p => c₁ p.1 + c₂ p.2) = expect μ c₁ + expect ν c₂ := by
  rw [show (fun p : A × B => c₁ p.1 + c₂ p.2) = fun p => (fun p : A × B => c₁ p.1) p
      + (fun p : A × B => c₂ p.2) p from rfl, expect_add, expect_prod2_fst, expect_prod2_snd]

/-- Expectation of a point indicator is the mass of the point.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_indicator_point {C : Type*} [Fintype C] [DecidableEq C] (μ : Distr C) (c₀ : C) :
    expect μ (fun c => if c = c₀ then 1 else 0) = μ.mass c₀ := by
  unfold expect
  simp [mul_ite, sum_ite_eq']

/-! ## (a) Additive cost composes; (b) compounding -/

/-- **Taylor's Cost Independence bound (T4(a)).** For bases `γ₁, γ₂`, the same `q`, and an
additive cost `c(a₁, a₂) = c₁(a₁) + c₂(a₂)` with `cᵢ ≥ 0`: independent `q`-quantilizers pay at
most `(1/q)` times the base — no exponential blow-up. Lemma 1 twice.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 §3.3 Cost Independence Assumption (l. 183–185); [[corr-wf14-inventory]] 097 / caution-final.md S5(a) (l. 69)
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem prod2_quantilize_additive_cost_bound [LinearOrder A] [LinearOrder B] (γ₁ : Distr A)
    (γ₂ : Distr B) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (c₁ : A → ℝ) (c₂ : B → ℝ)
    (hc₁ : ∀ a, 0 ≤ c₁ a) (hc₂ : ∀ b, 0 ≤ c₂ b) :
    expect (Distr.prod2 (quantilize γ₁ q hq hq1) (quantilize γ₂ q hq hq1)) (fun p => c₁ p.1 + c₂ p.2)
      ≤ (1 / q) * expect (Distr.prod2 γ₁ γ₂) (fun p => c₁ p.1 + c₂ p.2) := by
  rw [expect_prod2_add, expect_prod2_add, mul_add]
  exact add_le_add (quantilize_cost_bound γ₁ hq hq1 c₁ hc₁) (quantilize_cost_bound γ₂ hq hq1 c₂ hc₂)

/-- **Compounding, binary (T4(b)).** If `Qᵢ ≤ γᵢ/qᵢ` pointwise, then for *any* nonnegative cost
on the product (no additivity), `E_{Q₁⊗Q₂}[c] ≤ (1/(q₁q₂)) E_{γ₁⊗γ₂}[c]`.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 §3.3 ("This cost blowup increases exponentially with `n`", l. 191)
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem prod2_cost_bound_compound (γ₁ Q₁ : Distr A) (γ₂ Q₂ : Distr B) {q₁ q₂ : ℝ}
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hQ₁ : ∀ a, Q₁.mass a ≤ γ₁.mass a / q₁)
    (hQ₂ : ∀ b, Q₂.mass b ≤ γ₂.mass b / q₂) (c : A × B → ℝ) (hc : ∀ p, 0 ≤ c p) :
    expect (Distr.prod2 Q₁ Q₂) c ≤ (1 / (q₁ * q₂)) * expect (Distr.prod2 γ₁ γ₂) c := by
  unfold expect
  rw [mul_sum]
  refine sum_le_sum fun p _ => ?_
  simp only [Distr.prod2_mass]
  rw [show 1 / (q₁ * q₂) * (γ₁.mass p.1 * γ₂.mass p.2 * c p)
      = (γ₁.mass p.1 / q₁) * (γ₂.mass p.2 / q₂) * c p by field_simp]
  refine mul_le_mul_of_nonneg_right ?_ (hc p)
  exact mul_le_mul (hQ₁ p.1) (hQ₂ p.2) (Q₂.nonneg _) (div_nonneg (γ₁.nonneg _) hq₁.le)

/-- **Compounding for two quantilizers at the same `q`:** factor `q⁻²`.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 §3.3 (l. 191)
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem prod2_quantilize_compound [LinearOrder A] [LinearOrder B] (γ₁ : Distr A) (γ₂ : Distr B)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (c : A × B → ℝ) (hc : ∀ p, 0 ≤ c p) :
    expect (Distr.prod2 (quantilize γ₁ q hq hq1) (quantilize γ₂ q hq hq1)) c
      ≤ (1 / q ^ 2) * expect (Distr.prod2 γ₁ γ₂) c := by
  rw [sq]
  exact prod2_cost_bound_compound γ₁ _ γ₂ _ hq hq (qmass_le γ₁ hq) (qmass_le γ₂ hq) c hc

end Prod2

/-- **Compounding, `n`-fold over FAF's `Distr.prod` (T4(b), stretch).** For per-factor
distributions `Qᵢ ≤ pᵢ/qᵢ` pointwise and any nonnegative cost on the factored space,
`E_{⊗Q}[c] ≤ (∏ᵢ 1/qᵢ) E_{⊗p}[c]`.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 §3.3 (l. 191)
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem prod_cost_bound_compound {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] (p Q : ∀ i, Distr (Ω i)) (q : I → ℝ) (hq : ∀ i, 0 < q i)
    (hQ : ∀ i a, (Q i).mass a ≤ (p i).mass a / q i) (c : Pt Ω → ℝ) (hc : ∀ ω, 0 ≤ c ω) :
    expect (Distr.prod Q) c ≤ (∏ i, 1 / q i) * expect (Distr.prod p) c := by
  unfold expect
  rw [mul_sum]
  refine sum_le_sum fun ω _ => ?_
  simp only [Distr.prod_mass]
  have hprod : (∏ i, 1 / q i) * ∏ i, (p i).mass (ω i) = ∏ i, (p i).mass (ω i) / q i := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun i _ => by ring
  rw [← mul_assoc, hprod]
  refine mul_le_mul_of_nonneg_right ?_ (hc ω)
  exact prod_le_prod (fun i _ => (Q i).nonneg _) (fun i _ => hQ i (ω i))

/-! ## (c) Taylor's two-game example -/

section TwoGame

/-- The utility `U(a) = a` on `Fin 3` (the agent "gains that much utility").
Source: [[corr-refs-inventory]] 065 / Taylor 2016 §3.3 (l. 176, `Uᵢ(o) = o`)
Kind: D
Fidelity: exact -/
noncomputable def idU : Fin 3 → ℝ := fun a => (a : ℕ)

/-- The natural order is compatible with `idU`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma idU_compatible : Compatible idU := fun a b hab => by
  simp only [idU]; exact_mod_cast (Fin.lt_def.mp hab).le

/-- The joint utility `U(a₁, a₂) = a₁ + a₂`.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 §3.3 (l. 178, `U(o₁, …, oₙ) = ∑ Uᵢ(oᵢ)`)
Kind: D
Fidelity: exact -/
noncomputable def sumU : Fin 3 × Fin 3 → ℝ := fun p => idU p.1 + idU p.2

/-- Taylor's cost: `1` iff the pair is `(2, 2)`.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 §3.3 (l. 181)
Kind: D
Fidelity: exact -/
noncomputable def twoGameCost : Fin 3 × Fin 3 → ℝ := fun p => if p = (2, 2) then 1 else 0

/-- The uniform mass on `Fin 3 × Fin 3` is `1/9`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma uniform_mass_fin3sq (p : Fin 3 × Fin 3) :
    (Distr.uniform : Distr (Fin 3 × Fin 3)).mass p = 9⁻¹ := by
  simp [Distr.uniform, Fintype.card_prod]

/-- **Independent `1/3`-quantilizers play `(2, 2)` surely and pay `1`; the base pays `1/9`
(N+).** So per-step quantilization is `9 = (1/3)⁻²` times as costly as the base: (b) is tight
at `n = 2`.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 §3.3 (l. 181–191); [[corr-wf14-2-inventory]] 2-038 / caution-adversary.md A5.1 (l. 47)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem twoGame_independent :
    expect (Distr.prod2 (quantilize (Distr.uniform : Distr (Fin 3)) (1 / 3) (by norm_num) (by norm_num))
        (quantilize (Distr.uniform : Distr (Fin 3)) (1 / 3) (by norm_num) (by norm_num))) twoGameCost = 1 ∧
    expect (Distr.prod2 (Distr.uniform : Distr (Fin 3)) Distr.uniform) twoGameCost = 1 / 9 := by
  obtain ⟨-, -, h2⟩ := taylor3_maximizer (q := 1 / 3) (by norm_num) le_rfl
  constructor
  · unfold twoGameCost
    rw [expect_indicator_point, Distr.prod2_mass]
    simp only [h2, mul_one]
  · unfold twoGameCost
    rw [expect_indicator_point, Distr.prod2_mass, uniform_mass_fin]
    norm_num

/-- **The joint `1/3`-quantilizer is uniform on the top three pairs, under any compatible
tie-break (N+).** For every linear order on `Fin 3 × Fin 3` compatible with `a₁ + a₂`:
`Q(2,2) = Q(2,1) = Q(1,2) = 1/3` and every pair with `a₁ + a₂ ≤ 2` has mass `0`; hence the
joint quantilizer pays `1/3` — Lemma 1 on the product type is tight here.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 §3.3 and Figure 2 (l. 181–191)
Kind: N+
Fidelity: exact (any compatible tie-break, as the paper's "uniformly sample from the top third")
Hyps: none -/
theorem twoGame_joint (o : LinearOrder (Fin 3 × Fin 3)) (hU : @Compatible _ o sumU) :
    (@quantilize _ _ o Distr.uniform (1 / 3) (by norm_num) (by norm_num)).mass (2, 2) = 1 / 3 ∧
    (@quantilize _ _ o Distr.uniform (1 / 3) (by norm_num) (by norm_num)).mass (2, 1) = 1 / 3 ∧
    (@quantilize _ _ o Distr.uniform (1 / 3) (by norm_num) (by norm_num)).mass (1, 2) = 1 / 3 ∧
    (∀ p, sumU p ≤ 2 → (@quantilize _ _ o Distr.uniform (1 / 3) (by norm_num) (by norm_num)).mass p = 0) ∧
    expect (@quantilize _ _ o Distr.uniform (1 / 3) (by norm_num) (by norm_num)) twoGameCost = 1 / 3 := by
  letI := o
  -- the weak-upper masses at levels 4 and 3, and the strict-upper mass above level 2
  have h3 : ∑ b ∈ univ.filter (fun b => (3 : ℝ) ≤ sumU b), (Distr.uniform : Distr (Fin 3 × Fin 3)).mass b
      = 1 / 3 := by
    simp only [sum_filter, Fintype.sum_prod_type, Fin.sum_univ_three, uniform_mass_fin3sq, sumU, idU]
    norm_num
  have full : ∀ p, aboveEq (Distr.uniform : Distr (Fin 3 × Fin 3)) p ≤ 1 / 3 →
      (quantilize Distr.uniform (1 / 3) (by norm_num) (by norm_num)).mass p = 1 / 3 := by
    intro p hp
    rw [quantilize_mass, qmass_of_aboveEq_le _ hp, uniform_mass_fin3sq]; norm_num
  have h22 : aboveEq (Distr.uniform : Distr (Fin 3 × Fin 3)) (2, 2) ≤ 1 / 3 := by
    refine (aboveEq_le_weakAbove _ hU _).trans ?_
    simp only [sum_filter, Fintype.sum_prod_type, Fin.sum_univ_three, uniform_mass_fin3sq, sumU, idU]
    norm_num
  have h21 : aboveEq (Distr.uniform : Distr (Fin 3 × Fin 3)) (2, 1) ≤ 1 / 3 := by
    refine (aboveEq_le_weakAbove _ hU _).trans ?_
    simp only [sum_filter, Fintype.sum_prod_type, Fin.sum_univ_three, uniform_mass_fin3sq, sumU, idU]
    norm_num
  have h12 : aboveEq (Distr.uniform : Distr (Fin 3 × Fin 3)) (1, 2) ≤ 1 / 3 := by
    refine (aboveEq_le_weakAbove _ hU _).trans ?_
    simp only [sum_filter, Fintype.sum_prod_type, Fin.sum_univ_three, uniform_mass_fin3sq, sumU, idU]
    norm_num
  have hlow : ∀ p, sumU p ≤ 2 →
      (quantilize Distr.uniform (1 / 3) (by norm_num) (by norm_num)).mass p = 0 := by
    intro p hp
    rw [quantilize_mass, qmass_of_le_above]
    refine le_trans ?_ (strictAbove_le_above _ hU p)
    refine le_trans (le_of_eq h3.symm) ?_
    refine sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => (Distr.uniform).nonneg b
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    linarith
  refine ⟨full _ h22, full _ h21, full _ h12, hlow, ?_⟩
  unfold twoGameCost
  rw [expect_indicator_point]
  exact full _ h22

/-- **The two-game cost has no additive decomposition (N+):** there are no `c₁ c₂ : Fin 3 → ℝ`
with `c(a₁, a₂) = c₁(a₁) + c₂(a₂)` — so no per-step bound exists to be summed, and the
"per-step bounds sum to `0`" of the source is the statement that every single-action marginal
of this cost is `0` while the realized cost is `1`.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 §3.3 (l. 181–191); [[corr-wf14-inventory]] 097 / caution-final.md S5(a) (l. 69)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem twoGame_cost_not_additive :
    ¬ ∃ c₁ c₂ : Fin 3 → ℝ, ∀ p, twoGameCost p = c₁ p.1 + c₂ p.2 := by
  rintro ⟨c₁, c₂, h⟩
  have h22 := h (2, 2)
  have h21 := h (2, 1)
  have h12 := h (1, 2)
  have h11 := h (1, 1)
  simp [twoGameCost] at h22 h21 h12 h11
  linarith

end TwoGame

/-! ## (d1) Sharpness for every `n` -/

section NGame

variable (n : ℕ)

/-- The all-top point `(2, …, 2)` of the `n`-game factored space.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def allTop : Pt (fun _ : Fin n => Fin 3) := fun _ => 2

/-- The `n`-game cost: `1` iff every game plays the top action.
Source: [[corr-wf14-2-inventory]] 2-088 / caution-final.md S5(a) (l. 69, "compounding `q⁻ⁿ`")
Kind: D
Fidelity: exact -/
noncomputable def nGameCost : Pt (fun _ : Fin n => Fin 3) → ℝ :=
  fun ω => if ω = allTop n then 1 else 0

/-- **(b) is sharp for every `n` (N+):** independent `1/3`-quantilizers of `n` uniform three-action
games pay `1`, the product base pays `(1/3)ⁿ`; the ratio `3ⁿ = (1/3)⁻ⁿ` attains the `n`-fold
compounding bound.
Source: [[corr-wf14-2-inventory]] 2-088 / plan/formal.md l. 209; Taylor 2016 §3.3 (l. 191)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem nGame_sharp :
    expect (Distr.prod (fun _ : Fin n =>
        quantilize (Distr.uniform : Distr (Fin 3)) (1 / 3) (by norm_num) (by norm_num))) (nGameCost n) = 1 ∧
    expect (Distr.prod (fun _ : Fin n => (Distr.uniform : Distr (Fin 3)))) (nGameCost n) = (1 / 3) ^ n := by
  obtain ⟨-, -, h2⟩ := taylor3_maximizer (q := 1 / 3) (by norm_num) le_rfl
  constructor
  · unfold nGameCost
    rw [expect_indicator_point, Distr.prod_mass]
    simp only [allTop, prod_const, card_univ, Fintype.card_fin]
    rw [h2, one_pow]
  · unfold nGameCost
    rw [expect_indicator_point, Distr.prod_mass]
    simp [allTop, uniform_mass_fin, prod_const]

end NGame

/-! ## (d2) The product of two quantilizers is not a quantilizer of the product base -/

section D2

/-- `Q_{3/4}` of the uniform base on `Fin 2` is `(1/3, 2/3)`.
Source: [[corr-wf14-2-inventory]] 2-088
Kind: L
Fidelity: exact -/
lemma quantilize_fin2_three_quarters :
    (quantilize (Distr.uniform : Distr (Fin 2)) (3 / 4) (by norm_num) (by norm_num)).mass 0 = 1 / 3 ∧
    (quantilize (Distr.uniform : Distr (Fin 2)) (3 / 4) (by norm_num) (by norm_num)).mass 1 = 2 / 3 := by
  have h1 : above (Distr.uniform : Distr (Fin 2)) 1 = 0 := above_last (n := 1) _
  have h0 : above (Distr.uniform : Distr (Fin 2)) 0 = 1 / 2 := by
    simp only [above, sum_filter, Fin.sum_univ_two, uniform_mass_fin, Fin.lt_def]
    norm_num
  constructor
  · rw [quantilize_mass, qmass, aboveEq_eq, h0, uniform_mass_fin]; norm_num
  · rw [quantilize_mass, qmass, aboveEq_eq, h1, uniform_mass_fin]; norm_num

/-- **The product of two quantilizers is in general not a quantilizer of the product base
(N+).** `Q_{3/4}[uniform Fin 2] ⊗ Q_{3/4}[uniform Fin 2] = (1/9, 2/9, 2/9, 4/9)` is not
`Q_{q'}[uniform (Fin 2 × Fin 2)]` for any tie-break order and any `q' ∈ (0, 1]`: a
quantilizer has at most one partial atom (`partial_unique`) and its full atoms all carry the
same mass `(1/4)/q'`, but three of the four product masses are distinct and positive.
Source: [[corr-wf14-2-inventory]] 2-088 / plan/formal.md l. 209 ("or the witness that no additive law exists")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem prod2_quantilize_not_quantilizer (o : LinearOrder (Fin 2 × Fin 2)) {q' : ℝ}
    (hq' : 0 < q') (hq1' : q' ≤ 1) :
    @quantilize _ _ o Distr.uniform q' hq' hq1' ≠
      Distr.prod2 (quantilize (Distr.uniform : Distr (Fin 2)) (3 / 4) (by norm_num) (by norm_num))
        (quantilize (Distr.uniform : Distr (Fin 2)) (3 / 4) (by norm_num) (by norm_num)) := by
  letI := o
  obtain ⟨h0, h1⟩ := quantilize_fin2_three_quarters
  intro heq
  have hm : ∀ p, (quantilize (Distr.uniform : Distr (Fin 2 × Fin 2)) q' hq' hq1').mass p
      = (quantilize (Distr.uniform : Distr (Fin 2)) (3 / 4) (by norm_num) (by norm_num)).mass p.1 *
        (quantilize (Distr.uniform : Distr (Fin 2)) (3 / 4) (by norm_num) (by norm_num)).mass p.2 := by
    intro p; rw [heq]; rfl
  have hu : ∀ p : Fin 2 × Fin 2, (Distr.uniform : Distr (Fin 2 × Fin 2)).mass p = 4⁻¹ := by
    intro p; simp [Distr.uniform, Fintype.card_prod]
  have m00 := hm (0, 0); have m01 := hm (0, 1); have m11 := hm (1, 1)
  simp only [h0, h1, quantilize_mass] at m00 m01 m11
  have t00 := qmass_trichotomy (Distr.uniform : Distr (Fin 2 × Fin 2)) q' (0, 0)
  have t01 := qmass_trichotomy (Distr.uniform : Distr (Fin 2 × Fin 2)) q' (0, 1)
  have t11 := qmass_trichotomy (Distr.uniform : Distr (Fin 2 × Fin 2)) q' (1, 1)
  rw [m00, hu] at t00
  rw [m01, hu] at t01
  rw [m11, hu] at t11
  rcases t00 with f00 | z00 | p00
  · rcases t01 with f01 | z01 | p01
    · rw [← f01] at f00; norm_num at f00
    · norm_num at z01
    · rcases t11 with f11 | z11 | p11
      · rw [← f11] at f00; norm_num at f00
      · norm_num at z11
      · exact absurd (partial_unique _ p01 p11) (by decide)
  · norm_num at z00
  · rcases t01 with f01 | z01 | p01
    · rcases t11 with f11 | z11 | p11
      · rw [← f11] at f01; norm_num at f01
      · norm_num at z11
      · exact absurd (partial_unique _ p00 p11) (by decide)
    · norm_num at z01
    · exact absurd (partial_unique _ p00 p01) (by decide)

end D2

/-! ## (d3) The "no split ⟹ product law" direction, refuted -/

section D3

/-- The utility `(0, 1, 10)` on `Fin 3`.
Source: none: witness for [[corr-wf14-2-inventory]] 2-088 (d3)
Kind: D
Fidelity: n/a -/
noncomputable def d3U : Fin 3 → ℝ := ![0, 1, 10]

/-- The joint utility `U(a₁) + U(a₂)`. Source: none: witness. Kind: D. Fidelity: n/a -/
noncomputable def d3SumU : Fin 3 × Fin 3 → ℝ := fun p => d3U p.1 + d3U p.2

/-- `Q_{2/3}` of the uniform base on `Fin 3` is `(0, 1/2, 1/2)`, and the slice boundary `2/3` is
an atom edge: no atom is split.
Source: none: witness for 2-088 (d3)
Kind: L
Fidelity: exact -/
lemma quantilize_fin3_two_thirds :
    (quantilize (Distr.uniform : Distr (Fin 3)) (2 / 3) (by norm_num) (by norm_num)).mass 0 = 0 ∧
    (quantilize (Distr.uniform : Distr (Fin 3)) (2 / 3) (by norm_num) (by norm_num)).mass 1 = 1 / 2 ∧
    (quantilize (Distr.uniform : Distr (Fin 3)) (2 / 3) (by norm_num) (by norm_num)).mass 2 = 1 / 2 ∧
    (∀ a, ¬ (above (Distr.uniform : Distr (Fin 3)) a < 2 / 3 ∧
      2 / 3 < aboveEq (Distr.uniform : Distr (Fin 3)) a)) := by
  obtain ⟨h0, h1, h2⟩ := above_uniform_fin3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [quantilize_mass, qmass_of_le_above _ (by rw [h0])]
  · rw [quantilize_mass, qmass, aboveEq_eq, h1, uniform_mass_fin]; norm_num
  · rw [quantilize_mass, qmass, aboveEq_eq, h2, uniform_mass_fin]; norm_num
  · intro a
    fin_cases a
    · show ¬ (above (Distr.uniform : Distr (Fin 3)) 0 < 2 / 3 ∧
        2 / 3 < aboveEq (Distr.uniform : Distr (Fin 3)) 0)
      rw [aboveEq_eq, h0, uniform_mass_fin]; norm_num
    · show ¬ (above (Distr.uniform : Distr (Fin 3)) 1 < 2 / 3 ∧
        2 / 3 < aboveEq (Distr.uniform : Distr (Fin 3)) 1)
      rw [aboveEq_eq, h1, uniform_mass_fin]; norm_num
    · show ¬ (above (Distr.uniform : Distr (Fin 3)) 2 < 2 / 3 ∧
        2 / 3 < aboveEq (Distr.uniform : Distr (Fin 3)) 2)
      rw [aboveEq_eq, h2, uniform_mass_fin]; norm_num

/-- **(d3)'s "if" direction is false (N+).** With `U = (0, 1, 10)`, uniform base and `q = 2/3`
(no atom split in either factor), `Q_q ⊗ Q_q` puts `1/4` on `(1, 1)`, but for every order on
`Fin 3 × Fin 3` compatible with `U(a₁) + U(a₂)` the `q²`-quantilizer of the product base puts
`0` there: the five pairs of utility `> 2` carry mass `5/9 > 4/9 = q²` above `(1, 1)`. So the
product of quantilizers is not the `q²`-quantilizer of the product under the sum ranking even
when no boundary splits an atom; the exact law 2-088 asks for does not exist in this form.
Source: [[corr-wf14-2-inventory]] 2-088 / plan/formal.md l. 209
Kind: N+
Fidelity: exact
Hyps: none -/
theorem d3_no_split_not_joint (o : LinearOrder (Fin 3 × Fin 3)) (hU : @Compatible _ o d3SumU) :
    (Distr.prod2 (quantilize (Distr.uniform : Distr (Fin 3)) (2 / 3) (by norm_num) (by norm_num))
        (quantilize (Distr.uniform : Distr (Fin 3)) (2 / 3) (by norm_num) (by norm_num))).mass (1, 1) = 1 / 4 ∧
    (@quantilize _ _ o Distr.uniform (4 / 9) (by norm_num) (by norm_num)).mass (1, 1) = 0 := by
  letI := o
  obtain ⟨-, h1, -, -⟩ := quantilize_fin3_two_thirds
  constructor
  · rw [Distr.prod2_mass]; simp only [h1]; norm_num
  · rw [quantilize_mass, qmass_of_le_above]
    refine le_trans ?_ (strictAbove_le_above _ hU (1, 1))
    have : ∑ b ∈ univ.filter (fun b => d3SumU (1, 1) < d3SumU b),
        (Distr.uniform : Distr (Fin 3 × Fin 3)).mass b = 5 / 9 := by
      simp only [sum_filter, Fintype.sum_prod_type, Fin.sum_univ_three, uniform_mass_fin3sq,
        d3SumU, d3U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      norm_num
    rw [this]; norm_num

end D3

end Cleanroom.Corrigibility.CorrCautionPower
