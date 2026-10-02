import Cleanroom.Udt.UdtCondenseDd.Access

/-!
# `Cleanroom.Udt.UdtCondenseDd.Approx`: approximate factoring and utility-level approximate DD (T3, T4, T5)

Work package `udt-condense-dd`, targets T3 (the approximate factoring lemma, udt-rep-031), T4
(utility-level approximate DD in the fixed-observation and prediction-dependent-observation
regimes, udt-rep-032, 033) and T5 (DD with respect to the support, udt-rep-036). Source:
[[gap1-reframing-predictor-access]] §4 (the Lemma and Corollary) and §4(a).

All of this is reading (ii)-approximate of Gap 1 ([[gap1-reframing-predictor-access]] §2): family
statistical access, accuracy `δ` measured by the family's own observation law.

## The constant of T4(b), derived (mandate T4(b); findings §6.4; repair round 1)

The note asserts `|U(M₁) − U(M₂)| ≤ R (2δ + L · 2δ/γ)` for the prediction-dependent regime. Under
the reading of record — accuracy `δ` **under each mechanism's own observation law**
(ATTRIBUTION-UNVETTED: the note writes `Pr_{o ∼ D}` with `D` unsubscripted) — the proof gives

`|U(M₁) − U(M₂)| ≤ R · (2δ + tv(D₁, D₂)) ≤ R · (2δ + L · 2δ/γ)`,

**the note's constant exactly**: the total-variation distance enters **once**, through a pointwise
bound on `D₁(o) g₁(o) − D₂(o) g₂(o)` (`varying_sub_le`), and `tv ≤ L · |disSet| ≤ L · 2δ/γ` by the
counting bound under each own law. The package's first proof (audit round 1, both audits' B1) split
the difference into a fixed-law part and a change-of-law part and paid `tv` twice, giving
`R (2δ + 4Lδ/γ)` and wrongly putting the note's constant under suspicion; the sharp argument is the
r1 probe `NoteConstant.lean`'s, lifted here. `approxDD_varying_tv` is the total-variation form;
`approxDD_varying` is the closed form with the note's constant. The note's Lipschitz hypothesis is
single-step ("changing the prediction at one observation moves `D` by at most `L`");
`lipschitz_of_single_step` derives the Hamming form the theorems take from it (triangle inequality
`tv_triangle` + induction on the number of changed observations), so `approxDD_varying_single_step`
carries the note's hypothesis verbatim.

Total variation is defined once, as `tv D D' := ∑ o, max (D o − D' o) 0`, and shown equal to
`½ ∑ |D o − D' o|` (`tv_eq_half_sum_abs`).
-/

namespace Cleanroom.Udt.UdtCondenseDd

open Cleanroom.Udt.UdtPolicyCalc Finset

set_option linter.unusedSectionVars false

variable {M O A : Type} [Fintype O] [DecidableEq O] [DecidableEq A]

/-! ### Mass and counting lemmas -/

/-- Supporting lemma `mass_mono`: mass is monotone for non-negative weights.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_mono {w : O → ℝ} (hw : ∀ o, 0 ≤ w o) {S T : Finset O} (h : S ⊆ T) :
    mass w S ≤ mass w T :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun o _ _ => hw o

/-- Supporting lemma `mass_union_le`: the union bound.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_union_le {w : O → ℝ} (hw : ∀ o, 0 ≤ w o) (S T : Finset O) :
    mass w (S ∪ T) ≤ mass w S + mass w T := by
  unfold mass
  have h := Finset.sum_union_inter (s₁ := S) (s₂ := T) (f := w)
  have h0 : 0 ≤ ∑ o ∈ S ∩ T, w o := Finset.sum_nonneg fun o _ => hw o
  linarith

/-- **`γ · |S| ≤ mass(S)` when every weight is at least `γ`** — the counting step of the note's
proof, stated division-free.
Source: [[gap1-reframing-predictor-access]] §4 Lemma (proof, "`δ ≥ Pr_D(S_i) ≥ γ |S_i|`")
Kind: L
Fidelity: exact
Hyps: none -/
theorem mul_card_le_mass {w : O → ℝ} {γ : ℝ} (hγ : ∀ o, γ ≤ w o) (S : Finset O) :
    γ * S.card ≤ mass w S := by
  unfold mass
  have h := Finset.card_nsmul_le_sum S w γ fun o _ => hγ o
  rw [nsmul_eq_mul] at h
  linarith [h]

/-! ### T3: the approximate factoring lemma -/

/-- **Approximate factoring, per-mechanism accuracies** (the trivial generalization the mandate asks
to record): if `M₁` errs on `D`-mass `≤ δ₁` and `M₂` on `≤ δ₂`, two mechanisms with the same policy
disagree on `D`-mass `≤ δ₁ + δ₂`.
Source: [[gap1-reframing-predictor-access]] §4 Lemma (udt-rep-031), per-mechanism variant
Kind: P
Fidelity: stronger: per-mechanism accuracies
Hyps: (a) -/
theorem approxFactoring_mass' {p pol : M → O → A} (D : FinDist O) {δ₁ δ₂ : ℝ} {m₁ m₂ : M}
    (h₁ : mass D.w (errSet p pol m₁) ≤ δ₁) (h₂ : mass D.w (errSet p pol m₂) ≤ δ₂)
    (h : pol m₁ = pol m₂) : mass D.w (disSet p m₁ m₂) ≤ δ₁ + δ₂ :=
  (mass_mono D.nonneg (disSet_subset_union h)).trans
    ((mass_union_le D.nonneg _ _).trans (add_le_add h₁ h₂))

/-- **The approximate factoring lemma (T3, load-bearing 1), mass form**: accuracy `δ` under `D`
for every mechanism ⟹ two mechanisms with the same policy disagree on a set of `D`-mass `≤ 2δ`.
The honest replacement for the corpus's stipulation `isOptimalPredictor := factorsThroughPolicy`:
accuracy on a family is the premise, factoring its (approximate) consequence. `δ` is uniform over
mechanisms *under one law `D`*.
Source: [[gap1-reframing-predictor-access]] §4 Lemma, first bound (udt-rep-031)
Kind: P
Fidelity: exact
Hyps: (a) `hacc` (accuracy under the family's law) -/
theorem approxFactoring_mass {p pol : M → O → A} (D : FinDist O) {δ : ℝ}
    (hacc : ∀ m, mass D.w (errSet p pol m) ≤ δ) {m₁ m₂ : M} (h : pol m₁ = pol m₂) :
    mass D.w (disSet p m₁ m₂) ≤ 2 * δ := by
  have := approxFactoring_mass' D (hacc m₁) (hacc m₂) h
  linarith

/-- **The counting bound for one mechanism, division-free**: `γ · |err M| ≤ δ` when `D ≥ γ`
pointwise.
Source: [[gap1-reframing-predictor-access]] §4 Lemma (proof)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem card_errSet_le {p pol : M → O → A} (D : FinDist O) {δ γ : ℝ} (hγ : ∀ o, γ ≤ D.w o)
    (hacc : ∀ m, mass D.w (errSet p pol m) ≤ δ) (m : M) : γ * (errSet p pol m).card ≤ δ :=
  (mul_card_le_mass hγ _).trans (hacc m)

/-- **The approximate factoring lemma (T3), counting form, division-free**: if additionally
`D(o) ≥ γ` for every `o`, then `γ · |{o : p(M₁,o) ≠ p(M₂,o)}| ≤ 2δ`. Proved through the mass form
(`γ · |S| ≤ mass(S) ≤ 2δ`), so no sign condition on `γ` is needed here.
Source: [[gap1-reframing-predictor-access]] §4 Lemma, second bound (udt-rep-031)
Kind: P
Fidelity: exact (division-free form)
Hyps: (a) `hacc`, (a) `hγ` -/
theorem approxFactoring_card {p pol : M → O → A} (D : FinDist O) {δ γ : ℝ}
    (hacc : ∀ m, mass D.w (errSet p pol m) ≤ δ) (hγ : ∀ o, γ ≤ D.w o) {m₁ m₂ : M}
    (h : pol m₁ = pol m₂) : γ * (disSet p m₁ m₂).card ≤ 2 * δ :=
  (mul_card_le_mass hγ _).trans (approxFactoring_mass D hacc h)

/-- **The counting form with the division** (`0 < γ`): the predictions disagree on at most `2δ/γ`
observations — the tremble rate `γ` of the rarest branch in the denominator.
Source: [[gap1-reframing-predictor-access]] §4 Lemma, second bound (udt-rep-031)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem approxFactoring_card_div {p pol : M → O → A} (D : FinDist O) {δ γ : ℝ}
    (hacc : ∀ m, mass D.w (errSet p pol m) ≤ δ) (hγ : ∀ o, γ ≤ D.w o) (hγpos : 0 < γ)
    {m₁ m₂ : M} (h : pol m₁ = pol m₂) : ((disSet p m₁ m₂).card : ℝ) ≤ 2 * δ / γ := by
  rw [le_div_iff₀ hγpos, mul_comm]
  exact approxFactoring_card D hacc hγ h

/-! ### Total variation -/

/-- **Total variation** between two finite distributions, as the positive-part sum
`∑ o, max (D o − D' o) 0`; equal to `½ ∑ o, |D o − D' o|` (`tv_eq_half_sum_abs`).
Source: [[gap1-reframing-predictor-access]] §4 Corollary ("total-variation distance"); none: infrastructure
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def tv (D D' : FinDist O) : ℝ := ∑ o, max (D.w o - D'.w o) 0

/-- Supporting lemma `sum_sub_eq_zero`: two distributions have the same total mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_sub_eq_zero (D D' : FinDist O) : ∑ o, (D.w o - D'.w o) = 0 := by
  rw [Finset.sum_sub_distrib, D.sum_one, D'.sum_one, sub_self]

/-- Supporting lemma `max_eq_half_add_abs`: `max x 0 = (x + |x|) / 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem max_eq_half_add_abs (x : ℝ) : max x 0 = (x + |x|) / 2 := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, abs_of_nonpos h]; ring
  · rw [max_eq_left h, abs_of_nonneg h]; ring

/-- Supporting lemma `min_eq_sub_max`: `min x 0 = x − max x 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem min_eq_sub_max (x : ℝ) : min x 0 = x - max x 0 := by
  rcases le_total x 0 with h | h
  · rw [min_eq_left h, max_eq_right h, sub_zero]
  · rw [min_eq_right h, max_eq_left h, sub_self]

/-- **`tv = ½ ∑ |D o − D' o|`**: the positive-part sum is half the `ℓ¹` distance.
Source: none: infrastructure (mandate §3, "prove once")
Kind: L
Fidelity: exact
Hyps: none -/
theorem tv_eq_half_sum_abs (D D' : FinDist O) : tv D D' = (1 / 2) * ∑ o, |D.w o - D'.w o| := by
  unfold tv
  simp_rw [max_eq_half_add_abs]
  have hsplit : ∀ x : ℝ, (x + |x|) / 2 = (1 / 2) * x + (1 / 2) * |x| := fun x => by ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_sub_eq_zero, mul_zero,
    zero_add]

/-- Supporting lemma `tv_nonneg`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem tv_nonneg (D D' : FinDist O) : 0 ≤ tv D D' :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

/-- Supporting lemma `tv_symm`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem tv_symm (D D' : FinDist O) : tv D D' = tv D' D := by
  rw [tv_eq_half_sum_abs, tv_eq_half_sum_abs]
  congr 1
  exact Finset.sum_congr rfl fun o _ => abs_sub_comm _ _

/-- Supporting lemma `tv_self`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem tv_self (D : FinDist O) : tv D D = 0 := by
  unfold tv
  simp

/-- **Mass transfer**: the mass of any event under `D` exceeds its mass under `D'` by at most
`tv D D'`. This is how an accuracy bound known under one law is carried to another.
Source: none: infrastructure (mandate T4(b), "bounded only through … `tv D₁ D₂`")
Kind: L
Fidelity: exact
Hyps: none -/
theorem mass_sub_mass_le_tv (D D' : FinDist O) (S : Finset O) :
    mass D.w S - mass D'.w S ≤ tv D D' := by
  unfold mass tv
  rw [← Finset.sum_sub_distrib]
  calc ∑ o ∈ S, (D.w o - D'.w o) ≤ ∑ o ∈ S, max (D.w o - D'.w o) 0 :=
        Finset.sum_le_sum fun o _ => le_max_left _ _
    _ ≤ ∑ o, max (D.w o - D'.w o) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun o _ _ => le_max_right _ _

/-- **The total-variation bound for a bounded integrand**: if `f` takes values in an interval of
width `R`, `|∑ o, (D o − D' o) f o| ≤ R · tv D D'`. (Centring at `c` costs nothing because the
weights of `D − D'` sum to zero; then the positive and negative parts of `D − D'` each carry mass
`tv D D'`.)
Source: none: infrastructure (mandate §3 `tv_bound`)
Kind: P
Fidelity: exact
Hyps: none -/
theorem tv_bound (D D' : FinDist O) {f : O → ℝ} {c R : ℝ} (hf : ∀ o, f o ∈ Set.Icc c (c + R)) :
    |∑ o, (D.w o - D'.w o) * f o| ≤ R * tv D D' := by
  have h0 : ∑ o, (D.w o - D'.w o) = 0 := sum_sub_eq_zero D D'
  have hred : ∑ o, (D.w o - D'.w o) * f o = ∑ o, (D.w o - D'.w o) * (f o - c) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h0, zero_mul, sub_zero]
  have hg0 : ∀ o, 0 ≤ f o - c := fun o => by linarith [(hf o).1]
  have hgR : ∀ o, f o - c ≤ R := fun o => by linarith [(hf o).2]
  rw [hred]
  refine abs_le.2 ⟨?_, ?_⟩
  · -- lower bound: `∑ x g ≥ ∑ (min x 0) g ≥ R ∑ min x 0 = −R · tv`
    have hmin : ∑ o, min (D.w o - D'.w o) 0 = - tv D D' := by
      unfold tv
      simp_rw [min_eq_sub_max]
      rw [Finset.sum_sub_distrib, h0, zero_sub]
    have h1 : ∑ o, min (D.w o - D'.w o) 0 * R ≤ ∑ o, (D.w o - D'.w o) * (f o - c) :=
      Finset.sum_le_sum fun o _ =>
        (mul_le_mul_of_nonpos_left (hgR o) (min_le_right _ 0)).trans
          (mul_le_mul_of_nonneg_right (min_le_left _ 0) (hg0 o))
    rw [← Finset.sum_mul, hmin] at h1
    linarith
  · -- upper bound: `∑ x g ≤ ∑ (max x 0) g ≤ R ∑ max x 0 = R · tv`
    have h1 : ∑ o, (D.w o - D'.w o) * (f o - c) ≤ ∑ o, max (D.w o - D'.w o) 0 * R :=
      Finset.sum_le_sum fun o _ =>
        (mul_le_mul_of_nonneg_right (le_max_left _ 0) (hg0 o)).trans
          (mul_le_mul_of_nonneg_left (hgR o) (le_max_right _ 0))
    rw [← Finset.sum_mul] at h1
    unfold tv
    linarith

/-! ### T4(a): the fixed-observation regime -/

/-- **The fixed-observation utility** `U(M) = ∑ o, D(o) · u(o, p(M,o), π_M(o))`.
Source: [[gap1-reframing-predictor-access]] §4 Corollary, fixed-observation regime (udt-rep-032)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def fixedUtility (D : FinDist O) (u : O → A → A → ℝ) (p pol : M → O → A) (m : M) : ℝ :=
  ∑ o, D.w o * u o (p m o) (pol m o)

/-- **Utility-level approximate DD, fixed observations (T4(a))**: with `u` in an interval of width
`R` and a shared policy, `|U(M₁) − U(M₂)| ≤ R · Pr_D(p(M₁,·) ≠ p(M₂,·))` — termwise, the summands
agree off the disagreement set.
Source: [[gap1-reframing-predictor-access]] §4 Corollary, fixed-observation regime (udt-rep-032)
Kind: P
Fidelity: exact
Hyps: (a) `hu` -/
theorem approxDD_fixed (D : FinDist O) (u : O → A → A → ℝ) {c R : ℝ}
    (hu : ∀ o a b, u o a b ∈ Set.Icc c (c + R)) {p pol : M → O → A} {m₁ m₂ : M}
    (h : pol m₁ = pol m₂) :
    |fixedUtility D u p pol m₁ - fixedUtility D u p pol m₂| ≤ R * mass D.w (disSet p m₁ m₂) := by
  unfold fixedUtility
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have hfilt : ∑ o ∈ disSet p m₁ m₂, D.w o * (u o (p m₁ o) (pol m₁ o) - u o (p m₂ o) (pol m₂ o)) =
      ∑ o, D.w o * (u o (p m₁ o) (pol m₁ o) - u o (p m₂ o) (pol m₂ o)) := by
    apply Finset.sum_filter_of_ne
    intro o _ hne heq
    apply hne
    rw [heq, h, sub_self, mul_zero]
  rw [← hfilt]
  calc |∑ o ∈ disSet p m₁ m₂, D.w o * (u o (p m₁ o) (pol m₁ o) - u o (p m₂ o) (pol m₂ o))|
      ≤ ∑ o ∈ disSet p m₁ m₂, |D.w o * (u o (p m₁ o) (pol m₁ o) - u o (p m₂ o) (pol m₂ o))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ o ∈ disSet p m₁ m₂, D.w o * R := by
        refine Finset.sum_le_sum fun o _ => ?_
        rw [abs_mul, abs_of_nonneg (D.nonneg o)]
        refine mul_le_mul_of_nonneg_left (abs_le.2 ⟨?_, ?_⟩) (D.nonneg o)
        · linarith [(hu o (p m₁ o) (pol m₁ o)).1, (hu o (p m₂ o) (pol m₂ o)).2]
        · linarith [(hu o (p m₁ o) (pol m₁ o)).2, (hu o (p m₂ o) (pol m₂ o)).1]
    _ = R * mass D.w (disSet p m₁ m₂) := by
        rw [mass, Finset.mul_sum]
        exact Finset.sum_congr rfl fun o _ => mul_comm _ _

/-- **T4(a) composed with T3**: under accuracy `δ`, `|U(M₁) − U(M₂)| ≤ 2δR` — approximate DD at
cost `2δR`, no `γ` anywhere.
Source: [[gap1-reframing-predictor-access]] §4 Corollary, fixed-observation regime (udt-rep-032)
Kind: C
Fidelity: exact
Hyps: (a) `hu`, (a) `hacc`; `hR : 0 ≤ R` is implied by `hu` whenever `O` and `A` are inhabited -/
theorem approxDD_fixed_of_accurate (D : FinDist O) (u : O → A → A → ℝ) {c R : ℝ} (hR : 0 ≤ R)
    (hu : ∀ o a b, u o a b ∈ Set.Icc c (c + R)) {p pol : M → O → A} {δ : ℝ}
    (hacc : ∀ m, mass D.w (errSet p pol m) ≤ δ) {m₁ m₂ : M} (h : pol m₁ = pol m₂) :
    |fixedUtility D u p pol m₁ - fixedUtility D u p pol m₂| ≤ 2 * δ * R := by
  have h1 := approxDD_fixed D u hu (p := p) h
  have h2 := mul_le_mul_of_nonneg_left (approxFactoring_mass D hacc h) hR
  linarith

/-! ### T4(b): the prediction-dependent-observation regime -/

/-- **The prediction-dependent utility** `U(M) = ∑ o, D_{p(M,·)}(o) · u(o, p(M,o), π_M(o))`: the
observation law `Dof q` is a function of the prediction profile `q` (transparent Newcomb: whether
you see a full box is set by the predictor's verdict).
Source: [[gap1-reframing-predictor-access]] §4 Corollary, prediction-dependent regime (udt-rep-033)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def varyingUtility (Dof : (O → A) → FinDist O) (u : O → A → A → ℝ) (p pol : M → O → A)
    (m : M) : ℝ :=
  ∑ o, (Dof (p m)).w o * u o (p m o) (pol m o)

/-- **The one-sided sharp bound** (supporting lemma for T4(b)): with `u` in an interval of width
`R` and a shared policy, `U(M₁) − U(M₂) ≤ R · (mass D₁ err₁ + mass D₂ err₂ + tv(D₁, D₂))`, where
`Dᵢ = Dof (p Mᵢ)` and `errᵢ = errSet p pol Mᵢ`. Pointwise after centring `u` at `c`: on `err₁` the
summand `D₁ g₁ − D₂ g₂` is at most `R · D₁(o)`; on `err₂ \ err₁` at most
`R · D₂(o) + R · (D₁(o) − D₂(o))⁺`; off both error sets the integrands agree and
`(D₁ − D₂) g ≤ R · (D₁ − D₂)⁺`. The total-variation term enters **once**. (Repair round 1: this is
the argument of the r1 audits' probe `NoteConstant.lean`; the package's first proof paid `tv` twice.)
Source: [[gap1-reframing-predictor-access]] §4 Corollary, prediction-dependent regime (udt-rep-033)
Kind: P
Fidelity: n/a (supporting; the headline is `approxDD_varying`)
Hyps: none -/
theorem varying_sub_le (Dof : (O → A) → FinDist O) (u : O → A → A → ℝ) {c R : ℝ}
    (hR : 0 ≤ R) (hu : ∀ o a b, u o a b ∈ Set.Icc c (c + R)) {p pol : M → O → A} {m₁ m₂ : M}
    (h : pol m₁ = pol m₂) :
    varyingUtility Dof u p pol m₁ - varyingUtility Dof u p pol m₂ ≤
      R * (mass (Dof (p m₁)).w (errSet p pol m₁) + mass (Dof (p m₂)).w (errSet p pol m₂) +
        tv (Dof (p m₁)) (Dof (p m₂))) := by
  set D₁ := Dof (p m₁) with hD₁
  set D₂ := Dof (p m₂) with hD₂
  -- centring at `c`
  have hcent : varyingUtility Dof u p pol m₁ - varyingUtility Dof u p pol m₂ =
      ∑ o, (D₁.w o * (u o (p m₁ o) (pol m₁ o) - c) - D₂.w o * (u o (p m₂ o) (pol m₂ o) - c)) := by
    unfold varyingUtility
    rw [← hD₁, ← hD₂]
    have e1 : ∑ o, D₁.w o * (u o (p m₁ o) (pol m₁ o) - c) =
        ∑ o, D₁.w o * u o (p m₁ o) (pol m₁ o) - c := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, D₁.sum_one, one_mul]
    have e2 : ∑ o, D₂.w o * (u o (p m₂ o) (pol m₂ o) - c) =
        ∑ o, D₂.w o * u o (p m₂ o) (pol m₂ o) - c := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, D₂.sum_one, one_mul]
    rw [Finset.sum_sub_distrib, e1, e2]
    ring
  -- the pointwise bound
  have hpt : ∀ o, D₁.w o * (u o (p m₁ o) (pol m₁ o) - c) - D₂.w o * (u o (p m₂ o) (pol m₂ o) - c) ≤
      R * ((if o ∈ errSet p pol m₁ then D₁.w o else 0) +
        (if o ∈ errSet p pol m₂ then D₂.w o else 0) + max (D₁.w o - D₂.w o) 0) := by
    intro o
    have ha := D₁.nonneg o
    have hb := D₂.nonneg o
    have hmax0 : 0 ≤ max (D₁.w o - D₂.w o) 0 := le_max_right _ _
    have hmax1 : D₁.w o - D₂.w o ≤ max (D₁.w o - D₂.w o) 0 := le_max_left _ _
    have hx0 : 0 ≤ u o (p m₁ o) (pol m₁ o) - c := by linarith [(hu o (p m₁ o) (pol m₁ o)).1]
    have hxR : u o (p m₁ o) (pol m₁ o) - c ≤ R := by linarith [(hu o (p m₁ o) (pol m₁ o)).2]
    have hy0 : 0 ≤ u o (p m₂ o) (pol m₂ o) - c := by linarith [(hu o (p m₂ o) (pol m₂ o)).1]
    have hyR : u o (p m₂ o) (pol m₂ o) - c ≤ R := by linarith [(hu o (p m₂ o) (pol m₂ o)).2]
    by_cases h1 : o ∈ errSet p pol m₁
    · rw [if_pos h1]
      have hE₂ : 0 ≤ (if o ∈ errSet p pol m₂ then D₂.w o else 0) := by
        split_ifs
        · exact hb
        · exact le_rfl
      nlinarith [mul_nonneg hb hy0, mul_le_mul_of_nonneg_left hxR ha, mul_nonneg hR hE₂,
        mul_nonneg hR hmax0]
    · rw [if_neg h1]
      by_cases h2 : o ∈ errSet p pol m₂
      · rw [if_pos h2]
        nlinarith [mul_nonneg hb hy0, mul_le_mul_of_nonneg_left hxR ha,
          mul_le_mul_of_nonneg_right hmax1 hR]
      · rw [if_neg h2]
        have hxy : u o (p m₁ o) (pol m₁ o) - c = u o (p m₂ o) (pol m₂ o) - c := by
          rw [mem_errSet, not_not] at h1 h2
          rw [h1, h2, h]
        rw [← hxy]
        nlinarith [mul_le_mul_of_nonneg_right hmax1 hx0, mul_le_mul_of_nonneg_left hxR hmax0]
  -- the sum of the pointwise bounds
  have hsum : ∑ o, R * ((if o ∈ errSet p pol m₁ then D₁.w o else 0) +
        (if o ∈ errSet p pol m₂ then D₂.w o else 0) + max (D₁.w o - D₂.w o) 0) =
      R * (mass D₁.w (errSet p pol m₁) + mass D₂.w (errSet p pol m₂) + tv D₁ D₂) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have e1 : ∑ o, (if o ∈ errSet p pol m₁ then D₁.w o else 0) = mass D₁.w (errSet p pol m₁) := by
      rw [mass, ← Finset.sum_filter]
      congr 1
      ext o
      simp
    have e2 : ∑ o, (if o ∈ errSet p pol m₂ then D₂.w o else 0) = mass D₂.w (errSet p pol m₂) := by
      rw [mass, ← Finset.sum_filter]
      congr 1
      ext o
      simp
    rw [e1, e2, tv]
  rw [hcent, ← hsum]
  exact Finset.sum_le_sum fun o _ => hpt o

/-- **Utility-level approximate DD, prediction-dependent observations, total-variation form
(T4(b))**: with accuracy `δ` under **each mechanism's own law** and a shared policy,
`|U(M₁) − U(M₂)| ≤ R · (2δ + tv(D₁, D₂))` where `Dᵢ = Dof (p Mᵢ)`. The total-variation term
enters once (`varying_sub_le`, both ways round). Repair round 1: the first version of this theorem
had `2 · tv` and claimed the factor was real; it was an artifact of that proof (r1 audits, B1).
Source: [[gap1-reframing-predictor-access]] §4 Corollary, prediction-dependent regime (udt-rep-033)
Kind: P
Fidelity: exact (the total-variation form of the note's bound; closed form in `approxDD_varying`)
Hyps: (a) `hu`, (a) `hacc` (own-law reading, ATTRIBUTION-UNVETTED); `hR : 0 ≤ R` as in T4(a) -/
theorem approxDD_varying_tv (Dof : (O → A) → FinDist O) (u : O → A → A → ℝ) {c R : ℝ} (hR : 0 ≤ R)
    (hu : ∀ o a b, u o a b ∈ Set.Icc c (c + R)) {p pol : M → O → A} {δ : ℝ}
    (hacc : ∀ m, mass (Dof (p m)).w (errSet p pol m) ≤ δ) {m₁ m₂ : M} (h : pol m₁ = pol m₂) :
    |varyingUtility Dof u p pol m₁ - varyingUtility Dof u p pol m₂| ≤
      R * (2 * δ + tv (Dof (p m₁)) (Dof (p m₂))) := by
  have h12 := varying_sub_le Dof u hR hu (p := p) h
  have h21 := varying_sub_le Dof u hR hu (p := p) h.symm
  rw [tv_symm] at h21
  have hA := hacc m₁
  have hB := hacc m₂
  have hs1 : mass (Dof (p m₁)).w (errSet p pol m₁) + mass (Dof (p m₂)).w (errSet p pol m₂) +
      tv (Dof (p m₁)) (Dof (p m₂)) ≤ 2 * δ + tv (Dof (p m₁)) (Dof (p m₂)) := by linarith
  have hs2 : mass (Dof (p m₂)).w (errSet p pol m₂) + mass (Dof (p m₁)).w (errSet p pol m₁) +
      tv (Dof (p m₁)) (Dof (p m₂)) ≤ 2 * δ + tv (Dof (p m₁)) (Dof (p m₂)) := by linarith
  have hB1 := mul_le_mul_of_nonneg_left hs1 hR
  have hB2 := mul_le_mul_of_nonneg_left hs2 hR
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **Utility-level approximate DD, prediction-dependent observations, closed form (T4(b),
load-bearing 2)**: if changing predictions moves the law by at most `L` per changed observation in
total variation (the Hamming form; the note's single-step hypothesis gives it,
`approxDD_varying_single_step`), every law puts mass `≥ γ > 0` on every observation, and each
mechanism is `δ`-accurate under its own law, then for a shared policy
`|U(M₁) − U(M₂)| ≤ R · (2δ + L · 2δ/γ)` — **the note's constant, derived**:
`tv(D₁, D₂) ≤ L · |disSet| ≤ L · 2δ/γ` (the counting bound under each own law) and `tv` enters
once (`approxDD_varying_tv`). Repair round 1: the first version proved `R (2δ + 4Lδ/γ)` and left
the note's constant OPEN; the r1 audits showed the slack was the proof's, not the note's. In
transparent Newcomb the two-boxer-verdicted agent's full-box branch has law-mass `ε`, so `γ = ε`
there (`udt-policy-calc`'s ε-table, not re-proved).
Source: [[gap1-reframing-predictor-access]] §4 Corollary, prediction-dependent regime (udt-rep-033)
Kind: C
Fidelity: exact (the note's display, under the own-law reading of the accuracy hypothesis)
Hyps: (a) `hL` (Lipschitz law), (a) `hsupp` (own-law support), (a) `hacc` (own-law accuracy, ATTRIBUTION-UNVETTED reading), (a) `hu`; `hR`, `hL0` sign conditions (`hR` follows from `hu` when `O` and `A` are inhabited; `hL0` from `hL` at a pair `q ≠ q'`, which needs `|A| ≥ 2` and `O` inhabited; both are carried explicitly for the empty-carrier edge cases) -/
theorem approxDD_varying (Dof : (O → A) → FinDist O) (u : O → A → A → ℝ) {c R L γ δ : ℝ}
    (hR : 0 ≤ R) (hL0 : 0 ≤ L) (hγ : 0 < γ)
    (hu : ∀ o a b, u o a b ∈ Set.Icc c (c + R))
    (hL : ∀ q q' : O → A, tv (Dof q) (Dof q') ≤ L * (event fun o => q o ≠ q' o).card)
    {p pol : M → O → A} (hsupp : ∀ m o, γ ≤ (Dof (p m)).w o)
    (hacc : ∀ m, mass (Dof (p m)).w (errSet p pol m) ≤ δ) {m₁ m₂ : M} (h : pol m₁ = pol m₂) :
    |varyingUtility Dof u p pol m₁ - varyingUtility Dof u p pol m₂| ≤
      R * (2 * δ + L * (2 * δ / γ)) := by
  have hmain := approxDD_varying_tv Dof u hR hu hacc h
  -- `tv D₁ D₂ ≤ L · |disSet| ≤ L · 2δ/γ`
  have hcard : γ * ((disSet p m₁ m₂).card : ℝ) ≤ 2 * δ := by
    have hc : (disSet p m₁ m₂).card ≤ (errSet p pol m₁).card + (errSet p pol m₂).card :=
      (Finset.card_le_card (disSet_subset_union h)).trans (Finset.card_union_le _ _)
    have h1 : γ * ((errSet p pol m₁).card : ℝ) ≤ δ :=
      (mul_card_le_mass (hsupp m₁) _).trans (hacc m₁)
    have h2 : γ * ((errSet p pol m₂).card : ℝ) ≤ δ :=
      (mul_card_le_mass (hsupp m₂) _).trans (hacc m₂)
    have hc' : ((disSet p m₁ m₂).card : ℝ) ≤ (errSet p pol m₁).card + (errSet p pol m₂).card := by
      exact_mod_cast hc
    nlinarith [mul_le_mul_of_nonneg_left hc' hγ.le]
  have htv : tv (Dof (p m₁)) (Dof (p m₂)) ≤ L * (2 * δ / γ) := by
    have h1 := hL (p m₁) (p m₂)
    have h2 : L * ((disSet p m₁ m₂).card : ℝ) ≤ L * (2 * δ / γ) :=
      mul_le_mul_of_nonneg_left (by rw [le_div_iff₀ hγ, mul_comm]; exact hcard) hL0
    exact h1.trans h2
  have hfin : R * (2 * δ + tv (Dof (p m₁)) (Dof (p m₂))) ≤ R * (2 * δ + L * (2 * δ / γ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hR
  exact hmain.trans hfin

/-- Supporting lemma `tv_triangle`: the triangle inequality for total variation (it is half the
`ℓ¹` distance, `tv_eq_half_sum_abs`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem tv_triangle (D D' D'' : FinDist O) : tv D D'' ≤ tv D D' + tv D' D'' := by
  rw [tv_eq_half_sum_abs, tv_eq_half_sum_abs, tv_eq_half_sum_abs, ← mul_add,
    ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum fun o _ => abs_sub_le _ _ _

/-- **The note's single-step Lipschitz hypothesis gives the Hamming form**: if changing the
prediction at one observation moves the law by at most `L` in total variation, then changing it at
`k` observations moves it by at most `L · k` — by the triangle inequality along a chain of
one-observation updates (induction on the number of changed observations).
Source: [[gap1-reframing-predictor-access]] §4 ("if changing the prediction at one observation moves `D` by at most `L` in total variation") (udt-rep-033)
Kind: P
Fidelity: exact
Hyps: none -/
theorem lipschitz_of_single_step (Dof : (O → A) → FinDist O) {L : ℝ}
    (hL : ∀ (q : O → A) (o : O) (a : A), tv (Dof q) (Dof (Function.update q o a)) ≤ L) :
    ∀ q q' : O → A, tv (Dof q) (Dof q') ≤ L * (event fun o => q o ≠ q' o).card := by
  suffices key : ∀ n : ℕ, ∀ q q' : O → A, (event fun o => q o ≠ q' o).card = n →
      tv (Dof q) (Dof q') ≤ L * n from fun q q' => key _ q q' rfl
  intro n
  induction n with
  | zero =>
    intro q q' hc
    have hqq : q = q' := by
      funext o
      by_contra hne
      have hmem : o ∈ (event fun o => q o ≠ q' o) := by simp [hne]
      rw [Finset.card_eq_zero] at hc
      rw [hc] at hmem
      exact Finset.notMem_empty o hmem
    subst hqq
    simp [tv_self]
  | succ n ih =>
    intro q q' hc
    have hne : (event fun o => q o ≠ q' o).Nonempty := by
      rw [← Finset.card_pos, hc]; exact Nat.succ_pos n
    obtain ⟨o, ho⟩ := hne
    set q₁ := Function.update q o (q' o) with hq₁
    have hset : (event fun o' => q₁ o' ≠ q' o') = (event fun o' => q o' ≠ q' o').erase o := by
      ext o'
      by_cases h' : o' = o
      · subst h'
        simp [q₁]
      · simp [q₁, h']
    have hcard : (event fun o' => q₁ o' ≠ q' o').card = n := by
      rw [hset, Finset.card_erase_of_mem ho, hc]
      rfl
    have h1 := hL q o (q' o)
    have h2 := ih q₁ q' hcard
    have h3 := tv_triangle (Dof q) (Dof q₁) (Dof q')
    push_cast
    linarith

/-- **T4(b) with the note's hypothesis verbatim**: `approxDD_varying` under the single-step Lipschitz
hypothesis ("changing the prediction at one observation moves `D` by at most `L` in total
variation"), via `lipschitz_of_single_step`.
Source: [[gap1-reframing-predictor-access]] §4 Corollary, prediction-dependent regime (udt-rep-033)
Kind: C
Fidelity: exact (the note's display and the note's Lipschitz hypothesis, under the own-law reading of the accuracy hypothesis)
Hyps: (a) `hL` (single-step Lipschitz law), (a) `hsupp`, (a) `hacc` (own-law reading, ATTRIBUTION-UNVETTED), (a) `hu`; `hR`, `hL0` sign conditions -/
theorem approxDD_varying_single_step (Dof : (O → A) → FinDist O) (u : O → A → A → ℝ)
    {c R L γ δ : ℝ} (hR : 0 ≤ R) (hL0 : 0 ≤ L) (hγ : 0 < γ)
    (hu : ∀ o a b, u o a b ∈ Set.Icc c (c + R))
    (hL : ∀ (q : O → A) (o : O) (a : A), tv (Dof q) (Dof (Function.update q o a)) ≤ L)
    {p pol : M → O → A} (hsupp : ∀ m o, γ ≤ (Dof (p m)).w o)
    (hacc : ∀ m, mass (Dof (p m)).w (errSet p pol m) ≤ δ) {m₁ m₂ : M} (h : pol m₁ = pol m₂) :
    |varyingUtility Dof u p pol m₁ - varyingUtility Dof u p pol m₂| ≤
      R * (2 * δ + L * (2 * δ / γ)) :=
  approxDD_varying Dof u hR hL0 hγ hu (lipschitz_of_single_step Dof hL) hsupp hacc h

/-- **T4(c), the fixed-reference-law variant (stretch, `approxDD_varying_ref`)**: accuracy `δ` and
support `γ` measured under one reference law `D₀`, with each mechanism's own law within `η` of `D₀`
in total variation; then `|U(M₁) − U(M₂)| ≤ R (2(δ + η) + L · 2δ/γ)`. This is not a generalization
of the own-law form (`approxDD_varying`): there a mechanism's accuracy and support are measured
under *its own* law, and no single `D₀` is within `η = 0` of two different laws; here one reference
law serves both mechanisms and the mismatch is paid for as `2η`, through the mass transfer
`mass (Dof (p m)) (err m) ≤ mass D₀ (err m) + tv (Dof (p m), D₀)` (`mass_sub_mass_le_tv`). The two
forms are the two readings of the note's unsubscripted `Pr_{o∼D}`; the own-law one is of record.
Instantiated on `Witness.Varying` at `D₀ = unif4`, `δ = 1/4`, `γ = 7/32`, `η = 1/32`
(`Varying.bound_instance_ref`; repair round 2).
Source: [[gap1-reframing-predictor-access]] §4 Corollary (udt-rep-033); mandate T4(c) (the alternative reading of the accuracy hypothesis)
Kind: C
Fidelity: variant: accuracy and support under a fixed reference law `D₀`, own laws within `η`; constant `R (2(δ + η) + L · 2δ/γ)`
Hyps: (a) `hL`, `hsupp` (reference-law support), `hnear`, `hacc` (reference-law accuracy), `hu`; `hR`, `hL0` sign conditions -/
theorem approxDD_varying_ref (Dof : (O → A) → FinDist O) (u : O → A → A → ℝ) (D₀ : FinDist O)
    {c R L γ δ η : ℝ} (hR : 0 ≤ R) (hL0 : 0 ≤ L) (hγ : 0 < γ)
    (hu : ∀ o a b, u o a b ∈ Set.Icc c (c + R))
    (hL : ∀ q q' : O → A, tv (Dof q) (Dof q') ≤ L * (event fun o => q o ≠ q' o).card)
    {p pol : M → O → A} (hsupp : ∀ o, γ ≤ D₀.w o) (hnear : ∀ m, tv (Dof (p m)) D₀ ≤ η)
    (hacc : ∀ m, mass D₀.w (errSet p pol m) ≤ δ) {m₁ m₂ : M} (h : pol m₁ = pol m₂) :
    |varyingUtility Dof u p pol m₁ - varyingUtility Dof u p pol m₂| ≤
      R * (2 * (δ + η) + L * (2 * δ / γ)) := by
  have hacc' : ∀ m, mass (Dof (p m)).w (errSet p pol m) ≤ δ + η := fun m => by
    have := mass_sub_mass_le_tv (Dof (p m)) D₀ (errSet p pol m)
    linarith [hacc m, hnear m]
  have hmain := approxDD_varying_tv Dof u hR hu hacc' h
  have hcard : γ * ((disSet p m₁ m₂).card : ℝ) ≤ 2 * δ := by
    have hc : (disSet p m₁ m₂).card ≤ (errSet p pol m₁).card + (errSet p pol m₂).card :=
      (Finset.card_le_card (disSet_subset_union h)).trans (Finset.card_union_le _ _)
    have h1 : γ * ((errSet p pol m₁).card : ℝ) ≤ δ :=
      (mul_card_le_mass hsupp _).trans (hacc m₁)
    have h2 : γ * ((errSet p pol m₂).card : ℝ) ≤ δ :=
      (mul_card_le_mass hsupp _).trans (hacc m₂)
    have hc' : ((disSet p m₁ m₂).card : ℝ) ≤ (errSet p pol m₁).card + (errSet p pol m₂).card := by
      exact_mod_cast hc
    nlinarith [mul_le_mul_of_nonneg_left hc' hγ.le]
  have htv : tv (Dof (p m₁)) (Dof (p m₂)) ≤ L * (2 * δ / γ) := by
    have h1 := hL (p m₁) (p m₂)
    have h2 : L * ((disSet p m₁ m₂).card : ℝ) ≤ L * (2 * δ / γ) :=
      mul_le_mul_of_nonneg_left (by rw [le_div_iff₀ hγ, mul_comm]; exact hcard) hL0
    exact h1.trans h2
  have hfin : R * (2 * (δ + η) + tv (Dof (p m₁)) (Dof (p m₂))) ≤
      R * (2 * (δ + η) + L * (2 * δ / γ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hR
  exact hmain.trans hfin

/-! ### T5: DD with respect to the support -/

/-- **The utility depends on the mechanism only through the on-support policy (T5)**: if the
response and the payoff use only on-support predictions and on-support actions
(`U M = F (p(M,·)|_{supp D}) (π_M|_{supp D})`) and predictions are exact on the support, then two
mechanisms agreeing on the support have the same utility. *Reading* (the docstring's scope, not
the theorem's): "the UDT rule constrains the policy only on `supp D`"; the theorem is the invariance.
Source: [[gap1-reframing-predictor-access]] §4(a) (udt-rep-036)
Kind: L
Fidelity: exact (with the payoff's own dependence on the policy also restricted to the support; without that restriction the claim is false, since `U` could read `π_M` off-support directly)
Hyps: (a) `hU` (the response uses on-support data only), (a) `hacc` (on-support accuracy) -/
theorem utility_of_onSupport (D : FinDist O)
    (F : ({o : O // 0 < D.w o} → A) → ({o : O // 0 < D.w o} → A) → ℝ) {p pol : M → O → A}
    (hacc : ∀ m o, 0 < D.w o → p m o = pol m o) (U : M → ℝ)
    (hU : ∀ m, U m = F (fun o => p m o.1) (fun o => pol m o.1)) {m₁ m₂ : M}
    (h : ∀ o, 0 < D.w o → pol m₁ o = pol m₂ o) : U m₁ = U m₂ := by
  rw [hU, hU]
  have h1 : (fun o : {o : O // 0 < D.w o} => p m₁ o.1) = fun o => p m₂ o.1 :=
    funext fun o => by rw [hacc m₁ o.1 o.2, hacc m₂ o.1 o.2, h o.1 o.2]
  have h2 : (fun o : {o : O // 0 < D.w o} => pol m₁ o.1) = fun o => pol m₂ o.1 :=
    funext fun o => h o.1 o.2
  rw [h1, h2]

/-- **Off-support modification changes nothing (T5, corollary)**: for `o₀` with `D(o₀) = 0` and a
mechanism `m'` realizing `π_{m'} = π_m[o₀ ↦ a]` (`Function.update`, `udt-policy-calc`'s `modify`),
`U m' = U m`.
Source: [[gap1-reframing-predictor-access]] §4(a) ("modifying `π` off-support changes nothing"; udt-rep-036)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem utility_of_offSupport_modify (D : FinDist O)
    (F : ({o : O // 0 < D.w o} → A) → ({o : O // 0 < D.w o} → A) → ℝ) {p pol : M → O → A}
    (hacc : ∀ m o, 0 < D.w o → p m o = pol m o) (U : M → ℝ)
    (hU : ∀ m, U m = F (fun o => p m o.1) (fun o => pol m o.1)) {m m' : M} {o₀ : O} {a : A}
    (ho₀ : D.w o₀ = 0) (hm' : pol m' = Function.update (pol m) o₀ a) : U m' = U m := by
  refine utility_of_onSupport D F hacc U hU fun o ho => ?_
  rw [hm', Function.update_apply]
  have hne : o ≠ o₀ := fun heq => by rw [heq, ho₀] at ho; exact lt_irrefl _ ho
  simp [hne]

/-! ### T12(a): the converse of approximate factoring, and its surviving neighbour -/

/-- **An error of `m` is a disagreement with `m₀` or an error of `m₀`** when the two share a policy.
Source: mandate T12(a) (surviving neighbour)
Kind: L
Fidelity: exact
Hyps: none -/
theorem errSet_subset_disSet_union {p pol : M → O → A} {m m₀ : M} (h : pol m = pol m₀) :
    errSet p pol m ⊆ disSet p m m₀ ∪ errSet p pol m₀ := by
  intro o ho
  rw [mem_errSet] at ho
  rw [Finset.mem_union, mem_disSet, mem_errSet]
  by_cases h1 : p m o = p m₀ o
  · exact Or.inr fun h2 => ho (by rw [h1, h2, h])
  · exact Or.inl h1

/-- **Accuracy from one representative (T12(a), surviving neighbour)**: the error mass of `m` is at
most its disagreement mass with a representative `m₀` of its policy class plus `m₀`'s error mass.
Hence under exact factoring every member of a class is as accurate as any one member, and under
T3's `2δ`-disagreement bound a `δ`-accurate representative makes every member `3δ`-accurate
(`accuracy_of_factors_of_representative`).
Source: mandate T12(a)
Kind: P
Fidelity: exact (constant derived: `2δ + δ = 3δ`)
Hyps: (a) -/
theorem mass_errSet_le_of_representative {p pol : M → O → A} (D : FinDist O) {m m₀ : M}
    (h : pol m = pol m₀) :
    mass D.w (errSet p pol m) ≤ mass D.w (disSet p m m₀) + mass D.w (errSet p pol m₀) :=
  (mass_mono D.nonneg (errSet_subset_disSet_union h)).trans (mass_union_le D.nonneg _ _)

/-- **`3δ` from a `δ`-accurate representative under the `2δ`-disagreement bound** (T12(a)).
Source: mandate T12(a)
Kind: C
Fidelity: exact (constant derived)
Hyps: (a) -/
theorem accuracy_of_factors_of_representative {p pol : M → O → A} (D : FinDist O) {δ : ℝ}
    {m m₀ : M} (h : pol m = pol m₀) (hdis : mass D.w (disSet p m m₀) ≤ 2 * δ)
    (hrep : mass D.w (errSet p pol m₀) ≤ δ) : mass D.w (errSet p pol m) ≤ 3 * δ := by
  have := mass_errSet_le_of_representative D (p := p) h
  linarith

/-- **Under exact factoring, accuracy is a class property** (T12(a), `δ`-form).
Source: mandate T12(a)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem accuracy_of_factors {p pol : M → O → A} (D : FinDist O) (hf : Factors p pol) {δ : ℝ}
    {m m₀ : M} (h : pol m = pol m₀) (hrep : mass D.w (errSet p pol m₀) ≤ δ) :
    mass D.w (errSet p pol m) ≤ δ := by
  have hd : disSet p m m₀ = ∅ := disSet_eq_empty_iff.2 (hf m m₀ h)
  have := mass_errSet_le_of_representative D (p := p) h
  rw [hd] at this
  simp only [mass, Finset.sum_empty, zero_add] at this
  exact this.trans hrep

end Cleanroom.Udt.UdtCondenseDd
