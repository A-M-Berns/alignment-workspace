import Cleanroom.Found.CorrThreeStep.Setting
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# Product-form conditional expectations on FAF's `Distr` (infrastructure for T4–T7)

`expectOn μ A X = ∑_{ω ∈ A} μ(ω) X(ω)` (the denominator-free "`E[X ; A]`") and the *derived*
`condExpect μ A X = expectOn μ A X / μ(A)`. Every headline of the package that conditions on a
parent configuration `pa_H` either carries `0 < μ(pa_H)` or quantifies over configurations in the
support, so the junk value `condExpect μ A X = 0` at `μ(A) = 0` never decides a theorem (mandate
T1, "the junk point of the whole package"). The lemmas here are the ones Carey–Everitt's proofs use
without comment: monotonicity and congruence of conditional expectations *on the support*, the
mixture `E[X] = ∑_{pa} E[X ; pa]`, and "`P(A) = 1` iff every support point is in `A`".

Source: none: infrastructure. Reuses `corr-three-step`'s `expect` (not redefined).
-/

namespace Cleanroom.Corrigibility.CorrScimCid

open FactoredSpaces Cleanroom.Found.CorrThreeStep

variable {Ω : Type*} [Fintype Ω]

/-- The product-form restricted expectation `E_μ[X ; A] = ∑_{ω ∈ A} μ(ω) X(ω)`.
Source: none: infrastructure
Kind: D -/
noncomputable def expectOn (μ : Distr Ω) (A : Set Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, A.indicator (fun ω => μ.mass ω * X ω) ω

/-- The derived conditional expectation `E_μ[X | A] = E_μ[X ; A] / μ(A)` (junk `0` at `μ(A) = 0`;
never load-bearing, see the module docstring).
Source: none: infrastructure
Kind: D -/
noncomputable def condExpect (μ : Distr Ω) (A : Set Ω) (X : Ω → ℝ) : ℝ :=
  expectOn μ A X / μ.prob A

variable (μ : Distr Ω)

lemma expectOn_univ (X : Ω → ℝ) : expectOn μ Set.univ X = expect μ X := by
  simp [expectOn, expect]

lemma expectOn_apply (A : Set Ω) [DecidablePred (· ∈ A)] (X : Ω → ℝ) :
    expectOn μ A X = ∑ ω, if ω ∈ A then μ.mass ω * X ω else 0 := by
  simp [expectOn, Set.indicator_apply]

/-- Congruence on the support: two variables equal at every positive-mass point of `A` have the
same restricted expectation.
Source: none: infrastructure
Kind: L -/
lemma expectOn_congr {A : Set Ω} {X Y : Ω → ℝ}
    (h : ∀ ω ∈ A, 0 < μ.mass ω → X ω = Y ω) : expectOn μ A X = expectOn μ A Y := by
  classical
  simp only [expectOn_apply]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hA : ω ∈ A
  · simp only [hA, if_true]
    rcases (μ.nonneg ω).lt_or_eq with hpos | hzero
    · rw [h ω hA hpos]
    · rw [← hzero]; ring
  · simp [hA]

/-- Monotonicity on the support.
Source: none: infrastructure
Kind: L -/
lemma expectOn_mono {A : Set Ω} {X Y : Ω → ℝ}
    (h : ∀ ω ∈ A, 0 < μ.mass ω → X ω ≤ Y ω) : expectOn μ A X ≤ expectOn μ A Y := by
  classical
  simp only [expectOn_apply]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hA : ω ∈ A
  · simp only [hA, if_true]
    rcases (μ.nonneg ω).lt_or_eq with hpos | hzero
    · exact mul_le_mul_of_nonneg_left (h ω hA hpos) hpos.le
    · rw [← hzero]; simp
  · simp [hA]

lemma expectOn_const (A : Set Ω) (k : ℝ) : expectOn μ A (fun _ => k) = k * μ.prob A := by
  classical
  simp only [expectOn_apply, Distr.prob, Set.indicator_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hA : ω ∈ A <;> simp [hA, mul_comm]

lemma expectOn_add (A : Set Ω) (X Y : Ω → ℝ) :
    expectOn μ A (fun ω => X ω + Y ω) = expectOn μ A X + expectOn μ A Y := by
  classical
  simp only [expectOn_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hA : ω ∈ A <;> simp [hA, mul_add]

/-- A set of probability zero contributes nothing.
Source: none: infrastructure
Kind: L -/
lemma expectOn_eq_zero_of_prob_eq_zero {A : Set Ω} (h : μ.prob A = 0) (X : Ω → ℝ) :
    expectOn μ A X = 0 := by
  classical
  rw [Distr.prob_eq_zero_iff] at h
  simp only [expectOn_apply]
  refine Finset.sum_eq_zero fun ω _ => ?_
  by_cases hA : ω ∈ A
  · have : μ.mass ω = 0 := by
      by_contra hne
      have hpos : 0 < μ.mass ω := lt_of_le_of_ne (μ.nonneg ω) (Ne.symm hne)
      exact Set.disjoint_left.mp h hA hpos
    simp [hA, this]
  · simp [hA]

lemma expectOn_eq_condExpect_mul {A : Set Ω} (h : 0 < μ.prob A) (X : Ω → ℝ) :
    expectOn μ A X = condExpect μ A X * μ.prob A := by
  rw [condExpect, div_mul_cancel₀ _ h.ne']

lemma condExpect_le_condExpect {A : Set Ω} {X Y : Ω → ℝ}
    (h : expectOn μ A X ≤ expectOn μ A Y) : condExpect μ A X ≤ condExpect μ A Y :=
  div_le_div_of_nonneg_right h (μ.prob_nonneg A)

/-- Monotonicity of the conditional expectation on the support.
Source: none: infrastructure
Kind: L -/
lemma condExpect_mono {A : Set Ω} {X Y : Ω → ℝ}
    (h : ∀ ω ∈ A, 0 < μ.mass ω → X ω ≤ Y ω) : condExpect μ A X ≤ condExpect μ A Y :=
  condExpect_le_condExpect μ (expectOn_mono μ h)

/-- Congruence of the conditional expectation on the support.
Source: none: infrastructure
Kind: L -/
lemma condExpect_congr {A : Set Ω} {X Y : Ω → ℝ}
    (h : ∀ ω ∈ A, 0 < μ.mass ω → X ω = Y ω) : condExpect μ A X = condExpect μ A Y := by
  rw [condExpect, condExpect, expectOn_congr μ h]

/-- **The mixture identity**: `E[X] = ∑_{a ∈ range g} E[X ; g = a]`.
Source: none: infrastructure (Carey–Everitt Prop. 6 proof, "`E[U] = ∑_{pa} P(pa) E[U | pa]`")
Kind: L -/
lemma expect_eq_sum_expectOn {κ : Type*} [DecidableEq κ] (g : Ω → κ) (X : Ω → ℝ) :
    expect μ X = ∑ a ∈ Finset.univ.image g, expectOn μ {ω | g ω = a} X := by
  classical
  rw [expect, ← Finset.sum_fiberwise_of_maps_to (t := Finset.univ.image g) (g := g)
    (fun ω _ => Finset.mem_image_of_mem g (Finset.mem_univ ω))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [expectOn_apply, Finset.sum_filter]
  rfl

/-- **The mixture inequality**: if `E[X | g = a] ≤ E[Y | g = a]` at every positive-probability
fibre, then `E[X] ≤ E[Y]`.
Source: none: infrastructure (Carey–Everitt Prop. 6 proof, last step)
Kind: P -/
lemma expect_le_of_condExpect_le {κ : Type*} (g : Ω → κ) {X Y : Ω → ℝ}
    (h : ∀ a, 0 < μ.prob {ω | g ω = a} →
      condExpect μ {ω | g ω = a} X ≤ condExpect μ {ω | g ω = a} Y) :
    expect μ X ≤ expect μ Y := by
  classical
  rw [expect_eq_sum_expectOn μ g X, expect_eq_sum_expectOn μ g Y]
  refine Finset.sum_le_sum fun a _ => ?_
  rcases (μ.prob_nonneg {ω | g ω = a}).lt_or_eq with hpos | hzero
  · rw [expectOn_eq_condExpect_mul μ hpos, expectOn_eq_condExpect_mul μ hpos]
    exact mul_le_mul_of_nonneg_right (h a hpos) hpos.le
  · rw [expectOn_eq_zero_of_prob_eq_zero μ hzero.symm, expectOn_eq_zero_of_prob_eq_zero μ hzero.symm]

/-- `P(A) + P(Aᶜ) = 1`.
Source: none: infrastructure
Kind: L -/
lemma prob_add_prob_compl (A : Set Ω) : μ.prob A + μ.prob Aᶜ = 1 := by
  rw [← Distr.prob_union_of_disjoint μ disjoint_compl_right, Set.union_compl_self, Distr.prob_univ]

/-- **`P(A) = 1` iff every support point lies in `A`.** The conversion every "`P(·) = 1`" of
Carey–Everitt's definitions goes through.
Source: none: infrastructure
Kind: L -/
lemma prob_eq_one_iff (A : Set Ω) : μ.prob A = 1 ↔ ∀ ω, 0 < μ.mass ω → ω ∈ A := by
  have h := prob_add_prob_compl μ A
  constructor
  · intro h1 ω hω
    have hc : μ.prob Aᶜ = 0 := by linarith
    rw [Distr.prob_eq_zero_iff] at hc
    by_contra hA
    exact Set.disjoint_left.mp hc hA hω
  · intro hall
    have hc : μ.prob Aᶜ = 0 := by
      rw [Distr.prob_eq_zero_iff, Set.disjoint_left]
      intro ω hω hs
      exact hω (hall ω hs)
    linarith

lemma prob_pos_of_mass_pos {A : Set Ω} {ω : Ω} (hω : 0 < μ.mass ω) (hA : ω ∈ A) :
    0 < μ.prob A :=
  (Distr.prob_pos_iff μ A).mpr ⟨ω, hA, hω⟩

/-- A sub-event of a probability-zero event has every support point outside it.
Source: none: infrastructure
Kind: L -/
lemma not_mem_of_prob_eq_zero {A : Set Ω} (h : μ.prob A = 0) {ω : Ω} (hω : 0 < μ.mass ω) :
    ω ∉ A := fun hA => by
  rw [Distr.prob_eq_zero_iff] at h
  exact Set.disjoint_left.mp h hA hω

lemma prob_eq_zero_of_forall {A : Set Ω} (h : ∀ ω, 0 < μ.mass ω → ω ∉ A) : μ.prob A = 0 := by
  rw [Distr.prob_eq_zero_iff, Set.disjoint_left]
  exact fun ω hA hω => h ω hω hA

/-- `P(A | C) = 1` iff `P(A ∩ C) = P(C)`, when `P(C) > 0`.
Source: none: infrastructure
Kind: L -/
lemma condProb_eq_one_iff {A C : Set Ω} (hC : 0 < μ.prob C) :
    μ.condProb A C = 1 ↔ μ.prob (A ∩ C) = μ.prob C := by
  rw [Distr.condProb, div_eq_one_iff_eq hC.ne']

/-- If `P(A | C) = 1` then every support point of `C` is in `A`.
Source: none: infrastructure
Kind: L -/
lemma mem_of_condProb_eq_one {A C : Set Ω} (hC : 0 < μ.prob C) (h : μ.condProb A C = 1)
    {ω : Ω} (hω : 0 < μ.mass ω) (hωC : ω ∈ C) : ω ∈ A := by
  rw [condProb_eq_one_iff μ hC] at h
  have hsplit : μ.prob C = μ.prob (A ∩ C) + μ.prob (C \ A) := by
    rw [← Distr.prob_union_of_disjoint μ (Set.disjoint_left.mpr fun x hx hx' => hx'.2 hx.1)]
    congr 1
    ext x
    constructor
    · intro hx
      by_cases hxA : x ∈ A
      · exact Or.inl ⟨hxA, hx⟩
      · exact Or.inr ⟨hx, hxA⟩
    · rintro (⟨-, hx⟩ | ⟨hx, -⟩) <;> exact hx
  have hz : μ.prob (C \ A) = 0 := by linarith
  by_contra hA
  exact not_mem_of_prob_eq_zero μ hz hω ⟨hωC, hA⟩

/-- Conversely, if every support point of `C` is in `A` then `P(A | C) = 1`.
Source: none: infrastructure
Kind: L -/
lemma condProb_eq_one_of_forall {A C : Set Ω} (hC : 0 < μ.prob C)
    (h : ∀ ω, 0 < μ.mass ω → ω ∈ C → ω ∈ A) : μ.condProb A C = 1 := by
  rw [condProb_eq_one_iff μ hC]
  refine le_antisymm (μ.prob_mono Set.inter_subset_right) ?_
  rw [Distr.prob, Distr.prob]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hωC : ω ∈ C
  · rcases (μ.nonneg ω).lt_or_eq with hpos | hzero
    · rw [Set.indicator_of_mem hωC, Set.indicator_of_mem (show ω ∈ A ∩ C from ⟨h ω hpos hωC, hωC⟩)]
    · rw [Set.indicator_of_mem hωC, ← hzero]
      exact Set.indicator_nonneg (fun _ _ => μ.nonneg _) _
  · rw [Set.indicator_of_notMem hωC]
    exact Set.indicator_nonneg (fun _ _ => μ.nonneg _) _

/-- `P(A ∩ C) = P(C)` forces every support point of `C` into `A` — the set form.
Source: none: infrastructure
Kind: L -/
lemma prob_inter_eq_iff_forall {A C : Set Ω} (hC : 0 < μ.prob C) :
    μ.prob (A ∩ C) = μ.prob C ↔ ∀ ω, 0 < μ.mass ω → ω ∈ C → ω ∈ A := by
  rw [← condProb_eq_one_iff μ hC]
  exact ⟨fun h ω hω hωC => mem_of_condProb_eq_one μ hC h hω hωC,
    fun h => condProb_eq_one_of_forall μ hC h⟩

/-- The expectation of a variable that is pointwise at least `k` on the support and equals a
constant off a set, in the form Lemma 22/23 use: `E[X] = ∑_{ω ∈ B} μ(ω) X(ω) + ∑_{ω ∉ B} μ(ω) X(ω)`.
Source: none: infrastructure
Kind: L -/
lemma expect_eq_expectOn_add_expectOn_compl (B : Set Ω) (X : Ω → ℝ) :
    expect μ X = expectOn μ B X + expectOn μ Bᶜ X := by
  classical
  simp only [expect, expectOn_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hB : ω ∈ B <;> simp [hB]

end Cleanroom.Corrigibility.CorrScimCid
