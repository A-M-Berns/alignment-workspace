import Cleanroom.Found.CorrThreeStep.Setting
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Shared infrastructure for `corr-osg-chai`

Small lemmas about `corr-three-step`'s `expect` on FAF's `Distr` that several files of this
package use: evaluation under a Dirac belief, "an expectation is at most a maximiser's value",
linearity over a finite family, the change of variables under FAF's `Distr.map`, a
product-swap identity, the deterministic-choice lemma behind Garber's Lemma A.3 / Cor. A.6, and
the sum-over-choice-functions identity behind Lemma A.5 (the product-weights expansion of a
stochastic pair's payoff). Nothing here is a headline.
-/

namespace Cleanroom.Corrigibility.CorrOsgChai

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω]

/-- Expectation under a Dirac belief is evaluation.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_delta [DecidableEq Ω] (u₀ : Ω) (X : Ω → ℝ) : expect (Distr.delta u₀) X = X u₀ := by
  simp [expect, Distr.delta_mass]

/-- An expectation is at most the value at a pointwise maximiser.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_le_apply (μ : Distr Ω) (X : Ω → ℝ) {a : Ω} (h : ∀ ω, X ω ≤ X a) :
    expect μ X ≤ X a :=
  (expect_mono μ h).trans_eq (expect_const μ _)

/-- Linearity of `expect` over a finite family of scaled functions.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_sum {ι : Type*} (μ : Distr Ω) (t : Finset ι) (c : ι → ℝ) (f : ι → Ω → ℝ) :
    expect μ (fun ω => ∑ i ∈ t, c i * f i ω) = ∑ i ∈ t, c i * expect μ (f i) := by
  simp only [expect, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun ω _ => by ring

/-- The mass of FAF's pushforward `Distr.map` is the fibre mass.
Source: none: infrastructure (FAF's `Distr.map`). Kind: L. Fidelity: n/a -/
lemma map_mass_eq_sum_filter {T : Type*} [Fintype T] [DecidableEq T] (μ : Distr Ω) (g : Ω → T)
    (t : T) : (μ.map g).mass t = ∑ ω ∈ univ.filter (fun ω => g ω = t), μ.mass ω := by
  classical
  rw [Distr.map_mass, Distr.prob_eq_sum_filter, sum_filter, sum_filter]
  exact sum_congr rfl fun ω _ => by by_cases h : g ω = t <;> simp [h]

/-- Change of variables under the pushforward: `E_{g_* μ}[f] = E_μ[f ∘ g]`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_map {T : Type*} [Fintype T] [DecidableEq T] (μ : Distr Ω) (g : Ω → T) (f : T → ℝ) :
    expect (μ.map g) f = expect μ (fun ω => f (g ω)) := by
  simp only [expect, map_mass_eq_sum_filter, sum_mul]
  rw [← sum_fiberwise univ g (fun ω => μ.mass ω * f (g ω))]
  exact sum_congr rfl fun t _ => sum_congr rfl fun ω hω => by rw [(mem_filter.mp hω).2]

/-- Swapping a weighted sum with an inner mixture: `∑ x, c x · ∑ i, q i · m i x = ∑ i, q i · ∑ x, c x · m i x`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_mul_sum_swap {X I : Type*} [Fintype X] [Fintype I] (c : X → ℝ) (q : I → ℝ)
    (m : I → X → ℝ) : ∑ x, c x * ∑ i, q i * m i x = ∑ i, q i * ∑ x, c x * m i x := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun x _ => by ring

/-- **Deterministic choice per fibre** (the mechanism of Garber's Lemma A.3): a weighted sum in
which each index `i` draws its choice from a distribution `P (κ i)` attached to its fibre is at
most the same sum with a fixed choice `π (κ i)` per fibre, namely a maximiser of the fibre's
weighted sum. No sign condition on the weights is needed.
Source: Garber et al. 2024 Lemma A.3(a) (l. 349–356), the finite mechanism
Kind: L
Fidelity: n/a -/
lemma exists_det_ge {I K A : Type*} [Fintype I] [Fintype K] [DecidableEq K] [Fintype A]
    [Nonempty A] (w : I → ℝ) (κ : I → K) (P : K → Distr A) (g : I → A → ℝ) :
    ∃ π : K → A, ∑ i, w i * expect (P (κ i)) (g i) ≤ ∑ i, w i * g i (π (κ i)) := by
  have hmax : ∀ k : K, ∃ a : A, ∀ a',
      (∑ i ∈ univ.filter (fun i => κ i = k), w i * g i a') ≤
        ∑ i ∈ univ.filter (fun i => κ i = k), w i * g i a := fun k => by
    obtain ⟨a, -, ha⟩ := exists_max_image univ
      (fun a => ∑ i ∈ univ.filter (fun i => κ i = k), w i * g i a) univ_nonempty
    exact ⟨a, fun a' => ha a' (mem_univ _)⟩
  choose π hπ using hmax
  refine ⟨π, ?_⟩
  rw [← sum_fiberwise univ κ (fun i => w i * expect (P (κ i)) (g i)),
    ← sum_fiberwise univ κ (fun i => w i * g i (π (κ i)))]
  refine sum_le_sum fun k _ => ?_
  have h1 : ∑ i ∈ univ.filter (fun i => κ i = k), w i * expect (P (κ i)) (g i) =
      expect (P k) (fun a => ∑ i ∈ univ.filter (fun i => κ i = k), w i * g i a) := by
    rw [expect_sum]
    exact sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]
  have h2 : ∑ i ∈ univ.filter (fun i => κ i = k), w i * g i (π (κ i)) =
      ∑ i ∈ univ.filter (fun i => κ i = k), w i * g i (π k) :=
    sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]
  rw [h1, h2]
  exact expect_le_apply _ _ (hπ k)

/-- The product of two finite distributions, `mass (x, y) = P x · Q y` (FAF has `mix`, not the
product; built explicitly on FAF's `Distr`).
Source: none: infrastructure (Garber et al. 2024 §3, `μ ⊗ ν`). Kind: D. Fidelity: exact -/
noncomputable def prodDistr {X Y : Type*} [Fintype X] [Fintype Y] (P : Distr X) (Q : Distr Y) :
    Distr (X × Y) where
  mass p := P.mass p.1 * Q.mass p.2
  nonneg p := mul_nonneg (P.nonneg _) (Q.nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type, ← sum_mul_sum, P.sum_eq_one, Q.sum_eq_one, one_mul]

/-- Mass of the product. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma prodDistr_mass {X Y : Type*} [Fintype X] [Fintype Y] (P : Distr X) (Q : Distr Y)
    (x : X) (y : Y) : (prodDistr P Q).mass (x, y) = P.mass x * Q.mass y := rfl

/-- A point mass is at most `1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Distr_mass_le_one {A : Type*} [Fintype A] (P : Distr A) (a : A) : P.mass a ≤ 1 :=
  P.sum_eq_one ▸ single_le_sum (fun b _ => P.nonneg b) (mem_univ a)

/-- Some point has positive mass. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma exists_pos_mass {A : Type*} [Fintype A] (P : Distr A) : ∃ a, P.mass a ≠ 0 := by
  by_contra h
  have h' : ∀ a, P.mass a = 0 := fun a => by
    by_contra ha
    exact h ⟨a, ha⟩
  have := P.sum_eq_one
  simp [h'] at this

/-- A distribution with mass `1` at `a` is the Dirac at `a`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Distr_eq_delta_of_mass_eq_one {A : Type*} [Fintype A] [DecidableEq A] (P : Distr A) {a : A}
    (h : P.mass a = 1) : P = Distr.delta a := by
  have hrest : ∑ b ∈ univ.erase a, P.mass b = 0 := by
    have := P.sum_eq_one
    rw [← add_sum_erase univ P.mass (mem_univ a), h] at this
    linarith
  have hzero : ∀ b ∈ univ.erase a, P.mass b = 0 :=
    (sum_eq_zero_iff_of_nonneg fun b _ => P.nonneg b).mp hrest
  ext b
  rw [Distr.delta_mass]
  by_cases hb : b = a
  · rw [hb, h, if_pos rfl]
  · rw [if_neg hb]; exact hzero b (mem_erase.mpr ⟨hb, mem_univ b⟩)

/-- **Summing over choice functions with one coordinate scored**: `∑ π, (∏ i, w i (π i)) · g (π i₀)
= ∑ a, w i₀ a · g a` when every row of `w` sums to `1` — the finite change of summation order
behind Garber's Lemma A.5 (a product of sums is a sum over `Fintype.piFinset`).
Source: none: infrastructure (Garber et al. 2024 Lemma A.5's mechanism). Kind: L. Fidelity: n/a -/
lemma sum_pi_prod_mul_eval {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (w : I → K → ℝ) (hw : ∀ i, ∑ a, w i a = 1) (i₀ : I) (g : K → ℝ) :
    ∑ π : I → K, (∏ i, w i (π i)) * g (π i₀) = ∑ a, w i₀ a * g a := by
  have h1 : ∀ π : I → K, (∏ i, w i (π i)) * g (π i₀) =
      ∏ i, (w i (π i) * (if i = i₀ then g (π i) else 1)) := by
    intro π
    rw [prod_mul_distrib, prod_ite_eq', if_pos (mem_univ _)]
  have h2 : ∀ i, ∑ a, w i a * (if i = i₀ then g a else 1) =
      if i = i₀ then ∑ a, w i a * g a else 1 := by
    intro i
    by_cases hi : i = i₀
    · simp [hi]
    · simp [hi, hw i]
  calc ∑ π : I → K, (∏ i, w i (π i)) * g (π i₀)
      = ∑ π : I → K, ∏ i, (w i (π i) * (if i = i₀ then g (π i) else 1)) :=
        sum_congr rfl fun π _ => h1 π
    _ = ∏ i, ∑ a, w i a * (if i = i₀ then g a else 1) :=
        (Fintype.prod_sum (fun i a => w i a * (if i = i₀ then g a else 1))).symm
    _ = ∏ i, (if i = i₀ then ∑ a, w i a * g a else 1) := prod_congr rfl fun i _ => h2 i
    _ = ∑ a, w i₀ a * g a := by rw [prod_ite_eq', if_pos (mem_univ _)]

/-- The product weights of a family of distributions sum to `1` over all choice functions.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_pi_prod_mass {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] (σ : I → Distr K) :
    ∑ π : I → K, ∏ i, (σ i).mass (π i) = 1 := by
  rw [← Fintype.prod_sum (fun i a => (σ i).mass a)]
  simp [Distr.sum_eq_one]

end Cleanroom.Corrigibility.CorrOsgChai
