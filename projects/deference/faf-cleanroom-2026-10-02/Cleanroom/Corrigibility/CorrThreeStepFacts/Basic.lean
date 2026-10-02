import Cleanroom.Found.CorrThreeStep
import Mathlib.Tactic.FieldSimp

/-!
# `corr-three-step-facts`: shared infrastructure

Package `corr-three-step-facts` (area `corrigibility`), the facts the corpus built on the
parent's Setting S (`Cleanroom.Found.CorrThreeStep`). This file holds what every target file
needs and the parent does not provide:

* `Fintype Obs` and the two-term sum over observations;
* positivity of the press-weighted expectation under a support condition (the engine of T1);
* the joint of a prior and a kernel on a product type (`kernelProd`), used by the private-
  information, scan and hazard settings (Pattern A of the mandate);
* the joint on `Ω × Obs` (`jointDistr`), the bridge from Good's theorem on a partition (T16) to
  the parent's `voiButton`;
* a mass bound on FAF's `Distr` (FAF API request: `Distr` carries `nonneg` and `sum_eq_one`
  but no `mass_le_one`).

Nothing here is a headline. Product form throughout: no division.
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

/-- `Obs` is finite, with `univ = {press, silent}` definitionally (the parent derives only
`DecidableEq`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance : Fintype Obs := ⟨{Obs.press, Obs.silent}, fun x => by cases x <;> simp⟩

/-- Sums over `Obs` expand to two terms. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Obs.sum_eq (f : Obs → ℝ) : ∑ o, f o = f .press + f .silent := by
  rw [show (univ : Finset Obs) = {Obs.press, Obs.silent} from rfl, sum_pair (by decide)]

/-- A point mass of a finite distribution is at most one (FAF API request).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Distr.mass_le_one' {S : Type*} [Fintype S] (μ : Distr S) (s : S) : μ.mass s ≤ 1 := by
  have := single_le_sum (fun t _ => μ.nonneg t) (mem_univ s)
  rwa [μ.sum_eq_one] at this

/-- A point mass lies in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Distr.mass_mem_Icc {S : Type*} [Fintype S] (μ : Distr S) (s : S) :
    μ.mass s ∈ Set.Icc (0 : ℝ) 1 := ⟨μ.nonneg s, Distr.mass_le_one' μ s⟩

/-! ## Positivity of the press-weighted expectation -/

section ThreeStepBasic

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep Ω A₁ A₂)

/-- When the press mass is positive some world carries positive press weight `μ(ω) P(Pr|ω)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma exists_pos_pressWeight (a : A₁) (h : 0 < S.pressMass a) :
    ∃ ω, 0 < (S.μ a).mass ω * S.press a ω := by
  by_contra hcon
  push Not at hcon
  have : S.pressMass a ≤ 0 := sum_nonpos fun ω _ => hcon ω
  linarith

/-- Positive press weight forces positive prior mass at that world.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mass_pos_of_pressWeight_pos (a : A₁) {ω : Ω} (h : 0 < (S.μ a).mass ω * S.press a ω) :
    0 < (S.μ a).mass ω := by
  rcases mul_pos_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact h1
  · exact absurd h1 (not_lt.mpr ((S.μ a).nonneg ω))

/-- **Support positivity.** If every world where `X ≤ 0` is prior-null and the press has
positive mass, the press-weighted expectation of `X` is strictly positive: each summand
`μ(ω) P(Pr|ω) X(ω)` is nonnegative (a null `μ` kills the `X ≤ 0` worlds) and the world carrying
positive press weight contributes a positive term.
Source: [[corr-wf13-2-inventory]] 003 / miri.md Prop. 8.1 (R1 failure), the mechanism
Kind: L
Fidelity: exact -/
lemma obsExpect_press_pos_of_support (a : A₁) (h : 0 < S.pressMass a) {X : Ω → ℝ}
    (hX : ∀ ω, X ω ≤ 0 → (S.μ a).mass ω = 0) : 0 < S.obsExpect a .press X := by
  obtain ⟨ω₀, hω₀⟩ := exists_pos_pressWeight S a h
  unfold obsExpect
  simp only [obsWeight_press]
  refine sum_pos' (fun ω _ => ?_) ⟨ω₀, mem_univ _, ?_⟩
  · by_cases hx : X ω ≤ 0
    · rw [hX ω hx]; simp
    · exact mul_nonneg (mul_nonneg ((S.μ a).nonneg ω) (S.press_nonneg a ω))
        (le_of_lt (not_le.mp hx))
  · have hμ := mass_pos_of_pressWeight_pos S a hω₀
    have hx : 0 < X ω₀ := by
      by_contra hx
      have := hX ω₀ (not_lt.mp hx)
      linarith
    exact mul_pos hω₀ hx

/-- A strictly positive variable has strictly positive press-weighted expectation when the
press has positive mass.
Source: [[corr-wf14-inventory]] 007 / filler.md R4.2 ("`X(ω) > 0` for every `ω` ⟹ `E_P[X | Pr] > 0`")
Kind: L
Fidelity: exact -/
lemma obsExpect_press_pos_of_pos (a : A₁) (h : 0 < S.pressMass a) {X : Ω → ℝ}
    (hX : ∀ ω, 0 < X ω) : 0 < S.obsExpect a .press X :=
  obsExpect_press_pos_of_support S a h fun ω hω => absurd (hX ω) (not_lt.mpr hω)

/-- A part-maximiser of a singleton part is its element. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma isPartBest_singleton (a : A₁) (o : Obs) (b : A₂) : S.IsPartBest a o {b} b :=
  ⟨mem_singleton_self b, fun b' hb' => by rw [mem_singleton.mp hb']⟩

end ThreeStepBasic

/-! ## Joints on product types -/

section Products

variable {W T : Type*} [Fintype W] [Fintype T]

/-- The joint `P(w, t) = μ(w) k_w(t)` of a prior `μ` and a kernel `k` on `W × T`: the finite
product used by every enlarged-latent setting (private information, scans, reliability bits).
Source: none: infrastructure (Pattern A of the mandate)
Kind: D
Fidelity: n/a -/
noncomputable def kernelProd (μ : Distr W) (k : W → Distr T) : Distr (W × T) where
  mass p := μ.mass p.1 * (k p.1).mass p.2
  nonneg p := mul_nonneg (μ.nonneg _) ((k _).nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, Distr.sum_eq_one, mul_one]

/-- Mass of the kernel product. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma kernelProd_mass (μ : Distr W) (k : W → Distr T) (w : W) (t : T) :
    (kernelProd μ k).mass (w, t) = μ.mass w * (k w).mass t := rfl

/-- The `W`-marginal of the kernel product is `μ`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma kernelProd_marginal (μ : Distr W) (k : W → Distr T) (w : W) :
    ∑ t, (kernelProd μ k).mass (w, t) = μ.mass w := by
  simp only [kernelProd_mass, ← mul_sum, Distr.sum_eq_one, mul_one]

/-- Expectation under a kernel product is the prior expectation of the conditional
expectations: `E_{μ ⊗ k}[U] = ∑ w, μ(w) ∑ t, k_w(t) U(w, t)` (the expanded-agent identity of
[[corr-core-inventory]] 002, one lemma).
Source: [[corr-core-inventory]] 002 / corrigibility-discussion-outline.md l. 7 (`E_{P'}[U*] = ∑_θ P'(θ) E[U_θ ∣ θ]`)
Kind: L
Fidelity: exact -/
lemma expect_kernelProd (μ : Distr W) (k : W → Distr T) (U : W × T → ℝ) :
    expect (kernelProd μ k) U = ∑ w, μ.mass w * ∑ t, (k w).mass t * U (w, t) := by
  unfold expect
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun w _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun t _ => by rw [kernelProd_mass, mul_assoc]

end Products

section JointObs

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep Ω A₁ A₂)

/-- The joint `P(ω, o; a₁) = μ_{a₁}(ω) P(o | ω; a₁)` on `Ω × Obs`, as a FAF `Distr`: the carrier
on which the observation is a *partition* (`Prod.snd`), so Good's theorem on a finite
partition (T16) specialises to the parent's `voiButton`.
Source: [[corr-wf14-inventory]] 001 / filler.md R1 (the joint); miri.md Dict-1
Kind: D
Fidelity: exact -/
noncomputable def jointDistr (a : A₁) : Distr (Ω × Obs) where
  mass p := (S.μ a).mass p.1 * S.obsWeight a p.2 p.1
  nonneg p := mul_nonneg ((S.μ a).nonneg _) (S.obsWeight_nonneg a _ _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    have h : ∀ ω, ∑ o, (S.μ a).mass ω * S.obsWeight a o ω = (S.μ a).mass ω := fun ω => by
      rw [Obs.sum_eq, obsWeight_press, obsWeight_silent]; ring
    simp only [h]
    exact (S.μ a).sum_eq_one

/-- Mass of the joint. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma jointDistr_mass (a : A₁) (ω : Ω) (o : Obs) :
    (jointDistr S a).mass (ω, o) = (S.μ a).mass ω * S.obsWeight a o ω := rfl

end JointObs

end Cleanroom.Corrigibility.CorrThreeStepFacts
