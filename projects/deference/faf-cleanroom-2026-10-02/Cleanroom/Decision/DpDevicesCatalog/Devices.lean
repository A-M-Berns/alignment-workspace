import Cleanroom.Decision.DpDevicesCatalog.ToldYouSo

set_option autoImplicit false

/-!
# `dp-devices-catalog` — general device lemmas (infrastructure for T8)

Small tree-level facts the device table needs on every column:

* `paySum_eq_mul_nu_of_const`, `condExp_const`: an event all of whose leaf-worlds pay `c` has
  conditional value `c` (where realized);
* `payPoly_eq_C_mul_nuPoly_of_const`, `limitVal_of_const`: the tremble-limit act value of such
  an event is `c` (where tremble-realizable) — D4's cells on the mugging, TN-V2 and Told-You-So
  are all of this form;
* `limitVal_of_pos`: at a realized event the tremble-limit value is the strict conditional;
* `nu_pos_of_leaf`, `nuPoly_ne_zero_of_leaf`: one chance-positive leaf realizes an event.
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration

section general

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
  [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [∀ d, Nonempty (acts d)]

/-- If every leaf-world in `Y` pays `c`, then `𝔼[r 1_Y] = c · ν(Y)`.
Source: none: infrastructure
Kind: L -/
theorem paySum_eq_mul_nu_of_const (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (Y : Finset Ω)
    (c : ℚ) (h : ∀ ℓ, world B ℓ ∈ Y → payoff B ℓ = c) : paySum C B Y = c * nu C B Y := by
  unfold paySum nu mass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [worldEv, Finset.mem_filter] at hℓ
  rw [h ℓ hℓ.2]; ring

/-- **Constant-payoff events have that conditional value** where realized.
Source: none: infrastructure
Kind: L -/
theorem condExp_const (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (Y : Finset Ω) (c : ℚ)
    (h : ∀ ℓ, world B ℓ ∈ Y → payoff B ℓ = c) (hpos : 0 < nu C B Y) : condExp C B Y = c := by
  unfold condExp
  rw [paySum_eq_mul_nu_of_const C B Y c h, mul_div_assoc, div_self hpos.ne', mul_one]

/-- If every leaf-world in `Y` pays `c`, then `payPoly Y = C c · nuPoly Y`.
Source: none: infrastructure
Kind: L -/
theorem payPoly_eq_C_mul_nuPoly_of_const (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ)
    (Y : Finset Ω) (c : ℚ) (h : ∀ ℓ, world B ℓ ∈ Y → payoff B ℓ = c) :
    payPoly C B Y = Polynomial.C c * nuPoly C B Y := by
  unfold payPoly nuPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [worldEv, Finset.mem_filter] at hℓ
  rw [h ℓ hℓ.2]; ring

/-- **The tremble-limit value of a constant-payoff event is that payoff** (where
tremble-realizable).
Source: [[decision-problems-v2]] Remark 3.9 (advice stance); `calibration.md` D4
Kind: L -/
theorem limitVal_of_const (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (Y : Finset Ω) (c : ℚ)
    (h : ∀ ℓ, world B ℓ ∈ Y → payoff B ℓ = c) (hne : nuPoly C B Y ≠ 0) :
    limitVal C B Y = c := by
  unfold limitVal
  rw [payPoly_eq_C_mul_nuPoly_of_const C B Y c h, Polynomial.coeff_C_mul]
  have hc : (nuPoly C B Y).coeff (nuPoly C B Y).natTrailingDegree ≠ 0 :=
    Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hne
  field_simp

/-- **At a realized event the tremble-limit value is the strict conditional value.**
Source: [[decision-problems-v2]] Lemma 2 proof ("the limiting conditionals are the strict ones")
Kind: L -/
theorem limitVal_of_pos (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (Y : Finset Ω)
    (hpos : 0 < nu C B Y) : limitVal C B Y = paySum C B Y / nu C B Y := by
  unfold limitVal
  rw [(natTrailingDegree_nuPoly_eq_zero C B Y hpos).1, coeff_zero_payPoly, coeff_zero_nuPoly]

/-- One positive-mass leaf in `Y` realizes `Y`. Source: none: infrastructure. Kind: L -/
theorem nu_pos_of_leaf (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (Y : Finset Ω) (ℓ : B.Leaves)
    (hℓ : world B ℓ ∈ Y) (hpos : 0 < leafLaw C B ℓ) : 0 < nu C B Y := by
  unfold nu mass
  apply lt_of_lt_of_le hpos
  apply Finset.single_le_sum (fun ℓ' _ => leafLaw_nonneg _ B ℓ') (by simp [worldEv, hℓ])

/-- One chance-positive leaf in `Y` makes `Y` tremble-realizable. Source: none: infrastructure.
Kind: L -/
theorem nuPoly_ne_zero_of_leaf (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (Y : Finset Ω)
    (ℓ : B.Leaves) (hℓ : world B ℓ ∈ Y) (hpos : 0 < chanceWeight B ℓ) : nuPoly C B Y ≠ 0 :=
  (nuPoly_ne_zero_iff C B Y).mpr ⟨ℓ, hℓ, hpos⟩

/-- An event no leaf-world satisfies has `nuPoly = 0`. Source: none: infrastructure. Kind: L -/
theorem nuPoly_eq_zero_of_no_leaf (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (Y : Finset Ω)
    (h : ∀ ℓ, world B ℓ ∉ Y) : nuPoly C B Y = 0 := by
  by_contra hne
  obtain ⟨ℓ, hℓ, -⟩ := (nuPoly_ne_zero_iff C B Y).mp hne
  exact h ℓ hℓ

/-- Under a full-support procedure a chance-positive leaf realizes its event.
Source: none: infrastructure. Kind: L -/
theorem nu_pos_of_leaf_fullSupport {C : Proc ι acts ℚ} (hC : C.FullSupport) (B : Tree Ω ι acts ℚ)
    (Y : Finset Ω) (ℓ : B.Leaves) (hℓ : world B ℓ ∈ Y) (hpos : 0 < chanceWeight B ℓ) :
    0 < nu C B Y :=
  nu_pos_of_leaf C B Y ℓ hℓ (leafLaw_pos_of_fullSupport hC B ℓ hpos)

end general

end Cleanroom.Decision.DpDevicesCatalog
