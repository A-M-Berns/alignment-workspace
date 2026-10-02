import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# `udt-harmony-bargain` — counting sums over acceptable sets by membership bits

A sum over all `Finset α` of a summand that depends only on whether one or two fixed elements
belong to the set collapses to `2^(|α|−1)` or `2^(|α|−2)` copies of the finitely many bit-values.
This is the mandate's "group the 32 opponent proposals by the membership bits" and replaces every
enumeration of acceptable sets (plan rule 8).
-/

namespace Cleanroom.Udt.UdtHarmonyBargain

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **One-bit grouping**: `∑_S F([x ∈ S]) = 2^(|α|−1) (F false + F true)`.
Source: mandate T4 (grouping by membership bits)
Kind: P -/
theorem sum_finset_one_bit (x : α) (F : Bool → ℚ) :
    ∑ S : Finset α, F (decide (x ∈ S)) = 2 ^ (Fintype.card α - 1) * (F false + F true) := by
  set T := univ.erase x with hT
  have hx : x ∉ T := by simp [hT]
  have huniv : (univ : Finset α) = insert x T := by
    rw [hT, insert_erase (mem_univ x)]
  rw [← powerset_univ, huniv, sum_powerset_insert hx]
  have hcard : T.card = Fintype.card α - 1 := by
    rw [hT, card_erase_of_mem (mem_univ x), card_univ]
  have e1 : ∀ S ∈ T.powerset, F (decide (x ∈ S)) = F false := by
    intro S hS
    have hxS : x ∉ S := fun h => hx ((mem_powerset.mp hS) h)
    simp [hxS]
  have e2 : ∀ S ∈ T.powerset, F (decide (x ∈ insert x S)) = F true := by
    intro S _
    simp
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_const, sum_const, card_powerset, hcard]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- **Two-bit grouping**: for `x ≠ y`,
`∑_S F([x ∈ S], [y ∈ S]) = 2^(|α|−2) (F ff ff + F ff tt + F tt ff + F tt tt)`.
Source: mandate T4 (grouping by membership bits)
Kind: P -/
theorem sum_finset_two_bits {x y : α} (hxy : x ≠ y) (F : Bool → Bool → ℚ) :
    ∑ S : Finset α, F (decide (x ∈ S)) (decide (y ∈ S)) =
      2 ^ (Fintype.card α - 2) * (F false false + F false true + F true false + F true true) := by
  set T := (univ.erase x).erase y with hT
  have hyT : y ∉ T := by simp [hT]
  have hxT : x ∉ T := by simp [hT]
  have hx : x ∉ insert y T := by simp [hT, hxy]
  have huniv : (univ : Finset α) = insert x (insert y T) := by
    rw [hT, insert_erase (by simp [hxy.symm]), insert_erase (mem_univ x)]
  rw [← powerset_univ, huniv, sum_powerset_insert hx, sum_powerset_insert hyT,
    sum_powerset_insert hyT]
  have hcard : T.card = Fintype.card α - 2 := by
    rw [hT, card_erase_of_mem (by simp [hxy.symm]), card_erase_of_mem (mem_univ x), card_univ]
    omega
  have e1 : ∀ S ∈ T.powerset, F (decide (x ∈ S)) (decide (y ∈ S)) = F false false := by
    intro S hS
    have hxS : x ∉ S := fun h => hxT ((mem_powerset.mp hS) h)
    have hyS : y ∉ S := fun h => hyT ((mem_powerset.mp hS) h)
    simp [hxS, hyS]
  have e2 : ∀ S ∈ T.powerset, F (decide (x ∈ insert y S)) (decide (y ∈ insert y S)) =
      F false true := by
    intro S hS
    have hxS : x ∉ S := fun h => hxT ((mem_powerset.mp hS) h)
    simp [hxS, hxy]
  have e3 : ∀ S ∈ T.powerset, F (decide (x ∈ insert x S)) (decide (y ∈ insert x S)) =
      F true false := by
    intro S hS
    have hyS : y ∉ S := fun h => hyT ((mem_powerset.mp hS) h)
    simp [hyS, hxy.symm]
  have e4 : ∀ S ∈ T.powerset, F (decide (x ∈ insert x (insert y S)))
      (decide (y ∈ insert x (insert y S))) = F true true := by
    intro S _
    simp
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3, sum_congr rfl e4, sum_const, sum_const,
    sum_const, sum_const, card_powerset, hcard]
  simp only [nsmul_eq_mul]
  push_cast
  ring

end Cleanroom.Udt.UdtHarmonyBargain
