import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The data-cost ledger: UDT1.0 versus UDT1.1 (T15(a))

T15(a) of [[dp-faithful-udt-mandate]] (`firstperson.md` FP-14′ (ii)–(iv)): UDT1.1 consumes `V_B`
on all of `Π_U` — `∏_d |A_d|` values — while UDT1.0 (Definition 17's componentwise `UDT_{s°,ρ}`,
cUDT with PDC) consumes the Hamming-1 neighbourhood of the current profile — `1 + ∑_d (|A_d| − 1)`
values; the second is at most the first, with equality iff at most one point has `|A_d| > 1`
(`hamming_le_prod`, `hamming_eq_prod_iff`). The missing profiles are the Stag Hunt's `(S,S)`:
UDT1.0's discount buys its bad equilibria (`PiB.lean`, `twoStag_piA_ne_piB`).

Pure finite combinatorics; no FAF or tree object is involved.
-/

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset

/-- **FP-14′(iv), the inequality**: for `n : U → ℕ` with `1 ≤ n d`,
`1 + ∑_{d ∈ U} (n d − 1) ≤ ∏_{d ∈ U} n d` — the Hamming-1 neighbourhood of a profile is no larger
than the profile space.
Source: `firstperson.md` FP-14′ ("(iii) UDT1.0 … `1 + ∑_d(|A_d| − 1)` values. (iv) Equality iff at
most one point has `|A_d| > 1`"); dp-cf-114
Kind: P
Fidelity: exact
Hyps: (a) `∀ d ∈ U, 1 ≤ n d` -/
theorem hamming_le_prod {ι : Type} [DecidableEq ι] (U : Finset ι) (n : ι → ℕ)
    (hn : ∀ d ∈ U, 1 ≤ n d) : 1 + ∑ d ∈ U, (n d - 1) ≤ ∏ d ∈ U, n d := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert d U hd ih =>
      rw [Finset.sum_insert hd, Finset.prod_insert hd]
      have ih' := ih fun e he => hn e (Finset.mem_insert_of_mem he)
      have hnd := hn d (Finset.mem_insert_self d U)
      obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hnd
      have hprod : 1 ≤ ∏ e ∈ U, n e :=
        Finset.one_le_prod' fun e he => hn e (Finset.mem_insert_of_mem he)
      obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hprod
      rw [hb] at ih' ⊢
      rw [ha, Nat.add_sub_cancel_left]
      nlinarith [ih']

/-- **FP-14′(iv), the equality case**: `1 + ∑_{d ∈ U} (n d − 1) = ∏_{d ∈ U} n d` iff at most one
point has `n d > 1` (`(2,2)`: `4` vs `3`; `(2,3)`: `6` vs `4`; `(3,3)`: `9` vs `5`).
Source: `firstperson.md` FP-14′ ("(iv) Equality iff at most one point has `|A_d| > 1`")
Kind: P
Fidelity: exact
Hyps: (a) `∀ d ∈ U, 1 ≤ n d` -/
theorem hamming_eq_prod_iff {ι : Type} [DecidableEq ι] (U : Finset ι) (n : ι → ℕ)
    (hn : ∀ d ∈ U, 1 ≤ n d) :
    1 + ∑ d ∈ U, (n d - 1) = ∏ d ∈ U, n d ↔ ∀ d ∈ U, ∀ e ∈ U, 1 < n d → 1 < n e → d = e := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert d U hd ih =>
      have hn' : ∀ e ∈ U, 1 ≤ n e := fun e he => hn e (Finset.mem_insert_of_mem he)
      have hnd := hn d (Finset.mem_insert_self d U)
      have hle := hamming_le_prod U n hn'
      have hprod : 1 ≤ ∏ e ∈ U, n e := Finset.one_le_prod' hn'
      obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hnd
      obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hprod
      have ih' := ih hn'
      rw [Finset.sum_insert hd, Finset.prod_insert hd, ha, hb, Nat.add_sub_cancel_left]
      rw [hb] at hle ih'
      constructor
      · intro h
        have hab : a * b = 0 := by nlinarith [h, hle]
        have hS : 1 + ∑ e ∈ U, (n e - 1) = 1 + b := by nlinarith [h, hle]
        have hb0 : 0 < a → b = 0 := by
          intro ha0
          rcases Nat.mul_eq_zero.mp hab with h0 | h0
          · omega
          · exact h0
        intro e he e' he' h1 h1'
        rcases Finset.mem_insert.mp he with rfl | heU
        · rcases Finset.mem_insert.mp he' with rfl | he'U
          · rfl
          · exfalso
            have := Finset.single_le_prod' hn' he'U
            rw [hb, hb0 (by omega)] at this
            omega
        · rcases Finset.mem_insert.mp he' with rfl | he'U
          · exfalso
            have := Finset.single_le_prod' hn' heU
            rw [hb, hb0 (by omega)] at this
            omega
          · exact ih'.mp hS e heU e' he'U h1 h1'
      · intro h
        by_cases ha0 : 0 < a
        · have hU1 : ∀ e ∈ U, n e = 1 := by
            intro e he
            by_contra hne
            have h1e : 1 < n e := lt_of_le_of_ne (hn' e he) (Ne.symm hne)
            have h1d : 1 < n d := by omega
            have := h d (Finset.mem_insert_self d U) e (Finset.mem_insert_of_mem he) h1d h1e
            rw [this] at hd
            exact hd he
          have hP : ∏ e ∈ U, n e = 1 := Finset.prod_eq_one hU1
          have hS0 : ∑ e ∈ U, (n e - 1) = 0 :=
            Finset.sum_eq_zero fun e he => by rw [hU1 e he]; rfl
          rw [hP] at hb
          have hb0 : b = 0 := by omega
          rw [hS0, hb0]
          ring
        · have ha0' : a = 0 := by omega
          have hpair : ∀ e ∈ U, ∀ e' ∈ U, 1 < n e → 1 < n e' → e = e' :=
            fun e he e' he' h1 h1' =>
              h e (Finset.mem_insert_of_mem he) e' (Finset.mem_insert_of_mem he') h1 h1'
          have := ih'.mpr hpair
          rw [ha0']
          simp only [zero_add, add_zero, one_mul]
          exact this

end Cleanroom.Decision.DpFaithfulUdt
