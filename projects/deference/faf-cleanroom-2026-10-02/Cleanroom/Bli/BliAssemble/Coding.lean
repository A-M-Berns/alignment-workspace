import Cleanroom.Bli.BliAssemble.Defs
import Mathlib.Data.Nat.Digits.Defs

/-!
# `bli-assemble` · Coding: the write-out state coding (target 0)

`writeOutCoding 𝓜 : StateCoding 𝓜` — the coding of record for this package. The code of a
day-`m` table `Q` writes the **whole table out**: the grid numerators `⌊Q φ · d m⌋₊` along the
day-`m` small sentences in FAF-code order (`bli-superbelief`'s `encLE` sort, the same order the
tent product uses), then a terminating digit `1`, read as a numeral in base `4 (d m + 1)`, times
`4 ^ sizeBound m`. Hence:

* `inj` on the grid — the base exceeds every digit, the digit lists have one length, and the
  numerator is injective on `gridVals (d m)` (`Nat.ofDigits_inj_of_len_eq`).
* `large` — the factor `4 ^ sizeBound m` puts `sizeBound m ≤ log₄ code`.
* `writeOutCode_card_le_log` — **the write-out property**: `|S m| ≤ log₄ code`, so the state
  atom is at least as long as the tent expression is wide. This is what the mandate's Context
  identifies as load-bearing for the oracle's polynomial output bound (`R_length_le`): an
  arbitrary injective coding may give some grid tables codes of only `sizeBound m` digits while
  `tentExpr` has `≥ 88·|S m|` nodes with `|S m|` exponential in `sizeBound m`
  (`sizeBound_lt_card_smallSet`). Recorded as a finding against [[bli-program]] §3.4.

Not claimed here: computability of the coding in Lean's sense (the sorted small-sentence list
is noncomputable, as `smallSet` is — `bli-found`'s unlanded `smallList`), and decodability in
polynomial time. Both belong to the open computability statements of `Certificate.lean`.

Sources: bli-paper-032 ("written-out state"); [[bli-program]] §2.3, §3.4; mandate target 0
(`writeOutCoding`), Context.
-/

namespace Cleanroom.Bli.BliAssemble

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliSuperbelief

open Classical

noncomputable section

/-! ## Numerators and the sorted small sentences -/

/-- The grid numerator of a value: `⌊x · d⌋₊`, which is `k` on the grid value `k / d`.
Source: mandate target 0 (`writeOutCoding`: "numerators of `Q`")
Kind: D
Fidelity: n/a -/
def gridNumer (d : ℕ) (x : ℚ) : ℕ := ⌊x * d⌋₊

/-- The numerator of `k / d` is `k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gridNumer_div {d : ℕ} (hd : 0 < d) (k : ℕ) : gridNumer d ((k : ℚ) / d) = k := by
  unfold gridNumer
  rw [div_mul_cancel₀ _ (by exact_mod_cast hd.ne')]
  exact Nat.floor_natCast k

/-- The numerator is injective on the grid values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gridNumer_injOn {d : ℕ} (hd : 0 < d) {x y : ℚ} (hx : x ∈ gridVals d) (hy : y ∈ gridVals d)
    (h : gridNumer d x = gridNumer d y) : x = y := by
  obtain ⟨k, -, rfl⟩ := mem_gridVals_iff.mp hx
  obtain ⟨k', -, rfl⟩ := mem_gridVals_iff.mp hy
  rw [gridNumer_div hd, gridNumer_div hd] at h
  rw [h]

/-- The numerator of a grid value is at most `d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gridNumer_le {d : ℕ} (hd : 0 < d) {x : ℚ} (hx : x ∈ gridVals d) : gridNumer d x ≤ d := by
  obtain ⟨k, hk, rfl⟩ := mem_gridVals_iff.mp hx
  rw [gridNumer_div hd]; exact hk

/-- The day-`m` small sentences in FAF-code order (`bli-superbelief`'s sort).
Source: mandate target 0 ("sorted by FAF code … agrees with `bli-superbelief`'s `Finset.sort`")
Kind: D
Fidelity: n/a -/
def smallSorted (m : ℕ) : List ↥(smallIndex.S m) :=
  (Finset.univ : Finset ↥(smallIndex.S m)).sort (encLE smallIndex m)

/-- Every day-`m` small sentence is in the sorted list.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_smallSorted (m : ℕ) (φ : ↥(smallIndex.S m)) : φ ∈ smallSorted m :=
  (Finset.mem_sort _).mpr (Finset.mem_univ φ)

/-- The sorted list has `|S m|` entries.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma length_smallSorted (m : ℕ) : (smallSorted m).length = (smallSet m).card := by
  unfold smallSorted
  rw [Finset.length_sort _, Finset.card_univ, Fintype.card_coe]
  rfl

/-! ## The write-out code -/

/-- The digit list of a day-`m` table: its numerators along `smallSorted m`, then a `1`.
Source: mandate target 0 (`writeOutCoding`)
Kind: D
Fidelity: n/a -/
def writeOutDigits (𝓜 : Mesh) (m : ℕ) (Q : Table smallIndex m) : List ℕ :=
  ((smallSorted m).map fun φ => gridNumer (𝓜.d m) (Q φ)) ++ [1]

/-- The base of the write-out numeral: `4 (d m + 1)` — above every digit, and at least `4`.
Source: mandate target 0
Kind: D
Fidelity: n/a -/
def writeOutBase (𝓜 : Mesh) (m : ℕ) : ℕ := 4 * (𝓜.d m + 1)

/-- **The write-out code** of a day-`m` table: `4 ^ sizeBound m` times the digit list read in
base `writeOutBase 𝓜 m`.
Source: bli-paper-032; mandate target 0 (`writeOutCoding`)
Kind: D
Fidelity: n/a -/
def writeOutCode (𝓜 : Mesh) (m : ℕ) (Q : Table smallIndex m) : ℕ :=
  4 ^ sizeBound m * Nat.ofDigits (writeOutBase 𝓜 m) (writeOutDigits 𝓜 m Q)

/-- Every digit of a grid table's list is below the base.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma writeOutDigits_lt (𝓜 : Mesh) (m : ℕ) {Q : Table smallIndex m}
    (hQ : Q ∈ grid smallIndex 𝓜.d m) : ∀ x ∈ writeOutDigits 𝓜 m Q, x < writeOutBase 𝓜 m := by
  intro x hx
  unfold writeOutDigits at hx
  rw [List.mem_append, List.mem_map, List.mem_singleton] at hx
  unfold writeOutBase
  rcases hx with ⟨φ, -, rfl⟩ | rfl
  · have := gridNumer_le (𝓜.d_pos m) (mem_grid_iff.mp hQ φ)
    omega
  · omega

/-- The digit list has `|S m| + 1` entries.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma writeOutDigits_length (𝓜 : Mesh) (m : ℕ) (Q : Table smallIndex m) :
    (writeOutDigits 𝓜 m Q).length = (smallSet m).card + 1 := by
  unfold writeOutDigits
  rw [List.length_append, List.length_map, length_smallSorted]
  rfl

/-- The numeral is at least `base ^ |S m|` (the terminating digit).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ofDigits_writeOutDigits_ge (𝓜 : Mesh) (m : ℕ) (Q : Table smallIndex m) :
    writeOutBase 𝓜 m ^ (smallSet m).card ≤
      Nat.ofDigits (writeOutBase 𝓜 m) (writeOutDigits 𝓜 m Q) := by
  unfold writeOutDigits
  rw [Nat.ofDigits_append, Nat.ofDigits_singleton, mul_one, List.length_map, length_smallSorted]
  exact Nat.le_add_left _ _

/-- **Injectivity on the grid.**
Source: mandate target 0 (`inj`)
Kind: P
Fidelity: n/a -/
theorem writeOutCode_injOn (𝓜 : Mesh) (m : ℕ) :
    Set.InjOn (writeOutCode 𝓜 m) ↑(grid smallIndex 𝓜.d m) := by
  intro Q₁ hQ₁ Q₂ hQ₂ h
  unfold writeOutCode at h
  have hN : Nat.ofDigits (writeOutBase 𝓜 m) (writeOutDigits 𝓜 m Q₁) =
      Nat.ofDigits (writeOutBase 𝓜 m) (writeOutDigits 𝓜 m Q₂) :=
    Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hb : 1 < writeOutBase 𝓜 m := by unfold writeOutBase; omega
  have hL := Nat.ofDigits_inj_of_len_eq hb
    (by rw [writeOutDigits_length, writeOutDigits_length])
    (writeOutDigits_lt 𝓜 m hQ₁) (writeOutDigits_lt 𝓜 m hQ₂) hN
  unfold writeOutDigits at hL
  have hL' := List.append_cancel_right hL
  rw [List.map_inj_left] at hL'
  funext φ
  exact gridNumer_injOn (𝓜.d_pos m) (mem_grid_iff.mp hQ₁ φ) (mem_grid_iff.mp hQ₂ φ)
    (hL' φ (mem_smallSorted m φ))

/-- **Largeness**: `sizeBound m ≤ log₄ code`, from the factor `4 ^ sizeBound m`.
Source: mandate target 0 (`large`)
Kind: P
Fidelity: n/a -/
theorem writeOutCode_large (𝓜 : Mesh) (m : ℕ) (Q : Table smallIndex m) :
    sizeBound m ≤ Nat.log 4 (writeOutCode 𝓜 m Q) := by
  apply Nat.le_log_of_pow_le (by norm_num)
  unfold writeOutCode
  have h1 : 1 ≤ Nat.ofDigits (writeOutBase 𝓜 m) (writeOutDigits 𝓜 m Q) :=
    le_trans (Nat.one_le_pow _ _ (by unfold writeOutBase; omega)) (ofDigits_writeOutDigits_ge 𝓜 m Q)
  exact Nat.le_mul_of_pos_right _ h1

/-- **The write-out property**: the code has at least `|S m|` base-4 digits —
`|S m| ≤ log₄ code` — so the atom is at least as long as the tent expression is wide. This is
the property the mandate's Context identifies as load-bearing for the oracle's polynomial
output bound, and which an arbitrary injective coding lacks.
Source: mandate target 0 ("the length lower bound `|S m| ≤ Nat.log 4 (code m Q)`"), Context
Kind: P
Fidelity: n/a -/
theorem writeOutCode_card_le_log (𝓜 : Mesh) (m : ℕ) (Q : Table smallIndex m) :
    (smallSet m).card ≤ Nat.log 4 (writeOutCode 𝓜 m Q) := by
  apply Nat.le_log_of_pow_le (by norm_num)
  unfold writeOutCode
  calc 4 ^ (smallSet m).card ≤ writeOutBase 𝓜 m ^ (smallSet m).card :=
        Nat.pow_le_pow_left (by unfold writeOutBase; omega) _
    _ ≤ Nat.ofDigits (writeOutBase 𝓜 m) (writeOutDigits 𝓜 m Q) := ofDigits_writeOutDigits_ge 𝓜 m Q
    _ ≤ 4 ^ sizeBound m * Nat.ofDigits (writeOutBase 𝓜 m) (writeOutDigits 𝓜 m Q) :=
        Nat.le_mul_of_pos_left _ (by positivity)

/-- **The write-out coding of record** (target 0): `writeOutCode` as a `StateCoding`.
Source: bli-paper-032; [[bli-program]] §2.3; mandate target 0 (`writeOutCoding`)
Kind: D
Fidelity: exact -/
def writeOutCoding (𝓜 : Mesh) : StateCoding 𝓜 where
  code := writeOutCode 𝓜
  inj := writeOutCode_injOn 𝓜
  large := fun m Q _ => writeOutCode_large 𝓜 m Q

/-- Unfolding `writeOutCoding`'s code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma writeOutCoding_code (𝓜 : Mesh) (m : ℕ) (Q : Table smallIndex m) :
    (writeOutCoding 𝓜).code m Q = writeOutCode 𝓜 m Q := rfl

end

end Cleanroom.Bli.BliAssemble
