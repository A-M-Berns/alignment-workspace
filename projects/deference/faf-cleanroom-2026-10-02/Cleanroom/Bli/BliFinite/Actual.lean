import Cleanroom.Bli.BliFinite.Round

/-!
# `bli-finite` · Actual: actual tables and states of a rational history (T8)

The written-out state `⌜𝐐_m = Q⌝` of Appendix B is the *rounded* day-`m` table of the base
(bli-paper-032/033). Over a rational-valued history (`RatHistory`), `actualTable` reads the
day's small prices and `actualState` rounds them to the grid. The program's
`actualTable (Q : History)` over FAF's real-valued `History` is *not* definable with `ℚ`
tables; the hook for real histories is `Bridge.lean` (`RationalBeliefState` quotes).
-/

namespace Cleanroom.Bli.BliFinite

open LogicalInduction

/-- A rational-valued price history: one rational price per day and sentence.
Source: bli-paper-032; mandate T8
Kind: D
Fidelity: variant: `ℚ`-valued in place of FAF's real `History` (bridged in `Bridge.lean`) -/
abbrev RatHistory : Type := ℕ → Sentence → ℚ

/-- The day-`m` table of a rational history: its prices on the day-`m` small sentences.
Source: bli-paper-032
Kind: D
Fidelity: exact -/
def actualTable (𝒮 : SmallIndex) (Q : RatHistory) (m : ℕ) : Table 𝒮 m := fun φ => Q m φ.1

/-- The day-`m` **actual state**: the actual table rounded to the day-`m` grid — the written-out
state `⌜𝐐_m = Q⌝` names.
Source: bli-paper-032/033 (the written-out state is the rounded table)
Kind: D
Fidelity: exact (coordinatewise rounding) -/
def actualState (𝒮 : SmallIndex) (d : ℕ → ℕ) (Q : RatHistory) (m : ℕ) : Table 𝒮 m :=
  roundTo (d m) (actualTable 𝒮 Q m)

variable {𝒮 : SmallIndex} {d : ℕ → ℕ} {Q : RatHistory} {m : ℕ}

/-- The actual state is a grid table.
Source: bli-paper-033
Kind: L
Fidelity: exact -/
lemma actualState_mem_grid : actualState 𝒮 d Q m ∈ grid 𝒮 d m :=
  roundTo_mem_grid _

/-- A history with prices in `[0,1]` has actual tables in the unit cube.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma actualTable_inUnit (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) : (actualTable 𝒮 Q m).InUnit :=
  fun φ => hQ m φ.1

/-- The actual state is within half a grid step of the actual price, for a history in `[0,1]`.
Source: bli-paper-033 (`‖D_n(Q) − Q‖_∞ ≤ ε_n`)
Kind: L
Fidelity: exact -/
lemma actualState_err (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) (hd : 0 < d m) (φ : ↥(𝒮.S m)) :
    |actualState 𝒮 d Q m φ - Q m φ.1| ≤ 1 / (2 * d m) :=
  roundTo_err hd (actualTable_inUnit hQ) φ

/-- When the actual table is already a grid table, the actual state is the actual table.
Source: [[bli-program]] §2.2 (the "denominator grid" remark)
Kind: L
Fidelity: exact -/
lemma actualState_eq_of_mem_grid (hd : 0 < d m) (h : actualTable 𝒮 Q m ∈ grid 𝒮 d m) :
    actualState 𝒮 d Q m = actualTable 𝒮 Q m :=
  roundTo_eq_self_of_mem_grid hd h

end Cleanroom.Bli.BliFinite
