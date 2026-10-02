import Cleanroom.Bli.UdtBliCore.Mugging
import Mathlib.Tactic.FinCases

/-!
# `udt-bli-sist` · FourTables: the four `0/1` tables on `witIndex`'s day 1

`udt-bli-core`'s `mugTables` has three of the four `0/1` tables on the two day-1 sentences `p`, `q`
(`Ask = (1,0)`, `Rec = (0,1)`, `Other = (0,0)`); the fourth, `Both = (1,1)`, is what a second
ask-like table (the symmetric model's `Ask₂`, repair round 1 A1) and a second class (the CM/PH
witness of T3(b)) need. `fourTables := {Ask, Both, Rec, Other}`, with the state coordinate
`fourState : Fin 4 → ↥fourTables` (`0 ↦ Ask`, `1 ↦ Both`, `2 ↦ Rec`, `3 ↦ Other`) and the
`0/1` fact that gives faith by `faith_of_zeroOne`.

Source: repair round 1 (audit A1 and A2/B1); mandate §3.2 (branch predicates on tables).
-/

namespace Cleanroom.Bli.UdtBliSist

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliCore.Mugging Finset

/-- The `Both` table: `p ↦ 1`, `q ↦ 1`.
Source: repair round 1 (a second ask-like table); mandate §3.2
Kind: D
Fidelity: exact -/
def mBoth : Table witIndex 1 := fun _ => 1

/-- The day-1 coin `p` as a small sentence.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev pS : ↥(witIndex.S 1) := ⟨pW, pW_mem_S1⟩

/-- The day-1 sentence `q` as a small sentence.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev qS : ↥(witIndex.S 1) := ⟨qW, qW_mem_S1⟩

/-- `Both ≠ Ask` (they differ at `q`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mBoth_ne_mAsk : mBoth ≠ mAsk := fun h => by
  have := congrFun h qS
  simp [mBoth, mAsk, pW_ne_qW.symm] at this

/-- `Both ≠ Rec` (they differ at `p`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mBoth_ne_mRec : mBoth ≠ mRec := fun h => by
  have := congrFun h pS
  simp [mBoth, mRec] at this

/-- `Both ≠ Other`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mBoth_ne_mOther : mBoth ≠ mOther := fun h => by
  have := congrFun h pS
  simp [mBoth, mOther] at this

/-- **The four-table carrier** `{Ask, Both, Rec, Other}`.
Source: repair round 1; mandate §3.2
Kind: D
Fidelity: exact -/
def fourTables : Finset (Table witIndex 1) := {mAsk, mBoth, mRec, mOther}

/-- `Ask ∈ fourTables`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mAsk_mem4 : mAsk ∈ fourTables := by simp [fourTables]

/-- `Both ∈ fourTables`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mBoth_mem4 : mBoth ∈ fourTables := by simp [fourTables]

/-- `Rec ∈ fourTables`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mRec_mem4 : mRec ∈ fourTables := by simp [fourTables]

/-- `Other ∈ fourTables`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mOther_mem4 : mOther ∈ fourTables := by simp [fourTables]

/-- `Ask` as an element of the carrier.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev fAsk : ↥fourTables := ⟨mAsk, mAsk_mem4⟩

/-- `Both` as an element of the carrier.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev fBoth : ↥fourTables := ⟨mBoth, mBoth_mem4⟩

/-- `Rec` as an element of the carrier.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev fRec : ↥fourTables := ⟨mRec, mRec_mem4⟩

/-- `Other` as an element of the carrier.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev fOther : ↥fourTables := ⟨mOther, mOther_mem4⟩

/-- `fAsk ≠ fBoth`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fAsk_ne_fBoth : fAsk ≠ fBoth := fun h => mBoth_ne_mAsk (congrArg Subtype.val h).symm

/-- `fAsk ≠ fRec`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fAsk_ne_fRec : fAsk ≠ fRec := fun h => mAsk_ne_mRec (congrArg Subtype.val h)

/-- `fAsk ≠ fOther`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fAsk_ne_fOther : fAsk ≠ fOther := fun h => mAsk_ne_mOther (congrArg Subtype.val h)

/-- `fBoth ≠ fRec`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fBoth_ne_fRec : fBoth ≠ fRec := fun h => mBoth_ne_mRec (congrArg Subtype.val h)

/-- `fBoth ≠ fOther`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fBoth_ne_fOther : fBoth ≠ fOther := fun h => mBoth_ne_mOther (congrArg Subtype.val h)

/-- `fRec ≠ fOther`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fRec_ne_fOther : fRec ≠ fOther := fun h => mRec_ne_mOther (congrArg Subtype.val h)

/-- Every element of the carrier is one of the four tables.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eq_four (T : ↥fourTables) : T = fAsk ∨ T = fBoth ∨ T = fRec ∨ T = fOther := by
  rcases T with ⟨T, hT⟩
  simp only [fourTables, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-- The carrier's tables are `0/1`-valued (so faith is `faith_of_zeroOne`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma four_zeroOne : ∀ (T : ↥fourTables) (φ : ↥(witIndex.S 1)), T.1 φ = 0 ∨ T.1 φ = 1 := by
  intro T φ
  rcases eq_four T with rfl | rfl | rfl | rfl
  · simp only [mAsk]; split_ifs <;> simp
  · simp [mBoth]
  · simp only [mRec]; split_ifs <;> simp
  · simp [mOther]

/-- The state coordinate: `0 ↦ Ask`, `1 ↦ Both`, `2 ↦ Rec`, `3 ↦ Other`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def fourState : Fin 4 → ↥fourTables
  | 0 => fAsk
  | 1 => fBoth
  | 2 => fRec
  | 3 => fOther

/-- `fourState 0 = fAsk`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma fourState_zero : fourState 0 = fAsk := rfl

/-- `fourState 1 = fBoth`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma fourState_one : fourState 1 = fBoth := rfl

/-- `fourState 2 = fRec`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma fourState_two : fourState 2 = fRec := rfl

/-- `fourState 3 = fOther`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma fourState_three : fourState 3 = fOther := rfl

/-- `fourState` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fourState_injective : Function.Injective fourState := by
  intro s s' h
  fin_cases s <;> fin_cases s' <;>
    first
    | rfl
    | exact absurd h fAsk_ne_fBoth
    | exact absurd h fAsk_ne_fRec
    | exact absurd h fAsk_ne_fOther
    | exact absurd h fBoth_ne_fRec
    | exact absurd h fBoth_ne_fOther
    | exact absurd h fRec_ne_fOther
    | exact absurd h.symm fAsk_ne_fBoth
    | exact absurd h.symm fAsk_ne_fRec
    | exact absurd h.symm fAsk_ne_fOther
    | exact absurd h.symm fBoth_ne_fRec
    | exact absurd h.symm fBoth_ne_fOther
    | exact absurd h.symm fRec_ne_fOther

/-- `fourState s = fourState s' ↔ s = s'`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fourState_eq_iff (s s' : Fin 4) : fourState s = fourState s' ↔ s = s' :=
  fourState_injective.eq_iff

/-- The uniform point weights `1/2` on the carrier.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def fourHalf : ↥fourTables → Bool → ℚ := fun _ _ => 1 / 2

/-- `fourHalf` sums to one at every table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fourHalf_sum : ∀ T, ∑ a, fourHalf T a = 1 := by
  intro T; simp [fourHalf]

end Cleanroom.Bli.UdtBliSist
