import Cleanroom.Bli.UdtBliCore.WitnessCorr

/-!
# `udt-paper-tiling` · Tables: a three-table carrier for the witnesses

`udt-bli-core` ships the two-table carrier `twoTables = {Ask, Rec}` (`WitnessCorr.lean`). Two of
this package's models need three observations: the "NAC ⇏ PC" model of T8(b) (a third
observation is what makes it work) and the Third Button's `{pre, red, green}` of T10(e). This
file adds the all-zero day-1 table `mZero` and the carrier `threeTables = {Ask, Rec, Zero}` with
the same conveniences (`X1`, `X2`, `X3`, the inequalities, `three_zeroOne` for `handPrior`,
`eq_X1_or_X2_or_X3`, `threeState`).

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

/-- The all-zero day-1 table.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def mZero : Table witIndex 1 := fun _ => 0

/-- `Zero ≠ Ask` (they differ at `p`). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mZero_ne_mAsk : mZero ≠ mAsk := fun h => by
  have := congrFun h ⟨pW, pW_mem_S1⟩
  simp [mZero, mAsk] at this

/-- `Zero ≠ Rec` (they differ at `q`). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mZero_ne_mRec : mZero ≠ mRec := fun h => by
  have := congrFun h ⟨qW, qW_mem_S1⟩
  simp [mZero, mRec, pW_ne_qW.symm] at this

/-- `Ask ≠ Zero`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mAsk_ne_mZero : mAsk ≠ mZero := mZero_ne_mAsk.symm
/-- `Rec ≠ Zero`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mRec_ne_mZero : mRec ≠ mZero := mZero_ne_mRec.symm
/-- `Rec ≠ Ask`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mRec_ne_mAsk' : mRec ≠ mAsk := mAsk_ne_mRec.symm

/-- The three-table carrier `{Ask, Rec, Zero}`.
Source: none: infrastructure (T8(b), T10(e))
Kind: D
Fidelity: n/a -/
def threeTables : Finset (Table witIndex 1) := {mAsk, mRec, mZero}

/-- `Ask ∈ threeTables`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mAsk_mem_three : mAsk ∈ threeTables := by simp [threeTables]
/-- `Rec ∈ threeTables`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mRec_mem_three : mRec ∈ threeTables := by simp [threeTables]
/-- `Zero ∈ threeTables`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mZero_mem_three : mZero ∈ threeTables := by simp [threeTables]

/-- The first table `X1 = Ask`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
abbrev X1 : ↥threeTables := ⟨mAsk, mAsk_mem_three⟩
/-- The second table `X2 = Rec`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
abbrev X2 : ↥threeTables := ⟨mRec, mRec_mem_three⟩
/-- The third table `X3 = Zero`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
abbrev X3 : ↥threeTables := ⟨mZero, mZero_mem_three⟩

/-- `X1 ≠ X2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma X1_ne_X2 : X1 ≠ X2 := fun h => mAsk_ne_mRec (congrArg Subtype.val h)
/-- `X1 ≠ X3`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma X1_ne_X3 : X1 ≠ X3 := fun h => mAsk_ne_mZero (congrArg Subtype.val h)
/-- `X2 ≠ X3`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma X2_ne_X3 : X2 ≠ X3 := fun h => mRec_ne_mZero (congrArg Subtype.val h)
/-- `X2 ≠ X1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma X2_ne_X1 : X2 ≠ X1 := X1_ne_X2.symm
/-- `X3 ≠ X1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma X3_ne_X1 : X3 ≠ X1 := X1_ne_X3.symm
/-- `X3 ≠ X2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma X3_ne_X2 : X3 ≠ X2 := X2_ne_X3.symm

instance : Nonempty ↥threeTables := ⟨X1⟩

/-- All three tables are `{0,1}`-valued (so `handPrior` applies).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma three_zeroOne : ∀ (T : ↥threeTables) (φ : ↥(witIndex.S 1)), T.1 φ = 0 ∨ T.1 φ = 1 := by
  rintro ⟨T, hT⟩ φ
  simp only [threeTables, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl
  · simp only [mAsk]; split_ifs <;> simp
  · simp only [mRec]; split_ifs <;> simp
  · simp [mZero]

/-- Every table of `threeTables` is `X1`, `X2` or `X3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eq_X1_or_X2_or_X3 (T : ↥threeTables) : T = X1 ∨ T = X2 ∨ T = X3 := by
  rcases T with ⟨T, hT⟩
  simp only [threeTables, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- The state coordinate `0 ↦ X1`, `1 ↦ X2`, `2 ↦ X3`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def threeState : Fin 3 → ↥threeTables
  | 0 => X1
  | 1 => X2
  | 2 => X3

/-- Two policies on `threeTables` agreeing at `X1`, `X2`, `X3` are equal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policy_ext {A : Type} {π π' : Policy threeTables A} (h1 : π X1 = π' X1) (h2 : π X2 = π' X2)
    (h3 : π X3 = π' X3) : π = π' := by
  funext T
  rcases eq_X1_or_X2_or_X3 T with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

end Cleanroom.Udt.UdtPaperTiling
