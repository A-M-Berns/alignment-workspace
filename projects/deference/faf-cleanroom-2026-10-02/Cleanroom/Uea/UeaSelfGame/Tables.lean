import Cleanroom.Uea.UeaSelfGame.Defs
import Cleanroom.Uea.UeaSelfGame.FinSums

/-!
# Tables on `Fin 2 → Fin 2` and `Fin 3 → Fin 2`

Infrastructure for the instance files: a function on policies given by its table of values (`tab2`,
`tab3`), `simp` lemmas evaluating it on literal policies `![i, j]` / `![i, j, k]`, extensionality for
`Fin 2`/`Fin 3`-indexed policies as a conjunction of entry equalities, the `muSelf` unfolding at a literal
own policy, and the conditional's numerator and denominator as nested sums over the entries.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

/-- A real-valued table on `Fin 2 → Fin 2` (`a = 0`, `b = 1`): `tab2 v00 v01 v10 v11 π = v_{π 0, π 1}`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def tab2 (v00 v01 v10 v11 : ℝ) (π : Fin 2 → Fin 2) : ℝ :=
  if π 0 = 0 then (if π 1 = 0 then v00 else v01) else (if π 1 = 0 then v10 else v11)

/-- A real-valued table on `Fin 3 → Fin 2`: `tab3 v000 … v111 π = v_{π 0, π 1, π 2}`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def tab3 (v000 v001 v010 v011 v100 v101 v110 v111 : ℝ) (π : Fin 3 → Fin 2) : ℝ :=
  if π 0 = 0 then
    (if π 1 = 0 then (if π 2 = 0 then v000 else v001) else (if π 2 = 0 then v010 else v011))
  else
    (if π 1 = 0 then (if π 2 = 0 then v100 else v101) else (if π 2 = 0 then v110 else v111))

section Eval

variable {v00 v01 v10 v11 : ℝ}
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

@[simp] theorem tab2_00 : tab2 v00 v01 v10 v11 ![0, 0] = v00 := by simp [tab2]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem tab2_01 : tab2 v00 v01 v10 v11 ![0, 1] = v01 := by simp [tab2]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem tab2_10 : tab2 v00 v01 v10 v11 ![1, 0] = v10 := by simp [tab2]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem tab2_11 : tab2 v00 v01 v10 v11 ![1, 1] = v11 := by simp [tab2]

variable {v000 v001 v010 v011 v100 v101 v110 v111 : ℝ}
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

@[simp] theorem tab3_000 : tab3 v000 v001 v010 v011 v100 v101 v110 v111 ![0, 0, 0] = v000 := by simp [tab3]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem tab3_001 : tab3 v000 v001 v010 v011 v100 v101 v110 v111 ![0, 0, 1] = v001 := by simp [tab3]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem tab3_010 : tab3 v000 v001 v010 v011 v100 v101 v110 v111 ![0, 1, 0] = v010 := by simp [tab3]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem tab3_011 : tab3 v000 v001 v010 v011 v100 v101 v110 v111 ![0, 1, 1] = v011 := by simp [tab3]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem tab3_100 : tab3 v000 v001 v010 v011 v100 v101 v110 v111 ![1, 0, 0] = v100 := by simp [tab3]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem tab3_101 : tab3 v000 v001 v010 v011 v100 v101 v110 v111 ![1, 0, 1] = v101 := by simp [tab3]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem tab3_110 : tab3 v000 v001 v010 v011 v100 v101 v110 v111 ![1, 1, 0] = v110 := by simp [tab3]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem tab3_111 : tab3 v000 v001 v010 v011 v100 v101 v110 v111 ![1, 1, 1] = v111 := by simp [tab3]

end Eval

/-- Bounds on a `tab2` from bounds on its four values.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem tab2_bounds {lo hi v00 v01 v10 v11 : ℝ} (h00 : lo ≤ v00 ∧ v00 ≤ hi) (h01 : lo ≤ v01 ∧ v01 ≤ hi)
    (h10 : lo ≤ v10 ∧ v10 ≤ hi) (h11 : lo ≤ v11 ∧ v11 ≤ hi) (π : Fin 2 → Fin 2) :
    lo ≤ tab2 v00 v01 v10 v11 π ∧ tab2 v00 v01 v10 v11 π ≤ hi := by
  unfold tab2; split_ifs <;> assumption

/-- Bounds on a `tab3` from bounds on its eight values.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem tab3_bounds {lo hi v000 v001 v010 v011 v100 v101 v110 v111 : ℝ}
    (h000 : lo ≤ v000 ∧ v000 ≤ hi) (h001 : lo ≤ v001 ∧ v001 ≤ hi) (h010 : lo ≤ v010 ∧ v010 ≤ hi)
    (h011 : lo ≤ v011 ∧ v011 ≤ hi) (h100 : lo ≤ v100 ∧ v100 ≤ hi) (h101 : lo ≤ v101 ∧ v101 ≤ hi)
    (h110 : lo ≤ v110 ∧ v110 ≤ hi) (h111 : lo ≤ v111 ∧ v111 ≤ hi) (π : Fin 3 → Fin 2) :
    lo ≤ tab3 v000 v001 v010 v011 v100 v101 v110 v111 π ∧
      tab3 v000 v001 v010 v011 v100 v101 v110 v111 π ≤ hi := by
  unfold tab3; split_ifs <;> assumption

/-- The sum of a `tab2` over all policies.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sum_tab2 (v00 v01 v10 v11 : ℝ) : ∑ π, tab2 v00 v01 v10 v11 π = v00 + v01 + v10 + v11 := by
  rw [sum_fin2_arrow]; simp [Fin.sum_univ_two]; ring

/-- The sum of a `tab3` over all policies.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sum_tab3 (v000 v001 v010 v011 v100 v101 v110 v111 : ℝ) :
    ∑ π, tab3 v000 v001 v010 v011 v100 v101 v110 v111 π =
      v000 + v001 + v010 + v011 + v100 + v101 + v110 + v111 := by
  rw [sum_fin3_arrow]; simp [Fin.sum_univ_two]; ring

/-- Extensionality on `Fin 2 → A` as a conjunction of entries.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem fin2_ext_iff {A : Type*} (π ρ : Fin 2 → A) : π = ρ ↔ π 0 = ρ 0 ∧ π 1 = ρ 1 := by
  rw [funext_iff, Fin.forall_fin_two]

/-- A universal statement over `Fin 3` as a conjunction of three (only `Fin 3` quantifiers match it, unlike
`Fin.forall_fin_succ`, which would also unfold `Fin 2` quantifiers and leave `Fin 0` residue).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem forall_fin_three {P : Fin 3 → Prop} : (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 := by
  rw [Fin.forall_fin_succ, Fin.forall_fin_two]
  rfl

/-- Extensionality on `Fin 3 → A` as a conjunction of entries.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem fin3_ext_iff {A : Type*} (π ρ : Fin 3 → A) : π = ρ ↔ π 0 = ρ 0 ∧ π 1 = ρ 1 ∧ π 2 = ρ 2 := by
  rw [funext_iff, Fin.forall_fin_succ, Fin.forall_fin_two]
  rfl

namespace Game

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- `muSelf` on `Fin 2`-indexed policies, with the point mass written entrywise.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem muSelf_apply_fin2 (G : Game (Fin 2) A) (π π' : Fin 2 → A) :
    G.muSelf π π' = (1 - G.δ) * (if π' 0 = π 0 ∧ π' 1 = π 1 then 1 else 0) + G.δ * G.Po π' := by
  unfold muSelf; simp only [fin2_ext_iff]

/-- `muSelf` on `Fin 3`-indexed policies, with the point mass written entrywise.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem muSelf_apply_fin3 (G : Game (Fin 3) A) (π π' : Fin 3 → A) :
    G.muSelf π π' =
      (1 - G.δ) * (if π' 0 = π 0 ∧ π' 1 = π 1 ∧ π' 2 = π 2 then 1 else 0) + G.δ * G.Po π' := by
  unfold muSelf; simp only [fin3_ext_iff]

/-- The conditional's denominator over `Fin 2 → A` as a nested sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_fin2 (μ : (Fin 2 → A) → ℝ) (s : Fin 2) (a : A) :
    condDen μ s a = ∑ x, ∑ y, if ![x, y] s = a then μ ![x, y] else 0 := by
  unfold condDen; exact sum_fin2_arrow _
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_fin2 (G : Game (Fin 2) A) (μ : (Fin 2 → A) → ℝ) (s : Fin 2) (a : A) :
    G.condNum μ s a = ∑ x, ∑ y, if ![x, y] s = a then μ ![x, y] * G.U ![x, y] else 0 := by
  unfold condNum; exact sum_fin2_arrow _

/-- The conditional's denominator over `Fin 3 → A` as a nested sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_fin3 (μ : (Fin 3 → A) → ℝ) (s : Fin 3) (a : A) :
    condDen μ s a = ∑ x, ∑ y, ∑ z, if ![x, y, z] s = a then μ ![x, y, z] else 0 := by
  unfold condDen; exact sum_fin3_arrow _
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_fin3 (G : Game (Fin 3) A) (μ : (Fin 3 → A) → ℝ) (s : Fin 3) (a : A) :
    G.condNum μ s a = ∑ x, ∑ y, ∑ z, if ![x, y, z] s = a then μ ![x, y, z] * G.U ![x, y, z] else 0 := by
  unfold condNum; exact sum_fin3_arrow _

end Game

end Cleanroom.Uea.UeaSelfGame
