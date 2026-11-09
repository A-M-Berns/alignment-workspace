/-
# The rational row alternative

Round `projects/normativity/rounds/2026-11-08-content-recollection/`.

A finite list of rational rows `a · x ≤ b` either has a rational solution or carries
nonnegative multipliers whose weighted coefficient sum vanishes and whose weighted constant
sum is negative (`alternative`); and where it has a solution, every row valid on the solution
set is a nonnegative combination of the list's rows with slack (`entails_iff`).  Both are the
pinned `EconCSLib` results `EconCSLib.LinearAlgebra.theorem_of_alternative` and
`farkas_lemma`, which hold over any linearly ordered field, read into the repository's `Row`.
The pinned Mathlib has the closed-cone form over real inner product spaces only; `EconCSLib`
arrives through the pinned Formalized-Agent-Foundations manifest.

Consequences here: a rational system feasible over `ℝ` is feasible over `ℚ`
(`exists_rat_of_real`); the cube rows as a list (`cubeRows_sat_iff`, `mem_cubeRows`); a
bundle's region as the solution set of one list (`region_iff_satAll`, `regionR_iff_satR`).

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.SeedStatics
import EconCSLib.Math.LinearAlgebra.Farkas

namespace Workspace.Normativity.Contrib.RowAlternative

open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Finset

variable {d : ℕ}

/-- Every row of a list holds at a rational point. -/
def SatAll (L : List (Row d)) (x : Fin d → ℚ) : Prop := ∀ r ∈ L, r.Sat x

instance (L : List (Row d)) (x : Fin d → ℚ) : Decidable (SatAll L x) := by
  unfold SatAll; infer_instance

theorem satAll_append (L L' : List (Row d)) (x : Fin d → ℚ) :
    SatAll (L ++ L') x ↔ SatAll L x ∧ SatAll L' x := by
  simp [SatAll, List.mem_append, or_imp, forall_and]

/-- **Weights**: nonnegative multipliers on the rows of a list, by position. -/
structure Weights (L : List (Row d)) where
  u : Fin L.length → ℚ
  nonneg : ∀ k, 0 ≤ u k

namespace Weights

variable {L : List (Row d)}

/-- The weighted coefficient sum at a coordinate. -/
def coeff (w : Weights L) (j : Fin d) : ℚ := ∑ k, w.u k * (L.get k).a j

/-- The weighted constant sum. -/
def const (w : Weights L) : ℚ := ∑ k, w.u k * (L.get k).b

/-- The weighted sum of satisfied rows: `(Σ u_k a_k) · x ≤ Σ u_k b_k`. -/
theorem sum_le (w : Weights L) {x : Fin d → ℚ} (hx : SatAll L x) :
    ∑ j, w.coeff j * x j ≤ w.const := by
  have h1 : ∑ j, w.coeff j * x j = ∑ k, w.u k * ∑ j, (L.get k).a j * x j := by
    unfold coeff
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (hx _ (List.get_mem L k)) (w.nonneg k)

/-- The same at a real point. -/
theorem sum_leR (w : Weights L) {x : Fin d → ℝ} (hx : ∀ r ∈ L, r.SatR x) :
    ∑ j, (w.coeff j : ℝ) * x j ≤ (w.const : ℝ) := by
  have h1 : ∑ j, (w.coeff j : ℝ) * x j
      = ∑ k, (w.u k : ℝ) * ∑ j, ((L.get k).a j : ℝ) * x j := by
    unfold coeff
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1]
  unfold const
  push_cast
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (hx _ (List.get_mem L k)) (by exact_mod_cast w.nonneg k)

end Weights

/-- **The alternative over `ℚ`, for a finite family of rows.**  The family has no rational
solution iff it carries nonnegative multipliers with vanishing coefficient sum and negative
constant sum. -/
theorem alternative_family {I : Type*} [Fintype I] [DecidableEq I] (rows : I → Row d) :
    (¬ ∃ x, ∀ i, (rows i).Sat x) ↔
      ∃ u : I → ℚ, (∀ i, 0 ≤ u i) ∧ (∀ j, ∑ i, u i * (rows i).a j = 0) ∧
        ∑ i, u i * (rows i).b < 0 := by
  have key := EconCSLib.LinearAlgebra.theorem_of_alternative (𝕜 := ℚ)
    (fun (i : I) j => -(rows i).a j) (fun i => -(rows i).b)
  constructor
  · intro h
    have hinf : ¬ EconCSLib.LinearAlgebra.IsFeasible
        (fun (i : I) j => -(rows i).a j) (fun i => -(rows i).b) := by
      rintro ⟨x, hx⟩
      refine h ⟨x, fun i => ?_⟩
      have hi := hx i
      unfold EconCSLib.LinearAlgebra.rowEval at hi
      simp only [neg_mul, Finset.sum_neg_distrib] at hi
      unfold Row.Sat
      linarith
    obtain ⟨u, hu0, hcoef, hconst⟩ := key.1 hinf
    refine ⟨u, hu0, fun j => ?_, ?_⟩
    · have hj := hcoef j
      simp only [mul_neg, Finset.sum_neg_distrib, neg_eq_zero] at hj
      exact hj
    · simp only [mul_neg, Finset.sum_neg_distrib] at hconst
      linarith
  · rintro ⟨u, hu0, hc, hb⟩ ⟨x, hx⟩
    have h1 : ∑ i, u i * ∑ j, (rows i).a j * x j ≤ ∑ i, u i * (rows i).b :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hu0 i)
    have h2 : ∑ i, u i * ∑ j, (rows i).a j * x j = ∑ j, (∑ i, u i * (rows i).a j) * x j := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [h2] at h1
    simp only [hc, zero_mul, Finset.sum_const_zero] at h1
    linarith

/-- **Entailment over `ℚ`, for a finite family of rows.**  Where the family has a rational
solution, a row is valid at every solution iff it is a nonnegative combination of the family's
rows with slack in the constant. -/
theorem entails_family {I : Type*} [Fintype I] [DecidableEq I] (rows : I → Row d) (g : Row d)
    (hfeas : ∃ x, ∀ i, (rows i).Sat x) :
    (∀ x, (∀ i, (rows i).Sat x) → g.Sat x) ↔
      ∃ u : I → ℚ, (∀ i, 0 ≤ u i) ∧ (∀ j, ∑ i, u i * (rows i).a j = g.a j) ∧
        ∑ i, u i * (rows i).b ≤ g.b := by
  have hS : EconCSLib.LinearAlgebra.IsFeasible
      (fun (i : I) j => -(rows i).a j) (fun i => -(rows i).b) := by
    obtain ⟨x, hx⟩ := hfeas
    refine ⟨x, fun i => ?_⟩
    have hi := hx i
    unfold Row.Sat at hi
    unfold EconCSLib.LinearAlgebra.rowEval
    simp only [neg_mul, Finset.sum_neg_distrib]
    linarith
  have key := EconCSLib.LinearAlgebra.farkas_lemma (𝕜 := ℚ)
    (fun (i : I) j => -(rows i).a j) (fun i => -(rows i).b)
    (fun j => -g.a j) (-g.b) hS
  constructor
  · intro h
    have hprimal : ∀ x : Fin d → ℚ,
        (∀ i : I, -(rows i).b ≤ ∑ j, -(rows i).a j * x j) →
          -g.b ≤ ∑ j, -g.a j * x j := by
      intro x hx
      have hsat : ∀ i, (rows i).Sat x := by
        intro i
        have hi := hx i
        simp only [neg_mul, Finset.sum_neg_distrib] at hi
        unfold Row.Sat
        linarith
      have hg := h x hsat
      unfold Row.Sat at hg
      simp only [neg_mul, Finset.sum_neg_distrib]
      linarith
    obtain ⟨u, hu0, hcoef, hconst⟩ := key.1 hprimal
    refine ⟨u, hu0, fun j => ?_, ?_⟩
    · have hj := hcoef j
      simp only [mul_neg, Finset.sum_neg_distrib, neg_inj] at hj
      exact hj
    · simp only [mul_neg, Finset.sum_neg_distrib] at hconst
      linarith
  · rintro ⟨u, hu0, hc, hb⟩ x hx
    have h1 : ∑ i, u i * ∑ j, (rows i).a j * x j ≤ ∑ i, u i * (rows i).b :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hu0 i)
    have h2 : ∑ i, u i * ∑ j, (rows i).a j * x j = ∑ j, (∑ i, u i * (rows i).a j) * x j := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [h2] at h1
    simp only [hc] at h1
    unfold Row.Sat
    linarith

lemma satAll_iff_get (L : List (Row d)) (x : Fin d → ℚ) :
    SatAll L x ↔ ∀ k : Fin L.length, (L.get k).Sat x := by
  constructor
  · exact fun h k => h _ (List.get_mem L k)
  · intro h r hr
    obtain ⟨k, rfl⟩ := List.mem_iff_get.1 hr
    exact h k

/-- **The alternative over `ℚ`**, for a list of rows: no rational solution iff weights with
vanishing coefficient sum and negative constant sum. -/
theorem alternative (L : List (Row d)) :
    (¬ ∃ x, SatAll L x) ↔ ∃ w : Weights L, (∀ j, w.coeff j = 0) ∧ w.const < 0 := by
  simp only [satAll_iff_get]
  rw [alternative_family L.get]
  constructor
  · rintro ⟨u, hu0, hc, hb⟩
    exact ⟨⟨u, hu0⟩, hc, hb⟩
  · rintro ⟨w, hc, hb⟩
    exact ⟨w.u, w.nonneg, hc, hb⟩

/-- **Entailment over `ℚ`**, for a list of rows with a rational solution: a row is valid at
every solution iff it is a weighted sum of the list's rows with slack in the constant. -/
theorem entails_iff (L : List (Row d)) (g : Row d) (hfeas : ∃ x, SatAll L x) :
    (∀ x, SatAll L x → g.Sat x) ↔
      ∃ w : Weights L, (∀ j, w.coeff j = g.a j) ∧ w.const ≤ g.b := by
  simp only [satAll_iff_get] at hfeas ⊢
  rw [entails_family L.get g hfeas]
  constructor
  · rintro ⟨u, hu0, hc, hb⟩
    exact ⟨⟨u, hu0⟩, hc, hb⟩
  · rintro ⟨w, hc, hb⟩
    exact ⟨w.u, w.nonneg, hc, hb⟩

/-- **A rational system feasible over `ℝ` is feasible over `ℚ`.** -/
theorem exists_rat_of_real (L : List (Row d))
    (h : ∃ x : Fin d → ℝ, ∀ r ∈ L, r.SatR x) : ∃ x : Fin d → ℚ, SatAll L x := by
  by_contra hno
  obtain ⟨w, hc, hb⟩ := (alternative L).1 hno
  obtain ⟨x, hx⟩ := h
  have := w.sum_leR hx
  simp only [hc, Rat.cast_zero, zero_mul, Finset.sum_const_zero] at this
  have hb' : (w.const : ℝ) < 0 := by exact_mod_cast hb
  linarith

/-! ## The cube rows as a list -/

theorem mem_cubeRows (r : Row d) :
    r ∈ cubeRows d ↔ (∃ i, r = cubeUpper i) ∨ (∃ i, r = cubeLower i) := by
  simp only [cubeRows, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨i, rfl | rfl⟩
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨i, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨i, Or.inl rfl⟩
    · exact ⟨i, Or.inr rfl⟩

theorem cubeRows_sat_iff (x : Fin d → ℚ) : SatAll (cubeRows d) x ↔ InCube x := by
  constructor
  · intro h i
    have hu := h _ ((mem_cubeRows _).2 (Or.inl ⟨i, rfl⟩))
    have hl := h _ ((mem_cubeRows _).2 (Or.inr ⟨i, rfl⟩))
    unfold Row.Sat cubeUpper at hu
    unfold Row.Sat cubeLower at hl
    simp only [ite_mul, one_mul, neg_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at hu hl
    exact ⟨by linarith, hu⟩
  · intro h r hr
    rcases (mem_cubeRows r).1 hr with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact cubeUpper_sat h i
    · exact cubeLower_sat h i

/-- A bundle's region is the solution set of its rows and the cube rows. -/
theorem region_iff_satAll {Q : Type*} (B : Bundle Q d) (y : Fin d → ℚ) :
    B.Region y ↔ SatAll (B.map CitedRow.row ++ cubeRows d) y := by
  rw [satAll_append, cubeRows_sat_iff]
  unfold Bundle.Region SatAll
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact and_comm

/-- The same at real points. -/
theorem regionR_iff_satR {Q : Type*} (B : Bundle Q d) (y : Fin d → ℝ) :
    B.RegionR y ↔ ∀ r ∈ B.map CitedRow.row ++ cubeRows d, r.SatR y := by
  have hsplit : (∀ r ∈ B.map CitedRow.row ++ cubeRows d, r.SatR y) ↔
      (∀ r ∈ B.map CitedRow.row, r.SatR y) ∧ ∀ r ∈ cubeRows d, r.SatR y := by
    simp only [List.mem_append, or_imp, forall_and]
  rw [hsplit, cubeRows_satR_iff]
  unfold Bundle.RegionR
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact and_comm

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.RowAlternative.SatAll
#print axioms Workspace.Normativity.Contrib.RowAlternative.satAll_append
#print axioms Workspace.Normativity.Contrib.RowAlternative.Weights
#print axioms Workspace.Normativity.Contrib.RowAlternative.Weights.coeff
#print axioms Workspace.Normativity.Contrib.RowAlternative.Weights.const
#print axioms Workspace.Normativity.Contrib.RowAlternative.Weights.sum_le
#print axioms Workspace.Normativity.Contrib.RowAlternative.Weights.sum_leR
#print axioms Workspace.Normativity.Contrib.RowAlternative.alternative_family
#print axioms Workspace.Normativity.Contrib.RowAlternative.entails_family
#print axioms Workspace.Normativity.Contrib.RowAlternative.satAll_iff_get
#print axioms Workspace.Normativity.Contrib.RowAlternative.alternative
#print axioms Workspace.Normativity.Contrib.RowAlternative.entails_iff
#print axioms Workspace.Normativity.Contrib.RowAlternative.exists_rat_of_real
#print axioms Workspace.Normativity.Contrib.RowAlternative.mem_cubeRows
#print axioms Workspace.Normativity.Contrib.RowAlternative.cubeRows_sat_iff
#print axioms Workspace.Normativity.Contrib.RowAlternative.region_iff_satAll
#print axioms Workspace.Normativity.Contrib.RowAlternative.regionR_iff_satR

end Workspace.Normativity.Contrib.RowAlternative
