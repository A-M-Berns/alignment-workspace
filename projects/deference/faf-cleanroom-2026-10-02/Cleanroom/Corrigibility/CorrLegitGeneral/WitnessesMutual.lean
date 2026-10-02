import Cleanroom.Corrigibility.CorrLegitGeneral.Mutual
import Cleanroom.Corrigibility.CorrLegitGeneral.Eval
import Cleanroom.Lit.LitDdbFacts.Examples

/-!
# corr-legit-general — witnesses on four worlds, III: mutual deference (T8)

Two clear frames on `Fin 4`. `clearA` (cells `{0,1}`, `{2,3}`) and `clearH` (cells `{0,1,2}`,
`{3}`) disagree at `0`, are non-dogmatic there, and `clearA.P 0` does not totally trust `clearH`
(the forward theorem's conclusion fails with one relation missing). `clearA` and `clearH'`
(cells `{0,1}`, `{2}`, `{3}`) are distinct frames agreeing at `0`, so they trust each other's
frames (the converse).
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

open Cleanroom.Lit.LitDdbFacts.Examples in
/-- The agent's clear frame: cells `{0, 1}`, `{2, 3}` with uniform rows.
Source: mandate T8 (witness; no example in the source)
Kind: D
Fidelity: n/a -/
def clearA : Frame (Fin 4) :=
  mk4 ![1 / 2, 1 / 2, 0, 0] ![1 / 2, 1 / 2, 0, 0] ![0, 0, 1 / 2, 1 / 2] ![0, 0, 1 / 2, 1 / 2]
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

open Cleanroom.Lit.LitDdbFacts.Examples in
/-- The humans' clear frame disagreeing at world `0`: cells `{0, 1, 2}`, `{3}`.
Source: mandate T8 (witness)
Kind: D
Fidelity: n/a -/
def clearH : Frame (Fin 4) :=
  mk4 ![1 / 3, 1 / 3, 1 / 3, 0] ![1 / 3, 1 / 3, 1 / 3, 0] ![1 / 3, 1 / 3, 1 / 3, 0] ![0, 0, 0, 1]
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

open Cleanroom.Lit.LitDdbFacts.Examples in
/-- A second humans' frame agreeing with `clearA` on the cell `{0, 1}` but finer elsewhere:
cells `{0, 1}`, `{2}`, `{3}`. Distinct from `clearA` (at world `2`).
Source: mandate T8 (witness)
Kind: D
Fidelity: n/a -/
def clearH' : Frame (Fin 4) :=
  mk4 ![1 / 2, 1 / 2, 0, 0] ![1 / 2, 1 / 2, 0, 0] ![0, 0, 1, 0] ![0, 0, 0, 1]
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- The rows of the three frames.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem clear_P : (clearA.P 0 = ![1 / 2, 1 / 2, 0, 0] ∧ clearA.P 1 = ![1 / 2, 1 / 2, 0, 0] ∧
      clearA.P 2 = ![0, 0, 1 / 2, 1 / 2] ∧ clearA.P 3 = ![0, 0, 1 / 2, 1 / 2]) ∧
    (clearH.P 0 = ![1 / 3, 1 / 3, 1 / 3, 0] ∧ clearH.P 1 = ![1 / 3, 1 / 3, 1 / 3, 0] ∧
      clearH.P 2 = ![1 / 3, 1 / 3, 1 / 3, 0] ∧ clearH.P 3 = ![0, 0, 0, 1]) ∧
    (clearH'.P 0 = ![1 / 2, 1 / 2, 0, 0] ∧ clearH'.P 1 = ![1 / 2, 1 / 2, 0, 0] ∧
      clearH'.P 2 = ![0, 0, 1, 0] ∧ clearH'.P 3 = ![0, 0, 0, 1]) :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The distinct rows differ.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem clear_ne : (![1 / 2, 1 / 2, 0, 0] : Fin 4 → ℝ) ≠ ![0, 0, 1 / 2, 1 / 2] ∧
    (![1 / 3, 1 / 3, 1 / 3, 0] : Fin 4 → ℝ) ≠ ![0, 0, 0, 1] ∧
    (![1 / 2, 1 / 2, 0, 0] : Fin 4 → ℝ) ≠ ![0, 0, 1, 0] ∧
    (![1 / 2, 1 / 2, 0, 0] : Fin 4 → ℝ) ≠ ![0, 0, 0, 1] ∧
    (![0, 0, 1, 0] : Fin 4 → ℝ) ≠ ![0, 0, 0, 1] := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrFun h 0; norm_num at this
  · have := congrFun h 0; norm_num at this
  · have := congrFun h 0; norm_num at this
  · have := congrFun h 0; norm_num at this
  · have := congrFun h 2
    norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two] at this

/-- The cells of the three frames.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem clear_cell : (clearA.cell ![1 / 2, 1 / 2, 0, 0] = {0, 1} ∧
      clearA.cell ![0, 0, 1 / 2, 1 / 2] = {2, 3}) ∧
    (clearH.cell ![1 / 3, 1 / 3, 1 / 3, 0] = {0, 1, 2} ∧ clearH.cell ![0, 0, 0, 1] = {3}) ∧
    (clearH'.cell ![1 / 2, 1 / 2, 0, 0] = {0, 1} ∧ clearH'.cell ![0, 0, 1, 0] = {2} ∧
      clearH'.cell ![0, 0, 0, 1] = {3}) := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨h0, h1, h2, h3⟩, ⟨g0, g1, g2, g3⟩⟩ := clear_P
  obtain ⟨n1, n2, n3, n4, n5⟩ := clear_ne
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · ext w; fin_cases w
    · show (0 : Fin 4) ∈ clearA.cell ![1 / 2, 1 / 2, 0, 0] ↔ (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))
      rw [Frame.mem_cell, a0]
      exact iff_of_true rfl (by simp)
    · show (1 : Fin 4) ∈ clearA.cell ![1 / 2, 1 / 2, 0, 0] ↔ (1 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))
      rw [Frame.mem_cell, a1]
      exact iff_of_true rfl (by simp)
    · show (2 : Fin 4) ∈ clearA.cell ![1 / 2, 1 / 2, 0, 0] ↔ (2 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))
      rw [Frame.mem_cell, a2]
      exact iff_of_false n1.symm (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
    · show (3 : Fin 4) ∈ clearA.cell ![1 / 2, 1 / 2, 0, 0] ↔ (3 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))
      rw [Frame.mem_cell, a3]
      exact iff_of_false n1.symm (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  · ext w; fin_cases w
    · show (0 : Fin 4) ∈ clearA.cell ![0, 0, 1 / 2, 1 / 2] ↔ (0 : Fin 4) ∈ ({2, 3} : Finset (Fin 4))
      rw [Frame.mem_cell, a0]
      exact iff_of_false n1 (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
    · show (1 : Fin 4) ∈ clearA.cell ![0, 0, 1 / 2, 1 / 2] ↔ (1 : Fin 4) ∈ ({2, 3} : Finset (Fin 4))
      rw [Frame.mem_cell, a1]
      exact iff_of_false n1 (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
    · show (2 : Fin 4) ∈ clearA.cell ![0, 0, 1 / 2, 1 / 2] ↔ (2 : Fin 4) ∈ ({2, 3} : Finset (Fin 4))
      rw [Frame.mem_cell, a2]
      exact iff_of_true rfl (by simp)
    · show (3 : Fin 4) ∈ clearA.cell ![0, 0, 1 / 2, 1 / 2] ↔ (3 : Fin 4) ∈ ({2, 3} : Finset (Fin 4))
      rw [Frame.mem_cell, a3]
      exact iff_of_true rfl (by simp)
  · ext w; fin_cases w
    · show (0 : Fin 4) ∈ clearH.cell ![1 / 3, 1 / 3, 1 / 3, 0] ↔ (0 : Fin 4) ∈ ({0, 1, 2} : Finset (Fin 4))
      rw [Frame.mem_cell, h0]
      exact iff_of_true rfl (by simp)
    · show (1 : Fin 4) ∈ clearH.cell ![1 / 3, 1 / 3, 1 / 3, 0] ↔ (1 : Fin 4) ∈ ({0, 1, 2} : Finset (Fin 4))
      rw [Frame.mem_cell, h1]
      exact iff_of_true rfl (by simp)
    · show (2 : Fin 4) ∈ clearH.cell ![1 / 3, 1 / 3, 1 / 3, 0] ↔ (2 : Fin 4) ∈ ({0, 1, 2} : Finset (Fin 4))
      rw [Frame.mem_cell, h2]
      exact iff_of_true rfl (by simp)
    · show (3 : Fin 4) ∈ clearH.cell ![1 / 3, 1 / 3, 1 / 3, 0] ↔ (3 : Fin 4) ∈ ({0, 1, 2} : Finset (Fin 4))
      rw [Frame.mem_cell, h3]
      exact iff_of_false n2.symm (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  · ext w; fin_cases w
    · show (0 : Fin 4) ∈ clearH.cell ![0, 0, 0, 1] ↔ (0 : Fin 4) ∈ ({3} : Finset (Fin 4))
      rw [Frame.mem_cell, h0]
      exact iff_of_false n2 (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
    · show (1 : Fin 4) ∈ clearH.cell ![0, 0, 0, 1] ↔ (1 : Fin 4) ∈ ({3} : Finset (Fin 4))
      rw [Frame.mem_cell, h1]
      exact iff_of_false n2 (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
    · show (2 : Fin 4) ∈ clearH.cell ![0, 0, 0, 1] ↔ (2 : Fin 4) ∈ ({3} : Finset (Fin 4))
      rw [Frame.mem_cell, h2]
      exact iff_of_false n2 (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
    · show (3 : Fin 4) ∈ clearH.cell ![0, 0, 0, 1] ↔ (3 : Fin 4) ∈ ({3} : Finset (Fin 4))
      rw [Frame.mem_cell, h3]
      exact iff_of_true rfl (by simp)
  · ext w; fin_cases w
    · show (0 : Fin 4) ∈ clearH'.cell ![1 / 2, 1 / 2, 0, 0] ↔ (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))
      rw [Frame.mem_cell, g0]
      exact iff_of_true rfl (by simp)
    · show (1 : Fin 4) ∈ clearH'.cell ![1 / 2, 1 / 2, 0, 0] ↔ (1 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))
      rw [Frame.mem_cell, g1]
      exact iff_of_true rfl (by simp)
    · show (2 : Fin 4) ∈ clearH'.cell ![1 / 2, 1 / 2, 0, 0] ↔ (2 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))
      rw [Frame.mem_cell, g2]
      exact iff_of_false n3.symm (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
    · show (3 : Fin 4) ∈ clearH'.cell ![1 / 2, 1 / 2, 0, 0] ↔ (3 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))
      rw [Frame.mem_cell, g3]
      exact iff_of_false n4.symm (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  · ext w; fin_cases w
    · show (0 : Fin 4) ∈ clearH'.cell ![0, 0, 1, 0] ↔ (0 : Fin 4) ∈ ({2} : Finset (Fin 4))
      rw [Frame.mem_cell, g0]
      exact iff_of_false n3 (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
    · show (1 : Fin 4) ∈ clearH'.cell ![0, 0, 1, 0] ↔ (1 : Fin 4) ∈ ({2} : Finset (Fin 4))
      rw [Frame.mem_cell, g1]
      exact iff_of_false n3 (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
    · show (2 : Fin 4) ∈ clearH'.cell ![0, 0, 1, 0] ↔ (2 : Fin 4) ∈ ({2} : Finset (Fin 4))
      rw [Frame.mem_cell, g2]
      exact iff_of_true rfl (by simp)
    · show (3 : Fin 4) ∈ clearH'.cell ![0, 0, 1, 0] ↔ (3 : Fin 4) ∈ ({2} : Finset (Fin 4))
      rw [Frame.mem_cell, g3]
      exact iff_of_false n5.symm (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  · ext w; fin_cases w
    · show (0 : Fin 4) ∈ clearH'.cell ![0, 0, 0, 1] ↔ (0 : Fin 4) ∈ ({3} : Finset (Fin 4))
      rw [Frame.mem_cell, g0]
      exact iff_of_false n4 (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
    · show (1 : Fin 4) ∈ clearH'.cell ![0, 0, 0, 1] ↔ (1 : Fin 4) ∈ ({3} : Finset (Fin 4))
      rw [Frame.mem_cell, g1]
      exact iff_of_false n4 (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
    · show (2 : Fin 4) ∈ clearH'.cell ![0, 0, 0, 1] ↔ (2 : Fin 4) ∈ ({3} : Finset (Fin 4))
      rw [Frame.mem_cell, g2]
      exact iff_of_false n5 (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
    · show (3 : Fin 4) ∈ clearH'.cell ![0, 0, 0, 1] ↔ (3 : Fin 4) ∈ ({3} : Finset (Fin 4))
      rw [Frame.mem_cell, g3]
      exact iff_of_true rfl (by simp)

/-- The three frames are immodest (clear): each row's self-cell has mass one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem clear_immodest : clearA.Immodest ∧ clearH.Immodest ∧ clearH'.Immodest := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨h0, h1, h2, h3⟩, ⟨g0, g1, g2, g3⟩⟩ := clear_P
  obtain ⟨⟨cA0, cA2⟩, ⟨cH0, cH3⟩, ⟨cG0, cG2, cG3⟩⟩ := clear_cell
  refine ⟨fun w => ?_, fun w => ?_, fun w => ?_⟩
  · fin_cases w
    · show clearA.selfMass (clearA.P 0) = 1
      unfold Frame.selfMass; rw [a0, cA0]; unfold mass
      first
        | (rw [Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_singleton]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
    · show clearA.selfMass (clearA.P 1) = 1
      unfold Frame.selfMass; rw [a1, cA0]; unfold mass
      first
        | (rw [Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_singleton]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
    · show clearA.selfMass (clearA.P 2) = 1
      unfold Frame.selfMass; rw [a2, cA2]; unfold mass
      first
        | (rw [Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_singleton]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
    · show clearA.selfMass (clearA.P 3) = 1
      unfold Frame.selfMass; rw [a3, cA2]; unfold mass
      first
        | (rw [Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_singleton]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
  · fin_cases w
    · show clearH.selfMass (clearH.P 0) = 1
      unfold Frame.selfMass; rw [h0, cH0]; unfold mass
      first
        | (rw [Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_singleton]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
    · show clearH.selfMass (clearH.P 1) = 1
      unfold Frame.selfMass; rw [h1, cH0]; unfold mass
      first
        | (rw [Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_singleton]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
    · show clearH.selfMass (clearH.P 2) = 1
      unfold Frame.selfMass; rw [h2, cH0]; unfold mass
      first
        | (rw [Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_singleton]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
    · show clearH.selfMass (clearH.P 3) = 1
      unfold Frame.selfMass; rw [h3, cH3]; unfold mass
      first
        | (rw [Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_singleton]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
  · fin_cases w
    · show clearH'.selfMass (clearH'.P 0) = 1
      unfold Frame.selfMass; rw [g0, cG0]; unfold mass
      first
        | (rw [Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_singleton]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
    · show clearH'.selfMass (clearH'.P 1) = 1
      unfold Frame.selfMass; rw [g1, cG0]; unfold mass
      first
        | (rw [Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_singleton]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
    · show clearH'.selfMass (clearH'.P 2) = 1
      unfold Frame.selfMass; rw [g2, cG2]; unfold mass
      first
        | (rw [Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_singleton]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
    · show clearH'.selfMass (clearH'.P 3) = 1
      unfold Frame.selfMass; rw [g3, cG3]; unfold mass
      first
        | (rw [Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])
        | (rw [Finset.sum_singleton]; norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three])

/-- **N+ (the forward theorem's hypotheses are non-trivial and its conclusion fails without one
relation)**: `clearA` and `clearH` are clear and non-dogmatic at `0`, their actual states differ,
and `clearA.P 0` does not totally trust `clearH` (bet `X = 𝟙_{2}`, `s = 1/3`).
Source: mandate T8 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem clearA_clearH_witness :
    clearA.P 0 ≠ clearH.P 0 ∧ 0 < mass (clearA.P 0) (clearH.cell (clearH.P 0)) ∧
      0 < mass (clearH.P 0) (clearA.cell (clearA.P 0)) ∧ ¬ TotalTrust (clearA.P 0) clearH := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨h0, h1, h2, h3⟩, _⟩ := clear_P
  obtain ⟨⟨cA0, _⟩, ⟨cH0, _⟩, _⟩ := clear_cell
  refine ⟨fun h => ?_, ?_, ?_, fun h => ?_⟩
  · have := congrFun h 0
    rw [a0, h0] at this
    norm_num at this
  · rw [h0, cH0, a0]
    norm_num [mass, Finset.sum_insert, Finset.sum_pair, Cleanroom.Lit.LitDdbFacts.Examples.vec4_two]
  · rw [a0, cA0, h0]; norm_num [mass, Finset.sum_pair, Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three]
  · have := h (ind {2}) (1 / 3)
    norm_num [Fin.sum_univ_four, E, ind, a0, h0, h1, h2, h3,
      Cleanroom.Lit.LitDdbFacts.Examples.vec4_two, Cleanroom.Lit.LitDdbFacts.Examples.vec4_three]
      at this

/-- **N+ for the converse**: `clearA` and `clearH'` are distinct clear frames whose actual
states at `0` agree, so they totally trust each other's frames.
Source: mandate T8 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem clearA_clearH'_witness : clearA.P 2 ≠ clearH'.P 2 ∧ clearA.P 0 = clearH'.P 0 ∧
    TotalTrust (clearA.P 0) clearH' ∧ TotalTrust (clearH'.P 0) clearA := by
  have heq : clearA.P 0 = clearH'.P 0 := rfl
  obtain ⟨hA, _, hH'⟩ := clear_immodest
  obtain ⟨⟨_, _, a2, _⟩, _, ⟨_, _, g2, _⟩⟩ := clear_P
  refine ⟨fun h => ?_, heq, (mutual_totalTrust_of_eq hA hH' 0 heq).1,
    (mutual_totalTrust_of_eq hA hH' 0 heq).2⟩
  have := congrFun h 2
  rw [a2, g2] at this
  norm_num [Cleanroom.Lit.LitDdbFacts.Examples.vec4_two] at this

end

end Cleanroom.Corrigibility.CorrLegitGeneral
