import Cleanroom.Corrigibility.CorrThreeStepFacts.WitnessesC

/-!
# Audit r2 (adversarial) probe — the hull condition has content and subsumes T8

Three checks on `Hull.HullCondition` that the package does not state:

* `refinesModNull_of_hull_id`: on the *full* question (`qOf = id`) the hull condition implies
  refinement modulo null worlds (via sufficiency and T8's iff) — so it specialises to mm I9.2's
  condition, as a necessary-and-sufficient candidate must.
* `not_hull_straddle`: the hull condition **fails** on the T8 straddle frame (`lowHalf | id`),
  so it is not a tautology of the encoding.
* `hullCondition_of_refinesModNull`: under refinement modulo null worlds the hull condition holds
  for *every* question, with `a h₀ ∈ {0, 1}` (`1` on pressed cells whose joint cell with `y₀`
  carries mass) and `b = 0` — T8's case is inside the hull condition, so the condition covers
  refinement, screening-off (`hullCondition_of_screensOff`) and the live `h3` frame at once.

Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts.AuditR2

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect
open Cleanroom.Corrigibility.CorrThreeStepFacts

/-- On the full question the hull condition implies refinement modulo null worlds. -/
theorem refinesModNull_of_hull_id {W H Y : Type*} [Fintype W] [DecidableEq W] [Fintype H]
    [DecidableEq H] [Fintype Y] [DecidableEq Y] (P : Distr W) (hOf : W → H) (yOf : W → Y)
    (hH : HullCondition P hOf yOf (id : W → W)) : RefinesModNull P hOf yOf := by
  rw [← refinesModNull_iff]
  intro X y₀
  have := commonPriorRule_pressExpectOn_nonpos_of_hull P hOf yOf id hH X y₀
  simpa using this

/-- The hull condition fails on the T8 straddle frame: worlds `0` and `1` share the `h`-cell
`{0, 1}`, differ in `y = id`, and carry mass, so refinement fails and, by the previous theorem,
so does the hull condition. -/
theorem not_hull_straddle :
    ¬ HullCondition unif4 lowHalf (id : Fin 4 → Fin 4) (id : Fin 4 → Fin 4) := by
  intro hH
  have hRef := refinesModNull_of_hull_id unif4 lowHalf id hH
  have h := hRef 0 1 (by decide) (by norm_num [unif4]) (by norm_num [unif4])
  simp at h

/-- Under refinement modulo null worlds the hull condition holds for every question:
`a h₀ = 1` iff the joint cell `(h₀, y₀)` carries mass (then `qVecY h₀ y₀ = qVec h₀` mod null),
`b = 0`. -/
theorem hullCondition_of_refinesModNull {W H Y Q : Type*} [Fintype W] [Fintype H] [DecidableEq H]
    [Fintype Y] [DecidableEq Y] [Fintype Q] [DecidableEq Q] (P : Distr W) (hOf : W → H)
    (yOf : W → Y) (qOf : W → Q) (hRef : RefinesModNull P hOf yOf) :
    HullCondition P hOf yOf qOf := by
  classical
  intro f y₀
  refine ⟨fun h₀ => if ∃ w ∈ (cell yOf y₀).filter (hOf · = h₀), 0 < P.mass w then 1 else 0,
    fun _ => 0, fun h₀ => by dsimp only; split_ifs <;> norm_num, fun _ => le_rfl, fun q => ?_⟩
  simp only [zero_mul, sum_const_zero, sub_zero]
  refine sum_congr rfl fun h₀ _ => ?_
  split_ifs with hex
  · rw [one_mul]
    obtain ⟨w₁, hw₁, hpos⟩ := hex
    unfold qVecY qVec
    rw [mem_filter, cell, mem_filter] at hw₁
    refine sum_subset (fun w hw => ?_) (fun w hw hw' => ?_)
    · rw [mem_filter, mem_filter] at hw
      rw [mem_filter, cell, mem_filter]
      exact ⟨⟨mem_univ _, hw.1.2⟩, hw.2⟩
    · rw [mem_filter, cell, mem_filter] at hw
      by_contra hne
      have hpos' : 0 < P.mass w := lt_of_le_of_ne (P.nonneg w) (Ne.symm hne)
      have hy := hRef w₁ w (by rw [hw₁.2, hw.1.2]) hpos hpos'
      apply hw'
      rw [mem_filter, mem_filter, cell, mem_filter]
      exact ⟨⟨⟨mem_univ _, by rw [← hy, hw₁.1.2]⟩, hw.1.2⟩, hw.2⟩
  · rw [zero_mul]
    push Not at hex
    unfold qVecY
    refine sum_eq_zero fun w hw => ?_
    rw [mem_filter] at hw
    exact le_antisymm (hex w hw.1) (P.nonneg w)

end Cleanroom.Corrigibility.CorrThreeStepFacts.AuditR2
