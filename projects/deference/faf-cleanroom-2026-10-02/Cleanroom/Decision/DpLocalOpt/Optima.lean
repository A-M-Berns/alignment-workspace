import Cleanroom.Decision.DpLocalOpt.Assignments

/-!
# `dp-local-opt`: Definition 21 — existence and vertex attainment (T5)

* (b) On almost-fair trees, over any linearly ordered field, some deterministic procedure is
  optimal (`exists_pure_isOptimal_of_almostFair`), from `dp-core-tree`'s shared-seed purification
  and the agreement of the semantics on almost-fair trees.
* (d) The AMD has no deterministic optimum (`amd_no_pure_optimum`), while ZO-6's nested shape
  `(2; 1, 5)` has one, at `δ_b` (`zo6Amd_pure_optimum`; the mandate's "at `δ_a`" is a slip:
  `V = 5 − 7q + 4q²` is convex with `V(0) = 5 > 2 = V(1)`). So "attained by a deterministic
  procedure iff no self-succession" is false as an iff; v2's "whenever … not in general" is
  exact.
* (a) over `ℝ` and (c) no optimum over `ℚ` are not shipped (see the report).
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [DecidableEq ι] [∀ d, DecidableEq (acts d)]

/-- **Definition 21's vertex clause (T5(b))**: on an almost-fair tree some deterministic
procedure is optimal, over any linearly ordered field.
Source: [[decision-problems-v2]] §6 Definition 21 (line 201, "attained by a deterministic
procedure whenever no path contains two nodes sharing a decision-point") | dp-core-029
Kind: C
Fidelity: exact (composition of `exists_pure_max_value'` and `AlmostFair.value_eq_value'`)
Hyps: (a) `AlmostFair B` (the clause's hypothesis) -/
theorem exists_pure_isOptimal_of_almostFair [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K)
    (h : AlmostFair B) :
    ∃ σ : (d : ι) → acts d, IsOptimal (Proc.ofFun σ) B := by
  obtain ⟨π, hπ, -, -⟩ := exists_pure_max_value' B
  exact ⟨π, fun C => by rw [h.value_eq_value' C]; exact hπ C⟩

/-- **The AMD has no deterministic optimum** (`0, 1 < 4/3`).
Source: [[decision-problems-v2]] §6 Definition 21 ("but not in general: Proposition 5(c) is a
problem whose best procedure is properly stochastic")
Kind: N+ -/
theorem amd_no_pure_optimum : ∀ σ : Unit → Act2, ¬ IsOptimal (Proc.ofFun σ) amd := by
  intro σ h
  have hle := h (procQ (1/3) (by norm_num) (by norm_num))
  rw [amd_value] at hle
  rcases amd_value_ofFun σ with h0 | h1
  · rw [h0] at hle; norm_num at hle
  · rw [h1] at hle; norm_num at hle

/-- ZO-6's `(2; 1, 5)` is nested at its point.
Source: none: infrastructure
Kind: L -/
theorem zo6Amd_nested : Nested zo6Amd () := by
  refine ⟨by decide, ⟨.b, ⟨.a, ()⟩⟩, ?_, ?_⟩
  · unfold Positive zo6Amd amdShape; simp
  · unfold zo6Amd amdShape; simp

/-- **A nested tree with a deterministic optimum (T5(d))**: on `(2; 1, 5)` the always-continue
procedure `δ_b` is optimal (`V = 5`), so "attained by a deterministic procedure **iff** no
self-succession" (dp-core-029's phrasing) fails as an iff.
Source: mandate T5(d) (corrected: the optimum is at `δ_b`, not `δ_a`); dp-core-029
Kind: N+
Fidelity: exact -/
theorem zo6Amd_pure_optimum :
    Nested zo6Amd () ∧ IsOptimal (Proc.ofFun fun _ => Act2.b) zo6Amd ∧
    value (Proc.ofFun fun _ => Act2.b) zo6Amd = 5 := by
  have hb : (Proc.ofFun fun _ => Act2.b : Proc Unit (fun _ => Act2) ℚ) = procQ 0 le_rfl zero_le_one := by
    funext u; cases u; simp [Proc.ofFun, procQ, pure_b_eq_act2]
  refine ⟨zo6Amd_nested, ?_, ?_⟩
  · rw [hb]; exact zo6Amd_isOptimal_zero
  · rw [hb, zo6Amd_value]; norm_num

end Cleanroom.Decision.DpLocalOpt
