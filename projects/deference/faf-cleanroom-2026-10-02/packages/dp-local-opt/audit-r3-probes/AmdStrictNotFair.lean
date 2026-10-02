import Cleanroom.Decision.DpLocalOpt.StrongFair
import Cleanroom.Decision.DpLocalOpt.AmdWitness

/-!
# Audit r3 (fidelity) probe: strong fairness is not *necessary* for the conclusion

The ledger row, the `GatedInduction.lean` header and the docstring of
`almostFair_strictLocalMax_not_isOptimal` say "strong fairness is necessary" for
`stronglyFair_strictLocalMax_isOptimal`. What the package shows is that the hypothesis cannot be
weakened to `AlmostFair` (`twoStag`). It is not necessary for the conclusion: v2's absent-minded
driver is nested (not almost fair, hence not strongly fair), and its unique strict local maximum
`q = 1/3` is the global maximum. Not imported by the library.
-/

namespace Cleanroom.Decision.DpLocalOpt.AuditR3

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt

/-- The AMD is not strongly fair (it is nested at its point). -/
theorem amd_not_stronglyFair : ¬ StronglyFair amd := fun h => h.not_nested () amd_nested

/-- **On the AMD the optimum `q = 1/3` is a strict local maximum** (`ε = 1`):
`V(r) = (1 − r)(3r + 1)` and `4/3 − V(r) = 3 (r − 1/3)² > 0` for `r ≠ 1/3`. -/
theorem amd_third_isStrictLocalMax :
    IsStrictLocalMax (procQ (1/3) (by norm_num) (by norm_num)) amd := by
  refine ⟨1, one_pos, fun C' hne _ => ?_⟩
  obtain ⟨d, -, hd⟩ := hne
  rw [Proc.unit_eq_procQ C'] at hd ⊢
  have hne' : (C' ()).w .a ≠ 1/3 := by
    intro h
    apply hd
    cases d
    apply FinDistr.ext'
    intro a
    cases a <;> simp [procQ, h]
  rw [← amdShape_eq_amd, amdShape_value, amdShape_value]
  have hsq : 0 < ((C' ()).w .a - 1/3) * ((C' ()).w .a - 1/3) :=
    mul_self_pos.mpr (sub_ne_zero.mpr hne')
  nlinarith [hsq]

/-- **The conclusion of the general theorem holds on a tree that is not strongly fair**: the
AMD's strict local maximum at `q = 1/3` is global. So "strong fairness is necessary" means only
"cannot be weakened to almost-fairness", not a converse. -/
theorem amd_conclusion_without_strongFairness :
    ¬ StronglyFair amd ∧
    IsStrictLocalMax (procQ (1/3) (by norm_num) (by norm_num)) amd ∧
    IsOptimal (procQ (1/3) (by norm_num) (by norm_num)) amd :=
  ⟨amd_not_stronglyFair, amd_third_isStrictLocalMax, (amd_isOptimal_iff _ _ _).mpr rfl⟩

end Cleanroom.Decision.DpLocalOpt.AuditR3
