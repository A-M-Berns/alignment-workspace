import Cleanroom.Decision.DpCartesianFrames.DiagStruct
import Cleanroom.Decision.DpCartesianFrames.Cff8

/-!
# Audit r4 (adversarial) probe: the degenerate instances of ZO-5(b)/(c)

Ledger row 95 says of `diagStruct_injective_of_not_nestedFiber` that "trivially satisfiable
instances exist (`U = ∅`)". The degenerate class is larger: on any **chance-free** tree
`ChanceProfile B` is a subsingleton (`ChanceFree.subsingleton`, `Cff8.lean`), so
`diagStruct U B` is injective and `FrLit U B ≅ Fr B` for **every** `U` — including a `U`
whose fiber *is* nested. So (i) ZO-5(c)'s hypothesis is sufficient, not necessary (as the
source's "iff `E' = E_B`" already says: both sides are empty on a chance-free tree), and
(ii) a witness for the "if" theorem must have a chance node that is actually copied — the
catalogue's mugging with `U = {d}` (the fidelity auditor's parallel probe) is such an
instance; `U = ∅` and chance-free trees are not.

Not imported by the library.
-/

namespace Cleanroom.Decision.DpCartesianFrames.AuditR4

open CartesianFrames CategoryTheory
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpCartesianFrames

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [DecidableEq ι] [∀ d, Fintype (acts d)] (U : Finset ι)

/-- On a chance-free tree the structural diagonal is injective for every `U`, for the
trivial reason: there is one column. -/
theorem injective_diagStruct_of_chanceFree (B : Tree Ω ι acts K) (h : ChanceFree B) :
    Function.Injective (diagStruct U B) :=
  fun ε ε' _ => (ChanceFree.subsingleton B h).elim ε ε'

/-- Hence `FrLit U B ≅ Fr B` on every chance-free tree, for every `U` — nested or not. -/
theorem frLit_iso_fr_of_chanceFree (B : Tree Ω ι acts K) (h : ChanceFree B) :
    Nonempty (FrLit U B ≅ Fr B) :=
  ⟨frLitIsoFr_of_injective U B (injective_diagStruct_of_chanceFree U B h)⟩

/-- A chance-free tree with a **nested** `d`-fiber: `d` → `a` → `d` → leaf; `d` → `b` → leaf. -/
def nestedCF : Tree Bool Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .decision () fun _ => .leaf true 0
    | .b => .leaf true 0

theorem nestedCF_chanceFree : ChanceFree nestedCF := by
  intro act
  cases act
  · intro _; trivial
  · trivial

/-- Its `d`-fiber is nested (the inner `d`-node lies below the outer one). -/
theorem nestedCF_nestedFiber : NestedFiber nestedCF () :=
  ⟨some ⟨.a, none⟩, (mem_fiber _ _ _).2 rfl, fun h => h (by show () ∈ [()]; simp)⟩

/-- **The iso holds with a nested `U`-fiber**: ZO-5(c)'s hypothesis is sufficient, not
necessary, and the degenerate instances of `frLitIsoFr_of_injective` include every
chance-free tree with any `U`. -/
theorem nestedCF_frLit_iso :
    NestedFiber nestedCF () ∧ Nonempty (FrLit ({()} : Finset Unit) nestedCF ≅ Fr nestedCF) :=
  ⟨nestedCF_nestedFiber, frLit_iso_fr_of_chanceFree _ nestedCF nestedCF_chanceFree⟩

end Cleanroom.Decision.DpCartesianFrames.AuditR4
