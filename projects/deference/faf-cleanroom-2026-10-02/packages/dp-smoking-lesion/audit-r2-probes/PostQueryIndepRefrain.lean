import Cleanroom.Decision.DpSmokingLesion.Lemma3

/-!
# dp-smoking-lesion — audit round 2, adversarial lens: probe `PostQueryIndepRefrain`

Not imported by the library. `lemma3_printed_refuted_coverage` carries, as its second
conjunct, `PostQueryIndep procRefrain cexA₀ () evK` — the printed lemma's second hypothesis
at the refuting label `δ_refrain`. This probe shows that conjunct is **contentless at that
label**: at `δ_refrain` the smoke edge of the `d`-node has mass `0`, so every cross-multiplied
instance of `PostQueryIndep` is `0 = 0` or `x = x`, and the predicate holds for **every** event
`X`, cancer or not. (`PostQueryIndep C B d X` is trivial at every deterministic label on a
binary-action tree, for the same reason.) The content of the printed hypothesis lives in the
all-procedure theorem `cexA_postQueryIndep` (interior labels), which the ledger row cites — the
headline's conjunct should quantify over `C` as that theorem does.
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

/-- At `δ_refrain` the smoke edge of `cexA₀`'s `d`-node carries no mass, inside any `X` or not. -/
theorem cexA_smoke_edge_zero_refrain (X : Finset TickleW) :
    edgeMassIn procRefrain cexA₀ X cexANode true = 0 ∧
    edgeMass procRefrain cexA₀ cexANode true = 0 := by
  constructor
  · unfold edgeMassIn
    rw [cexA_sum]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, cexA_edgeOf.1, cexA_edgeOf.2, cexA_leafLaw_E,
      cexA_leafLaw_A]
    simp [procRefrain]
  · unfold edgeMass
    rw [cexA_sum]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, cexA_edgeOf.1, cexA_edgeOf.2, cexA_leafLaw_E,
      cexA_leafLaw_A]
    simp [procRefrain]

/-- **`PostQueryIndep` is vacuous at `δ_refrain` on `cexA₀`**: it holds for every event `X`. -/
theorem cexA_postQueryIndep_refrain_vacuous (X : Finset TickleW) :
    PostQueryIndep procRefrain cexA₀ () X := by
  intro q _ a b
  obtain rfl := cexA_nodes_cases q
  obtain ⟨hin, hm⟩ := cexA_smoke_edge_zero_refrain X
  cases a <;> cases b <;> simp [hin, hm]

end Cleanroom.Decision.DpSmokingLesion
