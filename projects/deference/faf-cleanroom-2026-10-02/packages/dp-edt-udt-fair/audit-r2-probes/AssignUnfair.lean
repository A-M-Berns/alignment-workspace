import Cleanroom.Decision.DpEdtUdtFair.Assignment
import Cleanroom.Decision.DpCalibration.Mugging

/-!
# `dp-edt-udt-fair` · audit round 2 (adversarial) · probe P3: T5's strong-fairness hypothesis is load-bearing

Evidence file for `dp-edt-udt-fair-audit-r2-adversarial.md`. **Not imported by the library.**

`stronglyFair_assignment` says: on a strongly fair tree some deterministic procedure dominates
every assignment. The package's witness (`dupPay_assignment_witness`) inhabits the hypothesis;
this probe checks the theorem is false without it, so the witness is not of a theorem that
holds everywhere. On the mugging `B₁ = mug1 1 3` (almost fair, not strongly fair) the
assignment "refuse at the live `T`-node, pay at the predictor `H`-node" has value `3/2`, while
every procedure has value `C(d)(pay) · (3 − 1)/2 ≤ 1`. So no procedure, deterministic or mixed,
dominates every assignment there: the conclusion of T5 fails off strong fairness, and
`max_π V_B(π) > max_C V_B(C)` (Proposition 5(b)'s inequality is strict on `B₁`).
-/

namespace Cleanroom.Decision.DpEdtUdtFair.AuditR2

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

/-- Refuse at the `T`-node (index `0`), pay at the `H`-node (index `1`): not fiber-constant. -/
def mugSplitAssign : Assign (mug1 1 3) := fun q => if q.1 = 0 then Act2.b else Act2.a

/-- **T5 fails off strong fairness**: on `mug1 1 3` the split assignment has value `3/2` and every
procedure has value at most `1`. -/
theorem mug1_assignment_beats_every_procedure :
    valueAssign (mug1 1 3) mugSplitAssign = 3 / 2 ∧
    ∀ C : Proc Unit (fun _ => Act2) ℚ, value C (mug1 1 3) ≤ 1 := by
  refine ⟨?_, fun C => ?_⟩
  · unfold valueAssign mugSplitAssign mug1
    rw [valueNode_chance, Fin.sum_univ_two]
    simp only [NodePolicy.restrictChance, valueNode_decision, Act2.sum_univ, valueNode_leaf,
      NodePolicy.ofAssign, FinDistr.pure_w, FinDistr.fair, FinDistr.coin, mugWorld1, mugPay]
    simp
    norm_num
  · rw [mug1_value]
    have hs := (C ()).sum_one
    rw [Act2.sum_univ] at hs
    have hb := (C ()).nonneg .b
    linarith

end Cleanroom.Decision.DpEdtUdtFair.AuditR2
