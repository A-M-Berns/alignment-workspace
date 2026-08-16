/-
# Fixed-action Φ-regret bridge

Stable mathematics extracted from the executable bridge.  `SemanticAction` has
eight values.  The generic preservation theorem says that pointwise loss
preservation plus a commuting action map preserves finite-horizon regret.  It
does not formalize Python responses, legality, or Blum--Mansour's theorem.

All names are provisional (`AGENTS.md` standard 6).
-/

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Workspace.Normativity.Contrib.PhiRegretBridge

/-- The fixed theorem-facing action alphabet used by the frozen environment. -/
inductive SemanticAction where
  | meritsPositive
  | meritsNegative
  | default
  | decline0
  | decline1
  | decline2
  | decline3
  | decline4
  deriving DecidableEq, Fintype

theorem semanticAction_card : Fintype.card SemanticAction = 8 := by decide

/-- Finite cumulative loss on an explicitly supplied list of round indices. -/
def cumulativeLoss {ι Action : Type} (rounds : List ι)
    (loss : ι → Action → ℚ) (play : ι → Action) : ℚ :=
  (rounds.map fun round => loss round (play round)).sum

/-- If decoding preserves each loss and commutes with each modification map,
then it preserves finite-horizon regret exactly. -/
theorem regret_preserved
    {ι Label Action : Type} (rounds : List ι)
    (decode : ι → Label → Action)
    (labelLoss : ι → Label → ℚ) (repoLoss : ι → Action → ℚ)
    (actual : ι → Label)
    (labelMap : ι → Label → Label) (repoMap : ι → Action → Action)
    (hloss : ∀ round label,
      labelLoss round label = repoLoss round (decode round label))
    (hcommute : ∀ round label,
      decode round (labelMap round label) = repoMap round (decode round label)) :
    cumulativeLoss rounds labelLoss actual -
        cumulativeLoss rounds labelLoss (fun round => labelMap round (actual round)) =
      cumulativeLoss rounds repoLoss (fun round => decode round (actual round)) -
        cumulativeLoss rounds repoLoss
          (fun round => repoMap round (decode round (actual round))) := by
  induction rounds with
  | nil => simp [cumulativeLoss]
  | cons round rounds ih =>
      simp only [cumulativeLoss, List.map_cons, List.sum_cons]
      rw [hloss round (actual round), hloss round (labelMap round (actual round)),
        hcommute round (actual round)]
      have htail := ih
      dsimp [cumulativeLoss] at htail
      linarith

/-- Finite form of the recurrent-failure implication. If mixed failure mass is
at least `ρT` and each unit saves `δ`, up to transient `B`, then expected regret
is at least `ρδT - B`. Deterministic firing counts embed as rational mass. -/
theorem recurrentFailure_lowerBound
    (T : ℕ) (failureMass ρ δ B regret : ℚ)
    (hδ : 0 ≤ δ)
    (hcount : ρ * T ≤ failureMass)
    (hregret : failureMass * δ - B ≤ regret) :
    ρ * δ * T - B ≤ regret := by
  have hscaled : ρ * T * δ ≤ failureMass * δ :=
    mul_le_mul_of_nonneg_right hcount hδ
  calc
    ρ * δ * T - B = ρ * T * δ - B := by ring
    _ ≤ failureMass * δ - B := sub_le_sub_right hscaled B
    _ ≤ regret := hregret

namespace Witness

def decode : Unit → SemanticAction → Bool := fun _ action =>
  action == SemanticAction.default

def labelLoss : Unit → SemanticAction → ℚ := fun round action =>
  if decode round action then 1 else 0

def repoLoss : Unit → Bool → ℚ := fun _ action => if action then 1 else 0

def actual : Unit → SemanticAction := fun _ => SemanticAction.default

def labelMap : Unit → SemanticAction → SemanticAction := fun _ action => action

def repoMap : Unit → Bool → Bool := fun _ action => action

theorem loss_commutes : ∀ round action,
    labelLoss round action = repoLoss round (decode round action) := by
  intro round action
  cases action <;> rfl

theorem action_commutes : ∀ round action,
    decode round (labelMap round action) = repoMap round (decode round action) := by
  intros
  rfl

theorem regret_preservation_inhabited :
    cumulativeLoss [()] labelLoss actual -
        cumulativeLoss [()] labelLoss (fun round => labelMap round (actual round)) =
      cumulativeLoss [()] repoLoss (fun round => decode round (actual round)) -
        cumulativeLoss [()] repoLoss
          (fun round => repoMap round (decode round (actual round))) :=
  regret_preserved [()] decode labelLoss repoLoss actual labelMap repoMap
    loss_commutes action_commutes

theorem recurrent_bound_inhabited :
    (1 / 2 : ℚ) * 1 * 4 - 0 ≤ 2 := by
  exact recurrentFailure_lowerBound 4 2 (1 / 2) 1 0 2 (by norm_num)
    (by norm_num) (by norm_num)

end Witness

#print axioms semanticAction_card
#print axioms regret_preserved
#print axioms recurrentFailure_lowerBound
#print axioms Witness.loss_commutes
#print axioms Witness.action_commutes
#print axioms Witness.regret_preservation_inhabited
#print axioms Witness.recurrent_bound_inhabited

end Workspace.Normativity.Contrib.PhiRegretBridge
