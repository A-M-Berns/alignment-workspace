import Cleanroom.Li.LiProjection.Church
import Cleanroom.Li.LiProjection.Open

/-!
# Audit r4 (adversarial) probe: the generalised T6.1 OPENs are inhabited by a genuinely
stage-indexed family.

Repair round 3 generalised `conditioned_record_not_injective` / `conditioned_limitRecord_not_injective`
from one sentence to `ψ : ℕ → Sentence` with per-stage hypotheses. Round 3's probe inhabited the
constant family only. Here the family `shiftFamily t := projAtom (t + 1)` puts a *different* fresh
atom at every stage (so it is not a constant family in disguise), every member is `u`-free for
`u := projAtomCode 0`, and both bits are plausible at every stage. Sorry-free; then both OPENs
applied at it (type-check; carry `sorryAx`, as they must).
-/

open Cleanroom.Li.LiProjection LogicalInduction LO.Propositional LO.FirstOrder
  LO.FirstOrder.Arithmetic Cleanroom.Bli.BliFound

/-- A different fresh atom at every stage. -/
noncomputable def shiftFamily (t : ℕ) : Sentence := projAtom (t + 1)

/-- The family is not constant. -/
theorem shiftFamily_not_const : shiftFamily 0 ≠ shiftFamily 1 := by
  intro h
  simp only [shiftFamily, projAtom] at h
  have := projAtomCode_injective (Formula.atom.inj h)
  omega

theorem family_T61_hyps_inhabited :
    IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) ∧
    AtomFreeProcess (projAtomCode 0) (paperDP 𝗜𝚺₁) ∧
    (∀ t, AtomFreeSentence (projAtomCode 0) (shiftFamily t)) ∧
    (∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧ v.Holds (shiftFamily n)) ∧
    (∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧ ¬ v.Holds (shiftFamily n)) := by
  refine ⟨LIA_is_logical_inductor _ (paperDP_computable _), paperDP_atomFree 𝗜𝚺₁ 0, ?_, ?_, ?_⟩
  · intro t
    exact atomFreeSentence_atom_of_ne (projAtomCode_injective.ne (Nat.succ_ne_zero t))
  · exact fun n =>
      exists_consistent_holds_atom (paperDP_atomFree 𝗜𝚺₁ (n + 1)) (paperDP_hworld 𝗜𝚺₁) n
  · exact fun n =>
      exists_consistent_not_holds_atom (paperDP_atomFree 𝗜𝚺₁ (n + 1)) (paperDP_hworld 𝗜𝚺₁) n

#print axioms family_T61_hyps_inhabited

/-- The every-stage OPEN applies at the stage-indexed family (carries `sorryAx`). -/
example : ∃ H' : History, IsLogicalInductor H' (paperDP 𝗜𝚺₁) ∧
    (∀ n φ, conditionedHistory H' shiftFamily n φ =
      conditionedHistory (liaHistory (paperDP 𝗜𝚺₁)) shiftFamily n φ) ∧
    ∃ φ, limitingBelief H' φ ≠ limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) φ :=
  haveI : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) :=
    LIA_is_logical_inductor _ (paperDP_computable _)
  conditioned_record_not_injective (paperDP 𝗜𝚺₁) (projAtomCode 0) (paperDP_atomFree 𝗜𝚺₁ 0)
    (liaHistory (paperDP 𝗜𝚺₁)) shiftFamily family_T61_hyps_inhabited.2.2.1
    family_T61_hyps_inhabited.2.2.2.1 family_T61_hyps_inhabited.2.2.2.2

/-- The limit OPEN applies at the stage-indexed family (carries `sorryAx`). -/
example : ∃ H' : History, IsLogicalInductor H' (paperDP 𝗜𝚺₁) ∧
    (∀ φ, limitingBelief (conditionedHistory H' shiftFamily) φ =
      limitingBelief (conditionedHistory (liaHistory (paperDP 𝗜𝚺₁)) shiftFamily) φ) ∧
    ∃ φ, limitingBelief H' φ ≠ limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) φ :=
  haveI : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) :=
    LIA_is_logical_inductor _ (paperDP_computable _)
  conditioned_limitRecord_not_injective (paperDP 𝗜𝚺₁) (projAtomCode 0) (paperDP_atomFree 𝗜𝚺₁ 0)
    (liaHistory (paperDP 𝗜𝚺₁)) shiftFamily family_T61_hyps_inhabited.2.2.1
    family_T61_hyps_inhabited.2.2.2.1 family_T61_hyps_inhabited.2.2.2.2
