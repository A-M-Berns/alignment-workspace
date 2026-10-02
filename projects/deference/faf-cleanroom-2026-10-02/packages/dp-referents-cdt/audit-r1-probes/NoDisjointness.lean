import Cleanroom.Decision.DpReferentsCdt.Rows

/-!
# `dp-referents-cdt` · audit r1 (adversarial) probe: the factorisation `ν_C(a ∧ O_d) = C(d)(a)·∑ R_q`
fails without Definition 3's disjointness — the tree findings F12 says was not built

Not imported by the library.

Mandate §7 trap 1 and findings F12: `ActRecording` carries no exclusivity clause, so Lemma C2-L2's
factorisation (`nu_actEv_inter_obs_eq`) needs `ActEvDisjoint` by name; "the tree that fails
without disjointness was not built". Here it is: one `d`-node, two leaves, worlds = the drawn
act, `O_d = ⊤`, `actEv a = {a}` but `actEv b = ⊤` (overlapping). The root is
node-action-veridical, so `ActRecording` holds for every procedure, yet
`ν(b ∧ O_d) = 1 ≠ C(d)(b)·∑_{realFiber} R_q = C(d)(b)` at any label with `C(d)(b) < 1`.
So the hypothesis is load-bearing (not a cosmetic (a)), and every headline that carries it
(C2-1, C2-A′, C2-B′, FA-20′(i), T12(a)-`refR2Real`, T12(d)) needs it.
-/

namespace Cleanroom.Decision.DpReferentsCdt.AuditR1Adversarial

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpReferentsCdt
open Finset

/-- One `d`-node; the leaf's world is the drawn act. -/
def ndTree : Tree Act2 Unit (fun _ => Act2) ℚ := .decision () fun act => .leaf act 0

/-- `O_d = ⊤`. -/
def ndObs : Unit → Finset Act2 := fun _ => Finset.univ

/-- `actEv a = {a}`, `actEv b = ⊤`: not pairwise disjoint. -/
def ndActEv : (d : Unit) → Act2 → Finset Act2 := fun _ a => if a = .a then {Act2.a} else Finset.univ

/-- The root is node-action-veridical (every leaf below the `x`-edge lies in `actEv x`). -/
theorem nd_root_nav : NodeActionVeridical ndActEv ndTree none := by
  intro ℓ a ha
  rcases ℓ with ⟨act, _⟩
  simp only [ndTree, edgeOf_decision_none, Option.some.injEq] at ha
  subst ha
  cases act <;> simp [ndActEv, ndTree, world]

/-- F3′ holds for every procedure. -/
theorem nd_actRecording (C : Proc Unit (fun _ => Act2) ℚ) : ActRecording ndObs ndActEv C ndTree () := by
  refine ⟨fun q _ _ ℓ _ => by simp [ndObs], ?_⟩
  intro ℓ _ _
  refine ⟨none, ⟨?_, nd_root_nav⟩, ?_⟩
  · rw [mem_dNodesOn]
    refine ⟨rfl, ?_⟩
    rcases ℓ with ⟨act, _⟩
    simp [ndTree, edgeOf_decision_none]
  · rintro (_ | ⟨_, e⟩) -
    · rfl
    · exact e.elim

/-- The action events are not disjoint. -/
theorem nd_not_disjoint : ¬ ActEvDisjoint ndActEv () := by
  intro h
  have := h .a .b (by decide)
  rw [Finset.disjoint_left] at this
  exact this (a := .a) (by simp [ndActEv]) (by simp [ndActEv])

/-- The real fiber is the root. -/
theorem nd_mem_realFiber (q : ndTree.DecNode) : q ∈ realFiber ndActEv ndTree () ↔ q = none := by
  rw [mem_realFiber]
  constructor
  · rintro ⟨-, -⟩
    rcases q with _ | ⟨_, e⟩
    · rfl
    · exact e.elim
  · rintro rfl
    exact ⟨rfl, nd_root_nav⟩

/-- **The factorisation fails**: at the label `1/2`, `ν(b ∧ O_d) = 1` while
`C(d)(b)·∑_{realFiber} R_q = 1/2`. -/
theorem nd_factorisation_fails :
    nu (procQ (1/2) (by norm_num) (by norm_num)) ndTree (ndActEv () .b ∩ ndObs ()) = 1 ∧
    (procQ (1/2) (by norm_num) (by norm_num) ()).w .b *
      realReach ndActEv (procQ (1/2) (by norm_num) (by norm_num)) ndTree () = 1 / 2 := by
  constructor
  · rw [nu_eq_sum]
    unfold ndTree
    rw [sum_leaves_decision]
    simp [ndActEv, ndObs, leafLaw, world, Act2.sum_univ, procQ]
  · unfold realReach
    rw [sum_realFiber_eq_of_unique ndActEv ndTree none nd_mem_realFiber]
    simp [ndTree, procQ]
    norm_num

end Cleanroom.Decision.DpReferentsCdt.AuditR1Adversarial
