import Cleanroom.Trust.TtFiniteFrames.Corr

/-!
# The Blackwell join of two deterministic experiments (F4)

Package `tt-finite-frames`, Target F4 (`stretch`, kind L; trust-lab-004/039), added in repair
round 2 as an agenda push. The pair map `w ↦ (f₁ w, f₂ w)` refines both `f₁` and `f₂` and is the
least such: any `f` refining both refines the pair (`refines_pair_fst`, `refines_pair_snd`,
`refines_pair_of_refines`), so it is the join in the refinement preorder and, through the
dependency's `Refines.blackwellLE`, the pair experiment is Blackwell-above both
(`blackwellLE_ofMap_pair_fst`, `_snd`). In the correspondence form the join is the cellwise
intersection (`Corr.ofMap_pair`), and a correspondence refines the join iff it refines both
(`Corr.refines_ofMap_pair_iff`) — for any correspondence, not only partitional ones.

Not formalized (recorded only, as the mandate allows): the finite VoI lemma "as B5/G3 on the
menu of `α`-payoffs", the "coarsest Blackwell-monotone abstraction" and the thermostat of
trust-lab-004/039, which are interpretation.
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The pair map refines its first component (`f₁ = Prod.fst ∘ pair`).
Source: mandate F4; trust-lab-004/039
Kind: L
Fidelity: exact -/
theorem refines_pair_fst {S T : Type} (f₁ : W → S) (f₂ : W → T) :
    Blackwell.Refines (fun w => (f₁ w, f₂ w)) f₁ :=
  ⟨Prod.fst, rfl⟩

/-- The pair map refines its second component.
Source: mandate F4; trust-lab-004/039
Kind: L
Fidelity: exact -/
theorem refines_pair_snd {S T : Type} (f₁ : W → S) (f₂ : W → T) :
    Blackwell.Refines (fun w => (f₁ w, f₂ w)) f₂ :=
  ⟨Prod.snd, rfl⟩

/-- **The pair is the least common refinement**: a map refining both `f₁` and `f₂` refines the
pair (`f₁ = g₁ ∘ f`, `f₂ = g₂ ∘ f` give `pair = (g₁, g₂) ∘ f`).
Source: mandate F4 ("refines both and is the least such"); trust-lab-004/039
Kind: L
Fidelity: exact -/
theorem refines_pair_of_refines {S T U : Type} {f : W → U} {f₁ : W → S} {f₂ : W → T}
    (h₁ : Blackwell.Refines f f₁) (h₂ : Blackwell.Refines f f₂) :
    Blackwell.Refines f (fun w => (f₁ w, f₂ w)) := by
  obtain ⟨g₁, rfl⟩ := h₁
  obtain ⟨g₂, rfl⟩ := h₂
  exact ⟨fun u => (g₁ u, g₂ u), rfl⟩

/-- The pair experiment is Blackwell-above the first component's experiment.
Source: mandate F4; the dependency's `Refines.blackwellLE`
Kind: L
Fidelity: exact -/
theorem blackwellLE_ofMap_pair_fst {S T : Type} [Fintype S] [Fintype T] [DecidableEq S]
    [DecidableEq T] (f₁ : W → S) (f₂ : W → T) :
    Blackwell.BlackwellLE (Blackwell.ofMap f₁) (Blackwell.ofMap (fun w => (f₁ w, f₂ w))) :=
  (refines_pair_fst f₁ f₂).blackwellLE

/-- The pair experiment is Blackwell-above the second component's experiment.
Source: mandate F4; the dependency's `Refines.blackwellLE`
Kind: L
Fidelity: exact -/
theorem blackwellLE_ofMap_pair_snd {S T : Type} [Fintype S] [Fintype T] [DecidableEq S]
    [DecidableEq T] (f₁ : W → S) (f₂ : W → T) :
    Blackwell.BlackwellLE (Blackwell.ofMap f₂) (Blackwell.ofMap (fun w => (f₁ w, f₂ w))) :=
  (refines_pair_snd f₁ f₂).blackwellLE

/-- **The join's cells are the intersections**: `ofMap (f₁, f₂) w = ofMap f₁ w ∩ ofMap f₂ w`.
Source: mandate F4; none: infrastructure
Kind: L
Fidelity: exact -/
theorem Corr.ofMap_pair {S T : Type} [DecidableEq S] [DecidableEq T] (f₁ : W → S) (f₂ : W → T)
    (w : W) :
    Corr.ofMap (fun w => (f₁ w, f₂ w)) w = Corr.ofMap f₁ w ∩ Corr.ofMap f₂ w := by
  ext v
  simp [Corr.mem_ofMap]

/-- **A correspondence refines the join iff it refines both components** — for any
correspondence `K`, partitional or not.
Source: mandate F4 ("the least such"), correspondence form
Kind: L
Fidelity: exact -/
theorem Corr.refines_ofMap_pair_iff {S T : Type} [DecidableEq S] [DecidableEq T] (K : Corr W)
    (f₁ : W → S) (f₂ : W → T) :
    Corr.Refines K (Corr.ofMap (fun w => (f₁ w, f₂ w))) ↔
      Corr.Refines K (Corr.ofMap f₁) ∧ Corr.Refines K (Corr.ofMap f₂) := by
  simp only [Corr.Refines, Corr.ofMap_pair, Finset.subset_inter_iff, forall_and]

end Cleanroom.Trust.TtFiniteFrames
