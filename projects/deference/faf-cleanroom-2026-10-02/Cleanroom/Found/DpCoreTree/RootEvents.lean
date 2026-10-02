import Cleanroom.Found.DpCoreTree.Occurrence

/-!
# Root events are policy-invariant

T9 of [[dp-core-tree-mandate]] (dp-core-2-014). A *root event* is decided at every topmost
decision node (`RootEvent`, `Recording.lean`). **Theorem** (`RootEvent.nu_eq`): for a root event
`X`, `ν_{B,C}(X) = ν_{B,C'}(X)` for all procedures `C, C'`; in particular `ν_{B,C}(X)` is
`C(d)`-free for every `d` (`RootEvent.nu_deviate_eq`). Proof: below a topmost decision node
the whole subtree agrees on `X`, so its mass is `0` or `1` whatever the node draws; above the
topmost nodes only chance acts.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [DecidableEq Ω]

namespace Tree

/-- Being decided passes from a chance node to its children.
Source: none: infrastructure
Kind: L -/
theorem DecidedAt.chance_child {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (i : Fin n) (q : (child i).DecNode) (X : Finset Ω)
    (h : DecidedAt (chance n β child) ⟨i, q⟩ X) : DecidedAt (child i) q X := by
  have key : ∀ ℓ ∈ leavesBelow (child i) q,
      (⟨i, ℓ⟩ : (chance n β child).Leaves) ∈ leavesBelow (chance n β child) ⟨i, q⟩ := by
    intro ℓ hℓ
    exact (mem_leavesBelow _ _ _).mpr
      (by rw [edgeOf_chance, dif_pos rfl]; exact (mem_leavesBelow _ _ _).mp hℓ)
  rcases h with h | h
  · left; intro ℓ hℓ
    have := h ⟨i, ℓ⟩ (key ℓ hℓ)
    simpa using this
  · right; intro ℓ hℓ
    have := h ⟨i, ℓ⟩ (key ℓ hℓ)
    simpa using this

/-- Root events pass from a chance node to its children.
Source: none: infrastructure
Kind: L -/
theorem RootEvent.chance_child {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (X : Finset Ω) (h : RootEvent (chance n β child) X) (i : Fin n) : RootEvent (child i) X := by
  intro q hq
  exact DecidedAt.chance_child β child i q X (h ⟨i, q⟩ hq)

/-- `ν` through a chance node.
Source: none: infrastructure
Kind: L -/
theorem nu_chance (C : Proc ι acts K) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (X : Finset Ω) :
    nu C (chance n β child) X = ∑ i, β.w i * nu C (child i) X := by
  simp only [nu_eq_sum]
  rw [sum_leaves_chance]
  simp only [world_chance, leafLaw_chance, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ℓ _ => ?_
  split_ifs <;> simp

/-- **Root events are policy-invariant**: `ν_{B,C}(X) = ν_{B,C'}(X)` for every root event `X`.
Source: `directions/clean-source-and-policy-responsiveness.md` §3 ("`ν_{B,C}(□⊥)` is constant
in `C`"; "an event is responsive only if a `d`-node lies upstream of it — none lies upstream of
a root"); mandate T9 (dp-core-2-014)
Kind: P
Fidelity: exact
Hyps: none -/
theorem RootEvent.nu_eq (X : Finset Ω) :
    (B : Tree Ω ι acts K) → RootEvent B X → ∀ C C' : Proc ι acts K, nu C B X = nu C' B X
  | leaf ω r, _, C, C' => by
      simp only [nu_eq_sum]
      show (∑ _ℓ : Unit, if ω ∈ X then (1 : K) else 0) = ∑ _ℓ : Unit, if ω ∈ X then 1 else 0
      rfl
  | chance _ β child, h, C, C' => by
      rw [nu_chance, nu_chance]
      exact Finset.sum_congr rfl fun i _ => by
        rw [RootEvent.nu_eq X (child i) (h.chance_child β child X i) C C']
  | decision d child, h, C, C' => by
      have hroot := h none rfl
      have hall : ∀ ℓ, ℓ ∈ leavesBelow (decision d child) none := by
        rintro ⟨a, ℓ⟩
        rw [mem_leavesBelow, edgeOf_decision_none]
        rfl
      rcases hroot with hin | hout
      · have h1 : ∀ D : Proc ι acts K, nu D (decision d child) X = 1 := by
          intro D
          rw [nu_eq_sum]
          simp only [hin _ (hall _), if_true]
          exact sum_leafLaw D _
        rw [h1, h1]
      · have h0 : ∀ D : Proc ι acts K, nu D (decision d child) X = 0 := by
          intro D
          rw [nu_eq_sum]
          simp [hout _ (hall _)]
        rw [h0, h0]

/-- A root event's mass is `C(d)`-free for every `d`.
Source: mandate T9 (corollary)
Kind: L -/
theorem RootEvent.nu_deviate_eq [DecidableEq ι] {B : Tree Ω ι acts K} {X : Finset Ω}
    (h : RootEvent B X) (C : Proc ι acts K) (d : ι) (m : FinDistr K (acts d)) :
    nu (C.deviate d m) B X = nu C B X :=
  RootEvent.nu_eq X B h _ _

end Tree

end Cleanroom.Found.DpCoreTree
