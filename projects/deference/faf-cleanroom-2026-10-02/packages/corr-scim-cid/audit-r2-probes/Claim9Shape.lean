import Cleanroom.Corrigibility.CorrScimCid.Incentives

/-!
# Audit r2 (fidelity) probe: the Fig. 7 / Fig. 12 shape is outside `TI.IsTIIgnoring`

Everitt 2019's Fig. 7 has the edge `Θ^R₂ → Θ^R₃` and Fig. 12 has `Θ^PM₂ → B²₂, B²₃`: in both, the
future objective has *children* that reach no reward of agent 1. On the package's eight-node type
the class `TI.IsTIIgnoring` is exactly "`Θ₂` is a sink" (audit r1 probe `TISink`), so a graph of
that shape is **not** in the class, and `TI.claim3` / `TI.claim9` (stated over `TI.ClassCid`) do
not apply to it. The general theorem `Scim.indifferent_of_not_ancSelf_utility` does: it only needs
`Θ₂` to be an ancestor-or-self of no utility node.

Probe: `fig7` plus the edge `Θ₂ → S₃` (`S₃` a sink standing in for `Θ^R₃` / `B²₃`).
* `not_isTIIgnoring`: the graph is outside the class;
* `indifferent_all`: every SCIM over it, every policy, is indifferent to `Θ₂` — by the general
  theorem, not by `claim9`.
Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrScimCid.AuditR2.Claim9Shape

open FactoredSpaces Cleanroom.Corrigibility.CorrScimCid
open TI.Node

/-- `fig7` plus `Θ₂ → S₃`. -/
def adjB : TI.Node → TI.Node → Bool
  | Θ₂, S₃ => true
  | u, v => TI.fig7Adj u v

def G' : Digraph TI.Node := ⟨fun u v => adjB u v = true⟩

instance : DecidableRel G'.Adj := fun u v => inferInstanceAs (Decidable (adjB u v = true))

lemma G'_acyclic : G'.IsAcyclic := Digraph.isAcyclic_of_rank TI.fig7Rank (by decide)

/-- The shape is outside the class: `Θ₂` has a child. -/
theorem not_isTIIgnoring : ¬ TI.IsTIIgnoring G' :=
  fun h => h.no_state S₃ (Or.inr (Or.inr rfl)) (by decide)

/-- Everything reachable from `Θ₂` is `S₃`. -/
lemma reach_Θ₂ : ∀ w, G'.IsAncestor Θ₂ w → w = S₃ := by
  intro w h
  induction h with
  | single e =>
    revert e
    show adjB Θ₂ _ = true → _
    cases ‹TI.Node› <;> decide
  | tail _ e ih =>
    subst ih
    revert e
    show adjB S₃ _ = true → _
    cases ‹TI.Node› <;> decide

/-- A CID over the shape with the class's kinds. -/
def C' (Val : TI.Node → Type) (uv : ∀ v, TI.kind v = .utility → Val v → ℝ) : Cid G' Val where
  acyclic := G'_acyclic
  kind := TI.kind
  utilVal := uv
  utility_sink := by decide

/-- `Θ₂` is an ancestor-or-self of no reward node in the shape. -/
lemma not_ancSelf_reward {Val : TI.Node → Type} (uv : ∀ v, TI.kind v = .utility → Val v → ℝ)
    (u : TI.Node) (hu : (C' Val uv).kind u = .utility) : ¬ Scm.AncSelf G' u Θ₂ := by
  rintro (e | e)
  · cases u <;> cases hu <;> cases e
  · have := reach_Θ₂ u e
    subst this
    cases hu

/-- **Every SCIM over the Fig. 7 / Fig. 12 shape is indifferent to `Θ₂`** — by the general theorem,
which `claim3`/`claim9` (over the sink class) cannot deliver here. -/
theorem indifferent_all {Val E : TI.Node → Type} [∀ v, Fintype (E v)]
    (uv : ∀ v, TI.kind v = .utility → Val v → ℝ) (M : Scim (C' Val uv) E) :
    M.IndifferentTo Θ₂ (show TI.kind Θ₂ ≠ .decision by decide) :=
  M.indifferent_of_not_ancSelf_utility (X := Θ₂) (show TI.kind Θ₂ ≠ .decision by decide)
    (not_ancSelf_reward uv)

end Cleanroom.Corrigibility.CorrScimCid.AuditR2.Claim9Shape
