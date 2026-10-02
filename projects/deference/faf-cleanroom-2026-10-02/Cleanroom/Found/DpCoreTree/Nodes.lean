import Cleanroom.Found.DpCoreTree.Defs

/-!
# Node addresses, the reach event, node-level policies

Addresses of decision nodes (`DecNode`), the point a node carries (`pt`), the edge a leaf's
path takes at a node (`edgeOf`), the leaves below a node (`leavesBelow`), the path-mass of reaching
a node (`reach`, v2 §8's `R_q`), minimality (no node carrying the same point above), and the
*node-level* policies of v2 §8's proof of Theorem 1 ("regard `V_B` as a function of one
distribution `p_q` per decision node"): `NodePolicy`, `leafLawNode`, `valueNode`, the tying
`NodePolicy.ofProc`, the single-node update, and the forced-below payoff mass whose ratio to
`reach` is v2's `G_q`.

All definitions are by structural recursion on the tree; the only casts are the `Fin n` /
`acts d` index equalities in `edgeOf` (a leaf's child index against a node's).
-/

namespace Cleanroom.Found.DpCoreTree

open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

namespace Tree

/-- Addresses of the decision nodes of a tree: none in a leaf; a chance node's are its
children's, tagged by the child index; a decision node's are itself (`none`) or a child's
(`some ⟨a, q⟩`).
Source: [[decision-problems-v2]] §8 ("a decision node `q`"); §3.1 Definition 5
Kind: D -/
def DecNode : Tree Ω ι acts K → Type
  | leaf _ _ => Empty
  | chance _ _ child => Σ i, (child i).DecNode
  | decision _ child => Option (Σ a, (child a).DecNode)

/-- `Fintype` structure on decision-node addresses, by recursion.
Source: none: infrastructure
Kind: D -/
@[reducible] def fintypeDecNode [∀ d, Fintype (acts d)] :
    (B : Tree Ω ι acts K) → Fintype B.DecNode
  | leaf _ _ => inferInstanceAs (Fintype Empty)
  | chance n _ child =>
      haveI : ∀ i, Fintype (child i).DecNode := fun i => fintypeDecNode (child i)
      inferInstanceAs (Fintype (Σ i : Fin n, (child i).DecNode))
  | decision d child =>
      haveI : ∀ a, Fintype (child a).DecNode := fun a => fintypeDecNode (child a)
      inferInstanceAs (Fintype (Option (Σ a : acts d, (child a).DecNode)))

instance [∀ d, Fintype (acts d)] (B : Tree Ω ι acts K) : Fintype B.DecNode := fintypeDecNode B

/-- Decidable equality of decision-node addresses, by recursion.
Source: none: infrastructure
Kind: D -/
@[reducible] def decEqDecNode [∀ d, DecidableEq (acts d)] :
    (B : Tree Ω ι acts K) → DecidableEq B.DecNode
  | leaf _ _ => inferInstanceAs (DecidableEq Empty)
  | chance n _ child =>
      haveI : ∀ i, DecidableEq (child i).DecNode := fun i => decEqDecNode (child i)
      inferInstanceAs (DecidableEq (Σ i : Fin n, (child i).DecNode))
  | decision d child =>
      haveI : ∀ a, DecidableEq (child a).DecNode := fun a => decEqDecNode (child a)
      inferInstanceAs (DecidableEq (Option (Σ a : acts d, (child a).DecNode)))

instance [∀ d, DecidableEq (acts d)] (B : Tree Ω ι acts K) : DecidableEq B.DecNode :=
  decEqDecNode B

/-- The decision point `d_q` carried by the node `q`.
Source: [[decision-problems-v2]] §3.1 Definition 5 (`d_q`)
Kind: D -/
def pt : (B : Tree Ω ι acts K) → B.DecNode → ι
  | leaf _ _, q => q.elim
  | chance _ _ child, ⟨i, q⟩ => pt (child i) q
  | decision d _, none => d
  | decision _ child, some ⟨a, q⟩ => pt (child a) q

/-- The points of the decision nodes strictly above `q`, root first.
Source: [[decision-problems-v2]] §3.1 Lemma 1 proof ("minimal `d`-nodes `q` (no `d`-node
strictly above)")
Kind: D -/
def ancestorPts : (B : Tree Ω ι acts K) → B.DecNode → List ι
  | leaf _ _, q => q.elim
  | chance _ _ child, ⟨i, q⟩ => ancestorPts (child i) q
  | decision _ _, none => []
  | decision d child, some ⟨a, q⟩ => d :: ancestorPts (child a) q

/-- `q` is a *minimal* `d_q`-node: no node strictly above it carries the same point.
Source: [[decision-problems-v2]] §3.1 Lemma 1 proof
Kind: D -/
def IsMinimal [DecidableEq ι] (B : Tree Ω ι acts K) (q : B.DecNode) : Prop :=
  pt B q ∉ ancestorPts B q

/-- `q` is a *topmost* decision node: no decision node at all lies above it.
Source: `directions/clean-source-and-policy-responsiveness.md` §3 ("an event is responsive only
if a `d`-node lies upstream of it — none lies upstream of a root")
Kind: D -/
def IsTopmost (B : Tree Ω ι acts K) (q : B.DecNode) : Prop := ancestorPts B q = []

/-- The edge a leaf's root path takes at the node `q`: `some a` if the path passes through `q`
and takes its `a`-edge, `none` if the path does not pass through `q`.
Source: [[decision-problems-v2]] §3.1 Definition 7 ("a decision node `q` on its path at which
`a` was drawn")
Kind: D -/
def edgeOf [∀ d, DecidableEq (acts d)] :
    (B : Tree Ω ι acts K) → (q : B.DecNode) → B.Leaves → Option (acts (pt B q))
  | leaf _ _, q, _ => q.elim
  | chance _ _ child, ⟨i, q⟩, ⟨j, ℓ⟩ =>
      if h : j = i then edgeOf (child i) q (h ▸ ℓ) else none
  | decision _ _, none, ⟨a, _⟩ => some a
  | decision _ child, some ⟨a, q⟩, ⟨b, ℓ⟩ =>
      if h : b = a then edgeOf (child a) q (h ▸ ℓ) else none

/-- The leaves below `q`: those whose path passes through `q`.
Source: [[decision-problems-v2]] §3.1 Definition 7 ("every leaf `ℓ'` below `q`"); §8 ("reach
`q`")
Kind: D -/
def leavesBelow [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] (B : Tree Ω ι acts K)
    (q : B.DecNode) : Finset B.Leaves :=
  Finset.univ.filter fun ℓ => (edgeOf B q ℓ).isSome

/-- The `d`-nodes on the path to `ℓ`.
Source: [[decision-problems-v2]] §3.1 Definition 6 (`#_d(ℓ)` counts the `d`-nodes on the
path); Definition 7 ("passes exactly one `d`-node")
Kind: D -/
def dNodesOn [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
    (B : Tree Ω ι acts K) (d : ι) (ℓ : B.Leaves) : Finset B.DecNode :=
  Finset.univ.filter fun q => pt B q = d ∧ (edgeOf B q ℓ).isSome

/-- The fiber of `q ↦ d_q` over `d`: all nodes carrying `d`.
Source: [[decision-problems-v2]] §8 Theorem 1 ("the fiber of `d`"; `∑_{q : d_q = d}`)
Kind: D -/
def fiber [DecidableEq ι] [∀ d, Fintype (acts d)] (B : Tree Ω ι acts K) (d : ι) :
    Finset B.DecNode :=
  Finset.univ.filter fun q => pt B q = d

/-- `R_q(C) := μ_{B,C}(reach q)`, as the product of the weights on the path to `q`.
Source: [[decision-problems-v2]] §8 (`R_q(C)`)
Kind: D -/
def reach [∀ d, Fintype (acts d)] (C : Proc ι acts K) :
    (B : Tree Ω ι acts K) → B.DecNode → K
  | leaf _ _, q => q.elim
  | chance _ β child, ⟨i, q⟩ => β.w i * reach C (child i) q
  | decision _ _, none => 1
  | decision d child, some ⟨a, q⟩ => (C d).w a * reach C (child a) q

/-- A *node-level policy*: one distribution `p_q ∈ Δ(A_{d_q})` per decision node (v2 §8's
"regard `V_B` as a function of one distribution `p_q` per decision node").
Source: [[decision-problems-v2]] §8 Theorem 1 proof
Kind: D -/
def NodePolicy [∀ d, Fintype (acts d)] (B : Tree Ω ι acts K) : Type :=
  (q : B.DecNode) → FinDistr K (acts (pt B q))

variable [∀ d, Fintype (acts d)]

/-- Restriction of a node-level policy on a chance node to its `i`-th child.
Source: none: infrastructure
Kind: D -/
def NodePolicy.restrictChance {n : ℕ} {β : FinDistr K (Fin n)} {child : Fin n → Tree Ω ι acts K}
    (p : NodePolicy (chance n β child)) (i : Fin n) : NodePolicy (child i) :=
  fun q => p ⟨i, q⟩

/-- Restriction of a node-level policy on a decision node to its `a`-child.
Source: none: infrastructure
Kind: D -/
def NodePolicy.restrictDecision {d : ι} {child : acts d → Tree Ω ι acts K}
    (p : NodePolicy (decision d child)) (a : acts d) : NodePolicy (child a) :=
  fun q => p (some ⟨a, q⟩)

/-- The node-level policy tied to a procedure: `p_q := C(d_q)`.
Source: [[decision-problems-v2]] §8 Theorem 1 proof ("Tying `p_q := C(d_q)`")
Kind: D -/
def NodePolicy.ofProc (C : Proc ι acts K) (B : Tree Ω ι acts K) : NodePolicy B :=
  fun q => C (pt B q)

/-- Update a node-level policy at one node only (`p[q ↦ m]`); v2 §8's single-instance
counterfactual when `m` is a point mass.
Source: [[decision-problems-v2]] §8 ("forcing the single instance, all other nodes … still
drawing")
Kind: D -/
def NodePolicy.update [∀ d, DecidableEq (acts d)] {B : Tree Ω ι acts K} (p : NodePolicy B)
    (q : B.DecNode) (m : FinDistr K (acts (pt B q))) : NodePolicy B :=
  Function.update p q m

/-- The run law under a node-level policy: each decision node draws from its own `p_q`.
Source: [[decision-problems-v2]] §8 Theorem 1 proof
Kind: D
Fidelity: exact (Definition 6 with per-node distributions) -/
def leafLawNode : (B : Tree Ω ι acts K) → NodePolicy B → B.Leaves → K
  | leaf _ _, _, _ => 1
  | chance _ β child, p, ⟨i, ℓ⟩ => β.w i * leafLawNode (child i) (p.restrictChance i) ℓ
  | decision _ child, p, ⟨a, ℓ⟩ => (p none).w a * leafLawNode (child a) (p.restrictDecision a) ℓ

/-- The value under a node-level policy.
Source: [[decision-problems-v2]] §8 Theorem 1 proof
Kind: D -/
def valueNode (B : Tree Ω ι acts K) (p : NodePolicy B) : K :=
  ∑ ℓ, leafLawNode B p ℓ * payoff B ℓ

/-- The reach mass `R_q(p)` under a node-level policy.
Source: [[decision-problems-v2]] §8 (`R_q`)
Kind: D -/
def reachNode : (B : Tree Ω ι acts K) → NodePolicy B → B.DecNode → K
  | leaf _ _, _, q => q.elim
  | chance _ β child, p, ⟨i, q⟩ => β.w i * reachNode (child i) (p.restrictChance i) q
  | decision _ _, _, none => 1
  | decision _ child, p, some ⟨a, q⟩ => (p none).w a * reachNode (child a) (p.restrictDecision a) q

/-- The payoff mass below `q` when `a` is forced at `q` only:
`∑_{ℓ below q} μ_{p[q ↦ δ_a]}(ℓ) r(ℓ)`. Its ratio to `R_q` is v2's `G_q(a)`; the product
`R_q · G_q(a)` is what enters the derivative of `V_B`, so this is the primary object and `G_q`
is derived (`gNode`), keeping division out of the headlines.
Source: [[decision-problems-v2]] §8 (`G_q(C, a)`, `∂V/∂p_q(a) = R_q · G_q(a)`)
Kind: D -/
def forcedBelow [∀ d, DecidableEq (acts d)] (B : Tree Ω ι acts K) (p : NodePolicy B)
    (q : B.DecNode) (a : acts (pt B q)) : K :=
  ∑ ℓ ∈ leavesBelow B q, leafLawNode B (p.update q (FinDistr.pure a)) ℓ * payoff B ℓ

/-- `G_q(p, a)`: the expected payoff below `q` forcing `a` at `q` only, i.e.
`forcedBelow / R_q`. Only meaningful when `R_q ≠ 0` (Lean's `x / 0 = 0` does no work in any
theorem: they are stated through `forcedBelow`).
Source: [[decision-problems-v2]] §8 (`G_q(C, a) := 𝔼_μ[r ∣ reach q, force a at q only]`)
Kind: D -/
def gNode [∀ d, DecidableEq (acts d)] (B : Tree Ω ι acts K) (p : NodePolicy B)
    (q : B.DecNode) (a : acts (pt B q)) : K :=
  forcedBelow B p q a / reachNode B p q

end Tree

end Cleanroom.Found.DpCoreTree
