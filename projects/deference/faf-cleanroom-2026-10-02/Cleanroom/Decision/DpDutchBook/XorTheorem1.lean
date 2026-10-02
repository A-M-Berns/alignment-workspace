import Cleanroom.Decision.DpDutchBook.Xor
import Cleanroom.Found.DpCoreTree.NodeSums
import Cleanroom.Found.DpCoreTree.Multilinear

/-!
# T13(a), the fifth evaluator: Theorem 1's fiber sum on XOR blackmail

v2's Theorem 1 evaluates an act `a` of the point `d` by `∑_{q ∈ F_d} R_q · G_q(a)` — the sum,
over *every* `d`-node of the tree (the simulation and the live node alike), of the payoff mass
below the node when `a` is forced at that node only, every other node still drawing from the
label (`dp-calibration`'s `fiberForced`, D3⁰ = `OccEdtConsistent`). On `xorTree δ c X` with
`q := C(d_L)(pay)`:

* `fiberForced(pay) = −2δX − 2(1−δ)cq − δc(1−q)`, `fiberForced(refuse) = −2δX − δcq`
  (`xor_fiberForced`), so Theorem 1 **refuses by `c(δ(1−2q) + 2q(1−δ))`**
  (`xor_fiberForced_sub`), positive for `0 < δ < ½`, `c > 0`, `q > 0` (`xor_theorem1_refuses`,
  re-founding the earlier arithmetic stub `p06_theorem1_refuses` over the tree); hence no label
  with `q > 0` is D3⁰-consistent there (`xor_not_occEdtConsistent`).

The encoding of `xorTree` keeps the live node on every run (its draw is recorded and paid only on
letter runs); the off-letter live nodes contribute act-independent terms to both sums, so the
margin is the source's.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- On a tree with a single point, Theorem 1's fiber sum is the plain sum over all decision
nodes (every node carries the point). Source: none: infrastructure. Kind: L -/
theorem fiberForced_unit {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] {acts : Unit → Type} [∀ d, Fintype (acts d)]
    [∀ d, DecidableEq (acts d)] (B : Tree Ω Unit acts K) (p : NodePolicy B) (a : acts ()) :
    fiberForced B p () a = ∑ q, forcedBelow B p q a := by
  unfold fiberForced
  refine Finset.sum_congr rfl fun q _ => ?_
  simp

section shape

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The two-level fiber shape `chance → simulation → live → leaf` with abstract leaf data
`w i x a`, `r i x a` (the shape of `xorTree`, the leaf data left opaque so that the derived
decidable equality of node addresses never has to look inside a leaf).
Source: none: infrastructure. Kind: D -/
def shape2 (β : FinDistr ℚ (Fin 2)) (w : Fin 2 → Act2 → Act2 → Ω) (r : Fin 2 → Act2 → Act2 → ℚ) :
    Tree Ω Unit (fun _ => Act2) ℚ :=
  .chance 2 β fun i => .decision () fun x => .decision () fun a => .leaf (w i x a) (r i x a)

variable (β : FinDistr ℚ (Fin 2)) (w : Fin 2 → Act2 → Act2 → Ω) (r : Fin 2 → Act2 → Act2 → ℚ)
  (C : Proc Unit (fun _ => Act2) ℚ)

/-- Sums over the eight leaves of the shape. Source: none: infrastructure. Kind: L -/
theorem shape2_sum {M : Type} [AddCommMonoid M] (f : (shape2 β w r).Leaves → M) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ x : Act2, ∑ a : Act2, f ⟨i, ⟨x, ⟨a, ()⟩⟩⟩ := by
  unfold shape2 at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- Sums over the six decision nodes of the shape: the two simulation nodes and the four live
nodes. Source: none: infrastructure. Kind: L -/
theorem shape2_decNode_sum {M : Type} [AddCommMonoid M] (f : (shape2 β w r).DecNode → M) :
    ∑ q, f q = ∑ i : Fin 2, (f ⟨i, none⟩ + ∑ x : Act2, f ⟨i, some ⟨x, none⟩⟩) := by
  unfold shape2 at f ⊢
  rw [sum_decNode_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_decNode_decision]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_decNode_decision]
  have h0 : ∑ a : Act2, ∑ q, f ⟨i, some ⟨x, some ⟨a, q⟩⟩⟩ = 0 :=
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun q _ => q.elim

  rw [h0, add_zero]

/-- A live node is not the simulation node of its branch (the derived decidable equality of
node addresses, decided once here so `simp` need not unfold `DecNode`).
Source: none: infrastructure. Kind: L -/
theorem shape2_node_ne₁ (i : Fin 2) (x : Act2) :
    (⟨i, some ⟨x, none⟩⟩ : (Tree.chance 2 β fun i => Tree.decision () fun x =>
      Tree.decision () fun a => (Tree.leaf (w i x a) (r i x a) : Tree Ω Unit (fun _ => Act2) ℚ)).DecNode)
      ≠ ⟨i, none⟩ := by
  intro h; cases h

/-- The simulation node is not a live node. Source: none: infrastructure. Kind: L -/
theorem shape2_node_ne₂ (i : Fin 2) (x : Act2) :
    (⟨i, none⟩ : (Tree.chance 2 β fun i => Tree.decision () fun x =>
      Tree.decision () fun a => (Tree.leaf (w i x a) (r i x a) : Tree Ω Unit (fun _ => Act2) ℚ)).DecNode)
      ≠ ⟨i, some ⟨x, none⟩⟩ := by
  intro h; cases h

/-- **Theorem 1's fiber sum on the shape**: forcing `a₀` at the simulation node of branch `i`
(the live node still drawing) contributes `β_i ∑_{a'} m(a') r(i, a₀, a')`; forcing it at the
live node below the sample `x` (the simulation still drawing) contributes `β_i m(x) r(i, x, a₀)`.
Source: [[decision-problems-v2]] §8 Theorem 1 (`∑_{q : d_q = d} R_q G_q(C, a)`)
Kind: P
Fidelity: exact -/
theorem shape2_fiberForced (a₀ : Act2) :
    fiberForced (shape2 β w r) (NodePolicy.ofProc C _) () a₀ =
      ∑ i : Fin 2, β.w i * (∑ a', (C ()).w a' * r i a₀ a' + ∑ x, (C ()).w x * r i x a₀) := by
  cases a₀ <;>
  · rw [fiberForced_unit, shape2_decNode_sum]
    simp only [Fin.sum_univ_two, Act2.sum_univ]
    unfold forcedBelow leavesBelow
    simp only [Finset.sum_filter, shape2_sum]
    unfold shape2
    simp [edgeOf, Act2.sum_univ, Fin.sum_univ_two, NodePolicy.update_restrictChance_same,
      NodePolicy.update_restrictChance_ne, NodePolicy.update_none_restrictDecision,
      NodePolicy.update_some_restrictDecision_same, NodePolicy.update_some_restrictDecision_ne,
      NodePolicy.update_some_none, NodePolicy.update_self]
    simp [NodePolicy.ofProc, NodePolicy.restrictChance, NodePolicy.restrictDecision,
      FinDistr.pure_w]
    ring

end shape

section tree

variable (δ : ℚ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (c X : ℚ) (C : Proc Unit (fun _ => Act2) ℚ)

/-- `xorTree` is the shape with XOR's leaf data. Source: none: infrastructure. Kind: L -/
theorem xorTree_eq_shape2 :
    xorTree δ h0 h1 c X = shape2 (FinDistr.coin δ h0 h1)
      (fun i x a => xorWorld (xorTermites i) x a) (fun i x a => xorPayW c X (xorTermites i) x a) :=
  rfl

/-- `d_L` is queried on XOR. Source: none: infrastructure. Kind: L -/
theorem xorTree_queried : () ∈ queried (xorTree δ h0 h1 c X) := by
  unfold xorTree; simp

/-- **Theorem 1's fiber sums on XOR**: forcing `pay` at one `d_L`-node at a time (the other node
still drawing from the label) and summing over the two simulation nodes and the four live nodes,
`∑_q R_q G_q(pay) = −2δX − 2(1−δ)cq − δc(1−q)` and `∑_q R_q G_q(refuse) = −2δX − δcq`.
Source: [[decision-problems-v2]] §8 Theorem 1; dp-sl-2-068 (`p06_theorem1_refuses`); P06-10′;
mandate T13(a)
Kind: P
Fidelity: exact (the off-letter live nodes of this encoding add the act-independent `−δX·m(x)`
terms to both acts) -/
theorem xor_fiberForced :
    fiberForced (xorTree δ h0 h1 c X) (NodePolicy.ofProc C _) () .a =
        -2 * δ * X - 2 * (1 - δ) * c * (C ()).w .a - δ * c * (1 - (C ()).w .a) ∧
      fiberForced (xorTree δ h0 h1 c X) (NodePolicy.ofProc C _) () .b =
        -2 * δ * X - δ * c * (C ()).w .a := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  constructor <;>
  · rw [xorTree_eq_shape2, shape2_fiberForced]
    simp [Fin.sum_univ_two, Act2.sum_univ, xorPayW, xorLetter, xorTermites, FinDistr.coin]
    rw [hb]; ring

/-- **Theorem 1 refuses by `c(δ(1−2q) + 2q(1−δ))`** on XOR.
Source: dp-sl-2-068 (`p06_theorem1_refuses`: "refuse beats pay in the SIA-forcing sum … by
`c(δ(1−2q) + 2q(1−δ))`"); P06-10′; mandate T13(a)
Kind: P
Fidelity: exact -/
theorem xor_fiberForced_sub :
    fiberForced (xorTree δ h0 h1 c X) (NodePolicy.ofProc C _) () .b -
        fiberForced (xorTree δ h0 h1 c X) (NodePolicy.ofProc C _) () .a =
      c * (δ * (1 - 2 * (C ()).w .a) + 2 * (C ()).w .a * (1 - δ)) := by
  obtain ⟨ha, hb⟩ := xor_fiberForced δ h0 h1 c X C
  rw [ha, hb]; ring

/-- **Theorem 1's evaluator strictly prefers refusing** for `0 < δ < ½`, `c > 0` and any label
with `q > 0` — the earlier arithmetic stub re-founded over the tree.
Source: dp-sl-2-068; P06-10′ ("Theorem 1 … refuses for `δ < ½`"); mandate T13(a)
Kind: P
Fidelity: exact
Hyps: (a) `0 < δ < ½`, `0 < c`, `0 < q` -/
theorem xor_theorem1_refuses (hδ0 : 0 < δ) (hδ : δ < 1/2) (hc : 0 < c)
    (hq : 0 < (C ()).w .a) :
    fiberForced (xorTree δ h0 h1 c X) (NodePolicy.ofProc C _) () .a <
      fiberForced (xorTree δ h0 h1 c X) (NodePolicy.ofProc C _) () .b := by
  have h := xor_fiberForced_sub δ h0 h1 c X C
  have hinner : 0 < δ * (1 - 2 * (C ()).w .a) + 2 * (C ()).w .a * (1 - δ) := by
    nlinarith [mul_pos hq (show (0 : ℚ) < 1/2 - δ by linarith)]
  have := mul_pos hc hinner
  linarith

/-- **No label with `q > 0` is D3⁰-consistent on XOR** (`dp-calibration`'s `OccEdtConsistent`,
Theorem 1's local-optimality condition at `ε = 0`): paying is supported yet refusing has the
strictly larger fiber sum.
Source: `calibration.md` D3⁰; dp-sl-2-068; mandate T13(a)
Kind: P
Fidelity: exact
Hyps: (a) `0 < δ < ½`, `0 < c`, `0 < q` -/
theorem xor_not_occEdtConsistent (hδ0 : 0 < δ) (hδ : δ < 1/2) (hc : 0 < c)
    (hq : 0 < (C ()).w .a) : ¬ OccEdtConsistent C (xorTree δ h0 h1 c X) := by
  intro h
  have := h () (xorTree_queried δ h0 h1 c X) .a hq .b
  exact absurd this (not_le.mpr (xor_theorem1_refuses δ h0 h1 c X C hδ0 hδ hc hq))

end tree

end Cleanroom.Decision.DpDutchBook
