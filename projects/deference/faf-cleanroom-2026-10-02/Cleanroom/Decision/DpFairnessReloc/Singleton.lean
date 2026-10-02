import Cleanroom.Decision.DpFairnessReloc.Fair

/-!
# Claim B: under evented chance and full recording, strongly fair fibers are singletons (T3(c))

Package `dp-fairness-reloc`, file 7. `adversary-repair.md` Claim B's "deeper structural fact":
on a pruned tree with **evented chance** (leaf worlds below distinct children of a chance node
are distinct — the edge events exist and are pairwise disjoint), **recording at every queried
point for every procedure**, and **realized observations** (every queried point's `O_d` is hit by
a positive run), **strong fairness forces every fiber to be a singleton**. So on FR-11's class the
fiber machinery is vacuous, and multi-member perfect-copy fibers exist only where the world
algebra is blind to which instance is which (un-evented chance) or recording fails.

The proof runs the source's argument: two members diverge at a branching node; at a chance node
the iso carries a leaf below one member to a leaf below the other with the *same world*, which
evented chance forbids; at a decision node carrying `e`, fairness transports subtree-veridicality
from the recorded `e`-node to the branching node, and recording's action clauses give the two
leaves' common world disjoint act-events.

Modelling choice: **evented chance** is rendered structurally (`EventedChance`): worlds of leaves
below distinct children of any chance node differ. This is equivalent to the existence of
pairwise-disjoint edge events entailed by the leaf worlds (take the events to be the world sets
below each edge). "a.s." is `Pruned` (every path has positive chance weight).
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-- **Evented chance (EC)**: the leaf worlds below distinct children of every chance node are
distinct — equivalently, every chance edge carries an event entailed by the leaf worlds below it,
pairwise disjoint across the edges of one node.
Source: `fair-repair.md` §1.1 "(EC) evented chance: every chance edge carries an event of `𝓔`;
edges of one chance node pairwise disjoint; leaf-worlds entail the events on their root-path"
Kind: D
Fidelity: variant: rendered as distinctness of the worlds below distinct edges (equivalent to
the existence of the events, which are then the world sets below the edges) -/
def EventedChance : Tree Ω ι acts K → Prop
  | .leaf _ _ => True
  | .chance _ _ child =>
      (∀ i j, i ≠ j → ∀ ℓ ℓ', world (child i) ℓ ≠ world (child j) ℓ') ∧ ∀ i, EventedChance (child i)
  | .decision _ child => ∀ a, EventedChance (child a)

/-! ### Leaves of a subtree as leaves of the tree -/

/-- A leaf of the subtree at `q`, as a leaf of the whole tree (below `q`).
Source: none: infrastructure
Kind: D -/
def embedLeaf : (B : Tree Ω ι acts K) → (q : B.DecNode) → (subtreeAt B q).Leaves → B.Leaves
  | .leaf _ _, q, _ => q.elim
  | .chance _ _ child, ⟨i, q⟩, ℓ => ⟨i, embedLeaf (child i) q ℓ⟩
  | .decision _ _, none, ℓ => ℓ
  | .decision _ child, some ⟨a, q⟩, ℓ => ⟨a, embedLeaf (child a) q ℓ⟩

theorem world_embedLeaf : (B : Tree Ω ι acts K) → ∀ (q : B.DecNode) (ℓ : (subtreeAt B q).Leaves),
    world B (embedLeaf B q ℓ) = world (subtreeAt B q) ℓ
  | .leaf _ _, q, _ => q.elim
  | .chance _ _ child, ⟨i, q⟩, ℓ => world_embedLeaf (child i) q ℓ
  | .decision _ _, none, _ => rfl
  | .decision _ child, some ⟨a, q⟩, ℓ => world_embedLeaf (child a) q ℓ

variable [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Fintype (acts d)]

theorem edgeOf_embedLeaf : (B : Tree Ω ι acts K) → ∀ (q : B.DecNode) (ℓ : (subtreeAt B q).Leaves),
    (edgeOf B q (embedLeaf B q ℓ)).isSome
  | .leaf _ _, q, _ => q.elim
  | .chance _ _ child, ⟨i, q⟩, ℓ => by
      show (edgeOf (Tree.chance _ _ child) ⟨i, q⟩ ⟨i, embedLeaf (child i) q ℓ⟩).isSome
      rw [edgeOf_chance, dif_pos rfl]
      exact edgeOf_embedLeaf (child i) q ℓ
  | .decision d child, none, ⟨a, ℓ⟩ => by
      show (edgeOf (Tree.decision d child) none ⟨a, ℓ⟩).isSome
      simp
  | .decision _ child, some ⟨a, q⟩, ℓ => by
      show (edgeOf (Tree.decision _ child) (some ⟨a, q⟩) ⟨a, embedLeaf (child a) q ℓ⟩).isSome
      rw [edgeOf_decision_some, dif_pos rfl]
      exact edgeOf_embedLeaf (child a) q ℓ

/-- Every leaf below `q` is a leaf of the subtree at `q`.
Source: none: infrastructure
Kind: L -/
theorem exists_embedLeaf_of_edge : (B : Tree Ω ι acts K) → ∀ (q : B.DecNode) (ℓ : B.Leaves),
    (edgeOf B q ℓ).isSome → ∃ ℓ', embedLeaf B q ℓ' = ℓ
  | .leaf _ _, q, _, _ => q.elim
  | .chance _ _ child, ⟨i, q⟩, ⟨j, ℓ⟩, h => by
      by_cases hji : j = i
      · subst hji
        rw [edgeOf_chance, dif_pos rfl] at h
        obtain ⟨ℓ', hℓ'⟩ := exists_embedLeaf_of_edge (child j) q ℓ h
        exact ⟨ℓ', by rw [← hℓ']; rfl⟩
      · simp [edgeOf_chance, hji] at h
  | .decision _ _, none, ℓ, _ => ⟨ℓ, rfl⟩
  | .decision _ child, some ⟨a, q⟩, ⟨b, ℓ⟩, h => by
      by_cases hba : b = a
      · subst hba
        rw [edgeOf_decision_some, dif_pos rfl] at h
        obtain ⟨ℓ', hℓ'⟩ := exists_embedLeaf_of_edge (child b) q ℓ h
        exact ⟨ℓ', by rw [← hℓ']; rfl⟩
      · simp [edgeOf_decision_some, hba] at h

/-! ### The honesty package used by the argument -/

/-- **Node honesty**: every decision node is subtree-veridical, and every leaf below it satisfies
the act-event of the edge it took there and no other. (This is what recording at every point,
realized observations and strong fairness jointly deliver on a pruned tree — `nodeHonest_of`.)
Source: `adversary-repair.md` Claim B proof ("fairness propagates subtree-veridicality to `n` …
recording's action clauses make leaf-worlds below different action-edges of `n` entail disjoint
act-events")
Kind: D -/
def NodeHonest (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω) (B : Tree Ω ι acts K) :
    Prop :=
  ∀ q : B.DecNode, (∀ ℓ, (edgeOf B q ℓ).isSome → world B ℓ ∈ obs (pt B q)) ∧
    ∀ ℓ a, edgeOf B q ℓ = some a →
      world B ℓ ∈ actEv (pt B q) a ∧ ∀ a', world B ℓ ∈ actEv (pt B q) a' → a' = a

section hereditary

variable {obs : ι → Finset Ω} {actEv : (d : ι) → acts d → Finset Ω}

theorem NodeHonest.chance_child {n : ℕ} {β : FinDistr K (Fin n)} {child : Fin n → Tree Ω ι acts K}
    (h : NodeHonest obs actEv (.chance n β child)) (i : Fin n) : NodeHonest obs actEv (child i) := by
  intro q
  obtain ⟨h1, h2⟩ := h ⟨i, q⟩
  refine ⟨fun ℓ hℓ => ?_, fun ℓ a ha => ?_⟩
  · have := h1 ⟨i, ℓ⟩ (by rw [edgeOf_chance, dif_pos rfl]; exact hℓ)
    exact this
  · have := h2 ⟨i, ℓ⟩ a (by rw [edgeOf_chance, dif_pos rfl]; exact ha)
    exact this

theorem NodeHonest.decision_child {d : ι} {child : acts d → Tree Ω ι acts K}
    (h : NodeHonest obs actEv (.decision d child)) (a : acts d) : NodeHonest obs actEv (child a) := by
  intro q
  obtain ⟨h1, h2⟩ := h (some ⟨a, q⟩)
  refine ⟨fun ℓ hℓ => ?_, fun ℓ b hb => ?_⟩
  · have := h1 ⟨a, ℓ⟩ (by rw [edgeOf_decision_some, dif_pos rfl]; exact hℓ)
    exact this
  · have := h2 ⟨a, ℓ⟩ b (by rw [edgeOf_decision_some, dif_pos rfl]; exact hb)
    exact this

theorem EventedChance.chance_child {n : ℕ} {β : FinDistr K (Fin n)}
    {child : Fin n → Tree Ω ι acts K} (h : EventedChance (.chance n β child)) (i : Fin n) :
    EventedChance (child i) := h.2 i

theorem EventedChance.decision_child {d : ι} {child : acts d → Tree Ω ι acts K}
    (h : EventedChance (.decision d child)) (a : acts d) : EventedChance (child a) := h a

/-- **The core of Claim B**: on a strongly fair, evented-chance, node-honest tree every fiber has
at most one member.
Source: `adversary-repair.md` Claim B ("strong fairness with `(λ,r)`-preserving isomorphism
forces every fiber to be a singleton")
Kind: P -/
theorem fiber_subsingleton_of_honest [∀ d, Nonempty (acts d)] :
    (B : Tree Ω ι acts K) → StronglyFair B → EventedChance B → NodeHonest obs actEv B →
      ∀ d, ∀ q ∈ fiber B d, ∀ q' ∈ fiber B d, q = q'
  | .leaf _ _, _, _, _ => fun _ q _ _ _ => q.elim
  | .chance _ β child, hf, hec, hh => by
      rintro d ⟨i, r⟩ hq ⟨j, r'⟩ hq'
      rw [mem_fiber] at hq hq'
      by_cases hij : i = j
      · subst hij
        have := fiber_subsingleton_of_honest (child i) (hf.chance_child i) (hec.chance_child i)
          (hh.chance_child i) d r (by simpa using hq) r' (by simpa using hq')
        rw [this]
      · exfalso
        have hiso := hf d ⟨i, r⟩ (by simpa using hq) ⟨j, r'⟩ (by simpa using hq')
        simp only [subtreeAt_chance] at hiso
        obtain ⟨e, he⟩ := hiso.exists_leafEquiv
        have ⟨ℓ₁⟩ := leaves_nonempty (subtreeAt (child i) r)
        obtain ⟨hw, -, -, -⟩ := he ℓ₁
        apply hec.1 i j hij (embedLeaf (child i) r ℓ₁) (embedLeaf (child j) r' (e ℓ₁))
        rw [world_embedLeaf, world_embedLeaf, hw]
  | .decision d' child, hf, hec, hh => by
      rintro d q hq q' hq'
      rw [mem_fiber] at hq hq'
      rcases q with _ | ⟨a, r⟩ <;> rcases q' with _ | ⟨a', r'⟩
      · rfl
      · exfalso
        have hiso := hf d none (by simpa using hq) (some ⟨a', r'⟩) (by simpa using hq')
        simp only [subtreeAt_decision_none, subtreeAt_decision_some] at hiso
        have hs := hiso.size_eq
        have h1 := size_subtreeAt_le (child a') r'
        have h2 := size_child_lt_decision d' child a'
        omega
      · exfalso
        have hiso := hf d (some ⟨a, r⟩) (by simpa using hq) none (by simpa using hq')
        simp only [subtreeAt_decision_none, subtreeAt_decision_some] at hiso
        have hs := hiso.size_eq
        have h1 := size_subtreeAt_le (child a) r
        have h2 := size_child_lt_decision d' child a
        omega
      · by_cases haa : a = a'
        · subst haa
          have := fiber_subsingleton_of_honest (child a) (hf.decision_child a)
            (hec.decision_child a) (hh.decision_child a) d r (by simpa using hq) r'
            (by simpa using hq')
          rw [this]
        · exfalso
          have hiso := hf d (some ⟨a, r⟩) (by simpa using hq) (some ⟨a', r'⟩) (by simpa using hq')
          simp only [subtreeAt_decision_some] at hiso
          obtain ⟨e, he⟩ := hiso.exists_leafEquiv
          have ⟨ℓ₁⟩ := leaves_nonempty (subtreeAt (child a) r)
          obtain ⟨hw, -, -, -⟩ := he ℓ₁
          -- the two leaves of `B` with a common world, below the root's `a`- and `a'`-edges
          obtain ⟨-, hroot⟩ := hh none
          have hL₁ := hroot ⟨a, embedLeaf (child a) r ℓ₁⟩ a rfl
          have hL₂ := hroot ⟨a', embedLeaf (child a') r' (e ℓ₁)⟩ a' rfl
          simp only [pt_decision_none, world_decision] at hL₁ hL₂
          rw [world_embedLeaf] at hL₁ hL₂
          rw [hw] at hL₂
          exact haa (hL₁.2 a' hL₂.1).symm

end hereditary

/-! ### Deriving node honesty from recording, realized observations and fairness -/

section derive

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)

/-- Strong fairness transports subtree-veridicality across a fiber.
Source: `adversary-repair.md` Claim A.1 / Claim B proof ("fairness propagates
subtree-veridicality")
Kind: L -/
theorem StronglyFair.subtreeVeridical_transfer {B : Tree Ω ι acts K} (hf : StronglyFair B)
    {q m : B.DecNode} (hqm : pt B q = pt B m) (hm : SubtreeVeridical obs B m) :
    SubtreeVeridical obs B q := by
  intro ℓ hℓ
  rw [mem_leavesBelow] at hℓ
  obtain ⟨ℓ₁, rfl⟩ := exists_embedLeaf_of_edge B q ℓ hℓ
  have hiso := hf (pt B q) q (by simp) m (by simp [hqm])
  obtain ⟨e, he⟩ := hiso.exists_leafEquiv
  obtain ⟨hw, -, -, -⟩ := he ℓ₁
  rw [world_embedLeaf, ← hw, ← world_embedLeaf]
  have := hm (embedLeaf B m (e ℓ₁)) (by rw [mem_leavesBelow]; exact edgeOf_embedLeaf B m _)
  rwa [hqm]

/-- **Node honesty from the source's hypotheses**: on a pruned, strongly fair tree that records
at every queried point for every procedure and realizes every observation, every node is honest.
Source: `adversary-repair.md` Claim B proof
Kind: P -/
theorem nodeHonest_of [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K} (hf : StronglyFair B)
    (hpr : Pruned B) (hrec : ∀ e ∈ queried B, RecordsFor obs actEv (Proc.uniform : Proc ι acts K) B e)
    (hreal : ∀ e ∈ queried B, ∃ ℓ, Positive B ℓ ∧ world B ℓ ∈ obs e) :
    NodeHonest obs actEv B := by
  intro q
  -- the point of `q` is queried
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_leaf_below B q
  have hqu : pt B q ∈ queried B :=
    (mem_queried_iff _ B).mpr ⟨ℓ₀, count_pos_of_edge B q ℓ₀ hℓ₀⟩
  -- a realized `O`-run passes a recorded, subtree-veridical node of the same point
  obtain ⟨ℓs, hpos, hobs⟩ := hreal _ hqu
  have hlaw : 0 < leafLaw (Proc.uniform : Proc ι acts K) B ℓs :=
    (leafLaw_pos_iff_of_fullSupport Proc.uniform_fullSupport B ℓs).mpr hpos
  obtain ⟨hcount, hnodes⟩ := hrec _ hqu ℓs hlaw hobs
  obtain ⟨m, hm, hme⟩ := exists_dNode_of_count_pos (pt B q) B ℓs (by omega)
  obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp hme
  have hsv : SubtreeVeridical obs B m := (hnodes m hm a₀ ha₀).1
  have hsvq : SubtreeVeridical obs B q := hf.subtreeVeridical_transfer obs hm.symm hsv
  refine ⟨fun ℓ hℓ => hsvq ℓ (by rw [mem_leavesBelow]; exact hℓ), fun ℓ a ha => ?_⟩
  -- recording at the leaf `ℓ` itself
  have hℓobs : world B ℓ ∈ obs (pt B q) := hsvq ℓ (by rw [mem_leavesBelow, ha]; rfl)
  have hℓlaw : 0 < leafLaw (Proc.uniform : Proc ι acts K) B ℓ :=
    (leafLaw_pos_iff_of_fullSupport Proc.uniform_fullSupport B ℓ).mpr (hpr ℓ)
  obtain ⟨-, hnodes'⟩ := hrec _ hqu ℓ hℓlaw hℓobs
  exact (hnodes' q rfl a ha).2

/-- **Claim B (singleton collapse)**: on a pruned tree with evented chance that records at every
queried point for every procedure and realizes every observation, strong fairness (with
`(λ, r)`-preserving isomorphism) forces every fiber to be a singleton. So on FR-11's class the
fiber-summation machinery is vacuous, and multi-instance "perfect-copy simulation" fibers exist
only where the world algebra is blind to which instance is which or recording fails.
Source: `adversary-repair.md` Claim B ("Under full EC + FRec with all observations realized …
strong fairness … forces every fiber to be a singleton"); `equiv.md` EQ-2 scope; A34
Kind: P
Fidelity: stronger: recording is required for the uniform procedure only (the source asks it for
every procedure; `singleton_fibers_of_recordsForAll` is that form). EC is rendered structurally
(equivalent to the source's edge-event clause, see the module docstring) — exact, not a
substitution. `Pruned` is added to the source's wording: it is the "a.s." of Definition 7 read on
every leaf, and the decision-node case needs honesty at an arbitrary leaf of the subtree.
Hyps: none (recording and realized observations are Definition 7 and the source's FRec and
realization hypotheses, taken as definitions of record) -/
theorem singleton_fibers [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K} (hf : StronglyFair B)
    (hec : EventedChance B) (hpr : Pruned B)
    (hrec : ∀ e ∈ queried B, RecordsFor obs actEv (Proc.uniform : Proc ι acts K) B e)
    (hreal : ∀ e ∈ queried B, ∃ ℓ, Positive B ℓ ∧ world B ℓ ∈ obs e) :
    ∀ d, ∀ q ∈ fiber B d, ∀ q' ∈ fiber B d, q = q' :=
  fiber_subsingleton_of_honest B hf hec (nodeHonest_of obs actEv hf hpr hrec hreal)

/-- Claim B in the source's form: recording at every queried point for **every** procedure.
Source: `adversary-repair.md` Claim B
Kind: C -/
theorem singleton_fibers_of_recordsForAll [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (hf : StronglyFair B) (hec : EventedChance B) (hpr : Pruned B)
    (hrec : ∀ e ∈ queried B, RecordsForAll obs actEv B e)
    (hreal : ∀ e ∈ queried B, ∃ ℓ, Positive B ℓ ∧ world B ℓ ∈ obs e) :
    ∀ d, ∀ q ∈ fiber B d, ∀ q' ∈ fiber B d, q = q' :=
  singleton_fibers obs actEv hf hec hpr (fun e he => hrec e he Proc.uniform) hreal

end derive

end Cleanroom.Decision.DpFairnessReloc
