import Cleanroom.Found.DpCoreTree.RecordingThms

/-!
# Sums over decision nodes; `#_d` as a cardinality; the edge-mass lemma

Node-level plumbing used by Lemma 3′ (`Screening.lean`):

* `sum_decNode_chance` / `sum_decNode_decision`: sums over `DecNode` decompose along the
  constructors (like `sum_leaves_*`).
* `count_eq_card_dNodesOn`: `#_d(ℓ)` is the number of `d`-nodes on the path to `ℓ`.
* `edgeS`: the edge a leaf takes at a node, tagged with the node's point (a cast-free
  `Option (Σ d, acts d)`), with `mem_draws_iff_exists_edgeS`.
* `mass_edge`: the mass of the leaves below `q` that take edge `a` is `C(d_q)(a)` times the
  mass of the leaves below `q`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [DecidableEq ι]

namespace Tree

/-! ### Sums over decision nodes -/

section sums

variable {M : Type} [AddCommMonoid M]

/-- Sums over the decision nodes of a chance node.
Source: none: infrastructure
Kind: L -/
theorem sum_decNode_chance {n : ℕ} {β : FinDistr K (Fin n)} {child : Fin n → Tree Ω ι acts K}
    (f : (chance n β child).DecNode → M) : ∑ q, f q = ∑ i, ∑ q, f ⟨i, q⟩ :=
  Fintype.sum_sigma _

/-- Sums over the decision nodes of a decision node: the node itself plus its children's.
Source: none: infrastructure
Kind: L -/
theorem sum_decNode_decision {d : ι} {child : acts d → Tree Ω ι acts K}
    (f : (decision d child).DecNode → M) : ∑ q, f q = f none + ∑ a, ∑ q, f (some ⟨a, q⟩) := by
  have h1 : ∑ q, f q = f none + ∑ x : Σ a, (child a).DecNode, f (some x) :=
    Fintype.sum_option f
  have h2 : ∑ x : Σ a, (child a).DecNode, f (some x) = ∑ a, ∑ q, f (some ⟨a, q⟩) :=
    Fintype.sum_sigma _
  rw [h1, h2]

end sums

/-! ### `#_d` as a cardinality -/

/-- Membership in `dNodesOn`.
Source: none: infrastructure
Kind: L -/
@[simp] theorem mem_dNodesOn (B : Tree Ω ι acts K) (d : ι) (ℓ : B.Leaves) (q : B.DecNode) :
    q ∈ dNodesOn B d ℓ ↔ pt B q = d ∧ (edgeOf B q ℓ).isSome := by
  simp [dNodesOn]

/-- `#_d(ℓ)` counts the `d`-nodes on the path to `ℓ`.
Source: [[decision-problems-v2]] §3.1 Definition 6 (`#_d(ℓ)` "counts the `d`-nodes on the path")
Kind: L -/
theorem count_eq_card_dNodesOn (d : ι) :
    (B : Tree Ω ι acts K) → ∀ ℓ, count d B ℓ = (dNodesOn B d ℓ).card
  | leaf _ _, _ => by
      simp only [count_leaf, dNodesOn]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q _; exact q.elim
  | chance _ β child, ⟨i, ℓ⟩ => by
      rw [count_chance, count_eq_card_dNodesOn d (child i) ℓ]
      unfold dNodesOn
      rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter,
        sum_decNode_chance]
      rw [Finset.sum_eq_single i]
      · refine Finset.sum_congr rfl fun q _ => ?_
        simp only [pt_chance, edgeOf_chance, dite_true]
      · intro j _ hj
        apply Finset.sum_eq_zero
        intro q _
        simp [edgeOf_chance, Ne.symm hj]
      · intro h; exact absurd (Finset.mem_univ i) h
  | decision d' child, ⟨a, ℓ⟩ => by
      rw [count_decision, count_eq_card_dNodesOn d (child a) ℓ]
      unfold dNodesOn
      rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter,
        sum_decNode_decision]
      congr 1
      · simp only [pt_decision_none, edgeOf_decision_none, Option.isSome_some, and_true]
      · rw [Finset.sum_eq_single a]
        · refine Finset.sum_congr rfl fun q _ => ?_
          simp only [pt_decision_some, edgeOf_decision_some, dite_true]
        · intro b _ hb
          apply Finset.sum_eq_zero
          intro q _
          simp [edgeOf_decision_some, Ne.symm hb]
        · intro h; exact absurd (Finset.mem_univ a) h

/-- `dNodesOn = fiber.filter (edge isSome)`.
Source: none: infrastructure
Kind: L -/
theorem dNodesOn_eq_filter_fiber (B : Tree Ω ι acts K) (d : ι) (ℓ : B.Leaves) :
    dNodesOn B d ℓ = (fiber B d).filter fun q => (edgeOf B q ℓ).isSome := by
  ext q; simp [dNodesOn, fiber]

/-! ### The tagged edge -/

/-- The edge a leaf takes at `q`, tagged with the node's point: `some ⟨d_q, a⟩` if the path
passes through `q` taking its `a`-edge, else `none`.
Source: none: infrastructure (a cast-free form of `edgeOf`)
Kind: D -/
def edgeS (B : Tree Ω ι acts K) (q : B.DecNode) (ℓ : B.Leaves) : Option (Σ d : ι, acts d) :=
  (edgeOf B q ℓ).map fun a => ⟨pt B q, a⟩

/-- `edgeS` at the node's own point is `edgeOf`.
Source: none: infrastructure
Kind: L -/
theorem edgeS_eq_some_iff (B : Tree Ω ι acts K) (q : B.DecNode) (ℓ : B.Leaves)
    (a : acts (pt B q)) : edgeS B q ℓ = some ⟨pt B q, a⟩ ↔ edgeOf B q ℓ = some a := by
  unfold edgeS
  cases h : edgeOf B q ℓ with
  | none => simp
  | some b => simp [Sigma.mk.injEq]

/-- A tagged edge names the node's point.
Source: none: infrastructure
Kind: L -/
theorem pt_eq_of_edgeS (B : Tree Ω ι acts K) (q : B.DecNode) (ℓ : B.Leaves) {x : Σ d, acts d}
    (h : edgeS B q ℓ = some x) : pt B q = x.1 := by
  unfold edgeS at h
  cases h' : edgeOf B q ℓ with
  | none => rw [h'] at h; cases h
  | some b => rw [h'] at h; simp only [Option.map_some, Option.some.injEq] at h; rw [← h]

/-- A tagged edge is an edge.
Source: none: infrastructure
Kind: L -/
theorem isSome_of_edgeS (B : Tree Ω ι acts K) (q : B.DecNode) (ℓ : B.Leaves) {x : Σ d, acts d}
    (h : edgeS B q ℓ = some x) : (edgeOf B q ℓ).isSome := by
  unfold edgeS at h
  cases h' : edgeOf B q ℓ with
  | none => rw [h'] at h; cases h
  | some b => rfl

/-- The draws on a path are exactly the tagged edges of the nodes on it.
Source: none: infrastructure
Kind: L -/
theorem mem_draws_iff_exists_edgeS :
    (B : Tree Ω ι acts K) → ∀ (ℓ : B.Leaves) (x : Σ d, acts d),
      x ∈ draws B ℓ ↔ ∃ q, edgeS B q ℓ = some x
  | leaf _ _, _, x => by
      simp only [draws_leaf, List.not_mem_nil, false_iff, not_exists]
      intro q; exact q.elim
  | chance _ β child, ⟨i, ℓ⟩, x => by
      rw [draws_chance, mem_draws_iff_exists_edgeS (child i) ℓ x]
      constructor
      · rintro ⟨q, hq⟩
        refine ⟨⟨i, q⟩, ?_⟩
        unfold edgeS at hq ⊢
        rw [edgeOf_chance, dif_pos rfl]
        exact hq
      · rintro ⟨⟨j, q⟩, hq⟩
        by_cases hij : i = j
        · subst hij
          refine ⟨q, ?_⟩
          unfold edgeS at hq ⊢
          rw [edgeOf_chance, dif_pos rfl] at hq
          exact hq
        · unfold edgeS at hq
          rw [edgeOf_chance, dif_neg hij] at hq
          cases hq
  | decision d child, ⟨a, ℓ⟩, x => by
      rw [draws_decision, List.mem_cons, mem_draws_iff_exists_edgeS (child a) ℓ x]
      constructor
      · rintro (rfl | ⟨q, hq⟩)
        · exact ⟨none, by simp [edgeS]⟩
        · refine ⟨some ⟨a, q⟩, ?_⟩
          unfold edgeS at hq ⊢
          rw [edgeOf_decision_some, dif_pos rfl]
          exact hq
      · rintro ⟨_ | ⟨b, q⟩, hq⟩
        · left
          simp [edgeS, edgeOf_decision_none] at hq
          first | exact hq.symm | exact hq
        · right
          by_cases hab : a = b
          · subst hab
            refine ⟨q, ?_⟩
            unfold edgeS at hq ⊢
            rw [edgeOf_decision_some, dif_pos rfl] at hq
            exact hq
          · unfold edgeS at hq
            rw [edgeOf_decision_some, dif_neg hab] at hq
            cases hq

/-! ### The edge-mass lemma -/

/-- **Edge mass**: the mass of the leaves below `q` taking edge `a` is `C(d_q)(a)` times the
mass of the leaves below `q`.
Source: [[decision-problems-v2]] §3.1 Definition 6 (the walk draws `a ∼ C(d_q)` at `q`
independently of the path); §7.3 Lemma 3 proof ("Definition 6 samples the draw independently of
the path")
Kind: P -/
theorem mass_edge (C : Proc ι acts K) :
    (B : Tree Ω ι acts K) → ∀ (q : B.DecNode) (a : acts (pt B q)),
      (∑ ℓ, if edgeOf B q ℓ = some a then leafLaw C B ℓ else 0) =
        (C (pt B q)).w a * ∑ ℓ, if (edgeOf B q ℓ).isSome then leafLaw C B ℓ else 0
  | leaf _ _, q, _ => q.elim
  | chance _ β child, ⟨i, q⟩, a => by
      rw [sum_leaves_chance, sum_leaves_chance, Finset.sum_eq_single i, Finset.sum_eq_single i]
      · simp only [edgeOf_chance, dite_true, leafLaw_chance, ite_mul_zero_eq, ← Finset.mul_sum,
          pt_chance]
        rw [mass_edge C (child i) q a]
        ring
      · intro j _ hj; apply Finset.sum_eq_zero; intro ℓ _; simp [edgeOf_chance, hj]
      · intro h; exact absurd (Finset.mem_univ i) h
      · intro j _ hj; apply Finset.sum_eq_zero; intro ℓ _; simp [edgeOf_chance, hj]
      · intro h; exact absurd (Finset.mem_univ i) h
  | decision d child, none, a => by
      revert a
      show ∀ a : acts d,
        (∑ ℓ, if edgeOf (decision d child) none ℓ = some a then leafLaw C (decision d child) ℓ
          else 0) =
        (C d).w a * ∑ ℓ, if (edgeOf (decision d child) none ℓ).isSome
          then leafLaw C (decision d child) ℓ else 0
      intro a
      rw [sum_leaves_decision, sum_leaves_decision]
      simp only [edgeOf_decision_none, Option.some.injEq, Option.isSome_some, if_true,
        leafLaw_decision]
      rw [Finset.sum_eq_single a]
      · simp [← Finset.mul_sum, sum_leafLaw, FinDistr.sum_one]
      · intro b _ hb; apply Finset.sum_eq_zero; intro ℓ _; simp [hb]
      · intro h; exact absurd (Finset.mem_univ a) h
  | decision d child, some ⟨c, q⟩, a => by
      rw [sum_leaves_decision, sum_leaves_decision, Finset.sum_eq_single c, Finset.sum_eq_single c]
      · simp only [edgeOf_decision_some, dite_true, leafLaw_decision, ite_mul_zero_eq,
          ← Finset.mul_sum, pt_decision_some]
        rw [mass_edge C (child c) q a]
        ring
      · intro b _ hb; apply Finset.sum_eq_zero; intro ℓ _; simp [edgeOf_decision_some, hb]
      · intro h; exact absurd (Finset.mem_univ c) h
      · intro b _ hb; apply Finset.sum_eq_zero; intro ℓ _; simp [edgeOf_decision_some, hb]
      · intro h; exact absurd (Finset.mem_univ c) h

end Tree

end Cleanroom.Found.DpCoreTree
