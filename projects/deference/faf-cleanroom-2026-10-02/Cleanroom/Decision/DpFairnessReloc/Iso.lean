import Cleanroom.Found.DpCoreTree

/-!
# Labelled isomorphism `≅`, world relabelling, transport of the run law

Package `dp-fairness-reloc` (area `decision`), file 1. The definition of record of *labelled
isomorphism* of concrete decision problems (phase 1's "isomorphic labelled subtrees",
`fair-repair.md` §0; v2-amendments A34 Definition 25, first candidate): leaves match on
`(λ, r)`; chance nodes match up to a permutation of the children that carries the chance
weights; decision nodes carry the same point and match children action by action. Chance-child
*order* is not a label (a permutation is allowed); a probability-one chance node is **not**
identified with its child (that is `≃_Δ`, `Relations.lean`), so `≅` preserves node count.

Also here: `size` (node count) and its `≅`-invariance, world relabelling `mapWorld` (used for the
*pre-enrichment* fairness of relocated trees, adversary-repair Claim B), and the transport
theorem: isomorphic trees have a bijection of leaves preserving world, payoff, chance weight and
the draw sequence — hence the same Definition-6 and Definition-6′ laws under every procedure.

Every definition here is over `dp-core-tree`'s `Tree` (`Cleanroom.Found.DpCoreTree`); nothing
of that package is restated.
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-- **Labelled isomorphism `T ≅ T'`** (definition of record): leaves iff equal `(ω, r)`; chance
nodes iff same arity and some permutation `σ` of the children with `β'(σ i) = β(i)` and
`child i ≅ child' (σ i)`; decision nodes iff the same point and `child a ≅ child' a` for every
action. Chance-child order is not a label; probability-one chance nodes do not collapse.
Source: `fair-repair.md` §0 ("Strong (structural) fairness … isomorphic labelled subtrees
(rooted-tree isomorphism preserving chance labels `β`, decision-point labels, and leaf pairs
`(λ, r)`)"); `v2-amendments.md` A34 Definition 25 (first candidate)
Kind: D
Fidelity: exact -/
inductive LabIso : Tree Ω ι acts K → Tree Ω ι acts K → Prop
  | leaf (ω : Ω) (r : K) : LabIso (.leaf ω r) (.leaf ω r)
  | chance {n : ℕ} (β β' : FinDistr K (Fin n)) (child child' : Fin n → Tree Ω ι acts K)
      (σ : Equiv.Perm (Fin n)) (hβ : ∀ i, β'.w (σ i) = β.w i)
      (h : ∀ i, LabIso (child i) (child' (σ i))) :
      LabIso (.chance n β child) (.chance n β' child')
  | decision (d : ι) (child child' : acts d → Tree Ω ι acts K)
      (h : ∀ a, LabIso (child a) (child' a)) :
      LabIso (.decision d child) (.decision d child')

/-- `≅` is reflexive (identity permutation at every chance node).
Source: none: infrastructure
Kind: L -/
theorem LabIso.refl : (T : Tree Ω ι acts K) → LabIso T T
  | .leaf ω r => .leaf ω r
  | .chance _ β child => .chance β β child child (Equiv.refl _) (fun _ => rfl)
      (fun i => LabIso.refl (child i))
  | .decision d child => .decision d child child (fun a => LabIso.refl (child a))

/-- Term equality is a sufficient condition for `≅` (used in witnesses; never as the
definition, since chance-child order is not a label).
Source: mandate §3 ("Term equality `=` may serve as a sufficient condition in witnesses")
Kind: L -/
theorem LabIso.of_eq {T T' : Tree Ω ι acts K} (h : T = T') : LabIso T T' := h ▸ LabIso.refl T

/-- `≅` is symmetric (inverse permutation).
Source: none: infrastructure
Kind: L -/
theorem LabIso.symm {T T' : Tree Ω ι acts K} (h : LabIso T T') : LabIso T' T := by
  induction h with
  | leaf ω r => exact .leaf ω r
  | chance β β' child child' σ hβ h ih =>
      refine .chance β' β child' child σ.symm (fun i => ?_) (fun i => ?_)
      · have := hβ (σ.symm i); simpa using this.symm
      · simpa using ih (σ.symm i)
  | decision d child child' h ih => exact .decision d child' child ih

/-- `≅` is transitive (composition of permutations).
Source: none: infrastructure
Kind: L -/
theorem LabIso.trans {A B C : Tree Ω ι acts K} (h₁ : LabIso A B) (h₂ : LabIso B C) :
    LabIso A C := by
  induction h₁ generalizing C with
  | leaf ω r => cases h₂; exact .leaf ω r
  | chance β β' child child' σ hβ h ih =>
      cases h₂ with
      | chance _ β'' _ child'' σ' hβ' h' =>
          refine .chance β β'' child child'' (σ.trans σ') (fun i => ?_) (fun i => ?_)
          · simp only [Equiv.trans_apply]; rw [hβ' (σ i), hβ i]
          · exact ih i (h' (σ i))
  | decision d child child' h ih =>
      cases h₂ with
      | decision _ _ child'' h' => exact .decision d child child'' fun a => ih a (h' a)

/-- `≅` is an equivalence relation.
Source: mandate §3 ("Prove `≅` is an equivalence")
Kind: L -/
theorem LabIso.equivalence : Equivalence (LabIso (Ω := Ω) (ι := ι) (acts := acts) (K := K)) :=
  ⟨LabIso.refl, LabIso.symm, LabIso.trans⟩

/-! ### Node count -/

section size

variable [∀ d, Fintype (acts d)]

/-- The number of nodes of a tree (leaves included).
Source: `fair-repair.md` FR-1(i) ("a proper subtree of a finite tree is not isomorphic to the
whole"); mandate T2(c) ("node count or height strictly drops along `subtreeAt`")
Kind: D -/
def size : Tree Ω ι acts K → ℕ
  | .leaf _ _ => 1
  | .chance _ _ child => 1 + ∑ i, size (child i)
  | .decision _ child => 1 + ∑ a, size (child a)

@[simp] theorem size_leaf (ω : Ω) (r : K) : size (.leaf ω r : Tree Ω ι acts K) = 1 := rfl

@[simp] theorem size_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K) :
    size (.chance n β child) = 1 + ∑ i, size (child i) := rfl

@[simp] theorem size_decision (d : ι) (child : acts d → Tree Ω ι acts K) :
    size (.decision d child) = 1 + ∑ a, size (child a) := rfl

/-- Every tree has at least one node.
Source: none: infrastructure
Kind: L -/
theorem one_le_size : (T : Tree Ω ι acts K) → 1 ≤ size T
  | .leaf _ _ => le_rfl
  | .chance _ _ _ => by simp
  | .decision _ _ => by simp

/-- A child of a chance node is strictly smaller than the node.
Source: none: infrastructure
Kind: L -/
theorem size_child_lt_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (i : Fin n) : size (child i) < size (.chance n β child) := by
  rw [size_chance]
  have := Finset.single_le_sum (fun j _ => Nat.zero_le (size (child j))) (Finset.mem_univ i)
  omega

/-- A child of a decision node is strictly smaller than the node.
Source: none: infrastructure
Kind: L -/
theorem size_child_lt_decision (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d) :
    size (child a) < size (.decision d child) := by
  rw [size_decision]
  have := Finset.single_le_sum (fun b _ => Nat.zero_le (size (child b))) (Finset.mem_univ a)
  omega

/-- **Isomorphic trees have the same node count** (a permutation of the children permutes the
sum). This is the lemma behind FR-1(i): a finite tree is not isomorphic to a proper subtree.
Source: `fair-repair.md` FR-1(i)
Kind: P -/
theorem LabIso.size_eq {T T' : Tree Ω ι acts K} (h : LabIso T T') : size T = size T' := by
  induction h with
  | leaf ω r => rfl
  | chance β β' child child' σ hβ h ih =>
      simp only [size_chance]
      congr 1
      rw [← Equiv.sum_comp σ (fun j => size (child' j))]
      exact Finset.sum_congr rfl fun i _ => ih i
  | decision d child child' h ih =>
      simp only [size_decision]
      congr 1
      exact Finset.sum_congr rfl fun a _ => ih a

end size

/-! ### World relabelling -/

variable {Ω' : Type}

/-- Relabel the leaf worlds along `f : Ω → Ω'`; the shape, chance labels, points and payoffs
are unchanged. Used to project the `pol` coordinates of a relocated tree away
(`mapWorld Prod.fst`), which is how the *pre-enrichment* fairness of the output is stated.
Source: `adversary-repair.md` Claim B ("Define fairness of `Rel_U(B)` over the pre-enrichment
algebra: isomorphism preserving `(λ|_E, r)`, fresh `pol`-coordinates exempted"); mandate §3
Kind: D -/
def mapWorld (f : Ω → Ω') : Tree Ω ι acts K → Tree Ω' ι acts K
  | .leaf ω r => .leaf (f ω) r
  | .chance n β child => .chance n β fun i => mapWorld f (child i)
  | .decision d child => .decision d fun a => mapWorld f (child a)

@[simp] theorem mapWorld_leaf (f : Ω → Ω') (ω : Ω) (r : K) :
    mapWorld f (.leaf ω r : Tree Ω ι acts K) = .leaf (f ω) r := rfl

@[simp] theorem mapWorld_chance (f : Ω → Ω') {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) :
    mapWorld f (.chance n β child) = .chance n β fun i => mapWorld f (child i) := rfl

@[simp] theorem mapWorld_decision (f : Ω → Ω') (d : ι) (child : acts d → Tree Ω ι acts K) :
    mapWorld f (.decision d child) = .decision d fun a => mapWorld f (child a) := rfl

/-- Relabelling composes.
Source: none: infrastructure
Kind: L -/
theorem mapWorld_mapWorld {Ω'' : Type} (g : Ω' → Ω'') (f : Ω → Ω') :
    (T : Tree Ω ι acts K) → mapWorld g (mapWorld f T) = mapWorld (g ∘ f) T
  | .leaf _ _ => rfl
  | .chance _ _ child => by
      simp only [mapWorld_chance]; congr 1; funext i; exact mapWorld_mapWorld g f (child i)
  | .decision _ child => by
      simp only [mapWorld_decision]; congr 1; funext a; exact mapWorld_mapWorld g f (child a)

/-- Relabelling by the identity is the identity.
Source: none: infrastructure
Kind: L -/
theorem mapWorld_id : (T : Tree Ω ι acts K) → mapWorld id T = T
  | .leaf _ _ => rfl
  | .chance _ _ child => by
      simp only [mapWorld_chance]; congr 1; funext i; exact mapWorld_id (child i)
  | .decision _ child => by
      simp only [mapWorld_decision]; congr 1; funext a; exact mapWorld_id (child a)

/-- `≅` is preserved by world relabelling (the permutations are reused).
Source: `adversary-repair.md` Claim B (pre-enrichment fairness)
Kind: L -/
theorem LabIso.mapWorld (f : Ω → Ω') {T T' : Tree Ω ι acts K} (h : LabIso T T') :
    LabIso (mapWorld f T) (mapWorld f T') := by
  induction h with
  | leaf ω r => exact .leaf (f ω) r
  | chance β β' child child' σ hβ h ih => exact .chance β β' _ _ σ hβ ih
  | decision d child child' h ih => exact .decision d _ _ ih

/-! ### Transport of the run law along an isomorphism -/

/-- A map of leaves `e : T.Leaves → T'.Leaves` *matches labels*: it preserves the world, the
payoff, the chance weight of the path and the draw sequence.
Source: mandate §3 ("isomorphic subtrees have the same leaf law up to a bijection of leaves for
every procedure")
Kind: D -/
def LeafMatch (T T' : Tree Ω ι acts K) (e : T.Leaves → T'.Leaves) : Prop :=
  ∀ ℓ, world T' (e ℓ) = world T ℓ ∧ payoff T' (e ℓ) = payoff T ℓ ∧
    chanceWeight T' (e ℓ) = chanceWeight T ℓ ∧ draws T' (e ℓ) = draws T ℓ

/-- **Transport theorem**: isomorphic trees have a bijection of leaves matching every label
Definition 6 reads (world, payoff, chance weight, draw sequence).
Source: `fair-repair.md` FR-1(ii) ("the isomorphism matches labels, and Definition 6's draws
depend only on labels"); mandate §3
Kind: P
Fidelity: exact -/
theorem LabIso.exists_leafEquiv {T T' : Tree Ω ι acts K} (h : LabIso T T') :
    ∃ e : T.Leaves ≃ T'.Leaves, LeafMatch T T' e := by
  induction h with
  | leaf ω r => exact ⟨Equiv.refl _, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  | chance β β' child child' σ hβ h ih =>
      choose e he using ih
      refine ⟨Equiv.sigmaCongr σ e, ?_⟩
      rintro ⟨i, ℓ⟩
      obtain ⟨hw, hp, hc, hd⟩ := he i ℓ
      refine ⟨?_, ?_, ?_, ?_⟩
      · show world (child' (σ i)) (e i ℓ) = world (child i) ℓ; exact hw
      · show payoff (child' (σ i)) (e i ℓ) = payoff (child i) ℓ; exact hp
      · show β'.w (σ i) * chanceWeight (child' (σ i)) (e i ℓ) =
          β.w i * chanceWeight (child i) ℓ
        rw [hβ i, hc]
      · show draws (child' (σ i)) (e i ℓ) = draws (child i) ℓ; exact hd
  | decision d child child' h ih =>
      choose e he using ih
      refine ⟨Equiv.sigmaCongrRight e, ?_⟩
      rintro ⟨a, ℓ⟩
      obtain ⟨hw, hp, hc, hd⟩ := he a ℓ
      refine ⟨?_, ?_, ?_, ?_⟩
      · show world (child' a) (e a ℓ) = world (child a) ℓ; exact hw
      · show payoff (child' a) (e a ℓ) = payoff (child a) ℓ; exact hp
      · show chanceWeight (child' a) (e a ℓ) = chanceWeight (child a) ℓ; exact hc
      · show (⟨d, a⟩ : Σ d, acts d) :: draws (child' a) (e a ℓ) =
          ⟨d, a⟩ :: draws (child a) ℓ
        rw [hd]

section transport

variable [∀ d, Fintype (acts d)]

/-- A label-matching map preserves the Definition-6 law of every procedure (path-product).
Source: `fair-repair.md` FR-1(ii)
Kind: L -/
theorem LeafMatch.leafLaw_eq {T T' : Tree Ω ι acts K} {e : T.Leaves → T'.Leaves}
    (he : LeafMatch T T' e) (C : Proc ι acts K) (ℓ : T.Leaves) :
    leafLaw C T' (e ℓ) = leafLaw C T ℓ := by
  obtain ⟨-, -, hc, hd⟩ := he ℓ
  rw [leafLaw_eq_chanceWeight_mul_drawsWeight, leafLaw_eq_chanceWeight_mul_drawsWeight, hc]
  unfold drawsWeight; rw [hd]

/-- A label-matching map preserves `#_d`.
Source: none: infrastructure
Kind: L -/
theorem LeafMatch.count_eq [DecidableEq ι] [∀ d, DecidableEq (acts d)] {T T' : Tree Ω ι acts K}
    {e : T.Leaves → T'.Leaves}
    (he : LeafMatch T T' e) (d : ι) (ℓ : T.Leaves) : count d T' (e ℓ) = count d T ℓ := by
  obtain ⟨-, -, -, hd⟩ := he ℓ
  rw [count_eq_draws_count, count_eq_draws_count, hd]

/-- A label-matching map preserves the Definition-6′ (shared-seed) law of every procedure.
Source: `fair-repair.md` FR-1(ii) (trembled procedures included: the law is a function of the
labels under either semantics)
Kind: L -/
theorem LeafMatch.leafLaw'_eq [DecidableEq ι] [∀ d, DecidableEq (acts d)]
    {T T' : Tree Ω ι acts K} {e : T.Leaves → T'.Leaves}
    (he : LeafMatch T T' e) (C : Proc ι acts K) (ℓ : T.Leaves) :
    leafLaw' C T' (e ℓ) = leafLaw' C T ℓ := by
  obtain ⟨-, -, hc, hd⟩ := he ℓ
  rw [Tree.leafLaw'_eq C T' (e ℓ), Tree.leafLaw'_eq C T ℓ, hc, hd]

end transport

end Cleanroom.Decision.DpFairnessReloc
