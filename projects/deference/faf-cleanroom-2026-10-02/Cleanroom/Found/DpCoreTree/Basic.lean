import Cleanroom.Found.DpCoreTree.Recording
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Basic lemmas: the run law is a probability; the path-product formula; queried-congruence

T1 of [[dp-core-tree-mandate]]: `∑_ℓ μ_{B,C}(ℓ) = 1`, `0 ≤ μ`, `ν` finitely additive with
`ν ⊤ = 1`, the path-product formula `μ(ℓ) = (∏ chance weights) · (∏ draw weights)`, and
`leafLaw_congr_queried` (`μ_{B,C} = μ_{B,C'}` when `C`, `C'` agree on `queried B`). Also the
leaf-sum decomposition lemmas through the recursive `Fintype` instance that every later file
uses, and the characterisation of `queried` by `#_d`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)]

namespace Tree

/-! ### Sums over leaves decompose along the constructors -/

section sums

variable {M : Type} [AddCommMonoid M]

/-- Summing over the leaves of a chance node is summing over children then leaves.
Source: none: infrastructure
Kind: L -/
theorem sum_leaves_chance {n : ℕ} {β : FinDistr K (Fin n)} {child : Fin n → Tree Ω ι acts K}
    (f : (chance n β child).Leaves → M) : ∑ ℓ, f ℓ = ∑ i, ∑ ℓ, f ⟨i, ℓ⟩ :=
  Fintype.sum_sigma _

/-- Summing over the leaves of a decision node is summing over actions then leaves.
Source: none: infrastructure
Kind: L -/
theorem sum_leaves_decision {d : ι} {child : acts d → Tree Ω ι acts K}
    (f : (decision d child).Leaves → M) : ∑ ℓ, f ℓ = ∑ a, ∑ ℓ, f ⟨a, ℓ⟩ :=
  Fintype.sum_sigma _

end sums

/-- A chance node's child index type is nonempty (its distribution sums to one).
Source: none: infrastructure
Kind: L -/
theorem FinDistr.nonempty_of_finDistr {α : Type} [Fintype α] (β : FinDistr K α) : Nonempty α := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := β.sum_one
  simp [Finset.univ_eq_empty] at this

/-- Every tree has a leaf.
Source: none: infrastructure
Kind: L -/
theorem leaves_nonempty [∀ d, Nonempty (acts d)] : (B : Tree Ω ι acts K) → Nonempty B.Leaves
  | leaf _ _ => ⟨()⟩
  | chance _ β child =>
      have ⟨i⟩ := FinDistr.nonempty_of_finDistr β
      have ⟨ℓ⟩ := leaves_nonempty (child i)
      ⟨⟨i, ℓ⟩⟩
  | decision d child =>
      have ⟨a⟩ := (inferInstance : Nonempty (acts d))
      have ⟨ℓ⟩ := leaves_nonempty (child a)
      ⟨⟨a, ℓ⟩⟩

/-! ### Equations for the recursive definitions (stated once, `rfl`) -/

section eqns

variable (C : Proc ι acts K)

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem leafLaw_leaf (ω : Ω) (r : K) (ℓ : (leaf ω r : Tree Ω ι acts K).Leaves) :
    leafLaw C (leaf ω r) ℓ = 1 := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem leafLaw_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (i : Fin n) (ℓ : (child i).Leaves) :
    leafLaw C (chance n β child) ⟨i, ℓ⟩ = β.w i * leafLaw C (child i) ℓ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem leafLaw_decision (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d)
    (ℓ : (child a).Leaves) :
    leafLaw C (decision d child) ⟨a, ℓ⟩ = (C d).w a * leafLaw C (child a) ℓ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem chanceWeight_leaf (ω : Ω) (r : K) (ℓ : (leaf ω r : Tree Ω ι acts K).Leaves) :
    chanceWeight (leaf ω r) ℓ = 1 := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem chanceWeight_chance {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (i : Fin n) (ℓ : (child i).Leaves) :
    chanceWeight (chance n β child) ⟨i, ℓ⟩ = β.w i * chanceWeight (child i) ℓ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem chanceWeight_decision (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d)
    (ℓ : (child a).Leaves) :
    chanceWeight (decision d child) ⟨a, ℓ⟩ = chanceWeight (child a) ℓ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem draws_leaf (ω : Ω) (r : K) (ℓ : (leaf ω r : Tree Ω ι acts K).Leaves) :
    draws (leaf ω r) ℓ = [] := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem draws_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (i : Fin n) (ℓ : (child i).Leaves) :
    draws (chance n β child) ⟨i, ℓ⟩ = draws (child i) ℓ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem draws_decision (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d)
    (ℓ : (child a).Leaves) :
    draws (decision d child) ⟨a, ℓ⟩ = ⟨d, a⟩ :: draws (child a) ℓ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem world_leaf (ω : Ω) (r : K) (ℓ : (leaf ω r : Tree Ω ι acts K).Leaves) :
    world (leaf ω r) ℓ = ω := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem world_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (i : Fin n) (ℓ : (child i).Leaves) :
    world (chance n β child) ⟨i, ℓ⟩ = world (child i) ℓ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem world_decision (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d)
    (ℓ : (child a).Leaves) :
    world (decision d child) ⟨a, ℓ⟩ = world (child a) ℓ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem payoff_leaf (ω : Ω) (r : K) (ℓ : (leaf ω r : Tree Ω ι acts K).Leaves) :
    payoff (leaf ω r) ℓ = r := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem payoff_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (i : Fin n) (ℓ : (child i).Leaves) :
    payoff (chance n β child) ⟨i, ℓ⟩ = payoff (child i) ℓ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem payoff_decision (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d)
    (ℓ : (child a).Leaves) :
    payoff (decision d child) ⟨a, ℓ⟩ = payoff (child a) ℓ := rfl

variable [DecidableEq ι]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem count_leaf (d : ι) (ω : Ω) (r : K) (ℓ : (leaf ω r : Tree Ω ι acts K).Leaves) :
    count d (leaf ω r) ℓ = 0 := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem count_chance (d : ι) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (i : Fin n) (ℓ : (child i).Leaves) :
    count d (chance n β child) ⟨i, ℓ⟩ = count d (child i) ℓ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem count_decision (d d' : ι) (child : acts d' → Tree Ω ι acts K) (a : acts d')
    (ℓ : (child a).Leaves) :
    count d (decision d' child) ⟨a, ℓ⟩ = (if d' = d then 1 else 0) + count d (child a) ℓ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem queried_leaf (ω : Ω) (r : K) : queried (leaf ω r : Tree Ω ι acts K) = ∅ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem queried_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K) :
    queried (chance n β child) = Finset.univ.biUnion fun i => queried (child i) := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem queried_decision (d : ι) (child : acts d → Tree Ω ι acts K) :
    queried (decision d child) = insert d (Finset.univ.biUnion fun a => queried (child a)) := rfl

end eqns

/-! ### The run law is a probability on the leaves -/

section law

variable (C : Proc ι acts K)

/-- `0 ≤ μ_{B,C}(ℓ)`.
Source: [[decision-problems-v2]] §3.1 Definition 6 (`μ_{B,C} ∈ Δ(Leaves(B))`)
Kind: L -/
theorem leafLaw_nonneg : (B : Tree Ω ι acts K) → ∀ ℓ, 0 ≤ leafLaw C B ℓ
  | leaf _ _, _ => zero_le_one
  | chance _ β child, ⟨i, ℓ⟩ =>
      mul_nonneg (β.nonneg i) (leafLaw_nonneg (child i) ℓ)
  | decision d child, ⟨a, ℓ⟩ =>
      mul_nonneg ((C d).nonneg a) (leafLaw_nonneg (child a) ℓ)

/-- **`∑_ℓ μ_{B,C}(ℓ) = 1`**: the run law is a probability on the leaves.
Source: [[decision-problems-v2]] §3.1 Definition 6 (`μ_{B,C} ∈ Δ(Leaves(B))`)
Kind: L -/
theorem sum_leafLaw : (B : Tree Ω ι acts K) → ∑ ℓ, leafLaw C B ℓ = 1
  | leaf _ _ => by
      show ∑ _ℓ : Unit, (1 : K) = 1
      simp
  | chance _ β child => by
      have ih : ∀ i, ∑ ℓ, leafLaw C (child i) ℓ = 1 := fun i => sum_leafLaw (child i)
      rw [sum_leaves_chance]
      simp only [leafLaw_chance, ← Finset.mul_sum, ih, mul_one]
      exact β.sum_one
  | decision d child => by
      have ih : ∀ a, ∑ ℓ, leafLaw C (child a) ℓ = 1 := fun a => sum_leafLaw (child a)
      rw [sum_leaves_decision]
      simp only [leafLaw_decision, ← Finset.mul_sum, ih, mul_one]
      exact (C d).sum_one

/-- `μ_{B,C}(ℓ) ≤ 1`.
Source: none: infrastructure
Kind: L -/
theorem leafLaw_le_one (B : Tree Ω ι acts K) (ℓ : B.Leaves) : leafLaw C B ℓ ≤ 1 := by
  rw [← sum_leafLaw C B]
  exact Finset.single_le_sum (fun ℓ' _ => leafLaw_nonneg C B ℓ') (Finset.mem_univ ℓ)

/-- `0 ≤ chanceWeight`.
Source: none: infrastructure
Kind: L -/
theorem chanceWeight_nonneg : (B : Tree Ω ι acts K) → ∀ ℓ, 0 ≤ chanceWeight B ℓ
  | leaf _ _, _ => zero_le_one
  | chance _ β child, ⟨i, ℓ⟩ => mul_nonneg (β.nonneg i) (chanceWeight_nonneg (child i) ℓ)
  | decision _ child, ⟨a, ℓ⟩ => chanceWeight_nonneg (child a) ℓ

/-- **The path-product formula**: the mass of a leaf is the product of the chance weights on
its path times the product of the draw weights `C(d_q)(a_q)` over the decision nodes on it.
Source: [[decision-problems-v2]] §3.1 Definition 6; mandate T1
Kind: P
Fidelity: exact -/
theorem leafLaw_eq_chanceWeight_mul_drawsWeight :
    (B : Tree Ω ι acts K) → ∀ ℓ, leafLaw C B ℓ = chanceWeight B ℓ * drawsWeight C B ℓ
  | leaf _ _, _ => by simp [drawsWeight]
  | chance _ β child, ⟨i, ℓ⟩ => by
      simp only [leafLaw_chance, chanceWeight_chance, drawsWeight, draws_chance]
      rw [leafLaw_eq_chanceWeight_mul_drawsWeight (child i) ℓ]
      simp only [drawsWeight]; ring
  | decision d child, ⟨a, ℓ⟩ => by
      simp only [leafLaw_decision, chanceWeight_decision, drawsWeight, draws_decision,
        List.map_cons, List.prod_cons]
      rw [leafLaw_eq_chanceWeight_mul_drawsWeight (child a) ℓ]
      simp only [drawsWeight]; ring

/-- The draw-weight product is non-negative.
Source: none: infrastructure
Kind: L -/
theorem drawsWeight_nonneg (B : Tree Ω ι acts K) (ℓ : B.Leaves) : 0 ≤ drawsWeight C B ℓ := by
  unfold drawsWeight
  apply List.prod_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact (C y.1).nonneg y.2

/-- A leaf of positive mass lies on a chance-positive path.
Source: none: infrastructure
Kind: L -/
theorem Positive.of_leafLaw_pos {B : Tree Ω ι acts K} {ℓ : B.Leaves} (h : 0 < leafLaw C B ℓ) :
    Positive B ℓ := by
  unfold Positive
  rw [leafLaw_eq_chanceWeight_mul_drawsWeight] at h
  rcases (chanceWeight_nonneg B ℓ).lt_or_eq with hlt | heq
  · exact hlt
  · rw [← heq, zero_mul] at h; exact absurd h (lt_irrefl 0)

end law

/-! ### Masses and the objective statistics -/

section mass

variable (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- `0 ≤ μ_{B,C}(S)`.
Source: none: infrastructure
Kind: L -/
theorem mass_nonneg (S : Finset B.Leaves) : 0 ≤ mass C B S :=
  Finset.sum_nonneg fun ℓ _ => leafLaw_nonneg C B ℓ

/-- `μ_{B,C}(Leaves) = 1`.
Source: [[decision-problems-v2]] §3.1 Definition 6
Kind: L -/
theorem mass_univ : mass C B Finset.univ = 1 := sum_leafLaw C B

/-- Finite additivity of `μ_{B,C}` on disjoint leaf sets.
Source: [[decision-problems-v2]] §3.1 Definition 6
Kind: L -/
theorem mass_union [∀ d, DecidableEq (acts d)] {S T : Finset B.Leaves} (h : Disjoint S T) :
    mass C B (S ∪ T) = mass C B S + mass C B T :=
  Finset.sum_union h

/-- Monotonicity of `μ_{B,C}`.
Source: none: infrastructure
Kind: L -/
theorem mass_mono {S T : Finset B.Leaves} (h : S ⊆ T) : mass C B S ≤ mass C B T :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun ℓ _ _ => leafLaw_nonneg C B ℓ

/-- `μ_{B,C}(S) ≤ 1`.
Source: none: infrastructure
Kind: L -/
theorem mass_le_one (S : Finset B.Leaves) : mass C B S ≤ 1 := by
  rw [← mass_univ C B]; exact mass_mono C B (Finset.subset_univ S)

/-- Mass of a filtered set as a sum with an indicator.
Source: none: infrastructure
Kind: L -/
theorem mass_filter (P : B.Leaves → Prop) [DecidablePred P] :
    mass C B (Finset.univ.filter P) = ∑ ℓ, if P ℓ then leafLaw C B ℓ else 0 := by
  unfold mass; rw [Finset.sum_filter]

variable [DecidableEq Ω]

/-- `ν_{B,C}(⊤) = 1`.
Source: [[decision-problems-v2]] §3.1 Definition 6 (`ν_{B,C} ∈ Δ(𝓐)`)
Kind: L -/
theorem nu_univ [Fintype Ω] : nu C B Finset.univ = 1 := by
  unfold nu worldEv
  simp only [Finset.mem_univ, Finset.filter_true_of_mem, implies_true]
  exact mass_univ C B

/-- `0 ≤ ν_{B,C}(X)`.
Source: none: infrastructure
Kind: L -/
theorem nu_nonneg (X : Finset Ω) : 0 ≤ nu C B X := mass_nonneg C B _

/-- `ν_{B,C}(X) ≤ 1`.
Source: none: infrastructure
Kind: L -/
theorem nu_le_one (X : Finset Ω) : nu C B X ≤ 1 := mass_le_one C B _

/-- `ν_{B,C}` is finitely additive on disjoint events.
Source: [[decision-problems-v2]] §3.1 Definition 6 ("a probability on `𝓐`")
Kind: L -/
theorem nu_union [∀ d, DecidableEq (acts d)] {X Y : Finset Ω} (h : Disjoint X Y) :
    nu C B (X ∪ Y) = nu C B X + nu C B Y := by
  unfold nu
  have : worldEv B (X ∪ Y) = worldEv B X ∪ worldEv B Y := by
    ext ℓ; simp [worldEv, Finset.mem_union]
  rw [this, mass_union]
  rw [Finset.disjoint_left]
  intro ℓ hX hY
  simp only [worldEv, Finset.mem_filter, Finset.mem_univ, true_and] at hX hY
  exact Finset.disjoint_left.mp h hX hY

/-- `ν` as a sum over leaves with an indicator.
Source: none: infrastructure
Kind: L -/
theorem nu_eq_sum (X : Finset Ω) :
    nu C B X = ∑ ℓ, if world B ℓ ∈ X then leafLaw C B ℓ else 0 := by
  unfold nu worldEv; exact mass_filter C B _

/-- `ν` of the empty event is zero.
Source: none: infrastructure
Kind: L -/
@[simp] theorem nu_empty : nu C B ∅ = 0 := by simp [nu_eq_sum]

/-- Monotonicity of `ν`.
Source: none: infrastructure
Kind: L -/
theorem nu_mono {X Y : Finset Ω} (h : X ⊆ Y) : nu C B X ≤ nu C B Y := by
  unfold nu; apply mass_mono
  intro ℓ; simp only [worldEv, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun hx => h hx

end mass

/-! ### Congruence on the queried points -/

section queried

variable [DecidableEq ι]

/-- The points queried in a child of a chance node are queried in the node.
Source: none: infrastructure
Kind: L -/
theorem queried_child_subset_chance {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (i : Fin n) :
    queried (child i) ⊆ queried (chance n β child) := by
  simp only [queried_chance]
  exact Finset.subset_biUnion_of_mem (fun i => queried (child i)) (Finset.mem_univ i)

/-- The points queried in a child of a decision node are queried in the node.
Source: none: infrastructure
Kind: L -/
theorem queried_child_subset_decision (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d) :
    queried (child a) ⊆ queried (decision d child) := by
  simp only [queried_decision]
  exact (Finset.subset_biUnion_of_mem (fun a => queried (child a)) (Finset.mem_univ a)).trans
    (Finset.subset_insert _ _)

/-- The point of a decision node is queried.
Source: none: infrastructure
Kind: L -/
theorem mem_queried_decision (d : ι) (child : acts d → Tree Ω ι acts K) :
    d ∈ queried (decision d child) := by
  simp only [queried_decision]; exact Finset.mem_insert_self _ _

/-- **`leafLaw_congr_queried`**: procedures agreeing on the queried points induce the same
run law.
Source: [[decision-problems-v2]] §3.1 (the extensional shadow: "no run touching finitely many
points"); mandate T1
Kind: P -/
theorem leafLaw_congr_queried {C C' : Proc ι acts K} :
    (B : Tree Ω ι acts K) → (∀ d ∈ queried B, C d = C' d) → ∀ ℓ, leafLaw C B ℓ = leafLaw C' B ℓ
  | leaf _ _, _, _ => rfl
  | chance _ β child, h, ⟨i, ℓ⟩ => by
      simp only [leafLaw_chance]
      rw [leafLaw_congr_queried (child i)
        (fun d hd => h d (queried_child_subset_chance β child i hd)) ℓ]
  | decision d child, h, ⟨a, ℓ⟩ => by
      simp only [leafLaw_decision]
      rw [h d (mem_queried_decision d child),
        leafLaw_congr_queried (child a)
          (fun d' hd => h d' (queried_child_subset_decision d child a hd)) ℓ]

/-- `ν` is a function of `C` on the queried points only.
Source: mandate T1
Kind: L -/
theorem nu_congr_queried [DecidableEq Ω] {C C' : Proc ι acts K} (B : Tree Ω ι acts K)
    (h : ∀ d ∈ queried B, C d = C' d) (X : Finset Ω) : nu C B X = nu C' B X := by
  simp only [nu_eq_sum]
  exact Finset.sum_congr rfl fun ℓ _ => by rw [leafLaw_congr_queried B h ℓ]

/-- `V_B` is a function of `C` on the queried points only.
Source: mandate T1
Kind: L -/
theorem value_congr_queried {C C' : Proc ι acts K} (B : Tree Ω ι acts K)
    (h : ∀ d ∈ queried B, C d = C' d) : value C B = value C' B := by
  unfold value
  exact Finset.sum_congr rfl fun ℓ _ => by rw [leafLaw_congr_queried B h ℓ]

/-- A point is queried iff some leaf's path meets a node carrying it.
Source: [[decision-problems-v2]] §3.1 Definition 5 ("queried if some node carries it")
Kind: L -/
theorem mem_queried_iff [∀ d, Nonempty (acts d)] (d : ι) :
    (B : Tree Ω ι acts K) → (d ∈ queried B ↔ ∃ ℓ, 0 < count d B ℓ)
  | leaf _ _ => by simp
  | chance _ β child => by
      simp only [queried_chance, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi⟩
        obtain ⟨ℓ, hℓ⟩ := (mem_queried_iff d (child i)).mp hi
        exact ⟨⟨i, ℓ⟩, by simpa using hℓ⟩
      · rintro ⟨⟨i, ℓ⟩, hℓ⟩
        exact ⟨i, (mem_queried_iff d (child i)).mpr ⟨ℓ, by simpa using hℓ⟩⟩
  | decision d' child => by
      simp only [queried_decision, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
        true_and]
      constructor
      · rintro (rfl | ⟨a, ha⟩)
        · have ⟨a⟩ := (inferInstance : Nonempty (acts d))
          have ⟨ℓ⟩ := leaves_nonempty (child a)
          exact ⟨⟨a, ℓ⟩, by simp⟩
        · obtain ⟨ℓ, hℓ⟩ := (mem_queried_iff d (child a)).mp ha
          exact ⟨⟨a, ℓ⟩, by simp only [count_decision]; omega⟩
      · rintro ⟨⟨a, ℓ⟩, hℓ⟩
        simp only [count_decision] at hℓ
        by_cases h : d' = d
        · exact Or.inl h.symm
        · simp only [h, if_false, zero_add] at hℓ
          exact Or.inr ⟨a, (mem_queried_iff d (child a)).mpr ⟨ℓ, hℓ⟩⟩

/-- An unqueried point is met on no path.
Source: none: infrastructure
Kind: L -/
theorem count_eq_zero_of_not_queried [∀ d, Nonempty (acts d)] {d : ι} {B : Tree Ω ι acts K}
    (h : d ∉ queried B) (ℓ : B.Leaves) : count d B ℓ = 0 := by
  by_contra h'
  exact h ((mem_queried_iff d B).mpr ⟨ℓ, Nat.pos_of_ne_zero h'⟩)

/-- Membership in `occ(d)`.
Source: [[decision-problems-v2]] §3.1 Definition 6
Kind: L -/
@[simp] theorem mem_occ (d : ι) (B : Tree Ω ι acts K) (ℓ : B.Leaves) :
    ℓ ∈ occ d B ↔ 0 < count d B ℓ := by
  simp [occ]

/-- Almost-fair trees are nested at no point.
Source: `seeds.md` SE-2 Corollary
Kind: L -/
theorem AlmostFair.not_nested {B : Tree Ω ι acts K} (h : AlmostFair B) (d : ι) : ¬ Nested B d := by
  rintro ⟨-, ℓ, -, h2⟩
  have := h d ℓ
  omega

end queried

end Tree

end Cleanroom.Found.DpCoreTree
