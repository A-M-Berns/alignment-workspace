import Cleanroom.Decision.DpFairnessReloc.Iso
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.SMulWithZero

/-!
# Subtrees, the continuation `(λ, r)`-law, and the three fairness grades

Package `dp-fairness-reloc`, file 2. Definitions of record:

* `subtreeAt B q`: the subtree rooted at the decision node `q`.
* `contLaw C T : Ω × K →₀ K`: the pushforward of `μ_{T,C}` along `ℓ ↦ (λ(ℓ), r(ℓ))` — the
  *continuation `(λ, r)`-law*, a finitely supported function (so that `V` and `ν` are literally
  linear functionals of it, `value_eq_contLaw_sum`, `nu_eq_contLaw_sum`).
* The fairness grades on a fiber `F_d = {q : d_q = d}` (`FairWrt E`, parametric in a relation
  `E` indexed by the point): **`StronglyFair`** (labelled-isomorphic subtrees, `≅`), **`LawFair`**
  (equal `contLaw` under every procedure), **`ValueFair`** (equal act values
  `Q(q, C, a) := V_{T_q}(C[d ↦ a])` under every procedure and action — GR-9's `D_V = 0`).
* `NestedFiber B d`: some `d`-node has a `d`-node strictly above it (`dp-core-tree`'s
  `IsMinimal` fails), and `Pruned B` (every path has positive chance weight).

Theorems: **FR-1(i)** — a strongly fair tree is almost fair, because `≅` preserves node count and
a proper subtree is strictly smaller (`StronglyFair.almostFair`); **T1(a)** — `AlmostFair B ↔ ¬ ∃ d,
NestedFiber B d`, with the positive-path form `Nested` related both ways; **T1(b)(ii)** — on
almost-fair trees `𝔼_μ[#_d 1_X] = μ(occ d ∩ {λ ⊨ X})` and `𝔼_μ[#_d] = μ(occ d)` literally.
Every hypothesis in this file is grade (a).
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-! ### Subtrees at decision nodes -/

/-- The subtree rooted at the decision node `q` (`T_q` of `equiv.md`, "the subtree at `q` read
as a problem").
Source: `equiv.md` Definitions carried (`T_q`); `fair-repair.md` §0 (fiber members' subtrees)
Kind: D -/
def subtreeAt : (B : Tree Ω ι acts K) → B.DecNode → Tree Ω ι acts K
  | .leaf _ _, q => q.elim
  | .chance _ _ child, ⟨i, q⟩ => subtreeAt (child i) q
  | .decision d child, none => .decision d child
  | .decision _ child, some ⟨a, q⟩ => subtreeAt (child a) q

@[simp] theorem subtreeAt_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (i : Fin n) (q : (child i).DecNode) :
    subtreeAt (.chance n β child) ⟨i, q⟩ = subtreeAt (child i) q := rfl

@[simp] theorem subtreeAt_decision_none (d : ι) (child : acts d → Tree Ω ι acts K) :
    subtreeAt (.decision d child) none = .decision d child := rfl

@[simp] theorem subtreeAt_decision_some (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d)
    (q : (child a).DecNode) : subtreeAt (.decision d child) (some ⟨a, q⟩) = subtreeAt (child a) q :=
  rfl

/-- The subtree at `q` is a decision node carrying `d_q`.
Source: none: infrastructure
Kind: L -/
theorem subtreeAt_eq_decision : (B : Tree Ω ι acts K) → ∀ q : B.DecNode,
    ∃ child : acts (pt B q) → Tree Ω ι acts K, subtreeAt B q = .decision (pt B q) child
  | .leaf _ _, q => q.elim
  | .chance _ _ child, ⟨i, q⟩ => subtreeAt_eq_decision (child i) q
  | .decision _ child, none => ⟨child, rfl⟩
  | .decision _ child, some ⟨a, q⟩ => subtreeAt_eq_decision (child a) q

section size

variable [∀ d, Fintype (acts d)]

/-- A subtree is no larger than the tree.
Source: none: infrastructure
Kind: L -/
theorem size_subtreeAt_le : (B : Tree Ω ι acts K) → ∀ q : B.DecNode, size (subtreeAt B q) ≤ size B
  | .leaf _ _, q => q.elim
  | .chance _ β child, ⟨i, q⟩ =>
      (size_subtreeAt_le (child i) q).trans (size_child_lt_chance β child i).le
  | .decision _ _, none => le_rfl
  | .decision d child, some ⟨a, q⟩ =>
      (size_subtreeAt_le (child a) q).trans (size_child_lt_decision d child a).le

end size

/-! ### The continuation `(λ, r)`-law -/

section law

variable [∀ d, Fintype (acts d)]

/-- **The continuation `(λ, r)`-law** `contLaw C T`: the pushforward of the Definition-6 run law
`μ_{T,C}` along `ℓ ↦ (λ(ℓ), r(ℓ))`, as a finitely supported function on `Ω × K`.
Source: `fair-repair.md` FR-1(ii) ("the downtree leaf-law conditional on reaching `q`" read at
the `(λ, r)` level, `θ_d`); `equiv.md` Definitions carried (`≈_law`: "equal `T̂(C)`");
`grounding.md` GR-9 ("continuation `(λ,r)`-laws")
Kind: D
Fidelity: exact (Definition 6 semantics; the leaf law itself is `leafLaw`) -/
noncomputable def contLaw (C : Proc ι acts K) (T : Tree Ω ι acts K) : Ω × K →₀ K :=
  ∑ ℓ, Finsupp.single (world T ℓ, payoff T ℓ) (leafLaw C T ℓ)

variable (C : Proc ι acts K)

@[simp] theorem contLaw_leaf (ω : Ω) (r : K) :
    contLaw C (.leaf ω r : Tree Ω ι acts K) = Finsupp.single (ω, r) 1 := by
  unfold contLaw
  show ∑ _ : Unit, Finsupp.single (ω, r) (1 : K) = _
  simp

theorem contLaw_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K) :
    contLaw C (.chance n β child) = ∑ i, β.w i • contLaw C (child i) := by
  unfold contLaw
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp [Finsupp.smul_single]

theorem contLaw_decision (d : ι) (child : acts d → Tree Ω ι acts K) :
    contLaw C (.decision d child) = ∑ a, (C d).w a • contLaw C (child a) := by
  unfold contLaw
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp [Finsupp.smul_single]

/-- The mass of the pair `(ω, r)` under the continuation law.
Source: none: infrastructure
Kind: L -/
theorem contLaw_apply [DecidableEq Ω] (T : Tree Ω ι acts K) (p : Ω × K) :
    contLaw C T p = ∑ ℓ, if (world T ℓ, payoff T ℓ) = p then leafLaw C T ℓ else 0 := by
  unfold contLaw
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun ℓ _ => Finsupp.single_apply

/-- **Every "expectation of a function of `(λ, r)`" is a linear functional of the continuation
law**: `∑_ℓ μ(ℓ) g(λ(ℓ), r(ℓ)) = ∑_{(ω,r)} contLaw(ω,r) g(ω,r)`.
Source: mandate §3 ("`value` is a functional of `contLaw`")
Kind: P -/
theorem sum_leafLaw_mul_eq_contLaw_sum (T : Tree Ω ι acts K) (g : Ω × K → K) :
    ∑ ℓ, leafLaw C T ℓ * g (world T ℓ, payoff T ℓ) =
      (contLaw C T).sum fun p v => v * g p := by
  unfold contLaw
  rw [← Finsupp.sum_finsetSum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finsupp.sum_single_index (zero_mul _)]

/-- `V_T(C)` is the integral of the payoff against the continuation law.
Source: mandate §3 ("`value` is a functional of `contLaw`")
Kind: L -/
theorem value_eq_contLaw_sum (T : Tree Ω ι acts K) :
    value C T = (contLaw C T).sum fun p v => v * p.2 :=
  sum_leafLaw_mul_eq_contLaw_sum C T Prod.snd

/-- `ν_{T,C}(X)` is the mass the continuation law puts on `X × K`.
Source: mandate §3
Kind: L -/
theorem nu_eq_contLaw_sum [DecidableEq Ω] (T : Tree Ω ι acts K) (X : Finset Ω) :
    nu C T X = (contLaw C T).sum fun p v => v * (if p.1 ∈ X then 1 else 0) := by
  rw [← sum_leafLaw_mul_eq_contLaw_sum]
  unfold nu mass worldEv
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun ℓ _ => by split_ifs <;> simp

/-- Equal continuation laws give equal values.
Source: none: infrastructure
Kind: L -/
theorem value_eq_of_contLaw_eq {T T' : Tree Ω ι acts K} (h : contLaw C T = contLaw C T') :
    value C T = value C T' := by
  rw [value_eq_contLaw_sum, value_eq_contLaw_sum, h]

/-- Equal continuation laws give equal statistics `ν`.
Source: none: infrastructure
Kind: L -/
theorem nu_eq_of_contLaw_eq [DecidableEq Ω] {T T' : Tree Ω ι acts K}
    (h : contLaw C T = contLaw C T') (X : Finset Ω) : nu C T X = nu C T' X := by
  rw [nu_eq_contLaw_sum, nu_eq_contLaw_sum, h]

/-- **Isomorphic trees have the same continuation law under every procedure** (transport
along the leaf bijection).
Source: `fair-repair.md` FR-1(ii); `v2-amendments.md` A34 ("equivalent subtrees ⟹ equal
continuation `(λ,r)`-laws under every procedure")
Kind: P
Fidelity: exact -/
theorem LabIso.contLaw_eq {T T' : Tree Ω ι acts K} (h : LabIso T T') :
    contLaw C T = contLaw C T' := by
  obtain ⟨e, he⟩ := h.exists_leafEquiv
  unfold contLaw
  refine Fintype.sum_equiv e _ _ fun ℓ => ?_
  obtain ⟨hw, hp, -, -⟩ := he ℓ
  rw [hw, hp, he.leafLaw_eq C ℓ]

end law

/-! ### The fairness grades -/

section fair

variable [DecidableEq ι] [∀ d, Fintype (acts d)]

/-- `Fair_E`: every fiber is pairwise `E`-related (`E` may read the point).
Source: `equiv.md` Definitions carried ("`Fair_E(B)`: every fiber pairwise `E`-related")
Kind: D -/
def FairWrt (E : ι → Tree Ω ι acts K → Tree Ω ι acts K → Prop) (B : Tree Ω ι acts K) : Prop :=
  ∀ d, ∀ q ∈ fiber B d, ∀ q' ∈ fiber B d, E d (subtreeAt B q) (subtreeAt B q')


/-- **Strong (structural) fairness**, grade 1 of GR-9: for every queried `d`, all members of the
fiber `F_d` have labelled-isomorphic subtrees (`Fair_≅`; Definition 25's first candidate).
Source: `fair-repair.md` §0; `fable-slop-notes.md` §1; `v2-amendments.md` A34 Definition 25
Kind: D
Fidelity: exact -/
def StronglyFair (B : Tree Ω ι acts K) : Prop := FairWrt (fun _ => LabIso) B

/-- **Law-fairness**, grade 2 of GR-9: all members of every fiber have the same continuation
`(λ, r)`-law under every procedure (`Fair_{≈law}`).
Source: `grounding.md` GR-9 ("law-fair"); `equiv.md` EQ-5 (`Fair_{≈law}`)
Kind: D
Fidelity: exact -/
def LawFair (B : Tree Ω ι acts K) : Prop :=
  FairWrt (fun _ T T' => ∀ C : Proc ι acts K, contLaw C T = contLaw C T') B

/-- **Value-fairness**, grade 3 of GR-9: all members of every fiber have the same act values
`Q(q, C, a) := V_{T_q}(C[d ↦ a])` under every procedure and every action (GR-9's `D_V = 0`).
Source: `grounding.md` GR-9 ("value-fair"; `D_V = 0`)
Kind: D
Fidelity: exact -/
def ValueFair [∀ d, DecidableEq (acts d)] (B : Tree Ω ι acts K) : Prop :=
  FairWrt (fun d T T' => ∀ (C : Proc ι acts K) (a : acts d),
    value (C.deviatePure d a) T = value (C.deviatePure d a) T') B

/-- Membership in a fiber.
Source: none: infrastructure
Kind: L -/
@[simp] theorem mem_fiber (B : Tree Ω ι acts K) (d : ι) (q : B.DecNode) :
    q ∈ fiber B d ↔ pt B q = d := by simp [fiber]

/-- Strong fairness passes to the children of a chance node.
Source: none: infrastructure
Kind: L -/
theorem StronglyFair.chance_child {n : ℕ} {β : FinDistr K (Fin n)}
    {child : Fin n → Tree Ω ι acts K} (h : StronglyFair (.chance n β child)) (i : Fin n) :
    StronglyFair (child i) := by
  intro d q hq q' hq'
  have := h d ⟨i, q⟩ (by simpa using hq) ⟨i, q'⟩ (by simpa using hq')
  simpa using this

/-- Strong fairness passes to the children of a decision node.
Source: none: infrastructure
Kind: L -/
theorem StronglyFair.decision_child {d : ι} {child : acts d → Tree Ω ι acts K}
    (h : StronglyFair (.decision d child)) (a : acts d) : StronglyFair (child a) := by
  intro e q hq q' hq'
  have := h e (some ⟨a, q⟩) (by simpa using hq) (some ⟨a, q'⟩) (by simpa using hq')
  simpa using this

/-- **FR-1(i): a strongly fair tree is almost fair.** If a path met `d` twice, the upper
`d`-node's subtree would be isomorphic to the lower one's, a proper subtree of it — but `≅`
preserves node count and a proper subtree is strictly smaller.
Source: `fair-repair.md` FR-1(i) ("a proper subtree of a finite tree is not isomorphic to the
whole"); `fable-slop-notes.md` Claim 1.2 ("nested nodes cannot have isomorphic finite subtrees")
Kind: P
Fidelity: exact (grade: strong fairness `≅`; conclusion is `dp-core-tree`'s `AlmostFair`, i.e.
`#_d ≤ 1` on every path, zero-weight paths included)
Hyps: none -/
theorem StronglyFair.almostFair [∀ d, DecidableEq (acts d)] :
    (B : Tree Ω ι acts K) → StronglyFair B → AlmostFair B
  | .leaf _ _, _ => fun _ _ => by simp
  | .chance _ β child, h => by
      rintro d ⟨i, ℓ⟩
      simpa using StronglyFair.almostFair (child i) (h.chance_child i) d ℓ
  | .decision d' child, h => by
      rintro d ⟨a, ℓ⟩
      have ih := StronglyFair.almostFair (child a) (h.decision_child a) d ℓ
      rw [count_decision]
      by_cases hd : d' = d
      · subst hd
        simp only [if_true]
        suffices hz : count d' (child a) ℓ = 0 by omega
        by_contra hne
        obtain ⟨q, hq, -⟩ := exists_dNode_of_count_pos d' (child a) ℓ (Nat.pos_of_ne_zero hne)
        have hiso := h d' none (by simp) (some ⟨a, q⟩) (by simpa using hq)
        have hsize := hiso.size_eq
        rw [subtreeAt_decision_none, subtreeAt_decision_some] at hsize
        have h1 := size_subtreeAt_le (child a) q
        have h2 := size_child_lt_decision d' child a
        omega
      · simp only [hd, if_false, zero_add]; exact ih

/-- Strongly fair trees are nested at no point (FR-1(i) in `dp-core-tree`'s positive-path
vocabulary).
Source: `fair-repair.md` FR-1(i)
Kind: C -/
theorem StronglyFair.not_nested [∀ d, DecidableEq (acts d)] {B : Tree Ω ι acts K}
    (h : StronglyFair B) (d : ι) :
    ¬ Nested B d :=
  (h.almostFair).not_nested d

/-! ### Nested fibers and T1 -/

/-- **A nested fiber**: some `d`-node has a `d`-node strictly above it (it is not `IsMinimal`) —
equivalently some member of `F_d` is a proper ancestor of another.
Source: `fair-repair.md` §0 ("`F_d` is nested (self-succession) if some member is a proper
ancestor of another"); `equiv.md` Definitions carried; A33 Definition 24
Kind: D
Fidelity: exact (ancestry read off `dp-core-tree`'s `ancestorPts`) -/
def NestedFiber (B : Tree Ω ι acts K) (d : ι) : Prop := ∃ q ∈ fiber B d, ¬ IsMinimal B q

/-- Every path has positive chance weight (zero-probability chance edges deleted).
Source: `equiv.md` Definitions carried ("*pruned* = zero-probability chance edges deleted")
Kind: D -/
def Pruned (B : Tree Ω ι acts K) : Prop := ∀ ℓ, Positive B ℓ

variable [∀ d, DecidableEq (acts d)]

omit [DecidableEq ι] in
/-- Every decision node has a leaf below it.
Source: none: infrastructure
Kind: L -/
theorem exists_leaf_below [∀ d, Nonempty (acts d)] :
    (B : Tree Ω ι acts K) → ∀ q : B.DecNode, ∃ ℓ, (edgeOf B q ℓ).isSome
  | .leaf _ _, q => q.elim
  | .chance _ _ child, ⟨i, q⟩ => by
      obtain ⟨ℓ, hℓ⟩ := exists_leaf_below (child i) q
      exact ⟨⟨i, ℓ⟩, by rw [edgeOf_chance, dif_pos rfl]; exact hℓ⟩
  | .decision d child, none => by
      have ⟨a⟩ := (inferInstance : Nonempty (acts d))
      have ⟨ℓ⟩ := leaves_nonempty (child a)
      exact ⟨⟨a, ℓ⟩, by simp⟩
  | .decision _ child, some ⟨a, q⟩ => by
      obtain ⟨ℓ, hℓ⟩ := exists_leaf_below (child a) q
      exact ⟨⟨a, ℓ⟩, by rw [edgeOf_decision_some, dif_pos rfl]; exact hℓ⟩

/-- On a path through `q`, `#_d` counts at least the `d`-ancestors of `q` plus `q` itself.
Source: none: infrastructure
Kind: L -/
theorem count_ge_of_edge (d : ι) :
    (B : Tree Ω ι acts K) → ∀ (q : B.DecNode) (ℓ : B.Leaves), (edgeOf B q ℓ).isSome →
      (ancestorPts B q).count d + (if pt B q = d then 1 else 0) ≤ count d B ℓ
  | .leaf _ _, q, _, _ => q.elim
  | .chance _ β child, ⟨i, q⟩, ⟨j, ℓ⟩, h => by
      by_cases hji : j = i
      · subst hji
        rw [edgeOf_chance, dif_pos rfl] at h
        exact count_ge_of_edge d (child j) q ℓ h
      · simp [edgeOf_chance, hji] at h
  | .decision d' child, none, ⟨a, ℓ⟩, _ => by
      simp only [ancestorPts_decision_none, List.count_nil, pt_decision_none, count_decision,
        zero_add]
      split_ifs <;> omega
  | .decision d' child, some ⟨a, q⟩, ⟨b, ℓ⟩, h => by
      by_cases hba : b = a
      · subst hba
        rw [edgeOf_decision_some, dif_pos rfl] at h
        have := count_ge_of_edge d (child b) q ℓ h
        simp only [ancestorPts_decision_some, pt_decision_some, count_decision, List.count_cons]
        split_ifs with h1 h2 <;> simp_all <;> omega
      · simp [edgeOf_decision_some, hba] at h

/-- A path meeting `d` twice passes a non-minimal `d`-node.
Source: none: infrastructure
Kind: L -/
theorem exists_nonMinimal_of_two_le (d : ι) :
    (B : Tree Ω ι acts K) → ∀ ℓ, 2 ≤ count d B ℓ → ∃ q ∈ fiber B d, ¬ IsMinimal B q
  | .leaf _ _, _, h => by simp at h
  | .chance _ β child, ⟨i, ℓ⟩, h => by
      obtain ⟨q, hq, hmin⟩ := exists_nonMinimal_of_two_le d (child i) ℓ (by simpa using h)
      refine ⟨⟨i, q⟩, by simpa using hq, ?_⟩
      simpa [IsMinimal] using hmin
  | .decision d' child, ⟨a, ℓ⟩, h => by
      rw [count_decision] at h
      by_cases hd : d' = d
      · subst hd
        simp only [if_true] at h
        obtain ⟨q, hq, -⟩ := exists_dNode_of_count_pos d' (child a) ℓ (by omega)
        refine ⟨some ⟨a, q⟩, by simpa using hq, ?_⟩
        simp [IsMinimal, hq]
      · simp only [hd, if_false, zero_add] at h
        obtain ⟨q, hq, hmin⟩ := exists_nonMinimal_of_two_le d (child a) ℓ h
        refine ⟨some ⟨a, q⟩, by simpa using hq, ?_⟩
        simp only [mem_fiber] at hq
        simp only [IsMinimal, pt_decision_some, ancestorPts_decision_some, List.mem_cons,
          not_or, not_and, Classical.not_not] at hmin ⊢
        intro; exact hmin

/-- **T1(a): Definition 24's two readings agree** — no path meets a point twice iff no fiber is
nested.
Source: `v2-amendments.md` A33 Definition 24 ("no root-to-leaf path contains two decision nodes
carrying the same point — equivalently `#_d ≤ 1` identically"); `fair-repair.md` Definition
(almost fair) ("no fiber of `B` is nested — equivalently every point is consulted at most once
per run")
Kind: P
Fidelity: exact
Hyps: none (`[∀ d, Nonempty (acts d)]` is Definition 3's non-emptiness of `A_d`) -/
theorem almostFair_iff_not_nestedFiber [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K) :
    AlmostFair B ↔ ¬ ∃ d, NestedFiber B d := by
  constructor
  · rintro h ⟨d, q, hq, hmin⟩
    obtain ⟨ℓ, hℓ⟩ := exists_leaf_below B q
    have := count_ge_of_edge d B q ℓ hℓ
    rw [mem_fiber] at hq
    simp only [IsMinimal, Classical.not_not] at hmin
    rw [hq] at hmin this
    simp only [if_true] at this
    have hc := List.count_pos_iff.mpr hmin
    have := h d ℓ
    omega
  · intro h d ℓ
    by_contra hlt
    exact h ⟨d, exists_nonMinimal_of_two_le d B ℓ (by omega)⟩

/-- A positively-nested point (`dp-core-tree`'s `Nested`) has a nested fiber, unconditionally.
Source: A33 Definition 24 ("… and only on almost-fair problems, once zero-probability chance
edges are pruned and single-action points are ignored")
Kind: L -/
theorem NestedFiber.of_nested {B : Tree Ω ι acts K} {d : ι} (h : Nested B d) : NestedFiber B d := by
  obtain ⟨-, ℓ, -, h2⟩ := h
  exact exists_nonMinimal_of_two_le d B ℓ h2

/-- On a pruned tree, a nested fiber at a point with at least two actions is positively nested:
the three notions agree once zero edges are pruned and single-action points ignored.
Source: A33 Definition 24 (the pruned equivalence)
Kind: P -/
theorem NestedFiber.nested_of_pruned [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K} {d : ι}
    (hp : Pruned B) (h2 : 2 ≤ Fintype.card (acts d)) (h : NestedFiber B d) : Nested B d := by
  obtain ⟨q, hq, hmin⟩ := h
  obtain ⟨ℓ, hℓ⟩ := exists_leaf_below B q
  refine ⟨h2, ℓ, hp ℓ, ?_⟩
  have := count_ge_of_edge d B q ℓ hℓ
  rw [mem_fiber] at hq
  simp only [IsMinimal, Classical.not_not] at hmin
  rw [hq] at hmin this
  simp only [if_true] at this
  have hc := List.count_pos_iff.mpr hmin
  omega

/-! ### T1(b)(ii): the two occurrence statistics are one equation on almost-fair trees -/

/-- `𝔼_μ[#_d · 1_X]`: the expected number of `d`-consultations on runs whose world satisfies
`X` — the numerator of Definition 13's per-occurrence statistic.
Source: [[decision-problems-v2]] Definition 13 (per-occurrence clause); `fair-repair.md` FR-1(i)
Kind: D -/
def expCountIn [DecidableEq Ω] (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (X : Finset Ω) :
    K :=
  ∑ ℓ, leafLaw C B ℓ * (count d B ℓ : K) * (if world B ℓ ∈ X then 1 else 0)

/-- `𝔼_μ[#_d]`.
Source: [[decision-problems-v2]] Definition 13
Kind: D -/
def expCount (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) : K :=
  ∑ ℓ, leafLaw C B ℓ * (count d B ℓ : K)

/-- **On almost-fair trees `𝔼_μ[#_d 1_X] = μ(occ(d) ∧ {λ ⊨ X})`**: the per-occurrence and
per-run numerators of Definition 13 are literally the same number.
Source: `fair-repair.md` FR-1(i) ("`𝔼_μ[#_d 1_{λ⊨X}] = μ(occ(d) ∧ {λ ⊨ X})` … when
`#_d ∈ {0,1}`"); A33 Definition 24
Kind: P
Fidelity: exact
Hyps: none -/
theorem AlmostFair.expCountIn_eq [DecidableEq Ω] {B : Tree Ω ι acts K} (h : AlmostFair B)
    (C : Proc ι acts K) (d : ι) (X : Finset Ω) :
    expCountIn C B d X = mass C B (worldEv B X ∩ occ d B) := by
  unfold expCountIn mass
  rw [← Finset.univ_inter (worldEv B X ∩ occ d B), ← Finset.sum_ite_mem]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have hc := h d ℓ
  simp only [Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and, mem_occ]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h0 | h1
  · simp [h0]
  · simp [h1]

omit [∀ d, DecidableEq (acts d)] in
/-- **On almost-fair trees `𝔼_μ[#_d] = μ(occ(d))`**.
Source: `fair-repair.md` FR-1(i) ("`𝔼_μ[#_d] = μ(occ(d))` when `#_d ∈ {0,1}`")
Kind: P
Fidelity: exact
Hyps: none -/
theorem AlmostFair.expCount_eq {B : Tree Ω ι acts K} (h : AlmostFair B) (C : Proc ι acts K)
    (d : ι) : expCount C B d = mass C B (occ d B) := by
  unfold expCount
  rw [mass_occ]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have hc := h d ℓ
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h0 | h1
  · simp [h0]
  · simp [h1]

end fair

end Cleanroom.Decision.DpFairnessReloc
