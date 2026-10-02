import Cleanroom.Decision.DpFairnessReloc.Fair

/-!
# The grade implications and the anthropic fork (T2(a), T3(a)–(b))

Package `dp-fairness-reloc`, file 3.

* **T2(a)**: `StronglyFair → LawFair → ValueFair` (`≅` transports `contLaw`; `V` is a functional
  of `contLaw`).
* **Lemma 1's decompositions**, proved for every tree with no fairness hypothesis: for every
  `g : Ω × K → K`, the `occ(d)`-restricted expectation `∑_{ℓ ∈ occ d} μ(ℓ) g(λ(ℓ), r(ℓ))` is
  `∑_{q minimal d-node} R_q · ∫ g dμ_{T_q}` (`occ_decomposition`), and the `#_d`-weighted one
  `∑_ℓ μ(ℓ) #_d(ℓ) g(…)` is `∑_{q ∈ F_d} R_q · ∫ g dμ_{T_q}` (`count_decomposition`).
* **EQ-5 / L3 / Claim 1.1 (fork closure)**: on a law-fair tree the continuation law
  `θ_q(C) := contLaw C (T_q)` is fiber-constant, and both Definition-13 statistics reduce to
  it: `μ(occ d ∧ {λ ⊨ X}) = (∑_{q minimal} R_q) · θ_d(C)(X)` with `μ(occ d) = ∑_{q minimal} R_q`,
  and `𝔼_μ[#_d 1_X] = (∑_{q ∈ F_d} R_q) · θ_d(C)(X)` with `𝔼_μ[#_d] = ∑_{q ∈ F_d} R_q`.
  Scope: **law-fair** (law-spurious nesting allowed), **Definition 6**, every procedure
  (trembled procedures included since it is for every `C`). Strong fairness is not assumed; its
  form is a one-line corollary.
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

variable [∀ d, Fintype (acts d)]

/-! ### T2(a): the grade implications -/

/-- **Strongly fair ⟹ law-fair**: isomorphic subtrees have the same continuation law under
every procedure.
Source: `grounding.md` GR-9 ("Labelled-isomorphic ⟹ law-fair"); `fair-repair.md` FR-1(ii)
Kind: P
Fidelity: exact
Hyps: none -/
theorem StronglyFair.lawFair [DecidableEq ι] {B : Tree Ω ι acts K} (h : StronglyFair B) :
    LawFair B :=
  fun d q hq q' hq' C => (h d q hq q' hq').contLaw_eq C

/-- **Law-fair ⟹ value-fair**: the act value is a functional of the continuation law.
Source: `grounding.md` GR-9 ("law-fair ⟹ value-fair")
Kind: P
Fidelity: exact
Hyps: none -/
theorem LawFair.valueFair [DecidableEq ι] [∀ d, DecidableEq (acts d)] {B : Tree Ω ι acts K}
    (h : LawFair B) :
    ValueFair B :=
  fun d q hq q' hq' C a => value_eq_of_contLaw_eq _ (h d q hq q' hq' (C.deviatePure d a))

/-! ### Lemma 1's decompositions over minimal / all `d`-nodes -/

/-- `∫ g dμ_{T,C}` for `g` a function of `(λ, r)`: the expectation of `g(λ(ℓ), r(ℓ))`.
Source: none: infrastructure (the functional of `sum_leafLaw_mul_eq_contLaw_sum`)
Kind: D -/
def lawInt (C : Proc ι acts K) (T : Tree Ω ι acts K) (g : Ω × K → K) : K :=
  ∑ ℓ, leafLaw C T ℓ * g (world T ℓ, payoff T ℓ)

theorem lawInt_eq_contLaw_sum (C : Proc ι acts K) (T : Tree Ω ι acts K) (g : Ω × K → K) :
    lawInt C T g = (contLaw C T).sum fun p v => v * g p :=
  sum_leafLaw_mul_eq_contLaw_sum C T g

/-- Equal continuation laws give equal expectations of every function of `(λ, r)`.
Source: none: infrastructure
Kind: L -/
theorem lawInt_eq_of_contLaw_eq (C : Proc ι acts K) {T T' : Tree Ω ι acts K}
    (h : contLaw C T = contLaw C T') (g : Ω × K → K) : lawInt C T g = lawInt C T' g := by
  rw [lawInt_eq_contLaw_sum, lawInt_eq_contLaw_sum, h]

theorem lawInt_chance (C : Proc ι acts K) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (g : Ω × K → K) :
    lawInt C (.chance n β child) g = ∑ i, β.w i * lawInt C (child i) g := by
  unfold lawInt
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [leafLaw_chance, world_chance, payoff_chance]; ring

theorem lawInt_decision (C : Proc ι acts K) (d : ι) (child : acts d → Tree Ω ι acts K)
    (g : Ω × K → K) :
    lawInt C (.decision d child) g = ∑ a, (C d).w a * lawInt C (child a) g := by
  unfold lawInt
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [leafLaw_decision, world_decision, payoff_decision]; ring

variable [DecidableEq ι] [∀ d, DecidableEq (acts d)]

/-- The minimal `d`-nodes of a tree.
Source: [[decision-problems-v2]] Lemma 1 proof ("minimal `d`-nodes `q`")
Kind: D -/
def minimalFiber (B : Tree Ω ι acts K) (d : ι) : Finset B.DecNode :=
  (fiber B d).filter fun q => pt B q ∉ ancestorPts B q

theorem mem_minimalFiber (B : Tree Ω ι acts K) (d : ι) (q : B.DecNode) :
    q ∈ minimalFiber B d ↔ pt B q = d ∧ IsMinimal B q := by
  simp [minimalFiber, fiber, IsMinimal]

/-- Sums over the minimal fiber, unfolded to indicator sums over all nodes.
Source: none: infrastructure
Kind: L -/
theorem sum_minimalFiber (B : Tree Ω ι acts K) (d : ι) (f : B.DecNode → K) :
    ∑ q ∈ minimalFiber B d, f q =
      ∑ q, if pt B q = d then (if pt B q ∉ ancestorPts B q then f q else 0) else 0 := by
  unfold minimalFiber fiber
  rw [Finset.sum_filter, Finset.sum_filter]

/-- Sums over the fiber, unfolded to indicator sums over all nodes.
Source: none: infrastructure
Kind: L -/
theorem sum_fiber (B : Tree Ω ι acts K) (d : ι) (f : B.DecNode → K) :
    ∑ q ∈ fiber B d, f q = ∑ q, if pt B q = d then f q else 0 := by
  unfold fiber
  rw [Finset.sum_filter]

/-- The minimal fiber of a chance node is the union of its children's.
Source: none: infrastructure
Kind: L -/
theorem sum_minimalFiber_chance (d : ι) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (f : (Tree.chance n β child).DecNode → K) :
    ∑ q ∈ minimalFiber (.chance n β child) d, f q =
      ∑ i, ∑ q ∈ minimalFiber (child i) d, f ⟨i, q⟩ := by
  rw [sum_minimalFiber, sum_decNode_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_minimalFiber]
  rfl

/-- The fiber of a chance node is the union of its children's.
Source: none: infrastructure
Kind: L -/
theorem sum_fiber_chance (d : ι) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (f : (Tree.chance n β child).DecNode → K) :
    ∑ q ∈ fiber (.chance n β child) d, f q = ∑ i, ∑ q ∈ fiber (child i) d, f ⟨i, q⟩ := by
  rw [sum_fiber, sum_decNode_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_fiber]
  rfl

/-- The minimal `d`-fiber of a `d'`-node: the node itself if `d' = d` (and then nothing below
is minimal), else the union of the children's minimal fibers.
Source: none: infrastructure
Kind: L -/
theorem sum_minimalFiber_decision (d d' : ι) (child : acts d' → Tree Ω ι acts K)
    (f : (Tree.decision d' child).DecNode → K) :
    ∑ q ∈ minimalFiber (.decision d' child) d, f q =
      if d' = d then f none else ∑ a, ∑ q ∈ minimalFiber (child a) d, f (some ⟨a, q⟩) := by
  rw [sum_minimalFiber, sum_decNode_decision]
  simp only [pt_decision_none, pt_decision_some, ancestorPts_decision_none,
    ancestorPts_decision_some, List.not_mem_nil, not_false_eq_true, if_true]
  by_cases hd : d' = d
  · subst hd
    simp only [if_true, add_eq_left]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro q _
    by_cases h1 : pt (child a) q = d'
    · rw [if_pos h1, if_neg]
      intro h2; exact h2 (by rw [h1]; exact List.mem_cons_self)
    · rw [if_neg h1]
  · simp only [hd, if_false, zero_add]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_minimalFiber]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h1 : pt (child a) q = d
    · simp only [h1, if_true, List.mem_cons, not_or, Ne.symm hd, not_false_eq_true, true_and]
    · simp only [h1, if_false]

/-- The `d`-fiber of a `d'`-node: the node itself if `d' = d`, plus the children's fibers.
Source: none: infrastructure
Kind: L -/
theorem sum_fiber_decision (d d' : ι) (child : acts d' → Tree Ω ι acts K)
    (f : (Tree.decision d' child).DecNode → K) :
    ∑ q ∈ fiber (.decision d' child) d, f q =
      (if d' = d then f none else 0) + ∑ a, ∑ q ∈ fiber (child a) d, f (some ⟨a, q⟩) := by
  rw [sum_fiber, sum_decNode_decision]
  simp only [pt_decision_none, pt_decision_some]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_fiber]
  rfl

/-- **Lemma 1's decomposition over minimal nodes**: on every tree and for every `g`,
`∑_{ℓ ∈ occ d} μ(ℓ) g(λ(ℓ), r(ℓ)) = ∑_{q minimal d-node} R_q(C) · ∫ g dμ_{T_q, C}` — the
`occ(d)`-runs are the disjoint union of the runs through the minimal `d`-nodes, and below such a
node the walk is the walk of the subtree.
Source: [[decision-problems-v2]] Lemma 1 proof; `equiv.md` EQ-5 ("Lemma 1's decomposition");
`fable-slop-notes.md` Claim 1.1 ("a mixture over minimal `d`-nodes of their downtree laws")
Kind: P
Fidelity: exact
Hyps: none -/
theorem occ_decomposition (C : Proc ι acts K) (d : ι) (g : Ω × K → K) :
    (B : Tree Ω ι acts K) →
      (∑ ℓ, if 0 < count d B ℓ then leafLaw C B ℓ * g (world B ℓ, payoff B ℓ) else 0) =
        ∑ q ∈ minimalFiber B d, reach C B q * lawInt C (subtreeAt B q) g
  | .leaf _ _ => by
      simp only [count_leaf, lt_irrefl, if_false, Finset.sum_const_zero]
      symm; apply Finset.sum_eq_zero; intro q _; exact q.elim
  | .chance _ β child => by
      rw [sum_leaves_chance, sum_minimalFiber_chance]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hR : (∑ q ∈ minimalFiber (child i) d, reach C (.chance _ β child) ⟨i, q⟩ *
          lawInt C (subtreeAt (.chance _ β child) ⟨i, q⟩) g) =
          β.w i * ∑ q ∈ minimalFiber (child i) d, reach C (child i) q *
            lawInt C (subtreeAt (child i) q) g := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        show β.w i * reach C (child i) q * lawInt C (subtreeAt (child i) q) g = _
        ring
      rw [hR, ← occ_decomposition C d g (child i), Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      simp only [count_chance, leafLaw_chance, world_chance, payoff_chance]
      split_ifs <;> ring
  | .decision d' child => by
      rw [sum_leaves_decision, sum_minimalFiber_decision]
      by_cases hd : d' = d
      · subst hd
        rw [if_pos rfl]
        show _ = 1 * lawInt C (.decision d' child) g
        rw [one_mul, lawInt_decision]
        refine Finset.sum_congr rfl fun a _ => ?_
        unfold lawInt
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        have hpos : 0 < count d' (.decision d' child) ⟨a, ℓ⟩ := by
          rw [count_decision, if_pos rfl]; omega
        rw [if_pos hpos]
        simp only [leafLaw_decision, world_decision, payoff_decision]
        ring
      · rw [if_neg hd]
        refine Finset.sum_congr rfl fun a _ => ?_
        have hR : (∑ q ∈ minimalFiber (child a) d, reach C (.decision d' child) (some ⟨a, q⟩) *
            lawInt C (subtreeAt (.decision d' child) (some ⟨a, q⟩)) g) =
            (C d').w a * ∑ q ∈ minimalFiber (child a) d, reach C (child a) q *
              lawInt C (subtreeAt (child a) q) g := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          show (C d').w a * reach C (child a) q * lawInt C (subtreeAt (child a) q) g = _
          ring
        rw [hR, ← occ_decomposition C d g (child a), Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        simp only [count_decision, leafLaw_decision, world_decision, payoff_decision, hd,
          if_false, zero_add]
        split_ifs <;> ring

/-- **Lemma 1's decomposition over all `d`-nodes**: on every tree and for every `g`,
`∑_ℓ μ(ℓ) #_d(ℓ) g(λ(ℓ), r(ℓ)) = ∑_{q ∈ F_d} R_q(C) · ∫ g dμ_{T_q, C}` — every `d`-node on a run
contributes once.
Source: `fable-slop-notes.md` Claim 1.1 ("`𝔼_μ[#_d 1_X] = ∑_{q : d_q = d} μ(reach q ∧ X)`");
`equiv.md` EQ-5
Kind: P
Fidelity: exact
Hyps: none -/
theorem count_decomposition (C : Proc ι acts K) (d : ι) (g : Ω × K → K) :
    (B : Tree Ω ι acts K) →
      (∑ ℓ, leafLaw C B ℓ * (count d B ℓ : K) * g (world B ℓ, payoff B ℓ)) =
        ∑ q ∈ fiber B d, reach C B q * lawInt C (subtreeAt B q) g
  | .leaf _ _ => by
      simp only [count_leaf, Nat.cast_zero, mul_zero, zero_mul, Finset.sum_const_zero]
      symm; apply Finset.sum_eq_zero; intro q _; exact q.elim
  | .chance _ β child => by
      rw [sum_leaves_chance, sum_fiber_chance]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hR : (∑ q ∈ fiber (child i) d, reach C (.chance _ β child) ⟨i, q⟩ *
          lawInt C (subtreeAt (.chance _ β child) ⟨i, q⟩) g) =
          β.w i * ∑ q ∈ fiber (child i) d, reach C (child i) q *
            lawInt C (subtreeAt (child i) q) g := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        show β.w i * reach C (child i) q * lawInt C (subtreeAt (child i) q) g = _
        ring
      rw [hR, ← count_decomposition C d g (child i), Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      simp only [count_chance, leafLaw_chance, world_chance, payoff_chance]
      ring
  | .decision d' child => by
      rw [sum_leaves_decision, sum_fiber_decision]
      have hR : ∀ a, (∑ q ∈ fiber (child a) d, reach C (.decision d' child) (some ⟨a, q⟩) *
          lawInt C (subtreeAt (.decision d' child) (some ⟨a, q⟩)) g) =
          (C d').w a * ∑ q ∈ fiber (child a) d, reach C (child a) q *
            lawInt C (subtreeAt (child a) q) g := fun a => by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        show (C d').w a * reach C (child a) q * lawInt C (subtreeAt (child a) q) g = _
        ring
      simp only [hR]
      by_cases hd : d' = d
      · subst hd
        rw [if_pos rfl]
        show _ = 1 * lawInt C (.decision d' child) g + _
        rw [one_mul, lawInt_decision, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← count_decomposition C d' g (child a)]
        unfold lawInt
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        simp only [count_decision, leafLaw_decision, world_decision, payoff_decision]
        push_cast
        ring
      · rw [if_neg hd, zero_add]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← count_decomposition C d g (child a), Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        simp only [count_decision, leafLaw_decision, world_decision, payoff_decision, hd,
          if_false, zero_add]
        ring

/-! ### The continuation law at a node, and its fiber-constancy on law-fair trees -/

/-- `θ_q(C) := contLaw C (T_q)`, the continuation `(λ, r)`-law below the node `q`.
Source: `fair-repair.md` FR-1(ii) (`θ_d`, "the downtree leaf-law conditional on reaching `q`");
`equiv.md` EQ-5 (`θ_d(C)`)
Kind: D -/
noncomputable def thetaAt (C : Proc ι acts K) (B : Tree Ω ι acts K) (q : B.DecNode) :
    Ω × K →₀ K :=
  contLaw C (subtreeAt B q)

/-- **On a law-fair tree `θ_q(C)` is fiber-constant**: `θ_d(C)` is well defined.
Source: `equiv.md` EQ-5 ("the downtree law `θ_d(C)` is node-independent for every `C`,
trembled included"); `fair-repair.md` FR-1(ii)
Kind: P
Fidelity: exact
Hyps: none -/
theorem LawFair.thetaAt_eq {B : Tree Ω ι acts K} (h : LawFair B) (C : Proc ι acts K) {d : ι}
    {q q' : B.DecNode} (hq : q ∈ fiber B d) (hq' : q' ∈ fiber B d) :
    thetaAt C B q = thetaAt C B q' :=
  h d q hq q' hq' C

/-- `θ_d(C)`: the common continuation law of the fiber, read at any member (a nonempty fiber).
Source: `fair-repair.md` FR-1(ii); `equiv.md` EQ-5
Kind: D -/
noncomputable def theta (C : Proc ι acts K) (B : Tree Ω ι acts K) {d : ι}
    (hd : (fiber B d).Nonempty) : Ω × K →₀ K :=
  thetaAt C B hd.choose

/-- On a law-fair tree `θ_q(C) = θ_d(C)` for every member `q` of the fiber.
Source: `equiv.md` EQ-5
Kind: L -/
theorem LawFair.thetaAt_eq_theta {B : Tree Ω ι acts K} (h : LawFair B) (C : Proc ι acts K) {d : ι}
    (hd : (fiber B d).Nonempty) {q : B.DecNode} (hq : q ∈ fiber B d) :
    thetaAt C B q = theta C B hd :=
  h.thetaAt_eq C hq hd.choose_spec

/-! ### EQ-5 / L3 / Claim 1.1: the fork closes on law-fair trees -/

/-- The world-marginal `θ_d(C)(X)` of the continuation law at `q`: `ν_{T_q, C}(X)`.
Source: `fair-repair.md` FR-1(ii) ("the common SSC value is `θ_d`'s world-marginal")
Kind: L -/
theorem nu_subtreeAt_eq_thetaAt_sum [DecidableEq Ω] (C : Proc ι acts K) (B : Tree Ω ι acts K)
    (q : B.DecNode) (X : Finset Ω) :
    nu C (subtreeAt B q) X = (thetaAt C B q).sum fun p v => v * (if p.1 ∈ X then 1 else 0) :=
  nu_eq_contLaw_sum C _ X

/-- **Fork closure, per-run clause (EQ-5 / L3 / Claim 1.1)**: on a **law-fair** tree, for every
procedure `C` (trembled included), point `d`, event `X` and fiber member `q₀`,
`μ_{B,C}(occ d ∧ {λ ⊨ X}) = (∑_{q minimal d-node} R_q(C)) · ν_{T_{q₀}, C}(X)` and
`μ_{B,C}(occ d) = ∑_{q minimal d-node} R_q(C)`. So the per-run statistic of Definition 13 is
`θ_d(C)`'s world-marginal whenever `μ(occ d) > 0`, independently of the reach weights. Scope:
law-fair (law-spurious nesting allowed), Definition 6, root site irrelevant.
Source: `equiv.md` EQ-5 ("per-run SSC gives `μ(X ∣ occ(d)) = ∑_{q minimal} R_q θ_d(X) /
∑_{q minimal} R_q = θ_d(X)`"); `fair-repair.md` FR-1(ii); `fable-slop-notes.md` Claim 1.1
Kind: P
Fidelity: exact (stated multiplicatively; the divided form is `LawFair.perRun_statistic`)
Hyps: none -/
theorem LawFair.fork_closure_perRun [DecidableEq Ω] {B : Tree Ω ι acts K} (h : LawFair B)
    (C : Proc ι acts K) (d : ι) (X : Finset Ω) {q₀ : B.DecNode} (hq₀ : q₀ ∈ fiber B d) :
    mass C B (worldEv B X ∩ occ d B) =
        (∑ q ∈ minimalFiber B d, reach C B q) * nu C (subtreeAt B q₀) X ∧
      mass C B (occ d B) = ∑ q ∈ minimalFiber B d, reach C B q := by
  constructor
  · have hL : mass C B (worldEv B X ∩ occ d B) =
        ∑ ℓ, if 0 < count d B ℓ then leafLaw C B ℓ *
          (fun p : Ω × K => if p.1 ∈ X then (1 : K) else 0) (world B ℓ, payoff B ℓ) else 0 := by
      unfold mass
      rw [← Finset.univ_inter (worldEv B X ∩ occ d B), ← Finset.sum_ite_mem]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      simp only [Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and, mem_occ]
      by_cases hc : 0 < count d B ℓ <;> by_cases hx : world B ℓ ∈ X <;> simp [hc, hx]
    rw [hL, occ_decomposition C d (fun p : Ω × K => if p.1 ∈ X then (1 : K) else 0) B,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [mem_minimalFiber] at hq
    have hθ : contLaw C (subtreeAt B q) = contLaw C (subtreeAt B q₀) :=
      h d q (by simpa using hq.1) q₀ hq₀ C
    rw [lawInt_eq_of_contLaw_eq C hθ, nu_eq_contLaw_sum, ← lawInt_eq_contLaw_sum]
  · have hL : mass C B (occ d B) = ∑ ℓ, if 0 < count d B ℓ then leafLaw C B ℓ *
        (fun _ : Ω × K => (1 : K)) (world B ℓ, payoff B ℓ) else 0 := by
      rw [mass_occ]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      split_ifs <;> simp
    rw [hL, occ_decomposition C d (fun _ : Ω × K => (1 : K)) B]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : lawInt C (subtreeAt B q) (fun _ => (1 : K)) = 1 := by
      unfold lawInt; simp [sum_leafLaw]
    rw [this, mul_one]

/-- **Fork closure, per-occurrence clause (EQ-5 / Claim 1.1)**: on a **law-fair** tree, for every
`C`, `d`, `X` and fiber member `q₀`, `𝔼_μ[#_d 1_X] = (∑_{q ∈ F_d} R_q(C)) · ν_{T_{q₀}, C}(X)`
and `𝔼_μ[#_d] = ∑_{q ∈ F_d} R_q(C)` — all `d`-nodes, not only the minimal ones. So the
per-occurrence statistic is again `θ_d(C)`'s world-marginal whenever `𝔼_μ[#_d] > 0`: the
anthropic fork closes without the trace level.
Source: `equiv.md` EQ-5 ("per-occurrence SSC gives `∑_q R_q θ_d(X) / ∑_q R_q = θ_d(X)`");
`fable-slop-notes.md` Claim 1.1
Kind: P
Fidelity: exact (multiplicative form)
Hyps: none -/
theorem LawFair.fork_closure_perOcc [DecidableEq Ω]
    {B : Tree Ω ι acts K} (h : LawFair B)
    (C : Proc ι acts K) (d : ι) (X : Finset Ω) {q₀ : B.DecNode} (hq₀ : q₀ ∈ fiber B d) :
    expCountIn C B d X = (∑ q ∈ fiber B d, reach C B q) * nu C (subtreeAt B q₀) X ∧
      expCount C B d = ∑ q ∈ fiber B d, reach C B q := by
  constructor
  · have hL : expCountIn C B d X = ∑ ℓ, leafLaw C B ℓ * (count d B ℓ : K) *
        (fun p : Ω × K => if p.1 ∈ X then (1 : K) else 0) (world B ℓ, payoff B ℓ) := rfl
    rw [hL, count_decomposition C d (fun p : Ω × K => if p.1 ∈ X then (1 : K) else 0) B,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hθ : contLaw C (subtreeAt B q) = contLaw C (subtreeAt B q₀) := h d q hq q₀ hq₀ C
    rw [lawInt_eq_of_contLaw_eq C hθ, nu_eq_contLaw_sum, ← lawInt_eq_contLaw_sum]
  · have hL : expCount C B d = ∑ ℓ, leafLaw C B ℓ * (count d B ℓ : K) *
        (fun _ : Ω × K => (1 : K)) (world B ℓ, payoff B ℓ) := by
      unfold expCount; simp
    rw [hL, count_decomposition C d (fun _ : Ω × K => (1 : K)) B]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : lawInt C (subtreeAt B q) (fun _ => (1 : K)) = 1 := by
      unfold lawInt; simp [sum_leafLaw]
    rw [this, mul_one]

/-- The per-run statistic in divided form: `μ(X ∣ occ d) = ν_{T_{q₀},C}(X)` when `μ(occ d) > 0`.
Source: `equiv.md` EQ-5
Kind: C -/
theorem LawFair.perRun_statistic [DecidableEq Ω] {B : Tree Ω ι acts K} (h : LawFair B)
    (C : Proc ι acts K) (d : ι) (X : Finset Ω) {q₀ : B.DecNode} (hq₀ : q₀ ∈ fiber B d)
    (hpos : 0 < mass C B (occ d B)) :
    mass C B (worldEv B X ∩ occ d B) / mass C B (occ d B) = nu C (subtreeAt B q₀) X := by
  obtain ⟨h1, h2⟩ := h.fork_closure_perRun C d X hq₀
  have hS : (∑ q ∈ minimalFiber B d, reach C B q) ≠ 0 := by rw [← h2]; exact hpos.ne'
  rw [h1, h2, mul_div_cancel_left₀ _ hS]

/-- The per-occurrence statistic in divided form: `𝔼[#_d 1_X] / 𝔼[#_d] = ν_{T_{q₀},C}(X)` when
`𝔼[#_d] > 0`.
Source: `equiv.md` EQ-5
Kind: C -/
theorem LawFair.perOcc_statistic [DecidableEq Ω]
    {B : Tree Ω ι acts K} (h : LawFair B)
    (C : Proc ι acts K) (d : ι) (X : Finset Ω) {q₀ : B.DecNode} (hq₀ : q₀ ∈ fiber B d)
    (hpos : 0 < expCount C B d) :
    expCountIn C B d X / expCount C B d = nu C (subtreeAt B q₀) X := by
  obtain ⟨h1, h2⟩ := h.fork_closure_perOcc C d X hq₀
  have hS : (∑ q ∈ fiber B d, reach C B q) ≠ 0 := by rw [← h2]; exact hpos.ne'
  rw [h1, h2, mul_div_cancel_left₀ _ hS]

/-- **Both statistics agree on law-fair trees** (the fork is closed): the per-run and the
per-occurrence statistic are the same number whenever both denominators are positive.
Source: `equiv.md` EQ-5 ("both Definition-13 senses reduce to `P_{s_d} = θ_d`")
Kind: C -/
theorem LawFair.perRun_eq_perOcc [DecidableEq Ω]
    {B : Tree Ω ι acts K} (h : LawFair B)
    (C : Proc ι acts K) (d : ι) (X : Finset Ω) {q₀ : B.DecNode} (hq₀ : q₀ ∈ fiber B d)
    (hpos : 0 < mass C B (occ d B)) (hpos' : 0 < expCount C B d) :
    mass C B (worldEv B X ∩ occ d B) / mass C B (occ d B) =
      expCountIn C B d X / expCount C B d := by
  rw [h.perRun_statistic C d X hq₀ hpos, h.perOcc_statistic C d X hq₀ hpos']

/-- The strongly-fair form of fork closure, as a one-line corollary of the law-fair form.
Source: `fair-repair.md` FR-1(ii); `fable-slop-notes.md` Claim 1.1
Kind: C -/
theorem StronglyFair.fork_closure [DecidableEq Ω]
    {B : Tree Ω ι acts K} (h : StronglyFair B)
    (C : Proc ι acts K) (d : ι) (X : Finset Ω) {q₀ : B.DecNode} (hq₀ : q₀ ∈ fiber B d) :
    (mass C B (worldEv B X ∩ occ d B) =
        (∑ q ∈ minimalFiber B d, reach C B q) * nu C (subtreeAt B q₀) X) ∧
      expCountIn C B d X = (∑ q ∈ fiber B d, reach C B q) * nu C (subtreeAt B q₀) X :=
  ⟨(h.lawFair.fork_closure_perRun C d X hq₀).1, (h.lawFair.fork_closure_perOcc C d X hq₀).1⟩

end Cleanroom.Decision.DpFairnessReloc
