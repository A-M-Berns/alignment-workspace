import Cleanroom.Decision.DpFairnessReloc.RelationsChain

/-!
# Trace functionals, EQ-4 at the trace level, EQ-3's corollary (repair round 1)

Package `dp-fairness-reloc`, file 12. Over `RelationsThms.lean`: every statistic of the form
`∑_ℓ μ(ℓ) g(draws ℓ, λ(ℓ), r(ℓ))` is a functional of `traceDist` (`sum_leafLaw_mul_trace`), which
gives EQ-6's per-statistic clauses for `≈_tr` and `≃_Δ` (`BisimΔ.statistics_eq`); the maximal
`d`-count `maxCount` is `≈_tr`-invariant on pruned trees and separates a `d`-root from its
children, which gives EQ-4 for `≈_tr`, `≃_Δ` and `≃` (`FairTr.almostFair` and corollaries);
EQ-3's corollary is split into the proved direction (`FairBisimΔ.fairTr`, in `RelationsThms`)
and the OPEN direction `fairTr_imp_fairBisimΔ` (with its attempt record); EQ-6's Definition-7
clause is stated OPEN (`bisimΔ_recordsFor_iff`).
-/
namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-! ### Trace functionals: EQ-6's per-statistic clauses -/

section traces

variable [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-- The trace key of a leaf: its draws, world and payoff.
Source: `equiv.md` Headline (consultation traces `((d₁,a₁),…,(d_k,a_k),(λ,r))`)
Kind: D -/
abbrev traceKey (T : Tree Ω ι acts K) (ℓ : T.Leaves) : List (Σ d : ι, acts d) × (Ω × K) :=
  (draws T ℓ, (world T ℓ, payoff T ℓ))

/-- Every statistic of the form `∑_ℓ μ(ℓ) g(trace ℓ)` is a functional of the trace distribution.
Source: `equiv.md` EQ-6 ("`≃_Δ`-related subtrees agree for every `C` on traces, hence on …")
Kind: L -/
theorem sum_leafLaw_mul_trace (C : Proc ι acts K) (T : Tree Ω ι acts K)
    (g : List (Σ d : ι, acts d) × (Ω × K) → K) :
    ∑ ℓ, leafLaw C T ℓ * g (traceKey T ℓ) = (traceDist C T).sum fun τ v => v * g τ := by
  unfold traceDist
  rw [← Finsupp.sum_finsetSum_index (h := fun τ v => v * g τ) (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finsupp.sum_single_index (zero_mul _)]

/-- Trace-equivalent trees agree on every trace functional, for every procedure.
Source: `equiv.md` EQ-6
Kind: L -/
theorem TrEq.sum_eq {T T' : Tree Ω ι acts K} (h : TrEq T T') (C : Proc ι acts K)
    (g : List (Σ d : ι, acts d) × (Ω × K) → K) :
    ∑ ℓ, leafLaw C T ℓ * g (traceKey T ℓ) = ∑ ℓ, leafLaw C T' ℓ * g (traceKey T' ℓ) := by
  rw [sum_leafLaw_mul_trace, sum_leafLaw_mul_trace, h C]

/-- `μ(occ e)` as a trace functional (`#_e` is the number of `e`-draws on the trace).
Source: none: infrastructure
Kind: L -/
theorem mass_occ_eq_trace (C : Proc ι acts K) (T : Tree Ω ι acts K) (e : ι) :
    mass C T (occ e T) = ∑ ℓ, leafLaw C T ℓ *
      (if 0 < ((traceKey T ℓ).1.map Sigma.fst).count e then 1 else 0) := by
  unfold mass occ
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [count_eq_draws_count]
  split_ifs <;> simp

/-- **EQ-6, `μ(occ e)`**: trace-equivalent trees have the same occurrence mass at every point,
for every procedure.
Source: `equiv.md` EQ-6 ("`μ(occ(e))`")
Kind: C
Fidelity: exact -/
theorem TrEq.mass_occ_eq {T T' : Tree Ω ι acts K} (h : TrEq T T') (C : Proc ι acts K) (e : ι) :
    mass C T (occ e T) = mass C T' (occ e T') := by
  rw [mass_occ_eq_trace, mass_occ_eq_trace]
  exact h.sum_eq C fun τ => if 0 < (τ.1.map Sigma.fst).count e then 1 else 0

/-- `𝔼[#_e 1_X]` as a trace functional.
Source: none: infrastructure
Kind: L -/
theorem expCountIn_eq_trace [DecidableEq Ω] (C : Proc ι acts K) (T : Tree Ω ι acts K) (e : ι)
    (X : Finset Ω) :
    expCountIn C T e X = ∑ ℓ, leafLaw C T ℓ *
      ((((traceKey T ℓ).1.map Sigma.fst).count e : K) * if (traceKey T ℓ).2.1 ∈ X then 1 else 0) := by
  unfold expCountIn
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [count_eq_draws_count, mul_assoc]

/-- **EQ-6, `𝔼[#_e 1_X]`**: trace-equivalent trees have the same per-occurrence numerator at
every point and event, for every procedure.
Source: `equiv.md` EQ-6 ("`𝔼[#_e 1_X]` for every point `e`")
Kind: C
Fidelity: exact -/
theorem TrEq.expCountIn_eq [DecidableEq Ω] {T T' : Tree Ω ι acts K} (h : TrEq T T')
    (C : Proc ι acts K) (e : ι) (X : Finset Ω) : expCountIn C T e X = expCountIn C T' e X := by
  rw [expCountIn_eq_trace, expCountIn_eq_trace]
  exact h.sum_eq C fun τ => ((τ.1.map Sigma.fst).count e : K) * if τ.2.1 ∈ X then 1 else 0

/-- `𝔼[#_e]` as a trace functional. Source: none: infrastructure. Kind: L -/
theorem expCount_eq_trace (C : Proc ι acts K) (T : Tree Ω ι acts K) (e : ι) :
    expCount C T e = ∑ ℓ, leafLaw C T ℓ * (((traceKey T ℓ).1.map Sigma.fst).count e : K) := by
  unfold expCount
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [count_eq_draws_count]

/-- **EQ-6, `𝔼[#_e]`**. Source: `equiv.md` EQ-6. Kind: C. Fidelity: exact -/
theorem TrEq.expCount_eq {T T' : Tree Ω ι acts K} (h : TrEq T T') (C : Proc ι acts K) (e : ι) :
    expCount C T e = expCount C T' e := by
  rw [expCount_eq_trace, expCount_eq_trace]
  exact h.sum_eq C fun τ => ((τ.1.map Sigma.fst).count e : K)

/-- `ν(X)` as a trace functional. Source: none: infrastructure. Kind: L -/
theorem nu_eq_trace [DecidableEq Ω] (C : Proc ι acts K) (T : Tree Ω ι acts K) (X : Finset Ω) :
    nu C T X = ∑ ℓ, leafLaw C T ℓ * (if (traceKey T ℓ).2.1 ∈ X then 1 else 0) := by
  unfold nu mass worldEv
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  split_ifs <;> simp

/-- **EQ-6, `ν(X)`**: the world marginal. Source: `equiv.md` EQ-6. Kind: C. Fidelity: exact -/
theorem TrEq.nu_eq [DecidableEq Ω] {T T' : Tree Ω ι acts K} (h : TrEq T T') (C : Proc ι acts K)
    (X : Finset Ω) : nu C T X = nu C T' X := by
  rw [nu_eq_trace, nu_eq_trace]
  exact h.sum_eq C fun τ => if τ.2.1 ∈ X then 1 else 0

/-- **EQ-6 for `≃_Δ`** (every tree, pruned or not): `≃_Δ`-related subtrees agree for every
procedure on `μ(occ e)`, `𝔼[#_e 1_X]`, `𝔼[#_e]`, `ν(X)`, the continuation law and the value.
Source: `equiv.md` EQ-6 ("`≃_Δ`-related subtrees agree for every `C` on traces, hence on `T̂(C)`,
`μ(occ(e))`, `𝔼[#_e 1_X]` for every point `e`, … optimal values")
Kind: C
Fidelity: stronger (no pruning needed for these statistics; the Definition-7 clause, which does
need pruning, is `bisimΔ_recordsFor_iff`, OPEN) -/
theorem BisimΔ.statistics_eq [DecidableEq Ω] {T T' : Tree Ω ι acts K} (h : BisimΔ T T')
    (C : Proc ι acts K) :
    (∀ e, mass C T (occ e T) = mass C T' (occ e T')) ∧
      (∀ e X, expCountIn C T e X = expCountIn C T' e X) ∧
      (∀ e, expCount C T e = expCount C T' e) ∧
      (∀ X, nu C T X = nu C T' X) ∧
      contLaw C T = contLaw C T' ∧ value C T = value C T' :=
  ⟨fun e => h.trEq.mass_occ_eq C e, fun e X => h.trEq.expCountIn_eq C e X,
    fun e => h.trEq.expCount_eq C e, fun X => h.trEq.nu_eq C X, h.trEq.lawEq C,
    h.trEq.lawEq.valEq C⟩

end traces

/-! ### EQ-4 at the trace level: `Fair_{≈tr}` excludes nested fibers on pruned trees -/

section eq4

variable [DecidableEq ι] [∀ d, Fintype (acts d)]

/-- `Fair_E` passes to the children of a chance node.
Source: none: infrastructure
Kind: L -/
theorem FairWrt.chance_child {E : ι → Tree Ω ι acts K → Tree Ω ι acts K → Prop} {n : ℕ}
    {β : FinDistr K (Fin n)} {child : Fin n → Tree Ω ι acts K} (h : FairWrt E (.chance n β child))
    (i : Fin n) : FairWrt E (child i) := by
  intro d q hq q' hq'
  have := h d ⟨i, q⟩ (by simpa using hq) ⟨i, q'⟩ (by simpa using hq')
  simpa using this

/-- `Fair_E` passes to the children of a decision node.
Source: none: infrastructure
Kind: L -/
theorem FairWrt.decision_child {E : ι → Tree Ω ι acts K → Tree Ω ι acts K → Prop} {d : ι}
    {child : acts d → Tree Ω ι acts K} (h : FairWrt E (.decision d child)) (a : acts d) :
    FairWrt E (child a) := by
  intro e q hq q' hq'
  have := h e (some ⟨a, q⟩) (by simpa using hq) (some ⟨a, q'⟩) (by simpa using hq')
  simpa using this

variable [∀ d, DecidableEq (acts d)]

/-- Pruning passes to the children of a chance node. Source: none: infrastructure. Kind: L -/
theorem Pruned.chance_child {n : ℕ} {β : FinDistr K (Fin n)} {child : Fin n → Tree Ω ι acts K}
    (h : Pruned (.chance n β child)) (i : Fin n) : Pruned (child i) :=
  fun ℓ => ((Positive.chance_iff β child i ℓ).mp (h ⟨i, ℓ⟩)).2

/-- Pruning passes to the children of a decision node. Source: none: infrastructure. Kind: L -/
theorem Pruned.decision_child {d : ι} {child : acts d → Tree Ω ι acts K}
    (h : Pruned (.decision d child)) (a : acts d) : Pruned (child a) :=
  fun ℓ => (Positive.decision_iff d child a ℓ).mp (h ⟨a, ℓ⟩)

/-- The count of `e` along a subtree leaf is at most its count along the embedded leaf.
Source: none: infrastructure
Kind: L -/
theorem count_le_count_embedLeaf (e : ι) :
    (B : Tree Ω ι acts K) → ∀ (q : B.DecNode) (ℓ : (subtreeAt B q).Leaves),
      count e (subtreeAt B q) ℓ ≤ count e B (embedLeaf B q ℓ)
  | .leaf _ _, q, _ => q.elim
  | .chance _ _ child, ⟨i, q⟩, ℓ => by
      show count e (subtreeAt (child i) q) ℓ ≤ count e (.chance _ _ child) ⟨i, embedLeaf (child i) q ℓ⟩
      rw [count_chance]
      exact count_le_count_embedLeaf e (child i) q ℓ
  | .decision _ _, none, _ => le_rfl
  | .decision d' child, some ⟨a, q⟩, ℓ => by
      show count e (subtreeAt (child a) q) ℓ ≤ count e (.decision d' child) ⟨a, embedLeaf (child a) q ℓ⟩
      rw [count_decision]
      have := count_le_count_embedLeaf e (child a) q ℓ
      omega

/-- A positive embedded leaf is positive in the subtree.
Source: none: infrastructure
Kind: L -/
theorem Positive.of_embedLeaf :
    (B : Tree Ω ι acts K) → ∀ (q : B.DecNode) (ℓ : (subtreeAt B q).Leaves),
      Positive B (embedLeaf B q ℓ) → Positive (subtreeAt B q) ℓ
  | .leaf _ _, q, _, _ => q.elim
  | .chance _ β child, ⟨i, q⟩, ℓ, h => by
      show Positive (subtreeAt (child i) q) ℓ
      have h' : Positive (.chance _ β child) ⟨i, embedLeaf (child i) q ℓ⟩ := h
      exact Positive.of_embedLeaf (child i) q ℓ ((Positive.chance_iff β child i _).mp h').2
  | .decision _ _, none, _, h => h
  | .decision d' child, some ⟨a, q⟩, ℓ, h => by
      show Positive (subtreeAt (child a) q) ℓ
      have h' : Positive (.decision d' child) ⟨a, embedLeaf (child a) q ℓ⟩ := h
      exact Positive.of_embedLeaf (child a) q ℓ ((Positive.decision_iff d' child a _).mp h')

/-- Subtrees of pruned trees are pruned. Source: none: infrastructure. Kind: L -/
theorem Pruned.subtreeAt {B : Tree Ω ι acts K} (h : Pruned B) (q : B.DecNode) :
    Pruned (subtreeAt B q) :=
  fun ℓ => Positive.of_embedLeaf B q ℓ (h _)

/-- The largest number of `d`-nodes on any root path of `T`.
Source: `equiv.md` EQ-4 ("bisimilar nodes have equal height after pruning"), rendered as the
maximal `d`-count over root paths — the invariant that separates a node from a proper
`d`-descendant
Kind: D -/
def maxCount (d : ι) (T : Tree Ω ι acts K) : ℕ := Finset.univ.sup (count d T)

theorem count_le_maxCount (d : ι) (T : Tree Ω ι acts K) (ℓ : T.Leaves) :
    count d T ℓ ≤ maxCount d T :=
  Finset.le_sup (f := count d T) (Finset.mem_univ ℓ)

theorem maxCount_le_of_forall {d : ι} {T : Tree Ω ι acts K} {n : ℕ} (h : ∀ ℓ, count d T ℓ ≤ n) :
    maxCount d T ≤ n :=
  Finset.sup_le fun ℓ _ => h ℓ

/-- The maximal count does not grow when passing to a subtree.
Source: none: infrastructure
Kind: L -/
theorem maxCount_subtreeAt_le (d : ι) (B : Tree Ω ι acts K) (q : B.DecNode) :
    maxCount d (subtreeAt B q) ≤ maxCount d B :=
  maxCount_le_of_forall fun ℓ => (count_le_count_embedLeaf d B q ℓ).trans (count_le_maxCount d B _)

/-- Below a `d`-root the maximal `d`-count of a child is strictly smaller.
Source: none: infrastructure
Kind: L -/
theorem maxCount_child_lt_decision [∀ d, Nonempty (acts d)] (d : ι)
    (child : acts d → Tree Ω ι acts K) (a : acts d) :
    maxCount d (child a) < maxCount d (.decision d child) := by
  have hne : (Finset.univ : Finset (child a).Leaves).Nonempty :=
    Finset.univ_nonempty_iff.mpr (leaves_nonempty (child a))
  obtain ⟨ℓ, -, hℓ⟩ := Finset.exists_mem_eq_sup Finset.univ hne (count d (child a))
  have := count_le_maxCount d (.decision d child) ⟨a, ℓ⟩
  rw [count_decision, if_pos rfl] at this
  show Finset.univ.sup (count d (child a)) < maxCount d (.decision d child)
  rw [hℓ]
  omega

/-- A leaf of positive mass puts mass on its trace.
Source: none: infrastructure
Kind: L -/
theorem traceDist_ne_zero_of_pos {C : Proc ι acts K} {T : Tree Ω ι acts K} (ℓ : T.Leaves)
    (h : 0 < leafLaw C T ℓ) : traceDist C T (traceKey T ℓ) ≠ 0 := by
  classical
  unfold traceDist
  rw [Finsupp.finsetSum_apply]
  refine ne_of_gt (lt_of_lt_of_le h ?_)
  calc leafLaw C T ℓ
      = Finsupp.single (traceKey T ℓ) (leafLaw C T ℓ) (traceKey T ℓ) := by simp
    _ ≤ ∑ ℓ', Finsupp.single (traceKey T ℓ') (leafLaw C T ℓ') (traceKey T ℓ) := by
        refine Finset.single_le_sum
          (f := fun ℓ' => Finsupp.single (traceKey T ℓ') (leafLaw C T ℓ') (traceKey T ℓ))
          (fun ℓ' _ => ?_) (Finset.mem_univ ℓ)
        rw [Finsupp.single_apply]
        split_ifs
        · exact leafLaw_nonneg C T ℓ'
        · exact le_rfl

/-- A trace of non-zero mass is the trace of some leaf.
Source: none: infrastructure
Kind: L -/
theorem exists_leaf_of_traceDist_ne_zero {C : Proc ι acts K} {T : Tree Ω ι acts K}
    {τ : List (Σ d : ι, acts d) × (Ω × K)} (h : traceDist C T τ ≠ 0) : ∃ ℓ, traceKey T ℓ = τ := by
  classical
  unfold traceDist at h
  rw [Finsupp.finsetSum_apply] at h
  obtain ⟨ℓ, -, hℓ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨ℓ, ?_⟩
  by_contra hne
  rw [Finsupp.single_apply, if_neg hne] at hℓ
  exact hℓ rfl

/-- On pruned trees, trace equivalence bounds the maximal `d`-count: every positive trace of
`T` (all of them, under the uniform procedure) is a trace of `T'`.
Source: `equiv.md` EQ-4 ("`≈_tr`: a proper `d`-ancestor has positive mass on traces with `≥ 2`
`d`-events under any full-support `C`")
Kind: P -/
theorem TrEq.maxCount_le [∀ d, Nonempty (acts d)] {T T' : Tree Ω ι acts K} (h : TrEq T T')
    (hp : Pruned T) (d : ι) : maxCount d T ≤ maxCount d T' := by
  refine maxCount_le_of_forall fun ℓ => ?_
  have hpos : 0 < leafLaw (Proc.uniform : Proc ι acts K) T ℓ :=
    (leafLaw_pos_iff_of_fullSupport Proc.uniform_fullSupport T ℓ).mpr (hp ℓ)
  have h1 := traceDist_ne_zero_of_pos ℓ hpos
  rw [h Proc.uniform] at h1
  obtain ⟨ℓ', hℓ'⟩ := exists_leaf_of_traceDist_ne_zero h1
  have hc : count d T' ℓ' = count d T ℓ := by
    have hd : draws T' ℓ' = draws T ℓ := congrArg Prod.fst hℓ'
    rw [count_eq_draws_count, count_eq_draws_count, hd]
  rw [← hc]
  exact count_le_maxCount d T' ℓ'

/-- On pruned trees the maximal `d`-count is `≈_tr`-invariant.
Source: `equiv.md` EQ-4
Kind: P -/
theorem TrEq.maxCount_eq [∀ d, Nonempty (acts d)] {T T' : Tree Ω ι acts K} (h : TrEq T T')
    (hp : Pruned T) (hp' : Pruned T') (d : ι) : maxCount d T = maxCount d T' :=
  le_antisymm (h.maxCount_le hp d) ((TrEq.equivalence.symm h).maxCount_le hp' d)

/-- **EQ-4 at the trace level**: on a pruned tree, `Fair_{≈tr}` excludes nested fibers — if a
path met `d` twice, the upper `d`-node's subtree would be trace-equivalent to the lower one's,
a proper subtree of one of its children; but the maximal `d`-count is `≈_tr`-invariant on
pruned trees, does not grow on subtrees, and drops strictly from a `d`-root to its children.
Source: `equiv.md` EQ-4 ("Nesting is excluded by … `≈_tr` (a proper `d`-ancestor has positive
mass on traces with `≥ 2` `d`-events under any full-support `C`)")
Kind: P
Fidelity: exact (grade `≈_tr`; pruned; conclusion `dp-core-tree`'s `AlmostFair`, which on a
pruned tree is the positive-path notion)
Hyps: (a) `Pruned B` — the source's own "after pruning" scope, a definition of record; it cannot
be dropped (`pruned_load_bearing`, `AuditWitnesses.lean`: zero-weight nesting is invisible to
`≃`, `≃_Δ` and `≈_tr`) -/
theorem FairTr.almostFair [∀ d, Nonempty (acts d)] :
    (B : Tree Ω ι acts K) → FairTr B → Pruned B → AlmostFair B
  | .leaf _ _, _, _ => fun _ _ => by simp
  | .chance _ β child, h, hp => by
      rintro d ⟨i, ℓ⟩
      simpa using FairTr.almostFair (child i) (FairWrt.chance_child h i) (hp.chance_child i) d ℓ
  | .decision d' child, h, hp => by
      rintro d ⟨a, ℓ⟩
      have ih := FairTr.almostFair (child a) (FairWrt.decision_child h a) (hp.decision_child a) d ℓ
      rw [count_decision]
      by_cases hd : d' = d
      · subst hd
        simp only [if_true]
        suffices hz : count d' (child a) ℓ = 0 by omega
        by_contra hne
        obtain ⟨q, hq, -⟩ := exists_dNode_of_count_pos d' (child a) ℓ (Nat.pos_of_ne_zero hne)
        have htr : TrEq (.decision d' child) (subtreeAt (child a) q) := by
          have := h d' none (by simp) (some ⟨a, q⟩) (by simpa using hq)
          rwa [subtreeAt_decision_none, subtreeAt_decision_some] at this
        have hmax := htr.maxCount_eq hp ((hp.decision_child a).subtreeAt q) d'
        have h1 := maxCount_subtreeAt_le d' (child a) q
        have h2 := maxCount_child_lt_decision d' child a
        omega
      · simp only [hd, if_false, zero_add]; exact ih

/-- **EQ-4 for `≃_Δ`**: on pruned trees `Fair_{≃Δ}` excludes nested fibers (through the chain).
Source: `equiv.md` EQ-4 ("`≃` and `≃_Δ` (bisimilar nodes have equal height after pruning)")
Kind: C
Fidelity: exact -/
theorem FairBisimΔ.almostFair [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K} (h : FairBisimΔ B)
    (hp : Pruned B) : AlmostFair B :=
  FairTr.almostFair B h.fairTr hp

/-- **EQ-4 for `≃`**: on pruned trees `Fair_≃` excludes nested fibers.
Source: `equiv.md` EQ-4
Kind: C
Fidelity: exact (pruning is needed for `≃`: a zero-weight nested copy is `≃`-invisible) -/
theorem FairBisim.almostFair [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K} (h : FairBisim B)
    (hp : Pruned B) : AlmostFair B :=
  h.fairBisimΔ.almostFair hp

end eq4

/-! ### EQ-3's corollary: the open direction -/

section eq3

variable [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-- **OPEN — EQ-3, the coincidence theorem** (theorem form, over the package's objects: the
source's "chance-normal" is absorbed by `flatDist`, so the hypotheses are pruning and inner
`≃_Δ`-fairness on both sides): two pruned, `Fair_{≃Δ}` trees that are `≈_tr` are `≃_Δ`.
Route (`equiv.md` EQ-3, made precise in repair round 2 after audit r2 fidelity §3.2): induction
on `size T + size T'`. Both trees are almost fair (`FairBisimΔ.almostFair`), so no subtree has
a `d`-node below a `d`-root. Write both flattenings' supports as leaves plus decision nodes
grouped by point. (i) Leaves: `flatDist T (leaf ω r) = traceDist C T ([], (ω, r))` for any `C`
(the empty-draw traces), so equal leaves carry equal masses on both sides. (ii) Decision nodes of
point `e`: every such support element is `subtreeAt T q` for some `q ∈ fiber T e` (a chance-only
positive path from the root), so by inner fairness the `e`-group on each side is pairwise `≃_Δ`,
hence pairwise `≈_tr`; the `e`-prefixed part of `traceDist C T` is therefore
`(∑_{S ∈ group} flatDist T S) • traceDist C S₀` for any representative `S₀`, and likewise on the
other side; the `e`-masses agree (read off the trace distribution under `Proc.uniform`, positive
on pruned trees) and so `TrEq S₀ S₀'` for one representative pair. (iii) `TrEq S₀ S₀'` with both
of the form `decision e c`, `decision e c'`: evaluate at `C⁺ := C[e ↦ Proc.uniform e]`, split
`traceDist C⁺` by the first draw `(e, a)` (prefixing is injective, the `(e, a)`-parts have
disjoint supports), so `traceDist C⁺ (c a) = traceDist C⁺ (c' a)`; then `e ∉ queried (c a)`
(almost fair) and `leafLaw_congr_queried` transfer this back to `C`. So `TrEq (c a) (c' a)`, and
the induction hypothesis (both children are pruned, inner-fair, and strictly smaller) gives
`BisimΔ (c a) (c' a)`; `BisimΔ.of_nonChance_pair` gives `BisimΔ S₀ S₀'`, and `BisimΔ.trans`
spreads it over the group. (iv) Assemble: the product coupling per point scaled by the
`e`-mass, plus the diagonal on leaves, has the two flattenings as marginals and is supported on
`≃_Δ`-related pairs; `BisimΔ.of_flatCoupling` closes. Steps (i)–(ii) need the lemma "support
elements of `flatDist` are fiber members" and the first-draw decomposition of `traceDist`; step
(iii) is the (decision, decision) step of round 1's record, whose `C(e)(a) = 0` case is
dischargeable exactly because inner fairness makes both trees almost fair — round 1's
"perturbation/polynomial-identity" route is not needed. Not attempted in Lean (repair round 2
did the corollary's reduction below and the witnesses of `AuditWitnesses.lean`).
Source: `equiv.md` EQ-3 ("for chance-normal `T, T'` whose inner fibers are `≃_Δ`-fair,
`T ≈_tr T' ⇒ T ≃ T'`")
Kind: OPEN -/
theorem bisimΔ_of_trEq_of_fairBisimΔ [∀ d, Nonempty (acts d)] {T T' : Tree Ω ι acts K}
    (hp : Pruned T) (hp' : Pruned T') (hf : FairBisimΔ T) (hf' : FairBisimΔ T')
    (h : TrEq T T') : BisimΔ T T' := by
  sorry

/-- `Fair_E` passes to every subtree at a decision node (fibers of the subtree embed in fibers of
the tree).
Source: none: infrastructure
Kind: L -/
theorem FairWrt.subtreeAt {E : ι → Tree Ω ι acts K → Tree Ω ι acts K → Prop} :
    (B : Tree Ω ι acts K) → FairWrt E B → ∀ q : B.DecNode, FairWrt E (subtreeAt B q)
  | .leaf _ _, _, q => q.elim
  | .chance _ β child, h, ⟨i, q⟩ => by
      rw [subtreeAt_chance]; exact FairWrt.subtreeAt (child i) (h.chance_child i) q
  | .decision _ _, h, none => by rw [subtreeAt_decision_none]; exact h
  | .decision d child, h, some ⟨a, q⟩ => by
      rw [subtreeAt_decision_some]; exact FairWrt.subtreeAt (child a) (h.decision_child a) q

/-- **EQ-3's corollary, the direction `Fair_{≈tr} ⟹ Fair_{≃Δ}`** on pruned trees — reduced to
the theorem form `bisimΔ_of_trEq_of_fairBisimΔ` (OPEN), on which it rests (listed). The
reduction is proved: strong induction on `size B`; for `q, q'` in a `d`-fiber of `B`, either both
are the root (`BisimΔ.refl`), or exactly one is the root of a `d`-decision `B` and the other a
`d`-node strictly below it — impossible, `B` is almost fair (`FairTr.almostFair`) — or both are
proper subtrees, which are pruned, `Fair_{≈tr}` (`FairWrt.subtreeAt`), hence `Fair_{≃Δ}` by the
induction hypothesis, and `≈_tr` by the fiber; the theorem form then gives `≃_Δ`.
Source: `equiv.md` EQ-3 corollary ("`Fair_{≈tr}(B) ⟺ Fair_{≃Δ}(B)` for every finite pruned `B`")
Kind: OPEN (rests on `bisimΔ_of_trEq_of_fairBisimΔ`; the reduction itself is proved) -/
theorem fairTr_imp_fairBisimΔ [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K) (hp : Pruned B)
    (h : FairTr B) : FairBisimΔ B := by
  suffices key : ∀ n, ∀ B : Tree Ω ι acts K, size B = n → Pruned B → FairTr B → FairBisimΔ B from
    key _ B rfl hp h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B hn hp h d q hq q' hq'
    -- both proper subtrees: the induction hypothesis and the theorem form
    have both : ∀ T T' : Tree Ω ι acts K, size T < n → size T' < n → Pruned T → Pruned T' →
        FairTr T → FairTr T' → TrEq T T' → BisimΔ T T' :=
      fun T T' hT hT' hpT hpT' hfT hfT' htr =>
        bisimΔ_of_trEq_of_fairBisimΔ hpT hpT' (ih _ hT T rfl hpT hfT) (ih _ hT' T' rfl hpT' hfT') htr
    have htr : TrEq (subtreeAt B q) (subtreeAt B q') := h d q hq q' hq'
    subst hn
    -- a `d`-node strictly below the `d`-root of a decision tree contradicts almost fairness
    have below : ∀ (d' : ι) (child : acts d' → Tree Ω ι acts K), B = .decision d' child →
        ∀ (a : acts d') (r : (child a).DecNode), pt (child a) r = d' → False := by
      intro d' child hB a r hr
      subst hB
      have haf := FairTr.almostFair _ h hp
      obtain ⟨ℓ, hℓ⟩ := exists_leaf_below (child a) r
      have hpos := count_pos_of_edge (child a) r ℓ hℓ
      rw [hr] at hpos
      have := haf d' ⟨a, ℓ⟩
      rw [count_decision, if_pos rfl] at this
      omega
    cases B with
    | leaf _ _ => exact q.elim
    | chance n' β child =>
      obtain ⟨i, r⟩ := q
      obtain ⟨j, r'⟩ := q'
      rw [subtreeAt_chance] at htr ⊢
      rw [subtreeAt_chance]
      exact both _ _
        ((size_subtreeAt_le (child i) r).trans_lt (size_child_lt_chance β child i))
        ((size_subtreeAt_le (child j) r').trans_lt (size_child_lt_chance β child j))
        ((hp.chance_child i).subtreeAt r) ((hp.chance_child j).subtreeAt r')
        (FairWrt.subtreeAt _ (h.chance_child i) r) (FairWrt.subtreeAt _ (h.chance_child j) r') htr
    | decision d' child =>
      rw [mem_fiber] at hq hq'
      rcases q with _ | ⟨a, r⟩ <;> rcases q' with _ | ⟨a', r'⟩
      · exact BisimΔ.refl _
      · exact (below d' child rfl a' r' (by simpa using hq'.trans hq.symm)).elim
      · exact (below d' child rfl a r (by simpa using hq.trans hq'.symm)).elim
      · rw [subtreeAt_decision_some] at htr ⊢
        rw [subtreeAt_decision_some]
        exact both _ _
          ((size_subtreeAt_le (child a) r).trans_lt (size_child_lt_decision d' child a))
          ((size_subtreeAt_le (child a') r').trans_lt (size_child_lt_decision d' child a'))
          ((hp.decision_child a).subtreeAt r) ((hp.decision_child a').subtreeAt r')
          (FairWrt.subtreeAt _ (h.decision_child a) r) (FairWrt.subtreeAt _ (h.decision_child a') r')
          htr

/-- **EQ-3's corollary**: `Fair_{≈tr} ↔ Fair_{≃Δ}` on pruned trees — the `⇐` direction is
`FairBisimΔ.fairTr` (proved), the `⇒` direction is `fairTr_imp_fairBisimΔ` (reduced to the OPEN
theorem form `bisimΔ_of_trEq_of_fairBisimΔ`); this statement rests on the open one and is listed
with it.
Source: `equiv.md` EQ-3 corollary
Kind: OPEN -/
theorem fairTr_iff_fairBisimΔ [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K) (hp : Pruned B) :
    FairTr B ↔ FairBisimΔ B :=
  ⟨fairTr_imp_fairBisimΔ B hp, FairBisimΔ.fairTr⟩

/-- **OPEN — EQ-6's Definition-7 clause**: on pruned trees, `≃_Δ`-related subtrees have the same
recording status at every point for every procedure. Route: a positive leaf of `T` with world
in `obs d` corresponds through the flat coupling to a positive leaf of `T'` with the same trace
(so the same `d`-count and the same act-event clauses); the `d`-node on its path corresponds to
a `≃_Δ`-related `d`-node on the other path (the coupling's decision clause, followed down the
draws), and subtree-veridicality transfers because the two nodes' subtrees have the same
positive-leaf world sets (`TrEq.nu_eq` under the uniform procedure on pruned subtrees). Needs
pruning: D8's zero-branch pair is `≃_Δ` with different subtree-veridicality. Not attempted for
time (repair round 1).
Source: `equiv.md` EQ-6 ("Definition-7 statuses"; "Without pruning the claim fails at
Definition 7 (D8's zero-branch pair)")
Kind: OPEN -/
theorem bisimΔ_recordsFor_iff (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
    {T T' : Tree Ω ι acts K} (h : BisimΔ T T') (hp : Pruned T) (hp' : Pruned T')
    (C : Proc ι acts K) (d : ι) :
    RecordsFor obs actEv C T d ↔ RecordsFor obs actEv C T' d := by
  sorry

end eq3

end Cleanroom.Decision.DpFairnessReloc
