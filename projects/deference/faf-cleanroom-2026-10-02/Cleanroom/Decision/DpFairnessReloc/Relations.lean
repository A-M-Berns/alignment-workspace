import Cleanroom.Decision.DpFairnessReloc.Witnesses

/-!
# The six subtree relations (T8: EQ-2, EQ-4, EQ-6, with EQ-3 stated open)

Package `dp-fairness-reloc`, file 10. Definitions of record:

* `≅` — `LabIso` (`Iso.lean`).
* `≃` — **strong probabilistic bisimulation** `Bisim`: constructors match; chance nodes are
  related through a *coupling* `w : Fin n → Fin n' → K` (non-negative, marginals `β`, `β'`)
  supported on bisimilar children (Larsen–Skou lifting, coupling form).
* `≃_Δ` — **bisimulation modulo the chance laws** `BisimΔ`: chance is flattened first
  (`flatDist T`, the distribution on the non-chance descendants reached by chance-only paths,
  with the chance-path weights multiplied — flattening, zero-branch deletion and
  probability-one collapse are built into the flattening), and the two flattened distributions
  are coupled on leaves with equal labels and decision nodes with the same point and pairwise
  `≃_Δ` children. This is Definition 13′'s prose ("chance nodes, after flattening nested chance,
  induce the same distribution on equivalence classes of non-chance descendants, a
  probability-one chance node being identified with its child") rendered directly, without
  constructing the normal form `N`.
* `≈_tr` — equal trace distributions (`traceDist C T : List (Σ d, acts d) × (Ω × K) →₀ K`)
  under every procedure; `≈_law` — equal `contLaw` under every procedure; `≈_val` — equal values
  under every procedure.

Proved: reflexivity and symmetry of each; transitivity of the three semantic relations;
`≅ ⊆ ≃` (a permutation is a coupling); `≃_Δ ⊆ ≈_tr` (the trace distribution is the
`flatDist`-mixture of the non-chance descendants' trace distributions, and coupled descendants
have equal trace distributions); `≈_tr ⊆ ≈_law` (the law is the trace marginal); `≈_law ⊆ ≈_val`.
Witnesses: E1 (`≃` fails, `≃_Δ` holds), E2 (`≅` fails, `≃` holds), E3 (`≈_tr` fails, `≈_law`
holds), SL-β0 (`≈_law` fails, `≈_val` holds). Repair round 1 spread the rest over three files:
transitivity of `≃` and `≃_Δ` in `RelationsThms.lean`; the link `≃ ⊆ ≃_Δ` and the fairness-grade
chain in `RelationsChain.lean`; EQ-6's statistics, EQ-4 and EQ-3 (theorem form and corollary,
open direction) in `RelationsStats.lean`; E4 in `RelationsWitnesses.lean`.
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-! ### `≃`: strong probabilistic bisimulation (coupling form) -/

/-- **Strong probabilistic bisimulation `T ≃ T'`** (definition of record): leaves iff equal
`(ω, r)`; decision nodes iff the same point and children `≃` action by action; chance nodes iff
some coupling of `β` and `β'` is supported on `≃`-related children.
Source: `equiv.md` Definitions carried ("`≃` strong probabilistic bisimulation (Larsen–Skou
lifting; constructors must match)")
Kind: D
Fidelity: exact (the lifting is stated through an explicit coupling) -/
inductive Bisim : Tree Ω ι acts K → Tree Ω ι acts K → Prop
  | leaf (ω : Ω) (r : K) : Bisim (.leaf ω r) (.leaf ω r)
  | decision (d : ι) (child child' : acts d → Tree Ω ι acts K)
      (h : ∀ a, Bisim (child a) (child' a)) : Bisim (.decision d child) (.decision d child')
  | chance {n n' : ℕ} (β : FinDistr K (Fin n)) (β' : FinDistr K (Fin n'))
      (child : Fin n → Tree Ω ι acts K) (child' : Fin n' → Tree Ω ι acts K)
      (w : Fin n → Fin n' → K) (hw : ∀ i j, 0 ≤ w i j)
      (hl : ∀ i, ∑ j, w i j = β.w i) (hr : ∀ j, ∑ i, w i j = β'.w j)
      (h : ∀ i j, w i j ≠ 0 → Bisim (child i) (child' j)) :
      Bisim (.chance n β child) (.chance n' β' child')

theorem Bisim.refl : (T : Tree Ω ι acts K) → Bisim T T
  | .leaf ω r => .leaf ω r
  | .decision d child => .decision d child child fun a => Bisim.refl (child a)
  | .chance _ β child =>
      .chance β β child child (fun i j => if i = j then β.w i else 0)
        (fun i j => by split_ifs <;> [exact β.nonneg i; exact le_rfl])
        (fun i => by simp) (fun j => by simp)
        (fun i j hij => by
          by_cases h : i = j
          · subst h; exact Bisim.refl (child i)
          · exact absurd (by simp [h]) hij)

theorem Bisim.symm {T T' : Tree Ω ι acts K} (h : Bisim T T') : Bisim T' T := by
  induction h with
  | leaf ω r => exact .leaf ω r
  | decision d child child' h ih => exact .decision d child' child ih
  | chance β β' child child' w hw hl hr h ih =>
      exact .chance β' β child' child (fun j i => w i j) (fun j i => hw i j) hr hl
        (fun j i hij => ih i j hij)

/-- `≅ ⊆ ≃`: a permutation is a coupling.
Source: `equiv.md` EQ-2 (the chain)
Kind: P -/
theorem LabIso.bisim {T T' : Tree Ω ι acts K} (h : LabIso T T') : Bisim T T' := by
  induction h with
  | leaf ω r => exact .leaf ω r
  | decision d child child' h ih => exact .decision d child child' ih
  | chance β β' child child' σ hβ h ih =>
      refine .chance β β' child child' (fun i j => if σ i = j then β.w i else 0)
        (fun i j => by split_ifs <;> [exact β.nonneg i; exact le_rfl])
        (fun i => by rw [Finset.sum_ite_eq]; simp)
        (fun j => ?_) (fun i j hij => ?_)
      · rw [Finset.sum_eq_single (σ.symm j)]
        · rw [← hβ (σ.symm j)]; simp
        · intro i _ hi
          rw [if_neg]
          intro h; exact hi (by rw [← h]; simp)
        · intro h; exact absurd (Finset.mem_univ _) h
      · by_cases hs : σ i = j
        · subst hs; exact ih i
        · exact absurd (by simp [hs]) hij

/-! ### Flattening and `≃_Δ` -/

open Classical in
/-- **The flattened chance distribution** of a tree: the distribution on its non-chance
descendants reached by chance-only paths, weighted by the chance-path products. Chance-of-chance
is flattened, zero-weight branches contribute nothing, a probability-one chance node is its
child, and equal descendants are merged (the weights add).
Source: `equiv.md` Definitions carried ("Chance-normal form `N(T)` (bottom-up): flatten
chance-of-chance, drop zero-probability branches, merge … summing probabilities, delete
probability-one chance nodes"), rendered as a distribution rather than a normal-form tree
Kind: D
Fidelity: variant: the normal form `N` is not constructed; `flatDist` is the distribution `N`
would present, with merging by term equality of the non-chance descendants -/
noncomputable def flatDist : Tree Ω ι acts K → (Tree Ω ι acts K →₀ K)
  | .leaf ω r => Finsupp.single (.leaf ω r) 1
  | .decision d child => Finsupp.single (.decision d child) 1
  | .chance _ β child => ∑ i, β.w i • flatDist (child i)

theorem flatDist_leaf (ω : Ω) (r : K) :
    flatDist (.leaf ω r : Tree Ω ι acts K) = Finsupp.single (.leaf ω r) 1 := rfl

theorem flatDist_decision (d : ι) (child : acts d → Tree Ω ι acts K) :
    flatDist (.decision d child) = Finsupp.single (.decision d child) 1 := rfl

theorem flatDist_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K) :
    flatDist (.chance n β child) = ∑ i, β.w i • flatDist (child i) := rfl

/-- A tree is *non-chance* if its root is a leaf or a decision node.
Source: `equiv.md` Definitions carried ("non-chance descendants")
Kind: D -/
def NonChance : Tree Ω ι acts K → Prop
  | .leaf _ _ => True
  | .decision _ _ => True
  | .chance _ _ _ => False

theorem flatDist_nonneg : (T : Tree Ω ι acts K) → ∀ S, 0 ≤ flatDist T S
  | .leaf _ _, S => by
      rw [flatDist_leaf]; classical
      rw [Finsupp.single_apply]; split_ifs <;> norm_num
  | .decision _ _, S => by
      rw [flatDist_decision]; classical
      rw [Finsupp.single_apply]; split_ifs <;> norm_num
  | .chance _ β child, S => by
      rw [flatDist_chance, Finsupp.finsetSum_apply]
      exact Finset.sum_nonneg fun i _ => by
        rw [Finsupp.smul_apply, smul_eq_mul]
        exact mul_nonneg (β.nonneg i) (flatDist_nonneg (child i) S)

theorem nonChance_of_mem_support_flatDist :
    (T : Tree Ω ι acts K) → ∀ S ∈ (flatDist T).support, NonChance S
  | .leaf ω r, S, hS => by
      rw [flatDist_leaf, Finsupp.mem_support_iff] at hS
      classical
      rw [Finsupp.single_apply] at hS
      split_ifs at hS with h
      · rw [← h]; trivial
      · exact absurd rfl hS
  | .decision d child, S, hS => by
      rw [flatDist_decision, Finsupp.mem_support_iff] at hS
      classical
      rw [Finsupp.single_apply] at hS
      split_ifs at hS with h
      · rw [← h]; trivial
      · exact absurd rfl hS
  | .chance _ β child, S, hS => by
      rw [flatDist_chance, Finsupp.mem_support_iff, Finsupp.finsetSum_apply] at hS
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
      rw [Finsupp.smul_apply, smul_eq_mul] at hi
      exact nonChance_of_mem_support_flatDist (child i) S
        (Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hi))

/-- **Bisimulation modulo the chance laws `T ≃_Δ T'`** (definition of record): a coupling of the
two flattened distributions, supported on pairs of equal leaves or of decision nodes carrying the
same point with pairwise `≃_Δ` children.
Source: `equiv.md` Definitions carried (`≃_Δ := N(T) ≃ N(T')`); `v2-amendments.md` Definition
13′ ("bisimilar modulo the chance laws: leaves match on `(λ, r)`; decision nodes carry the same
point and have equivalent children action by action; chance nodes, after flattening nested
chance, induce the same distribution on equivalence classes of non-chance descendants, a
probability-one chance node being identified with its child")
Kind: D
Fidelity: variant: Definition 13′'s prose rendered directly on `flatDist`, without `N` -/
inductive BisimΔ : Tree Ω ι acts K → Tree Ω ι acts K → Prop
  | mk (T T' : Tree Ω ι acts K)
      (W : ↥(flatDist T).support → ↥(flatDist T').support → K) (hw : ∀ i j, 0 ≤ W i j)
      (hl : ∀ i, ∑ j, W i j = flatDist T i) (hr : ∀ j, ∑ i, W i j = flatDist T' j)
      (hleaf : ∀ i j, W i j ≠ 0 → ∀ ω r, (i : Tree Ω ι acts K) = .leaf ω r → (j : Tree Ω ι acts K) = .leaf ω r)
      (hleaf' : ∀ i j, W i j ≠ 0 → ∀ ω r, (j : Tree Ω ι acts K) = .leaf ω r → (i : Tree Ω ι acts K) = .leaf ω r)
      (hpt : ∀ i j, W i j ≠ 0 → ∀ d c d' c', (i : Tree Ω ι acts K) = .decision d c →
        (j : Tree Ω ι acts K) = .decision d' c' → d = d')
      (hdec : ∀ i j, W i j ≠ 0 → ∀ d c c', (i : Tree Ω ι acts K) = .decision d c →
        (j : Tree Ω ι acts K) = .decision d c' → ∀ a, BisimΔ (c a) (c' a)) :
      BisimΔ T T'

theorem size_le_of_mem_support_flatDist [∀ d, Fintype (acts d)] :
    (T : Tree Ω ι acts K) → ∀ S ∈ (flatDist T).support, size S ≤ size T
  | .leaf ω r, S, hS => by
      rw [flatDist_leaf, Finsupp.mem_support_iff] at hS
      classical
      rw [Finsupp.single_apply] at hS
      split_ifs at hS with h
      · rw [← h]
      · exact absurd rfl hS
  | .decision d child, S, hS => by
      rw [flatDist_decision, Finsupp.mem_support_iff] at hS
      classical
      rw [Finsupp.single_apply] at hS
      split_ifs at hS with h
      · rw [← h]
      · exact absurd rfl hS
  | .chance _ β child, S, hS => by
      rw [flatDist_chance, Finsupp.mem_support_iff, Finsupp.finsetSum_apply] at hS
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
      rw [Finsupp.smul_apply, smul_eq_mul] at hi
      exact (size_le_of_mem_support_flatDist (child i) S
        (Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hi))).trans
        (size_child_lt_chance β child i).le

/-- The diagonal coupling: two trees with equal flattenings are `≃_Δ` (in particular `≃_Δ` is
reflexive).
Source: none: infrastructure
Kind: L -/
theorem BisimΔ.of_flatDist_eq_aux [∀ d, Fintype (acts d)] :
    ∀ n, ∀ T T' : Tree Ω ι acts K, size T ≤ n → flatDist T = flatDist T' → BisimΔ T T' := by
  intro n
  induction n with
  | zero =>
      intro T _ hT
      have := one_le_size T
      omega
  | succ n ih =>
      intro T T' hT hflat
      classical
      have hsupp : (flatDist T).support = (flatDist T').support := by rw [hflat]
      refine .mk T T' (fun i j => if (i : Tree Ω ι acts K) = j then flatDist T i else 0)
        (fun i j => by split_ifs <;> [exact flatDist_nonneg T i; exact le_rfl])
        (fun i => ?_) (fun j => ?_) ?_ ?_ ?_ ?_
      · rw [Finset.sum_eq_single ⟨(i : Tree Ω ι acts K), by rw [← hsupp]; exact i.2⟩]
        · simp
        · intro j _ hj
          rw [if_neg]
          intro h; exact hj (Subtype.ext h.symm)
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [Finset.sum_eq_single ⟨(j : Tree Ω ι acts K), by rw [hsupp]; exact j.2⟩]
        · simp [hflat]
        · intro i _ hi
          rw [if_neg]
          intro h; exact hi (Subtype.ext h)
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro i j hij ω r hi
        by_cases h : (i : Tree Ω ι acts K) = j
        · rw [← h]; exact hi
        · exact absurd (by simp [h]) hij
      · intro i j hij ω r hj
        by_cases h : (i : Tree Ω ι acts K) = j
        · rw [h]; exact hj
        · exact absurd (by simp [h]) hij
      · intro i j hij d c d' c' hi hj
        by_cases h : (i : Tree Ω ι acts K) = j
        · rw [h, hj] at hi; exact (Tree.decision.inj hi).1.symm
        · exact absurd (by simp [h]) hij
      · intro i j hij d c c' hi hj a
        by_cases h : (i : Tree Ω ι acts K) = j
        · have hi' := hi
          rw [h, hj] at hi'
          have hcc := (Tree.decision.inj hi').2
          rw [heq_iff_eq] at hcc
          rw [hcc]
          refine ih (c a) (c a) ?_ rfl
          have h1 := size_child_lt_decision d c a
          have h2 := size_le_of_mem_support_flatDist T i i.2
          rw [hi] at h2
          omega
        · exact absurd (by simp [h]) hij

theorem BisimΔ.of_flatDist_eq [∀ d, Fintype (acts d)] {T T' : Tree Ω ι acts K}
    (h : flatDist T = flatDist T') : BisimΔ T T' :=
  BisimΔ.of_flatDist_eq_aux (size T) T T' le_rfl h

theorem BisimΔ.refl [∀ d, Fintype (acts d)] (T : Tree Ω ι acts K) : BisimΔ T T :=
  BisimΔ.of_flatDist_eq rfl

theorem BisimΔ.symm {T T' : Tree Ω ι acts K} (h : BisimΔ T T') : BisimΔ T' T := by
  induction h with
  | mk T T' W hw hl hr hleaf hleaf' hpt hdec ih =>
      exact .mk T' T (fun j i => W i j) (fun j i => hw i j) hr hl
        (fun j i hij ω r hj => hleaf' i j hij ω r hj) (fun j i hij ω r hi => hleaf i j hij ω r hi)
        (fun j i hij d c d' c' hj hi => (hpt i j hij d' c' d c hi hj).symm)
        (fun j i hij d c c' hj hi a => ih i j hij d c' c hi hj a)

/-! ### The semantic relations -/

section semantic

variable [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-- **The trace distribution** of `C` on `T`: the law of the consultation trace
`((d₁,a₁), …, (d_k,a_k), (λ(ℓ), r(ℓ)))` (chance steps invisible).
Source: `equiv.md` Headline ("the run distribution over consultation traces
`((d₁,a₁),…,(d_k,a_k),(λ,r))` for every procedure")
Kind: D -/
noncomputable def traceDist (C : Proc ι acts K) (T : Tree Ω ι acts K) :
    List (Σ d : ι, acts d) × (Ω × K) →₀ K :=
  ∑ ℓ, Finsupp.single (draws T ℓ, (world T ℓ, payoff T ℓ)) (leafLaw C T ℓ)

/-- `≈_tr`: equal trace distributions under every procedure.
Source: `equiv.md` Definitions carried (`≈_tr`)
Kind: D -/
def TrEq (T T' : Tree Ω ι acts K) : Prop := ∀ C : Proc ι acts K, traceDist C T = traceDist C T'

/-- `≈_law`: equal continuation laws under every procedure.
Source: `equiv.md` Definitions carried (`≈_law`)
Kind: D -/
def LawEq (T T' : Tree Ω ι acts K) : Prop := ∀ C : Proc ι acts K, contLaw C T = contLaw C T'

/-- `≈_val`: equal values under every procedure.
Source: `equiv.md` Definitions carried (`≈_val`)
Kind: D -/
def ValEq (T T' : Tree Ω ι acts K) : Prop := ∀ C : Proc ι acts K, value C T = value C T'

theorem TrEq.equivalence : Equivalence (TrEq (Ω := Ω) (ι := ι) (acts := acts) (K := K)) :=
  ⟨fun _ _ => rfl, fun h C => (h C).symm, fun h h' C => (h C).trans (h' C)⟩

theorem LawEq.equivalence : Equivalence (LawEq (Ω := Ω) (ι := ι) (acts := acts) (K := K)) :=
  ⟨fun _ _ => rfl, fun h C => (h C).symm, fun h h' C => (h C).trans (h' C)⟩

theorem ValEq.equivalence : Equivalence (ValEq (Ω := Ω) (ι := ι) (acts := acts) (K := K)) :=
  ⟨fun _ _ => rfl, fun h C => (h C).symm, fun h h' C => (h C).trans (h' C)⟩

/-- The continuation law is the `(λ, r)`-marginal of the trace distribution.
Source: `equiv.md` EQ-2 (`≈_tr ⊆ ≈_law`)
Kind: L -/
theorem contLaw_eq_traceDist_marginal (C : Proc ι acts K) (T : Tree Ω ι acts K) :
    contLaw C T = (traceDist C T).sum fun τ v => Finsupp.single τ.2 v := by
  unfold contLaw traceDist
  rw [← Finsupp.sum_finsetSum_index (fun _ => Finsupp.single_zero _)
    (fun _ _ _ => Finsupp.single_add _ _ _)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finsupp.sum_single_index (Finsupp.single_zero _)]

/-- `≈_tr ⊆ ≈_law`.
Source: `equiv.md` EQ-2
Kind: C -/
theorem TrEq.lawEq {T T' : Tree Ω ι acts K} (h : TrEq T T') : LawEq T T' := fun C => by
  rw [contLaw_eq_traceDist_marginal, contLaw_eq_traceDist_marginal, h C]

/-- `≈_law ⊆ ≈_val`.
Source: `equiv.md` EQ-2
Kind: C -/
theorem LawEq.valEq {T T' : Tree Ω ι acts K} (h : LawEq T T') : ValEq T T' := fun C =>
  value_eq_of_contLaw_eq C (h C)

theorem traceDist_chance (C : Proc ι acts K) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) :
    traceDist C (.chance n β child) = ∑ i, β.w i • traceDist C (child i) := by
  unfold traceDist
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp [Finsupp.smul_single]

/-- The trace distribution is the `flatDist`-mixture of the non-chance descendants' trace
distributions.
Source: `equiv.md` EQ-6 proof idea (chance steps are invisible to traces)
Kind: P -/
theorem traceDist_eq_flatDist_sum (C : Proc ι acts K) :
    (T : Tree Ω ι acts K) → traceDist C T = (flatDist T).sum fun S v => v • traceDist C S
  | .leaf ω r => by
      rw [flatDist_leaf, Finsupp.sum_single_index] <;> simp
  | .decision d child => by
      rw [flatDist_decision, Finsupp.sum_single_index] <;> simp
  | .chance _ β child => by
      rw [traceDist_chance, flatDist_chance,
        ← Finsupp.sum_finsetSum_index (h := fun S v => v • traceDist C S) (fun _ => zero_smul _ _)
          (fun _ _ _ => add_smul _ _ _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.sum_smul_index' (h := fun S v => v • traceDist C S) (fun _ => zero_smul _ _),
        traceDist_eq_flatDist_sum C (child i), Finsupp.smul_sum]
      refine Finsupp.sum_congr fun S _ => ?_
      rw [smul_eq_mul, mul_smul]

/-- Two non-chance trees matched by `≃_Δ`'s clauses have the same trace distribution, given the
children do.
Source: none: infrastructure
Kind: L -/
theorem traceDist_decision (C : Proc ι acts K) (d : ι) (child : acts d → Tree Ω ι acts K) :
    traceDist C (.decision d child) =
      ∑ a, (C d).w a • (traceDist C (child a)).sum fun τ v =>
        Finsupp.single ((⟨d, a⟩ : Σ d, acts d) :: τ.1, τ.2) v := by
  unfold traceDist
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finsupp.sum_finsetSum_index (fun _ => Finsupp.single_zero _)
    (fun _ _ _ => Finsupp.single_add _ _ _), Finset.smul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finsupp.sum_single_index (Finsupp.single_zero _)]
  simp only [draws_decision, world_decision, payoff_decision, leafLaw_decision, Finsupp.smul_single,
    smul_eq_mul]

/-- **`≃_Δ ⊆ ≈_tr`**: coupled flattenings with equal traces on the support give equal trace
distributions.
Source: `equiv.md` EQ-2 (`≃_Δ ⊆ ≈_tr`), EQ-6
Kind: P
Fidelity: exact -/
theorem BisimΔ.trEq {T T' : Tree Ω ι acts K} (h : BisimΔ T T') : TrEq T T' := by
  induction h with
  | mk T T' W hw hl hr hleaf hleaf' hpt hdec ih =>
      intro C
      rw [traceDist_eq_flatDist_sum, traceDist_eq_flatDist_sum]
      -- write both sums over the supports and couple them
      have hsum : ∀ (μ : Tree Ω ι acts K →₀ K) (F : Tree Ω ι acts K → List (Σ d, acts d) × (Ω × K) →₀ K),
          (μ.sum fun S v => v • F S) = ∑ i : ↥μ.support, μ i • F i := by
        intro μ F
        unfold Finsupp.sum
        rw [← Finset.sum_coe_sort]
      rw [hsum, hsum]
      -- the coupled pairs have equal trace distributions
      have hpair : ∀ i j, W i j ≠ 0 →
          traceDist C (i : Tree Ω ι acts K) = traceDist C (j : Tree Ω ι acts K) := by
        intro i j hij
        have hi := nonChance_of_mem_support_flatDist T i i.2
        have hj := nonChance_of_mem_support_flatDist T' j j.2
        rcases hS : (i : Tree Ω ι acts K) with ⟨ω, r⟩ | ⟨n, β, c⟩ | ⟨d, c⟩
        · rw [hleaf i j hij ω r hS]
        · rw [hS] at hi; exact hi.elim
        · rcases hS' : (j : Tree Ω ι acts K) with ⟨ω', r'⟩ | ⟨n', β', c'⟩ | ⟨d', c'⟩
          · have := hleaf' i j hij ω' r' hS'
            rw [hS] at this
            cases this
          · rw [hS'] at hj; exact hj.elim
          · have hd := hpt i j hij d c d' c' hS hS'
            subst hd
            rw [traceDist_decision, traceDist_decision]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [ih i j hij d c c' hS hS' a C]
      calc (∑ i : ↥(flatDist T).support, flatDist T i • traceDist C (i : Tree Ω ι acts K))
          = ∑ i : ↥(flatDist T).support, ∑ j : ↥(flatDist T').support,
              W i j • traceDist C (i : Tree Ω ι acts K) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← hl i, Finset.sum_smul]
        _ = ∑ i : ↥(flatDist T).support, ∑ j : ↥(flatDist T').support,
              W i j • traceDist C (j : Tree Ω ι acts K) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            by_cases hij : W i j = 0
            · rw [hij, zero_smul, zero_smul]
            · rw [hpair i j hij]
        _ = ∑ j : ↥(flatDist T').support, flatDist T' j • traceDist C (j : Tree Ω ι acts K) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← hr j, Finset.sum_smul]

end semantic

/-! ### Witnesses: the strict inclusions -/

section witnesses

/-- E1 `split_vs_leaf`: a probability-one chance node over a leaf, versus the leaf.
Source: `equiv.md` EQ-2 (E1 "`bis:n bisΔ:Y`")
Kind: D -/
def e1Split : Tree Unit Unit (fun _ => Act2) ℚ :=
  .chance 1 (FinDistr.pure 0) fun _ => .leaf () 1

def e1Leaf : Tree Unit Unit (fun _ => Act2) ℚ := .leaf () 1

/-- E1: `≃` fails (constructors differ) …
Source: `equiv.md` EQ-2
Kind: N+ -/
theorem e1_not_bisim : ¬ Bisim e1Split e1Leaf := by
  intro h; cases h

/-- … while `≃_Δ` holds (the flattenings are both `δ_{leaf}`).
Source: `equiv.md` EQ-2 ("E1 `bis:n bisΔ:Y`")
Kind: N+ -/
theorem e1_bisimΔ : BisimΔ e1Split e1Leaf := by
  apply BisimΔ.of_flatDist_eq
  unfold e1Split e1Leaf
  rw [flatDist_chance, flatDist_leaf, Fin.sum_univ_one]
  simp

/-- E2 `split_probs`: a fair coin over two copies of a leaf, versus a `(¼, ¾)` coin over the same
two copies.
Source: `equiv.md` EQ-2 (E2 "`iso:n bis:Y`")
Kind: D -/
def e2Fair : Tree Unit Unit (fun _ => Act2) ℚ := .chance 2 FinDistr.fair fun _ => .leaf () 1

def e2Skew : Tree Unit Unit (fun _ => Act2) ℚ :=
  .chance 2 (FinDistr.coin (1/4) (by norm_num) (by norm_num)) fun _ => .leaf () 1

/-- E2: `≅` fails (the weights `½` and `¼, ¾` cannot be matched by a permutation) …
Source: `equiv.md` EQ-2
Kind: N+ -/
theorem e2_not_iso : ¬ LabIso e2Fair e2Skew := by
  intro h
  cases h with
  | chance _ _ _ _ σ hβ _ =>
      have h0 := hβ 0
      revert h0
      generalize σ 0 = k
      intro h0
      fin_cases k <;> simp [FinDistr.fair, FinDistr.coin] at h0 <;> norm_num at h0

/-- … while `≃` holds (the product coupling: both children are the same leaf).
Source: `equiv.md` EQ-2 ("E2 `iso:n bis:Y`")
Kind: N+ -/
theorem e2_bisim : Bisim e2Fair e2Skew := by
  unfold e2Fair e2Skew
  refine .chance _ _ _ _ (fun i j => FinDistr.fair.w i * (FinDistr.coin (1/4) (by norm_num) (by norm_num)).w j)
    (fun i j => mul_nonneg (FinDistr.nonneg _ i) (FinDistr.nonneg _ j))
    (fun i => by rw [← Finset.mul_sum, FinDistr.sum_one, mul_one])
    (fun j => by rw [← Finset.sum_mul, FinDistr.sum_one, one_mul])
    (fun i j _ => Bisim.refl _)

/-- E3 `spurious_query`: a decision node all of whose children are the same leaf, versus the leaf.
Source: `equiv.md` EQ-2 (E3 "`tr:n law:Y`")
Kind: D -/
def e3Query : Tree Unit Unit (fun _ => Act2) ℚ := .decision () fun _ => .leaf () 1

def e3Leaf : Tree Unit Unit (fun _ => Act2) ℚ := .leaf () 1

/-- E3: `≈_law` holds (the spurious query changes no `(λ, r)`-mass) …
Source: `equiv.md` EQ-2 ("E3 `tr:n law:Y`")
Kind: N+ -/
theorem e3_lawEq : LawEq e3Query e3Leaf := by
  intro C
  unfold e3Query e3Leaf
  rw [contLaw_decision, Act2.sum_univ]
  simp only [contLaw_leaf, ← add_smul]
  have := (C ()).sum_one
  rw [Act2.sum_univ] at this
  rw [this, one_smul]

/-- … while `≈_tr` fails (the trace of the query carries a `(d, a)` event the leaf has not).
Source: `equiv.md` EQ-2
Kind: N+ -/
theorem e3_not_trEq : ¬ TrEq e3Query e3Leaf := by
  intro h
  have := congrArg (fun f => f ([], ((), 1))) (h (pureProc .a))
  (try simp only at this)
  unfold traceDist e3Query e3Leaf at this
  rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf,
    Tree.sum_leaves_leaf] at this
  simp [Finsupp.single_apply] at this

/-- Smoking-Lesion `β = 0` shape: two subtrees with the same payoff law but different world laws
(`¾` vs `¼` on `ω₁`).
Source: `equiv.md` EQ-2 ("Smoking Lesion S3 with `β = 0` `law:n val:Y` … world laws `γ₁ = ¾`
vs `γ₀ = ¼`")
Kind: D -/
def slL (m : ℚ) : Tree Bool Unit (fun _ => Act2) ℚ :=
  .chance 2 (FinDistr.coin (3/4) (by norm_num) (by norm_num)) fun i => .leaf (i = 0) m

def slR (m : ℚ) : Tree Bool Unit (fun _ => Act2) ℚ :=
  .chance 2 (FinDistr.coin (1/4) (by norm_num) (by norm_num)) fun i => .leaf (i = 0) m

/-- SL-β0: `≈_val` holds (both are worth `m`) …
Source: `equiv.md` EQ-2 ("values `m | m`")
Kind: N+ -/
theorem sl_valEq (m : ℚ) : ValEq (slL m) (slR m) := by
  intro C
  unfold value slL slR
  rw [sum_leaves_chance, sum_leaves_chance, Fin.sum_univ_two, Fin.sum_univ_two,
    Tree.sum_leaves_leaf, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  show (FinDistr.coin (3/4) (by norm_num) (by norm_num)).w 0 * 1 * m +
      (FinDistr.coin (3/4) (by norm_num) (by norm_num)).w 1 * 1 * m =
    (FinDistr.coin (1/4) (by norm_num) (by norm_num)).w 0 * 1 * m +
      (FinDistr.coin (1/4) (by norm_num) (by norm_num)).w 1 * 1 * m
  rw [coin_w_zero, coin_w_one, coin_w_zero, coin_w_one]
  ring

/-- … while `≈_law` fails (the world laws differ).
Source: `equiv.md` EQ-2 ("world laws `γ₁ = ¾` vs `γ₀ = ¼`")
Kind: N+ -/
theorem sl_not_lawEq (m : ℚ) : ¬ LawEq (slL m) (slR m) := by
  intro h
  have := congrArg (fun f => f (true, m)) (h (pureProc .a))
  (try simp only at this)
  rw [contLaw_apply, contLaw_apply] at this
  unfold slL slR at this
  rw [sum_leaves_chance, sum_leaves_chance, Fin.sum_univ_two, Fin.sum_univ_two,
    Tree.sum_leaves_leaf, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf] at this
  change (if ((decide ((0 : Fin 2) = 0)), m) = (true, m) then
        (FinDistr.coin (3/4) (by norm_num) (by norm_num)).w 0 * 1 else 0) +
      (if ((decide ((1 : Fin 2) = 0)), m) = (true, m) then
        (FinDistr.coin (3/4) (by norm_num) (by norm_num)).w 1 * 1 else 0) =
    (if ((decide ((0 : Fin 2) = 0)), m) = (true, m) then
        (FinDistr.coin (1/4) (by norm_num) (by norm_num)).w 0 * 1 else 0) +
      (if ((decide ((1 : Fin 2) = 0)), m) = (true, m) then
        (FinDistr.coin (1/4) (by norm_num) (by norm_num)).w 1 * 1 else 0) at this
  rw [coin_w_zero, coin_w_one, coin_w_zero, coin_w_one] at this
  norm_num at this

end witnesses

/-! ### `Fair_E` for the structural and trace relations -/

/-- `Fair_E` for `≃_Δ`.
Source: `equiv.md` Definitions carried (`Fair_E(B)`)
Kind: D -/
def FairBisimΔ [DecidableEq ι] [∀ d, Fintype (acts d)] (B : Tree Ω ι acts K) : Prop :=
  FairWrt (fun _ => BisimΔ) B

/-- `Fair_E` for `≈_tr`.
Source: `equiv.md` Definitions carried (`Fair_E(B)`)
Kind: D -/
def FairTr [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
    (B : Tree Ω ι acts K) : Prop :=
  FairWrt (fun _ => TrEq) B

/-- `Fair_E` for `≃`.
Source: `equiv.md` Definitions carried (`Fair_E(B)`)
Kind: D -/
def FairBisim [DecidableEq ι] [∀ d, Fintype (acts d)] (B : Tree Ω ι acts K) : Prop :=
  FairWrt (fun _ => Bisim) B

end Cleanroom.Decision.DpFairnessReloc
