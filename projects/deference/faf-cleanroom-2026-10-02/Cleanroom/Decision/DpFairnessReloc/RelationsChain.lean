import Cleanroom.Decision.DpFairnessReloc.RelationsThms

/-!
# `≃ ⊆ ≃_Δ` and the fairness grades along the chain (repair round 1)

Package `dp-fairness-reloc`, file 11b. Over `RelationsThms.lean` (coupling composition, the
transitivity of `≃` and `≃_Δ`, flat couplings as total functions): the point coupling of two
non-chance trees (`BisimΔ.of_nonChance_pair`), the product coupling of a chance node's coupling
with the children's flat couplings (`Bisim.bisimΔ`, the link `≃ ⊆ ≃_Δ` that closes EQ-2's
chain), and the grades `Fair_≅ ⟹ Fair_≃ ⟹ Fair_{≃Δ} ⟹ Fair_{≈tr} ⟹ Fair_{≈law}` — the last
step being the proved direction of EQ-3's corollary.
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-- The flattening of a non-chance tree is the point mass at the tree.
Source: none: infrastructure
Kind: L -/
theorem flatDist_eq_single_of_nonChance {T : Tree Ω ι acts K} (h : NonChance T) :
    flatDist T = Finsupp.single T 1 := by
  cases T with
  | leaf ω r => rfl
  | chance _ _ _ => exact h.elim
  | decision d c => rfl

/-- Two non-chance trees matched by Definition 13′'s clauses are `≃_Δ` (the point coupling).
Source: none: infrastructure
Kind: L -/
theorem BisimΔ.of_nonChance_pair {T T' : Tree Ω ι acts K} (hT : NonChance T) (hT' : NonChance T')
    (hleaf : ∀ ω r, T = .leaf ω r → T' = .leaf ω r)
    (hleaf' : ∀ ω r, T' = .leaf ω r → T = .leaf ω r)
    (hpt : ∀ d c d' c', T = .decision d c → T' = .decision d' c' → d = d')
    (hdec : ∀ d c c', T = .decision d c → T' = .decision d c' → ∀ a, BisimΔ (c a) (c' a)) :
    BisimΔ T T' := by
  classical
  have hs : (flatDist T).support = {T} := by
    rw [flatDist_eq_single_of_nonChance hT, Finsupp.support_single _ one_ne_zero]
  have hs' : (flatDist T').support = {T'} := by
    rw [flatDist_eq_single_of_nonChance hT', Finsupp.support_single _ one_ne_zero]
  have hne : ∀ S S', (if S = T ∧ S' = T' then (1 : K) else 0) ≠ 0 → S = T ∧ S' = T' := by
    intro S S' h
    by_cases hc : S = T ∧ S' = T'
    · exact hc
    · exact absurd (if_neg hc) h
  refine BisimΔ.of_flatCoupling (W := fun S S' => if S = T ∧ S' = T' then 1 else 0)
    ⟨fun S S' => by split_ifs <;> norm_num, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
  · intro S S' hS
    rw [hs, Finset.mem_singleton] at hS
    exact if_neg fun h => hS h.1
  · intro S S' hS'
    rw [hs', Finset.mem_singleton] at hS'
    exact if_neg fun h => hS' h.2
  · intro S
    rw [hs', Finset.sum_singleton, flatDist_eq_single_of_nonChance hT, Finsupp.single_apply]
    by_cases hS : S = T
    · simp [hS]
    · simp [hS, Ne.symm hS]
  · intro S'
    rw [hs, Finset.sum_singleton, flatDist_eq_single_of_nonChance hT', Finsupp.single_apply]
    by_cases hS' : S' = T'
    · simp [hS']
    · simp [hS', Ne.symm hS']
  · intro S S' h ω r hS
    obtain ⟨rfl, rfl⟩ := hne S S' h
    exact hleaf ω r hS
  · intro S S' h ω r hS'
    obtain ⟨rfl, rfl⟩ := hne S S' h
    exact hleaf' ω r hS'
  · intro S S' h d c d' c' hS hS'
    obtain ⟨rfl, rfl⟩ := hne S S' h
    exact hpt d c d' c' hS hS'
  · intro S S' h d c c' hS hS' a
    obtain ⟨rfl, rfl⟩ := hne S S' h
    exact hdec d c c' hS hS' a

/-- Below a chance edge of positive weight, the child's flattening support lies in the parent's.
Source: none: infrastructure
Kind: L -/
theorem support_flatDist_child_subset {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) {i : Fin n} (hi : 0 < β.w i) :
    (flatDist (child i)).support ⊆ (flatDist (.chance n β child)).support := by
  intro S hS
  rw [Finsupp.mem_support_iff] at hS ⊢
  rw [flatDist_chance, Finsupp.finsetSum_apply]
  have hpos : 0 < β.w i * flatDist (child i) S :=
    mul_pos hi (lt_of_le_of_ne (flatDist_nonneg _ _) (Ne.symm hS))
  refine ne_of_gt (lt_of_lt_of_le hpos ?_)
  refine Finset.single_le_sum (f := fun k => (β.w k • flatDist (child k)) S) ?_ (Finset.mem_univ i)
  intro k _
  rw [Finsupp.smul_apply, smul_eq_mul]
  exact mul_nonneg (β.nonneg k) (flatDist_nonneg _ _)

/-- **`≃ ⊆ ≃_Δ`**: a chance node's coupling, multiplied with the children's flat couplings,
couples the flattenings; leaves and decision nodes use the point coupling.
Source: `equiv.md` EQ-2 (the chain)
Kind: P
Fidelity: exact -/
theorem Bisim.bisimΔ [∀ d, Fintype (acts d)] {T T' : Tree Ω ι acts K} (h : Bisim T T') :
    BisimΔ T T' := by
  induction h with
  | leaf ω r => exact BisimΔ.refl _
  | decision d child child' h ih =>
      refine BisimΔ.of_nonChance_pair trivial trivial (fun ω r h => by cases h)
        (fun ω r h => by cases h) (fun d₀ c d' c' h h' => ?_) (fun d₀ c c' h h' a => ?_)
      · exact (Tree.decision.inj h).1.symm.trans (Tree.decision.inj h').1
      · obtain ⟨rfl, hc⟩ := Tree.decision.inj h
        obtain ⟨-, hc'⟩ := Tree.decision.inj h'
        rw [heq_iff_eq] at hc hc'
        rw [← hc, ← hc']
        exact ih a
  | chance β β' child child' w hw hl hr h ih =>
      classical
      choose Wc hWc using fun i j (hij : w i j ≠ 0) => (ih i j hij).exists_flatCoupling
      let Wij : ∀ i j, Tree Ω ι acts K → Tree Ω ι acts K → K := fun i j =>
        if hij : w i j ≠ 0 then Wc i j hij else fun _ _ => 0
      have hWij : ∀ i j (hij : w i j ≠ 0), Wij i j = Wc i j hij := fun i j hij => dif_pos hij
      have hWij0 : ∀ i j, w i j = 0 → Wij i j = fun _ _ => 0 := fun i j hij =>
        dif_neg (not_not.mpr hij)
      have hβ : ∀ i j, w i j ≠ 0 → 0 < β.w i := by
        intro i j hij
        rw [← hl i]
        exact lt_of_lt_of_le (lt_of_le_of_ne (hw i j) (Ne.symm hij))
          (Finset.single_le_sum (fun k _ => hw i k) (Finset.mem_univ j))
      have hβ' : ∀ i j, w i j ≠ 0 → 0 < β'.w j := by
        intro i j hij
        rw [← hr j]
        exact lt_of_lt_of_le (lt_of_le_of_ne (hw i j) (Ne.symm hij))
          (Finset.single_le_sum (fun k _ => hw k j) (Finset.mem_univ i))
      -- a non-zero entry of the product coupling comes from a non-zero child entry
      have hprod : ∀ S S', (∑ i, ∑ j, w i j * Wij i j S S') ≠ 0 →
          ∃ i j, ∃ hij : w i j ≠ 0, Wc i j hij S S' ≠ 0 := by
        intro S S' hne
        obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
        obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
        have hij : w i j ≠ 0 := left_ne_zero_of_mul hj
        refine ⟨i, j, hij, ?_⟩
        rw [hWij i j hij] at hj
        exact right_ne_zero_of_mul hj
      refine BisimΔ.of_flatCoupling (W := fun S S' => ∑ i, ∑ j, w i j * Wij i j S S')
        ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
      · intro S S'
        refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hw i j) ?_
        by_cases hij : w i j ≠ 0
        · rw [hWij i j hij]; exact (hWc i j hij).1.nonneg S S'
        · rw [hWij0 i j (not_not.mp hij)]
      · intro S S' hS
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        by_cases hij : w i j ≠ 0
        · rw [hWij i j hij, (hWc i j hij).1.zero_left S S', mul_zero]
          exact fun hS' => hS (support_flatDist_child_subset β child (hβ i j hij) hS')
        · rw [not_not.mp hij, zero_mul]
      · intro S S' hS'
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        by_cases hij : w i j ≠ 0
        · rw [hWij i j hij, (hWc i j hij).1.zero_right S S', mul_zero]
          exact fun hS => hS' (support_flatDist_child_subset β' child' (hβ' i j hij) hS)
        · rw [not_not.mp hij, zero_mul]
      · intro S
        calc (∑ S' ∈ (flatDist (.chance _ β' child')).support, ∑ i, ∑ j, w i j * Wij i j S S')
            = ∑ i, ∑ j, ∑ S' ∈ (flatDist (.chance _ β' child')).support, w i j * Wij i j S S' := by
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
          _ = ∑ i, (β.w i • flatDist (child i)) S := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finsupp.smul_apply, smul_eq_mul, ← hl i, Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [← Finset.mul_sum]
              by_cases hij : w i j ≠ 0
              · rw [hWij i j hij]
                congr 1
                rw [← (hWc i j hij).1.sum_right S]
                symm
                refine Finset.sum_subset (support_flatDist_child_subset β' child' (hβ' i j hij)) ?_
                intro S' _ hS'
                exact (hWc i j hij).1.zero_right S S' hS'
              · rw [not_not.mp hij, zero_mul, zero_mul]
          _ = flatDist (.chance _ β child) S := by
              rw [flatDist_chance β child, Finsupp.finsetSum_apply]
      · intro S'
        calc (∑ S ∈ (flatDist (.chance _ β child)).support, ∑ i, ∑ j, w i j * Wij i j S S')
            = ∑ i, ∑ j, ∑ S ∈ (flatDist (.chance _ β child)).support, w i j * Wij i j S S' := by
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
          _ = ∑ j, ∑ i, ∑ S ∈ (flatDist (.chance _ β child)).support, w i j * Wij i j S S' :=
              Finset.sum_comm
          _ = ∑ j, (β'.w j • flatDist (child' j)) S' := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finsupp.smul_apply, smul_eq_mul, ← hr j, Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← Finset.mul_sum]
              by_cases hij : w i j ≠ 0
              · rw [hWij i j hij]
                congr 1
                rw [← (hWc i j hij).1.sum_left S']
                symm
                refine Finset.sum_subset (support_flatDist_child_subset β child (hβ i j hij)) ?_
                intro S _ hS
                exact (hWc i j hij).1.zero_left S S' hS
              · rw [not_not.mp hij, zero_mul, zero_mul]
          _ = flatDist (.chance _ β' child') S' := by
              rw [flatDist_chance β' child', Finsupp.finsetSum_apply]
      · intro S S' hne ω r hS
        obtain ⟨i, j, hij, hW⟩ := hprod S S' hne
        exact (hWc i j hij).2.1 S S' hW ω r hS
      · intro S S' hne ω r hS'
        obtain ⟨i, j, hij, hW⟩ := hprod S S' hne
        exact (hWc i j hij).2.2.1 S S' hW ω r hS'
      · intro S S' hne d c d' c' hS hS'
        obtain ⟨i, j, hij, hW⟩ := hprod S S' hne
        exact (hWc i j hij).2.2.2.1 S S' hW d c d' c' hS hS'
      · intro S S' hne d c c' hS hS' a
        obtain ⟨i, j, hij, hW⟩ := hprod S S' hne
        exact (hWc i j hij).2.2.2.2 S S' hW d c c' hS hS' a

/-! ### The fairness grades along the chain -/

section grades

variable [DecidableEq ι] [∀ d, Fintype (acts d)]

/-- `Fair_≅ ⟹ Fair_≃`.
Source: `equiv.md` EQ-2 (the chain, read on fibers)
Kind: C -/
theorem StronglyFair.fairBisim {B : Tree Ω ι acts K} (h : StronglyFair B) : FairBisim B :=
  fun d q hq q' hq' => (h d q hq q' hq').bisim

/-- `Fair_≃ ⟹ Fair_{≃Δ}`.
Source: `equiv.md` EQ-2
Kind: C -/
theorem FairBisim.fairBisimΔ {B : Tree Ω ι acts K} (h : FairBisim B) : FairBisimΔ B :=
  fun d q hq q' hq' => (h d q hq q' hq').bisimΔ

variable [∀ d, DecidableEq (acts d)]

/-- **EQ-3's corollary, the direction `Fair_{≃Δ} ⟹ Fair_{≈tr}`** (on every tree, pruned or not):
`≃_Δ`-related fiber members have equal trace distributions.
Source: `equiv.md` EQ-3 corollary ("`Fair_{≈tr}(B) ⟺ Fair_{≃Δ}(B)`"), the `⇐` half
Kind: C
Fidelity: stronger (no pruning needed for this direction) -/
theorem FairBisimΔ.fairTr {B : Tree Ω ι acts K} (h : FairBisimΔ B) : FairTr B :=
  fun d q hq q' hq' => (h d q hq q' hq').trEq

/-- `Fair_{≈tr} ⟹ Fair_{≈law}` (law-fairness).
Source: `equiv.md` EQ-2
Kind: C -/
theorem FairTr.lawFair {B : Tree Ω ι acts K} (h : FairTr B) : LawFair B :=
  fun d q hq q' hq' => (h d q hq q' hq').lawEq

end grades

end Cleanroom.Decision.DpFairnessReloc
