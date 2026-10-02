import Cleanroom.Decision.DpFairnessReloc.Relations
import Mathlib.Algebra.BigOperators.Field

/-!
# The six relations, continued (T8: the chain closed, EQ-4, EQ-6, EQ-3's corollary)

Package `dp-fairness-reloc`, file 11 (repair round 1). Over `Relations.lean`:

* **Coupling composition** (`compCoupling`): the composite `w₁₃(i,k) := ∑_j w₁₂(i,j)·w₂₃(j,k)/γ_j`
  of two couplings through a common middle marginal `γ` is a coupling of the outer marginals
  (the `γ_j = 0` terms vanish because non-negative summands of a zero sum are zero), supported on
  composable pairs. It gives `Bisim.trans` and `BisimΔ.trans`.
* **Flat couplings as total functions** (`FlatCoupling`): `≃_Δ`'s coupling on the support
  subtypes, presented as a function on all trees that vanishes off the supports
  (`BisimΔ.of_flatCoupling`, `BisimΔ.exists_flatCoupling`).
* `≃` and `≃_Δ` are equivalences.

Continued in `RelationsChain.lean` (`≃ ⊆ ≃_Δ`, the fairness grades along the chain),
`RelationsStats.lean` (trace functionals, EQ-6, EQ-4, EQ-3's corollary) and
`RelationsWitnesses.lean` (E4).
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-! ### Coupling composition -/

section coupling

variable {I J L : Type} [Fintype I] [Fintype J] [Fintype L]

/-- The composite of two couplings through the middle marginal `γ`:
`w₁₃(i,l) := ∑_j w₁₂(i,j)·w₂₃(j,l)/γ_j` (a term with `γ_j = 0` is `0`, Lean's `x / 0 = 0`).
Source: none: infrastructure (the standard composition of couplings)
Kind: D -/
def compCoupling (w₁₂ : I → J → K) (w₂₃ : J → L → K) (γ : J → K) (i : I) (l : L) : K :=
  ∑ j, w₁₂ i j * w₂₃ j l / γ j

variable {w₁₂ : I → J → K} {w₂₃ : J → L → K} {γ : J → K}

/-- Non-negative summands of a zero sum are zero.
Source: none: infrastructure
Kind: L -/
theorem eq_zero_of_sum_eq_zero_of_nonneg {J' : Type} [Fintype J'] {f : J' → K} (hf : ∀ j, 0 ≤ f j)
    (h : ∑ j, f j = 0) (j : J') : f j = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hf j).mp h j (Finset.mem_univ j)

/-- The composite of non-negative couplings is non-negative.
Source: none: infrastructure
Kind: L -/
theorem compCoupling_nonneg (hw₁₂ : ∀ i j, 0 ≤ w₁₂ i j) (hw₂₃ : ∀ j l, 0 ≤ w₂₃ j l)
    (hγ : ∀ j, 0 ≤ γ j) (i : I) (l : L) : 0 ≤ compCoupling w₁₂ w₂₃ γ i l :=
  Finset.sum_nonneg fun j _ => div_nonneg (mul_nonneg (hw₁₂ i j) (hw₂₃ j l)) (hγ j)

/-- The composite's right marginal is the first coupling's.
Source: none: infrastructure
Kind: L -/
theorem compCoupling_sum_right (hw₁₂ : ∀ i j, 0 ≤ w₁₂ i j) (hγ₁ : ∀ j, ∑ i, w₁₂ i j = γ j)
    (hγ₂ : ∀ j, ∑ l, w₂₃ j l = γ j) (i : I) :
    ∑ l, compCoupling w₁₂ w₂₃ γ i l = ∑ j, w₁₂ i j := by
  unfold compCoupling
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_div, ← Finset.mul_sum, hγ₂ j]
  by_cases h : γ j = 0
  · rw [h, mul_zero, zero_div]
    exact (eq_zero_of_sum_eq_zero_of_nonneg (fun i => hw₁₂ i j) (by rw [hγ₁ j, h]) i).symm
  · rw [mul_div_assoc, div_self h, mul_one]

/-- The composite's left marginal is the second coupling's.
Source: none: infrastructure
Kind: L -/
theorem compCoupling_sum_left (hw₂₃ : ∀ j l, 0 ≤ w₂₃ j l) (hγ₁ : ∀ j, ∑ i, w₁₂ i j = γ j)
    (hγ₂ : ∀ j, ∑ l, w₂₃ j l = γ j) (l : L) :
    ∑ i, compCoupling w₁₂ w₂₃ γ i l = ∑ j, w₂₃ j l := by
  unfold compCoupling
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_div, ← Finset.sum_mul, hγ₁ j]
  by_cases h : γ j = 0
  · rw [h, zero_mul, zero_div]
    exact (eq_zero_of_sum_eq_zero_of_nonneg (hw₂₃ j) (by rw [hγ₂ j, h]) l).symm
  · rw [mul_comm, mul_div_assoc, div_self h, mul_one]

/-- A non-zero composite entry passes through some middle index with both factors non-zero.
Source: none: infrastructure
Kind: L -/
theorem compCoupling_ne_zero {i : I} {l : L} (h : compCoupling w₁₂ w₂₃ γ i l ≠ 0) :
    ∃ j, w₁₂ i j ≠ 0 ∧ w₂₃ j l ≠ 0 := by
  unfold compCoupling at h
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨j, fun h' => hj ?_, fun h' => hj ?_⟩
  · rw [h', zero_mul, zero_div]
  · rw [h', mul_zero, zero_div]

end coupling

/-! ### Transitivity of `≃` and `≃_Δ` -/

/-- **Transitivity of `≃`** (coupling composition through the middle chance law).
Source: mandate T8(a) ("prove each relation is an equivalence")
Kind: P
Fidelity: exact -/
theorem Bisim.trans {A B C : Tree Ω ι acts K} (h₁ : Bisim A B) (h₂ : Bisim B C) : Bisim A C := by
  induction h₁ generalizing C with
  | leaf ω r => exact h₂
  | decision d child child' h ih =>
      cases h₂ with
      | decision _ _ child'' h' => exact .decision d child child'' fun a => ih a (h' a)
  | chance β β' child child' w hw hl hr h ih =>
      cases h₂ with
      | chance _ β'' _ child'' w' hw' hl' hr' h' =>
          refine .chance β β'' child child'' (compCoupling w w' β'.w)
            (compCoupling_nonneg hw hw' β'.nonneg)
            (fun i => by rw [compCoupling_sum_right hw hr hl' i, hl i])
            (fun k => by rw [compCoupling_sum_left hw' hr hl' k, hr' k])
            (fun i k hik => ?_)
          obtain ⟨j, hij, hjk⟩ := compCoupling_ne_zero hik
          exact ih i j hij (h' j k hjk)

/-- `≃` is an equivalence.
Source: mandate T8(a)
Kind: L -/
theorem Bisim.equivalence : Equivalence (Bisim (Ω := Ω) (ι := ι) (acts := acts) (K := K)) :=
  ⟨Bisim.refl, Bisim.symm, Bisim.trans⟩

/-- A non-chance tree that is not a leaf is a decision node.
Source: none: infrastructure
Kind: L -/
theorem exists_decision_of_nonChance {S : Tree Ω ι acts K} (h : NonChance S)
    (hn : ∀ ω r, S ≠ .leaf ω r) : ∃ d c, S = .decision d c := by
  cases S with
  | leaf ω r => exact absurd rfl (hn ω r)
  | chance _ _ _ => exact h.elim
  | decision d c => exact ⟨d, c, rfl⟩

/-- **Transitivity of `≃_Δ`** (coupling composition on the flattenings, through the middle
flattening's masses).
Source: mandate T8(a)
Kind: P
Fidelity: exact -/
theorem BisimΔ.trans {A B C : Tree Ω ι acts K} (h₁ : BisimΔ A B) (h₂ : BisimΔ B C) : BisimΔ A C := by
  induction h₁ generalizing C with
  | mk A B W hw hl hr hleaf hleaf' hpt hdec ih =>
      cases h₂ with
      | mk _ _ W' hw' hl' hr' hleaf₂ hleaf₂' hpt₂ hdec₂ =>
          -- the middle node of a composable pair whose ends are decision nodes is a decision node
          have hmid : ∀ (i : ↥(flatDist A).support) (j : ↥(flatDist B).support), W i j ≠ 0 →
              ∀ d (c : acts d → Tree Ω ι acts K), (i : Tree Ω ι acts K) = .decision d c →
              ∃ d₁ c₁, (j : Tree Ω ι acts K) = .decision d₁ c₁ := by
            intro i j hij d c hi
            refine exists_decision_of_nonChance (nonChance_of_mem_support_flatDist B j j.2) ?_
            intro ω r hj
            have := hleaf' i j hij ω r hj
            rw [hi] at this
            cases this
          refine .mk A C (compCoupling W W' fun j => flatDist B j)
            (compCoupling_nonneg hw hw' fun j => flatDist_nonneg B j)
            (fun i => by rw [compCoupling_sum_right hw hr hl' i, hl i])
            (fun k => by rw [compCoupling_sum_left hw' hr hl' k, hr' k])
            ?_ ?_ ?_ ?_
          · intro i k hik ω r hi
            obtain ⟨j, hij, hjk⟩ := compCoupling_ne_zero hik
            exact hleaf₂ j k hjk ω r (hleaf i j hij ω r hi)
          · intro i k hik ω r hk
            obtain ⟨j, hij, hjk⟩ := compCoupling_ne_zero hik
            exact hleaf' i j hij ω r (hleaf₂' j k hjk ω r hk)
          · intro i k hik d c d' c' hi hk
            obtain ⟨j, hij, hjk⟩ := compCoupling_ne_zero hik
            obtain ⟨d₁, c₁, hj⟩ := hmid i j hij d c hi
            exact (hpt i j hij d c d₁ c₁ hi hj).trans (hpt₂ j k hjk d₁ c₁ d' c' hj hk)
          · intro i k hik d c c' hi hk a
            obtain ⟨j, hij, hjk⟩ := compCoupling_ne_zero hik
            obtain ⟨d₁, c₁, hj⟩ := hmid i j hij d c hi
            have hd := hpt i j hij d c d₁ c₁ hi hj
            subst hd
            exact ih i j hij d c c₁ hi hj a (hdec₂ j k hjk d c₁ c' hj hk a)

/-- `≃_Δ` is an equivalence.
Source: mandate T8(a)
Kind: L -/
theorem BisimΔ.equivalence [∀ d, Fintype (acts d)] :
    Equivalence (BisimΔ (Ω := Ω) (ι := ι) (acts := acts) (K := K)) :=
  ⟨BisimΔ.refl, BisimΔ.symm, BisimΔ.trans⟩

/-! ### Flat couplings as total functions -/

/-- A coupling of the flattenings of `T` and `T'`, presented as a function on all pairs of trees
that vanishes off the two supports and has the two flattenings as marginals.
Source: none: infrastructure (the coupling of `BisimΔ.mk` extended by zero)
Kind: D -/
structure FlatCoupling (T T' : Tree Ω ι acts K) (W : Tree Ω ι acts K → Tree Ω ι acts K → K) :
    Prop where
  nonneg : ∀ S S', 0 ≤ W S S'
  zero_left : ∀ S S', S ∉ (flatDist T).support → W S S' = 0
  zero_right : ∀ S S', S' ∉ (flatDist T').support → W S S' = 0
  sum_right : ∀ S, ∑ S' ∈ (flatDist T').support, W S S' = flatDist T S
  sum_left : ∀ S', ∑ S ∈ (flatDist T).support, W S S' = flatDist T' S'

/-- A flat coupling whose support pairs satisfy Definition 13′'s clauses witnesses `≃_Δ`.
Source: none: infrastructure
Kind: L -/
theorem BisimΔ.of_flatCoupling {T T' : Tree Ω ι acts K} {W : Tree Ω ι acts K → Tree Ω ι acts K → K}
    (hW : FlatCoupling T T' W)
    (hleaf : ∀ S S', W S S' ≠ 0 → ∀ ω r, S = .leaf ω r → S' = .leaf ω r)
    (hleaf' : ∀ S S', W S S' ≠ 0 → ∀ ω r, S' = .leaf ω r → S = .leaf ω r)
    (hpt : ∀ S S', W S S' ≠ 0 → ∀ d c d' c', S = .decision d c → S' = .decision d' c' → d = d')
    (hdec : ∀ S S', W S S' ≠ 0 → ∀ d c c', S = .decision d c → S' = .decision d c' →
      ∀ a, BisimΔ (c a) (c' a)) :
    BisimΔ T T' :=
  .mk T T' (fun i j => W i j) (fun i j => hW.nonneg i j)
    (fun i => by
      rw [Finset.sum_coe_sort (flatDist T').support (fun j => W i j)]
      exact hW.sum_right i)
    (fun j => by
      rw [Finset.sum_coe_sort (flatDist T).support (fun i => W i j)]
      exact hW.sum_left j)
    (fun i j h => hleaf i j h) (fun i j h => hleaf' i j h) (fun i j h => hpt i j h)
    (fun i j h => hdec i j h)

/-- `≃_Δ` yields a flat coupling whose support pairs satisfy Definition 13′'s clauses.
Source: none: infrastructure
Kind: L -/
theorem BisimΔ.exists_flatCoupling {T T' : Tree Ω ι acts K} (h : BisimΔ T T') :
    ∃ W : Tree Ω ι acts K → Tree Ω ι acts K → K, FlatCoupling T T' W ∧
      (∀ S S', W S S' ≠ 0 → ∀ ω r, S = .leaf ω r → S' = .leaf ω r) ∧
      (∀ S S', W S S' ≠ 0 → ∀ ω r, S' = .leaf ω r → S = .leaf ω r) ∧
      (∀ S S', W S S' ≠ 0 → ∀ d c d' c', S = .decision d c → S' = .decision d' c' → d = d') ∧
      (∀ S S', W S S' ≠ 0 → ∀ d c c', S = .decision d c → S' = .decision d c' →
        ∀ a, BisimΔ (c a) (c' a)) := by
  classical
  cases h with
  | mk T T' W hw hl hr hleaf hleaf' hpt hdec =>
      let W' : Tree Ω ι acts K → Tree Ω ι acts K → K := fun S S' =>
        if h : S ∈ (flatDist T).support ∧ S' ∈ (flatDist T').support then W ⟨S, h.1⟩ ⟨S', h.2⟩
        else 0
      have hmem : ∀ S S', W' S S' ≠ 0 →
          ∃ h : S ∈ (flatDist T).support ∧ S' ∈ (flatDist T').support,
            W' S S' = W ⟨S, h.1⟩ ⟨S', h.2⟩ := by
        intro S S' hne
        by_cases h : S ∈ (flatDist T).support ∧ S' ∈ (flatDist T').support
        · exact ⟨h, dif_pos h⟩
        · exact absurd (dif_neg h) hne
      refine ⟨W', ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · intro S S'
        by_cases h : S ∈ (flatDist T).support ∧ S' ∈ (flatDist T').support
        · rw [show W' S S' = W ⟨S, h.1⟩ ⟨S', h.2⟩ from dif_pos h]; exact hw _ _
        · rw [show W' S S' = 0 from dif_neg h]
      · intro S S' hS
        exact dif_neg fun h => hS h.1
      · intro S S' hS'
        exact dif_neg fun h => hS' h.2
      · intro S
        by_cases hS : S ∈ (flatDist T).support
        · rw [← hl ⟨S, hS⟩, ← Finset.sum_coe_sort (flatDist T').support]
          refine Finset.sum_congr rfl fun j _ => ?_
          exact dif_pos ⟨hS, j.2⟩
        · have h0 : flatDist T S = 0 := by
            by_contra h'; exact hS (Finsupp.mem_support_iff.mpr h')
          rw [h0]
          exact Finset.sum_eq_zero fun S' _ => dif_neg fun h => hS h.1
      · intro S'
        by_cases hS' : S' ∈ (flatDist T').support
        · rw [← hr ⟨S', hS'⟩, ← Finset.sum_coe_sort (flatDist T).support]
          refine Finset.sum_congr rfl fun i _ => ?_
          exact dif_pos ⟨i.2, hS'⟩
        · have h0 : flatDist T' S' = 0 := by
            by_contra h'; exact hS' (Finsupp.mem_support_iff.mpr h')
          rw [h0]
          exact Finset.sum_eq_zero fun S _ => dif_neg fun h => hS' h.2
      · intro S S' hne ω r hS
        obtain ⟨h, hW⟩ := hmem S S' hne
        rw [hW] at hne
        exact hleaf _ _ hne ω r hS
      · intro S S' hne ω r hS'
        obtain ⟨h, hW⟩ := hmem S S' hne
        rw [hW] at hne
        exact hleaf' _ _ hne ω r hS'
      · intro S S' hne d c d' c' hS hS'
        obtain ⟨h, hW⟩ := hmem S S' hne
        rw [hW] at hne
        exact hpt _ _ hne d c d' c' hS hS'
      · intro S S' hne d c c' hS hS' a
        obtain ⟨h, hW⟩ := hmem S S' hne
        rw [hW] at hne
        exact hdec _ _ hne d c c' hS hS' a

end Cleanroom.Decision.DpFairnessReloc
