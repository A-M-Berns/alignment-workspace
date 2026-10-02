import Cleanroom.Decision.DpCalibLimits.Defs

/-!
# T1 — Definition 10's limit conditional is a Popper function; the LPS reading

[[dp-calib-limits-mandate]] T1 (dp-sl-029, P07 I2′, SL-12).

* `popperLimit_isPopper`: with the `≡ 1` convention on tremble-unreachable conditions, the
  algebraic limit conditional of Definition 10 satisfies the five Popper axioms on every
  finite tree (no hypothesis: every tree has a chance-positive leaf,
  `exists_chanceWeight_pos`, which is all (P4) needs).
* **What fails without the convention.** With `dp-calibration`'s junk `0`, the function
  `limitCond C B` satisfies (P0), unconditional additivity (hence (P2)), the multiplication
  axiom (P3) and (P4) on every tree (`limitCond_bounds`, `limitCond_add`, `limitCond_mul`,
  `limitCond_nontrivial`); it fails exactly (P1) at the unreachable conditions
  (`limitCond_self_iff`), witnessed on Told-You-So at `n = 5 ∧ m = 10`
  (`tys_limitCond_unreachable_ne_one`). The inventory's "four Popper axioms fail" (dp-sl-029)
  is therefore an over-count under this axiom set: see `dp-calib-limits-findings.md`.
* **The LPS reading** (`limitCond_eq_lps`): `limitCond X O` is the conditional of the
  lexicographic level `k = ord (nuPoly O)` — the first level that gives `O` mass — where
  level `j` is the (normalised) sum of the leading coefficients of the leaves of order `j`;
  level `0` is `ν_C` (`lps_zero_eq_nu`). Levels are by *order*, not by number of trembled
  draws: an act of positive weight has order `0`. N+ on Told-You-So under `(five, five)`:
  level `0` gives `O₁₀` no mass, level `1` gives it `½` (`tys_take5_lps_levels`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Polynomial infrastructure -/

section polyInfra

/-- A coefficient at or above the order is the trailing coefficient at the order and `0` above
it. Source: none: infrastructure. Kind: L -/
theorem coeff_eq_ite_of_le {p : Polynomial K} {k : ℕ} (hk : k ≤ p.natTrailingDegree) :
    p.coeff k = if p.natTrailingDegree = k then p.trailingCoeff else 0 := by
  rcases hk.lt_or_eq with hlt | heq
  · rw [if_neg hlt.ne', Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt]
  · rw [if_pos heq.symm]; subst heq; rfl

end polyInfra

section tree

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-- Membership in `worldEv`. Source: none: infrastructure. Kind: L -/
theorem mem_worldEv (B : Tree Ω ι acts K) (X : Finset Ω) (ℓ : B.Leaves) :
    ℓ ∈ worldEv B X ↔ world B ℓ ∈ X := by simp [worldEv]

/-- `worldEv (X ∩ O) ⊆ worldEv O`. Source: none: infrastructure. Kind: L -/
theorem worldEv_inter_subset (B : Tree Ω ι acts K) (X O : Finset Ω) :
    worldEv B (X ∩ O) ⊆ worldEv B O := by
  intro ℓ hℓ
  rw [mem_worldEv] at hℓ ⊢
  exact (Finset.mem_inter.mp hℓ).2

/-- **Every tree has a chance-positive leaf** (a chance node's distribution has a positive
weight; decision nodes have an action). So (P4) needs no hypothesis.
Source: none: infrastructure (mandate T1(a) carried this as hypothesis (a); it is derived)
Kind: L -/
theorem exists_chanceWeight_pos : (B : Tree Ω ι acts K) → ∃ ℓ, 0 < chanceWeight B ℓ
  | .leaf _ _ => ⟨(), by simp [chanceWeight]⟩
  | .chance n β child => by
      have hi : ∃ i, 0 < β.w i := by
        by_contra h
        push Not at h
        have := β.sum_one
        rw [Finset.sum_eq_zero (fun i _ => le_antisymm (h i) (β.nonneg i))] at this
        exact zero_ne_one this
      obtain ⟨i, hi⟩ := hi
      obtain ⟨ℓ, hℓ⟩ := exists_chanceWeight_pos (child i)
      exact ⟨⟨i, ℓ⟩, by rw [chanceWeight_chance]; exact mul_pos hi hℓ⟩
  | .decision d child => by
      obtain ⟨a⟩ := (inferInstance : Nonempty (acts d))
      obtain ⟨ℓ, hℓ⟩ := exists_chanceWeight_pos (child a)
      exact ⟨⟨a, ℓ⟩, by rw [chanceWeight_decision]; exact hℓ⟩

variable (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- `nuPoly ⊤ ≠ 0` on every tree. Source: none: infrastructure. Kind: L -/
theorem nuPoly_univ_ne_zero : nuPoly C B Finset.univ ≠ 0 := by
  obtain ⟨ℓ, hℓ⟩ := exists_chanceWeight_pos B
  exact (nuPoly_ne_zero_iff C B _).mpr ⟨ℓ, Finset.mem_univ _, hℓ⟩

/-- `nuPoly ∅ = 0`. Source: none: infrastructure. Kind: L -/
@[simp] theorem nuPoly_empty : nuPoly C B ∅ = 0 := by
  simp [nuPoly, worldEv]

/-- `nuPoly` is additive on disjoint events. Source: none: infrastructure. Kind: L -/
theorem nuPoly_union {X Y : Finset Ω} (h : Disjoint X Y) :
    nuPoly C B (X ∪ Y) = nuPoly C B X + nuPoly C B Y := by
  simp only [nuPoly_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases hX : world B ℓ ∈ X
  · have hY : world B ℓ ∉ Y := Finset.disjoint_left.mp h hX
    simp [hX, hY]
  · by_cases hY : world B ℓ ∈ Y <;> simp [hX, hY]

/-- A sub-event of a tremble-unreachable event is tremble-unreachable.
Source: none: infrastructure. Kind: L -/
theorem nuPoly_eq_zero_of_subset {X O : Finset Ω} (h : nuPoly C B O = 0) (hXO : X ⊆ O) :
    nuPoly C B X = 0 := by
  by_contra hne
  obtain ⟨ℓ, hℓ, hpos⟩ := (nuPoly_ne_zero_iff C B X).mp hne
  exact absurd h ((nuPoly_ne_zero_iff C B O).mpr ⟨ℓ, hXO hℓ, hpos⟩)

/-- The order of `nuPoly O` is at most the order of any non-zero leaf polynomial of an
`O`-leaf. Source: none: infrastructure. Kind: L -/
theorem natTrailingDegree_nuPoly_le_leaf (O : Finset Ω) {ℓ : B.Leaves} (hℓ : ℓ ∈ worldEv B O)
    (h : leafLawPoly C B ℓ ≠ 0) :
    (nuPoly C B O).natTrailingDegree ≤ (leafLawPoly C B ℓ).natTrailingDegree := by
  unfold nuPoly
  exact PosTrail.natTrailingDegree_sum_le _ _ (fun ℓ' _ => posTrail_leafLawPoly C B ℓ') hℓ h

/-- The coefficient of an `O`-leaf's polynomial at the order of `nuPoly O` is non-negative.
Source: none: infrastructure. Kind: L -/
theorem coeff_leafLawPoly_nonneg (O : Finset Ω) {ℓ : B.Leaves} (hℓ : ℓ ∈ worldEv B O) :
    0 ≤ (leafLawPoly C B ℓ).coeff (nuPoly C B O).natTrailingDegree := by
  by_cases h : leafLawPoly C B ℓ = 0
  · rw [h, Polynomial.coeff_zero]
  · rw [coeff_eq_ite_of_le (natTrailingDegree_nuPoly_le_leaf C B O hℓ h)]
    split_ifs
    · exact (posTrail_leafLawPoly C B ℓ h).le
    · exact le_rfl

/-- The numerator coefficient of `limitCond X O` is non-negative.
Source: none: infrastructure. Kind: L -/
theorem coeff_nuPoly_inter_nonneg (X O : Finset Ω) :
    0 ≤ (nuPoly C B (X ∩ O)).coeff (nuPoly C B O).natTrailingDegree := by
  have e : nuPoly C B (X ∩ O) = ∑ ℓ ∈ worldEv B (X ∩ O), leafLawPoly C B ℓ := rfl
  rw [e, Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg fun ℓ hℓ =>
    coeff_leafLawPoly_nonneg C B O (worldEv_inter_subset B X O hℓ)

/-- The numerator coefficient of `limitCond X O` is at most the denominator's.
Source: none: infrastructure. Kind: L -/
theorem coeff_nuPoly_inter_le (X O : Finset Ω) :
    (nuPoly C B (X ∩ O)).coeff (nuPoly C B O).natTrailingDegree ≤
      (nuPoly C B O).coeff (nuPoly C B O).natTrailingDegree := by
  have e1 : nuPoly C B (X ∩ O) = ∑ ℓ ∈ worldEv B (X ∩ O), leafLawPoly C B ℓ := rfl
  have e2 : nuPoly C B O = ∑ ℓ ∈ worldEv B O, leafLawPoly C B ℓ := rfl
  conv_lhs => rw [e1]
  conv_rhs => rw [e2]
  rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  exact Finset.sum_le_sum_of_subset_of_nonneg (worldEv_inter_subset B X O)
    fun ℓ hℓ _ => coeff_leafLawPoly_nonneg C B O hℓ

/-! ## The junk-`0` limit conditional: which axioms it satisfies on every tree -/

/-- **(P0) for the junk-`0` function**: `0 ≤ limitCond X O ≤ 1` on every tree.
Source: P07 I2′; mandate T1(a)
Kind: P
Fidelity: exact -/
theorem limitCond_bounds (X O : Finset Ω) : 0 ≤ limitCond C B X O ∧ limitCond C B X O ≤ 1 := by
  unfold limitCond
  refine ⟨div_nonneg (coeff_nuPoly_inter_nonneg C B X O) ?_, div_le_one_of_le₀ (coeff_nuPoly_inter_le C B X O) ?_⟩
  · have := coeff_nuPoly_inter_nonneg C B Finset.univ O
    rwa [Finset.univ_inter] at this
  · have := coeff_nuPoly_inter_nonneg C B Finset.univ O
    rwa [Finset.univ_inter] at this

/-- **Additivity of the junk-`0` function on every condition** (hence (P2)): for disjoint
`A, A'`, `limitCond (A ∪ A') O = limitCond A O + limitCond A' O`, with no normality
hypothesis (at an unreachable `O` all three are `0`).
Source: P07 I2′ ("additivity … transfers"); mandate T1(a)
Kind: P
Fidelity: exact -/
theorem limitCond_add {A A' : Finset Ω} (O : Finset Ω) (h : Disjoint A A') :
    limitCond C B (A ∪ A') O = limitCond C B A O + limitCond C B A' O := by
  unfold limitCond
  have hd : Disjoint (A ∩ O) (A' ∩ O) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left h)
  rw [Finset.union_inter_distrib_right, nuPoly_union C B hd, Polynomial.coeff_add, add_div]

/-- The core of the multiplication axiom, where both conditions are tremble-reachable: the
orders `k = ord (nuPoly C')` and `k' = ord (nuPoly (B' ∩ C'))` satisfy `k ≤ k'`; if `k < k'`
both sides vanish (the numerators have no `ε^k` term), if `k = k'` the middle coefficient
cancels.
Source: P07 I2′ ("the multiplication axiom transfers from ratios in `ℝ(ε)`")
Kind: P
Fidelity: exact -/
theorem limitCond_mul_core (A B' C' : Finset Ω) (hC : nuPoly C B C' ≠ 0)
    (hBC : nuPoly C B (B' ∩ C') ≠ 0) :
    limitCond C B (A ∩ B') C' = limitCond C B A (B' ∩ C') * limitCond C B B' C' := by
  unfold limitCond
  rw [Finset.inter_assoc]
  have hkk' : (nuPoly C B C').natTrailingDegree ≤ (nuPoly C B (B' ∩ C')).natTrailingDegree :=
    natTrailingDegree_nuPoly_mono C B B' C' hBC
  rcases hkk'.lt_or_eq with hlt | heq
  · have h1 : (nuPoly C B (B' ∩ C')).coeff (nuPoly C B C').natTrailingDegree = 0 :=
      Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt
    have h2 : (nuPoly C B (A ∩ (B' ∩ C'))).coeff (nuPoly C B C').natTrailingDegree = 0 := by
      by_cases hz : nuPoly C B (A ∩ (B' ∩ C')) = 0
      · rw [hz, Polynomial.coeff_zero]
      · exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
          (hlt.trans_le (natTrailingDegree_nuPoly_mono C B A (B' ∩ C') hz))
    rw [h1, h2, zero_div, mul_zero]
  · rw [← heq]
    have hM : (nuPoly C B (B' ∩ C')).coeff (nuPoly C B C').natTrailingDegree ≠ 0 := by
      rw [heq]; exact (trailingCoeff_nuPoly_pos C B _ hBC).ne'
    have hD : (nuPoly C B C').coeff (nuPoly C B C').natTrailingDegree ≠ 0 :=
      (trailingCoeff_nuPoly_pos C B _ hC).ne'
    field_simp

/-- **(P3) for the junk-`0` function on every tree**: the multiplication axiom holds with no
convention at all (at an unreachable condition every factor is `0`).
Source: P07 I2′; mandate T1(b) (asked for a failure of (P3): there is none)
Kind: P
Fidelity: exact -/
theorem limitCond_mul (A B' C' : Finset Ω) :
    limitCond C B (A ∩ B') C' = limitCond C B A (B' ∩ C') * limitCond C B B' C' := by
  by_cases hC : nuPoly C B C' = 0
  · have h0 : ∀ X, limitCond C B X C' = 0 := fun X => by
      unfold limitCond; rw [hC, Polynomial.coeff_zero, div_zero]
    rw [h0, h0, mul_zero]
  · by_cases hBC : nuPoly C B (B' ∩ C') = 0
    · have h0 : ∀ X, limitCond C B X (B' ∩ C') = 0 := fun X => by
        unfold limitCond; rw [hBC, Polynomial.coeff_zero, div_zero]
      have h1 : nuPoly C B (A ∩ B' ∩ C') = 0 :=
        nuPoly_eq_zero_of_subset C B hBC (by rw [Finset.inter_assoc]; exact Finset.inter_subset_right)
      have h2 : limitCond C B (A ∩ B') C' = 0 := by
        unfold limitCond; rw [h1, Polynomial.coeff_zero, zero_div]
      rw [h2, h0, zero_mul]
    · exact limitCond_mul_core C B A B' C' hC hBC

/-- **(P1) holds for the junk-`0` function exactly at tremble-reachable conditions.**
Source: P07 I2′ ("without which the axioms fail on any tree with an unreachable act")
Kind: P
Fidelity: exact -/
theorem limitCond_self_iff (O : Finset Ω) : limitCond C B O O = 1 ↔ nuPoly C B O ≠ 0 := by
  unfold limitCond
  rw [Finset.inter_self]
  constructor
  · intro h h0
    rw [h0, Polynomial.coeff_zero, div_zero] at h
    exact zero_ne_one h
  · intro h
    exact div_self (trailingCoeff_nuPoly_pos C B O h).ne'

/-- (P4) for the junk-`0` function: `limitCond ∅ ⊤ = 0 ≠ 1`.
Source: none: infrastructure. Kind: L -/
theorem limitCond_nontrivial : ∃ A O : Finset Ω, limitCond C B A O ≠ 1 := by
  refine ⟨∅, Finset.univ, ?_⟩
  unfold limitCond
  rw [Finset.empty_inter, nuPoly_empty, Polynomial.coeff_zero, zero_div]
  exact zero_ne_one

/-- **The count of failing axioms is presentation-relative**: under the junk `0` a
tremble-unreachable condition `O` is *normal* for `IsPopper`'s `Abnormal` (`limitCond ∅ O = 0 ≠ 1`)
and yet `limitCond ⊤ O = 0 ≠ 1`, so Hájek's clause (ii) — "`p(· | B)` is a probability measure
for every normal `B`", which carries normalization — fails at `O` as well as (P1). Under
`IsPopper` as typed (additivity only in (P2)) exactly (P1) fails; under Hájek's chunking two
axioms fail. The systems agree; the count does not. The wording of clause (ii) is
**[reconstructed]**: Hájek 2003 is not in the repo (only the multiplication axiom was confirmed
from it by the SL run, mandate §5 item 6), so "Hájek's chunking" is a (b)-typed reconstruction
exactly as the axiom set `IsPopper` is; the theorem itself does not depend on it.
Source: Hájek 2003 p. 316 (clause (ii)) [reconstructed]; P07 I2′; audit r1 fidelity B1; audit r2
fidelity N3
Kind: P
Fidelity: exact
Hyps: (a) `nuPoly C B O = 0` (tremble-unreachable) -/
theorem limitCond_unreachable_normal_univ_eq_zero (O : Finset Ω) (h : nuPoly C B O = 0) :
    ¬ Abnormal (limitCond C B) O ∧ limitCond C B Finset.univ O = 0 := by
  have hz : ∀ X, limitCond C B X O = 0 := fun X => by
    unfold limitCond; rw [h]; simp
  exact ⟨fun hab => zero_ne_one ((hz ∅).symm.trans (hab ∅)), hz _⟩

/-! ## The Popper reading -/

/-- Abnormality of `popperLimit` is tremble-unreachability.
Source: P07 I2′. Kind: L -/
theorem abnormal_popperLimit_iff (O : Finset Ω) :
    Abnormal (popperLimit C B) O ↔ nuPoly C B O = 0 := by
  constructor
  · intro h
    by_contra hne
    have := h ∅
    unfold popperLimit at this
    rw [if_pos hne] at this
    unfold limitCond at this
    rw [Finset.empty_inter, nuPoly_empty, Polynomial.coeff_zero, zero_div] at this
    exact zero_ne_one this
  · intro h A
    unfold popperLimit
    rw [if_neg (not_not.mpr h)]

/-- The multiplication axiom for `popperLimit`: at an unreachable `C'` every factor is `1`;
at a reachable `C'` with unreachable `B' ∩ C'` the middle factor is `1` and the outer two are
`0`; otherwise it is `limitCond_mul_core`.
Source: P07 I2′
Kind: P
Fidelity: exact -/
theorem popperLimit_mul (A B' C' : Finset Ω) :
    popperLimit C B (A ∩ B') C' = popperLimit C B A (B' ∩ C') * popperLimit C B B' C' := by
  unfold popperLimit
  by_cases hC : nuPoly C B C' = 0
  · have hBC : nuPoly C B (B' ∩ C') = 0 :=
      nuPoly_eq_zero_of_subset C B hC Finset.inter_subset_right
    simp [hC, hBC]
  · rw [if_pos hC, if_pos hC]
    by_cases hBC : nuPoly C B (B' ∩ C') = 0
    · rw [if_neg (not_not.mpr hBC), one_mul]
      have h1 : nuPoly C B (A ∩ B' ∩ C') = 0 :=
        nuPoly_eq_zero_of_subset C B hBC (by rw [Finset.inter_assoc]; exact Finset.inter_subset_right)
      unfold limitCond
      rw [h1, hBC, Polynomial.coeff_zero, zero_div]
    · rw [if_pos hBC]
      exact limitCond_mul_core C B A B' C' hC hBC

/-- **Definition 10's limit conditional is a Popper function** on the world algebra, with the
`≡ 1` convention on tremble-unreachable conditions. (P0) from the coefficient bounds; (P1)
from the trailing coefficient; (P2) on normal conditions (= tremble-reachable,
`abnormal_popperLimit_iff`) from additivity of `nuPoly`; (P3) `popperLimit_mul`; (P4) from a
chance-positive leaf (every tree has one).
Source: P07 I2′ (dp-sl-029): "Definition 10's limit conditional is a Popper function on the
leaf algebra … with the convention `P(· | B) ≡ 1` on tremble-unreachable `B`"; SL-12
Kind: P
Fidelity: variant: finite atomic algebra; the (b)-grade axiom form of `IsPopper`; limit taken
algebraically
Hyps: none ((P4)'s positive leaf is derived: `exists_chanceWeight_pos`); the axiom set
itself is (b): reconstructed from Hájek 2003 pp. 316–317 by the SL run -/
theorem popperLimit_isPopper : IsPopper (popperLimit C B) where
  bounds A O := by
    unfold popperLimit
    split_ifs
    · exact limitCond_bounds C B A O
    · exact ⟨zero_le_one, le_rfl⟩
  refl O := by
    unfold popperLimit
    split_ifs with h
    · exact (limitCond_self_iff C B O).mpr h
    · rfl
  add A A' O hn hd := by
    have h : nuPoly C B O ≠ 0 := fun h0 => hn ((abnormal_popperLimit_iff C B O).mpr h0)
    unfold popperLimit
    simp only [if_pos h]
    exact limitCond_add C B O hd
  mul := popperLimit_mul C B
  nontrivial := by
    refine ⟨∅, Finset.univ, ?_⟩
    unfold popperLimit
    rw [if_pos (nuPoly_univ_ne_zero C B)]
    unfold limitCond
    rw [Finset.empty_inter, nuPoly_empty, Polynomial.coeff_zero, zero_div]
    exact zero_ne_one

/-- The bundled Popper function of a procedure on a tree.
Source: P07 I2′
Kind: D -/
noncomputable def popperFnOf : PopperFn Ω K := ⟨popperLimit C B, popperLimit_isPopper C B⟩

/-! ## Without the convention: the Told-You-So witness -/

/-- Told-You-So's unreachable act event `n = 5 ∧ m = 10`.
Source: P07 I2′ ("Told-You-So's `m=10 ∧ n=5`")
Kind: D -/
def tysUnreachable : Finset TysW := tysObs .five ∩ tysActEv .five .ten

/-- `n = 5 ∧ m = 10` is tremble-unreachable on Told-You-So under every procedure: no leaf
carries that world.
Source: P07 I2′
Kind: L -/
theorem tys_nuPoly_unreachable (C : Proc Five10 (fun _ => Five10) ℚ) :
    nuPoly C toldYouSo tysUnreachable = 0 := by
  rw [tys_nuPoly]
  simp [tysUnreachable, tysObs, tysActEv]

/-- **(P1) fails for the junk-`0` function on Told-You-So** at `n = 5 ∧ m = 10`:
`limitCond B' B' = 0 ≠ 1`, for every procedure (in particular `(five, five)`). Under `IsPopper`
as typed this is the one axiom the convention repairs (`limitCond_self_iff`); the other four
fields hold for the junk-`0` function on every tree (`limitCond_bounds`, `limitCond_add`,
`limitCond_mul`, `limitCond_nontrivial`). The count is presentation-relative
(`limitCond_unreachable_normal_univ_eq_zero`, `tys_limitCond_univ_unreachable`): under Hájek's
chunking normalization fails at the same condition too. P07 I2′'s own sentence ("the axioms
fail on any tree with an unreachable act") is confirmed; no source sentence asserts a count of
four *axioms* (findings F1).
Source: P07 I2′ ("without which the axioms fail on any tree with an unreachable act (e.g.
Told-You-So's `m=10 ∧ n=5`)"); survey dp-sl-029
Kind: N+
Fidelity: exact
Hyps: none -/
theorem tys_limitCond_unreachable_ne_one (C : Proc Five10 (fun _ => Five10) ℚ) :
    limitCond C toldYouSo tysUnreachable tysUnreachable ≠ 1 := by
  rw [Ne, limitCond_self_iff, not_not]
  exact tys_nuPoly_unreachable C

/-- On Told-You-So the unreachable condition is normal for the junk-`0` function and
`limitCond ⊤ B' = 0`: Hájek's clause (ii) [reconstructed; see
`limitCond_unreachable_normal_univ_eq_zero`] fails there as well as (P1).
Source: Hájek 2003 p. 316 [reconstructed]; audit r1 fidelity B1. Kind: N+ -/
theorem tys_limitCond_univ_unreachable (C : Proc Five10 (fun _ => Five10) ℚ) :
    ¬ Abnormal (limitCond C toldYouSo) tysUnreachable ∧
    limitCond C toldYouSo Finset.univ tysUnreachable = 0 :=
  limitCond_unreachable_normal_univ_eq_zero C toldYouSo tysUnreachable (tys_nuPoly_unreachable C)

/-- Under the convention the same condition is abnormal: `popperLimit A B' = 1` for every `A`.
Source: P07 I2′. Kind: L -/
theorem tys_popperLimit_unreachable (C : Proc Five10 (fun _ => Five10) ℚ) (A : Finset TysW) :
    popperLimit C toldYouSo A tysUnreachable = 1 :=
  (abnormal_popperLimit_iff C toldYouSo tysUnreachable).mpr (tys_nuPoly_unreachable C) A

/-! ## The lexicographic probability system of a procedure -/

/-- The order (in `ε`) of a leaf's law along the uniform ray: the number of off-support draws
on its path (an act of positive weight has order `0`, `posTrail_trembleW`).
Source: P07 I2′ ("Popper functions correspond to a subclass of lexicographic probability
systems … each ray selects one"); mandate T1(c)
Kind: D -/
noncomputable def leafOrder (ℓ : B.Leaves) : ℕ := (leafLawPoly C B ℓ).natTrailingDegree

/-- The leading coefficient of a leaf's law along the uniform ray (positive for a
chance-positive leaf, `posTrail_leafLawPoly`; `0` for a chance-null one).
Source: P07 I2′; mandate T1(c)
Kind: D -/
noncomputable def leafLead (ℓ : B.Leaves) : K := (leafLawPoly C B ℓ).trailingCoeff

/-- The unnormalised mass of the event `X` at lexicographic level `j`: the sum of the leading
coefficients of the `X`-leaves of order `j`.
Source: P07 I2′; mandate T1(c)
Kind: D -/
noncomputable def lpsMass (j : ℕ) (X : Finset Ω) : K :=
  ∑ ℓ ∈ (worldEv B X).filter (fun ℓ => leafOrder C B ℓ = j), leafLead C B ℓ

/-- **The lexicographic probability system of `C` on `B`**: level `j` is `lpsMass j`
normalised (junk `0` at an empty level).
Source: P07 I2′ ("each ray of trembles selects one [LPS]"); mandate T1(c)
Kind: D
Fidelity: variant: levels indexed by order in `ε`; the uniform ray -/
noncomputable def lps (j : ℕ) (X : Finset Ω) : K := lpsMass C B j X / lpsMass C B j Finset.univ

/-- A leading coefficient is non-negative (`0` for a chance-null leaf).
Source: none: infrastructure. Kind: L -/
theorem leafLead_nonneg (ℓ : B.Leaves) : 0 ≤ leafLead C B ℓ := by
  unfold leafLead
  by_cases h : leafLawPoly C B ℓ = 0
  · rw [h, Polynomial.trailingCoeff_zero]
  · exact (posTrail_leafLawPoly C B ℓ h).le

/-- Level masses are monotone in the event. Source: none: infrastructure. Kind: L -/
theorem lpsMass_mono (j : ℕ) {X Y : Finset Ω} (h : X ⊆ Y) : lpsMass C B j X ≤ lpsMass C B j Y := by
  unfold lpsMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ (fun ℓ hℓ => by rw [mem_worldEv] at hℓ ⊢; exact h hℓ)
  · intro ℓ _ _; exact leafLead_nonneg C B ℓ

/-- The coefficient of `ε^k` in `nuPoly Y` is the level-`k` mass of `Y`, provided no non-null
`Y`-leaf has order below `k`.
Source: none: infrastructure. Kind: L -/
theorem coeff_nuPoly_eq_lpsMass (Y : Finset Ω) (k : ℕ)
    (hk : ∀ ℓ ∈ worldEv B Y, leafLawPoly C B ℓ ≠ 0 → k ≤ (leafLawPoly C B ℓ).natTrailingDegree) :
    (nuPoly C B Y).coeff k = lpsMass C B k Y := by
  unfold nuPoly lpsMass
  rw [Polynomial.finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  by_cases h : leafLawPoly C B ℓ = 0
  · simp only [leafOrder, leafLead, h, Polynomial.coeff_zero, Polynomial.trailingCoeff_zero,
      ite_self]
  · rw [coeff_eq_ite_of_le (hk ℓ hℓ h)]; rfl

/-- **The LPS reading of Definition 10**: `limitCond X O` is the conditional of the level
`k = ord (nuPoly O)` — the first lexicographic level giving `O` mass — i.e. the ratio of the
level-`k` masses of `X ∩ O` and `O`. (Unconditional: at an unreachable `O` both sides are the
junk `0/0`.)
Source: P07 I2′ ("Popper functions correspond to a subclass of lexicographic probability
systems and these to nonstandard probabilities (Halpern), and each ray of trembles selects
one"); SL-12
Kind: C (regraded from P in repair round 1: with `lpsMass` defined as the level-`k` mass, this
is `coeff_nuPoly_eq_lpsMass` applied twice over `natTrailingDegree_nuPoly_le_leaf`)
Fidelity: exact (levels by order in `ε`; the uniform ray)
Hyps: none -/
theorem limitCond_eq_lps (X O : Finset Ω) :
    limitCond C B X O =
      lpsMass C B (nuPoly C B O).natTrailingDegree (X ∩ O) /
        lpsMass C B (nuPoly C B O).natTrailingDegree O := by
  unfold limitCond
  rw [coeff_nuPoly_eq_lpsMass C B (X ∩ O) _
      (fun ℓ hℓ hne => natTrailingDegree_nuPoly_le_leaf C B O (worldEv_inter_subset B X O hℓ) hne),
    coeff_nuPoly_eq_lpsMass C B O _
      (fun ℓ hℓ hne => natTrailingDegree_nuPoly_le_leaf C B O hℓ hne)]

/-- The same in normalised form: `limitCond X O = lps k (X ∩ O) / lps k O` where `O` is
tremble-reachable (so level `k` has positive total mass).
Source: P07 I2′
Kind: L -/
theorem limitCond_eq_lps_normalised (X O : Finset Ω) (h : nuPoly C B O ≠ 0) :
    limitCond C B X O =
      lps C B (nuPoly C B O).natTrailingDegree (X ∩ O) /
        lps C B (nuPoly C B O).natTrailingDegree O := by
  have hpos : 0 < lpsMass C B (nuPoly C B O).natTrailingDegree Finset.univ := by
    have h1 : 0 < lpsMass C B (nuPoly C B O).natTrailingDegree O := by
      rw [← coeff_nuPoly_eq_lpsMass C B O _
        (fun ℓ hℓ hne => natTrailingDegree_nuPoly_le_leaf C B O hℓ hne)]
      exact trailingCoeff_nuPoly_pos C B O h
    exact lt_of_lt_of_le h1 (lpsMass_mono C B _ (Finset.subset_univ O))
  unfold lps
  rw [div_div_div_cancel_right₀ hpos.ne', limitCond_eq_lps]

/-- Level `0` is `ν_C`: the unnormalised level-`0` mass of `X` is `ν_{B,C}(X)`.
Source: P07 I2′ ("the first level is `ν_C`"); `coeff_zero_nuPoly`
Kind: L -/
theorem lpsMass_zero_eq_nu (X : Finset Ω) : lpsMass C B 0 X = nu C B X := by
  rw [← coeff_nuPoly_eq_lpsMass C B X 0 (fun _ _ _ => Nat.zero_le _), coeff_zero_nuPoly]

/-- **Level `0` of the LPS is `ν_C`** (normalised).
Source: P07 I2′ ("each ray selects a lexicographic probability system whose first level is
`ν_C`")
Kind: P
Fidelity: exact -/
theorem lps_zero_eq_nu (X : Finset Ω) : lps C B 0 X = nu C B X := by
  unfold lps
  rw [lpsMass_zero_eq_nu, lpsMass_zero_eq_nu, nu_univ, div_one]

end tree

/-! ## N+: two levels on Told-You-So under `(five, five)` -/

/-- **Told-You-So under `(five, five)` has two lexicographic levels**: level `0` (= `ν_C`,
the point mass at `(5,5)`) gives `O₁₀ = {n = 10}` mass `0`, level `1` gives it mass `½`
(the leaves `(10,10)` and `(10,5)` each of order `1`); `O₁₀` is tremble-reachable of order
`1`, so `limitCond {(10,5)} O₁₀` (= `1`, `tys_take5_strict_not_limit`) is level-`1`
conditioning: `lpsMass 1 ({(10,5)} ∩ O₁₀) / lpsMass 1 O₁₀ = (½)/(½)`.
Source: P07 I2′; `dp-calibration` `tys_take5_coeffs`, `tys_take5_deg_obs`
Kind: N+
Fidelity: exact
Hyps: none -/
theorem tys_take5_lps_levels :
    lpsMass procTake5 toldYouSo 0 (tysObs .ten) = 0 ∧
    lpsMass procTake5 toldYouSo 1 (tysObs .ten) = 1 / 2 ∧
    lpsMass procTake5 toldYouSo 0 Finset.univ = 1 ∧
    lpsMass procTake5 toldYouSo 1 ({(Five10.ten, Five10.five)} ∩ tysObs .ten) = 1 / 2 ∧
    limitCond procTake5 toldYouSo {(Five10.ten, Five10.five)} (tysObs .ten) =
      lpsMass procTake5 toldYouSo 1 ({(Five10.ten, Five10.five)} ∩ tysObs .ten) /
        lpsMass procTake5 toldYouSo 1 (tysObs .ten) := by
  obtain ⟨h0, h1, hX0, hX1, -⟩ := tys_take5_coeffs
  have hdeg := tys_take5_deg_obs
  have hk1 : ∀ Y, ∀ ℓ ∈ worldEv toldYouSo (Y ∩ tysObs .ten), leafLawPoly procTake5 toldYouSo ℓ ≠ 0 →
      1 ≤ (leafLawPoly procTake5 toldYouSo ℓ).natTrailingDegree := fun Y ℓ hℓ hne => by
    have := natTrailingDegree_nuPoly_le_leaf procTake5 toldYouSo (tysObs .ten)
      (worldEv_inter_subset toldYouSo Y _ hℓ) hne
    rwa [hdeg] at this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [lpsMass_zero_eq_nu, ← coeff_zero_nuPoly, h0]
  · have := hk1 Finset.univ
    rw [Finset.univ_inter] at this
    rw [← coeff_nuPoly_eq_lpsMass procTake5 toldYouSo _ 1 this, h1]
  · rw [lpsMass_zero_eq_nu, nu_univ]
  · rw [← coeff_nuPoly_eq_lpsMass procTake5 toldYouSo _ 1 (hk1 _), hX1]
    simp
  · rw [limitCond_eq_lps, hdeg]

end Cleanroom.Decision.DpCalibLimits
