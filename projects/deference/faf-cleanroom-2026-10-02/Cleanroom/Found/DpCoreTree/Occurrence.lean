import Cleanroom.Found.DpCoreTree.Basic

/-!
# Lemma 1 (occurrence constancy), the reach mass, and Lemma 1 under Definition 6′

T4 of [[dp-core-tree-mandate]]. `μ_{B,C}(occ(d))` does not depend on `C(d)`: proved in the
general form `mass_occ_congr_off` (procedures agreeing off `d` give `occ(d)` the same mass),
of which Lemma 1 (`occurrence_constancy`: every point-deviation `C[d ↦ m]`) is a corollary.
The proof is by structural recursion: at a `d`-node the whole subtree lies in `occ(d)`, so its
contribution is `∑_a C(d)(a) · 1 = 1` whatever `C(d)` is; every other node contributes a
`C(d)`-free weight.

Also: equation lemmas for the node-level definitions of `Nodes.lean`; `reach C B q = μ_{B,C}
(leavesBelow q)` (v2 §8's `R_q` as a mass); the shared-seed walk is a probability and Lemma 1
holds under Definition 6′ (SE-1(c)).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)]

namespace Tree

/-! ### Equation lemmas for node-level definitions -/

section nodeEqns

variable (C : Proc ι acts K)

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem pt_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (i : Fin n) (q : (child i).DecNode) : pt (chance n β child) ⟨i, q⟩ = pt (child i) q := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem pt_decision_none (d : ι) (child : acts d → Tree Ω ι acts K) :
    pt (decision d child) none = d := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem pt_decision_some (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d)
    (q : (child a).DecNode) : pt (decision d child) (some ⟨a, q⟩) = pt (child a) q := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem ancestorPts_chance {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (i : Fin n) (q : (child i).DecNode) :
    ancestorPts (chance n β child) ⟨i, q⟩ = ancestorPts (child i) q := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem ancestorPts_decision_none (d : ι) (child : acts d → Tree Ω ι acts K) :
    ancestorPts (decision d child) none = [] := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem ancestorPts_decision_some (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d)
    (q : (child a).DecNode) :
    ancestorPts (decision d child) (some ⟨a, q⟩) = d :: ancestorPts (child a) q := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem reach_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (i : Fin n) (q : (child i).DecNode) :
    reach C (chance n β child) ⟨i, q⟩ = β.w i * reach C (child i) q := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem reach_decision_none (d : ι) (child : acts d → Tree Ω ι acts K) :
    reach C (decision d child) none = 1 := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem reach_decision_some (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d)
    (q : (child a).DecNode) :
    reach C (decision d child) (some ⟨a, q⟩) = (C d).w a * reach C (child a) q := rfl

variable [∀ d, DecidableEq (acts d)]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem edgeOf_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (i : Fin n) (q : (child i).DecNode) (j : Fin n) (ℓ : (child j).Leaves) :
    edgeOf (chance n β child) ⟨i, q⟩ ⟨j, ℓ⟩ =
      if h : j = i then edgeOf (child i) q (h ▸ ℓ) else none := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem edgeOf_decision_none (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d)
    (ℓ : (child a).Leaves) : edgeOf (decision d child) none ⟨a, ℓ⟩ = some a := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem edgeOf_decision_some (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d)
    (q : (child a).DecNode) (b : acts d) (ℓ : (child b).Leaves) :
    edgeOf (decision d child) (some ⟨a, q⟩) ⟨b, ℓ⟩ =
      if h : b = a then edgeOf (child a) q (h ▸ ℓ) else none := rfl

/-- Membership in `leavesBelow`.
Source: none: infrastructure
Kind: L -/
@[simp] theorem mem_leavesBelow (B : Tree Ω ι acts K) (q : B.DecNode) (ℓ : B.Leaves) :
    ℓ ∈ leavesBelow B q ↔ (edgeOf B q ℓ).isSome := by
  simp [leavesBelow]

end nodeEqns

/-! ### Lemma 1: occurrence constancy -/

/-- Pull a constant factor out of an indicator.
Source: none: infrastructure
Kind: L -/
theorem ite_mul_zero_eq {P : Prop} [Decidable P] (c f : K) :
    (if P then c * f else 0) = c * if P then f else 0 := by
  split_ifs <;> simp

section occurrence

variable [DecidableEq ι] (C : Proc ι acts K)

/-- `μ_{B,C}(occ(d))` as an indicator sum over leaves.
Source: none: infrastructure
Kind: L -/
theorem mass_occ (B : Tree Ω ι acts K) (d : ι) :
    mass C B (occ d B) = ∑ ℓ, if 0 < count d B ℓ then leafLaw C B ℓ else 0 :=
  mass_filter C B _

/-- **Lemma 1, general form**: two procedures that agree at every point other than `d` give
`occ(d)` the same mass. (`μ_{B,C}(occ(d))` is a function of `C` off `d`.)
Source: [[decision-problems-v2]] §3.1 Lemma 1
Kind: P
Fidelity: stronger (agreement off `d` rather than a single point-deviation) -/
theorem mass_occ_congr_off (d : ι) :
    (B : Tree Ω ι acts K) → ∀ {C C' : Proc ι acts K}, (∀ d', d' ≠ d → C d' = C' d') →
      mass C B (occ d B) = mass C' B (occ d B)
  | leaf _ _, _, _, _ => by simp [mass_occ]
  | chance _ β child, C, C', h => by
      have ih : ∀ i, (∑ ℓ, if 0 < count d (child i) ℓ then leafLaw C (child i) ℓ else 0) =
          ∑ ℓ, if 0 < count d (child i) ℓ then leafLaw C' (child i) ℓ else 0 := fun i => by
        rw [← mass_occ, ← mass_occ]; exact mass_occ_congr_off d (child i) h
      rw [mass_occ, mass_occ, sum_leaves_chance, sum_leaves_chance]
      simp only [count_chance, leafLaw_chance, ite_mul_zero_eq, ← Finset.mul_sum, ih]
  | decision d' child, C, C', h => by
      have ih : ∀ a, (∑ ℓ, if 0 < count d (child a) ℓ then leafLaw C (child a) ℓ else 0) =
          ∑ ℓ, if 0 < count d (child a) ℓ then leafLaw C' (child a) ℓ else 0 := fun a => by
        rw [← mass_occ, ← mass_occ]; exact mass_occ_congr_off d (child a) h
      rw [mass_occ, mass_occ, sum_leaves_decision, sum_leaves_decision]
      by_cases hd : d' = d
      · subst hd
        have hpos : ∀ n : ℕ, 0 < 1 + n := fun n => by omega
        simp only [count_decision, if_true, leafLaw_decision, hpos, ← Finset.mul_sum,
          sum_leafLaw, mul_one, FinDistr.sum_one]
      · simp only [count_decision, hd, if_false, zero_add, leafLaw_decision, ite_mul_zero_eq,
          ← Finset.mul_sum, ih, h d' hd]

/-- **Lemma 1 (occurrence constancy)**: `μ_{B,C[d↦m]}(occ(d)) = μ_{B,C}(occ(d))` for every `m`.
A one-line specialisation of `mass_occ_congr_off` (the `P` row), kept under the source's name.
Source: [[decision-problems-v2]] §3.1 Lemma 1
Kind: L
Fidelity: exact
Hyps: none -/
theorem occurrence_constancy (B : Tree Ω ι acts K) (d : ι) (m : FinDistr K (acts d)) :
    mass (C.deviate d m) B (occ d B) = mass C B (occ d B) :=
  mass_occ_congr_off d B fun _ h => Proc.deviate_ne C m h

end occurrence

/-! ### The reach mass -/

section reach

variable [∀ d, DecidableEq (acts d)] (C : Proc ι acts K)

/-- `R_q(C) = μ_{B,C}(leavesBelow q)`: the path product to `q` is the mass of the leaves below it.
Source: [[decision-problems-v2]] §8 (`R_q(C) := μ_{B,C}(reach q)`)
Kind: P -/
theorem reach_eq_mass_leavesBelow :
    (B : Tree Ω ι acts K) → ∀ q, reach C B q = mass C B (leavesBelow B q)
  | leaf _ _, q => q.elim
  | chance _ β child, ⟨i, q⟩ => by
      rw [reach_chance, reach_eq_mass_leavesBelow (child i) q]
      unfold mass leavesBelow
      rw [Finset.sum_filter, Finset.sum_filter, sum_leaves_chance]
      rw [Finset.sum_eq_single i]
      · simp only [edgeOf_chance, dite_true, leafLaw_chance, mul_ite, mul_zero, Finset.mul_sum]
        rfl
      · intro j _ hj
        simp [edgeOf_chance, hj]
      · intro h; exact absurd (Finset.mem_univ i) h
  | decision d child, none => by
      rw [reach_decision_none]
      unfold mass leavesBelow
      rw [Finset.sum_filter, sum_leaves_decision]
      simp [← Finset.mul_sum, sum_leafLaw, (C d).sum_one]
  | decision d child, some ⟨a, q⟩ => by
      rw [reach_decision_some, reach_eq_mass_leavesBelow (child a) q]
      unfold mass leavesBelow
      rw [Finset.sum_filter, Finset.sum_filter, sum_leaves_decision]
      rw [Finset.sum_eq_single a]
      · simp only [edgeOf_decision_some, dite_true, leafLaw_decision, mul_ite, mul_zero,
          Finset.mul_sum]
        rfl
      · intro b _ hb
        simp [edgeOf_decision_some, hb]
      · intro h; exact absurd (Finset.mem_univ a) h

/-- `0 ≤ R_q`.
Source: none: infrastructure
Kind: L -/
theorem reach_nonneg (B : Tree Ω ι acts K) (q : B.DecNode) : 0 ≤ reach C B q := by
  rw [reach_eq_mass_leavesBelow]; exact mass_nonneg C B _

end reach

/-! ### Definition 6′: the memoised walk is a probability; Lemma 1 under 6′ -/

section seed

variable [DecidableEq ι] [∀ d, DecidableEq (acts d)] (C : Proc ι acts K)

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem leafLawSeed_leaf (env : (d : ι) → Option (acts d)) (ω : Ω) (r : K)
    (ℓ : (leaf ω r : Tree Ω ι acts K).Leaves) : leafLawSeed C env (leaf ω r) ℓ = 1 := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem leafLawSeed_chance (env : (d : ι) → Option (acts d)) {n : ℕ}
    (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K) (i : Fin n) (ℓ : (child i).Leaves) :
    leafLawSeed C env (chance n β child) ⟨i, ℓ⟩ = β.w i * leafLawSeed C env (child i) ℓ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem leafLawSeed_decision_of_some {env : (d : ι) → Option (acts d)} {d : ι} {a' : acts d}
    (h : env d = some a') (child : acts d → Tree Ω ι acts K) (a : acts d) (ℓ : (child a).Leaves) :
    leafLawSeed C env (decision d child) ⟨a, ℓ⟩ =
      if a' = a then leafLawSeed C env (child a) ℓ else 0 := by
  simp only [leafLawSeed, h]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem leafLawSeed_decision_of_none {env : (d : ι) → Option (acts d)} {d : ι}
    (h : env d = none) (child : acts d → Tree Ω ι acts K) (a : acts d) (ℓ : (child a).Leaves) :
    leafLawSeed C env (decision d child) ⟨a, ℓ⟩ =
      (C d).w a * leafLawSeed C (Function.update env d (some a)) (child a) ℓ := by
  simp only [leafLawSeed, h]

/-- The memoised walk gives non-negative masses.
Source: `seeds.md` Definition 6′
Kind: L -/
theorem leafLawSeed_nonneg :
    (B : Tree Ω ι acts K) → ∀ env ℓ, 0 ≤ leafLawSeed C env B ℓ
  | leaf _ _, _, _ => zero_le_one
  | chance _ β child, env, ⟨i, ℓ⟩ =>
      mul_nonneg (β.nonneg i) (leafLawSeed_nonneg (child i) env ℓ)
  | decision d child, env, ⟨a, ℓ⟩ => by
      rcases h : env d with _ | a'
      · rw [leafLawSeed_decision_of_none C h]
        exact mul_nonneg ((C d).nonneg a) (leafLawSeed_nonneg (child a) _ ℓ)
      · rw [leafLawSeed_decision_of_some C h]
        split_ifs
        · exact leafLawSeed_nonneg (child a) env ℓ
        · exact le_rfl

/-- The memoised walk is a probability on the leaves, from any seed environment.
Source: `seeds.md` Definition 6′ (`μ'_{B,C} ∈ Δ(Leaves(B))`)
Kind: L -/
theorem sum_leafLawSeed :
    (B : Tree Ω ι acts K) → ∀ env, ∑ ℓ, leafLawSeed C env B ℓ = 1
  | leaf _ _, _ => by
      show ∑ _ℓ : Unit, (1 : K) = 1
      simp
  | chance _ β child, env => by
      have ih : ∀ i, ∑ ℓ, leafLawSeed C env (child i) ℓ = 1 :=
        fun i => sum_leafLawSeed (child i) env
      rw [sum_leaves_chance]
      simp only [leafLawSeed_chance, ← Finset.mul_sum, ih, mul_one]
      exact β.sum_one
  | decision d child, env => by
      rw [sum_leaves_decision]
      rcases h : env d with _ | a'
      · have ih : ∀ a, ∑ ℓ, leafLawSeed C (Function.update env d (some a)) (child a) ℓ = 1 :=
          fun a => sum_leafLawSeed (child a) _
        simp only [leafLawSeed_decision_of_none C h, ← Finset.mul_sum, ih, mul_one]
        exact (C d).sum_one
      · have ih : ∀ a, ∑ ℓ, leafLawSeed C env (child a) ℓ = 1 :=
          fun a => sum_leafLawSeed (child a) env
        simp only [leafLawSeed_decision_of_some C h]
        rw [Finset.sum_eq_single a']
        · simp [ih]
        · intro b _ hb; simp [Ne.symm hb]
        · intro h; exact absurd (Finset.mem_univ a') h

/-- `∑_ℓ μ'_{B,C}(ℓ) = 1`.
Source: `seeds.md` Definition 6′
Kind: L -/
theorem sum_leafLaw' (B : Tree Ω ι acts K) : ∑ ℓ, leafLaw' C B ℓ = 1 :=
  sum_leafLawSeed C B _

/-- `0 ≤ μ'_{B,C}(ℓ)`.
Source: none: infrastructure
Kind: L -/
theorem leafLaw'_nonneg (B : Tree Ω ι acts K) (ℓ : B.Leaves) : 0 ≤ leafLaw' C B ℓ :=
  leafLawSeed_nonneg C B _ ℓ

/-- `0 ≤ ν'_{B,C}(X)`.
Source: none: infrastructure
Kind: L -/
theorem nu'_nonneg [DecidableEq Ω] (B : Tree Ω ι acts K) (X : Finset Ω) : 0 ≤ nu' C B X :=
  Finset.sum_nonneg fun ℓ _ => leafLaw'_nonneg C B ℓ

/-- `ν'_{B,C}(X) ≤ 1`.
Source: none: infrastructure
Kind: L -/
theorem nu'_le_one [DecidableEq Ω] (B : Tree Ω ι acts K) (X : Finset Ω) : nu' C B X ≤ 1 := by
  unfold nu'
  rw [← sum_leafLaw' C B]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun ℓ _ _ => leafLaw'_nonneg C B ℓ

/-- Lemma 1 under Definition 6′, general form: from any seed environment, the mass of
`occ(d)` under the memoised walk is the same for procedures agreeing off `d`.
Source: `seeds.md` SE-1(c) ("Lemma 1 holds verbatim under 6′")
Kind: P -/
theorem sum_occ_seed_congr_off (d : ι) :
    (B : Tree Ω ι acts K) → ∀ env {C C' : Proc ι acts K}, (∀ d', d' ≠ d → C d' = C' d') →
      (∑ ℓ, if 0 < count d B ℓ then leafLawSeed C env B ℓ else 0) =
        ∑ ℓ, if 0 < count d B ℓ then leafLawSeed C' env B ℓ else 0
  | leaf _ _, _, _, _, _ => by simp
  | chance _ β child, env, C, C', h => by
      have ih := fun i => sum_occ_seed_congr_off d (child i) env h
      rw [sum_leaves_chance, sum_leaves_chance]
      simp only [count_chance, leafLawSeed_chance, ite_mul_zero_eq, ← Finset.mul_sum, ih]
  | decision d' child, env, C, C', h => by
      rw [sum_leaves_decision, sum_leaves_decision]
      by_cases hd : d' = d
      · subst hd
        have hpos : ∀ n : ℕ, 0 < 1 + n := fun n => by omega
        simp only [count_decision, if_true, hpos]
        rcases henv : env d' with _ | a'
        · simp only [leafLawSeed_decision_of_none C henv, leafLawSeed_decision_of_none C' henv,
            ← Finset.mul_sum, sum_leafLawSeed, mul_one, FinDistr.sum_one]
        · simp only [leafLawSeed_decision_of_some C henv, leafLawSeed_decision_of_some C' henv]
          rw [Finset.sum_eq_single a', Finset.sum_eq_single a']
          · simp [sum_leafLawSeed]
          · intro b _ hb; simp [Ne.symm hb]
          · intro h; exact absurd (Finset.mem_univ a') h
          · intro b _ hb; simp [Ne.symm hb]
          · intro h; exact absurd (Finset.mem_univ a') h
      · have ih : ∀ a env', (∑ ℓ, if 0 < count d (child a) ℓ then leafLawSeed C env' (child a) ℓ else 0) =
            ∑ ℓ, if 0 < count d (child a) ℓ then leafLawSeed C' env' (child a) ℓ else 0 :=
          fun a env' => sum_occ_seed_congr_off d (child a) env' h
        simp only [count_decision, hd, if_false, zero_add]
        rcases henv : env d' with _ | a'
        · simp only [leafLawSeed_decision_of_none C henv, leafLawSeed_decision_of_none C' henv,
            ite_mul_zero_eq, ← Finset.mul_sum, h d' hd]
          exact Finset.sum_congr rfl fun a _ => by
            rw [sum_occ_seed_congr_off d (child a) _ h]
        · simp only [leafLawSeed_decision_of_some C henv, leafLawSeed_decision_of_some C' henv]
          exact Finset.sum_congr rfl fun a _ => by
            split_ifs
            · exact ih a env
            · simp

/-- **Lemma 1 under Definition 6′**: `μ'_{B,C[d↦m]}(occ(d)) = μ'_{B,C}(occ(d))`.
Source: `seeds.md` SE-1(c)
Kind: C
Fidelity: exact -/
theorem occurrence_constancy' (B : Tree Ω ι acts K) (d : ι) (m : FinDistr K (acts d)) :
    (∑ ℓ ∈ occ d B, leafLaw' (C.deviate d m) B ℓ) = ∑ ℓ ∈ occ d B, leafLaw' C B ℓ := by
  unfold occ leafLaw'
  rw [Finset.sum_filter, Finset.sum_filter]
  exact sum_occ_seed_congr_off d B _ fun _ h => Proc.deviate_ne C m h

end seed

end Tree

end Cleanroom.Found.DpCoreTree
