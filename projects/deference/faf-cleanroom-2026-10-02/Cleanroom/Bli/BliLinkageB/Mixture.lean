import Cleanroom.Bli.BliLinkageB.Defs

/-!
# bli-linkage, angle B — the partition engine on a world mixture

Every determination theorem of this angle (bracket or exact) runs the same argument inside
a finite world mixture: under the partition constraint `E5σ` (mass one, exclusivity in
`P`-measure), **every charged world holds exactly one candidate state**, so `P n ψ` splits as
`∑_q P n (ψ ⋏ σ_q)` (the law of total probability over the partition), and each summand is
read off world by world from what the state forces. This module proves that engine over an
abstract mixture `(W, w)` and abstract state day `m`; `Bracket.lean` and `Determination.lean`
instantiate it. It is the (⇐) direction of `bli-trajectory`'s `Partition.e4_iff_partition_mass`
made reusable (that proof is inlined there, over B1's `stateAtom`).

Everything here is infrastructure (`L`), with no headline.
-/

namespace Cleanroom.Bli.BliLinkageB

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

/-! ## Payout laws (re-proved locally; `bli-trajectory` has them behind its parser import) -/

/-- A world's payout on a conjunction is the product of the payouts.
Source: none: infrastructure (FAF `PCWorld.holds_and`)
Kind: L
Fidelity: n/a -/
lemma payout_and (v : PCWorld) (φ ψ : Sentence) :
    v.payout (φ ⋏ ψ) = v.payout φ * v.payout ψ := by
  unfold PCWorld.payout
  by_cases hφ : v.Holds φ <;> by_cases hψ : v.Holds ψ <;> simp [PCWorld.holds_and, hφ, hψ]

/-- Payouts are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_nonneg (v : PCWorld) (φ : Sentence) : 0 ≤ v.payout φ := (payout_mem_Icc v φ).1

/-- The payout of a held sentence is `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_of_holds {v : PCWorld} {φ : Sentence} (h : v.Holds φ) : v.payout φ = 1 := by
  unfold PCWorld.payout; rw [if_pos h]

/-- The payout of a refuted sentence is `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_of_not_holds {v : PCWorld} {φ : Sentence} (h : ¬ v.Holds φ) : v.payout φ = 0 := by
  unfold PCWorld.payout; rw [if_neg h]

/-- A sentence with payout `≠ 0` holds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_of_payout_ne_zero {v : PCWorld} {φ : Sentence} (h : v.payout φ ≠ 0) : v.Holds φ := by
  by_contra hc; exact h (payout_of_not_holds hc)

/-! ## Mixtures -/

/-- **A finite world mixture representing `p` on the algebra of `A`**: nonnegative weights
summing to one, and `p φ = ∑ᵢ wᵢ · payoutᵢ φ` for every `φ` with atoms in `A`. `CoherentOnW 𝒲 A p`
is the existence of one whose worlds lie in `𝒲` (`coherentOnW_iff`).
Source: none: infrastructure (bli-found `Constraints.CoherentOn` unpacked)
Kind: D
Fidelity: n/a -/
structure IsMixture {k : ℕ} (W : Fin k → PCWorld) (w : Fin k → ℝ) (A : Finset ℕ)
    (p : Sentence → ℝ) : Prop where
  /-- Nonnegative weights. -/
  nonneg : ∀ i, 0 ≤ w i
  /-- Weights sum to one. -/
  sum_one : ∑ i, w i = 1
  /-- The representation on the algebra of `A`. -/
  rep : ∀ φ, sentenceAtomCodes φ ⊆ A → p φ = ∑ i, w i * (W i).payout φ

/-- `CoherentOnW` unpacked.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem coherentOnW_iff (𝒲 : PCWorld → Prop) (A : Finset ℕ) (p : Sentence → ℝ) :
    CoherentOnW 𝒲 A p ↔
      ∃ (k : ℕ) (W : Fin k → PCWorld) (w : Fin k → ℝ), (∀ i, 𝒲 (W i)) ∧ IsMixture W w A p := by
  constructor
  · rintro ⟨k, W, w, hW, hw, hsum, hrep⟩
    exact ⟨k, W, w, hW, ⟨hw, hsum, hrep⟩⟩
  · rintro ⟨k, W, w, hW, ⟨hw, hsum, hrep⟩⟩
    exact ⟨k, W, w, hW, hw, hsum, hrep⟩

section Mixture

variable {k : ℕ} {W : Fin k → PCWorld} {w : Fin k → ℝ} {A : Finset ℕ} {p : Sentence → ℝ}

/-- A represented sentence has nonnegative `p`-value.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsMixture.nonneg_of_subset (hM : IsMixture W w A p) {ψ : Sentence}
    (hψ : sentenceAtomCodes ψ ⊆ A) : 0 ≤ p ψ := by
  rw [hM.rep ψ hψ]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hM.nonneg i) (payout_nonneg _ _)

/-- A represented sentence has `p`-value at most one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsMixture.le_one_of_subset (hM : IsMixture W w A p) {ψ : Sentence}
    (hψ : sentenceAtomCodes ψ ⊆ A) : p ψ ≤ 1 := by
  rw [hM.rep ψ hψ, ← hM.sum_one]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_of_le_one_right (hM.nonneg i) (payout_mem_Icc _ _).2

/-- If `p ψ = 0` for a represented `ψ`, no charged world holds `ψ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsMixture.not_holds_of_eq_zero (hM : IsMixture W w A p) {ψ : Sentence}
    (hψ : sentenceAtomCodes ψ ⊆ A) (h0 : p ψ = 0) {i : Fin k} (hi : 0 < w i) :
    ¬ (W i).Holds ψ := by
  intro hh
  rw [hM.rep ψ hψ] at h0
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (hM.nonneg j) (payout_nonneg (W j) ψ))).1 h0 i (Finset.mem_univ i)
  rw [payout_of_holds hh, mul_one] at this
  exact absurd this (ne_of_gt hi)

/-! ## The partition constraint -/

/-- **The partition constraint at state day `m`**, in `p`-measure: the candidates' masses sum
to one and distinct candidates are exclusive. `E5σ` at day `n` is this at `p := P n`, `m := n+1`
(`partitionAt_of_E5σ`).
Source: bli-found `Constraints.E5σ`
Kind: D
Fidelity: n/a -/
structure PartitionAt (σ : ℕ → ℕ → Sentence) (S : StateSystem) (p : Sentence → ℝ) (m : ℕ) :
    Prop where
  /-- Mass one on the candidates. -/
  mass : ∑ q ∈ S.states m, p (σ m q) = 1
  /-- Exclusivity in `p`-measure. -/
  excl : ∀ q₁ ∈ S.states m, ∀ q₂ ∈ S.states m, q₁ ≠ q₂ → p (σ m q₁ ⋏ σ m q₂) = 0

/-- `E5σ` at day `n` is `PartitionAt` at `(P n, n+1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem partitionAt_of_E5σ {σ : ℕ → ℕ → Sentence} {S : StateSystem} {P : History} (h : E5σ σ S P)
    (n : ℕ) : PartitionAt σ S (P n) (n + 1) := ⟨(h n).1, (h n).2⟩

variable {σ : ℕ → ℕ → Sentence} {S : StateSystem} {m : ℕ}

/-- **A charged world holds at most one candidate.**
Source: bli-trajectory `Partition.e4_iff_partition_mass` (⇐), the exclusivity step
Kind: L
Fidelity: n/a -/
theorem IsMixture.charged_not_both (hM : IsMixture W w A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A) (hpart : PartitionAt σ S p m)
    {i : Fin k} (hi : 0 < w i) {q₁ q₂ : ℕ} (hq₁ : q₁ ∈ S.states m) (hq₂ : q₂ ∈ S.states m)
    (hne : q₁ ≠ q₂) : ¬ ((W i).Holds (σ m q₁) ∧ (W i).Holds (σ m q₂)) := by
  have hA : sentenceAtomCodes (σ m q₁ ⋏ σ m q₂) ⊆ A := by
    rw [sentenceAtomCodes_and]; exact Finset.union_subset (hσA q₁ hq₁) (hσA q₂ hq₂)
  have := hM.not_holds_of_eq_zero hA (hpart.excl q₁ hq₁ q₂ hq₂ hne) hi
  rwa [PCWorld.holds_and] at this

/-- In a charged world the candidates' payouts sum to at most one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsMixture.charged_sum_payout_le_one (hM : IsMixture W w A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A) (hpart : PartitionAt σ S p m)
    {i : Fin k} (hi : 0 < w i) : ∑ q ∈ S.states m, (W i).payout (σ m q) ≤ 1 := by
  by_cases h : ∃ q₀ ∈ S.states m, (W i).Holds (σ m q₀)
  · obtain ⟨q₀, hq₀, hh⟩ := h
    rw [Finset.sum_eq_single_of_mem q₀ hq₀ (fun q hq hne => payout_of_not_holds
      (fun hq' => hM.charged_not_both hσA hpart hi hq hq₀ hne ⟨hq', hh⟩))]
    rw [payout_of_holds hh]
  · rw [Finset.sum_eq_zero fun q hq => payout_of_not_holds fun hh => h ⟨q, hq, hh⟩]
    exact zero_le_one

/-- **A charged world holds exactly one candidate**: the candidates' payouts sum to one.
Source: bli-trajectory `Partition.e4_iff_partition_mass` (⇐), the mass-one step
Kind: L
Fidelity: n/a -/
theorem IsMixture.charged_sum_payout_eq_one (hM : IsMixture W w A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A) (hpart : PartitionAt σ S p m)
    {i : Fin k} (hi : 0 < w i) : ∑ q ∈ S.states m, (W i).payout (σ m q) = 1 := by
  set s : Fin k → ℝ := fun j => ∑ q ∈ S.states m, (W j).payout (σ m q) with hs
  have hmass : ∑ j, w j * s j = 1 := by
    have h1 : ∑ q ∈ S.states m, ∑ j : Fin k, w j * (W j).payout (σ m q) = 1 := by
      rw [← hpart.mass]
      exact Finset.sum_congr rfl fun q hq => (hM.rep (σ m q) (hσA q hq)).symm
    rw [Finset.sum_comm] at h1
    simp_rw [hs, Finset.mul_sum]
    exact h1
  have hzero : ∑ j, w j * (1 - s j) = 0 := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, hM.sum_one, hmass, sub_self]
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin k)), 0 ≤ w j * (1 - s j) := by
    intro j _
    rcases (hM.nonneg j).lt_or_eq with hj | hj
    · exact mul_nonneg hj.le (sub_nonneg.2 (hM.charged_sum_payout_le_one hσA hpart hj))
    · rw [← hj, zero_mul]
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hzero i (Finset.mem_univ i)
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (ne_of_gt hi)
  · exact (sub_eq_zero.1 h).symm

/-- A charged world holds some candidate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsMixture.charged_exists_state (hM : IsMixture W w A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A) (hpart : PartitionAt σ S p m)
    {i : Fin k} (hi : 0 < w i) : ∃ q ∈ S.states m, (W i).Holds (σ m q) := by
  by_contra h
  have h1 := hM.charged_sum_payout_eq_one hσA hpart hi
  rw [Finset.sum_eq_zero fun q hq => payout_of_not_holds fun hh => h ⟨q, hq, hh⟩] at h1
  exact zero_ne_one h1

/-- **Exactly one candidate holds in a charged world.**
Source: bli-trajectory `Partition.e4_iff_partition_mass` (⇐)
Kind: L
Fidelity: n/a -/
theorem IsMixture.charged_unique_state (hM : IsMixture W w A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A) (hpart : PartitionAt σ S p m)
    {i : Fin k} (hi : 0 < w i) :
    ∃ q ∈ S.states m, (W i).Holds (σ m q) ∧
      ∀ q' ∈ S.states m, (W i).Holds (σ m q') → q' = q := by
  obtain ⟨q, hq, hh⟩ := hM.charged_exists_state hσA hpart hi
  refine ⟨q, hq, hh, fun q' hq' hh' => ?_⟩
  by_contra hne
  exact hM.charged_not_both hσA hpart hi hq' hq hne ⟨hh', hh⟩

/-- **The law of total probability over the partition**: `p ψ = ∑_q p (ψ ⋏ σ_q)` for every
represented `ψ`.
Source: mandate K2 ("`P n φ = ∑_q P n (φ ⋏ σ_q)` in a world mixture where exactly one state holds")
Kind: L
Fidelity: n/a -/
theorem IsMixture.sum_and_state (hM : IsMixture W w A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A) (hpart : PartitionAt σ S p m)
    {ψ : Sentence} (hψA : sentenceAtomCodes ψ ⊆ A) :
    p ψ = ∑ q ∈ S.states m, p (ψ ⋏ σ m q) := by
  have hA : ∀ q ∈ S.states m, sentenceAtomCodes (ψ ⋏ σ m q) ⊆ A := fun q hq => by
    rw [sentenceAtomCodes_and]; exact Finset.union_subset hψA (hσA q hq)
  rw [Finset.sum_congr rfl (fun q hq => hM.rep _ (hA q hq)), Finset.sum_comm, hM.rep ψ hψA]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [payout_and]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rcases (hM.nonneg i).lt_or_eq with hi | hi
  · rw [hM.charged_sum_payout_eq_one hσA hpart hi, mul_one]
  · rw [← hi, zero_mul, zero_mul]

/-- If every charged world holding `σ_q` holds `ψ`, then `p (ψ ⋏ σ_q) = p σ_q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsMixture.and_state_eq_of_forced (hM : IsMixture W w A p) {q : ℕ}
    (hσq : sentenceAtomCodes (σ m q) ⊆ A) {ψ : Sentence} (hψA : sentenceAtomCodes ψ ⊆ A)
    (hforce : ∀ i, 0 < w i → (W i).Holds (σ m q) → (W i).Holds ψ) :
    p (ψ ⋏ σ m q) = p (σ m q) := by
  have hA : sentenceAtomCodes (ψ ⋏ σ m q) ⊆ A := by
    rw [sentenceAtomCodes_and]; exact Finset.union_subset hψA hσq
  rw [hM.rep _ hA, hM.rep _ hσq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases (hM.nonneg i).lt_or_eq with hi | hi
  · congr 1
    by_cases hs : (W i).Holds (σ m q)
    · rw [payout_and, payout_of_holds (hforce i hi hs), one_mul]
    · rw [payout_and, payout_of_not_holds hs, mul_zero]
  · rw [← hi, zero_mul, zero_mul]

/-- If no charged world holds both `σ_q` and `ψ`, then `p (ψ ⋏ σ_q) = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsMixture.and_state_eq_zero_of_excluded (hM : IsMixture W w A p) {q : ℕ}
    (hσq : sentenceAtomCodes (σ m q) ⊆ A) {ψ : Sentence} (hψA : sentenceAtomCodes ψ ⊆ A)
    (hexcl : ∀ i, 0 < w i → (W i).Holds (σ m q) → ¬ (W i).Holds ψ) :
    p (ψ ⋏ σ m q) = 0 := by
  have hA : sentenceAtomCodes (ψ ⋏ σ m q) ⊆ A := by
    rw [sentenceAtomCodes_and]; exact Finset.union_subset hψA hσq
  rw [hM.rep _ hA]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases (hM.nonneg i).lt_or_eq with hi | hi
  · by_cases hs : (W i).Holds (σ m q)
    · rw [payout_and, payout_of_not_holds (hexcl i hi hs), zero_mul, mul_zero]
    · rw [payout_and, payout_of_not_holds hs, mul_zero, mul_zero]
  · rw [← hi, zero_mul]

/-- `p (ψ ⋏ σ_q) ≤ p σ_q` for represented sentences.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsMixture.and_state_le (hM : IsMixture W w A p) {q : ℕ}
    (hσq : sentenceAtomCodes (σ m q) ⊆ A) {ψ : Sentence} (hψA : sentenceAtomCodes ψ ⊆ A) :
    p (ψ ⋏ σ m q) ≤ p (σ m q) := by
  have hA : sentenceAtomCodes (ψ ⋏ σ m q) ⊆ A := by
    rw [sentenceAtomCodes_and]; exact Finset.union_subset hψA hσq
  rw [hM.rep _ hA, hM.rep _ hσq]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [payout_and]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (payout_nonneg _ _) (payout_mem_Icc _ _).2) (hM.nonneg i)

/-- `0 ≤ p (ψ ⋏ σ_q)` for represented sentences.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsMixture.and_state_nonneg (hM : IsMixture W w A p) {q : ℕ}
    (hσq : sentenceAtomCodes (σ m q) ⊆ A) {ψ : Sentence} (hψA : sentenceAtomCodes ψ ⊆ A) :
    0 ≤ p (ψ ⋏ σ m q) :=
  hM.nonneg_of_subset (by rw [sentenceAtomCodes_and]; exact Finset.union_subset hψA hσq)

end Mixture

end Cleanroom.Bli.BliLinkageB
