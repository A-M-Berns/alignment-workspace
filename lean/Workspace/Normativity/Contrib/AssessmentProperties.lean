/-
# Which Logical Induction properties generalize, and in what form

The paper's §4 properties are stated for an arbitrary market satisfying the
criterion, so the question is what their *hypotheses* mention of the deductive
process.  Reading the source, every one of them factors into exactly three kinds:

1. the criterion itself, `[IsLogicalInductor P DP]`;
2. **stagewise nonemptiness**, `∀ n, ∃ v, v.ConsistentWith (DP.D n)` — which is
   the round's `(L3)`, appearing here and not in the construction;
3. a condition on what the assessed worlds say, in one of two shapes:
   * *semantic* — `∀ n v, v.ConsistentWith (DP.D n) → …`, which is already a
     statement about the assessment set and transfers by substitution;
   * *syntactic* — `φ ∈ DP.D n`, which has no analogue for an arbitrary assessment
     process, and which the source proofs consume **only** by deriving its semantic
     consequence.

This file makes the third point a theorem rather than a reading, for the two
families whose exploiting trader is a constant: provability induction and the
refutation half of coherence.  Each is stated with the semantic hypothesis and each
carries a corollary recovering the source's syntactic hypothesis at the deductive
instance.

What is *not* claimed: that every family was re-derived.  The classification of the
rest is by hypothesis shape, recorded in the round's `PROOF_CLOSURE.md`, and two
families are excluded there because their *conclusions* are about completions of the
theory rather than about prices.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.AssessmentProcess
import LogicalInduction.Properties.ProvabilityInduction
import LogicalInduction.Properties.Coherence

namespace Workspace.Normativity.Contrib.AssessmentProperties

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Filter Topology

/-! ## Provability induction over an assessment process -/

/-- Exploitation under infinitely-often underpricing of a sentence every assessed
world affirms.  Source: `buyDaily_exploits_freq`, with the syntactic hypothesis
`φ ∈ DP.D n` replaced by the semantic consequence the source derives from it. -/
theorem buyDaily_exploits_freq (L : Assessment) (P : History) (φ : Sentence) (ε : ℝ)
    (hε : 0 < ε) (haff : ∀ n (v : PCWorld), L.Live n v → v.payout φ = 1)
    (hP1 : ∀ n, P n φ ≤ 1) (hfreq : ∃ᶠ n in atTop, P n φ ≤ 1 - ε)
    (hlive : ∀ n, ∃ v : PCWorld, L.Live n v) :
    L.Exploits (buyDaily φ) P := by
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rintro x ⟨m, v, hv, rfl⟩
    rw [buyDaily_netWorth]
    refine Finset.sum_nonneg (fun i _ => ?_)
    rw [haff m v hv]
    have := hP1 i
    linarith
  · rintro ⟨B, hB⟩
    obtain ⟨g, hg_mono, hg⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨M, hM⟩ := exists_nat_gt (B / ε)
    obtain ⟨v, hv⟩ := hlive (g M)
    have hsub : (Finset.range (M + 1)).image g ⊆ Finset.range (g M + 1) := by
      intro i hi
      simp only [Finset.mem_image, Finset.mem_range] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      exact Finset.mem_range.mpr
        (by have := hg_mono.monotone (Nat.lt_succ_iff.mp hk); omega)
    have hge : (M + 1 : ℝ) * ε ≤ (buyDaily φ).netWorth P v (g M) := by
      rw [buyDaily_netWorth, haff (g M) v hv]
      calc (M + 1 : ℝ) * ε
          = ∑ _k ∈ Finset.range (M + 1), ε := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ ≤ ∑ k ∈ Finset.range (M + 1), (1 - P (g k) φ) :=
            Finset.sum_le_sum (fun k _ => by have := hg k; linarith)
        _ = ∑ i ∈ (Finset.range (M + 1)).image g, (1 - P i φ) := by
            rw [Finset.sum_image (hg_mono.injective.injOn)]
        _ ≤ ∑ i ∈ Finset.range (g M + 1), (1 - P i φ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun i _ _ => by have := hP1 i; linarith)
    have hmem : (buyDaily φ).netWorth P v (g M) ∈ L.plausibleAssessments (buyDaily φ) P :=
      ⟨g M, v, hv, rfl⟩
    have hBm : B < (M + 1 : ℝ) * ε := by rw [div_lt_iff₀ hε] at hM; nlinarith
    exact absurd (le_trans hge (hB hmem)) (by linarith)

/-- **Provability induction, generalized.**  Under `LIC_L`, the price of a sentence
every assessed world affirms converges to one. -/
theorem lic_affirmed_tendsto_one (L : Assessment) (P : History)
    (hLIC : ∀ Tr : Trader, EfficientlyComputable Tr → ¬ L.Exploits Tr P)
    (hrange : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (φ : Sentence)
    (haff : ∀ n (v : PCWorld), L.Live n v → v.payout φ = 1)
    (hlive : ∀ n, ∃ v : PCWorld, L.Live n v) :
    ConvergesTo (fun n => P n φ) 1 := by
  have hP1 : ∀ n, P n φ ≤ 1 := fun n => (hrange n φ).2
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  have hev : ∀ᶠ n in atTop, 1 - ε < P n φ := by
    by_contra h
    rw [not_eventually] at h
    simp only [not_lt] at h
    exact hLIC (buyDaily φ) (EfficientlyComputable.ofTokenEmitter (buyDaily_ec φ))
      (buyDaily_exploits_freq L P φ ε hε haff hP1 h hlive)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have h1 := hN n hn
  have h2 := hP1 n
  constructor <;> linarith

/-! ## The refutation half of coherence over an assessment process -/

/-- Exploitation under infinitely-often overpricing of a sentence every assessed world
refutes.  Source: `sellDaily_exploits_freq`. -/
theorem sellDaily_exploits_freq (L : Assessment) (P : History) (φ : Sentence) (ε : ℝ)
    (hε : 0 < ε) (href : ∀ n (v : PCWorld), L.Live n v → v.payout φ = 0)
    (hP0 : ∀ n, 0 ≤ P n φ) (hfreq : ∃ᶠ n in atTop, ε ≤ P n φ)
    (hlive : ∀ n, ∃ v : PCWorld, L.Live n v) :
    L.Exploits (sellDaily φ) P := by
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rintro x ⟨m, v, hv, rfl⟩
    rw [sellDaily_netWorth]
    refine Finset.sum_nonneg (fun i _ => ?_)
    rw [href m v hv]
    have := hP0 i
    linarith
  · rintro ⟨B, hB⟩
    obtain ⟨g, hg_mono, hg⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨M, hM⟩ := exists_nat_gt (B / ε)
    obtain ⟨v, hv⟩ := hlive (g M)
    have hsub : (Finset.range (M + 1)).image g ⊆ Finset.range (g M + 1) := by
      intro i hi
      simp only [Finset.mem_image, Finset.mem_range] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      exact Finset.mem_range.mpr
        (by have := hg_mono.monotone (Nat.lt_succ_iff.mp hk); omega)
    have hge : (M + 1 : ℝ) * ε ≤ (sellDaily φ).netWorth P v (g M) := by
      rw [sellDaily_netWorth, href (g M) v hv]
      calc (M + 1 : ℝ) * ε
          = ∑ _k ∈ Finset.range (M + 1), ε := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ ≤ ∑ k ∈ Finset.range (M + 1), (P (g k) φ - 0) :=
            Finset.sum_le_sum (fun k _ => by have := hg k; linarith)
        _ = ∑ i ∈ (Finset.range (M + 1)).image g, (P i φ - 0) := by
            rw [Finset.sum_image (hg_mono.injective.injOn)]
        _ ≤ ∑ i ∈ Finset.range (g M + 1), (P i φ - 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun i _ _ => by have := hP0 i; linarith)
    have hmem : (sellDaily φ).netWorth P v (g M) ∈ L.plausibleAssessments (sellDaily φ) P :=
      ⟨g M, v, hv, rfl⟩
    have hBm : B < (M + 1 : ℝ) * ε := by rw [div_lt_iff₀ hε] at hM; nlinarith
    exact absurd (le_trans hge (hB hmem)) (by linarith)

/-- **The refutation half of coherence, generalized.**  Under `LIC_L`, the price of a
sentence every assessed world refutes converges to zero. -/
theorem lic_refuted_tendsto_zero (L : Assessment) (P : History)
    (hLIC : ∀ Tr : Trader, EfficientlyComputable Tr → ¬ L.Exploits Tr P)
    (hrange : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (φ : Sentence)
    (href : ∀ n (v : PCWorld), L.Live n v → v.payout φ = 0)
    (hlive : ∀ n, ∃ v : PCWorld, L.Live n v) :
    ConvergesTo (fun n => P n φ) 0 := by
  have hP0 : ∀ n, 0 ≤ P n φ := fun n => (hrange n φ).1
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  have hev : ∀ᶠ n in atTop, P n φ < ε := by
    by_contra h
    rw [not_eventually] at h
    simp only [not_lt] at h
    exact hLIC (sellDaily φ) (EfficientlyComputable.ofTokenEmitter (sellDaily_ec φ))
      (sellDaily_exploits_freq L P φ ε hε href hP0 h hlive)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have := hP0 n
  have h1 := hN n hn
  constructor <;> linarith

/-! ## Recovering the source's syntactic hypotheses

At the deductive instance the semantic hypotheses above are exactly what the source's
`φ ∈ DP.D n` delivers, and nothing more of it is used. -/

theorem affirmed_of_mem_stage (DP : DeductiveProcess) (φ : Sentence)
    (hded : ∀ n, φ ∈ DP.D n) (n : ℕ) (v : PCWorld)
    (hv : (ofDeductiveProcess DP).Live n v) : v.payout φ = 1 := by
  rw [PCWorld.payout, if_pos (hv φ (hded n))]

theorem refuted_of_neg_mem_stage (DP : DeductiveProcess) (φ : Sentence)
    (hdis : ∀ n, (∼φ) ∈ DP.D n) (n : ℕ) (v : PCWorld)
    (hv : (ofDeductiveProcess DP).Live n v) : v.payout φ = 0 :=
  PCWorld.payout_of_disprovable v φ (hv (∼φ) (hdis n))

/-- The deductive instance of provability induction, obtained from the generalized
statement rather than from the source's — a check that the generalization really
covers the original. -/
theorem lic_deducible_tendsto_one_via_assessment (DP : DeductiveProcess) (P : History)
    (hLIC : ∀ Tr : Trader, EfficientlyComputable Tr →
      ¬ (ofDeductiveProcess DP).Exploits Tr P)
    (hrange : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (φ : Sentence)
    (hded : ∀ n, φ ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n φ) 1 :=
  lic_affirmed_tendsto_one (ofDeductiveProcess DP) P hLIC hrange φ
    (affirmed_of_mem_stage DP φ hded) hcons

end Workspace.Normativity.Contrib.AssessmentProperties

#print axioms Workspace.Normativity.Contrib.AssessmentProperties.buyDaily_exploits_freq
#print axioms Workspace.Normativity.Contrib.AssessmentProperties.lic_affirmed_tendsto_one
#print axioms Workspace.Normativity.Contrib.AssessmentProperties.sellDaily_exploits_freq
#print axioms Workspace.Normativity.Contrib.AssessmentProperties.lic_refuted_tendsto_zero
#print axioms Workspace.Normativity.Contrib.AssessmentProperties.affirmed_of_mem_stage
#print axioms Workspace.Normativity.Contrib.AssessmentProperties.refuted_of_neg_mem_stage
#print axioms Workspace.Normativity.Contrib.AssessmentProperties.lic_deducible_tendsto_one_via_assessment
