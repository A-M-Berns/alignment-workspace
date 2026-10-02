import Cleanroom.Found.LiQuoteLane.PullBack
import Cleanroom.Deference.DefSelfTrust.Weights

/-!
# `trust-merge` · WeightClass: the averaged clause's weighting class is inhabited (N+ guard)

The averaged clause (`QuoteUnbiased`, `Defs.lean`) and every theorem that delivers it
(`wub_at_quote`, `mirror_feedback_unbiased`, `hop2_avg_of_bigenerable`) quantify over weightings
`W` that are `PGenerableWeighting`, `DivergentWeighting W P` and
`WeightingSupportedOnDeferralImage W P f`. If that class were empty the conclusions would be
vacuous for want of a weighting. It is not: for every history `P` and every strictly increasing
deferral `f`, the indicator of `im f` as a feature — `li-quote-lane`'s
`pullBack f (fun _ => EF.const 1)` — is generable (`pullBack_pgenerable` on the constant),
divergent (its prefix mass through day `f K` is at least `K + 1`) and supported on `im f`
(`pullBack_supported`). Recorded as an N+ row of the package at the round-1 adversarial auditor's
suggestion (N7; its probe `WeightClassInhabited.lean`, ported). No such guard existed in round 0.
-/

namespace Cleanroom.Trust.TrustMerge

open LogicalInduction Filter Topology Finset
open Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefSelfTrust

noncomputable section

/-- The pulled-back constant-1 weighting denotes `1` on `im f`.
Source: none: infrastructure (`li-quote-lane` `pullBack_apply`)
Kind: L
Fidelity: n/a -/
theorem pullBackOne_denote (P : History) (f : DeferralFunction) (hinj : Function.Injective f.f)
    (n : ℕ) : (pullBack f (fun _ => EF.const 1) (f.f n)).denote P = 1 := by
  rw [pullBack_apply f hinj]
  simp

/-- It lies in `[0,1]` everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pullBackOne_denote_mem (P : History) (f : DeferralFunction) (m : ℕ) :
    0 ≤ (pullBack f (fun _ => EF.const 1) m).denote P ∧
      (pullBack f (fun _ => EF.const 1) m).denote P ≤ 1 := by
  unfold pullBack
  split_ifs <;> simp

/-- The pulled-back constant-1 feature denotes the same real on any two histories (it reads no
price), so it is the same weight on every market.
Source: none: infrastructure (audit r2 adversarial N10, probe `BiGenerableInhabited.lean`)
Kind: L
Fidelity: n/a -/
theorem pullBackOne_denote_hist_indep (P Q : History) (f : DeferralFunction) (m : ℕ) :
    (pullBack f (fun _ => EF.const 1) m).denote P =
      (pullBack f (fun _ => EF.const 1) m).denote Q := by
  unfold pullBack
  split_ifs <;> simp

/-- The prefix mass of the image indicator through any day `n ≥ f K` is at least `K + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pullBackOne_prefixSum_ge (P : History) (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) (K n : ℕ) (hn : f.f K ≤ n) :
    (K : ℝ) + 1 ≤ prefixSum (fun i => (pullBack f (fun _ => EF.const 1) i).denote P) n := by
  have hinj : Function.Injective f.f := hf.injective
  set w : ℕ → ℝ := fun i => (pullBack f (fun _ => EF.const 1) i).denote P with hw
  have hsub : (range (K + 1)).image f.f ⊆ range (n + 1) := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hm
    rw [mem_range] at hk ⊢
    have : f.f k ≤ f.f K := hf.monotone (Nat.lt_succ_iff.1 hk)
    omega
  have hnn : ∀ i ∈ range (n + 1), i ∉ (range (K + 1)).image f.f → 0 ≤ w i :=
    fun i _ _ => (pullBackOne_denote_mem P f i).1
  calc (K : ℝ) + 1 = ∑ k ∈ range (K + 1), w (f.f k) := by
        simp only [hw, pullBackOne_denote P f hinj, sum_const, card_range, nsmul_eq_mul, mul_one]
        push_cast
        ring
    _ = ∑ m ∈ (range (K + 1)).image f.f, w m :=
        (sum_image (fun x _ y _ h => hinj h)).symm
    _ ≤ ∑ i ∈ range (n + 1), w i := sum_le_sum_of_subset_of_nonneg hsub hnn
    _ = prefixSum w n := rfl

/-- The image indicator is a divergent `[0,1]` weighting on every history.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pullBackOne_divergent (P : History) (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) :
    DivergentWeighting (pullBack f (fun _ => EF.const 1)) P := by
  refine ⟨fun n => pullBackOne_denote_mem P f n, ?_⟩
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨f.f ⌈b⌉₊, fun n hn => ?_⟩
  have h := pullBackOne_prefixSum_ge P f hf ⌈b⌉₊ n hn
  have : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
  linarith

/-- **The weighting class of the averaged clause is inhabited (N+ guard):** for every history and
every strictly increasing deferral there is a weighting that is `PGenerableWeighting`, divergent
on `P` and supported on `im f` — the indicator of `im f`. So the universal quantifier of
`QuoteUnbiased` (hence of `mirror_feedback_unbiased`, `wub_at_quote`,
`hop2_avg_of_bigenerable`) ranges over a nonempty class, and the witness is the same feature on
every market (so it is bi-generable in the sense of `BiGenerable`, denoting `1` on `im f` and
`0` off it on any history).
Source: mandate T1 ("require `DivergentWeighting`"); audit r1 adversarial N7 (the probe
`WeightClassInhabited.lean`); `li-quote-lane` `pullBack`
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem weightClass_inhabited (P : History) (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) :
    ∃ W : ℕ → EF, PGenerableWeighting W ∧ DivergentWeighting W P ∧
      WeightingSupportedOnDeferralImage W P f :=
  ⟨pullBack f (fun _ => EF.const 1), pullBack_pgenerable f hf (constWeighting 1),
    pullBackOne_divergent P f hf, pullBack_supported f _ P⟩

end

end Cleanroom.Trust.TrustMerge
