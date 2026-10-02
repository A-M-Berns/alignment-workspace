import Cleanroom.Deference.DefArgmaxValue.Calc
import Cleanroom.Deference.DefSqueezeDiamond.PaperExpert
import Cleanroom.Deference.DefSqueezeDiamond.SelfPins

/-!
# `def-argmax-value` · Pin: the deferred-day pinning engine of the self-expert

`li-diagonal`'s `pinning_engine` pins a *same-day* price by an anti-inductive link. The liar
probe of target 1 (`LiarProbe.lean`) is decided by the market's **deferred-day** price against
the menu's own mesh comparison, so its pin needs the engine at day `f n`. Over the paper
market the two ingredients exist: the self-expert folds every ramp quote
(`def-squeeze-diamond` `selfFoldsAt_rampAbove`, from `def-self-trust`'s generable `est` weight),
and the ramp quotes themselves exist on every e.c. valued source (`paperRampQuote`).

* `selfEstimate_eventually_lt_of_link` — the above face: if, eventually, a day-`f n` price above
  `t + ε` forces the world value to `0`, then eventually the price is below `t + ε + δ`. Proof:
  the ramp product `XW := ⌜X · Ind_δ(E*(X) > t+ε)⌝` is valued `0` in every world (where the ramp
  is positive the link kills `X`; elsewhere the ramp is `0`), so deferred provind gives
  `E*(XW) ≈ₙ 0`; the fold gives `E*(XW) ≈ₙ Ind_δ(E*(X) > t+ε) · E*(X)`; where `E*(X) ≥ t+ε+δ`
  the ramp is `1` and the product is `E*(X) ≥ t+ε+δ > 0` — finitely often.
* `liarPrice_tendsto` — the two-sided pin of a reflected family
  `χ_n ↔ P_{f n}(χ_n) < thr n` with `thr n → s ∈ (0,1)`: the above face on `literalIndicator χ`
  and on `literalIndicator (∼χ)` (with `deferred_neg_coherence`) give `P_{f n}(χ_n) → s`.

Construction-facing; single market (self); every deferral strictly increasing (design
decision 6).
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **The above face of the deferred pinning engine** for the self-expert: an e.c. source `X`
determined at `x n` in every `paperDP T`-world, with the anti-inductive link "eventually,
`t + ε < E*(X_n)` forces `x n = 0`", has `E*(X_n) < t + ε + δ` eventually, for every `δ > 0`.
Composition: `paperRampQuote` (the ramp quote at `t + ε`, width `δ`), `selfFoldsAt_rampAbove`
(the fold), `expect_deferred_asympEq_zero_of_eventually_abs_le` (the product is valued `0`).
Source: mandate target 1b ("`pinning_engine` … margin from the comparison's slack for route
(ii)"); li-diagonal `pinning_engine` (the same-day engine); LI §4.11 (paradox resistance)
Kind: C
Fidelity: exact (asymptotic; at the deferred day)
Hyps: (a); `hf` -/
theorem selfEstimate_eventually_lt_of_link (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    (x : ℕ → ℝ)
    (hx : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) → v.ValuesAt (X n) (x n))
    (t ε : ℚ)
    (hlink : ∀ᶠ n in atTop,
      (t : ℝ) + ε < (X n).expect (liaHistory (paperDP T)) (f n) → x n = 0)
    {δ : ℚ} (hδ : 0 < δ) (hpos : 0 < (t : ℝ) + ε + δ) :
    ∀ᶠ n in atTop, (X n).expect (liaHistory (paperDP T)) (f n) < (t : ℝ) + ε + δ := by
  set P := liaHistory (paperDP T) with hP
  have hXv : Valued (paperDP T) X := fun n v hv => ⟨x n, hx n v hv⟩
  have q : WeightQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) X
      (rampAbove δ (t + ε)) (estW T f hX hδ (t + ε)) (estXW T f hX hδ (t + ε)) :=
    paperRampQuote T f (extendsBase_self T) hf.injective hX hXv hδ (t + ε)
  have hfold := selfFoldsAt_rampAbove T f hf (t + ε) hδ X _ _ hX q
  have hXWv : Valued (paperDP T) (estXW T f hX hδ (t + ε)) := fun n v hv => by
    obtain ⟨z, hz, -⟩ := q.product_reflected n v hv (x n) (hx n v hv)
    exact ⟨z, hz⟩
  set terms : List ((ℕ → EF) × (ℕ → LUV)) :=
    [(fun _ => EF.const 1, estXW T f hX hδ (t + ε))] with hterms
  have hzero : (fun n => (estXW T f hX hδ (t + ε) n).expect P (f n)) ≈ₙ (fun _ => (0 : ℝ)) := by
    have h := expect_deferred_asympEq_zero_of_eventually_abs_le (P := P) (DP := paperDP T) f hf
      (c₀ := fun _ => EF.const 0) (constWeighting 0) (terms := terms)
      (fun p hp => by
        simp only [hterms, List.mem_singleton] at hp; subst hp; exact constWeighting 1)
      (fun p hp => by
        simp only [hterms, List.mem_singleton] at hp; subst hp; exact q.product_codes)
      (fun p hp => by simp only [hterms, List.mem_singleton] at hp; subst hp; exact hXWv)
      (B := 1) (by norm_num) (fun m => by simp [hterms, EF.denote_const])
      (fun ε' hε' => by
        filter_upwards [hlink, (tendsto_order.1 q.slack_tendsto).2 ε' hε'] with n hn hsl v hv ν hν
        have hνXW := hν (fun _ => EF.const 1, estXW T f hX hδ (t + ε)) (by simp [hterms])
        obtain ⟨z, hz, hb⟩ := q.product_reflected n v hv (x n) (hx n v hv)
        have e : ν (estXW T f hX hδ (t + ε) n) = z := hνXW.eq hz
        have hprod : x n * rampAbove δ (t + ε) ((Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate X n) = 0 := by
          by_cases hc : (t : ℝ) + ε < (X n).expect P (f n)
          · rw [hn hc, zero_mul]
          · have h0 : rampAbove δ (t + ε)
                ((Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate X n) = 0 := by
              simp only [rampAbove, Expert.self_estimate]
              push_cast
              exact ctsInd_eq_zero_of_le hδ (not_lt.1 hc)
            rw [h0, mul_zero]
        rw [hprod, _root_.sub_zero] at hb
        simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          EF.denote_const, e]
        push_cast
        have : (0 : ℝ) + (1 * z + 0) = z := by ring
        rw [this]
        exact hb.trans hsl.le) (paperDP_hworld T)
    have hE : deferredExpect P f (fun _ => EF.const 0) terms =
        fun n => (estXW T f hX hδ (t + ε) n).expect P (f n) := by
      funext n
      simp [deferredExpect, hterms, EF.denote_const]
    rwa [hE] at h
  have hprod : (fun n => rampAbove δ (t + ε)
      ((Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate X n) *
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate X n) ≈ₙ
      (fun _ => (0 : ℝ)) := by
    unfold ExpertFoldAt at hfold
    exact hfold.symm.trans hzero
  have hT := tendsto_of_asympEq_const hprod
  filter_upwards [(tendsto_order.1 hT).2 ((t : ℝ) + ε + δ) hpos] with n hn
  by_contra hge
  push Not at hge
  have h1 : rampAbove δ (t + ε)
      ((Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate X n) = 1 := by
    simp only [rampAbove, Expert.self_estimate]
    apply ctsInd_eq_one_of_le_sub _ _ _ hδ
    push_cast
    linarith
  rw [h1, one_mul] at hn
  simp only [Expert.self_estimate] at hn
  linarith

/-- **The two-sided deferred pin of a reflected family**: if `χ_n` holds in every `paperDP T`-world
exactly when `P_{f n}(χ_n) < thr n`, with `thr n → s ∈ (0,1)`, then `P_{f n}(χ_n) → s`. The
above face on `literalIndicator χ` bounds the price above; the above face on
`literalIndicator (∼χ)` with `deferred_neg_coherence` bounds it below.
Source: mandate target 1b ("`P (f n) (χ_n) ≈ₙ s`"); LI §4.11 (`thm:lp` at the deferred day)
Kind: C
Fidelity: exact (asymptotic)
Hyps: (a); `hf` -/
theorem liarPrice_tendsto (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    {χ : ℕ → Sentence} (hχ : MachineSentenceCodes χ) (thr : ℕ → ℝ) (s : ℚ) (hs0 : 0 < s)
    (hs1 : s < 1) (hthr : Tendsto thr atTop (𝓝 (s : ℝ)))
    (hrefl : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      (v.Holds (χ n) ↔ (liaHistory (paperDP T)) (f n) (χ n) < thr n)) :
    Tendsto (fun n => (liaHistory (paperDP T)) (f n) (χ n)) atTop (𝓝 (s : ℝ)) := by
  set P := liaHistory (paperDP T) with hP
  have hs0R : (0 : ℝ) < s := by exact_mod_cast hs0
  have hs1R : (s : ℝ) < 1 := by exact_mod_cast hs1
  set x : ℕ → ℝ := fun n => if P (f n) (χ n) < thr n then 1 else 0 with hxdef
  have hx : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      v.ValuesAt (literalIndicator (χ n)) (x n) := by
    intro n v hv
    have h := literalIndicator_valuesAt (χ n) (paperDP T) hv
    have e : v.payout (χ n) = x n := by
      unfold PCWorld.payout
      simp only [hxdef]
      by_cases hc : P (f n) (χ n) < thr n
      · rw [if_pos ((hrefl n v hv).2 hc), if_pos hc]
      · rw [if_neg (fun hh => hc ((hrefl n v hv).1 hh)), if_neg hc]
    rwa [e] at h
  have hx' : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      v.ValuesAt (literalIndicator (∼ χ n)) (1 - x n) := by
    intro n v hv
    have h := literalIndicator_valuesAt (∼ χ n) (paperDP T) hv
    have e : v.payout (∼ χ n) = 1 - x n := by
      unfold PCWorld.payout
      rw [PCWorld.holds_neg]
      simp only [hxdef]
      by_cases hc : P (f n) (χ n) < thr n
      · rw [if_neg (fun hh => hh ((hrefl n v hv).2 hc)), if_pos hc]; norm_num
      · rw [if_pos (fun hh => hc ((hrefl n v hv).1 hh)), if_neg hc]; norm_num
    rwa [e] at h
  have hcodes : LUV.MachineThresholdCodeSeq (fun n => literalIndicator (χ n)) :=
    literalIndicator_machineThresholdCodeSeq hχ
  have hcodes' : LUV.MachineThresholdCodeSeq (fun n => literalIndicator (∼ χ n)) :=
    literalIndicator_machineThresholdCodeSeq hχ.neg
  have hneg := tendsto_of_asympEq_const
    (deferred_neg_coherence (P := P) (DP := paperDP T) f hf hχ (paperDP_hworld T))
  rw [tendsto_order]
  constructor
  · -- the lower bound, through the negated family
    intro a ha
    obtain ⟨r, har, hrs⟩ := exists_rat_btwn ha
    have hrs' : r < s := by exact_mod_cast hrs
    set ε : ℚ := (s - r) / 6 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    have hεR : (ε : ℝ) = ((s : ℝ) - r) / 6 := by rw [hε]; push_cast; ring
    have hεR0 : (0 : ℝ) < ε := by exact_mod_cast hεpos
    have hneg' : ∀ᶠ n in atTop, |P (f n) (χ n) + P (f n) (∼ χ n) - 1| < ε := by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hneg ε (by exact_mod_cast hεpos)
      exact Filter.eventually_atTop.2 ⟨N, fun n hn => by
        have := hN n hn; rwa [Real.dist_eq] at this⟩
    -- the link at threshold `(1 − s) + 2ε`: a price of `∼χ` above it forces `P(χ) < s − ε < thr`
    have hlink : ∀ᶠ n in atTop,
        ((1 - s : ℚ) : ℝ) + ((2 * ε : ℚ) : ℝ) < (literalIndicator (∼ χ n)).expect P (f n) →
          1 - x n = 0 := by
      have hthr' : ∀ᶠ n in atTop, (s : ℝ) - ε < thr n :=
        (tendsto_order.1 hthr).1 _ (by linarith)
      filter_upwards [hthr', hneg'] with n h1 h2 hgt
      rw [literalIndicator_expect] at hgt
      push_cast at hgt
      rw [abs_lt] at h2
      have hlt : P (f n) (χ n) < thr n := by linarith [h1, h2.2]
      simp only [hxdef, if_pos hlt]
      norm_num
    have hev := selfEstimate_eventually_lt_of_link T f hf hcodes' (fun n => 1 - x n) hx' (1 - s)
      (2 * ε) hlink hεpos (by push_cast; linarith)
    filter_upwards [hev, hneg'] with n h1 h2
    rw [literalIndicator_expect] at h1
    push_cast at h1
    rw [abs_lt] at h2
    have : (r : ℝ) < P (f n) (χ n) := by linarith [h2.1, h1, hεR]
    exact lt_trans har this
  · -- the upper bound
    intro b hb
    obtain ⟨r, hsr, hrb⟩ := exists_rat_btwn hb
    have hsr' : s < r := by exact_mod_cast hsr
    set ε : ℚ := (r - s) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    have hεR : (ε : ℝ) = ((r : ℝ) - s) / 2 := by rw [hε]; push_cast; ring
    have hlink : ∀ᶠ n in atTop,
        (s : ℝ) + ε < (literalIndicator (χ n)).expect P (f n) → x n = 0 := by
      have hthr' : ∀ᶠ n in atTop, thr n < (s : ℝ) + ε :=
        (tendsto_order.1 hthr).2 _ (by linarith)
      filter_upwards [hthr'] with n h1 hgt
      rw [literalIndicator_expect] at hgt
      have hnlt : ¬ P (f n) (χ n) < thr n := by linarith
      simp only [hxdef, if_neg hnlt]
    have hev := selfEstimate_eventually_lt_of_link T f hf hcodes x hx s ε hlink hεpos
      (by linarith)
    filter_upwards [hev] with n h1
    rw [literalIndicator_expect] at h1
    have : (s : ℝ) + ε + ε = r := by rw [hεR]; ring
    rw [this] at h1
    exact lt_trans h1 hrb

end

end Cleanroom.Deference.DefArgmaxValue
