import Cleanroom.Fa.FaForcingTrader.Schedule
import LogicalInduction.Construction.Statistics.FeedbackEmission

/-!
# `fa-forcing-trader` · angle A · Bridge: the `H`-side Kelly round trip at grade (a) (T4)

**The microscope** (trust-lab-066). Every kernel-checked deference theorem of `lean-deference/`
and the trust lab took the `H`-side logical-induction content as named real-sequence hypotheses:
`hbdd` (bounded trader profit), `hbias` (a full-limit weighted calibration), `StreamlinedSS`'s
`hNoExp`/`hMirror` (bounded log-wealth of a Kelly trader and of its mirror). Here none is assumed.
The `H`-side bridge is FAF's criterion applied to FAF's own trader:
`AffineCombination.lic_not_frequently_positive_feedback_return` — the Kelly-sized round trips
"buy `As (g i)` at `g i`, sell at `g (i+1)`" along a strictly increasing deferral `g`, for any
generable divergent weighting, cannot realize a positive fraction of the mass infinitely often —
with `As := bundle X` (the day-`n` threshold mesh of `X n`), `g := interleave f d` (even rungs the
scheduled days `d k`, odd rungs the lookahead days `f (d k)`, where the weighting is `0`), and the
mirror from `PolySequence.neg`. The syntax boundary (`FeedbackTraderEmission`) is discharged by
FAF's own inhabitant `feedbackTraderEmission`. The result is a **full limit**, two-sided, of the
weighted average of the realized round-trip cash `price_{f n}(bundle_n) − price_n(bundle_n)`.

What replaced what (the ledger's "Microscope" row): `hbdd` → `feedbackTrader_plausible_bddBelow`
(inside FAF's theorem); `hNoExp`/`hMirror` → `IsLogicalInductor.noExploit` on `feedbackTrader` and
on its negation; `hbias` → not needed on this side (the `A`-side input is fa-theorem-a's
`quote_unbiased`); the `≈ₙ`-slack of `expprovind` → not needed (no settlement is consulted: the
sale is at `H`'s own later price, which is what `A`'s quote names).

No `(c)`: the hypotheses are the criterion instance, the e.c. certificate of `X`, the world
boundary, and the weighting's generability, support and divergence — all FAF's own premises.
-/

namespace Cleanroom.Fa.FaForcingTrader.A

open LogicalInduction LogicalInduction.AffineCombination LogicalInduction.FeedbackEmission
  Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.DefLattice Cleanroom.Fa.FaForcingTrader Filter Topology

/-- **The forcing trader is FAF's feedback trader** on the interleaved schedule with the
day-`n` threshold meshes as its instruments — an abbreviation so that the docstrings can name it;
nothing is redefined.
Source: [[fa-positive-results-corrected-v3]] §3 ("the human-side trader `T`"); vq-wiki-049 (trader variant); FAF `feedbackTrader`
Kind: D
Fidelity: exact (FAF's D.4 Kelly round trip; constants `δ ≤ 1/2`, `γ > 2δ` are FAF's, K6)
Hyps: n/a -/
noncomputable abbrev forcingTrader {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    {G : ℕ → EF} (hG : PGenerableWeighting G) {f d : DeferralFunction} (hwd : WindowDisjoint f d)
    (δ : ℚ) : Trader :=
  feedbackTrader (bundle_polySequence hX) hG (interleave_strictMono hwd) δ

/-- The weighting read along the rungs of `g`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def wSeq (G : ℕ → EF) (H : History) (g : DeferralFunction) (i : ℕ) : ℝ :=
  (G (g.f i)).denote H

/-- The realized return of the round trip opened at rung `i`: sell price at `g (i+1)` minus buy
price at `g i`, of the instrument `As (g i)`.
Source: [[fa-positive-results-corrected-v3]] §3 (the budget factor's increment)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def retSeq (As : ℕ → AffineCombination) (H : History) (g : DeferralFunction)
    (i : ℕ) : ℝ :=
  (As (g.f i)).price H (g.f (i + 1)) - (As (g.f i)).price H (g.f i)

/-- **One sign of the criterion endpoint, in the form used below**: for every `γ > 0`, eventually
the realized cash of the first `k` round trips is below `γ` times their mass. This is FAF's
`lic_not_frequently_positive_feedback_return` with the Kelly fraction chosen as a rational
`δ < min (1/2) (γ/2)`, and the emission certificate FAF's `feedbackTraderEmission`.
Source: FAF `lic_not_frequently_positive_feedback_return` (`thm:wubaff`'s engine); lean-deference-036 (`hNoExp` discharged)
Kind: C
Fidelity: exact
Hyps: (a) none beyond FAF's premises (criterion instance, `hpoly`, `hmag`, `hG`, `hdiv`, `hmass`, `hworld`) -/
theorem feedback_upper {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    {As : ℕ → AffineCombination} (hpoly : AffineCombination.PolySequence As)
    (hmag : ∀ i, (As i).magnitude H ≤ 1) {G : ℕ → EF} (hG : PGenerableWeighting G)
    {g : DeferralFunction} (hstrict : StrictlyIncreasingDeferral g)
    (hdiv : DivergentWeighting G H)
    (hmass : Tendsto (feedbackPrefixSum (wSeq G H g)) atTop atTop)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ k in atTop, feedbackPrefixSum (fun i => wSeq G H g i * retSeq As H g i) k <
      γ * feedbackPrefixSum (wSeq G H g) k := by
  obtain ⟨δ, hδ0, hδlt⟩ := exists_rat_btwn (lt_min (by norm_num : (0 : ℝ) < 1 / 2) (half_pos hγ))
  have hδ : (δ : ℝ) ≤ 1 / 2 := hδlt.le.trans (min_le_left _ _)
  have hgap : 2 * (δ : ℝ) < γ := by
    have := lt_of_lt_of_le hδlt (min_le_right _ _)
    linarith
  have h := lic_not_frequently_positive_feedback_return hpoly hG hstrict δ γ
    (feedbackTraderEmission hpoly hG hstrict δ) hdiv hmag hδ0 hδ hgap hmass hworld
  rw [Filter.not_frequently] at h
  exact h.mono (fun k hk => not_le.1 hk)

/-- **Both signs**: the mirror trader (FAF's `PolySequence.neg`, magnitude preserved by
`neg_magnitude`, prices negated by `neg_price`) gives the lower bound, so for every `γ > 0`
eventually `|cash_k| < γ · mass_k`.
Source: FAF `lic_not_frequently_positive_feedback_return` at `hpoly.neg`; lean-deference-036 (`hMirror` discharged)
Kind: C
Fidelity: exact
Hyps: (a) none beyond FAF's premises -/
theorem feedback_abs_lt {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    {As : ℕ → AffineCombination} (hpoly : AffineCombination.PolySequence As)
    (hmag : ∀ i, (As i).magnitude H ≤ 1) {G : ℕ → EF} (hG : PGenerableWeighting G)
    {g : DeferralFunction} (hstrict : StrictlyIncreasingDeferral g)
    (hdiv : DivergentWeighting G H)
    (hmass : Tendsto (feedbackPrefixSum (wSeq G H g)) atTop atTop)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ k in atTop, |feedbackPrefixSum (fun i => wSeq G H g i * retSeq As H g i) k| <
      γ * feedbackPrefixSum (wSeq G H g) k := by
  have h1 := feedback_upper hpoly hmag hG hstrict hdiv hmass hworld hγ
  have hmagneg : ∀ i, ((As i).neg).magnitude H ≤ 1 := fun i => by
    rw [AffineCombination.neg_magnitude]
    exact hmag i
  have h2 := feedback_upper hpoly.neg hmagneg hG hstrict hdiv hmass hworld hγ
  have hneg : ∀ k, feedbackPrefixSum (fun i => wSeq G H g i * retSeq (fun n => (As n).neg) H g i) k
      = -feedbackPrefixSum (fun i => wSeq G H g i * retSeq As H g i) k := by
    intro k
    simp only [feedbackPrefixSum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [retSeq, AffineCombination.neg_price]
    ring
  filter_upwards [h1, h2] with k hk1 hk2
  rw [hneg] at hk2
  rw [abs_lt]
  exact ⟨by linarith, hk1⟩

/-- From `|cash_k| < γ · mass_k` for every `γ > 0` and divergent mass: the feedback-clock weighted
average of the returns tends to `0`.
Source: none: infrastructure (the `limsup ≤ 0 ∧ liminf ≥ 0 ⇒ limit` step of mandate T4)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem feedbackWeightedAverage_tendsto_zero_of_abs {w r : ℕ → ℝ}
    (hmass : Tendsto (feedbackPrefixSum w) atTop atTop)
    (h : ∀ γ : ℝ, 0 < γ → ∀ᶠ k in atTop,
      |feedbackPrefixSum (fun i => w i * r i) k| < γ * feedbackPrefixSum w k) :
    Tendsto (feedbackWeightedAverage w r) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h ε hε, hmass.eventually (eventually_gt_atTop 0)] with k hk hpos
  rw [feedbackWeightedAverage, if_neg hpos.ne', Real.dist_eq, sub_zero, abs_div,
    abs_of_pos hpos, div_lt_iff₀ hpos]
  exact hk

/-- **T4 (headline). The `H`-side bridge: the criterion forces the Kelly round trip's realized
cash to average to zero.** For `[IsLogicalInductor H DPH]`, an e.c. family `X` of `H`'s LUVs, a
window-disjoint schedule `d` for the lookahead `f`, and any `PGenerableWeighting G` of `H`'s
market supported on `im d` and divergent in `H`'s prices: the `G`-weighted average of
`price^H_{f n}((X n).expectAffine (n+1)) − 𝔼^H_n(X_n)` — what the trader banks per scheduled day,
buying the day-`n` threshold mesh at `n` and selling it at `f n` — tends to `0` (two-sided full
limit, `WeightedApprox`).
Scope: one-way (`H`'s own market only; nothing about `A`). e.d. family `X`. Schedule:
window-disjoint `DeferralFunction`. Grade: full limit.
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
Proof: `g := interleave f d`; FAF's `lic_not_frequently_positive_feedback_return` on
`As := bundle X`, `W := G` (zero on the odd rungs, which are never scheduled days), for every
rational Kelly fraction and its mirror, gives `|cash_k| < γ · mass_k` eventually for every
`γ > 0`; the mass along `g`'s rungs diverges (`feedbackPrefixSum_tendsto_atTop`); on even rungs
the sale day `g (i+1)` is `f (g i)` and on odd rungs the weight is `0`, so the rung-indexed sums
are the day-indexed ones; FAF's `weightedAverage_supported_asympEq_zero_of_feedback` transfers
the feedback clock to all days.
Source: vq-wiki-049 (trader variant); vq-wiki-057 Theorem 5.2 (one-position case); lean-deference-036 (`kelly_round_trip` with `hNoExp`/`hMirror` discharged); trust-lab-066; [[theorem-ss-streamlined]] §3 Remark; [[fa-positive-results-corrected-v3]] §3 "The human-side trader"
Kind: C
Fidelity: variant: the trader sells the day-`n` mesh at its day-`f n` *price* (the opening grid), not at `𝔼^H_{f n}(X_n)` as v3 §3 writes (F-A9); the trader is FAF's D.4 round trip on that mesh, and the gap is the mesh term T5, washed out of every divergent average
Hyps: (a) all: `hcode` (e.c. certificate of `X`), `hworldH` (FAF's world boundary), `hG`, `hsupp`, `hdiv`; no (b), no (c). -/
theorem hSideBridge {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    {X : ℕ → LUV} (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    {f d : DeferralFunction} (hwd : WindowDisjoint f d)
    {G : ℕ → EF} (hG : PGenerableWeighting G)
    (hsupp : ∀ n, (G n).denote H ≠ 0 → ∃ k, d.f k = n)
    (hdiv : DivergentWeighting G H) :
    WeightedApprox (fun n => (G n).denote H) (fun n => (bundle X n).price H (f.f n))
      (fun n => (X n).expect H n) := by
  have hstrict : StrictlyIncreasingDeferral (interleave f d hwd) := interleave_strictMono hwd
  have hpoly : AffineCombination.PolySequence (bundle X) := bundle_polySequence hcode
  have hmag : ∀ i, (bundle X i).magnitude H ≤ 1 := bundle_magnitude_le_one X H
  have hsupportg : WeightingSupportedOnDeferralImage G H (interleave f d hwd) :=
    fun n hn => interleave_supported hwd hsupp n hn
  have hmass : Tendsto (feedbackPrefixSum (wSeq G H (interleave f d hwd))) atTop atTop :=
    feedbackPrefixSum_tendsto_atTop hstrict hdiv hsupportg
  have habs := fun (γ : ℝ) (hγ : 0 < γ) =>
    feedback_abs_lt hpoly hmag hG hstrict hdiv hmass hworldH hγ
  have hfa := feedbackWeightedAverage_tendsto_zero_of_abs hmass habs
  -- the rung-indexed returns are the day-indexed cash on the support
  have hident : ∀ k, feedbackWeightedAverage (wSeq G H (interleave f d hwd))
      (retSeq (bundle X) H (interleave f d hwd)) k =
      feedbackWeightedAverage (fun i => (G ((interleave f d hwd).f i)).denote H)
        (fun i => (bundle X ((interleave f d hwd).f i)).price H (f.f ((interleave f d hwd).f i)) -
          (X ((interleave f d hwd).f i)).expect H ((interleave f d hwd).f i)) k := by
    intro k
    unfold feedbackWeightedAverage wSeq
    have hnum : feedbackPrefixSum (fun i => (G ((interleave f d hwd).f i)).denote H *
        retSeq (bundle X) H (interleave f d hwd) i) k =
        feedbackPrefixSum (fun i => (G ((interleave f d hwd).f i)).denote H *
          ((bundle X ((interleave f d hwd).f i)).price H (f.f ((interleave f d hwd).f i)) -
            (X ((interleave f d hwd).f i)).expect H ((interleave f d hwd).f i))) k := by
      simp only [feedbackPrefixSum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rcases Nat.mod_two_eq_zero_or_one i with hi | hi
      · simp only [retSeq, interleave_succ_of_even hwd hi, bundle_price_self]
      · have hw0 : (G ((interleave f d hwd).f i)).denote H = 0 := by
          by_contra hne
          obtain ⟨k', hk'⟩ := hsupp _ hne
          exact interleave_not_mem_of_odd hwd hi k' hk'
        simp only [hw0, zero_mul]
    rw [hnum]
  have hsparse : feedbackWeightedAverage (fun i => (G ((interleave f d hwd).f i)).denote H)
      (fun i => (bundle X ((interleave f d hwd).f i)).price H (f.f ((interleave f d hwd).f i)) -
        (X ((interleave f d hwd).f i)).expect H ((interleave f d hwd).f i)) ≈ₙ (fun _ => 0) := by
    show Tendsto (fun k => _ - (0 : ℝ)) atTop (𝓝 0)
    simp only [sub_zero]
    exact hfa.congr hident
  have hres := weightedAverage_supported_asympEq_zero_of_feedback
    (w := fun n => (G n).denote H)
    (x := fun n => (bundle X n).price H (f.f n) - (X n).expect H n) hstrict
    (fun n hn => hsupportg n hn) hsparse
  show Tendsto (weightedAverage (fun n => (G n).denote H)
    (fun i => (bundle X i).price H (f.f i) - (X i).expect H i)) atTop (𝓝 0)
  have hres' : Tendsto (fun n => weightedAverage (fun n => (G n).denote H)
      (fun i => (bundle X i).price H (f.f i) - (X i).expect H i) n - 0) atTop (𝓝 0) := hres
  simpa only [sub_zero] using hres'

end Cleanroom.Fa.FaForcingTrader.A
