import Cleanroom.Fa.FaForcingTrader.A.Witnesses
import Cleanroom.Fa.FaForcingTrader.TheoremSS

/-!
# `fa-forcing-trader` · Witnesses: full-package inhabitants of T6/T7 (repair round 1)

Main module added in repair round 1 (audit r1 fidelity B2 / adversarial B1). Angle A's
same-market instances `A.theoremSS_paper_self` / `A.schedThresholdAbove_paper_self` take the
gate's divergence `hdiv` as a hypothesis and so do not inhabit the *full* hypothesis package of
`theoremSS_limitPoint` / `schedThresholdAbove_of_theoremSS` ([[STANDARDS]] §3). This module
discharges `hdiv` two ways and ships the resulting inhabitants:

* **§A, the sub-zero threshold** (both auditors' probes): for `t ≤ −δ` the ramp is saturated
  at `1` on every inductor (quotes lie in `[0,1]`), the scheduled gate *is* the schedule
  indicator, and `hdiv` is a theorem (`schedGate_divergent_of_le_neg`). The instances
  `theoremSS_paper_self_negOne` / `schedThresholdAbove_paper_self_negOne` inhabit the full
  package with no hypothesis — but at a threshold where T7 says nothing (`h ≥ 0`), so they are
  **N−** for content on that count too.
* **§B, a content threshold** (adversarial B1 (ii)): with `X ≡ 𝟙(⊤)` the realized value
  `𝔼^H_{n+1}(𝟙(⊤)) = P_{n+1}(⊤ ⋏ ∼∼⊤)` tends to `1` (FAF's `lic_provind_true`: every world holds
  the threshold sentence, so no deducibility premise is needed), `quote_unbiased` on the bare
  schedule indicator makes the scheduled average of the quote `a_n = 𝔼^H_n(⌜𝔼^H_{n+1}(𝟙(⊤))⌝)`
  have limit point `1`, and the ramp bound `Ind_δ(a > t) ≥ 1 − (1 − a)/(1 − t − δ)` turns that
  into divergent gate mass at every `t + δ < 1` (`schedGate_divergent_of_realized_tendsto_one`,
  general in the quoting market). `theoremSS_paper_self_top` /
  `schedThresholdAbove_paper_self_top` inhabit the full package at, e.g., `t = 1/2`, `δ = 1/4`.
  Still same-market (`A = H`, the conclusion also follows from `cee`) and the human's credence
  `𝔼^H_n(𝟙(⊤)) → 1` makes T7's conclusion immediate there: **N+ for the package at a content
  threshold, N− for content**, as the ledger says.

* **§C, the mirror**: with `X ≡ 𝟙(⊥)` the realized value tends to `0` (`lic_provind_false`),
  and the lower gate `1[n ∈ im d]·Ind_δ(a_n < t)` has divergent mass at every `t > δ`
  (`schedGateBelow_divergent_of_realized_tendsto_zero`); `theoremSS_paper_self_bot` /
  `schedThresholdBelow_paper_self_bot` inhabit the full package of the `_below` rows.

* **§D, what the instances test** (repair round 2, audit r2 adversarial N3): `h → 1` alone
  gives T7's conclusion on any divergent nonnegative weight (`schedThresholdAbove_of_tendsto_one`)
  but not T6's (`not_hasLimitPoint_bias_const`) — the two reasons behind "N− content".
* **§E, the T4 witness's return** (repair round 2, audit r2 adversarial N6): on a constant
  indicator family the round-trip return is `P_{n+1}(φ ⋏ ∼∼φ) − P_n(φ ⋏ ∼∼φ) → 0` with no
  trader (`bundle_indicator_return_tendsto_zero`, `hSideBridge_w2_return_tendsto_zero`), so
  `A.hSideBridge_w2` is N− for content in the strongest sense.

What is *not* shown: an inhabitant whose quote is of an undecided family (`cleanX`) at a content
threshold — that would evaluate the LIA's prices; and a two-market inhabitant (T11, OPEN).
-/

namespace Cleanroom.Fa.FaForcingTrader

open LogicalInduction LO.Propositional Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Filter Topology

/-! ## A. The sub-zero threshold: the scheduled gate is the schedule indicator -/

/-- At any threshold `t ≤ −δ` the upper ramp is saturated on an inductor's quotes (they lie in
`[0,1]`), so the scheduled gate denotes the bare schedule indicator.
Source: audit r1 fidelity B2 (probe `HdivNegThreshold.lean`), adversarial B1 (probe P2)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGate_denote_of_le_neg {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (Y : ℕ → LUV) (d : DeferralFunction) {t δ : ℚ} (hδ : 0 < δ)
    (ht : t ≤ -δ) (n : ℕ) : (schedGate Y d t δ n).denote P = schedInd d n := by
  rw [schedGate_denote Y d t hδ P n, rampAbove]
  have ha : (Y n).expect P n ∈ Set.Icc (0 : ℝ) 1 :=
    LUV.expect_mem_Icc P n (Y n)
      (fun s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s)
  have h1 : ctsInd δ (quoteSeq Y P n) (t : ℝ) = 1 := by
    rw [ctsInd_eq_one_iff hδ]
    have ht' : (t : ℝ) ≤ -δ := by exact_mod_cast ht
    have h0 := ha.1
    simp only [quoteSeq]
    linarith
  rw [h1, mul_one]

/-- **`hdiv` is a theorem at every threshold `t ≤ −δ`**, in every inductor's market, for every
quote family: the gate is the schedule indicator, which is divergent.
Source: audit r1 fidelity B2, adversarial B1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGate_divergent_of_le_neg {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (Y : ℕ → LUV) (d : DeferralFunction) {t δ : ℚ} (hδ : 0 < δ)
    (ht : t ≤ -δ) : DivergentWeighting (schedGate Y d t δ) P := by
  refine ⟨fun n => schedGate_mem_Icc Y d t hδ P n, ?_⟩
  have h := (scheduleIndicator_divergent d P).2
  simp only [scheduleIndicator_denote] at h
  have hfun : (fun n => (schedGate Y d t δ n).denote P) = fun n => schedInd d n :=
    funext (schedGate_denote_of_le_neg (DP := DP) Y d hδ ht)
  rw [hfun]
  exact h

/-- **T6 at the same-market instance, full package, sub-zero threshold** (`t = −1`, `δ = 1`): no
hypothesis beyond the schedule. The gate is the whole schedule, so the content is the scheduled
average of `𝔼^H_n(⌜𝔼^H_{n+1}(cleanX_n)⌝) − 𝔼^H_n(cleanX_n)` having limit point `0` — N− for
content (`A = H`; and the threshold carries no selection).
Source: mandate T6 witness; audit r1 fidelity B2
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem theoremSS_paper_self_negOne {d : DeferralFunction} (hwd : WindowDisjoint succDeferral d) :
    HasLimitPoint (weightedBias (fun n => (schedGate A.selfY d (-1) 1 n).denote A.selfH)
      (quoteSeq A.selfY A.selfH) (fun n => (cleanX n).expect A.selfH n)) 0 :=
  haveI := w1_inductorH
  A.theoremSS_paper_self (δ := 1) hwd (-1) (by norm_num)
    (schedGate_divergent_of_le_neg (DP := paperDP 𝗜𝚺₁) (t := -1) (δ := 1) A.selfY d
      (by norm_num) (by norm_num))

/-- **T7 at the same-market instance, full package, sub-zero threshold.** Inhabited with no
hypothesis, but at `t = −1` the conclusion (`∀ ρ > 0`, frequently the average of a `[0,1]`
sequence is `≥ −1 − ρ`) is trivially true: N− for content (adversarial r1 probe P3).
Source: mandate T7 witness; audit r1 adversarial B1
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem schedThresholdAbove_paper_self_negOne {d : DeferralFunction}
    (hwd : WindowDisjoint succDeferral d) :
    SchedThresholdAbove (fun n => (schedGate A.selfY d (-1) 1 n).denote A.selfH)
      (fun n => (cleanX n).expect A.selfH n) ((-1 : ℚ) : ℝ) :=
  haveI := w1_inductorH
  A.schedThresholdAbove_paper_self (δ := 1) hwd (-1) (by norm_num)
    (schedGate_divergent_of_le_neg (DP := paperDP 𝗜𝚺₁) (t := -1) (δ := 1) A.selfY d
      (by norm_num) (by norm_num))

/-! ## B. A content threshold: `hdiv` from a realized value tending to `1` -/

/-- The upper ramp is bounded below by an affine function of its argument once the threshold
leaves room: for `t + δ < 1` and `x ≤ 1`, `Ind_δ(x > t) ≥ 1 − (1 − x)/(1 − t − δ)` (saturated
at `1` when `x ≥ t + δ`; the bound is negative otherwise).
Source: none: infrastructure (repair round 1)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem ctsInd_ge_affine {δ : ℚ} (hδ : 0 < δ) {t x : ℝ} (hx1 : x ≤ 1)
    (hc : 0 < 1 - t - δ) : 1 - (1 - x) / (1 - t - δ) ≤ ctsInd δ x t := by
  by_cases h : (δ : ℝ) ≤ x - t
  · rw [(ctsInd_eq_one_iff hδ x t).2 h]
    have : 0 ≤ (1 - x) / (1 - t - δ) := div_nonneg (by linarith) hc.le
    linarith
  · have h' : x - t < δ := not_le.1 h
    have h2 : 1 < (1 - x) / (1 - t - δ) := by
      rw [lt_div_iff₀ hc]
      linarith
    have := ctsInd_nonneg δ x t
    linarith

/-- Prefix sums of a nonnegative sequence are monotone.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem prefixSum_mono_of_nonneg {g : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i) : Monotone (prefixSum g) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  rw [prefixSum_succ]
  linarith [hg (n + 1)]

/-- A nonnegative sequence whose prefix sums are frequently at least half those of a divergent
sequence has divergent prefix sums (monotonicity carries the frequent bound forward).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem tendsto_prefixSum_atTop_of_frequently_half {g s : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i)
    (hs : Tendsto (prefixSum s) atTop atTop)
    (hfreq : ∃ᶠ n in atTop, prefixSum s n / 2 ≤ prefixSum g n) :
    Tendsto (prefixSum g) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  have hev : ∀ᶠ n in atTop, 2 * M ≤ prefixSum s n := Filter.tendsto_atTop.1 hs (2 * M)
  obtain ⟨n₀, hn₀⟩ := (hfreq.and_eventually hev).exists
  refine ⟨n₀, fun n hn => ?_⟩
  have hmono := prefixSum_mono_of_nonneg hg hn
  linarith [hn₀.1, hn₀.2]

/-- Summing the ramp bound: if `g ≥ w · (1 − (1 − a)/c)` pointwise then
`∑ g ≥ ∑ w − (1/c) ∑ w (1 − a)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem prefixSum_ge_of_affine {w a g : ℕ → ℝ} {c : ℝ}
    (hg : ∀ i, w i * (1 - (1 - a i) / c) ≤ g i) (n : ℕ) :
    prefixSum w n - (1 / c) * prefixSum (fun i => w i * (1 - a i)) n ≤ prefixSum g n := by
  have h : ∀ i, w i - (1 / c) * (w i * (1 - a i)) ≤ g i := fun i => by
    have e : w i * (1 - (1 - a i) / c) = w i - (1 / c) * (w i * (1 - a i)) := by ring
    rw [← e]
    exact hg i
  unfold prefixSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum (fun i _ => h i)

/-- **`hdiv` at a content threshold from the realized value tending to `1`.** For an inductor
`P` quoting `H`'s deferred expectation through a `CrossQuotePackage`, if the realized value
`𝔼^H_{f n}(X_n)` tends to `1`, then the scheduled upper quote gate `1[n ∈ im d]·Ind_δ(a_n > t)`
has divergent mass in `P`'s market at every `t + δ < 1`. Proof: `quote_unbiased` on the bare
schedule indicator gives the scheduled average of `a_n − 𝔼^H_{f n}(X_n)` limit point `0`; the
donor rule moves the realized value to `1`; so frequently the scheduled average of `1 − a_n` is
below `(1 − t − δ)/2`, and the ramp bound `ctsInd_ge_affine` then puts the gate's mass above half
the schedule's, which diverges; monotonicity finishes.
Scope: one-way (only `P`'s criterion is used). General in the quoting market.
Source: audit r1 adversarial B1 (ii); FAF `thm:recurringunbiasednessexp` via fa-theorem-a's `quote_unbiased`
Kind: C
Fidelity: n/a (a derivation of T6/T7's `hdiv`)
Hyps: (a) `hworld`, `hδ`, `ht`, `hv`; (c) `pkg.reflected` (through `quote_unbiased`). -/
theorem schedGate_divergent_of_realized_tendsto_one {H P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DP f X Y)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (d : DeferralFunction) {t δ : ℚ} (hδ : 0 < δ) (ht : (t : ℝ) + δ < 1)
    (hv : Tendsto (realized H f X) atTop (𝓝 1)) :
    DivergentWeighting (schedGate Y d t δ) P := by
  have hc : (0 : ℝ) < 1 - t - δ := by linarith
  have hw : ∀ i, 0 ≤ schedInd d i := fun i => (schedInd_mem_Icc d i).1
  have hwdiv : Tendsto (prefixSum (schedInd d)) atTop atTop := by
    have h := (scheduleIndicator_divergent d P).2
    simpa only [scheduleIndicator_denote] using h
  have ha : ∀ i, quoteSeq Y P i ∈ Set.Icc (0 : ℝ) 1 := fun i =>
    LUV.expect_mem_Icc P i (Y i)
      (fun s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) i s)
  -- the quote's scheduled average has limit point `1`
  have hlp : HasLimitPoint (weightedBias (schedInd d) (quoteSeq Y P) (realized H f X)) 0 := by
    have h := quote_unbiased pkg hworld (scheduleIndicator_pgenerable d)
      (scheduleIndicator_divergent d P)
    have hfun : (fun i => (scheduleIndicator d i).denote P) = schedInd d :=
      funext (scheduleIndicator_denote d P)
    rw [hfun] at h
    exact h
  have hv1 : Tendsto (weightedAverage (schedInd d) (fun i => realized H f X i - 1)) atTop
      (𝓝 0) :=
    weightedAverage_tendsto_zero hw hwdiv (by simpa using hv.sub_const 1)
  have hlp1 : HasLimitPoint (weightedAverage (schedInd d) (fun i => quoteSeq Y P i - 1)) 0 :=
    A.hasLimitPoint_zero_of_add_tendsto hlp hv1 (fun n => by
      show weightedAverage (schedInd d) (fun i => quoteSeq Y P i - 1) n =
        weightedAverage (schedInd d) (fun i => quoteSeq Y P i - realized H f X i) n +
          weightedAverage (schedInd d) (fun i => realized H f X i - 1) n
      exact A.weightedAverage_split (schedInd d) (quoteSeq Y P) (realized H f X) (fun _ => 1) n)
  -- the gate's mass dominates half the schedule's, frequently
  refine ⟨fun n => schedGate_mem_Icc Y d t hδ P n, ?_⟩
  have hg0 : ∀ i, 0 ≤ (schedGate Y d t δ i).denote P :=
    fun i => (schedGate_mem_Icc Y d t hδ P i).1
  have hgw : ∀ i, schedInd d i * (1 - (1 - quoteSeq Y P i) / (1 - t - δ)) ≤
      (schedGate Y d t δ i).denote P := fun i => by
    rw [schedGate_denote Y d t hδ P i, rampAbove]
    exact mul_le_mul_of_nonneg_left (ctsInd_ge_affine hδ (ha i).2 hc) (hw i)
  refine tendsto_prefixSum_atTop_of_frequently_half hg0 hwdiv ?_
  have hpos : ∀ᶠ n in atTop, 0 < prefixSum (schedInd d) n :=
    (Filter.tendsto_atTop.1 hwdiv 1).mono (fun n hn => by linarith)
  have hfr := (hasLimitPoint_zero_iff.1 hlp1) ((1 - t - δ) / 2) (half_pos hc)
  refine (hfr.and_eventually hpos).mono (fun n hn => ?_)
  obtain ⟨habs, hpn⟩ := hn
  have hneg : weightedAverage (schedInd d) (fun i => 1 - quoteSeq Y P i) n =
      - weightedAverage (schedInd d) (fun i => quoteSeq Y P i - 1) n := by
    rw [← weightedAverage_neg]
    congr 1
    funext i
    ring
  have hbound : prefixSum (fun i => schedInd d i * (1 - quoteSeq Y P i)) n ≤
      ((1 - t - δ) / 2) * prefixSum (schedInd d) n := by
    have h1 : weightedAverage (schedInd d) (fun i => 1 - quoteSeq Y P i) n < (1 - t - δ) / 2 := by
      rw [hneg]
      have := (abs_lt.1 habs).1
      linarith
    rw [weightedAverage_eq_div hpn.ne', div_lt_iff₀ hpn] at h1
    exact h1.le
  have hge := prefixSum_ge_of_affine hgw n
  have hhalf : (1 / (1 - t - δ)) * prefixSum (fun i => schedInd d i * (1 - quoteSeq Y P i)) n ≤
      prefixSum (schedInd d) n / 2 := by
    calc (1 / (1 - t - δ)) * prefixSum (fun i => schedInd d i * (1 - quoteSeq Y P i)) n
        ≤ (1 / (1 - t - δ)) * (((1 - t - δ) / 2) * prefixSum (schedInd d) n) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = prefixSum (schedInd d) n / 2 := by
          field_simp
  linarith

/-- **FAF's indicator LUV averages the price of `φ ⋏ ∼∼φ`**: `𝔼_n(𝟙(φ)) = P_n(φ ⋏ ∼∼φ)` for every
history (the `n+1` thresholds `i/(n+1)`, `i ≤ n`, all lie in `[0,1)`, where `LUV.indicatorOf φ`
has the threshold sentence `φ ⋏ ∼∼φ`). Arithmetic only; the same identity as
`DefDoseResponse.indicatorOf_expect_eq`, re-proved here to keep that package out of the imports.
Source: FAF `LUV.indicatorOf` (`Framework/Expectations.lean:612`), `def:e`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem indicatorOf_expect_eq (P : History) (n : ℕ) (φ : Sentence) :
    (LUV.indicatorOf φ).expect P n = P n (φ ⋏ ∼∼φ) := by
  simp only [LUV.expect, LUV.expectApprox]
  have h : ∀ i ∈ Finset.range (n + 1),
      P n ((LUV.indicatorOf φ).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))) = P n (φ ⋏ ∼∼φ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h0 : ¬ ((i : ℚ) / ((n : ℚ) + 1) < 0) := not_lt.mpr (by positivity)
    have h1 : (i : ℚ) / ((n : ℚ) + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      exact_mod_cast hi
    simp [LUV.indicatorOf, h0, h1]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The expectation of `𝟙(⊤)` tends to `1` on every inductor**: its threshold sentence
`⊤ ⋏ ∼∼⊤` holds in every world, so FAF's `lic_provind_true` (no deducibility premise is needed)
drives its price to `1`, and `indicatorOf_expect_eq` identifies the expectation with that price.
Source: FAF `thm:provind` (`lic_provind_true`); `def:e`
Kind: C
Fidelity: exact
Hyps: (a) `hworld` -/
theorem indicatorOf_top_expect_tendsto_one (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n => (LUV.indicatorOf ⊤).expect P n) atTop (𝓝 1) := by
  have h := lic_provind_true P DP (fun _ => ((⊤ : Sentence) ⋏ ∼∼(⊤ : Sentence)))
    (MachineSentenceCodes.const _)
    (fun _ v _ => by
      rw [PCWorld.holds_and, PCWorld.holds_neg, PCWorld.holds_neg]
      exact ⟨PCWorld.holds_top v, fun h => h (PCWorld.holds_top v)⟩) hworld
  have h' : Tendsto (fun n => P n ((⊤ : Sentence) ⋏ ∼∼(⊤ : Sentence))) atTop (𝓝 1) :=
    convergesTo_iff_asympEq_const.mpr h
  exact h'.congr (fun n => (indicatorOf_expect_eq P n ⊤).symm)

/-- The constant family `X_n ≡ 𝟙(⊤)`: the one e.c. family whose realized value an inductor is
known to drive to `1` without any fact about its prices.
Source: audit r1 adversarial B1 (ii)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable abbrev topX : ℕ → LUV := fun _ => LUV.indicatorOf ⊤

/-- `topX` is an e.c. family of LUVs (constant family of a machine-coded indicator).
Source: fa-theorem-a `machineThresholdCodeSeq_const`, `indicatorOf_machineThresholdCodes`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem topX_codes : LUV.MachineThresholdCodeSeq topX :=
  machineThresholdCodeSeq_const (indicatorOf_machineThresholdCodes ⊤)

/-- FAF's Σ₁ quotation family of the paper LIA's own next-day expectations of `𝟙(⊤)`.
Source: li-quote-lane `crossQuotePackage_paper_self`; FAF `paperDeferredExpectationQuoteCode`
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable abbrev topY : ℕ → LUV :=
  (paperDeferredExpectationQuoteCode 𝗜𝚺₁ succDeferral topX topX_codes).luv

/-- The same-market quote package for `topX` (li-quote-lane T2.3).
Source: li-quote-lane `crossQuotePackage_paper_self`
Kind: L
Fidelity: exact (same-market instance)
Hyps: (a) none -/
theorem top_pkg : CrossQuotePackage A.selfH (paperDP 𝗜𝚺₁) succDeferral topX topY :=
  crossQuotePackage_paper_self 𝗜𝚺₁ succDeferral topX topX_codes

/-- The realized value `𝔼^H_{n+1}(𝟙(⊤))` tends to `1` on the paper LIA.
Source: `indicatorOf_top_expect_tendsto_one`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem realized_topX_tendsto_one :
    Tendsto (realized A.selfH succDeferral topX) atTop (𝓝 1) :=
  haveI := w1_inductorH
  (indicatorOf_top_expect_tendsto_one A.selfH (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)).comp
    (tendsto_add_atTop_nat 1)

/-- **`hdiv` discharged at every content threshold `t + δ < 1`** on the paper LIA's quote of its
own next-day expectation of `𝟙(⊤)`.
Source: `schedGate_divergent_of_realized_tendsto_one`
Kind: C
Fidelity: n/a
Hyps: (a) `hδ`, `ht` -/
theorem schedGate_top_divergent (d : DeferralFunction) {t δ : ℚ} (hδ : 0 < δ)
    (ht : (t : ℝ) + δ < 1) : DivergentWeighting (schedGate topY d t δ) A.selfH :=
  haveI := w1_inductorH
  schedGate_divergent_of_realized_tendsto_one top_pkg (paperDP_hworld 𝗜𝚺₁) d hδ ht
    realized_topX_tendsto_one

/-- **T6 at the same-market instance, full package, content threshold.** For every
window-disjoint schedule for `succDeferral` and rationals `0 < δ`, `t + δ < 1` (e.g. `t = 1/2`,
`δ = 1/4`): on the scheduled upper quote gate of the paper LIA's quote of its own next-day
expectation of `𝟙(⊤)`, `0` is a limit point of the gate-weighted average of
`𝔼^H_n(⌜𝔼^H_{n+1}(𝟙(⊤))⌝) − 𝔼^H_n(𝟙(⊤))` — every hypothesis of `theoremSS_limitPoint`
discharged, `hdiv` included. N+ for the package at a content threshold; N− for content (`A = H`,
and both sides tend to `1`). What the instance tests (audit r2 adversarial N3; §D below): the
conclusion does **not** follow from `𝔼^H_n(𝟙(⊤)) → 1` alone (`not_hasLimitPoint_bias_const`), so
the quote's gated average tending to `1` is exercised — but at `A = H` that is `cee`-type content.
On this instance the gate selects nothing in the limit: the quote's scheduled average has limit
point `1` (inside `schedGate_divergent_of_realized_tendsto_one`), so the ramp is saturated on a
set of positive scheduled density; "content threshold" is a fact about `t`, not about selection.
Source: mandate T6 witness; audit r1 adversarial B1 (ii)
Kind: N+ (package) / N− (content)
Fidelity: n/a
Hyps: (a) none -/
theorem theoremSS_paper_self_top {d : DeferralFunction} (hwd : WindowDisjoint succDeferral d)
    {t δ : ℚ} (hδ : 0 < δ) (ht : (t : ℝ) + δ < 1) :
    HasLimitPoint (weightedBias (fun n => (schedGate topY d t δ n).denote A.selfH)
      (quoteSeq topY A.selfH) (fun n => (topX n).expect A.selfH n)) 0 :=
  haveI := w1_inductorH
  theoremSS_limitPoint top_pkg topX_codes (paperDP_hworld 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)
    (fun _ v hv => indicatorOf_valued ⊤ _ v hv) hwd t hδ
    (legibleOn_quote_self topY top_pkg.quote_codes A.selfH) (schedGate_top_divergent d hδ ht)

/-- **T7 at the same-market instance, full package, content threshold.** Same instance as
`theoremSS_paper_self_top`: the scheduled, gate-averaged credence `𝔼^H_n(𝟙(⊤))` is frequently
`≥ t − ρ`. The package is inhabited at a content threshold; the conclusion is immediate there
(`𝔼^H_n(𝟙(⊤)) → 1` gives `SchedThresholdAbove` on *every* nonnegative divergent weight at every
`t ≤ 1`, with no quote, gate or criterion — `schedThresholdAbove_of_tendsto_one`, §D), so N− for
content: this instance tests T7's hypothesis package, not its mechanism.
Source: mandate T7 witness; audit r1 adversarial B1 (ii)
Kind: N+ (package) / N− (content)
Fidelity: n/a
Hyps: (a) none -/
theorem schedThresholdAbove_paper_self_top {d : DeferralFunction}
    (hwd : WindowDisjoint succDeferral d) {t δ : ℚ} (hδ : 0 < δ) (ht : (t : ℝ) + δ < 1) :
    SchedThresholdAbove (fun n => (schedGate topY d t δ n).denote A.selfH)
      (fun n => (topX n).expect A.selfH n) t :=
  haveI := w1_inductorH
  schedThresholdAbove_of_theoremSS top_pkg topX_codes (paperDP_hworld 𝗜𝚺₁)
    (paperDP_hworld 𝗜𝚺₁) (fun _ v hv => indicatorOf_valued ⊤ _ v hv) hwd t hδ
    (legibleOn_quote_self topY top_pkg.quote_codes A.selfH) (schedGate_top_divergent d hδ ht)

/-- The content threshold is inhabited: `t = 1/2`, `δ = 1/4` satisfy `0 < δ` and `t + δ < 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem theoremSS_paper_self_half {d : DeferralFunction} (hwd : WindowDisjoint succDeferral d) :
    HasLimitPoint (weightedBias (fun n => (schedGate topY d (1/2) (1/4) n).denote A.selfH)
      (quoteSeq topY A.selfH) (fun n => (topX n).expect A.selfH n)) 0 :=
  theoremSS_paper_self_top hwd (by norm_num) (by norm_num)


/-! ## C. The mirror: the lower gate from a realized value tending to `0` (`X ≡ 𝟙(⊥)`) -/

/-- The lower ramp is bounded below by an affine function of its argument once the threshold
leaves room: for `δ < t` and `x ≥ 0`, `Ind_δ(x < t) ≥ 1 − x/(t − δ)`.
Source: none: infrastructure (repair round 1)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem ctsInd_below_ge_affine {δ : ℚ} (hδ : 0 < δ) {t x : ℝ} (hx0 : 0 ≤ x)
    (hc : 0 < t - δ) : 1 - x / (t - δ) ≤ ctsInd δ t x := by
  by_cases h : (δ : ℝ) ≤ t - x
  · rw [(ctsInd_eq_one_iff hδ t x).2 h]
    have : 0 ≤ x / (t - δ) := div_nonneg hx0 hc.le
    linarith
  · have h' : t - x < δ := not_le.1 h
    have h2 : 1 < x / (t - δ) := by
      rw [lt_div_iff₀ hc]
      linarith
    have := ctsInd_nonneg δ t x
    linarith

/-- **`hdiv` for the lower gate at a content threshold from the realized value tending to `0`.**
Mirror of `schedGate_divergent_of_realized_tendsto_one`: if `𝔼^H_{f n}(X_n) → 0` then the
scheduled lower quote gate `1[n ∈ im d]·Ind_δ(a_n < t)` has divergent mass in `P`'s market at
every `t > δ`.
Scope: one-way. General in the quoting market.
Source: audit r1 adversarial B1 (ii), mirror; FAF `thm:recurringunbiasednessexp` via `quote_unbiased`
Kind: C
Fidelity: n/a (a derivation of the mirror rows' `hdiv`)
Hyps: (a) `hworld`, `hδ`, `ht`, `hv`; (c) `pkg.reflected` (through `quote_unbiased`). -/
theorem schedGateBelow_divergent_of_realized_tendsto_zero {H P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DP f X Y)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (d : DeferralFunction) {t δ : ℚ} (hδ : 0 < δ) (ht : (δ : ℝ) < t)
    (hv : Tendsto (realized H f X) atTop (𝓝 0)) :
    DivergentWeighting (schedGateBelow Y d t δ) P := by
  have hc : (0 : ℝ) < t - δ := by linarith
  have hw : ∀ i, 0 ≤ schedInd d i := fun i => (schedInd_mem_Icc d i).1
  have hwdiv : Tendsto (prefixSum (schedInd d)) atTop atTop := by
    have h := (scheduleIndicator_divergent d P).2
    simpa only [scheduleIndicator_denote] using h
  have ha : ∀ i, quoteSeq Y P i ∈ Set.Icc (0 : ℝ) 1 := fun i =>
    LUV.expect_mem_Icc P i (Y i)
      (fun s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) i s)
  have hlp : HasLimitPoint (weightedBias (schedInd d) (quoteSeq Y P) (realized H f X)) 0 := by
    have h := quote_unbiased pkg hworld (scheduleIndicator_pgenerable d)
      (scheduleIndicator_divergent d P)
    have hfun : (fun i => (scheduleIndicator d i).denote P) = schedInd d :=
      funext (scheduleIndicator_denote d P)
    rw [hfun] at h
    exact h
  have hv0 : Tendsto (weightedAverage (schedInd d) (fun i => realized H f X i - 0)) atTop
      (𝓝 0) :=
    weightedAverage_tendsto_zero hw hwdiv (by simpa using hv)
  have hlp0 : HasLimitPoint (weightedAverage (schedInd d) (fun i => quoteSeq Y P i - 0)) 0 :=
    A.hasLimitPoint_zero_of_add_tendsto hlp hv0 (fun n => by
      show weightedAverage (schedInd d) (fun i => quoteSeq Y P i - 0) n =
        weightedAverage (schedInd d) (fun i => quoteSeq Y P i - realized H f X i) n +
          weightedAverage (schedInd d) (fun i => realized H f X i - 0) n
      exact A.weightedAverage_split (schedInd d) (quoteSeq Y P) (realized H f X) (fun _ => 0) n)
  refine ⟨fun n => schedGateBelow_mem_Icc Y d t hδ P n, ?_⟩
  have hg0 : ∀ i, 0 ≤ (schedGateBelow Y d t δ i).denote P :=
    fun i => (schedGateBelow_mem_Icc Y d t hδ P i).1
  have hgw : ∀ i, schedInd d i * (1 - (1 - (1 - quoteSeq Y P i)) / (t - δ)) ≤
      (schedGateBelow Y d t δ i).denote P := fun i => by
    rw [schedGateBelow_denote Y d t hδ P i, rampBelow]
    have e : (1 : ℝ) - (1 - quoteSeq Y P i) = quoteSeq Y P i := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (ctsInd_below_ge_affine hδ (ha i).1 hc) (hw i)
  refine tendsto_prefixSum_atTop_of_frequently_half hg0 hwdiv ?_
  have hpos : ∀ᶠ n in atTop, 0 < prefixSum (schedInd d) n :=
    (Filter.tendsto_atTop.1 hwdiv 1).mono (fun n hn => by linarith)
  have hfr := (hasLimitPoint_zero_iff.1 hlp0) ((t - δ) / 2) (half_pos hc)
  refine (hfr.and_eventually hpos).mono (fun n hn => ?_)
  obtain ⟨habs, hpn⟩ := hn
  have hbound : prefixSum (fun i => schedInd d i * (1 - (1 - quoteSeq Y P i))) n ≤
      ((t - δ) / 2) * prefixSum (schedInd d) n := by
    have h1 : weightedAverage (schedInd d) (fun i => quoteSeq Y P i - 0) n < (t - δ) / 2 := by
      have := (abs_lt.1 habs).2
      linarith
    rw [weightedAverage_eq_div hpn.ne', div_lt_iff₀ hpn] at h1
    have e : (fun i => schedInd d i * (1 - (1 - quoteSeq Y P i))) =
        fun i => schedInd d i * (quoteSeq Y P i - 0) := by
      funext i
      ring
    rw [e]
    exact h1.le
  have hge := prefixSum_ge_of_affine hgw n
  have hhalf : (1 / (t - δ)) * prefixSum (fun i => schedInd d i * (1 - (1 - quoteSeq Y P i))) n ≤
      prefixSum (schedInd d) n / 2 := by
    calc (1 / (t - δ)) * prefixSum (fun i => schedInd d i * (1 - (1 - quoteSeq Y P i))) n
        ≤ (1 / (t - δ)) * (((t - δ) / 2) * prefixSum (schedInd d) n) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = prefixSum (schedInd d) n / 2 := by
          field_simp
  linarith

/-- No world holds `⊥` (Foundation's Boolean evaluation).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem not_holds_bot (v : PCWorld) : ¬ v.Holds (⊥ : Sentence) := by
  simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val]

/-- **The expectation of `𝟙(⊥)` tends to `0` on every inductor**: its threshold sentence
`⊥ ⋏ ∼∼⊥` holds in no world, so FAF's `lic_provind_false` drives its price to `0`.
Source: FAF `thm:provind` (`lic_provind_false`); `def:e`
Kind: C
Fidelity: exact
Hyps: (a) `hworld` -/
theorem indicatorOf_bot_expect_tendsto_zero (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n => (LUV.indicatorOf ⊥).expect P n) atTop (𝓝 0) := by
  have h := lic_provind_false P DP (fun _ => ((⊥ : Sentence) ⋏ ∼∼(⊥ : Sentence)))
    (MachineSentenceCodes.const _)
    (fun _ v _ => by
      rw [PCWorld.holds_neg, PCWorld.holds_and]
      exact fun hb => not_holds_bot v hb.1) hworld
  have h' : Tendsto (fun n => P n ((⊥ : Sentence) ⋏ ∼∼(⊥ : Sentence))) atTop (𝓝 0) :=
    convergesTo_iff_asympEq_const.mpr h
  exact h'.congr (fun n => (indicatorOf_expect_eq P n ⊥).symm)

/-- The constant family `X_n ≡ 𝟙(⊥)`.
Source: audit r1 adversarial B1 (ii), mirror
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable abbrev botX : ℕ → LUV := fun _ => LUV.indicatorOf ⊥

/-- `botX` is an e.c. family of LUVs.
Source: fa-theorem-a `machineThresholdCodeSeq_const`, `indicatorOf_machineThresholdCodes`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem botX_codes : LUV.MachineThresholdCodeSeq botX :=
  machineThresholdCodeSeq_const (indicatorOf_machineThresholdCodes ⊥)

/-- FAF's Σ₁ quotation family of the paper LIA's own next-day expectations of `𝟙(⊥)`.
Source: li-quote-lane `crossQuotePackage_paper_self`; FAF `paperDeferredExpectationQuoteCode`
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable abbrev botY : ℕ → LUV :=
  (paperDeferredExpectationQuoteCode 𝗜𝚺₁ succDeferral botX botX_codes).luv

/-- The same-market quote package for `botX`.
Source: li-quote-lane `crossQuotePackage_paper_self`
Kind: L
Fidelity: exact (same-market instance)
Hyps: (a) none -/
theorem bot_pkg : CrossQuotePackage A.selfH (paperDP 𝗜𝚺₁) succDeferral botX botY :=
  crossQuotePackage_paper_self 𝗜𝚺₁ succDeferral botX botX_codes

/-- The realized value `𝔼^H_{n+1}(𝟙(⊥))` tends to `0` on the paper LIA.
Source: `indicatorOf_bot_expect_tendsto_zero`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem realized_botX_tendsto_zero :
    Tendsto (realized A.selfH succDeferral botX) atTop (𝓝 0) :=
  haveI := w1_inductorH
  (indicatorOf_bot_expect_tendsto_zero A.selfH (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)).comp
    (tendsto_add_atTop_nat 1)

/-- **`hdiv` for the lower gate discharged at every content threshold `t > δ`** on the paper
LIA's quote of its own next-day expectation of `𝟙(⊥)`.
Source: `schedGateBelow_divergent_of_realized_tendsto_zero`
Kind: C
Fidelity: n/a
Hyps: (a) `hδ`, `ht` -/
theorem schedGateBelow_bot_divergent (d : DeferralFunction) {t δ : ℚ} (hδ : 0 < δ)
    (ht : (δ : ℝ) < t) : DivergentWeighting (schedGateBelow botY d t δ) A.selfH :=
  haveI := w1_inductorH
  schedGateBelow_divergent_of_realized_tendsto_zero bot_pkg (paperDP_hworld 𝗜𝚺₁) d hδ ht
    realized_botX_tendsto_zero

/-- **T6 mirror at the same-market instance, full package, content threshold.** For every
window-disjoint schedule for `succDeferral` and rationals `0 < δ < t` (e.g. `t = 1/2`,
`δ = 1/4`): on the scheduled lower quote gate of the paper LIA's quote of its own next-day
expectation of `𝟙(⊥)`, `0` is a limit point of the gate-weighted average of
`𝔼^H_n(⌜𝔼^H_{n+1}(𝟙(⊥))⌝) − 𝔼^H_n(𝟙(⊥))` — every hypothesis of `theoremSS_limitPoint_below`
discharged. N+ for the package at a content threshold; N− for content (`A = H`; both sides
tend to `0`; as for `theoremSS_paper_self_top`, the conclusion is not immediate from the realized
value alone).
Source: mandate T6 witness (mirror); audit r1 adversarial B1 (ii)
Kind: N+ (package) / N− (content)
Fidelity: n/a
Hyps: (a) none -/
theorem theoremSS_paper_self_bot {d : DeferralFunction} (hwd : WindowDisjoint succDeferral d)
    {t δ : ℚ} (hδ : 0 < δ) (ht : (δ : ℝ) < t) :
    HasLimitPoint (weightedBias (fun n => (schedGateBelow botY d t δ n).denote A.selfH)
      (quoteSeq botY A.selfH) (fun n => (botX n).expect A.selfH n)) 0 :=
  haveI := w1_inductorH
  theoremSS_limitPoint_below bot_pkg botX_codes (paperDP_hworld 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)
    (fun _ v hv => indicatorOf_valued ⊥ _ v hv) hwd t hδ
    (legibleOn_quote_self botY bot_pkg.quote_codes A.selfH) (schedGateBelow_bot_divergent d hδ ht)

/-- **T7 mirror at the same-market instance, full package, content threshold.** Same instance as
`theoremSS_paper_self_bot`: the scheduled, lower-gate-averaged credence `𝔼^H_n(𝟙(⊥))` is
frequently `≤ t + ρ`. Inhabited at a content threshold; the conclusion is immediate there
(`𝔼^H_n(𝟙(⊥)) → 0`; the mirror of `schedThresholdAbove_of_tendsto_one`), so N− for content.
Source: mandate T7 witness (mirror); audit r1 adversarial B1 (ii)
Kind: N+ (package) / N− (content)
Fidelity: n/a
Hyps: (a) none -/
theorem schedThresholdBelow_paper_self_bot {d : DeferralFunction}
    (hwd : WindowDisjoint succDeferral d) {t δ : ℚ} (hδ : 0 < δ) (ht : (δ : ℝ) < t) :
    SchedThresholdBelow (fun n => (schedGateBelow botY d t δ n).denote A.selfH)
      (fun n => (botX n).expect A.selfH n) t :=
  haveI := w1_inductorH
  schedThresholdBelow_of_theoremSS bot_pkg botX_codes (paperDP_hworld 𝗜𝚺₁)
    (paperDP_hworld 𝗜𝚺₁) (fun _ v hv => indicatorOf_valued ⊥ _ v hv) hwd t hδ
    (legibleOn_quote_self botY bot_pkg.quote_codes A.selfH) (schedGateBelow_bot_divergent d hδ ht)


/-! ## D. What the content-threshold instances test (audit r2 adversarial N3; probe adopted)

Two bounds on the grades of §B/§C, over abstract real sequences (the adversarial auditor's probe
`audit-r2-probes/TrivialContentTop.lean`, adopted over the record's `SchedThresholdAbove`):

* `schedThresholdAbove_of_tendsto_one` — whenever the credence `h → 1`, `SchedThresholdAbove w h t`
  holds on **every** nonnegative weight with divergent mass at every `t ≤ 1`: no quote, no gate
  selection, no criterion. So `schedThresholdAbove_paper_self_top` inhabits T7's full package,
  but its conclusion holds for a reason unrelated to T7's mechanism — the precise sense of its
  "N− content".
* `not_hasLimitPoint_bias_const` — `h → 1` alone does **not** give T6's conclusion (`a ≡ 0`,
  `h ≡ 1`, `w ≡ 1`: the bias is `≡ −1`), so `theoremSS_paper_self_top` does exercise the quote's
  gated average tending to `1`; its "N− content" is the same-market one (`A = H`, `cee`-type
  content). -/

/-- The weighted average of the constant `1` is `1` once the mass is positive.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem weightedAverage_one_of_pos {w : ℕ → ℝ} {n : ℕ} (hn : 0 < prefixSum w n) :
    weightedAverage w (fun _ => (1 : ℝ)) n = 1 := by
  rw [weightedAverage_eq_div hn.ne']
  simp only [mul_one]
  exact div_self hn.ne'

/-- **`h → 1` makes the scheduled above-threshold inequality free**: on every nonnegative weight
with divergent mass and at every `t ≤ 1`, `SchedThresholdAbove w h t` follows from
`Tendsto h atTop (𝓝 1)` alone — no quote, no gate, no criterion. This is the exact content of
the "N− content" grade of `schedThresholdAbove_paper_self_top` (and, mirrored, of
`schedThresholdBelow_paper_self_bot`): the instance tests T7's hypothesis package, not its
mechanism.
Source: audit r2 adversarial N3 (probe `TrivialContentTop.lean`, C1)
Kind: L
Fidelity: n/a (a bound on what a witness tests)
Hyps: (a) none -/
theorem schedThresholdAbove_of_tendsto_one {w h : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) (hv : Tendsto h atTop (𝓝 1)) {t : ℝ}
    (ht : t ≤ 1) : SchedThresholdAbove w h t := by
  intro ρ hρ
  have hev : ∀ᶠ n in atTop, 0 < prefixSum w n := hdiv.eventually (eventually_gt_atTop 0)
  have h1h : Tendsto (fun i => (1 : ℝ) - h i) atTop (𝓝 (1 - 1)) := tendsto_const_nhds.sub hv
  rw [sub_self] at h1h
  have h0 : Tendsto (weightedAverage w (fun i => 1 - h i)) atTop (𝓝 0) :=
    weightedAverage_tendsto_zero hw hdiv h1h
  have hsm := (Metric.tendsto_nhds.1 h0) ρ hρ
  refine (hsm.and hev).frequently.mono (fun n hn => ?_)
  obtain ⟨h1, h2⟩ := hn
  rw [Real.dist_eq, sub_zero, weightedAverage_sub w (fun _ => 1) h h2.ne',
    weightedAverage_one_of_pos h2, abs_lt] at h1
  linarith [h1.1]

/-- The bias of `a ≡ 0` against `h ≡ 1` under `w ≡ 1` is `−1` on every day.
Source: audit r2 adversarial N3 (probe C2)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bias_const_neg_one (n : ℕ) :
    weightedBias (fun _ => (1 : ℝ)) (fun _ => 0) (fun _ => 1) n = -1 := by
  have hpos : 0 < prefixSum (fun _ : ℕ => (1 : ℝ)) n := by
    unfold prefixSum
    simp
    positivity
  rw [weightedBias, weightedAverage_eq_div hpos.ne']
  have h1 : prefixSum (fun i => (fun _ : ℕ => (1 : ℝ)) i * ((fun _ : ℕ => (0 : ℝ)) i - 1)) n =
      - prefixSum (fun _ : ℕ => (1 : ℝ)) n := by
    unfold prefixSum
    simp
  rw [h1, neg_div, div_self hpos.ne']

/-- **`h → 1` alone does not give T6's conclusion**: a quote stuck at `0` against a credence at
`1` under a divergent weight has bias `−1`, and `0` is not a limit point. So the content-threshold
instance `theoremSS_paper_self_top` exercises the quote's gated average (which tends to `1`
there), unlike T7's instance, whose conclusion `schedThresholdAbove_of_tendsto_one` gives for free.
Source: audit r2 adversarial N3 (probe C2)
Kind: L
Fidelity: n/a (a bound on what a witness tests)
Hyps: (a) none -/
theorem not_hasLimitPoint_bias_const :
    ¬ HasLimitPoint (weightedBias (fun _ => (1 : ℝ)) (fun _ => 0) (fun _ => 1)) 0 := by
  intro h
  have hfr := (hasLimitPoint_zero_iff.1 h) (1 / 2) (by norm_num)
  obtain ⟨n, hn⟩ := hfr.exists
  rw [bias_const_neg_one] at hn
  norm_num at hn


/-! ## E. The T4 witness's return vanishes without the trader (audit r2 adversarial N6)

`A.hSideBridge_w2` discharges every hypothesis of `hSideBridge` on li-pseudorandom's decided-atom
inductor with the **constant** family `X ≡ 𝟙(atom k)`. Its conclusion holds for a reason that
needs no trader: the day-`n` mesh of an indicator LUV is priced at `P_m(φ ⋏ ∼∼φ)` on *every* day
`m` (`bundle_indicator_price`, from FAF's `expectAffine_priceAt` and the threshold arithmetic of
`indicatorOf_expectApprox_eq`), so the round-trip return is `P_{n+1}(φ ⋏ ∼∼φ) − P_n(φ ⋏ ∼∼φ)`,
which tends to `0` by the convergence of a fixed sentence's price alone (FAF's `thm:con`,
`lic_limitingBelief_tendsto`). So the T4 witness is N− for content in the strongest sense: on a
constant indicator family the per-day return itself vanishes
(`hSideBridge_w2_return_tendsto_zero`), and the averaged conclusion follows for every weighting.
A witness that exercises the return needs a non-constant family, which the package does not
build. (The auditor argued this and did not probe it; it is machine-checked here.) -/

/-- **FAF's indicator LUV averages the price of `φ ⋏ ∼∼φ` at every precision, under every
valuation**: `𝔼^V_k(𝟙(φ)) = V(φ ⋏ ∼∼φ)` for `k > 0` (all `k` thresholds `i/k`, `i < k`, lie in
`[0,1)`). `indicatorOf_expect_eq` is the case `V = P_n`, `k = n+1`.
Source: FAF `LUV.indicatorOf`, `def:e`; audit r2 adversarial N6
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem indicatorOf_expectApprox_eq (V : Valuation) {k : ℕ} (hk : 0 < k) (φ : Sentence) :
    (LUV.indicatorOf φ).expectApprox V k = V (φ ⋏ ∼∼φ) := by
  simp only [LUV.expectApprox]
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have h : ∀ i ∈ Finset.range k,
      V ((LUV.indicatorOf φ).gt ((i : ℚ) / (k : ℚ))) = V (φ ⋏ ∼∼φ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h0 : ¬ ((i : ℚ) / (k : ℚ) < 0) := not_lt.mpr (by positivity)
    have h1 : (i : ℚ) / (k : ℚ) < 1 := by
      rw [div_lt_one hkq]
      exact_mod_cast hi
    simp [LUV.indicatorOf, h0, h1]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

/-- **The mesh of an indicator LUV is priced at `P_m(φ ⋏ ∼∼φ)` on every day `m`**: FAF's
`expectAffine_priceAt` plus `indicatorOf_expectApprox_eq`. In particular the day-`n` mesh's
day-`(n+1)` price and its day-`n` expectation differ by `P_{n+1}(φ ⋏ ∼∼φ) − P_n(φ ⋏ ∼∼φ)`.
Source: FAF `expectAffine_priceAt`; audit r2 adversarial N6
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bundle_indicator_price (P : History) (φ : Sentence) (n m : ℕ) :
    (bundle (fun _ => LUV.indicatorOf φ) n).price P m = P m (φ ⋏ ∼∼φ) := by
  show ((LUV.indicatorOf φ).expectAffine (n + 1)).price P m = _
  rw [LUV.expectAffine_priceAt, indicatorOf_expectApprox_eq (P m) (Nat.succ_pos n)]

/-- **The round-trip return on a constant indicator family vanishes with no trader**: on any
inductor, `price^P_{n+1}(bundle_n) − 𝔼^P_n(𝟙(φ)) = P_{n+1}(φ ⋏ ∼∼φ) − P_n(φ ⋏ ∼∼φ) → 0` by the
convergence of the fixed sentence's price (FAF `thm:con`). Hence T4's conclusion on such a family
holds for every weighting without `lic_not_frequently_positive_feedback_return`.
Source: FAF `lic_limitingBelief_tendsto` (`thm:con`); audit r2 adversarial N6
Kind: C
Fidelity: n/a (a bound on what the T4 witness tests)
Hyps: (a) `hworld` -/
theorem bundle_indicator_return_tendsto_zero {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (φ : Sentence) :
    Tendsto (fun n => (bundle (fun _ => LUV.indicatorOf φ) n).price P (n + 1)
      - (LUV.indicatorOf φ).expect P n) atTop (𝓝 0) := by
  have hc : Tendsto (fun n => P n (φ ⋏ ∼∼φ)) atTop (𝓝 (limitingBelief P (φ ⋏ ∼∼φ))) :=
    lic_limitingBelief_tendsto P DP hworld (φ ⋏ ∼∼φ)
  have h1 := (hc.comp (tendsto_add_atTop_nat 1)).sub hc
  rw [sub_self] at h1
  refine h1.congr (fun n => ?_)
  simp only [Function.comp_apply]
  rw [bundle_indicator_price, indicatorOf_expect_eq]

/-- **The T4 witness's return vanishes without the trader** (audit r2 adversarial N6): on
`A.hSideBridge_w2`'s instance (`w2H x`, `X ≡ w2X k = 𝟙(atom k)`, lookahead `succDeferral`) the
per-day return `price^H_{n+1}(bundle_n) − 𝔼^H_n(𝟙(atom k))` tends to `0` on its own, so the
witness's conclusion holds for every weighting with no criterion on the trader. The instance is
N− for content in this strong sense (the return is not merely "not shown non-zero": it is zero in
the limit); a witness exercising the return needs a non-constant family.
Source: audit r2 adversarial N6; fa-theorem-a W2; findings F-A10
Kind: N− (content check on `A.hSideBridge_w2`)
Fidelity: n/a
Hyps: (a) none -/
theorem hSideBridge_w2_return_tendsto_zero {x : ℕ → Bool} (hx : Primrec x) (k : ℕ) :
    Tendsto (fun n => (bundle (fun _ => w2X k) n).price (w2H x) (succDeferral.f n)
      - (w2X k).expect (w2H x) n) atTop (𝓝 0) :=
  haveI := w2_inductorH hx
  bundle_indicator_return_tendsto_zero (w2_hworldH x) (Formula.atom k)

end Cleanroom.Fa.FaForcingTrader
