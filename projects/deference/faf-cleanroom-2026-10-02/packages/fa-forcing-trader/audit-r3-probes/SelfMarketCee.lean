import Cleanroom.Fa.FaForcingTrader.Witnesses
import Cleanroom.Fa.FaForcingTrader.Analysis

/-!
# `fa-forcing-trader` · audit r3 (adversarial) · probe: the same-market witnesses from `cee` alone

Evidence for `fa-forcing-trader-audit-r3-adversarial.md`. **Not imported by the library.**

The package grades its same-market witnesses "N+ package / N− content" and gives as the reason
for "N− content" that at `A = H` the conclusion "also follows from `cee`" (ledger §2, rows T3 and
T6; `A/Witnesses.lean` header). That reason is stated, not machine-checked. This probe checks it,
and finds it is *stronger* than stated: FAF's closed `thm:cee` over the paper LIA
(`lic_expected_future_expectations_closed`) gives `a_n − 𝔼^H_n(X_n) → 0` **pointwise** at
`A = H = liaHistory (paperDP 𝗜𝚺₁)`, so

* **C1** — T6's conclusion holds there at **full-limit** grade on every nonnegative divergent
  weight, with no certificate, no gate legality, no trader and no `quote_unbiased` (the donor
  rule alone): the conclusions of `A.theoremSS_paper_self` (limit point, conditional on `hdiv`)
  and of `theoremSS_paper_self_top` are instances. So at the same market even the grade-2/3
  conclusion is free of its (b); the "exercises the quote's gated average" of
  `theoremSS_paper_self_top`'s docstring is exercise of `cee`, not of the two-sided mechanism.
* **C2** — the violation weight `violW` of `A.v3Theorem1_paper_self` is **eventually `0`** for
  every `ε > 0`, so T3's conclusion there (finite mass) holds with no trader and no T4.
* **C3** — hence `ChasingSchedule succDeferral (viol …)` is a theorem at `A = H` (vacuously, the
  weight tends to `0`; probe `ChasingVacuous.lean`), and the *full* hypothesis package of
  `v3Theorem1_tendsto_zero_of_chasing` — a load-bearing T10 row the ledger ships **no**
  witness for — is inhabited at the same market, with the conclusion being the premise
  (N− in the strongest sense).

Nothing here is a defect in a statement: it sharpens three grading sentences and supplies one
missing (degenerate) inhabitant. Heavy import (`Witnesses` → `A/Witnesses` → the paper LIA).
-/

namespace Cleanroom.Fa.FaForcingTrader.AuditR3

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Cleanroom.Fa.FaForcingTrader
  Filter Topology

/-- **`cee` at the paper-self instance, pointwise**: for any e.c. theory-valued family `X`, the
paper LIA's quote of its own next-day expectation agrees with its present expectation,
`a_n − 𝔼^H_n(X_n) → 0` (FAF `lic_expected_future_expectations_closed`, sides swapped). -/
theorem cee_self (X : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X)
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP 𝗜𝚺₁) →
      ∃ x : ℝ, v.ValuesAt (X n) x) :
    Tendsto (fun n => quoteSeq (paperDeferredExpectationQuoteCode 𝗜𝚺₁ succDeferral X hX).luv
      A.selfH n - (X n).expect A.selfH n) atTop (𝓝 0) := by
  have h := lic_expected_future_expectations_closed 𝗜𝚺₁ succDeferral X hX hval
  have h' : Tendsto (fun n => (X n).expect A.selfH n -
      quoteSeq (paperDeferredExpectationQuoteCode 𝗜𝚺₁ succDeferral X hX).luv A.selfH n)
      atTop (𝓝 0) := h
  have hneg := h'.neg
  rw [neg_zero] at hneg
  exact hneg.congr (fun n => by ring)

/-- **C1.** T6's conclusion at `A = H`, full-limit grade, on *every* nonnegative divergent weight
— from `cee` and the donor rule alone. -/
theorem theoremSS_self_fullLimit_of_cee (X : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X)
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP 𝗜𝚺₁) →
      ∃ x : ℝ, v.ValuesAt (X n) x)
    {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (hdiv : Tendsto (prefixSum w) atTop atTop) :
    WeightedApprox w (quoteSeq (paperDeferredExpectationQuoteCode 𝗜𝚺₁ succDeferral X hX).luv
      A.selfH) (fun n => (X n).expect A.selfH n) :=
  weightedAverage_tendsto_zero hw hdiv (cee_self X hX hval)

/-- **C1, instance**: the conclusion of `A.theoremSS_paper_self` (on `cleanX`, limit point, its
gate) from `cee` alone — the trader bridge T4 and `quote_unbiased` are not used. -/
theorem theoremSS_paper_self_of_cee {d : DeferralFunction} (t δ : ℚ)
    (hdiv : DivergentWeighting (schedGate A.selfY d t δ) A.selfH) :
    HasLimitPoint (weightedBias (fun n => (schedGate A.selfY d t δ n).denote A.selfH)
      (quoteSeq A.selfY A.selfH) (fun n => (cleanX n).expect A.selfH n)) 0 := by
  have h := theoremSS_self_fullLimit_of_cee cleanX cleanX_codes
    (fun n v hv => indicatorOf_valued (witnessQuoted 0 n) _ v hv)
    (fun i => (hdiv.1 i).1) hdiv.2
  rw [weightedApprox_iff_weightedBias] at h
  rw [hasLimitPoint_zero_iff]
  intro ε hε
  exact ((Metric.tendsto_nhds.1 h) ε hε).frequently.mono (fun n hn => by
    rwa [Real.dist_eq, sub_zero] at hn)

/-- **C1, instance**: the conclusion of `theoremSS_paper_self_top` (on `𝟙(⊤)`) from `cee` alone,
at every `t`, `δ` for which the gate diverges — in particular at every content threshold. -/
theorem theoremSS_paper_self_top_of_cee {d : DeferralFunction} (t δ : ℚ)
    (hdiv : DivergentWeighting (schedGate topY d t δ) A.selfH) :
    HasLimitPoint (weightedBias (fun n => (schedGate topY d t δ n).denote A.selfH)
      (quoteSeq topY A.selfH) (fun n => (topX n).expect A.selfH n)) 0 := by
  have h := theoremSS_self_fullLimit_of_cee topX topX_codes
    (fun _ v hv => indicatorOf_valued ⊤ _ v hv) (fun i => (hdiv.1 i).1) hdiv.2
  rw [weightedApprox_iff_weightedBias] at h
  rw [hasLimitPoint_zero_iff]
  intro ε hε
  exact ((Metric.tendsto_nhds.1 h) ε hε).frequently.mono (fun n hn => by
    rwa [Real.dist_eq, sub_zero] at hn)

/-- **C2.** At `A = H` the schedule-free violation weight is eventually `0` for every `ε > 0`:
positive weight needs `a_n > t` and `h_n < t − ε`, i.e. `a_n − h_n > ε`, which `cee` forbids
eventually. -/
theorem viol_self_eventually_zero (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      viol (fun n => (cleanX n).expect A.selfH n) (quoteSeq A.selfY A.selfH) t ε δ n = 0 := by
  have hc := cee_self cleanX cleanX_codes (fun n v hv => indicatorOf_valued (witnessQuoted 0 n) _ v hv)
  have h := (Metric.tendsto_nhds.1 hc) ε (by exact_mod_cast hε)
  refine h.mono (fun n hn => ?_)
  rw [Real.dist_eq, sub_zero] at hn
  by_contra hne
  have hpos : 0 < viol (fun n => (cleanX n).expect A.selfH n) (quoteSeq A.selfY A.selfH) t ε δ n :=
    lt_of_le_of_ne (dsWeight_nonneg _ _ _ _ _) (Ne.symm hne)
  obtain ⟨hta, hht⟩ := dsWeight_pos_imp hδ hpos
  have hgt : (ε : ℝ) < quoteSeq A.selfY A.selfH n - (cleanX n).expect A.selfH n := by linarith
  linarith [le_abs_self (quoteSeq A.selfY A.selfH n - (cleanX n).expect A.selfH n)]

/-- The scheduled violation weight is then eventually `0` too. -/
theorem violW_self_eventually_zero (d : DeferralFunction) (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      violW d (quoteSeq A.selfY A.selfH) (fun n => (cleanX n).expect A.selfH n) t ε δ n = 0 :=
  (viol_self_eventually_zero t ε hδ hε).mono (fun n hn => by
    unfold violW
    rw [hn, mul_zero])

/-- A nonnegative sequence that is `0` from `N` on has prefix sums bounded by the `N`-th. -/
theorem prefixSum_le_of_eventually_zero {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) {N : ℕ}
    (hN : ∀ n, N ≤ n → w n = 0) (n : ℕ) : prefixSum w n ≤ prefixSum w N := by
  rcases le_or_gt n N with h | h
  · exact prefixSum_mono hw h
  · have hconst : ∀ k, prefixSum w (N + k) = prefixSum w N := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [← Nat.add_assoc, prefixSum_succ, ih, hN (N + k + 1) (by omega), add_zero]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.le
    exact (hconst k).le

/-- **C2, the T3 instance**: the conclusion of `A.v3Theorem1_paper_self` from `cee` alone — no
trader, no T4, no `quote_unbiased`. -/
theorem v3Theorem1_paper_self_of_cee (d : DeferralFunction) (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hε : 0 < ε) :
    ¬ Tendsto (prefixSum (violW d (quoteSeq A.selfY A.selfH)
      (fun n => (cleanX n).expect A.selfH n) t ε δ)) atTop atTop := by
  intro hdiv
  obtain ⟨N, hN⟩ := eventually_atTop.1 (violW_self_eventually_zero d t ε hδ hε)
  have hb := prefixSum_le_of_eventually_zero (fun i => (violW_mem_Icc _ _ _ _ _ _ i).1) hN
  obtain ⟨n, hn⟩ := (hdiv.eventually (eventually_gt_atTop
    (prefixSum (violW d (quoteSeq A.selfY A.selfH) (fun n => (cleanX n).expect A.selfH n) t ε δ)
      N))).exists
  linarith [hb n]

/-- **C3.** The chasing hypothesis is a theorem at `A = H`: the violation weight tends to `0`, so
no `θ > 0` is reached frequently. -/
theorem chasing_self (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ) (hε : 0 < ε) :
    ChasingSchedule succDeferral
      (viol (fun n => (cleanX n).expect A.selfH n) (quoteSeq A.selfY A.selfH) t ε δ) := by
  intro θ hθ hfr
  exfalso
  obtain ⟨n, h1, h2⟩ := (hfr.and_eventually (viol_self_eventually_zero t ε hδ hε)).exists
  rw [h2] at h1
  linarith

/-- **C3, the inhabitant**: the full hypothesis package of `v3Theorem1_tendsto_zero_of_chasing`
(T10's FAF corollary, `partial: over the OPEN pair and under chasing`) is inhabited at the same
market — `hjointAll` by `A.self_jointLegible` on every schedule, `hch` by `chasing_self`. The
package ships no witness for this row. N− in the strongest sense: the conclusion is
`viol_self_eventually_zero`. -/
theorem v3Theorem1_tendsto_zero_of_chasing_paper_self (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hε : 0 < ε) :
    Tendsto (viol (fun n => (cleanX n).expect A.selfH n) (quoteSeq A.selfY A.selfH) t ε δ)
      atTop (𝓝 0) :=
  haveI := w1_inductorH
  v3Theorem1_tendsto_zero_of_chasing A.self_pkg cleanX_codes (paperDP_hworld 𝗜𝚺₁)
    (paperDP_hworld 𝗜𝚺₁) (fun n v hv => indicatorOf_valued (witnessQuoted 0 n) _ v hv) t ε hδ hε
    (fun d _ => ⟨A.self_jointLegible d t ε hδ, A.self_jointLegible d t ε hδ⟩)
    (chasing_self t ε hδ hε)

end Cleanroom.Fa.FaForcingTrader.AuditR3
