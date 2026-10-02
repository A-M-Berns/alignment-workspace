import Cleanroom.Fa.FaAdaptiveJoint.Theorem2

/-!
# `fa-adaptive-joint` · Staleness: the one-day staleness question (T7)

[[fa-adaptive-joint-mandate]] T7; [[fa-positive-results-corrected-v3]] §1 (A1) remark 3, §6 (iii);
root-fa-023; lean-deference-059; [[joint-clearing-and-trader-class]] §5. Scope: for a *fixed*
question the issue is moot (Theorem A needs no visibility); this is about v3's varying-question
gate. In an alternating protocol `A` sees `H`'s *previous-day* price, so the gate `A` can carry is
the **stale gate** `staleViol_n = Ind_δ(a_n > t) · Ind_δ(h_{n−1} < t − ε)` (day `0` reads `h_0`:
natural subtraction, one day's convention).

* (i) `staleViol`, `StaleLegible` — the stale gate and its legibility on `A`, the *cheaper* (c)
  (one-way, settled data: [[delay-program]] §1).
* (ii) `stale_gate_fires_off_violation` — what alternation costs: an alternating `h` on which the
  stale gate fires exactly on the days the same-day gate is silent and vice versa; the `A`-side
  engine on the stale gate says nothing about same-day violation, and the trader's purchase-price
  bound `h_n < t − ε` is exactly what fails.
* (iii) the positive transfer: `dsWeight_le_shift` (a one-day move of at most `ε/4` bounds one
  gate by the other at half the margin), `viol_tendsto_of_stale`/`staleViol_tendsto_of_viol`, and
  **`v3Theorem2_stale_of_noJumps_of_bridge`**: Theorem 2 for the stale gate under "no one-day
  jumps on the gate" (the gate-general `v3Theorem2_gate_of_bridge`), with
  `v3Theorem2_alternating_transfer` carrying it to the same-day gate at margin `2ε`.
* The OPEN row of record `v3Theorem2_strictAlternation` over the carrier `AlternatingPair`:
  Theorem 2's conclusion for the alternating pair *without* the no-jumps hypothesis — neither a
  proof nor a counterexample is known (a counterexample needs an inductor pair with `Θ(1)`
  one-day moves on the gate infinitely often; (ii) is only the real-sequence half).
-/

namespace Cleanroom.Fa.FaAdaptiveJoint

open LogicalInduction Cleanroom.Fa.FaForcingTrader Cleanroom.Fa.FaTheoremA
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Filter Topology

/-! ## A. The stale gate -/

/-- **The stale gate** `Ind_δ(a_n > t) · Ind_δ(h_{n−1} < t − ε)`: the violation weight read with
`H`'s previous-day price. Day `0` reads `h_0` (natural subtraction `0 − 1 = 0`); the convention
affects one day and no limit.
Source: [[fa-positive-results-corrected-v3]] §1 (A1) remark 3, §6 (iii); root-fa-023; [[fa-adaptive-joint-mandate]] § T7 (i)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def staleViol (h a : ℕ → ℝ) (t ε δ : ℚ) (n : ℕ) : ℝ :=
  dsWeight (t : ℝ) (ε : ℝ) δ (a n) (h (n - 1))

/-- The stale gate is the same-day gate of the shifted sequence.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem staleViol_eq_viol_shift (h a : ℕ → ℝ) (t ε δ : ℚ) :
    staleViol h a t ε δ = viol (fun n => h (n - 1)) a t ε δ := rfl

/-- **The cheaper (c)**: the stale gate is legible on `A`'s market — `A` reads `H`'s *previous*-day
price, which under an alternating protocol is settled data ([[delay-program]] §1's axis table),
unlike the same-day price that `hjoint` requires. One-way in direction (`A` reads `H`), stated as
a definition of the hypothesis shape, not proved (no two-market inhabitant of `LegibleOn` is
known, `fa-forcing-trader` T11).
Source: [[delay-program]] §1; [[joint-clearing-and-trader-class]] §5; [[fa-adaptive-joint-mandate]] § T7 (i)
Kind: D
Fidelity: variant: the one-way ledger reading rendered as `LegibleOn A` of the stale gate
Hyps: n/a -/
def StaleLegible (A : History) (h a : ℕ → ℝ) (t ε δ : ℚ) : Prop :=
  LegibleOn A (staleViol h a t ε δ)

/-! ## B. (ii) What alternation costs -/

/-- **T7 (ii) — the stale gate fires off the violation and misses it**: with `a ≡ 1` and
`h = 0, 1, 0, 1, …`, `t = ½`, `ε = ¼`, `δ = ⅛`: on every odd day the stale gate is `1` while the
same-day gate is `0` (the stale gate fires, but the purchase price `h_n = 1 ≥ t` — the bound
`h_n < t − ε` fails), and on every even day `≥ 2` the same-day gate is `1` while the stale gate is
`0` (a violation the stale gate misses). Both gates have divergent mass. So the `A`-side engine
on the stale gate (`quote_unbiased` applies: generability is all it needs) says nothing about
same-day violation.
Source: [[fa-positive-results-corrected-v3]] §6 (iii); root-fa-023; lean-deference-059; [[fa-adaptive-joint-mandate]] § T7 (ii)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem stale_gate_fires_off_violation :
    ∃ (a h : ℕ → ℝ) (t ε δ : ℚ), 0 < ε ∧ 0 < δ ∧ (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ n, h n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ j, viol h a t ε δ (2 * j + 1) = 0 ∧ staleViol h a t ε δ (2 * j + 1) = 1) ∧
      (∀ j, viol h a t ε δ (2 * j + 2) = 1 ∧ staleViol h a t ε δ (2 * j + 2) = 0) ∧
      ¬ Summable (staleViol h a t ε δ) ∧ ¬ Summable (viol h a t ε δ) := by
  refine ⟨fun _ => 1, fun n => if n % 2 = 0 then 0 else 1, 1 / 2, 1 / 4, 1 / 8, by norm_num,
    by norm_num, fun n => by norm_num,
    fun n => by
      show (if n % 2 = 0 then (0 : ℝ) else 1) ∈ Set.Icc 0 1
      split_ifs <;> norm_num,
    ?_, ?_, ?_, ?_⟩
  · intro j
    constructor
    · show dsWeight _ _ _ 1 (if (2 * j + 1) % 2 = 0 then 0 else 1) = 0
      rw [if_neg (by omega), dsWeight,
        ctsInd_eq_zero_of_le (1 / 8 : ℚ) (((1 / 2 : ℚ) : ℝ) - ((1 / 4 : ℚ) : ℝ)) (1 : ℝ)
          (by norm_num) (by norm_num), mul_zero]
    · show dsWeight _ _ _ 1 (if (2 * j + 1 - 1) % 2 = 0 then 0 else 1) = 1
      rw [if_pos (by omega)]
      exact dsWeight_eq_one (by norm_num) (by norm_num) (by norm_num)
  · intro j
    constructor
    · show dsWeight _ _ _ 1 (if (2 * j + 2) % 2 = 0 then 0 else 1) = 1
      rw [if_pos (by omega)]
      exact dsWeight_eq_one (by norm_num) (by norm_num) (by norm_num)
    · show dsWeight _ _ _ 1 (if (2 * j + 2 - 1) % 2 = 0 then 0 else 1) = 0
      rw [if_neg (by omega), dsWeight,
        ctsInd_eq_zero_of_le (1 / 8 : ℚ) (((1 / 2 : ℚ) : ℝ) - ((1 / 4 : ℚ) : ℝ)) (1 : ℝ)
          (by norm_num) (by norm_num), mul_zero]
  · intro hs
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hs.tendsto_atTop_zero (1 / 2) (by norm_num)
    have h1 := hN (2 * N + 1) (by omega)
    have hval : staleViol (fun n => if n % 2 = 0 then (0 : ℝ) else 1) (fun _ => 1)
        (1 / 2) (1 / 4) (1 / 8) (2 * N + 1) = 1 := by
      show dsWeight _ _ _ 1 (if (2 * N + 1 - 1) % 2 = 0 then 0 else 1) = 1
      rw [if_pos (by omega)]
      exact dsWeight_eq_one (by norm_num) (by norm_num) (by norm_num)
    rw [hval, Real.dist_eq] at h1
    norm_num at h1
  · intro hs
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hs.tendsto_atTop_zero (1 / 2) (by norm_num)
    have h1 := hN (2 * N + 2) (by omega)
    have hval : viol (fun n => if n % 2 = 0 then (0 : ℝ) else 1) (fun _ => 1)
        (1 / 2) (1 / 4) (1 / 8) (2 * N + 2) = 1 := by
      show dsWeight _ _ _ 1 (if (2 * N + 2) % 2 = 0 then 0 else 1) = 1
      rw [if_pos (by omega)]
      exact dsWeight_eq_one (by norm_num) (by norm_num) (by norm_num)
    rw [hval, Real.dist_eq] at h1
    norm_num at h1

/-! ## C. (iii) The positive transfer -/

/-- **One gate bounds the other at half the margin when the two `h`-readings differ by at most
`ε/4`**: `dsWeight t ε δ a y ≤ dsWeight t (ε/2) δ a x / min 1 (ε/(4δ))` whenever `x ≤ y + ε/4`.
(If the `ε`-gate at `y` is positive then `y < t − ε`, so `x < t − 3ε/4` and the `ε/2`-ramp at `x`
is at least `min 1 (ε/(4δ))`.)
Source: [[fa-adaptive-joint-mandate]] § T7 (iii) ("`staleViol ≤ viol(ε/2) + o(1)`-style domination")
Kind: P
Fidelity: exact
Hyps: (a) `hε`, `hδ`, `hxy` -/
theorem dsWeight_le_shift {t ε : ℝ} (hε : 0 < ε) {δ : ℚ} (hδ : 0 < δ) {a x y : ℝ}
    (hxy : x ≤ y + ε / 4) :
    dsWeight t ε δ a y ≤ dsWeight t (ε / 2) δ a x / min 1 (ε / (4 * δ)) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hm : 0 < min 1 (ε / (4 * δ)) := lt_min one_pos (by positivity)
  have hA := ctsInd_mem_Icc δ a t
  unfold dsWeight
  rcases (ctsInd_mem_Icc δ (t - ε) y).1.lt_or_eq with hB | hB
  · have hy : y < t - ε := ctsInd_pos_imp hδ hB
    have hB' : min 1 (ε / (4 * δ)) ≤ ctsInd δ (t - ε / 2) x := by
      unfold ctsInd
      refine min_le_min le_rfl ?_
      refine le_max_of_le_right ?_
      rw [div_le_div_iff₀ (by positivity) hδR]
      nlinarith
    have hB1 : ctsInd δ (t - ε) y ≤ 1 := (ctsInd_mem_Icc _ _ _).2
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hA.1
    rw [le_div_iff₀ hm]
    calc ctsInd δ (t - ε) y * min 1 (ε / (4 * δ)) ≤ 1 * min 1 (ε / (4 * δ)) :=
          mul_le_mul_of_nonneg_right hB1 hm.le
      _ = min 1 (ε / (4 * δ)) := one_mul _
      _ ≤ ctsInd δ (t - ε / 2) x := hB'
  · rw [← hB, mul_zero]
    exact div_nonneg (mul_nonneg hA.1 (ctsInd_mem_Icc _ _ _).1) hm.le

/-- **Transfer, stale → same-day**: if `h` moves by at most `ε/4` per day (eventually) and the
stale gate at margin `ε/2` vanishes, the same-day gate at margin `ε` vanishes.
Source: [[fa-adaptive-joint-mandate]] § T7 (iii)
Kind: C
Fidelity: exact
Hyps: (a) `hε`, `hδ`; (c) `hjump` ("no one-day jumps") -/
theorem viol_tendsto_of_stale {h a : ℕ → ℝ} {t ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ)
    (hjump : ∀ᶠ n in atTop, h (n - 1) ≤ h n + (ε : ℝ) / 4)
    (hst : Tendsto (staleViol h a t (ε / 2) δ) atTop (𝓝 0)) :
    Tendsto (viol h a t ε δ) atTop (𝓝 0) := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hm : 0 < min 1 ((ε : ℝ) / (4 * δ)) := lt_min one_pos (by positivity)
  have hlim : Tendsto (fun n => staleViol h a t (ε / 2) δ n / min 1 ((ε : ℝ) / (4 * δ)))
      atTop (𝓝 0) := by
    simpa using hst.div_const (min 1 ((ε : ℝ) / (4 * δ)))
  refine squeeze_zero' (Eventually.of_forall (fun n => dsWeight_nonneg _ _ _ _ _)) ?_ hlim
  filter_upwards [hjump] with n hn
  have := dsWeight_le_shift (t := (t : ℝ)) hεR hδ (a := a n) hn
  simpa [viol, staleViol] using this

/-- **Transfer, same-day → stale** (the mirror).
Source: [[fa-adaptive-joint-mandate]] § T7 (iii)
Kind: C
Fidelity: exact
Hyps: (a) `hε`, `hδ`; (c) `hjump` -/
theorem staleViol_tendsto_of_viol {h a : ℕ → ℝ} {t ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ)
    (hjump : ∀ᶠ n in atTop, h n ≤ h (n - 1) + (ε : ℝ) / 4)
    (hv : Tendsto (viol h a t (ε / 2) δ) atTop (𝓝 0)) :
    Tendsto (staleViol h a t ε δ) atTop (𝓝 0) := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hm : 0 < min 1 ((ε : ℝ) / (4 * δ)) := lt_min one_pos (by positivity)
  have hlim : Tendsto (fun n => viol h a t (ε / 2) δ n / min 1 ((ε : ℝ) / (4 * δ)))
      atTop (𝓝 0) := by
    simpa using hv.div_const (min 1 ((ε : ℝ) / (4 * δ)))
  refine squeeze_zero' (Eventually.of_forall (fun n => dsWeight_nonneg _ _ _ _ _)) ?_ hlim
  filter_upwards [hjump] with n hn
  have := dsWeight_le_shift (t := (t : ℝ)) hεR hδ (a := a n) hn
  simpa [viol, staleViol] using this

/-- **T7 (iii) — Theorem 2 for the stale gate under "no one-day jumps on the gate"** (two-way,
bridge as a hypothesis): if the stale gate is jointly legible (the cheaper (c) on `A`, and on `H`,
which has both readings) and on its support `h_n ≤ h_{n−1} + ε/2`, then the stale gate tends to
`0`. The instance `g = staleViol`, `c = ε/2` of `v3Theorem2_gate_of_bridge`: on the support
`a_n > t` and `h_{n−1} < t − ε`, so `a_n − h_n > ε/2`.
Scope: two-way (partial: over the OPEN pair). Grade: as T3.
Source: [[fa-positive-results-corrected-v3]] §6 (iii); [[fa-adaptive-joint-mandate]] § T7 (iii)
Kind: C
Fidelity: variant: the stale gate in place of the same-day gate, under the no-jump (c)
Hyps: (a) `hcode`, `hworldA`, `hworldH`, `hval`, `hε`, `hδ`; (c) `pkg.reflected`; (c) `hjoint` (stale joint legibility); (c) `hjump` (no one-day jumps on the gate); `hbridge` (T4, OPEN). -/
theorem v3Theorem2_stale_of_noJumps_of_bridge {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ) (hε : 0 < ε)
    (hjump : ∀ n, 0 < staleViol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ n →
      (X n).expect H n ≤ (X (n - 1)).expect H (n - 1) + (ε : ℝ) / 2)
    (hjoint : LegibleOn A (staleViol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) ∧
      LegibleOn H (staleViol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ))
    (hbridge : AdaptiveBridgeHolds H f X) :
    Tendsto (staleViol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) atTop (𝓝 0) := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  refine v3Theorem2_gate_of_bridge pkg hcode hworldA hworldH hval
    (g := staleViol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ)
    (fun n => ⟨dsWeight_nonneg _ _ _ _ _, dsWeight_le_one _ _ _ _ _⟩)
    (c := (ε : ℝ) / 2) (half_pos hεR) (fun n hn => ?_) hjoint hbridge
  have hpos : 0 < dsWeight (t : ℝ) (ε : ℝ) δ (quoteSeq Y A n) ((X (n - 1)).expect H (n - 1)) := hn
  obtain ⟨hta, hht⟩ := dsWeight_pos_imp hδ hpos
  have := hjump n hn
  linarith

/-- **T7 (iii) — the transfer to the alternating pair's same-day gate**: under no-jumps on the
stale gate (for Theorem 2) and no-jumps eventually (for the transfer), the same-day violation
weight at margin `2ε` tends to `0`.
Scope: two-way (partial: over the OPEN pair).
Source: [[fa-adaptive-joint-mandate]] § T7 (iii) ("Theorem 2 transfers to the alternating pair")
Kind: C
Fidelity: variant: margin `2ε` on the same-day gate
Hyps: as `v3Theorem2_stale_of_noJumps_of_bridge`, plus (c) `hjump'`. -/
theorem v3Theorem2_alternating_transfer {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ) (hε : 0 < ε)
    (hjump : ∀ n, 0 < staleViol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ n →
      (X n).expect H n ≤ (X (n - 1)).expect H (n - 1) + (ε : ℝ) / 2)
    (hjump' : ∀ᶠ n in atTop, (X (n - 1)).expect H (n - 1) ≤ (X n).expect H n + (ε : ℝ) / 2)
    (hjoint : LegibleOn A (staleViol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) ∧
      LegibleOn H (staleViol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ))
    (hbridge : AdaptiveBridgeHolds H f X) :
    Tendsto (viol (fun n => (X n).expect H n) (quoteSeq Y A) t (2 * ε) δ) atTop (𝓝 0) := by
  have hst := v3Theorem2_stale_of_noJumps_of_bridge pkg hcode hworldA hworldH hval t ε hδ hε
    hjump hjoint hbridge
  refine viol_tendsto_of_stale (by positivity) hδ ?_ ?_
  · filter_upwards [hjump'] with n hn
    push_cast
    linarith
  · have : (2 * ε / 2 : ℚ) = ε := by ring
    rw [this]
    exact hst

/-! ## D. The OPEN row of record: strict alternation -/

/-- **The alternating pair** (the carrier of the OPEN row): two inductors with a quote package,
where `A` can read `H`'s *previous*-day expectation (the stale gate is legible on `A`, every
rational triple) and `H` can read `A`'s same-day quote (both gates legible on `H`). No existence
is claimed (the construction is `li-coupled-pair`'s, OPEN there); the structure bundles what the
statement needs.
Source: [[fa-adaptive-joint-mandate]] § T7 (iii) (`AlternatingPair`); [[joint-clearing-and-trader-class]] §5
Kind: D
Fidelity: variant: a `TwoWayPair`-shaped hypothesis package over abstract histories (no ledger construction)
Hyps: n/a -/
structure AlternatingPair (H A : History) (DPA DPH : DeductiveProcess) (f : DeferralFunction)
    (X Y : ℕ → LUV) : Prop where
  pkg : CrossQuotePackage H DPA f X Y
  hcode : LUV.MachineThresholdCodeSeq X
  hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)
  hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)
  hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x
  /-- `A` reads `H`'s previous-day expectation: the stale gate is legible on `A`. -/
  staleA : ∀ t ε δ : ℚ, 0 < ε → 0 < δ →
    LegibleOn A (staleViol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ)
  /-- `H` reads `A`'s same-day quote and its own prices: the stale gate is legible on `H`. -/
  staleH : ∀ t ε δ : ℚ, 0 < ε → 0 < δ →
    LegibleOn H (staleViol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ)
  /-- … and so is the same-day gate. -/
  sameH : ∀ t ε δ : ℚ, 0 < ε → 0 < δ →
    LegibleOn H (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ)

/-- **OPEN (T7, the row of record): Theorem 2 for the alternating pair without the no-jumps
hypothesis.** For an `AlternatingPair` (and `[IsLogicalInductor]` on both sides), **given the
`H`-side bridge** `hbridge` (T4's conclusion, as every T3-shaped row takes it — so the row isolates
the alternation question from T4; repair round 1, audit r1 adversarial N3), does the *same-day*
violation weight tend to `0`? Neither a proof nor a counterexample is known: a proof would need an
`A`-side engine on a gate `A` cannot carry (the same-day gate), or a transfer from the stale gate
without the jump bound; a counterexample needs an inductor pair with `Θ(1)` one-day moves on the
gate infinitely often (lean-deference-059's "a counterexample is M" is about the real-sequence
half, `stale_gate_fires_off_violation`, not the inductor half). Listed in
`fa-adaptive-joint-open.txt`.
Scope: two-way (partial: over the OPEN pair).
Source: [[fa-positive-results-corrected-v3]] §6 (iii); root-fa-023; lean-deference-059; [[fa-adaptive-joint-mandate]] § T7 (iii)
Kind: OPEN
Fidelity: exact
Hyps: (c) `P` (the alternating pair, including `pkg.reflected` and the stale/same-day legibilities); `hbridge` (T4, OPEN). -/
theorem v3Theorem2_strictAlternation {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (P : AlternatingPair H A DPA DPH f X Y) (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ) (hε : 0 < ε)
    (hbridge : AdaptiveBridgeHolds H f X) :
    Tendsto (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) atTop (𝓝 0) := by
  sorry

end Cleanroom.Fa.FaAdaptiveJoint
