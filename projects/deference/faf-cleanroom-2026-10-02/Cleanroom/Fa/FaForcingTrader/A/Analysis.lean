import Cleanroom.Fa.FaForcingTrader.A.Violation
import Cleanroom.Found.LiAsympCalc.Spikes
import Mathlib.Analysis.PSeries

/-!
# `fa-forcing-trader` · angle A · Analysis: cross-price fidelity (T9) and the schedule equivalence (T10)

**T9.** Real-sequence facts with no FAF content, recorded because they fix hypotheses elsewhere:
(i) a signed average can vanish while the absolute average does not (lean-deference-2-011's
elementary core); (ii) **new**: on a slowly-massing gate `u_k = 1/(k+1)` a per-day mismatch
`η_k = 1/(⌊√(k+1)⌋+1) → 0` has `∑ η` *not* `o(∑ u)` — so the (R2) approximant route
(li-quote-lane's `ledgerRamp_tracks`, a per-day `o(1)`) cannot replace (L) in T6 by the donor
rule, and any statement that silently swaps `𝔼^H_n(α_n)` for `a_n` inside a scheduled average is a
(c). (iii) (prose, findings): FAF's `lic_provability_induction` needs a sequence of *theorems*,
and `PGenerableWeighting` reads only the market's own prices.

**T10.** Over real sequences `w ∈ [0,1]^ℕ`: "finite on every window-disjoint schedule" **implies**
`w_n → 0` (the greedy schedule through the days with `w_n ≥ θ`, root-fa-2-003 (ii)); the
**converse is false** (`w_n = 1/(n+1)`, `d_k = 2k`: finding F-A3 — the mandate's and
root-fa-2-003's "⟺" is wrong in the ⇐ direction). The gap of record: the greedy schedule is not a
`DeferralFunction` in general (lean-deference-2-010), so T3 over all `DeferralFunction` schedules
does not yield `w_n → 0`; what it yields is the one-sided corollary under `ChasingSchedule` — the
(c) `fa-adaptive-joint` must discharge — and from it v3's Corollary 2 (`Dominates`) through
li-asymp-calc's compactness lemma.
-/

namespace Cleanroom.Fa.FaForcingTrader.A

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Cleanroom.Fa.FaForcingTrader
  Filter Topology

/-! ## A. T9 (i): signed averages do not buy absolute fidelity -/

/-- The alternating sign sequence `+1, −1, +1, …`.
Source: lean-deference-2-011 (b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def altSign (k : ℕ) : ℝ := if k % 2 = 0 then 1 else -1

/-- Its partial sums are `0` or `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem altSign_sum : ∀ N, ∑ i ∈ Finset.range N, altSign i = if N % 2 = 0 then 0 else 1
  | 0 => by simp
  | 1 => by simp [altSign]
  | N + 2 => by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, altSign_sum N]
      unfold altSign
      rcases Nat.mod_two_eq_zero_or_one N with h | h
      · have h1 : (N + 1) % 2 = 1 := by omega
        have h2 : (N + 2) % 2 = 0 := by omega
        simp [h, h1, h2]
      · have h1 : (N + 1) % 2 = 0 := by omega
        have h2 : (N + 2) % 2 = 1 := by omega
        simp [h, h1, h2]

/-- **T9 (i).** A `[−1,1]`-valued error whose Cesàro mean tends to `0` while the Cesàro mean of
its absolute value does not: signed unbiasedness says nothing about absolute fidelity.
Source: lean-deference-2-011 (b) (the elementary core); root-fa-017
Kind: N+
Fidelity: exact
Hyps: n/a -/
theorem signed_average_not_absolute :
    (∀ k, |altSign k| ≤ 1) ∧ Tendsto (cesaro altSign) atTop (𝓝 0) ∧
      ¬ Tendsto (cesaro (fun k => |altSign k|)) atTop (𝓝 0) := by
  have habs : ∀ k, |altSign k| = 1 := fun k => by
    unfold altSign
    split_ifs <;> simp
  refine ⟨fun k => (habs k).le, ?_, ?_⟩
  · have hbound : ∀ N : ℕ, |cesaro altSign N| ≤ 1 / (N : ℝ) := fun N => by
      unfold cesaro
      rw [altSign_sum N, abs_div, Nat.abs_cast]
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
        rw [div_le_div_iff_of_pos_right hNpos]
        split_ifs <;> simp
    refine squeeze_zero_norm' (Eventually.of_forall (fun N => ?_))
      tendsto_one_div_atTop_nhds_zero_nat
    rw [Real.norm_eq_abs]
    exact hbound N
  · intro h
    have hone : ∀ᶠ N in atTop, cesaro (fun k => |altSign k|) N = 1 := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      unfold cesaro
      simp only [habs, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      have hNpos : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      exact div_self hNpos
    have h1 : Tendsto (cesaro (fun k => |altSign k|)) atTop (𝓝 1) :=
      tendsto_const_nhds.congr' (hone.mono (fun N hN => hN.symm))
    have := tendsto_nhds_unique h h1
    norm_num at this

/-! ## B. T9 (ii): a per-day `o(1)` mismatch is not `o(W_n)` on a slowly-massing gate -/

/-- The harmonic gate `u_k = 1/(k+1)` (read as the gate's value on the `k`-th scheduled day; the
schedule reindexing changes no sum).
Source: mandate T9 (ii) ("take `u_{d_k} = 1/k`")
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def harmonicGate (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

/-- The per-day mismatch `η_k = 1/(⌊√(k+1)⌋ + 1)`, which tends to `0`.
Source: mandate T9 (ii) ("mismatch `1/√k`")
Kind: D
Fidelity: variant: integer square root (no `Real.sqrt`), same rate
Hyps: n/a -/
noncomputable def sqrtMismatch (k : ℕ) : ℝ := 1 / ((Nat.sqrt (k + 1) : ℝ) + 1)

/-- Off day `0`, the gate is below the mismatch (`⌊√(k+1)⌋ ≤ k` for `k ≥ 1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem harmonicGate_le_sqrtMismatch {k : ℕ} (hk : 1 ≤ k) : harmonicGate k ≤ sqrtMismatch k := by
  unfold harmonicGate sqrtMismatch
  have hs : Nat.sqrt (k + 1) ≤ k := by
    have := Nat.sqrt_lt_self (show 1 < k + 1 by omega)
    omega
  have hsR : (Nat.sqrt (k + 1) : ℝ) ≤ k := by exact_mod_cast hs
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- The gate's mass is at most the mismatch's mass plus `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem prefixSum_harmonicGate_le (n : ℕ) :
    prefixSum harmonicGate n ≤ prefixSum sqrtMismatch n + 1 := by
  unfold prefixSum
  rw [Finset.sum_range_succ', Finset.sum_range_succ' sqrtMismatch]
  have h0 : harmonicGate 0 = 1 := by simp [harmonicGate]
  have hsm0 : 0 ≤ sqrtMismatch 0 := by unfold sqrtMismatch; positivity
  have hle : ∑ i ∈ Finset.range n, harmonicGate (i + 1) ≤
      ∑ i ∈ Finset.range n, sqrtMismatch (i + 1) :=
    Finset.sum_le_sum (fun i _ => harmonicGate_le_sqrtMismatch (by omega))
  linarith

/-- **T9 (ii) (headline witness).** A `[0,1]`-valued gate `u` with divergent mass and a
nonnegative per-day mismatch `η → 0` such that `∑_{i≤n} η_i / ∑_{i≤n} u_i` does **not** tend to
`0` (it is eventually `≥ 1/2`). Hence a per-day `o(1)` approximant error — li-quote-lane's
`ledgerRamp_tracks`, the (R2) device — cannot be washed out of a scheduled average by the donor
rule when the gate's mass grows slowly (as it does on a sparse schedule), and (L) stays a
hypothesis in T6.
Source: lean-deference-2-011 (b); root-fa-017; vq-wiki-048 (d); mandate T9 (ii) (new)
Kind: N+
Fidelity: exact (the mandate's `1/√k` as `1/(⌊√(k+1)⌋+1)`)
Hyps: n/a -/
theorem approximant_mismatch_not_small :
    (∀ k, harmonicGate k ∈ Set.Icc (0 : ℝ) 1) ∧ Tendsto (prefixSum harmonicGate) atTop atTop ∧
      (∀ k, 0 ≤ sqrtMismatch k) ∧ Tendsto sqrtMismatch atTop (𝓝 0) ∧
      ¬ Tendsto (fun n => prefixSum sqrtMismatch n / prefixSum harmonicGate n) atTop (𝓝 0) := by
  have hu01 : ∀ k, harmonicGate k ∈ Set.Icc (0 : ℝ) 1 := fun k => by
    unfold harmonicGate
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hudiv : Tendsto (prefixSum harmonicGate) atTop atTop := by
    have := Real.tendsto_sum_range_one_div_nat_succ_atTop.comp (tendsto_add_atTop_nat 1)
    exact this
  have hη0 : ∀ k, 0 ≤ sqrtMismatch k := fun k => by unfold sqrtMismatch; positivity
  have hηlim : Tendsto sqrtMismatch atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (Nat.sqrt (k + 1) : ℝ) + 1) atTop atTop :=
      (tendsto_natCast_atTop_atTop.comp (tendsto_natSqrt_atTop.comp (tendsto_add_atTop_nat 1))).atTop_add
        tendsto_const_nhds
    have := h1.inv_tendsto_atTop
    refine this.congr (fun k => ?_)
    simp [sqrtMismatch, one_div]
  refine ⟨hu01, hudiv, hη0, hηlim, ?_⟩
  intro hlim
  have hηdiv : Tendsto (prefixSum sqrtMismatch) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) (hudiv.atTop_add (tendsto_const_nhds (x := (-1 : ℝ))))
    linarith [prefixSum_harmonicGate_le n]
  have hev1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ prefixSum sqrtMismatch n :=
    hηdiv.eventually (eventually_ge_atTop 1)
  have hev2 : ∀ᶠ n in atTop, 0 < prefixSum harmonicGate n :=
    hudiv.eventually (eventually_gt_atTop 0)
  have hsmall := (Metric.tendsto_nhds.1 hlim) (1 / 2) (by norm_num)
  obtain ⟨n, h1, h2, h3⟩ := (hev1.and (hev2.and hsmall)).exists
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (prefixSum_nonneg hη0 n) h2.le),
    div_lt_iff₀ h2] at h3
  linarith [prefixSum_harmonicGate_le n]

/-! ## C. T10: finite on every window-disjoint schedule ⟹ `w_n → 0`, and the converse fails -/

/-- Divergence of the mass from recurrent weight `≥ θ > 0` (fa-theorem-a's
`tendsto_prefixSum_atTop_of_frequently_one`, rescaled).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem tendsto_prefixSum_atTop_of_frequently_ge {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) {θ : ℝ}
    (hθ : 0 < θ) (hfreq : ∃ᶠ n in atTop, θ ≤ w n) : Tendsto (prefixSum w) atTop atTop := by
  have h1 : ∃ᶠ n in atTop, 1 ≤ w n / θ := hfreq.mono (fun n hn => by
    rw [le_div_iff₀ hθ, one_mul]
    exact hn)
  have h2 := tendsto_prefixSum_atTop_of_frequently_one (fun i => div_nonneg (hw i) hθ.le) h1
  have h3 : prefixSum (fun n => w n / θ) = fun n => prefixSum w n / θ := by
    funext n
    simp [prefixSum, Finset.sum_div]
  rw [h3] at h2
  refine (h2.const_mul_atTop hθ).congr (fun n => ?_)
  field_simp

/-- **T10 (⟹). Finite on every window-disjoint schedule forces `w_n → 0`** (real sequences, any
lookahead `f` with `f n > n`): if `w_n ≥ θ` infinitely often, the greedy schedule — the first
such day, then the first such day beyond the previous window — is strictly increasing,
window-disjoint, and carries weight `≥ θ` at every step, so it is not summable.
Source: root-fa-2-003 (ii) (the greedy lemma); [[fa-positive-results-corrected-v3]] §4
Kind: P
Fidelity: exact (this direction)
Hyps: (a) none -/
theorem tendsto_zero_of_summable_on_windowDisjoint {f : ℕ → ℕ} (hf : ∀ n, n < f n) {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n)
    (h : ∀ d : ℕ → ℕ, StrictMono d → (∀ k, f (d k) < d (k + 1)) → Summable (fun k => w (d k))) :
    Tendsto w atTop (𝓝 0) := by
  classical
  by_contra hnot
  have hfreq : ∃ θ : ℝ, 0 < θ ∧ ∃ᶠ n in atTop, θ ≤ w n := by
    rw [Metric.tendsto_nhds] at hnot
    push_neg at hnot
    obtain ⟨θ, hθ, hθ'⟩ := hnot
    refine ⟨θ, hθ, hθ'.mono (fun n hn => ?_)⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hw0 n)] at hn
    exact hn
  obtain ⟨θ, hθ, hfr⟩ := hfreq
  have hnext : ∀ m : ℕ, ∃ n, m < n ∧ θ ≤ w n := fun m => by
    obtain ⟨n, hn, hwn⟩ := (frequently_atTop.1 hfr) (m + 1)
    exact ⟨n, by omega, hwn⟩
  let d : ℕ → ℕ := fun k =>
    Nat.rec (Nat.find (hnext 0)) (fun _ prev => Nat.find (hnext (f prev))) k
  have hd0 : d 0 = Nat.find (hnext 0) := rfl
  have hdsucc : ∀ k, d (k + 1) = Nat.find (hnext (f (d k))) := fun k => rfl
  have hdw : ∀ k, θ ≤ w (d k) := by
    intro k
    cases k with
    | zero => rw [hd0]; exact (Nat.find_spec (hnext 0)).2
    | succ k => rw [hdsucc]; exact (Nat.find_spec (hnext (f (d k)))).2
  have hdgap : ∀ k, f (d k) < d (k + 1) := fun k => by
    rw [hdsucc]
    exact (Nat.find_spec (hnext (f (d k)))).1
  have hmono : StrictMono d := strictMono_nat_of_lt_succ (fun k => lt_trans (hf (d k)) (hdgap k))
  have hlim := (h d hmono hdgap).tendsto_atTop_zero
  obtain ⟨k, hk⟩ := ((Metric.tendsto_nhds.1 hlim) θ hθ).exists
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hw0 _)] at hk
  linarith [hdw k]

/-- **T10 (⟸ refuted).** `w_n → 0` does **not** make `w` summable on every window-disjoint
schedule: `w_n = 1/(n+1)` tends to `0`, `d_k = 2k` is strictly increasing with gaps `2` (window-
disjoint for the successor lookahead), and `∑_k 1/(2k+1) = ∞`. The mandate's T10 and
root-fa-2-003 (ii) state an equivalence; only the ⟹ direction holds (findings F-A3).
Source: root-fa-2-003 (ii) (refuted in the ⇐ direction); mandate T10
Kind: N+
Fidelity: n/a (refutation of the stated converse)
Hyps: n/a -/
theorem not_summable_on_windowDisjoint_of_tendsto_zero :
    ∃ w : ℕ → ℝ, (∀ n, w n ∈ Set.Icc (0 : ℝ) 1) ∧ Tendsto w atTop (𝓝 0) ∧
      ∃ d : ℕ → ℕ, StrictMono d ∧ (∀ k, d k + 1 < d (k + 1)) ∧ ¬ Summable (fun k => w (d k)) := by
  refine ⟨harmonicGate, approximant_mismatch_not_small.1, ?_, fun k => 2 * k, ?_, ?_, ?_⟩
  · have h1 : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    refine h1.inv_tendsto_atTop.congr (fun k => ?_)
    simp [harmonicGate, one_div]
  · exact strictMono_nat_of_lt_succ (fun k => by
      show 2 * k < 2 * (k + 1)
      omega)
  · intro k
    show 2 * k + 1 < 2 * (k + 1)
    omega
  · intro hs
    have hs2 : Summable (fun k : ℕ => (2 : ℝ) * (1 / ((2 * (k : ℝ)) + 1))) := by
      refine (hs.mul_left 2).congr (fun k => ?_)
      simp only [harmonicGate]
      push_cast
      ring
    have hs1 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs2
      calc (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((2 * (k : ℝ) + 1) / 2) :=
            one_div_le_one_div_of_le (by positivity) (by linarith)
        _ = 2 * (1 / (2 * (k : ℝ) + 1)) := by rw [one_div_div, mul_one_div]
    have hs1' : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) :=
      hs1.congr (fun k => by push_cast; rfl)
    exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 hs1')

/-- **The chasing hypothesis** (the (c) `fa-adaptive-joint` must discharge): whenever the
schedule-free weight `w` is `≥ θ` infinitely often, some window-disjoint `DeferralFunction`
passes through infinitely many such days. The greedy schedule of
`tendsto_zero_of_summable_on_windowDisjoint` witnesses it over real sequences; it is a
`DeferralFunction` only when the days with `w_n ≥ θ` are decidable in polynomial time
(lean-deference-2-010: computing `d_k` costs `R(d_k)`), which is exactly the gap between T3 and
the box.
Source: lean-deference-2-010; root-fa-2-003 (ii) readings (α)/(β); root-fa-005 (the box); root-fa-020 ((A4))
Kind: D
Fidelity: exact (the gap of record, named)
Hyps: n/a -/
def ChasingSchedule (f : DeferralFunction) (w : ℕ → ℝ) : Prop :=
  ∀ θ : ℝ, 0 < θ → (∃ᶠ n in atTop, θ ≤ w n) →
    ∃ d : DeferralFunction, WindowDisjoint f d ∧ ∃ᶠ k in atTop, θ ≤ w (d.f k)

/-- Under chasing, finiteness of the scheduled mass on every window-disjoint `DeferralFunction`
forces the schedule-free weight to `0`.
Source: root-fa-2-003 (ii); mandate T10
Kind: C
Fidelity: exact
Hyps: (a) none (`hch` is the named (c) of the consumer) -/
theorem tendsto_zero_of_chasing {f : DeferralFunction} {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n)
    (hch : ChasingSchedule f w)
    (hfin : ∀ d : DeferralFunction, WindowDisjoint f d →
      ¬ Tendsto (prefixSum (fun n => schedInd d n * w n)) atTop atTop) :
    Tendsto w atTop (𝓝 0) := by
  by_contra hnot
  have hfreq : ∃ θ : ℝ, 0 < θ ∧ ∃ᶠ n in atTop, θ ≤ w n := by
    rw [Metric.tendsto_nhds] at hnot
    push_neg at hnot
    obtain ⟨θ, hθ, hθ'⟩ := hnot
    refine ⟨θ, hθ, hθ'.mono (fun n hn => ?_)⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hw0 n)] at hn
    exact hn
  obtain ⟨θ, hθ, hfr⟩ := hfreq
  obtain ⟨d, hwd, hfrk⟩ := hch θ hθ hfr
  refine hfin d hwd (tendsto_prefixSum_atTop_of_frequently_ge
    (fun n => mul_nonneg (schedInd_mem_Icc d n).1 (hw0 n)) hθ ?_)
  rw [frequently_atTop]
  intro a
  obtain ⟨k, hk, hwk⟩ := (frequently_atTop.1 hfrk) a
  refine ⟨d.f k, le_trans hk (d.lt k).le, ?_⟩
  rw [schedInd_of_mem, one_mul]
  exact hwk

/-- **T10, the FAF corollary.** If v3 Theorem 1's joint legibility holds on every window-disjoint
`DeferralFunction` schedule and the violation days can be chased (`ChasingSchedule`), then the
schedule-free violation weight `Ind_δ(a_n > t) · Ind_δ(h_n < t − ε)` tends to `0`. The second
hypothesis is exactly the (c) `fa-adaptive-joint` must discharge ((A4)); without it, T3 over all
`DeferralFunction` schedules says nothing about `w_n → 0` (lean-deference-2-010).
Scope: two-way (partial: over the OPEN pair, and under chasing). e.d. family.
Source: root-fa-005 (the box, recovered only under (A4)); root-fa-2-003 (ii); lean-deference-2-010; mandate T10
Kind: C
Fidelity: variant: conditional on `ChasingSchedule` (the e.c.-level gap named, not closed)
Hyps: (c) `pkg.reflected`; (c) `hjointAll` (joint legibility on every schedule); (c) `hch` (chasing, (A4)). -/
theorem v3Theorem1_tendsto_zero_of_chasing {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ) (hε : 0 < ε)
    (hjointAll : ∀ d : DeferralFunction, WindowDisjoint f d →
      LegibleOn A (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ) ∧
        LegibleOn H (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ))
    (hch : ChasingSchedule f (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ)) :
    Tendsto (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) atTop (𝓝 0) :=
  tendsto_zero_of_chasing (fun n => dsWeight_nonneg _ _ _ _ _) hch (fun d hwd =>
    v3Theorem1_of_jointLegible pkg hcode hworldA hworldH hval hwd t ε hδ hε (hjointAll d hwd))

/-- **v3's Corollary 2 under chasing**: with joint legibility on every schedule and chasing for
every rational parameter triple, `H`'s credence dominates `A`'s quote
(`Dominates`: `∀ c > 0, ∀ᶠ n, a_n − c < h_n`) — li-asymp-calc's compactness lemma on the
schedule-free violation weights.
Scope: two-way (partial: over the OPEN pair, and under chasing).
Source: [[fa-positive-results-corrected-v3]] §5 Corollary 2; root-fa-005; li-asymp-calc `tendsto_viol_iff_dominates`
Kind: C
Fidelity: variant: conditional on `ChasingSchedule` for every `(t, ε, δ)`
Hyps: (c) `pkg.reflected`; (c) `hjointAll`; (c) `hch`. -/
theorem v3Corollary2_of_chasing {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (hjointAll : ∀ (t ε δ : ℚ) (d : DeferralFunction), WindowDisjoint f d →
      LegibleOn A (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ) ∧
        LegibleOn H (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ))
    (hch : ∀ t ε δ : ℚ, 0 < ε → 0 < δ →
      ChasingSchedule f (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ)) :
    Dominates (fun n => (X n).expect H n) (quoteSeq Y A) := by
  have ha : ∀ n, quoteSeq Y A n ∈ Set.Icc (0 : ℝ) 1 := fun n =>
    LUV.expect_mem_Icc A n (Y n) (fun s => IsLogicalInductor.price_mem_Icc (P := A) (DP := DPA) n s)
  exact (tendsto_viol_iff_dominates ha).1 (fun t ε δ hε hδ =>
    v3Theorem1_tendsto_zero_of_chasing pkg hcode hworldA hworldH hval t ε hδ hε
      (hjointAll t ε δ) (hch t ε δ hε hδ))

end Cleanroom.Fa.FaForcingTrader.A
