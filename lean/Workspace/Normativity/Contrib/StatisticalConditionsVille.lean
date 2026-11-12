/-
# Statistical conditions with random outcomes: a capital bound with a probability

Round `projects/normativity/rounds/2026-11-12-statistical-conditions/`.

No market.  A filtration, outcomes `x n ∈ [0, 1]` known at `n + 1` with conditional
expectation at least `c` given the past, stakes `mu n ≥ 0` known at `n`, and the per-day
ceiling `Q n + mu n (1 - c) ≤ U` on the settled account `Q n = ∑_{i < n} mu i (x i - c)`.

* `ville` — a nonnegative supermartingale `Y` reaches `a > 0` with probability at most
  `E[Y 0] / a`.
* `Betting.headroom_supermartingale` — `U - Q` is a nonnegative supermartingale.
* `Betting.account_bound` — `P(∃ n, Q n ≤ -K) ≤ U / (U + K)`.
* `Betting.ae_bounded_below` — almost surely the settled account is bounded below.
* `Betting.witness` — the hypotheses hold for a fair coin staked at `c = 1/2`.

Names are provisional (`AGENTS.md` standard 6).
-/

import Mathlib.Probability.Martingale.OptionalStopping
import Workspace.Normativity.Contrib.StatisticalConditions

namespace Workspace.Normativity.Contrib.StatisticalConditions

open MeasureTheory
open Workspace.Normativity.Contrib.ExactConditions
open scoped ENNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-- The maximal inequality through day `N`, by optional stopping at the first day the
process is at least `a`. -/
theorem ville_finite [IsFiniteMeasure μ] {Y : ℕ → Ω → ℝ} (hY : Supermartingale Y ℱ μ)
    (hnn : ∀ n ω, 0 ≤ Y n ω) {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    a * μ.real {ω | ∃ k, k ≤ N ∧ a ≤ Y k ω} ≤ ∫ ω, Y 0 ω ∂μ := by
  set τ : Ω → ℕ∞ := fun ω ↦ (hittingBtwn Y {y : ℝ | a ≤ y} 0 N ω : ℕ) with hτdef
  have hτ : IsStoppingTime ℱ τ :=
    hY.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hbdd : ∀ ω, τ ω ≤ N := fun ω => by
    simp only [hτdef]
    exact_mod_cast hittingBtwn_le (u := Y) (s := {y : ℝ | a ≤ y}) (n := 0) (m := N) ω
  have h0 : IsStoppingTime ℱ (fun _ => ((0 : ℕ) : ℕ∞)) := isStoppingTime_const ℱ 0
  have hmono := hY.neg.expected_stoppedValue_mono h0 hτ (fun ω => bot_le) hbdd
  have hint : Integrable (stoppedValue Y τ) μ :=
    integrable_stoppedValue ℕ hτ hY.integrable hbdd
  have hneg : ∀ σ : Ω → ℕ∞, stoppedValue (-Y) σ = -stoppedValue Y σ := fun σ => by
    funext ω; simp [stoppedValue]
  have hzero : stoppedValue Y (fun _ => ((0 : ℕ) : ℕ∞)) = Y 0 := stoppedValue_const Y 0
  rw [hneg, hneg, hzero] at hmono
  have hle : ∫ ω, stoppedValue Y τ ω ∂μ ≤ ∫ ω, Y 0 ω ∂μ := by
    have h1 : ∫ ω, (-Y 0) ω ∂μ = -∫ ω, Y 0 ω ∂μ := integral_neg _
    have h2 : ∫ ω, (-stoppedValue Y τ) ω ∂μ = -∫ ω, stoppedValue Y τ ω ∂μ := integral_neg _
    linarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun ω => (by simp only [stoppedValue]; exact hnn _ ω :
      (0 : Ω → ℝ) ω ≤ stoppedValue Y τ ω)) hint a
  have hsubset : {ω | ∃ k, k ≤ N ∧ a ≤ Y k ω} ⊆ {ω | a ≤ stoppedValue Y τ ω} := by
    rintro ω ⟨k, hk, hak⟩
    exact stoppedValue_hittingBtwn_mem (s := {y : ℝ | a ≤ y}) ⟨k, ⟨Nat.zero_le _, hk⟩, hak⟩
  have hmeas : μ.real {ω | ∃ k, k ≤ N ∧ a ≤ Y k ω} ≤ μ.real {ω | a ≤ stoppedValue Y τ ω} :=
    measureReal_mono hsubset
  calc a * μ.real {ω | ∃ k, k ≤ N ∧ a ≤ Y k ω}
      ≤ a * μ.real {ω | a ≤ stoppedValue Y τ ω} := mul_le_mul_of_nonneg_left hmeas ha
    _ ≤ ∫ ω, stoppedValue Y τ ω ∂μ := hmarkov
    _ ≤ ∫ ω, Y 0 ω ∂μ := hle

/-- **Ville's inequality.**  A nonnegative supermartingale reaches `a > 0` with
probability at most `E[Y 0] / a`. -/
theorem ville [IsFiniteMeasure μ] {Y : ℕ → Ω → ℝ} (hY : Supermartingale Y ℱ μ)
    (hnn : ∀ n ω, 0 ≤ Y n ω) {a : ℝ} (ha : 0 < a) :
    μ {ω | ∃ n, a ≤ Y n ω} ≤ ENNReal.ofReal ((∫ ω, Y 0 ω ∂μ) / a) := by
  have hunion : {ω | ∃ n, a ≤ Y n ω} = ⋃ N : ℕ, {ω | ∃ k, k ≤ N ∧ a ≤ Y k ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩, fun ⟨_, k, _, hk⟩ => ⟨k, hk⟩⟩
  have hmonoS : Monotone fun N : ℕ => {ω | ∃ k, k ≤ N ∧ a ≤ Y k ω} := by
    intro N N' hNN' ω ⟨k, hk, hak⟩
    exact ⟨k, hk.trans hNN', hak⟩
  rw [hunion, hmonoS.measure_iUnion]
  refine iSup_le fun N => ?_
  have h := ville_finite hY hnn ha.le N
  have hint0 : 0 ≤ (∫ ω, Y 0 ω ∂μ) / a :=
    div_nonneg (integral_nonneg fun ω => hnn 0 ω) ha.le
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hint0, le_div_iff₀ ha, mul_comm]
  exact h

/-! ## The staking process -/

namespace Betting

open Bridge Losses

/-- The settled account before day `n`, pathwise. -/
def account (c : ℝ) (x mu : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  prior c (fun i => x i ω) (fun i => mu i ω) n

/-- **The hypotheses**: predictable nonnegative stakes, outcomes in `[0, 1]` favourable
given the past, and the per-day ceiling. -/
structure Fair (μ : Measure Ω) (ℱ : Filtration ℕ m0) (c U : ℝ) (x mu : ℕ → Ω → ℝ) : Prop where
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  mu_meas : ∀ n, StronglyMeasurable[ℱ n] (mu n)
  x_meas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (x n)
  x_range : ∀ n ω, 0 ≤ x n ω ∧ x n ω ≤ 1
  mu_nonneg : ∀ n ω, 0 ≤ mu n ω
  favourable : ∀ n, (fun _ => c) ≤ᵐ[μ] μ[x n | ℱ n]
  ceiling : ∀ n ω, account c x mu n ω + mu n ω * (1 - c) ≤ U

variable {c U : ℝ} {x mu : ℕ → Ω → ℝ}

lemma Fair.U_nonneg (h : Fair μ ℱ c U x mu) [Nonempty Ω] : 0 ≤ U := by
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have := h.ceiling 0 ω
  have h2 : 0 ≤ mu 0 ω * (1 - c) := mul_nonneg (h.mu_nonneg 0 ω) (by linarith [h.c_lt_one])
  simp only [account, prior, Finset.range_zero, Finset.sum_empty] at this
  linarith

lemma Fair.headroom_nonneg (h : Fair μ ℱ c U x mu) (n : ℕ) (ω : Ω) :
    0 ≤ U - account c x mu n ω := by
  have h2 : 0 ≤ mu n ω * (1 - c) := mul_nonneg (h.mu_nonneg n ω) (by linarith [h.c_lt_one])
  linarith [h.ceiling n ω]

/-- The stakes are bounded on each day: `mu n ≤ U (1 - c)^-(n + 1)`. -/
lemma Fair.mu_le (h : Fair μ ℱ c U x mu) (n : ℕ) (ω : Ω) :
    mu n ω ≤ U * ((1 - c)⁻¹) ^ (n + 1) := by
  have h1c : 0 < 1 - c := by linarith [h.c_lt_one]
  have ha : 1 ≤ (1 - c)⁻¹ := (one_le_inv₀ h1c).mpr (by linarith [h.c_nonneg])
  have hhead := headroom_le (x := fun i => x i ω) (mu := fun i => mu i ω) h.c_nonneg
    h.c_lt_one (fun i => (h.x_range i ω).1) (fun i => h.mu_nonneg i ω)
    (fun i => h.ceiling i ω) n
  have hU : 0 ≤ U := by
    have := h.ceiling 0 ω
    have h2 : 0 ≤ mu 0 ω * (1 - c) := mul_nonneg (h.mu_nonneg 0 ω) h1c.le
    simp only [account, prior, Finset.range_zero, Finset.sum_empty] at this
    linarith
  have hlost : lost c (fun i => x i ω) n ≤ n := by
    unfold lost
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hpow : ((1 - c)⁻¹) ^ lost c (fun i => x i ω) n ≤ ((1 - c)⁻¹) ^ n :=
    pow_le_pow_right₀ ha hlost
  have hstake : mu n ω * (1 - c) ≤ U * ((1 - c)⁻¹) ^ n := by
    have := h.ceiling n ω
    have := mul_le_mul_of_nonneg_left hpow hU
    unfold account at *
    linarith
  rw [pow_succ, ← mul_assoc, le_mul_inv_iff₀ h1c]
  exact hstake

lemma Fair.stake_integrable [IsFiniteMeasure μ] (h : Fair μ ℱ c U x mu) (n : ℕ) :
    Integrable (mu n * fun ω => x n ω - c) μ := by
  have hmeas : AEStronglyMeasurable (mu n * fun ω => x n ω - c) μ :=
    (((h.mu_meas n).mono (ℱ.le n)).mul
      (((h.x_meas n).mono (ℱ.le (n + 1))).sub stronglyMeasurable_const)).aestronglyMeasurable
  refine Integrable.of_bound hmeas (U * ((1 - c)⁻¹) ^ (n + 1)) (ae_of_all μ fun ω => ?_)
  have h1 := h.mu_le n ω
  have h2 := h.mu_nonneg n ω
  have h3 : |x n ω - c| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [(h.x_range n ω).1, (h.x_range n ω).2, h.c_nonneg, h.c_lt_one]
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
  calc mu n ω * |x n ω - c| ≤ mu n ω * 1 := mul_le_mul_of_nonneg_left h3 h2
    _ ≤ U * ((1 - c)⁻¹) ^ (n + 1) := by linarith

lemma account_succ (c : ℝ) (x mu : ℕ → Ω → ℝ) (n : ℕ) :
    account c x mu (n + 1) = account c x mu n + mu n * fun ω => x n ω - c := by
  funext ω
  simp [account, prior_succ]

lemma Fair.account_meas (h : Fair μ ℱ c U x mu) (n : ℕ) :
    StronglyMeasurable[ℱ n] (account c x mu n) := by
  induction n with
  | zero =>
      have : account c x mu 0 = fun _ => 0 := by funext ω; simp [account, prior]
      rw [this]
      exact stronglyMeasurable_const
  | succ n ih =>
      rw [account_succ]
      exact (ih.mono (ℱ.mono (Nat.le_succ n))).add
        (((h.mu_meas n).mono (ℱ.mono (Nat.le_succ n))).mul
          ((h.x_meas n).sub stronglyMeasurable_const))

lemma Fair.account_integrable [IsFiniteMeasure μ] (h : Fair μ ℱ c U x mu) (n : ℕ) :
    Integrable (account c x mu n) μ := by
  induction n with
  | zero =>
      have : account c x mu 0 = fun _ => 0 := by funext ω; simp [account, prior]
      rw [this]
      exact integrable_const 0
  | succ n ih =>
      rw [account_succ]
      exact ih.add (h.stake_integrable n)

/-- **The headroom is a nonnegative supermartingale.** -/
theorem Fair.headroom_supermartingale [IsFiniteMeasure μ] (h : Fair μ ℱ c U x mu) :
    Supermartingale (fun n ω => U - account c x mu n ω) ℱ μ := by
  refine supermartingale_of_condExp_sub_nonneg_nat
    (fun n => stronglyMeasurable_const.sub (h.account_meas n))
    (fun n => (integrable_const U).sub (h.account_integrable n)) fun n => ?_
  have hdiff : ((fun ω => U - account c x mu n ω) - fun ω => U - account c x mu (n + 1) ω) =
      mu n * fun ω => x n ω - c := by
    rw [account_succ]
    funext ω
    simp
  rw [hdiff]
  have hxint : Integrable (fun ω => x n ω - c) μ := by
    refine Integrable.of_bound
      (((h.x_meas n).mono (ℱ.le (n + 1))).sub stronglyMeasurable_const).aestronglyMeasurable 1
      (ae_of_all μ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(h.x_range n ω).1, (h.x_range n ω).2, h.c_nonneg, h.c_lt_one]
  have hxint' : Integrable (x n) μ := by
    refine Integrable.of_bound ((h.x_meas n).mono (ℱ.le (n + 1))).aestronglyMeasurable 1
      (ae_of_all μ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(h.x_range n ω).1, (h.x_range n ω).2]
  have hpull := condExp_mul_of_stronglyMeasurable_left (μ := μ) (h.mu_meas n)
    (h.stake_integrable n) hxint
  have hsub : μ[fun ω => x n ω - c | ℱ n] =ᵐ[μ] μ[x n | ℱ n] - fun _ => c := by
    have h1 := condExp_sub hxint' (integrable_const c) (ℱ n) (μ := μ)
    have h2 : μ[fun _ : Ω => c | ℱ n] = fun _ => c := condExp_const (ℱ.le n) c
    rw [h2] at h1
    exact h1
  filter_upwards [hpull, hsub, h.favourable n] with ω h1 h2 h3
  rw [h1]
  simp only [Pi.zero_apply, Pi.mul_apply, Pi.sub_apply] at h2 ⊢
  rw [h2]
  exact mul_nonneg (h.mu_nonneg n ω) (by linarith)

/-- **The capital bound.**  With probability at least `K / (U + K)` the settled account
never reaches `-K`. -/
theorem Fair.account_bound [IsProbabilityMeasure μ] (h : Fair μ ℱ c U x mu) {K : ℝ}
    (hK : 0 < K) :
    μ {ω | ∃ n, account c x mu n ω ≤ -K} ≤ ENNReal.ofReal (U / (U + K)) := by
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hU : 0 ≤ U := h.U_nonneg
  have hv := ville h.headroom_supermartingale (fun n ω => h.headroom_nonneg n ω)
    (a := U + K) (by linarith)
  have h0 : ∫ ω, U - account c x mu 0 ω ∂μ = U := by
    simp [account, prior]
  rw [h0] at hv
  refine le_trans (measure_mono fun ω hω => ?_) hv
  obtain ⟨n, hn⟩ := hω
  exact ⟨n, by show U + K ≤ U - account c x mu n ω; linarith⟩

/-- **Almost surely the settled account is bounded below.** -/
theorem Fair.ae_bounded_below [IsProbabilityMeasure μ] (h : Fair μ ℱ c U x mu) :
    ∀ᵐ ω ∂μ, ∃ K : ℕ, ∀ n, -(K : ℝ) < account c x mu n ω := by
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hU : 0 ≤ U := h.U_nonneg
  rw [ae_iff]
  have hsub : ∀ K : ℕ, {ω | ¬ ∃ K : ℕ, ∀ n, -(K : ℝ) < account c x mu n ω} ⊆
      {ω | ∃ n, account c x mu n ω ≤ -((K : ℝ) + 1)} := by
    intro K ω hω
    simp only [Set.mem_setOf_eq, not_exists, not_forall, not_lt] at hω
    obtain ⟨n, hn⟩ := hω (K + 1)
    exact ⟨n, by push_cast at hn; exact hn⟩
  have hle : ∀ K : ℕ, μ {ω | ¬ ∃ K : ℕ, ∀ n, -(K : ℝ) < account c x mu n ω} ≤
      ENNReal.ofReal (U / (U + ((K : ℝ) + 1))) := fun K =>
    (measure_mono (hsub K)).trans (h.account_bound (by positivity))
  have htend : Filter.Tendsto (fun K : ℕ => ENNReal.ofReal (U / (U + ((K : ℝ) + 1))))
      Filter.atTop (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    have hden : Filter.Tendsto (fun K : ℕ => U + ((K : ℝ) + 1)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_left _ _
        (Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    exact hden.const_div_atTop U
  exact le_antisymm (ge_of_tendsto' htend hle) bot_le

/-! ### The witness: one fair coin

`Ω = Bool` with mass `1/2` on each point; nothing is known on day `0` and everything from
day `1`.  The day-`0` outcome is the coin, staked one unit at `c = 1/2`; every later
outcome is one and is not staked.  The settled account from day `1` is `1/2` on heads and
`-1/2` on tails. -/

/-- The fair coin. -/
noncomputable def coin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure coin :=
  ⟨by simp only [coin]; simp; exact ENNReal.inv_two_add_inv_two⟩

/-- Nothing on day `0`, everything after. -/
def coinFiltration : Filtration ℕ (⊤ : MeasurableSpace Bool) where
  seq n := if n = 0 then ⊥ else ⊤
  mono' i j hij := by
    by_cases hi : i = 0
    · simp [hi]
    · have hj : j ≠ 0 := fun h => hi (Nat.le_zero.mp (h ▸ hij))
      simp [hi, hj]
  le' _ := le_top

/-- The coin on day `0`, one after. -/
def coinOutcome (n : ℕ) (ω : Bool) : ℝ := if n = 0 then (if ω then 1 else 0) else 1

/-- One unit on day `0`, nothing after. -/
def coinStake (n : ℕ) (_ : Bool) : ℝ := if n = 0 then 1 else 0

lemma coin_integral (f : Bool → ℝ) : ∫ ω, f ω ∂coin = (f true + f false) / 2 := by
  have hfin : ∀ b : Bool, IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac b) := fun b =>
    ⟨by simp⟩
  haveI := hfin true
  haveI := hfin false
  unfold coin
  rw [integral_add_measure Integrable.of_finite Integrable.of_finite, integral_smul_measure,
    integral_smul_measure,
    integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- **Matter 3, inhabited**: the hypotheses hold for the coin at `c = 1/2`, `U = 1/2`, and
the settled account after day `0` is `-1/2` on tails. -/
theorem witness :
    Fair (m0 := (⊤ : MeasurableSpace Bool)) coin coinFiltration (1 / 2) (1 / 2)
      coinOutcome coinStake ∧
      account (1 / 2) coinOutcome coinStake 1 false = -(1 / 2) := by
  have hacc : ∀ n ω, account (1 / 2) coinOutcome coinStake n ω =
      if n = 0 then 0 else (if ω then 1 / 2 else -(1 / 2)) := by
    intro n ω
    induction n with
    | zero => simp [account, prior]
    | succ n ih =>
        unfold account at ih ⊢
        rw [prior_succ, ih]
        by_cases hn : n = 0
        · subst hn; cases ω <;> norm_num [coinOutcome, coinStake]
        · simp [coinStake, hn]
  refine ⟨⟨by norm_num, by norm_num, fun n => ?_, fun n => ?_, fun n ω => ?_, fun n ω => ?_,
    fun n => ?_, fun n ω => ?_⟩, by rw [hacc]; simp⟩
  · have : coinStake n = fun _ => if n = 0 then (1 : ℝ) else 0 := rfl
    rw [this]
    exact stronglyMeasurable_const
  · have htop : (coinFiltration : ℕ → MeasurableSpace Bool) (n + 1) = ⊤ := by
      change (if n + 1 = 0 then ⊥ else ⊤) = _
      simp
    rw [htop]
    exact (measurable_from_top (f := coinOutcome n)).stronglyMeasurable
  · unfold coinOutcome
    split_ifs <;> norm_num
  · unfold coinStake
    split_ifs <;> norm_num
  · by_cases hn : n = 0
    · subst hn
      have hbot : (coinFiltration : ℕ → MeasurableSpace Bool) 0 = ⊥ := by
        change (if (0 : ℕ) = 0 then ⊥ else ⊤) = _
        simp
      rw [hbot, condExp_bot, coin_integral]
      exact Filter.Eventually.of_forall fun _ => by norm_num [coinOutcome]
    · have hone : coinOutcome n = fun _ => 1 := by
        funext ω; simp [coinOutcome, hn]
      rw [hone, condExp_const (coinFiltration.le n)]
      exact Filter.Eventually.of_forall fun _ => by norm_num
  · rw [hacc]
    by_cases hn : n = 0
    · subst hn; norm_num [coinStake]
    · cases ω <;> simp [coinStake, hn]

end Betting

end Workspace.Normativity.Contrib.StatisticalConditions

#print axioms Workspace.Normativity.Contrib.StatisticalConditions.ville_finite
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.ville
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.Betting.Fair.headroom_supermartingale
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.Betting.Fair.account_bound
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.Betting.Fair.ae_bounded_below
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.Betting.witness
