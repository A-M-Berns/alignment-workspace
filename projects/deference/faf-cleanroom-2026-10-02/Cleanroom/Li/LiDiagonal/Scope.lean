import Cleanroom.Found.LiAsympCalc.Ramp
import Cleanroom.Found.LiAsympCalc.LimitPoint
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# `li-diagonal` · Scope: the scope-note §4 cluster as real-sequence facts (T7a, T7b, T7d)

Three facts about **real sequences** against FAF's ramp `ctsInd` and FAF's `weightedAverage`,
settling the arithmetic claims of [[faithful-acceleration-scope]] §4 and its critics
(trust-lab-055/056, trust-lab-2-046, root-fa-018). None of them mentions an inductor: by
`Legality.lean` (T7c(i)) the hard gate of T7b is no `EF`, so the inductor-level content of this
cluster is T2's engine with soft gates (`Engine.lean`); what is settled here is what the sources
actually argued about — sequences.

* **T7a, the hovering quote** (`aHover`, `yHover`): the quote `½ + 2⁻ⁿ` on even days, `½` on odd
  days, against the inverting settlement `𝟙[a ≤ ½]`. The scope note's high ramp has bounded
  weight (`aHover_highRamp_sum_le`), its low ramp is identically `0` (`aHover_lowRamp_eq_zero`),
  yet the quote never settles on one side (`aHover_straddles`) and the uniform-weighted bias
  tends to `0` (`aHover_cesaro_tendsto_zero`, `aHover_uniform_bias_tendsto_zero`). So §4's step 3
  ("hence `a_n ≤ ½`") is a non sequitur and step 4's "`→ −½`" is false on this sequence. Finding
  F-8's real-sequence witness.
* **T7b, the repaired dichotomy** (`hard_dichotomy`): for every `[0,1]`-valued `a`, one of the
  hard one-sided gates `𝟙[a > ½]`, `𝟙[a ≤ ½]` has divergent weight, and on the divergent one the
  weighted bias against `𝟙[a ≤ ½]` is one-signed of size `≥ ½` wherever the weight is positive —
  hence never has `0` as a limit point (`hard_dichotomy_not_hasLimitPoint`). Deletion test:
  with the benign settlement `Y ≡ a ≡ ½` the divergent gate carries zero bias
  (`hard_dichotomy_deletion_test`).
* **T7d, dithering** (`dither`, `highRamp`, `lowRamp`): for `a_n = ½ + s_n η_n` with
  `s_n ∈ {±1}`, `0 < η_n < ½`, the soft high ramp `ctsInd δ (a_n) ½` has divergent weight and
  bias `≥ ½` on its support **under the side-density hypothesis** `∑_{s_n = +1} η_n = ∞`
  (`dither_high_kills`); mirror for the low ramp (`dither_low_kills`); for every non-summable
  ditherer one of the two holds (`dither_one_sided_kills`). The source's "the soft high gate kills
  every non-summable ditherer" is false as stated: `sparseDither` has `∑ η_n = ∞` with a single
  `+` day, and its high ramp has total weight `≤ 1` (`sparseDither_highRamp_sum_le_one`). K5.

Scope: single-market (real sequences; no market object).
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction Cleanroom.Found.LiAsympCalc
open Filter Topology Finset Set

/-! ### Shared infrastructure -/

/-- The inverting settlement `Y_n := 𝟙[a_n ≤ ½]` of a real quote sequence (the scope note's
`Y_n`; `Defs.side` is the same map on a rational table).
Source: [[faithful-acceleration-scope]] §4; [[trust-lab-inventory]] 056
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def invSide (a : ℕ → ℝ) (n : ℕ) : ℝ := if a n ≤ 1 / 2 then 1 else 0

lemma invSide_of_le {a : ℕ → ℝ} {n : ℕ} (h : a n ≤ 1 / 2) : invSide a n = 1 := by
  unfold invSide; rw [if_pos h]

lemma invSide_of_gt {a : ℕ → ℝ} {n : ℕ} (h : 1 / 2 < a n) : invSide a n = 0 := by
  unfold invSide; rw [if_neg (not_le.mpr h)]

/-- Inclusive prefix sums of a nonnegative sequence are monotone.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma monotone_prefixSum {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) : Monotone (prefixSum u) :=
  monotone_nat_of_le_succ fun n => by rw [prefixSum_succ]; linarith [hu (n + 1)]

/-- If the prefix sums of `u + v` (both nonnegative) diverge, those of `u` or of `v` do.
Source: none: infrastructure (the "at least one of `∑ w⁺`, `∑ w⁻` diverges" step of
[[trust-lab-inventory]] 056 and [[trust-lab-2-inventory]] 046)
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma divergent_or_of_add {u v : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (h : Tendsto (prefixSum (fun i => u i + v i)) atTop atTop) :
    Tendsto (prefixSum u) atTop atTop ∨ Tendsto (prefixSum v) atTop atTop := by
  by_cases hdiv : Tendsto (prefixSum u) atTop atTop
  · exact Or.inl hdiv
  · right
    have hbdd : ∃ B, ∀ n, prefixSum u n < B := by
      by_contra hcon
      refine hdiv (tendsto_atTop_atTop_of_monotone (monotone_prefixSum hu) fun b => ?_)
      by_contra hb
      exact hcon ⟨b, fun n => lt_of_not_ge fun h => hb ⟨n, h⟩⟩
    obtain ⟨B, hB⟩ := hbdd
    refine tendsto_atTop_atTop_of_monotone (monotone_prefixSum hv) fun b => ?_
    obtain ⟨n, hn⟩ := (tendsto_atTop.1 h (b + B)).exists
    refine ⟨n, ?_⟩
    rw [prefixSum_add] at hn
    linarith [hB n]

/-- A sequence eventually bounded away from `0` in absolute value has no limit point `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma not_hasLimitPoint_zero_of_eventually_abs_ge {f : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ n in atTop, c ≤ |f n|) : ¬ HasLimitPoint f 0 := by
  intro hlp
  obtain ⟨n, hn1, hn2⟩ := ((hasLimitPoint_zero_iff.1 hlp) c hc).and_eventually h |>.exists
  linarith

/-! ### T7a. The hovering quote -/

/-- The hovering quote of trust-lab-055: `½ + (½)^n` on even days, `½` on odd days.
Source: [[trust-lab-inventory]] 055 (Finding A); [[faithful-acceleration-scope]] §4
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def aHover (n : ℕ) : ℝ := if Even n then 1 / 2 + (1 / 2 : ℝ) ^ n else 1 / 2

/-- The inverting settlement of the hovering quote, `𝟙[aHover n ≤ ½]`.
Source: [[trust-lab-inventory]] 055
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def yHover : ℕ → ℝ := invSide aHover

lemma aHover_even {n : ℕ} (h : Even n) : aHover n = 1 / 2 + (1 / 2 : ℝ) ^ n := by
  simp [aHover, h]

lemma aHover_odd {n : ℕ} (h : ¬ Even n) : aHover n = 1 / 2 := by
  simp [aHover, h]

lemma yHover_even {n : ℕ} (h : Even n) : yHover n = 0 := by
  unfold yHover
  apply invSide_of_gt
  rw [aHover_even h]
  have : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  linarith

lemma yHover_odd {n : ℕ} (h : ¬ Even n) : yHover n = 1 := by
  unfold yHover
  apply invSide_of_le
  rw [aHover_odd h]

lemma aHover_ge_quarter (n : ℕ) : 1 / 4 ≤ aHover n := by
  unfold aHover
  split_ifs
  · have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
    linarith
  · norm_num

/-- The source's sequence is a price only from day `1` on: `aHover 0 = 3/2` (a presentation nit
of trust-lab-055; nothing below uses day `0`'s value beyond its sign).
Source: [[trust-lab-inventory]] 055
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma aHover_zero : aHover 0 = 3 / 2 := by
  simp [aHover]; norm_num

lemma aHover_le_one_of_pos {n : ℕ} (hn : 1 ≤ n) : aHover n ≤ 1 := by
  unfold aHover
  split_ifs
  · have h2 : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    linarith
  · norm_num

/-- **T7a (non sequitur witness).** The hovering quote never settles on one side of `½`: above
`½` on every even day, at `½` on every odd day. So "on all but bounded weight `a_n = ½ ± o(1)`,
hence `a_n ≤ ½`" (scope note §4 step 3) does not follow.
Scope: single-market (real sequences).
Source: [[faithful-acceleration-scope]] §4 step 3; [[trust-lab-inventory]] 055; [[root-fa-inventory]] 018
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem aHover_straddles (N : ℕ) :
    (∃ n, N ≤ n ∧ 1 / 2 < aHover n) ∧ (∃ n, N ≤ n ∧ aHover n ≤ 1 / 2) := by
  refine ⟨⟨2 * N, by omega, ?_⟩, ⟨2 * N + 1, by omega, ?_⟩⟩
  · rw [aHover_even (even_two_mul N)]
    have : (0 : ℝ) < (1 / 2 : ℝ) ^ (2 * N) := by positivity
    linarith
  · rw [aHover_odd (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one N))]

/-- Pointwise bound on the high ramp of width `¼` at threshold `½`: `≤ 4 · (½)^n`.
Source: [[trust-lab-inventory]] 055
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma aHover_highRamp_le (n : ℕ) :
    ctsInd (1 / 4) (aHover n) (1 / 2) ≤ 4 * (1 / 2 : ℝ) ^ n := by
  have hq : (((1 : ℚ) / 4 : ℚ) : ℝ) = 1 / 4 := by norm_num
  have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  unfold ctsInd
  rw [hq]
  by_cases h : Even n
  · rw [aHover_even h]
    have heq : (1 / 2 + (1 / 2 : ℝ) ^ n - 1 / 2) / (1 / 4) = 4 * (1 / 2 : ℝ) ^ n := by ring
    rw [heq, max_eq_right (by positivity)]
    exact min_le_right _ _
  · rw [aHover_odd h]
    simp only [sub_self, zero_div, max_self]
    rw [min_eq_right zero_le_one]
    positivity

/-- **T7a(i).** The scope note's high ramp `Ind_¼(a_n > ½)` has bounded total weight on the
hovering quote: every partial sum is `≤ 8`. So it is not divergent, and recurring unbiasedness
on it says nothing.
Scope: single-market (real sequences).
Source: [[trust-lab-inventory]] 055 ("`Σ softInd δ (a_n − ½) ≤ 16/3`": the bound `8` here is cruder, the fact is the same); [[faithful-acceleration-scope]] §4 step 1
Kind: P
Fidelity: weaker: cruder constant (`8` in place of the source's `16/3`), same fact (bounded high ramp)
Hyps: (a) none -/
theorem aHover_highRamp_sum_le (N : ℕ) :
    ∑ i ∈ range N, ctsInd (1 / 4) (aHover i) (1 / 2) ≤ 8 := by
  calc ∑ i ∈ range N, ctsInd (1 / 4) (aHover i) (1 / 2)
      ≤ ∑ i ∈ range N, 4 * (1 / 2 : ℝ) ^ i := sum_le_sum fun i _ => aHover_highRamp_le i
    _ = 4 * ∑ i ∈ range N, (1 / 2 : ℝ) ^ i := by rw [mul_sum]
    _ ≤ 4 * 2 := by
        have := sum_geometric_two_le N
        linarith
    _ = 8 := by norm_num

/-- **T7a(i), prefix-sum form.** The high ramp's inclusive prefix sums do not diverge.
Scope: single-market (real sequences).
Source: [[trust-lab-inventory]] 055; [[faithful-acceleration-scope]] §4 step 1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem aHover_highRamp_not_divergent :
    ¬ Tendsto (prefixSum fun n => ctsInd (1 / 4) (aHover n) (1 / 2)) atTop atTop := by
  intro h
  obtain ⟨n, hn⟩ := (tendsto_atTop.1 h 9).exists
  have := aHover_highRamp_sum_le (n + 1)
  simp only [prefixSum] at hn
  linarith

/-- **T7a(ii).** The scope note's low ramp `Ind_¼(½ − ¼ − a_n)` — in FAF's spelling
`ctsInd ¼ ¼ (aHover n)`, positive iff `aHover n < ¼` — is identically `0` on the hovering quote.
Scope: single-market (real sequences).
Source: [[trust-lab-inventory]] 055; [[faithful-acceleration-scope]] §4 step 2
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem aHover_lowRamp_eq_zero (n : ℕ) : ctsInd (1 / 4) (1 / 4) (aHover n) = 0 :=
  (ctsInd_eq_zero_iff (by norm_num) _ _).2 (aHover_ge_quarter n)

/-- Partial sums of the per-day bias `aHover − yHover` (exclusive, `N` terms).
Source: [[trust-lab-inventory]] 055
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def hoverSum (N : ℕ) : ℝ := ∑ i ∈ range N, (aHover i - yHover i)

lemma hoverSum_two_mul (M : ℕ) : hoverSum (2 * M) = ∑ k ∈ range M, (1 / 4 : ℝ) ^ k := by
  induction M with
  | zero => simp [hoverSum]
  | succ M ih =>
    have h2 : 2 * (M + 1) = 2 * M + 1 + 1 := by ring
    rw [h2, hoverSum, sum_range_succ, sum_range_succ, ← hoverSum, ih, sum_range_succ,
      aHover_even (even_two_mul M), yHover_even (even_two_mul M),
      aHover_odd (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one M)),
      yHover_odd (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one M))]
    have hpow : (1 / 2 : ℝ) ^ (2 * M) = (1 / 4 : ℝ) ^ M := by
      rw [pow_mul]; norm_num
    rw [hpow]; ring

lemma sum_quarter_pow_le (M : ℕ) : ∑ k ∈ range M, (1 / 4 : ℝ) ^ k ≤ 2 := by
  calc ∑ k ∈ range M, (1 / 4 : ℝ) ^ k
      ≤ ∑ k ∈ range M, (1 / 2 : ℝ) ^ k :=
        sum_le_sum fun k _ => pow_le_pow_left₀ (by norm_num) (by norm_num) k
    _ ≤ 2 := sum_geometric_two_le M

/-- **T7a(iii), partial sums.** The partial sums of `aHover − yHover` lie in `[0, 4]`.
Scope: single-market (real sequences).
Source: [[trust-lab-inventory]] 055 ("partial sums in `[0, 7/2]`")
Kind: P
Fidelity: weaker: cruder constant (`[0, 4]` in place of the source's `[0, 7/2]`), same fact (bounded partial sums)
Hyps: (a) none -/
theorem hoverSum_mem_Icc (N : ℕ) : hoverSum N ∈ Icc (0 : ℝ) 4 := by
  obtain ⟨M, hM | hM⟩ := Nat.even_or_odd' N
  · subst hM
    rw [hoverSum_two_mul]
    exact ⟨sum_nonneg fun k _ => by positivity, (sum_quarter_pow_le M).trans (by norm_num)⟩
  · subst hM
    rw [hoverSum, sum_range_succ, ← hoverSum, hoverSum_two_mul, aHover_even (even_two_mul M),
      yHover_even (even_two_mul M)]
    have h1 := sum_quarter_pow_le M
    have h2 : (0 : ℝ) ≤ ∑ k ∈ range M, (1 / 4 : ℝ) ^ k := sum_nonneg fun k _ => by positivity
    have h3 : (1 / 2 : ℝ) ^ (2 * M) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h4 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 * M) := by positivity
    constructor <;> linarith

/-- **T7a(iii).** The uniform-weighted (Cesàro) bias of the hovering quote against its inverting
settlement tends to `0` — the scope note's step 4 ("`→ −½`") is false on this sequence. (This
refutes step 4, not the note's conclusion: the note quantifies (II) over *every* legal gate, and
the legal `evenIndicator` catches `aHover` with bias `≥ ½` on every even day; see F-8.)
Scope: single-market (real sequences).
Source: [[trust-lab-inventory]] 055; [[faithful-acceleration-scope]] §4 step 4; [[root-fa-inventory]] 018
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem aHover_cesaro_tendsto_zero :
    Tendsto (cesaro fun n => aHover n - yHover n) atTop (𝓝 0) := by
  have hbound : ∀ N : ℕ, |cesaro (fun n => aHover n - yHover n) N| ≤ 4 / (N : ℝ) := by
    intro N
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp [cesaro]
    · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      change |hoverSum N / (N : ℝ)| ≤ 4 / (N : ℝ)
      rw [abs_div, Nat.abs_cast]
      apply div_le_div_of_nonneg_right _ hNpos.le
      obtain ⟨h0, h4⟩ := hoverSum_mem_Icc N
      rw [abs_of_nonneg h0]; exact h4
  have hlim : Tendsto (fun N : ℕ => 4 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun N : ℕ => -(4 / (N : ℝ)))
    (h := fun N : ℕ => 4 / (N : ℝ)) ?_ hlim (fun N => (abs_le.1 (hbound N)).1)
    (fun N => (abs_le.1 (hbound N)).2)
  simpa using hlim.neg

/-- **T7a(iii), FAF spelling.** The uniform weighting's `weightedBias` of the hovering quote
against its inverting settlement tends to `0`.
Scope: single-market (real sequences).
Source: [[faithful-acceleration-scope]] §4 step 4; [[trust-lab-inventory]] 055
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem aHover_uniform_bias_tendsto_zero :
    Tendsto (weightedBias (fun _ => (1 : ℝ)) aHover yHover) atTop (𝓝 0) := by
  have h := aHover_cesaro_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  refine h.congr fun n => ?_
  simp only [Function.comp, weightedBias]
  rw [cesaro_eq_weightedAverage_one _ (by omega), Nat.add_sub_cancel]

/-! ### T7b. The repaired dichotomy: hard one-sided gates against the inverting settlement -/

/-- The hard high gate `𝟙[a_n > ½]`.
Source: [[trust-lab-inventory]] 056
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def wPlus (a : ℕ → ℝ) (n : ℕ) : ℝ := if 1 / 2 < a n then 1 else 0

/-- The hard low gate `𝟙[a_n ≤ ½] = 1 − 𝟙[a_n > ½]`.
Source: [[trust-lab-inventory]] 056
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def wMinus (a : ℕ → ℝ) (n : ℕ) : ℝ := 1 - wPlus a n

lemma wPlus_nonneg (a : ℕ → ℝ) (n : ℕ) : 0 ≤ wPlus a n := by
  unfold wPlus; split_ifs <;> norm_num

lemma wMinus_nonneg (a : ℕ → ℝ) (n : ℕ) : 0 ≤ wMinus a n := by
  unfold wMinus wPlus; split_ifs <;> norm_num

lemma wPlus_pos_iff {a : ℕ → ℝ} {n : ℕ} : 0 < wPlus a n ↔ 1 / 2 < a n := by
  unfold wPlus; split_ifs with h
  · exact ⟨fun _ => h, fun _ => one_pos⟩
  · exact ⟨fun h0 => absurd h0 (lt_irrefl 0), fun h' => absurd h' h⟩

lemma wMinus_pos_iff {a : ℕ → ℝ} {n : ℕ} : 0 < wMinus a n ↔ a n ≤ 1 / 2 := by
  unfold wMinus wPlus; split_ifs with h
  · rw [sub_self]
    exact ⟨fun h0 => absurd h0 (lt_irrefl 0), fun h' => absurd h (not_lt.2 h')⟩
  · rw [sub_zero]
    exact ⟨fun _ => not_lt.1 h, fun _ => one_pos⟩

/-- The two hard gates sum to the uniform weighting, so their prefix sums add to `n + 1`.
Source: [[trust-lab-inventory]] 056
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma prefixSum_wPlus_add_wMinus (a : ℕ → ℝ) (n : ℕ) :
    prefixSum (fun i => wPlus a i + wMinus a i) n = (n : ℝ) + 1 := by
  have : (fun i => wPlus a i + wMinus a i) = fun _ => (1 : ℝ) := by
    funext i; simp [wMinus]
  rw [this, prefixSum_one]

/-- One of the two hard gates has divergent weight (no hypothesis on `a`).
Source: [[trust-lab-inventory]] 056
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem hard_gates_one_divergent (a : ℕ → ℝ) :
    Tendsto (prefixSum (wPlus a)) atTop atTop ∨ Tendsto (prefixSum (wMinus a)) atTop atTop := by
  apply divergent_or_of_add (wPlus_nonneg a) (wMinus_nonneg a)
  have : prefixSum (fun i => wPlus a i + wMinus a i) = fun n : ℕ => (n : ℝ) + 1 := by
    funext n; exact prefixSum_wPlus_add_wMinus a n
  rw [this]
  exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

/-- On the high gate's support the bias against the inverting settlement is `a_n ∈ [½, 1]`.
Source: [[trust-lab-inventory]] 056
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem wPlus_bias_ge {a : ℕ → ℝ} (ha : ∀ n, a n ∈ Icc (0 : ℝ) 1) {n : ℕ}
    (hden : 0 < prefixSum (wPlus a) n) :
    1 / 2 ≤ weightedBias (wPlus a) a (invSide a) n := by
  unfold weightedBias
  refine (weightedAverage_mem_Icc_of_support (a := 1 / 2) (b := 1) (wPlus_nonneg a) ?_ hden).1
  intro i hi
  have h := wPlus_pos_iff.1 hi
  rw [invSide_of_gt h, sub_zero]
  exact ⟨h.le, (ha i).2⟩

/-- On the low gate's support the bias against the inverting settlement is `a_n − 1 ∈ [−1, −½]`.
Source: [[trust-lab-inventory]] 056
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem wMinus_bias_le {a : ℕ → ℝ} (ha : ∀ n, a n ∈ Icc (0 : ℝ) 1) {n : ℕ}
    (hden : 0 < prefixSum (wMinus a) n) :
    weightedBias (wMinus a) a (invSide a) n ≤ -(1 / 2) := by
  unfold weightedBias
  refine (weightedAverage_mem_Icc_of_support (a := -1) (b := -(1 / 2)) (wMinus_nonneg a) ?_
    hden).2
  intro i hi
  have h := wMinus_pos_iff.1 hi
  rw [invSide_of_le h]
  exact ⟨by linarith [(ha i).1], by linarith⟩

/-- **T7b, the repaired dichotomy.** For every `[0,1]`-valued quote sequence `a`, one of the hard
one-sided gates `𝟙[a > ½]`, `𝟙[a ≤ ½]` has divergent weight, and on the divergent one the
weighted bias against the inverting settlement `𝟙[a ≤ ½]` is one-signed of size `≥ ½` whenever
the weight is positive. This is a fact about real sequences: the hard gate is no `EF`
(`hardGate_yesterday_not_ef`, T7c(i)), so it says nothing about inductors.
Scope: single-market (real sequences).
Source: [[trust-lab-inventory]] 056 (the repair of 055); [[root-fa-inventory]] 018
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem hard_dichotomy (a : ℕ → ℝ) (ha : ∀ n, a n ∈ Icc (0 : ℝ) 1) :
    (Tendsto (prefixSum (wPlus a)) atTop atTop ∧
        ∀ n, 0 < prefixSum (wPlus a) n → 1 / 2 ≤ weightedBias (wPlus a) a (invSide a) n) ∨
      (Tendsto (prefixSum (wMinus a)) atTop atTop ∧
        ∀ n, 0 < prefixSum (wMinus a) n → weightedBias (wMinus a) a (invSide a) n ≤ -(1 / 2)) := by
  rcases hard_gates_one_divergent a with h | h
  · exact Or.inl ⟨h, fun n hn => wPlus_bias_ge ha hn⟩
  · exact Or.inr ⟨h, fun n hn => wMinus_bias_le ha hn⟩

/-- **T7b, limit-point form.** On the divergent hard gate the weighted bias never has `0` as a
limit point — the shape of the scope note's "(II)" fails for it.
Scope: single-market (real sequences).
Source: [[trust-lab-inventory]] 056; [[faithful-acceleration-scope]] §4
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem hard_dichotomy_not_hasLimitPoint (a : ℕ → ℝ) (ha : ∀ n, a n ∈ Icc (0 : ℝ) 1) :
    (Tendsto (prefixSum (wPlus a)) atTop atTop ∧
        ¬ HasLimitPoint (weightedBias (wPlus a) a (invSide a)) 0) ∨
      (Tendsto (prefixSum (wMinus a)) atTop atTop ∧
        ¬ HasLimitPoint (weightedBias (wMinus a) a (invSide a)) 0) := by
  rcases hard_dichotomy a ha with ⟨h, hb⟩ | ⟨h, hb⟩
  · refine Or.inl ⟨h, not_hasLimitPoint_zero_of_eventually_abs_ge (c := 1 / 2) (by norm_num) ?_⟩
    filter_upwards [eventually_prefixSum_pos h] with n hn
    exact le_trans (hb n hn) (le_abs_self _)
  · refine Or.inr ⟨h, not_hasLimitPoint_zero_of_eventually_abs_ge (c := 1 / 2) (by norm_num) ?_⟩
    filter_upwards [eventually_prefixSum_pos h] with n hn
    have := hb n hn
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- **T7b, deletion test.** With the benign settlement `Y ≡ ½` and the quote `a ≡ ½`, the low
gate is the uniform weighting (divergent) and carries zero bias: the inverting settlement is
load-bearing in `hard_dichotomy`.
Scope: single-market (real sequences).
Source: [[trust-lab-inventory]] 056 ("deletion test"); [[trust-lab-2-inventory]] 046 Part 3
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem hard_dichotomy_deletion_test :
    Tendsto (prefixSum (wMinus fun _ => (1 / 2 : ℝ))) atTop atTop ∧
      ∀ n, weightedBias (wMinus fun _ => (1 / 2 : ℝ)) (fun _ => 1 / 2) (fun _ => 1 / 2) n = 0 := by
  have hw : wMinus (fun _ => (1 / 2 : ℝ)) = fun _ => (1 : ℝ) := by
    funext n; simp [wMinus, wPlus]
  refine ⟨?_, fun n => ?_⟩
  · rw [hw]; exact tendsto_prefixSum_one
  · simp [weightedBias, weightedAverage, prefixSum]

/-! ### T7d. Dithering: soft one-sided ramps need a side-density hypothesis -/

/-- A dithering quote `a_n := ½ + s_n η_n` (sides `s_n ∈ {±1}`, amplitudes `η_n`).
Source: [[trust-lab-inventory]] 058; [[trust-lab-2-inventory]] 046 Part 4a
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def dither (s η : ℕ → ℝ) (n : ℕ) : ℝ := 1 / 2 + s n * η n

/-- The soft high ramp `Ind_δ(a_n > ½)`, FAF's `ctsInd δ (a_n) ½`.
Source: [[trust-lab-2-inventory]] 046; [[faithful-acceleration-scope]] §4 step 1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def highRamp (δ : ℚ) (a : ℕ → ℝ) (n : ℕ) : ℝ := ctsInd δ (a n) (1 / 2)

/-- The soft low ramp `Ind_δ(½ > a_n)`, FAF's `ctsInd δ ½ (a_n)`.
Source: [[trust-lab-2-inventory]] 046
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def lowRamp (δ : ℚ) (a : ℕ → ℝ) (n : ℕ) : ℝ := ctsInd δ (1 / 2) (a n)

/-- The amplitude mass on the `+` side, `η_n · 𝟙[s_n = 1]`.
Source: [[trust-lab-2-inventory]] 046 (its "Flags")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def plusMass (s η : ℕ → ℝ) (n : ℕ) : ℝ := if s n = 1 then η n else 0

/-- The amplitude mass on the `−` side, `η_n · 𝟙[s_n = −1]`.
Source: [[trust-lab-2-inventory]] 046 (its "Flags")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def minusMass (s η : ℕ → ℝ) (n : ℕ) : ℝ := if s n = -1 then η n else 0

section Dither

variable {s η : ℕ → ℝ} (hs : ∀ n, s n = 1 ∨ s n = -1) (hη : ∀ n, 0 < η n ∧ η n < 1 / 2)
include hs hη

lemma dither_mem (n : ℕ) : dither s η n ∈ Icc (0 : ℝ) 1 := by
  unfold dither
  rcases hs n with h | h <;> rw [h] <;> constructor <;> linarith [hη n]

omit hs hη in
lemma dither_plus {n : ℕ} (h : s n = 1) : dither s η n = 1 / 2 + η n := by
  simp [dither, h]

omit hs hη in
lemma dither_minus {n : ℕ} (h : s n = -1) : dither s η n = 1 / 2 - η n := by
  simp [dither, h]; ring

omit hs hη in
lemma plusMass_nonneg (hη : ∀ n, 0 < η n ∧ η n < 1 / 2) (n : ℕ) : 0 ≤ plusMass s η n := by
  unfold plusMass; split_ifs <;> linarith [hη n]

omit hs hη in
lemma minusMass_nonneg (hη : ∀ n, 0 < η n ∧ η n < 1 / 2) (n : ℕ) : 0 ≤ minusMass s η n := by
  unfold minusMass; split_ifs <;> linarith [hη n]

omit hη in
lemma plusMass_add_minusMass (n : ℕ) : plusMass s η n + minusMass s η n = η n := by
  unfold plusMass minusMass
  rcases hs n with h | h
  · rw [if_pos h, if_neg (by rw [h]; norm_num), add_zero]
  · rw [if_neg (by rw [h]; norm_num), if_pos h, zero_add]

/-- The high ramp's support is exactly the `+` days.
Source: [[trust-lab-2-inventory]] 046 Part 4a
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma highRamp_pos_iff {δ : ℚ} (hδ : 0 < δ) (n : ℕ) :
    0 < highRamp δ (dither s η) n ↔ s n = 1 := by
  unfold highRamp
  rw [ctsInd_pos_iff hδ]
  rcases hs n with h | h
  · rw [dither_plus h]; simp only [h, iff_true]; linarith [hη n]
  · rw [dither_minus h]
    constructor
    · intro hlt; linarith [hη n]
    · intro h1; rw [h] at h1; norm_num at h1

/-- The low ramp's support is exactly the `−` days.
Source: [[trust-lab-2-inventory]] 046
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma lowRamp_pos_iff {δ : ℚ} (hδ : 0 < δ) (n : ℕ) :
    0 < lowRamp δ (dither s η) n ↔ s n = -1 := by
  unfold lowRamp
  rw [ctsInd_pos_iff hδ]
  rcases hs n with h | h
  · rw [dither_plus h]
    constructor
    · intro hlt; linarith [hη n]
    · intro h1; rw [h] at h1; norm_num at h1
  · rw [dither_minus h]; simp only [h, iff_true]; linarith [hη n]

/-- Lower bound: the high ramp dominates `min 1 (1/δ)` times the `+`-side mass.
Source: [[trust-lab-2-inventory]] 046 Part 4a ("weight sum `~ Σ_{s_n=+1} η_n/δ`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma highRamp_ge_plusMass {δ : ℚ} (hδ : 0 < δ) (n : ℕ) :
    min 1 (1 / (δ : ℝ)) * plusMass s η n ≤ highRamp δ (dither s η) n := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold plusMass highRamp
  rcases hs n with h | h
  · rw [if_pos h, dither_plus h]
    unfold ctsInd
    have hsub : (1 / 2 + η n - 1 / 2) / (δ : ℝ) = η n / δ := by ring
    obtain ⟨h0, h1⟩ := hη n
    rw [hsub, max_eq_right (div_nonneg h0.le hδR.le)]
    refine le_min ?_ ?_
    · exact mul_le_one₀ (min_le_left _ _) h0.le (by linarith)
    · calc min 1 (1 / (δ : ℝ)) * η n ≤ (1 / (δ : ℝ)) * η n :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) h0.le
        _ = η n / δ := by ring
  · rw [if_neg (by rw [h]; norm_num), mul_zero]
    exact ctsInd_nonneg _ _ _

/-- Mirror: the low ramp dominates `min 1 (1/δ)` times the `−`-side mass.
Source: [[trust-lab-2-inventory]] 046
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma lowRamp_ge_minusMass {δ : ℚ} (hδ : 0 < δ) (n : ℕ) :
    min 1 (1 / (δ : ℝ)) * minusMass s η n ≤ lowRamp δ (dither s η) n := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold minusMass lowRamp
  rcases hs n with h | h
  · rw [if_neg (by rw [h]; norm_num), mul_zero]
    exact ctsInd_nonneg _ _ _
  · rw [if_pos h, dither_minus h]
    unfold ctsInd
    have hsub : (1 / 2 - (1 / 2 - η n)) / (δ : ℝ) = η n / δ := by ring
    obtain ⟨h0, h1⟩ := hη n
    rw [hsub, max_eq_right (div_nonneg h0.le hδR.le)]
    refine le_min ?_ ?_
    · exact mul_le_one₀ (min_le_left _ _) h0.le (by linarith)
    · calc min 1 (1 / (δ : ℝ)) * η n ≤ (1 / (δ : ℝ)) * η n :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) h0.le
        _ = η n / δ := by ring

omit hs hη in
lemma prefixSum_const_mul (c : ℝ) (u : ℕ → ℝ) (n : ℕ) :
    prefixSum (fun i => c * u i) n = c * prefixSum u n := by
  simp only [prefixSum, mul_sum]

/-- **T7d (high side).** Under the side-density hypothesis `∑_{s_n = +1} η_n = ∞`, the soft high
ramp of any width `δ > 0` has divergent weight, and on it the weighted bias against the
inverting settlement `𝟙[a ≤ ½]` is `≥ ½` whenever the weight is positive; hence `0` is not a
limit point of that bias.
Scope: single-market (real sequences).
Source: [[trust-lab-2-inventory]] 046 Part 4a, corrected by its "Flags" (K5); [[trust-lab-inventory]] 058
Kind: P
Fidelity: variant: the side-density hypothesis replaces the source's "non-summable" (which is false as stated: `sparseDither_highRamp_sum_le_one`)
Hyps: (a) none beyond the side-density hypothesis, which is the corrected claim's own hypothesis -/
theorem dither_high_kills {δ : ℚ} (hδ : 0 < δ)
    (hdens : Tendsto (prefixSum (plusMass s η)) atTop atTop) :
    Tendsto (prefixSum (highRamp δ (dither s η))) atTop atTop ∧
      (∀ n, 0 < prefixSum (highRamp δ (dither s η)) n →
        1 / 2 ≤ weightedBias (highRamp δ (dither s η)) (dither s η) (invSide (dither s η)) n) ∧
      ¬ HasLimitPoint (weightedBias (highRamp δ (dither s η)) (dither s η)
          (invSide (dither s η))) 0 := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hc : (0 : ℝ) < min 1 (1 / (δ : ℝ)) := lt_min one_pos (by positivity)
  have hdiv : Tendsto (prefixSum (highRamp δ (dither s η))) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) (hdens.const_mul_atTop hc)
    rw [← prefixSum_const_mul]
    unfold prefixSum
    exact sum_le_sum fun i _ => highRamp_ge_plusMass hs hη hδ i
  have hbias : ∀ n, 0 < prefixSum (highRamp δ (dither s η)) n →
      1 / 2 ≤ weightedBias (highRamp δ (dither s η)) (dither s η) (invSide (dither s η)) n := by
    intro n hn
    unfold weightedBias
    refine (weightedAverage_mem_Icc_of_support (a := 1 / 2) (b := 1)
      (fun i => ctsInd_nonneg _ _ _) ?_ hn).1
    intro i hi
    have h := (highRamp_pos_iff hs hη hδ i).1 hi
    have hgt : 1 / 2 < dither s η i := by rw [dither_plus h]; linarith [hη i]
    rw [invSide_of_gt hgt, sub_zero]
    exact ⟨hgt.le, (dither_mem hs hη i).2⟩
  refine ⟨hdiv, hbias, not_hasLimitPoint_zero_of_eventually_abs_ge (c := 1 / 2) (by norm_num) ?_⟩
  filter_upwards [eventually_prefixSum_pos hdiv] with n hn
  exact le_trans (hbias n hn) (le_abs_self _)

/-- **T7d (low side, mirror).** Under `∑_{s_n = −1} η_n = ∞`, the soft low ramp has divergent
weight and bias `≤ −½` on its support; `0` is not a limit point.
Scope: single-market (real sequences).
Source: [[trust-lab-2-inventory]] 046 (mirror); K5
Kind: P
Fidelity: variant (side-density hypothesis)
Hyps: (a) none beyond the side-density hypothesis -/
theorem dither_low_kills {δ : ℚ} (hδ : 0 < δ)
    (hdens : Tendsto (prefixSum (minusMass s η)) atTop atTop) :
    Tendsto (prefixSum (lowRamp δ (dither s η))) atTop atTop ∧
      (∀ n, 0 < prefixSum (lowRamp δ (dither s η)) n →
        weightedBias (lowRamp δ (dither s η)) (dither s η) (invSide (dither s η)) n ≤ -(1 / 2)) ∧
      ¬ HasLimitPoint (weightedBias (lowRamp δ (dither s η)) (dither s η)
          (invSide (dither s η))) 0 := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hc : (0 : ℝ) < min 1 (1 / (δ : ℝ)) := lt_min one_pos (by positivity)
  have hdiv : Tendsto (prefixSum (lowRamp δ (dither s η))) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) (hdens.const_mul_atTop hc)
    rw [← prefixSum_const_mul]
    unfold prefixSum
    exact sum_le_sum fun i _ => lowRamp_ge_minusMass hs hη hδ i
  have hbias : ∀ n, 0 < prefixSum (lowRamp δ (dither s η)) n →
      weightedBias (lowRamp δ (dither s η)) (dither s η) (invSide (dither s η)) n ≤ -(1 / 2) := by
    intro n hn
    unfold weightedBias
    refine (weightedAverage_mem_Icc_of_support (a := -1) (b := -(1 / 2))
      (fun i => ctsInd_nonneg _ _ _) ?_ hn).2
    intro i hi
    have h := (lowRamp_pos_iff hs hη hδ i).1 hi
    have hle : dither s η i ≤ 1 / 2 := by rw [dither_minus h]; linarith [hη i]
    rw [invSide_of_le hle]
    exact ⟨by linarith [(dither_mem hs hη i).1], by linarith⟩
  refine ⟨hdiv, hbias, not_hasLimitPoint_zero_of_eventually_abs_ge (c := 1 / 2) (by norm_num) ?_⟩
  filter_upwards [eventually_prefixSum_pos hdiv] with n hn
  have := hbias n hn
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **T7d (the honest claim).** For every non-summable ditherer (`∑ η_n = ∞`), one of the two
soft one-sided ramps has divergent weight with one-signed bias of size `≥ ½` on its support.
This is K5's corrected form of "the soft high gate kills every non-summable ditherer".
Scope: single-market (real sequences).
Source: [[trust-lab-2-inventory]] 046 ("Flags": the correct claim is "one of the two soft one-sided gates kills it"); K5
Kind: C
Fidelity: variant: the one-sided claim of the source is false; this is the disjunction
Hyps: (a) none beyond non-summability, the source's own hypothesis -/
theorem dither_one_sided_kills {δ : ℚ} (hδ : 0 < δ)
    (hdiv : Tendsto (prefixSum η) atTop atTop) :
    (Tendsto (prefixSum (highRamp δ (dither s η))) atTop atTop ∧
        ∀ n, 0 < prefixSum (highRamp δ (dither s η)) n →
          1 / 2 ≤ weightedBias (highRamp δ (dither s η)) (dither s η) (invSide (dither s η)) n) ∨
      (Tendsto (prefixSum (lowRamp δ (dither s η))) atTop atTop ∧
        ∀ n, 0 < prefixSum (lowRamp δ (dither s η)) n →
          weightedBias (lowRamp δ (dither s η)) (dither s η) (invSide (dither s η)) n
            ≤ -(1 / 2)) := by
  have hsum : prefixSum (fun i => plusMass s η i + minusMass s η i) = prefixSum η := by
    funext n; unfold prefixSum
    exact sum_congr rfl fun i _ => plusMass_add_minusMass hs i
  rcases divergent_or_of_add (plusMass_nonneg hη) (minusMass_nonneg hη) (hsum ▸ hdiv) with h | h
  · obtain ⟨h1, h2, _⟩ := dither_high_kills hs hη hδ h
    exact Or.inl ⟨h1, h2⟩
  · obtain ⟨h1, h2, _⟩ := dither_low_kills hs hη hδ h
    exact Or.inr ⟨h1, h2⟩

end Dither

/-! #### The counterexample to the literal claim (K5) -/

/-- Sides of the sparse ditherer: `+1` on day `0`, `−1` afterwards.
Source: [[trust-lab-2-inventory]] 046 "Flags" (K5)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def sparseSide (n : ℕ) : ℝ := if n = 0 then 1 else -1

/-- Amplitudes of the sparse ditherer: `η_n := 1/(n+3)`, non-summable, each `< ½`.
Source: [[trust-lab-2-inventory]] 046 "Flags" (K5)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def sparseEta (n : ℕ) : ℝ := 1 / ((n : ℝ) + 3)

lemma sparseSide_mem (n : ℕ) : sparseSide n = 1 ∨ sparseSide n = -1 := by
  unfold sparseSide; split_ifs <;> simp

lemma sparseEta_mem (n : ℕ) : 0 < sparseEta n ∧ sparseEta n < 1 / 2 := by
  unfold sparseEta
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · positivity
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith

/-- The sparse ditherer is non-summable: `∑ 1/(n+3) = ∞` (harmonic).
Source: [[trust-lab-2-inventory]] 046 "Flags" (K5)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem sparseEta_divergent : Tendsto (prefixSum sparseEta) atTop atTop := by
  have hharm := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hthird : Tendsto (fun N : ℕ => (1 / 3 : ℝ) * ∑ i ∈ range N, (1 / ((i : ℝ) + 1))) atTop
      atTop := hharm.const_mul_atTop (by norm_num)
  have hmono : Tendsto (fun N : ℕ => ∑ i ∈ range N, sparseEta i) atTop atTop := by
    refine tendsto_atTop_mono (fun N => ?_) hthird
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    unfold sparseEta
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hrw : (1 / 3 : ℝ) * (1 / ((i : ℝ) + 1)) = 1 / (3 * ((i : ℝ) + 1)) := by
      field_simp
    rw [hrw]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  exact hmono.comp (tendsto_add_atTop_nat 1)

/-- **K5 refuted.** The sparse ditherer is a non-summable ditherer whose soft high ramp (any
width `δ > 0`) has total weight `≤ 1`: "the soft high gate kills every non-summable ditherer" is
false as stated; only the disjunction `dither_one_sided_kills` survives.
Scope: single-market (real sequences).
Source: [[trust-lab-2-inventory]] 046 Part 4a (refuted as stated); K5
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem sparseDither_highRamp_sum_le_one {δ : ℚ} (hδ : 0 < δ) (N : ℕ) :
    ∑ i ∈ range N, highRamp δ (dither sparseSide sparseEta) i ≤ 1 := by
  have hterm : ∀ i, highRamp δ (dither sparseSide sparseEta) i ≤ if i = 0 then 1 else 0 := by
    intro i
    by_cases hi : i = 0
    · rw [if_pos hi]; exact ctsInd_le_one _ _ _
    · rw [if_neg hi]
      have hside : sparseSide i = -1 := by simp [sparseSide, hi]
      unfold highRamp
      rw [(ctsInd_eq_zero_iff hδ _ _).2]
      rw [dither_minus hside]
      linarith [(sparseEta_mem i).1]
  calc ∑ i ∈ range N, highRamp δ (dither sparseSide sparseEta) i
      ≤ ∑ i ∈ range N, (if i = 0 then (1 : ℝ) else 0) := sum_le_sum fun i _ => hterm i
    _ ≤ 1 := by
        rw [sum_ite_eq' (range N) 0 (fun _ => (1 : ℝ))]
        split_ifs <;> norm_num

/-- **K5 refuted, prefix-sum form.** The sparse ditherer's high ramp is not divergent although
`∑ η_n = ∞`.
Scope: single-market (real sequences).
Source: [[trust-lab-2-inventory]] 046 (refuted as stated); K5
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem sparseDither_highRamp_not_divergent {δ : ℚ} (hδ : 0 < δ) :
    Tendsto (prefixSum sparseEta) atTop atTop ∧
      ¬ Tendsto (prefixSum (highRamp δ (dither sparseSide sparseEta))) atTop atTop := by
  refine ⟨sparseEta_divergent, fun h => ?_⟩
  obtain ⟨n, hn⟩ := (tendsto_atTop.1 h 2).exists
  have := sparseDither_highRamp_sum_le_one hδ (n + 1)
  simp only [prefixSum] at hn
  linarith

end Cleanroom.Li.LiDiagonal
