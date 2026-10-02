import Cleanroom.Li.LiDiagonal.Agent
import Cleanroom.Li.LiPseudorandom.Family
import Cleanroom.Li.LiPseudorandom.Computable
import Cleanroom.Found.LiQuoteLane.Feature
import Cleanroom.Found.LiAsympCalc.LimitPoint
import Mathlib.Analysis.PSeries

/-!
# `li-diagonal` · Baseline: the prediction-blind defector and the self-referential contrast (T8b, T8a corollary)

bli-soto-a-066/067's two agents against a logical inductor `P` that is fed the play:

* **T8b, the baseline** (`blind_baseline`): the agent that defects by `li-pseudorandom`'s family of
  record `truthStar a g q` — a pattern pseudorandom relative to the inductor's own generable
  weightings, at frequency `q` — earns reward `𝟙[defect] / P_n(D_n)` whose running average tends
  to `1`. Composition: `truthStar_learned` (`thm:benford`: `P_n(D_n) → q`) and the density
  `cesaro (truthR x) → q` (`truthStar_cesaro`, the family's own pseudorandomness at the uniform
  weighting, `pgenerableWeighting_const`), through the Cesàro calculus. Over the inductor
  instance for the LIA on `atomDP`; the instance is li-pseudorandom's OPEN T7, so the
  hypothesis-free corollary `blind_baseline_of_computable` is listed open here.
* **T8a's corollary** (`agent_reward_limit_point`): the agent of `AgentCoupling` at the threshold
  `p_n = 1/(2(n+1))` — "defect iff `1/P_n(D_n) > 2(n+1)`" — defects infinitely often
  (`agent_defects_io`), and on those days its running-average reward exceeds `2`: a limit point
  `≥ 2` against the baseline's `1`. Lean's `1/0 = 0` makes the reward `0` where the source's is
  undefined, so the statement carries the disjunct `P_n(D_n) = 0`; the clean form under
  `0 < P_n(D_n)` is `agent_reward_limit_point_of_pos`.

Scope: single-market (one inductor, one process); the coupling is (c) as in `Agent.lean`.
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction Cleanroom.Found.LiAsympCalc Cleanroom.Li.LiPseudorandom
open Filter Topology Finset

/-! ### Cesàro calculus (local) -/

/-- Cesàro means are additive.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma cesaro_add (x y : ℕ → ℝ) (N : ℕ) :
    cesaro (fun n => x n + y n) N = cesaro x N + cesaro y N := by
  simp only [cesaro, sum_add_distrib, add_div]

/-- Cesàro means commute with a constant factor.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma cesaro_const_mul (c : ℝ) (x : ℕ → ℝ) (N : ℕ) :
    cesaro (fun n => c * x n) N = c * cesaro x N := by
  simp only [cesaro, ← mul_sum, mul_div_assoc]

/-- `|truthR x n| ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma truthR_abs_le_one (x : ℕ → Bool) (n : ℕ) : |truthR x n| ≤ 1 := by
  unfold truthR; split_ifs <;> simp

/-- The uniform weighting `EF.const 1` is divergent on every history.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem const_one_divergent (P : History) : DivergentWeighting (fun _ => EF.const 1) P := by
  refine ⟨fun n => by simp, ?_⟩
  show Tendsto (prefixSum fun _ => (EF.const (1 : ℚ)).denote P) atTop atTop
  simp only [EF.denote_const, Rat.cast_one]
  exact tendsto_prefixSum_one

/-! ### T8b. The baseline -/

/-- **Density of the family of record.** The Cesàro frequency of `truthStar a g p` tends to `p`:
the family's pseudorandomness at the uniform weighting (generable by `pgenerableWeighting_const`,
divergent by `const_one_divergent`).
Scope: single-market (the LIA over `atomDP`).
Source: [[bli-soto-a-inventory]] 067 ("the LI learns its frequency"); li-pseudorandom `truthStar_pseudorandom_all`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem truthStar_cesaro (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    Tendsto (cesaro (truthR (truthStar a g p))) atTop (𝓝 p) := by
  have h := truthStar_pseudorandom_all a g hg p hp (fun _ => EF.const 1)
    (Cleanroom.Found.LiQuoteLane.pgenerableWeighting_const 1) (const_one_divergent _)
  simp only [EF.denote_const, Rat.cast_one] at h
  unfold AsympEq at h
  have h' : Tendsto (weightedAverage (fun _ => (1 : ℝ)) (truthR (truthStar a g p))) atTop
      (𝓝 p) := by
    simpa using h.add_const p
  have h2 : Tendsto (fun N => cesaro (truthR (truthStar a g p)) (N + 1)) atTop (𝓝 p) := by
    refine h'.congr fun N => ?_
    rw [cesaro_eq_weightedAverage_one _ (by omega), Nat.add_sub_cancel]
  exact (tendsto_add_atTop_iff_nat 1).1 h2

/-- The per-day reward of a prediction-blind defector with defection stream `x`:
`𝟙[x n] / P_n(⌜D_n⌝)` with `D_n := atom (a n)`; `0` on cooperation days. (Lean's `1/0 = 0`: at a
zero price the reward is `0` where the source's is undefined; irrelevant once `P_n(D_n) → q > 0`.)
Source: [[bli-soto-a-inventory]] 066, 067
Kind: D
Fidelity: exact (up to the `1/0` convention)
Hyps: n/a -/
noncomputable def blindReward (P : History) (a : ℕ → ℕ) (x : ℕ → Bool) (n : ℕ) : ℝ :=
  truthR x n / P n (atomFamily a n)

/-- **T8b, the baseline.** Against the LIA over its own deciding process, the agent defecting by
the family of record at frequency `q ∈ (0, 1]` has running-average reward `→ 1`: the inductor's
price of each `D_n` tends to `q` (`truthStar_learned`, `thm:benford`) while the defection
density is `q` (`truthStar_cesaro`), so `cesaro (𝟙[x n] / P_n(D_n)) → q · (1/q) = 1`.
Scope: single-market (the LIA over `atomDP a (truthStar a g q) g`); over the inductor instance
(li-pseudorandom's OPEN T7 for the family of record).
Source: [[bli-soto-a-inventory]] 067 ("`Σ_{defection days} 1/P_n(D_n) / N → 1`"); 066 (i)
Kind: C
Fidelity: exact
Hyps: (a) `hcodes` (the atom family's e.c. certificate, discharged for `a = id` in li-pseudorandom); the `IsLogicalInductor` instance is li-pseudorandom's OPEN T7 (status `partial: over OPEN computability`) -/
theorem blind_baseline (a g : ℕ → ℕ) (ha : Function.Injective a) (hg : ∀ j, j < g j)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (hcodes : MachineSentenceCodes (atomFamily a))
    [IsLogicalInductor (liaHistory (atomDP a (truthStar a g q) g))
      (atomDP a (truthStar a g q) g)] :
    Tendsto (cesaro (blindReward (liaHistory (atomDP a (truthStar a g q) g)) a
      (truthStar a g q))) atTop (𝓝 1) := by
  set P := liaHistory (atomDP a (truthStar a g q) g) with hP
  set x := truthStar a g q with hx
  have hlearn := truthStar_learned a g ha hg q ⟨hq0.le, hq1⟩ hcodes
  unfold AsympEq at hlearn
  have hπ : Tendsto (fun n => P n (atomFamily a n)) atTop (𝓝 q) := by
    simpa using hlearn.add_const q
  have hinv : Tendsto (fun n => 1 / P n (atomFamily a n)) atTop (𝓝 (1 / q)) :=
    tendsto_const_nhds.div hπ hq0.ne'
  have herr : Tendsto (fun n => 1 / P n (atomFamily a n) - 1 / q) atTop (𝓝 0) := by
    simpa using hinv.sub_const (1 / q)
  have hdens := truthStar_cesaro a g hg q ⟨hq0.le, hq1⟩
  have hdecomp : ∀ N, cesaro (blindReward P a x) N =
      (1 / q) * cesaro (truthR x) N +
        cesaro (fun n => truthR x n * (1 / P n (atomFamily a n) - 1 / q)) N := by
    intro N
    rw [← cesaro_const_mul, ← cesaro_add]
    congr 1
    funext n
    simp only [blindReward]
    ring
  have hnull : Tendsto (cesaro (fun n => truthR x n * (1 / P n (atomFamily a n) - 1 / q)))
      atTop (𝓝 0) := by
    apply tendsto_cesaro
    have habs : Tendsto (fun n => |1 / P n (atomFamily a n) - 1 / q|) atTop (𝓝 0) := by
      simpa using herr.abs
    have hb : ∀ n, |truthR x n * (1 / P n (atomFamily a n) - 1 / q)| ≤
        |1 / P n (atomFamily a n) - 1 / q| := by
      intro n
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (truthR_abs_le_one x n)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun n => -|1 / P n (atomFamily a n) - 1 / q|)
      (h := fun n => |1 / P n (atomFamily a n) - 1 / q|)
      (by simpa using habs.neg) habs (fun n => (abs_le.1 (hb n)).1) (fun n => (abs_le.1 (hb n)).2)
  have hlim := (hdens.const_mul (1 / q)).add hnull
  have hval : (1 / q) * q + 0 = 1 := by rw [one_div_mul_cancel hq0.ne', add_zero]
  rw [hval] at hlim
  exact hlim.congr fun N => (hdecomp N).symm

/-- **T8b over the computable instance** (rests on li-pseudorandom's OPEN `starDP_computable`,
through `truthStar_isLogicalInductor`; listed in `li-diagonal-open.txt` for that reason): the
baseline with no inductor hypothesis, at rational `q ∈ (0, 1]`.
Scope: single-market; `partial: over OPEN computability (li-pseudorandom T7)`.
Source: [[bli-soto-a-inventory]] 067; li-pseudorandom `truthStar_isLogicalInductor`
Kind: C
Fidelity: exact
Hyps: (a) `hcodes`; the instance rests on the OPEN T7 of li-pseudorandom -/
theorem blind_baseline_of_computable (a g : ℕ → ℕ) (ha : Computable a) (hg : Computable g)
    (hinj : Function.Injective a) (hg' : ∀ j, j < g j) (q : ℚ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hcodes : MachineSentenceCodes (atomFamily a)) :
    Tendsto (cesaro (blindReward (liaHistory (atomDP a (truthStar a g (q : ℝ)) g)) a
      (truthStar a g (q : ℝ)))) atTop (𝓝 1) :=
  haveI := truthStar_isLogicalInductor a g ha hg q
  blind_baseline a g hinj hg' (q : ℝ) (by exact_mod_cast hq0) (by exact_mod_cast hq1) hcodes

/-! ### T8a's corollary: the self-referential agent's reward has a limit point `≥ 2` -/

/-- The source's threshold `1/(2(n+1))`: "defect iff `1/P_n(D_n) > 2(n+1)`" (the source's `2n`
with days counted from `1`).
Source: [[bli-soto-a-inventory]] 066 (ii)
Kind: D
Fidelity: exact (indexing from day `0`)
Hyps: n/a -/
def halfHarmonic (n : ℕ) : ℚ := 1 / (2 * ((n : ℚ) + 1))

/-- The per-day reward of the coupled agent: `1/P_n(D_n)` on defection days (`P_n(D_n) < p_n`),
`0` on cooperation days. Lean's `1/0 = 0` applies at a zero price (where the source's reward is
undefined).
Source: [[bli-soto-a-inventory]] 066
Kind: D
Fidelity: exact (up to the `1/0` convention)
Hyps: n/a -/
noncomputable def agentReward (P : History) (D : ℕ → Sentence) (p : ℕ → ℚ) (n : ℕ) : ℝ :=
  if P n (D n) < (p n : ℝ) then 1 / P n (D n) else 0

/-- The threshold `1/(2(n+1))` is non-summable (half the harmonic series).
Source: [[bli-soto-a-inventory]] 066 (ii) ("`Σ 1/(2n) = ∞`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem halfHarmonic_divergent :
    Tendsto (prefixSum fun n => (halfHarmonic n : ℝ)) atTop atTop := by
  have hharm := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hhalf : Tendsto (fun N : ℕ => (1 / 2 : ℝ) * ∑ i ∈ range N, (1 / ((i : ℝ) + 1))) atTop
      atTop := hharm.const_mul_atTop (by norm_num)
  have heq : ∀ N : ℕ, (1 / 2 : ℝ) * ∑ i ∈ range N, (1 / ((i : ℝ) + 1)) =
      ∑ i ∈ range N, (halfHarmonic i : ℝ) := by
    intro N
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [halfHarmonic]
    push_cast
    field_simp
  have h2 : Tendsto (fun N : ℕ => ∑ i ∈ range N, (halfHarmonic i : ℝ)) atTop atTop :=
    hhalf.congr heq
  exact h2.comp (tendsto_add_atTop_nat 1)

/-- Prices of a logical inductor are nonnegative, so the reward stream is nonnegative.
Source: FAF `IsLogicalInductor.price_mem_Icc`
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma agentReward_nonneg (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (D : ℕ → Sentence) (p : ℕ → ℚ) (n : ℕ) : 0 ≤ agentReward P D p n := by
  unfold agentReward
  split_ifs
  · exact div_nonneg zero_le_one (IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n (D n)).1
  · exact le_rfl

/-- **T8a's corollary.** The agent "defect iff `1/P_n(D_n) > 2(n+1)`" (an `AgentCoupling` at the
threshold `halfHarmonic`) defects infinitely often, and on each such day its running-average
reward through that day exceeds `2` — unless the price is exactly `0`, where the source's reward
`1/P_n(D_n)` is undefined (Lean's is `0`). So the average reward has a limit point `≥ 2` in the
sense `∃ᶠ n, 2 < cesaro r (n+1)`, against the baseline's `→ 1` (`blind_baseline`).
Scope: single-market; the coupling is (c) (K7).
Source: [[bli-soto-a-inventory]] 066 (ii) ("hence `A`'s average reward has a limit point `≥ 2`")
Kind: C
Fidelity: exact (with the zero-price disjunct made explicit)
Hyps: (c) the coupling `C` (`decided_by` is the environment's design, K7); (a) the rest -/
theorem agent_reward_limit_point (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (D : ℕ → Sentence) (C : AgentCoupling P DP D halfHarmonic)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ᶠ n in atTop, P n (D n) = 0 ∨ 2 < cesaro (agentReward P D halfHarmonic) (n + 1) := by
  have hdef := agent_defects_io P DP D halfHarmonic C (fun n => by unfold halfHarmonic; positivity)
    halfHarmonic_divergent hworld
  refine hdef.mono fun n hn => ?_
  rcases eq_or_lt_of_le (IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n (D n)).1 with h0 | hpos
  · exact Or.inl h0.symm
  · right
    have hthr : (halfHarmonic n : ℝ) = 1 / (2 * ((n : ℝ) + 1)) := by
      simp only [halfHarmonic]; push_cast; ring
    have hrn : agentReward P D halfHarmonic n = 1 / P n (D n) := by
      unfold agentReward; rw [if_pos hn]
    have hn' : P n (D n) < 1 / (2 * ((n : ℝ) + 1)) := by rw [← hthr]; exact hn
    have hbig : 2 * ((n : ℝ) + 1) < 1 / P n (D n) := by
      rw [lt_div_iff₀ hpos]
      have h2 : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
      calc 2 * ((n : ℝ) + 1) * P n (D n) < 2 * ((n : ℝ) + 1) * (1 / (2 * ((n : ℝ) + 1))) :=
            mul_lt_mul_of_pos_left hn' h2
        _ = 1 := by field_simp
    have hsum : agentReward P D halfHarmonic n ≤
        ∑ i ∈ range (n + 1), agentReward P D halfHarmonic i :=
      single_le_sum (fun i _ => agentReward_nonneg P DP D halfHarmonic i) (mem_range.2 (by omega))
    have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    unfold cesaro
    rw [lt_div_iff₀ hN]
    push_cast
    linarith [hrn, hbig, hsum]

/-- **T8a's corollary, clean form.** Under positive prices the zero-price disjunct disappears:
`∃ᶠ n, 2 < cesaro r (n+1)`.
Scope: single-market; the coupling is (c) (K7).
Source: [[bli-soto-a-inventory]] 066 (ii)
Kind: L
Fidelity: exact
Hyps: (c) the coupling `C`; (a) `hpos` is the source's implicit "the reward is defined" (positive prices) -/
theorem agent_reward_limit_point_of_pos (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (D : ℕ → Sentence) (C : AgentCoupling P DP D halfHarmonic)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (hpos : ∀ n, 0 < P n (D n)) :
    ∃ᶠ n in atTop, 2 < cesaro (agentReward P D halfHarmonic) (n + 1) :=
  (agent_reward_limit_point P DP D C hworld).mono fun n hn =>
    hn.resolve_left (hpos n).ne'

end Cleanroom.Li.LiDiagonal
