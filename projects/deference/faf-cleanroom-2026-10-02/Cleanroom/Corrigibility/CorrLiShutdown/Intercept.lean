import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Basic

/-!
# `corr-li-shutdown` — Intercept (T7): Statement 5's intercept family, not attained

Pure real analysis; no FAF object. The sources' Statement 5 (repaired) says: for every
`f ∈ (0,1)` there is a constant `K_f` with `k₁(N) ≤ r(f,p)·k₀(N) + K_f` for all `N`, where
`r(f,p) = log(1/(1−f)) / log(1 + f(1/p − 1))` is **strictly above the odds** `p/(1−p)` for every
`f > 0` and tends to the odds as `f ↓ 0` while `K_f → ∞`. This file proves:

* `slope_gt_odds` (P): `p/(1−p) < r(f,p)` for every `f ∈ (0,1)`, `p ∈ (0,1)` — Bernoulli's
  inequality in the form `x·log(1/(1−f)) > x·f > log(1 + f·x)` (`Real.log_lt_sub_one_of_pos`
  twice).
* `budgetedWealth` (D) and `budgetedWealth_ge` (P): the per-round wealth recursion of the
  obedience trader, `W_{k+1} = W_k·(1 + f(1/𝗉_k − 1))` on an unjustified defiance (the agent
  priced `φ` at `𝗉_k ≤ p` and was wrong) and `W_k·(1 − f)` on a justified one, dominates
  `(1 + f(1/p − 1))^{k₁}·(1 − f)^{k₀}`.
* `record_inequality` (P): from any wealth cap `W_K ≤ C` the record inequality
  `k₁ ≤ r(f,p)·k₀ + log C / log(1 + f(1/p − 1))` follows, for all `K`.
* `interceptConst_tendsto_top` (P): the intercept `K_f = log C / log(1 + f(1/p − 1))` tends to
  `∞` as `f ↓ 0` for every fixed `C > 1`; `interceptSlope_tendsto_odds` (P): the slope tends to
  the odds `p/(1−p)` as `f ↓ 0` (a squeeze between `1/x` and `(1 + fx)/((1 − f)x)`).
* `no_trader_attains_odds` (L): the "not attained" headline.

**What is not here, and why.** The cap `C` is the criterion's bound on the trader's plausible
worth; its existence over FAF (`IsLogicalInductor.noExploit` for a `PolyFueledTrader` buying
`s_k` shares of `φ_{d_k}` on pressed scheduled days) is T7(e), `stretch`, not built: the
inequality is stated *from* a cap, per trader `f`, and nothing relates the caps across `f`
(the envelope `p/(1−p)·k₀ + Θ(√k₀)` under a uniform cap is counterfactual and is recorded, not
stated). The hidden decidedness hypothesis (H-blind) is the one-way tag: the press on `d_k` is
in stage `d_k` of the agent's process (`Setting.lean`, `pressAtom_mem_stage`). Numerics
(`+460 %` at `f = 0.5`) are not theorems.
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open Real Filter Topology

/-! ## A. The slope and the Bernoulli lemma -/

/-- **The slope of the intercept family** `r(f,p) := log(1/(1−f)) / log(1 + f(1/p − 1))`.
Source: [[corr-wf14-inventory]] 089 (`li-final.md` Statement 5, repaired)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def interceptSlope (f p : ℝ) : ℝ :=
  Real.log (1 / (1 - f)) / Real.log (1 + f * (1 / p - 1))

/-- **The intercept** `K_f(C) := log C / log(1 + f(1/p − 1))` of the family at cap `C`.
Source: [[corr-wf14-inventory]] 089 (Statement 5, `K_f`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def interceptConst (f p C : ℝ) : ℝ :=
  Real.log C / Real.log (1 + f * (1 / p - 1))

/-- The odds `p/(1−p)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def odds (p : ℝ) : ℝ := p / (1 - p)

/-- `1/p − 1 = (1 − p)/p > 0` for `p ∈ (0,1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma one_div_sub_one_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < 1 / p - 1 := by
  rw [sub_pos, lt_div_iff₀ hp0]; linarith

/-- `log(1 + f·x) > 0` for `f, x > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma log_one_add_mul_pos {f x : ℝ} (hf : 0 < f) (hx : 0 < x) : 0 < Real.log (1 + f * x) :=
  Real.log_pos (by nlinarith)

/-- `log(1 + f·x) < f·x` for `f, x > 0` (strict Bernoulli, logarithmic form).
Source: none: infrastructure (Mathlib `Real.log_lt_sub_one_of_pos`)
Kind: L
Fidelity: n/a -/
lemma log_one_add_mul_lt {f x : ℝ} (hf : 0 < f) (hx : 0 < x) :
    Real.log (1 + f * x) < f * x := by
  have h := Real.log_lt_sub_one_of_pos (x := 1 + f * x) (by nlinarith) (by nlinarith)
  linarith

/-- `log(1/(1−f)) > f` for `f ∈ (0,1)`.
Source: none: infrastructure (Mathlib `Real.log_lt_sub_one_of_pos` at `1 − f`)
Kind: L
Fidelity: n/a -/
lemma log_one_div_one_sub_gt {f : ℝ} (hf0 : 0 < f) (hf1 : f < 1) :
    f < Real.log (1 / (1 - f)) := by
  have h1f : 0 < 1 - f := by linarith
  have h := Real.log_lt_sub_one_of_pos h1f (by linarith)
  rw [one_div, Real.log_inv]
  linarith

/-- **The Bernoulli lemma** (T7(a), P): every slope in the family is strictly above the odds,
`p/(1−p) < r(f,p)`, for every `f ∈ (0,1)` and `p ∈ (0,1)`. Proof: with `x := 1/p − 1 > 0`,
`log(1 + f·x) < f·x < x·log(1/(1−f))`, and `p/(1−p) = 1/x`.
Source: [[corr-wf14-inventory]] 089 (Statement 5: "`r(f,p) > p/(1−p)` for every `f > 0`"); [[corr-wf14-2-inventory]] 2-030
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem slope_gt_odds {f p : ℝ} (hf0 : 0 < f) (hf1 : f < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    odds p < interceptSlope f p := by
  set x : ℝ := 1 / p - 1 with hx
  have hxpos : 0 < x := one_div_sub_one_pos hp0 hp1
  have hlogpos : 0 < Real.log (1 + f * x) := log_one_add_mul_pos hf0 hxpos
  have hodds : odds p = 1 / x := by
    rw [odds, hx]
    field_simp
  rw [hodds, interceptSlope, ← hx, lt_div_iff₀ hlogpos, div_mul_eq_mul_div, one_mul,
    div_lt_iff₀ hxpos]
  calc Real.log (1 + f * x) < f * x := log_one_add_mul_lt hf0 hxpos
    _ < Real.log (1 / (1 - f)) * x :=
        mul_lt_mul_of_pos_right (log_one_div_one_sub_gt hf0 hf1) hxpos

/-- **No member of the family has the odds as its slope** (T7(c), the "not attained" headline):
for every `f ∈ (0,1)`, `p/(1−p) < r(f,p)`. The develop file's headline "unjustified defiances
`≤` odds-ratio `×` justified defiances `+ K`" is withdrawn in favour of the family.
Source: [[corr-wf14-inventory]] 089 ("No trader attains the odds slope")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem no_trader_attains_odds {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ f ∈ Set.Ioo (0 : ℝ) 1, odds p < interceptSlope f p :=
  fun _ hf => slope_gt_odds hf.1 hf.2 hp0 hp1

/-- `1/x ≤ r(f,p)` for `f ∈ (0,1)`, with `x := 1/p − 1` (the lower half of the squeeze: `f ≤
log(1/(1−f))` and `log(1 + fx) ≤ fx`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma one_div_le_interceptSlope {f p : ℝ} (hf0 : 0 < f) (hf1 : f < 1) (hp0 : 0 < p)
    (hp1 : p < 1) : 1 / (1 / p - 1) ≤ interceptSlope f p := by
  set x : ℝ := 1 / p - 1 with hx
  have hxpos : 0 < x := one_div_sub_one_pos hp0 hp1
  have hlogpos : 0 < Real.log (1 + f * x) := log_one_add_mul_pos hf0 hxpos
  rw [interceptSlope, ← hx, le_div_iff₀ hlogpos]
  calc 1 / x * Real.log (1 + f * x) ≤ 1 / x * (f * x) :=
        mul_le_mul_of_nonneg_left (log_one_add_mul_lt hf0 hxpos).le (by positivity)
    _ = f := by field_simp
    _ ≤ Real.log (1 / (1 - f)) := (log_one_div_one_sub_gt hf0 hf1).le

/-- `r(f,p) ≤ (1 + fx)/((1 − f)·x)` for `f ∈ (0,1)`, with `x := 1/p − 1` (the upper half of the
squeeze: `log(1/(1−f)) ≤ f/(1−f)` and `fx/(1+fx) ≤ log(1+fx)`, both `Real.log_le_sub_one_of_pos`
/ `Real.one_sub_inv_le_log_of_pos`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma interceptSlope_le {f p : ℝ} (hf0 : 0 < f) (hf1 : f < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    interceptSlope f p ≤ (1 + f * (1 / p - 1)) / ((1 - f) * (1 / p - 1)) := by
  set x : ℝ := 1 / p - 1 with hx
  have hxpos : 0 < x := one_div_sub_one_pos hp0 hp1
  have h1f : 0 < 1 - f := by linarith
  have hlogpos : 0 < Real.log (1 + f * x) := log_one_add_mul_pos hf0 hxpos
  have hbase : 0 < 1 + f * x := by nlinarith
  have hA : Real.log (1 / (1 - f)) ≤ f / (1 - f) := by
    have := Real.log_le_sub_one_of_pos (one_div_pos.mpr h1f)
    calc Real.log (1 / (1 - f)) ≤ 1 / (1 - f) - 1 := this
      _ = f / (1 - f) := by
          field_simp
          ring
  have hB : f * x / (1 + f * x) ≤ Real.log (1 + f * x) := by
    have := Real.one_sub_inv_le_log_of_pos hbase
    calc f * x / (1 + f * x) = 1 - (1 + f * x)⁻¹ := by
          field_simp
          ring
      _ ≤ Real.log (1 + f * x) := this
  rw [interceptSlope, ← hx, div_le_iff₀ hlogpos]
  calc Real.log (1 / (1 - f)) ≤ f / (1 - f) := hA
    _ = (1 + f * x) / ((1 - f) * x) * (f * x / (1 + f * x)) := by
        field_simp
    _ ≤ (1 + f * x) / ((1 - f) * x) * Real.log (1 + f * x) :=
        mul_le_mul_of_nonneg_left hB (by positivity)

/-- **The slope tends to the odds as `f ↓ 0`** (T7(a), P): `r(f,p) → p/(1−p)` along `f → 0⁺`.
Squeeze: `1/x ≤ r(f,p) ≤ (1 + fx)/((1 − f)x)` on `(0,1)` with `x := 1/p − 1`, and the upper bound
is continuous at `f = 0` with value `1/x = odds p`.
Source: [[corr-wf14-inventory]] 089 (`li-final.md` Statement 5: "`r(f,p) → p/(1−p)` as `f ↓ 0`"); audit r1 fidelity N1
Kind: P
Fidelity: exact (the one-sided limit at `0`)
Hyps: (a) -/
theorem interceptSlope_tendsto_odds {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun f => interceptSlope f p) (𝓝[>] 0) (𝓝 (odds p)) := by
  set x : ℝ := 1 / p - 1 with hx
  have hxpos : 0 < x := one_div_sub_one_pos hp0 hp1
  have hodds : odds p = 1 / x := by
    rw [odds, hx]
    field_simp
  rw [hodds]
  have hmem : ∀ᶠ f in 𝓝[>] (0 : ℝ), 0 < f ∧ f < 1 := by
    have h1 : ∀ᶠ f in 𝓝[>] (0 : ℝ), 0 < f := self_mem_nhdsWithin
    have h2 : ∀ᶠ f in 𝓝[>] (0 : ℝ), f < 1 :=
      (eventually_lt_nhds (zero_lt_one' ℝ)).filter_mono nhdsWithin_le_nhds
    exact h1.and h2
  have hupper : Tendsto (fun f : ℝ => (1 + f * x) / ((1 - f) * x)) (𝓝[>] 0) (𝓝 (1 / x)) := by
    have hnum : Tendsto (fun f : ℝ => 1 + f * x) (𝓝 0) (𝓝 (1 + 0 * x)) :=
      (by fun_prop : Continuous fun f : ℝ => 1 + f * x).tendsto 0
    have hden : Tendsto (fun f : ℝ => (1 - f) * x) (𝓝 0) (𝓝 ((1 - 0) * x)) :=
      (by fun_prop : Continuous fun f : ℝ => (1 - f) * x).tendsto 0
    have h := hnum.div hden (by simp; exact hxpos.ne')
    simp only [zero_mul, add_zero, sub_zero, one_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [hmem] with f hf
    exact one_div_le_interceptSlope hf.1 hf.2 hp0 hp1
  · filter_upwards [hmem] with f hf
    exact interceptSlope_le hf.1 hf.2 hp0 hp1

/-! ## B. The budgeted wealth chain and the record inequality -/

/-- **The obedience trader's budgeted wealth** `W_K`: `W_0 = 1`; on round `k`, if the defiance
was unjustified (`viol k`, the agent priced `φ_{d_k}` at `𝗉_k` and was wrong) the wealth is
multiplied by `1 + f(1/𝗉_k − 1)`, otherwise by `1 − f`. The fraction `f` of wealth is bet each
round. **Two-kind record** (audit r1 fidelity N2): every non-violation round multiplies the
wealth by `1 − f`, whereas the sources' record (`li-final.md` S4, Statement 5) has a third kind —
defied and wrong with the credence in `(q − 2δ, q)`, factor `1 + f(1/𝗉 − 1) ≥ 1`, counted in
neither `k₀` nor `k₁`. The lower bound survives for the real trader (those factors are `≥ 1`),
but this chain cannot be instantiated on it without dropping those rounds.
Source: [[corr-wf14-inventory]] 089 (`li-final.md` §Proof of Statement 5, "per-round factors"); [[corr-wf14-2-inventory]] 2-081 (the chain hand-checked)
Kind: D
Fidelity: variant: two-kind record (the sources' third kind, factor `≥ 1`, is not modelled); the trader itself is T7(e), not built
Hyps: n/a -/
noncomputable def budgetedWealth (f : ℝ) (price : ℕ → ℝ) (viol : ℕ → Bool) : ℕ → ℝ
  | 0 => 1
  | k + 1 => budgetedWealth f price viol k * (if viol k then 1 + f * (1 / price k - 1) else 1 - f)

/-- The count `k₁(K)` of unjustified defiances among rounds `< K`.
Source: [[corr-wf14-inventory]] 082 (S4, "`k₁(N)` unjustified defiances")
Kind: D
Fidelity: exact
Hyps: n/a -/
def countUnjustified (viol : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => countUnjustified viol k + (if viol k then 1 else 0)

/-- The count `k₀(K)` of justified defiances among rounds `< K`.
Source: [[corr-wf14-inventory]] 082 (S4, "`k₀(N)` justified defiances")
Kind: D
Fidelity: exact
Hyps: n/a -/
def countJustified (viol : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => countJustified viol k + (if viol k then 0 else 1)

/-- **The product lower bound** (T7(b), P): if on every unjustified defiance the agent's price
`𝗉_k` satisfies `0 < 𝗉_k ≤ p`, then `W_K ≥ (1 + f(1/p − 1))^{k₁(K)}·(1 − f)^{k₀(K)}` for every
`K` (`0 ≤ f < 1`, `0 < p ≤ 1`).
Source: [[corr-wf14-inventory]] 089 (§Proof of Statement 5: "per-round factors give `W_K ≥ (1 + f(1/p − 1))^{k₁}(1 − f)^{k₀}`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem budgetedWealth_ge {f p : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hp0 : 0 < p)
    (price : ℕ → ℝ) (viol : ℕ → Bool)
    (hprice : ∀ k, viol k = true → 0 < price k ∧ price k ≤ p) :
    ∀ K, (1 + f * (1 / p - 1)) ^ countUnjustified viol K * (1 - f) ^ countJustified viol K ≤
      budgetedWealth f price viol K := by
  have hbase : 0 ≤ 1 + f * (1 / p - 1) := by
    have : 0 < 1 / p := by positivity
    nlinarith
  have h1f : 0 ≤ 1 - f := by linarith
  intro K
  induction K with
  | zero => simp [budgetedWealth, countUnjustified, countJustified]
  | succ k ih =>
    simp only [budgetedWealth, countUnjustified, countJustified]
    by_cases hv : viol k = true
    · simp only [hv, if_true, pow_succ, add_zero]
      obtain ⟨hpk0, hpkp⟩ := hprice k hv
      have hfac : 1 + f * (1 / p - 1) ≤ 1 + f * (1 / price k - 1) := by
        have : 1 / p ≤ 1 / price k := one_div_le_one_div_of_le hpk0 hpkp
        nlinarith
      have hW : 0 ≤ budgetedWealth f price viol k :=
        le_trans (by positivity) ih
      calc (1 + f * (1 / p - 1)) ^ countUnjustified viol k * (1 + f * (1 / p - 1)) *
            (1 - f) ^ countJustified viol k
          = ((1 + f * (1 / p - 1)) ^ countUnjustified viol k *
              (1 - f) ^ countJustified viol k) * (1 + f * (1 / p - 1)) := by ring
        _ ≤ budgetedWealth f price viol k * (1 + f * (1 / p - 1)) :=
            mul_le_mul_of_nonneg_right ih hbase
        _ ≤ budgetedWealth f price viol k * (1 + f * (1 / price k - 1)) :=
            mul_le_mul_of_nonneg_left hfac hW
    · have hv' : viol k = false := by simpa using hv
      simp only [hv']
      have hW : 0 ≤ budgetedWealth f price viol k :=
        le_trans (by positivity) ih
      calc (1 + f * (1 / p - 1)) ^ countUnjustified viol k *
            ((1 - f) ^ countJustified viol k * (1 - f))
          = ((1 + f * (1 / p - 1)) ^ countUnjustified viol k *
              (1 - f) ^ countJustified viol k) * (1 - f) := by ring
        _ ≤ budgetedWealth f price viol k * (1 - f) := mul_le_mul_of_nonneg_right ih h1f

/-- **The record inequality from a wealth cap** (T7(b), P): if `W_K ≤ C` (so `C > 0` automatically, the wealth being positive), then
`k₁(K) ≤ r(f,p)·k₀(K) + K_f(C)`. Logarithms of `budgetedWealth_ge`: `k₁·log(1 + f x) +
k₀·log(1 − f) ≤ log C` with `log(1 + f x) > 0` and `log(1 − f) = −log(1/(1−f))`.
Source: [[corr-wf14-inventory]] 089 (§Proof of Statement 5: "logarithms give `k₁ ≤ r(f,p) k₀ + K_f`")
Kind: P
Fidelity: variant: two-kind record (see `budgetedWealth`); per trader `f`, from a cap; the cap's existence over FAF is T7(e), not built
Hyps: (a) as the abstract lemma "cap ⇒ record inequality" (`hcap` named); **(c)** as Statement 5: the cap is the criterion's bound on an unmodeled trader (audit r1 adversarial N4) -/
theorem record_inequality {f p C : ℝ} (hf0 : 0 < f) (hf1 : f < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (price : ℕ → ℝ) (viol : ℕ → Bool)
    (hprice : ∀ k, viol k = true → 0 < price k ∧ price k ≤ p) (K : ℕ)
    (hcap : budgetedWealth f price viol K ≤ C) :
    (countUnjustified viol K : ℝ) ≤
      interceptSlope f p * countJustified viol K + interceptConst f p C := by
  set x : ℝ := 1 / p - 1 with hx
  have hxpos : 0 < x := one_div_sub_one_pos hp0 hp1
  have hlogpos : 0 < Real.log (1 + f * x) := log_one_add_mul_pos hf0 hxpos
  have hbase : 0 < 1 + f * x := by nlinarith
  have h1f : 0 < 1 - f := by linarith
  have hge := budgetedWealth_ge hf0.le hf1 hp0 price viol hprice K
  rw [← hx] at hge
  have hprodpos : 0 < (1 + f * x) ^ countUnjustified viol K * (1 - f) ^ countJustified viol K :=
    by positivity
  have hlog := Real.log_le_log hprodpos (hge.trans hcap)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  have hneg : Real.log (1 - f) = -Real.log (1 / (1 - f)) := by
    rw [one_div, Real.log_inv, neg_neg]
  rw [hneg] at hlog
  -- `k₁·L ≤ log C + k₀·log(1/(1−f))`, divide by `L > 0`
  unfold interceptSlope interceptConst
  rw [← hx, div_mul_eq_mul_div, ← add_div, le_div_iff₀ hlogpos]
  linarith

/-! ## C. The intercept diverges as `f ↓ 0` -/

/-- **The intercept tends to `∞` as `f ↓ 0`** (T7(a)): for fixed `p ∈ (0,1)` and `C > 1`,
`K_f(C) = log C / log(1 + f(1/p − 1)) → ∞` as `f → 0⁺` — the family's constants are not
uniform in `f`.
Source: [[corr-wf14-inventory]] 089 ("the intercept `K_f` grows like `1/f` for fixed `C`")
Kind: P
Fidelity: exact (divergence; the `1/f` rate is not stated)
Hyps: (a) -/
theorem interceptConst_tendsto_top {p C : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hC : 1 < C) :
    Tendsto (fun f => interceptConst f p C) (𝓝[>] 0) atTop := by
  set x : ℝ := 1 / p - 1 with hx
  have hxpos : 0 < x := one_div_sub_one_pos hp0 hp1
  have hlogC : 0 < Real.log C := Real.log_pos hC
  -- the denominator tends to `0` from above
  have hden : Tendsto (fun f : ℝ => Real.log (1 + f * x)) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : Continuous fun f : ℝ => 1 + f * x := by fun_prop
      have h1 : Tendsto (fun f : ℝ => 1 + f * x) (𝓝[>] 0) (𝓝 1) := by
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
        simpa using this
      have h2 := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
      simpa [Real.log_one, Function.comp_def] using h2
    · filter_upwards [self_mem_nhdsWithin] with f hf
      exact log_one_add_mul_pos hf hxpos
  have hinv : Tendsto (fun y : ℝ => Real.log C / y) (𝓝[>] 0) atTop := by
    have hinv0 : Tendsto (fun y : ℝ => y⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
    simpa [div_eq_mul_inv] using hinv0.const_mul_atTop hlogC
  exact hinv.comp hden

end Cleanroom.Corrigibility.CorrLiShutdown
