import Cleanroom.Udt.UdtPolicyCalc.Defs
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Self-sealing verdicts: the two-state chain (T15)

[[self-sealing-verdicts-and-trembles]] §2: a fixed true one-boxer; the predictor holds a verdict
`v ∈ {1B, 2B}`; the box is filled with probability `1 − ε` under `1B` and `ε` under `2B` (the
*filling tremble*); when filled, the verdict is set to the observed action (one-boxing); when
empty, the verdict stands.

* (a) `step`, `dist` (the `t`-step law of the verdict chain); `oneB_absorbing`;
  `uncorrected_eq : P(still 2B after t) = (1−ε)^t`; `corrected_eq`; `mean_correction_time`
  (`∑ t, t·ε·(1−ε)^{t−1} = 1/ε`).
* (b) The decay variant, **order of operations "update then flip w.p. ρ"** (the source fixes no
  order; the other order gives a different exact form — findings): `stepDecay`, the exact
  stationary distribution `statDecay` with `statDecay_stationary`.
* (c) `perEpisodeValue`: the one-boxer's stationary per-episode value `f(ε, ρ)`.

Package `udt-policy-calc` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPolicyCalc

noncomputable section

namespace SelfSealing

/-- The predictor's verdict about the agent's full-box behaviour.
Source: [[self-sealing-verdicts-and-trembles]] §2 (udt-rep-035)
Kind: D
Fidelity: exact
Hyps: n/a -/
inductive Verdict
  | oneB
  | twoB
  deriving DecidableEq, Fintype

/-- Supporting lemma `Verdict.univ_eq` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem Verdict.univ_eq : (Finset.univ : Finset Verdict) = {Verdict.oneB, Verdict.twoB} := by
  ext v
  cases v <;> simp

/-- Supporting lemma `Verdict.sum_eq` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem Verdict.sum_eq {M : Type} [AddCommMonoid M] (g : Verdict → M) :
    ∑ v, g v = g Verdict.oneB + g Verdict.twoB := by
  rw [Verdict.univ_eq, Finset.sum_pair (by decide)]

/-- **The base chain (a true one-boxer, filling tremble `ε`).** From `1B`: filled (`1 − ε`) →
observed one-boxing → confirmed; empty (`ε`) → stands: absorbing. From `2B`: filled (`ε`) →
corrected to `1B`; empty (`1 − ε`) → stands.
Source: [[self-sealing-verdicts-and-trembles]] §2 (udt-rep-035(a))
Kind: D
Fidelity: exact
Hyps: n/a -/
def step (ε : ℝ) : Verdict → Verdict → ℝ
  | .oneB, .oneB => 1
  | .oneB, .twoB => 0
  | .twoB, .oneB => ε
  | .twoB, .twoB => 1 - ε

/-- The law of the verdict after `t` episodes, started from `v₀`.
Source: [[self-sealing-verdicts-and-trembles]] §2 (udt-rep-035(a))
Kind: D
Fidelity: exact
Hyps: n/a -/
def dist (ε : ℝ) (v₀ : Verdict) : ℕ → Verdict → ℝ
  | 0, v => if v = v₀ then 1 else 0
  | t + 1, v => ∑ v', dist ε v₀ t v' * step ε v' v

/-- **T15(a).** `1B` is absorbing: started from `1B`, the verdict is `1B` forever.
Source: [[self-sealing-verdicts-and-trembles]] §2 ("`v = 1B` is absorbing") (udt-rep-035(a))
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem oneB_absorbing (ε : ℝ) (t : ℕ) :
    dist ε .oneB t .oneB = 1 ∧ dist ε .oneB t .twoB = 0 := by
  induction t with
  | zero => simp [dist]
  | succ t ih =>
    simp only [dist, Verdict.sum_eq, ih.1, ih.2, step]
    norm_num

/-- **T15(a), the identity.** Started from the wrong verdict `2B`, the probability of being still
uncorrected after `t` episodes is `(1 − ε)^t`.
Source: [[self-sealing-verdicts-and-trembles]] §2 ("`v = 2B` escapes only via the tremble") (udt-rep-035(a))
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem uncorrected_eq (ε : ℝ) (t : ℕ) : dist ε .twoB t .twoB = (1 - ε) ^ t := by
  induction t with
  | zero => simp [dist]
  | succ t ih =>
    simp only [dist, Verdict.sum_eq, ih, step]
    have h1 : dist ε .twoB t .oneB * 0 = 0 := mul_zero _
    rw [h1, zero_add, pow_succ]

/-- **T15(a).** Started from `2B`, the probability of having been corrected by episode `t` is
`1 − (1 − ε)^t`.
Source: [[self-sealing-verdicts-and-trembles]] §2 (udt-rep-035(a))
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem corrected_eq (ε : ℝ) (t : ℕ) : dist ε .twoB t .oneB = 1 - (1 - ε) ^ t := by
  induction t with
  | zero => simp [dist]
  | succ t ih =>
    simp only [dist, Verdict.sum_eq, ih, uncorrected_eq, step]
    ring

/-- **T15(a), the mean correction time** (stretch). For `0 < ε < 1`, the expected first correction
time `∑_{t ≥ 1} t·ε·(1−ε)^{t−1}` (written with `t = k + 1`) is `1/ε`.
Source: [[self-sealing-verdicts-and-trembles]] §2 ("Mean vindication time `1/ε` episodes") (udt-rep-035(a))
Kind: P
Fidelity: exact
Hyps: (a) `0 < ε < 1` -/
theorem mean_correction_time {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ∑' k : ℕ, ((k : ℝ) + 1) * ε * (1 - ε) ^ k = 1 / ε := by
  have hr : ‖(1 - ε)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hs1 : Summable (fun k : ℕ => (k : ℝ) * (1 - ε) ^ k) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  have hs2 : Summable (fun k : ℕ => (1 - ε) ^ k) :=
    summable_geometric_of_lt_one (by linarith) (by linarith)
  have hfun : (fun k : ℕ => ((k : ℝ) + 1) * ε * (1 - ε) ^ k) =
      fun k : ℕ => ε * ((k : ℝ) * (1 - ε) ^ k + (1 - ε) ^ k) := by
    funext k
    ring
  rw [hfun, tsum_mul_left, hs1.tsum_add hs2, tsum_coe_mul_geometric_of_norm_lt_one hr,
    tsum_geometric_of_lt_one (by linarith) (by linarith)]
  have hε : ε ≠ 0 := h0.ne'
  have : (1 : ℝ) - (1 - ε) = ε := by ring
  rw [this]
  field_simp
  ring

/-! ### (b) The decay variant, "update then flip with probability ρ" -/

/-- **The decay chain, order "update then flip w.p. `ρ`".** `P(1B → 2B) = ρ`,
`P(2B → 1B) = ε(1 − ρ) + (1 − ε)ρ`. (The other order, "flip then update", gives
`P(1B → 2B) = ρ(1 − ε)`, `P(2B → 1B) = ρ + (1 − ρ)ε` and a different exact stationary law —
findings; the source fixes no order.)
Source: [[self-sealing-verdicts-and-trembles]] §2 "Verdict-decay variant" (udt-rep-035(b))
Kind: D
Fidelity: variant: one of the two orders of operations the source leaves open
Hyps: n/a -/
def stepDecay (ε ρ : ℝ) : Verdict → Verdict → ℝ
  | .oneB, .oneB => 1 - ρ
  | .oneB, .twoB => ρ
  | .twoB, .oneB => ε * (1 - ρ) + (1 - ε) * ρ
  | .twoB, .twoB => 1 - (ε * (1 - ρ) + (1 - ε) * ρ)

/-- The exact stationary distribution of `stepDecay`: `π(2B) = ρ / (2ρ + ε − 2ερ)`,
`π(1B) = 1 − π(2B)`. To first order in small `ε, ρ` the odds are the source's `ρ : (ρ + ε)`.
Source: [[self-sealing-verdicts-and-trembles]] §2, §5 item 1 (udt-rep-035(b))
Kind: D
Fidelity: exact (for the chosen order)
Hyps: n/a -/
def statDecay (ε ρ : ℝ) : Verdict → ℝ
  | .oneB => 1 - ρ / (2 * ρ + ε - 2 * ε * ρ)
  | .twoB => ρ / (2 * ρ + ε - 2 * ε * ρ)

/-- Supporting lemma `decay_denom_pos` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem decay_denom_pos {ε ρ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hρ0 : 0 < ρ) :
    0 < 2 * ρ + ε - 2 * ε * ρ := by nlinarith

/-- **T15(b).** `statDecay` is stationary for `stepDecay`: `∑ v', π v' · P(v' → v) = π v`.
Source: [[self-sealing-verdicts-and-trembles]] §5 item 1 ("exact stationary distribution") (udt-rep-035(b))
Kind: P
Fidelity: exact (for the "update then flip" order)
Hyps: (a) `0 < ε < 1`, `0 < ρ` (the denominator is positive) -/
theorem statDecay_stationary {ε ρ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hρ0 : 0 < ρ) (v : Verdict) :
    ∑ v', statDecay ε ρ v' * stepDecay ε ρ v' v = statDecay ε ρ v := by
  have hD := (decay_denom_pos hε0 hε1 hρ0).ne'
  cases v <;> simp only [Verdict.sum_eq, statDecay, stepDecay]
  · linear_combination ρ * mul_inv_cancel₀ hD
  · linear_combination (-ρ) * mul_inv_cancel₀ hD

/-- `statDecay` sums to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem statDecay_sum (ε ρ : ℝ) : ∑ v, statDecay ε ρ v = 1 := by
  simp only [Verdict.sum_eq, statDecay]
  ring

/-! ### (c) The stationary per-episode value -/

/-- **T15(c).** The one-boxer's stationary expected per-episode value:
`f(ε, ρ) = π(1B)·(1−ε)·10⁶ + π(2B)·ε·10⁶` (filled with probability `1 − ε` under the right
verdict, `ε` under the wrong one; a one-boxer gets `10⁶` exactly when the box is filled).
Source: [[self-sealing-verdicts-and-trembles]] §5 item 1 (udt-rep-035(c))
Kind: D
Fidelity: exact (for the "update then flip" order)
Hyps: n/a -/
def perEpisodeValue (ε ρ : ℝ) : ℝ :=
  statDecay ε ρ .oneB * (1 - ε) * 1000000 + statDecay ε ρ .twoB * ε * 1000000

/-- `f(ε, ρ)` as one rational function.
Source: [[self-sealing-verdicts-and-trembles]] §5 item 1 (udt-rep-035(c))
Kind: L
Fidelity: exact
Hyps: (a) `0 < ε < 1`, `0 < ρ` -/
theorem perEpisodeValue_eq {ε ρ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hρ0 : 0 < ρ) :
    perEpisodeValue ε ρ =
      1000000 * ((ρ + ε - 2 * ε * ρ) * (1 - ε) + ρ * ε) / (2 * ρ + ε - 2 * ε * ρ) := by
  have hD := (decay_denom_pos hε0 hε1 hρ0).ne'
  simp only [perEpisodeValue, statDecay]
  linear_combination (-(1000000 * (1 - ε))) * mul_inv_cancel₀ hD

end SelfSealing

end

end Cleanroom.Udt.UdtPolicyCalc
