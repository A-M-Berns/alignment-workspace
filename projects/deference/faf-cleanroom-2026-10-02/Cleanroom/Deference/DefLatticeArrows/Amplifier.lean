import Cleanroom.Deference.DefLatticeArrows.Packages
import Cleanroom.Found.LiAsympCalc.Amplifier

/-!
# T8 — The amplifier: soft cuts come free, the gap-bet kill, the centered instances, the pinch

Package `def-lattice-arrows`, file 13. Measure model (`e ∼ Unif[0,1]`, layer-wise expectation
`g = amp c` from li-asymp-calc `Defs.lean`): every statement is an `intervalIntegral`
identity or inequality; **Fidelity: variant: measure model, not a LUV statement** throughout.
Already in li-asymp-calc and cited, not redone: the hard cut integrals and inequalities
(`integral_amp_upper/lower`, `amp_upper_cut`, `amp_lower_cut`), affine rigidity, the
impostor.

New here:
* **(i) soft cuts come free**: `∫_0^1 (amp c e − t) ctsInd δ e t ≥ 0` and the mirrored lower
  soft cut, for `c ≥ 0`, `t ∈ [0,1]`, `δ > 0` — by the piecewise-linear closed form (the wiki's
  averaging identity is not needed). This is why *parallel* cuts, soft or hard, cannot give
  the tower: the amplifier passes them all.
* **(ii) the gap-bet kill**: `∫_a^b (amp c e − e) = c (b − a)(a + b − 1)`, nonzero for `c > 0`,
  `a ≠ b`, `a + b ≠ 1`: gap-bets detect the amplifier — why T5 needs gap-closure.
* **(iii) the centered instances**: `∫_0^1 (amp c e − e) = 0` (the amplifier survives the
  unweighted centered bet) and `∫_0^1 (amp c e − e)(1 − e) = −c/6 < 0` for `c > 0` (dies under
  the weighted one): the centered-bet squeeze's instance.
* **(iv) the exact pinch** (single-state expert), **(v) the marginal identity** `∫_0^1 amp c = ½`.
-/

namespace Cleanroom.Deference.DefLatticeArrows.Amp

open LogicalInduction intervalIntegral Cleanroom.Found.LiAsympCalc
open Cleanroom.Deference.DefLatticeArrows

noncomputable section

/-! ### Integrals of quadratics -/

/-- `∫_a^b (k e² + m e + p) de = k (b³ − a³)/3 + m (b² − a²)/2 + p (b − a)`.
Source: none: infrastructure (li-asymp-calc `integral_linear`, one degree up)
Kind: L
Fidelity: n/a -/
theorem integral_quadratic (a b k m p : ℝ) :
    ∫ e in a..b, (k * e ^ 2 + m * e + p) =
      k * (b ^ 3 - a ^ 3) / 3 + m * (b ^ 2 - a ^ 2) / 2 + p * (b - a) := by
  have h1 : IntervalIntegrable (fun e : ℝ => k * e ^ 2) MeasureTheory.volume a b :=
    (by fun_prop : Continuous (fun e : ℝ => k * e ^ 2)).intervalIntegrable a b
  have h2 : IntervalIntegrable (fun e : ℝ => m * e) MeasureTheory.volume a b :=
    (by fun_prop : Continuous (fun e : ℝ => m * e)).intervalIntegrable a b
  have h3 : IntervalIntegrable (fun _ : ℝ => p) MeasureTheory.volume a b :=
    continuous_const.intervalIntegrable a b
  rw [integral_add (h1.add h2) h3, integral_add h1 h2, integral_const_mul, integral_const_mul,
    integral_pow, integral_id, integral_const, smul_eq_mul]
  push_cast
  ring

/-- The soft-cut integrand is continuous (the ramp is jointly continuous).
Source: none: infrastructure (li-asymp-calc `continuous_ctsInd`)
Kind: L
Fidelity: n/a -/
theorem continuous_softCutIntegrand (c t : ℝ) (δ : ℚ) :
    Continuous (fun e : ℝ => (amp c e - t) * ctsInd δ e t) := by
  have h1 : Continuous (fun e : ℝ => amp c e - t) := by unfold amp; fun_prop
  have h2 : Continuous (fun e : ℝ => ctsInd δ e t) :=
    (continuous_ctsInd δ).comp (continuous_id.prodMk continuous_const)
  exact h1.mul h2

/-! ### (i) Soft cuts come free -/

/-- **The upper soft cut, closed form, when the ramp saturates inside `[0,1]`** (`t + δ ≤ 1`):
`∫_0^1 (amp c e − t) ctsInd δ e t = ½ − t + t²/2 − δ²/6 + c (t − t² − tδ + δ/2 − δ²/3)`.
Source: [[amplifier-counterexample]] §The counterexample ("Soft cuts come free"); mandate T8 (i)
Kind: P
Fidelity: variant: measure model
Hyps: (a) `0 ≤ t`, `t + δ ≤ 1`, `0 < δ` -/
theorem integral_soft_upper_of_le {c t : ℝ} {δ : ℚ} (hδ : 0 < δ) (ht0 : 0 ≤ t)
    (htδ : t + δ ≤ 1) :
    ∫ e in (0 : ℝ)..1, (amp c e - t) * ctsInd δ e t =
      1 / 2 - t + t ^ 2 / 2 - (δ : ℝ) ^ 2 / 6 +
        c * (t - t ^ 2 - t * δ + (δ : ℝ) / 2 - (δ : ℝ) ^ 2 / 3) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hcont := continuous_softCutIntegrand c t δ
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun e : ℝ => (amp c e - t) * ctsInd δ e t)
      MeasureTheory.volume a b := fun a b => hcont.intervalIntegrable a b
  rw [← integral_add_adjacent_intervals (hii 0 t) (hii t 1),
    ← integral_add_adjacent_intervals (hii t (t + δ)) (hii (t + δ) 1)]
  -- piece 1: zero
  have hp1 : ∫ e in (0 : ℝ)..t, (amp c e - t) * ctsInd δ e t = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro e he
      rw [Set.uIcc_of_le ht0] at he
      simp [(ctsInd_eq_zero_iff hδ e t).mpr he.2]
  -- piece 2: the slope
  have hp2 : ∫ e in t..(t + δ), (amp c e - t) * ctsInd δ e t =
      ∫ e in t..(t + δ), (((1 + 2 * c) / δ) * e ^ 2 +
        ((-(c + t) - (1 + 2 * c) * t) / δ) * e + ((c + t) * t / δ)) := by
    apply integral_congr
    intro e he
    rw [Set.uIcc_of_le (by linarith)] at he
    dsimp only
    rw [ctsInd_eq_div hδ he.1 he.2]
    simp only [amp]
    field_simp
    ring
  -- piece 3: saturated
  have hp3 : ∫ e in (t + δ)..1, (amp c e - t) * ctsInd δ e t =
      ∫ e in (t + δ)..1, ((1 + 2 * c) * e + (-(c + t))) := by
    apply integral_congr
    intro e he
    rw [Set.uIcc_of_le htδ] at he
    dsimp only
    rw [(ctsInd_eq_one_iff hδ e t).mpr (by linarith [he.1])]
    simp only [amp]
    ring
  rw [hp1, hp2, hp3, integral_quadratic, integral_linear]
  field_simp
  ring

/-- **The upper soft cut, closed form, when the ramp does not saturate** (`1 < t + δ`):
`∫_0^1 (amp c e − t) ctsInd δ e t = (1 − t)² (2(1 − t) + c(3 − 2(1 − t))) / (6δ)`.
Source: mandate T8 (i)
Kind: P
Fidelity: variant: measure model
Hyps: (a) `0 ≤ t ≤ 1`, `1 < t + δ`, `0 < δ` -/
theorem integral_soft_upper_of_gt {c t : ℝ} {δ : ℚ} (hδ : 0 < δ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (htδ : 1 < t + δ) :
    ∫ e in (0 : ℝ)..1, (amp c e - t) * ctsInd δ e t =
      (1 - t) ^ 2 * (2 * (1 - t) + c * (3 - 2 * (1 - t))) / (6 * δ) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hcont := continuous_softCutIntegrand c t δ
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun e : ℝ => (amp c e - t) * ctsInd δ e t)
      MeasureTheory.volume a b := fun a b => hcont.intervalIntegrable a b
  rw [← integral_add_adjacent_intervals (hii 0 t) (hii t 1)]
  have hp1 : ∫ e in (0 : ℝ)..t, (amp c e - t) * ctsInd δ e t = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro e he
      rw [Set.uIcc_of_le ht0] at he
      simp [(ctsInd_eq_zero_iff hδ e t).mpr he.2]
  have hp2 : ∫ e in t..1, (amp c e - t) * ctsInd δ e t =
      ∫ e in t..1, (((1 + 2 * c) / δ) * e ^ 2 +
        ((-(c + t) - (1 + 2 * c) * t) / δ) * e + ((c + t) * t / δ)) := by
    apply integral_congr
    intro e he
    rw [Set.uIcc_of_le ht1] at he
    dsimp only
    rw [ctsInd_eq_div hδ he.1 (by linarith [he.2])]
    simp only [amp]
    field_simp
    ring
  rw [hp1, hp2, integral_quadratic]
  field_simp
  ring

/-- **(i) The upper soft cut is nonnegative**: for `c ≥ 0`, `t ∈ [0,1]`, `δ > 0`,
`∫_0^1 (amp c e − t) · ctsInd δ e t ≥ 0`. So passing all hard parallel cuts is not what
protects the amplifier: it passes every **soft** parallel cut too, at every width — the
reason `def-lattice`'s soft Total Trust on a single bet cannot pin the tower, and T5 needs
gap-closure.
Source: [[amplifier-counterexample]] §The counterexample ("Soft cuts come free"); vq-wiki-011;
lean-deference-019; mandate T8 (i)
Kind: P
Fidelity: variant: measure model (Unif[0,1] layer-wise expectation), not a LUV statement
Hyps: (a) none beyond the ranges -/
theorem soft_upper_cut_nonneg {c t : ℝ} {δ : ℚ} (hc : 0 ≤ c) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hδ : 0 < δ) : 0 ≤ ∫ e in (0 : ℝ)..1, (amp c e - t) * ctsInd δ e t := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  rcases le_or_gt (t + δ) 1 with h | h
  · rw [integral_soft_upper_of_le hδ ht.1 h]
    have hL : 0 ≤ 1 - t - δ := by linarith
    have h13 : 0 ≤ 1 / 2 - (δ : ℝ) / 3 := by linarith [ht.1]
    nlinarith [mul_nonneg hc (mul_nonneg hL ht.1), mul_nonneg hc (mul_nonneg hδR.le h13),
      sq_nonneg (1 - t - δ), mul_nonneg hL hδR.le, sq_nonneg (δ : ℝ)]
  · rw [integral_soft_upper_of_gt hδ ht.1 ht.2 h]
    have hM : 0 ≤ 1 - t := by linarith [ht.2]
    have hin : 0 ≤ 2 * (1 - t) + c * (3 - 2 * (1 - t)) := by
      nlinarith [mul_nonneg hc (by linarith [ht.1] : (0 : ℝ) ≤ 3 - 2 * (1 - t))]
    positivity

/-- The reflection `e ↦ 1 − e` carries the lower soft cut at `t` to the upper soft cut at
`1 − t`: `(t − amp c e) ctsInd δ t e = (amp c (1 − e) − (1 − t)) ctsInd δ (1 − e) (1 − t)`.
Source: none: infrastructure (`amp c (1 − e) = 1 − amp c e`)
Kind: L
Fidelity: n/a -/
theorem lower_integrand_reflect (c t : ℝ) (δ : ℚ) (e : ℝ) :
    (t - amp c e) * ctsInd δ t e = (amp c (1 - e) - (1 - t)) * ctsInd δ (1 - e) (1 - t) := by
  have h1 : amp c (1 - e) - (1 - t) = t - amp c e := by simp only [amp]; ring
  have h2 : ctsInd δ (1 - e) (1 - t) = ctsInd δ t e := by
    unfold ctsInd; congr 2; ring
  rw [h1, h2]

/-- **(i) The lower soft cut is nonnegative**: `∫_0^1 (t − amp c e) · ctsInd δ t e ≥ 0` — by
reflecting `e ↦ 1 − e` onto the upper cut at `1 − t`.
Source: [[amplifier-counterexample]] §The counterexample; mandate T8 (i)
Kind: P
Fidelity: variant: measure model
Hyps: (a) none beyond the ranges -/
theorem soft_lower_cut_nonneg {c t : ℝ} {δ : ℚ} (hc : 0 ≤ c) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hδ : 0 < δ) : 0 ≤ ∫ e in (0 : ℝ)..1, (t - amp c e) * ctsInd δ t e := by
  have hrefl : (fun e : ℝ => (t - amp c e) * ctsInd δ t e) =
      fun e => (fun x => (amp c x - (1 - t)) * ctsInd δ x (1 - t)) (1 - e) := by
    funext e; exact lower_integrand_reflect c t δ e
  rw [hrefl, integral_comp_sub_left (fun x => (amp c x - (1 - t)) * ctsInd δ x (1 - t)) 1]
  simp only [sub_zero, sub_self]
  exact soft_upper_cut_nonneg hc ⟨by linarith [ht.2], by linarith [ht.1]⟩ hδ

/-! ### (ii) The gap-bet kill -/

/-- **The gap-bet integral**: `∫_a^b (amp c e − e) de = c (b − a)(a + b − 1)`.
Source: [[amplifier-counterexample]] §Why it dies under gap-bets; [[total-trust-implies-mart]]
§Consistency with the amplifier
Kind: P
Fidelity: variant: measure model
Hyps: (a) none -/
theorem integral_gap (c a b : ℝ) :
    ∫ e in a..b, (amp c e - e) = c * (b - a) * (a + b - 1) := by
  have h : ∫ e in a..b, (amp c e - e) = ∫ e in a..b, ((2 * c) * e + (-c)) := by
    apply integral_congr
    intro e _
    simp only [amp]; ring
  rw [h, integral_linear]
  ring

/-- **(ii) Gap-bets detect the amplifier**: for `c > 0`, `a ≠ b`, `a + b ≠ 1`, the gap-bet
`Z = X · 1[e ∈ [a, b]]` has `E_π(Z − E*(Z)) ≠ 0`. In this static measure model (no day `n`)
the Total-Trust instance on a gap-bet is the exact two-sided cut at the pinned estimate, so a
nonzero value means a cut of small enough width fails on `Z`: the amplifier does not survive
gap-closed Total Trust, T5's gap-closure is necessary, and parallel cuts (i) cannot replace
it.
Source: [[amplifier-counterexample]] §Why it dies under gap-bets; [[total-trust-implies-mart]]
§Consistency with the amplifier; vq-wiki-011
Kind: N+
Fidelity: variant: measure model
Hyps: (a) `0 < c`, `a ≠ b`, `a + b ≠ 1` -/
theorem gap_kill {c a b : ℝ} (hc : 0 < c) (hab : a ≠ b) (hsum : a + b ≠ 1) :
    ∫ e in a..b, (amp c e - e) ≠ 0 := by
  rw [integral_gap]
  exact mul_ne_zero (mul_ne_zero hc.ne' (sub_ne_zero.mpr hab.symm)) (sub_ne_zero.mpr hsum)

/-- A concrete gap-bet kill: `c = 1`, `[a, b] = [0, ½]`: the integral is `−1/4`.
Source: mandate T8 (the required concrete `(a, b, c)`)
Kind: N+
Fidelity: variant: measure model -/
theorem gap_kill_concrete : ∫ e in (0 : ℝ)..(1 / 2), (amp 1 e - e) = -1 / 4 := by
  rw [integral_gap]; norm_num

/-! ### (iii) The centered instances -/

/-- **The unweighted centered instance**: `∫_0^1 (amp c e − e) = 0` — the amplifier survives
the bare centered bet (its overshoot and undershoot cancel).
Source: [[centered-bet-squeeze]] §4; root-deference-008; lean-deference-034
Kind: P
Fidelity: variant: measure model
Hyps: (a) none -/
theorem amp_unweighted_centered_zero (c : ℝ) : ∫ e in (0 : ℝ)..1, (amp c e - e) = 0 := by
  rw [integral_gap]; ring

/-- **The weighted centered moment**: `∫_0^1 (amp c e − e)(1 − e) = −c/6`.
Source: [[centered-bet-squeeze]] §4; root-deference-008
Kind: P
Fidelity: variant: measure model
Hyps: (a) none -/
theorem amp_weighted_centered_moment (c : ℝ) :
    ∫ e in (0 : ℝ)..1, (amp c e - e) * (1 - e) = -c / 6 := by
  have h : ∫ e in (0 : ℝ)..1, (amp c e - e) * (1 - e) =
      ∫ e in (0 : ℝ)..1, ((-(2 * c)) * e ^ 2 + (3 * c) * e + (-c)) := by
    apply integral_congr
    intro e _
    simp only [amp]; ring
  rw [h, integral_quadratic]
  ring

/-- **(iii) The amplifier dies under the weighted centered instance**: the moment is negative
for `c > 0` — the centered-bet squeeze's instance, with no appeal to boundedness.
Source: [[centered-bet-squeeze]] §4 ("So `c = 0` is forced"); root-deference-008
Kind: N+
Fidelity: variant: measure model
Hyps: (a) `0 < c` -/
theorem amp_weighted_centered_neg {c : ℝ} (hc : 0 < c) :
    ∫ e in (0 : ℝ)..1, (amp c e - e) * (1 - e) < 0 := by
  rw [amp_weighted_centered_moment]; linarith

/-! ### (iv) The exact pinch, (v) the marginal identity -/

/-- **The exact pinch** (single-state expert): if `s · mass ≤ ED` for all `s ≤ e*` and
`ED ≤ s · mass` for all `s ≥ e*`, then `ED = e* · mass` (take `s = e*` on both sides).
Source: `CenteredSqueeze.lean:216` (`exact_pinch`, shape only); lean-deference-034
Kind: L
Fidelity: exact
Hyps: (a) the two cut families -/
theorem exact_pinch (ED estar mass : ℝ) (hup : ∀ s : ℝ, s ≤ estar → s * mass ≤ ED)
    (hdn : ∀ s : ℝ, estar ≤ s → ED ≤ s * mass) : ED = estar * mass :=
  le_antisymm (hdn estar le_rfl) (hup estar le_rfl)

/-- **(v) The marginal identity**: `∫_0^1 amp c = ½` — the bare tower on the one bet holds for
the amplifier; its failure is strictly layer-wise.
Source: [[amplifier-counterexample]] §The counterexample ("Marginal identity too")
Kind: L
Fidelity: variant: measure model
Hyps: (a) none -/
theorem amp_marginal (c : ℝ) : ∫ e in (0 : ℝ)..1, amp c e = 1 / 2 := by
  rw [integral_amp_lower]; ring

end

end Cleanroom.Deference.DefLatticeArrows.Amp
