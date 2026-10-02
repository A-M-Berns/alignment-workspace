import Cleanroom.Deference.DefArgmaxValue.Refuted
import Cleanroom.Found.LiAsympCalc.WeightedAverage
import Cleanroom.Found.LiAsympCalc.LimitPoint

/-!
# `def-argmax-value` · Averaged: Value transport to the averaged grade (target 11a)

[[theorem-ss-streamlined]] §8's general-menu conjecture — "scheduled averaged argmax Value over
arbitrary e.d. menus, no scope condition" — is refuted by its own author's stress test
([[weak-loop-and-value-transport]] §1, 2026-08-03): on the liar probe the per-day deficit is
one-signed, and **averaging launders oscillation, not bias**. Over FAF: with any nonnegative
non-summable weighting `w` (the bare schedule `w ≡ 1` included), the `w`-averages of
`E^P_i(S_i)` and `E^P_i(const s)` converge to `s²` and `s` (Cesàro,
`Cleanroom.Found.LiAsympCalc.weightedAverage_tendsto` on the pointwise limits of
`Refuted.lean`), so the averaged Value instance on the probe menu fails
(`averaged_value_probe_refuted`, `averaged_value_probe_refuted_bare`). The two-option exact
transport (065(a)) is a pointwise identity averaged (`averaged_of_pointwise_identity`, cited to
`def-lattice`'s `twoOption_identity_above`).

Single market (self); `0 < s < 1`.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Found.LiAsympCalc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
variable (f : DeferralFunction) (s : ℚ)

/-- **The averaged follower expectation converges to `s²`** on the probe, for every nonnegative
non-summable weighting (Cesàro on `E^P_i(S_i) → s²`).
Source: [[weak-loop-and-value-transport]] §1 (the display `→ s²`); mandate target 11a
Kind: C
Fidelity: exact
Hyps: (a); `hf`; `w` nonnegative, non-summable -/
theorem averaged_probeFollower_tendsto (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (hdiv : Tendsto (prefixSum w) atTop atTop) :
    Tendsto (weightedAverage w
      (fun i => (probeFollower T f s hs0.le i).expect (liaHistory (paperDP T)) i)) atTop
      (𝓝 ((s : ℝ) * s)) := by
  refine weightedAverage_tendsto hw hdiv ?_
  have hS : Tendsto (fun n => (probeFollower T f s hs0.le n).expect (liaHistory (paperDP T)) n -
      (s : ℝ) * (liaHistory (paperDP T)) n (liarSentence T f s hs0.le n)) atTop (𝓝 0) :=
    probeFollower_expect T f s ⟨hs0.le, hs1.le⟩
  have hpn := liarPresentPrice_tendsto_s T f s hf hs0 hs1
  have := hS.add (hpn.const_mul (s : ℝ))
  refine (tendsto_congr (fun n => ?_)).mp (by simpa using this)
  ring

/-- **The averaged constant-option expectation converges to `s`**.
Source: [[weak-loop-and-value-transport]] §1 (the display `→ s`)
Kind: L
Fidelity: exact
Hyps: (a); `w` nonnegative, non-summable -/
theorem averaged_const_tendsto (hs : 0 ≤ s ∧ s ≤ 1) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) :
    Tendsto (weightedAverage w (fun i => (constLUV s).expect (liaHistory (paperDP T)) i)) atTop
      (𝓝 (s : ℝ)) :=
  weightedAverage_tendsto hw hdiv (tendsto_of_asympEq_const (expect_constLUV_asympEq
    (P := liaHistory (paperDP T)) (DP := paperDP T) hs (paperDP_hworld T)))

/-- **Scheduled averaged argmax Value is refuted on the probe** (target 11a, vq-wiki-065's
general-menu conjecture): for every nonnegative non-summable weighting, the `w`-averaged Value
instance `avg_w E^P_i(S_i) ≳ₙ avg_w E^P_i(O^1_i)` fails — the averages converge to `s² < s`.
Averaging launders oscillation, not the one-signed per-day deficit.
Source: [[weak-loop-and-value-transport]] §1; [[theorem-ss-streamlined]] §8 ⚠ 2026-08-03;
mandate target 11a
Kind: refuted
Fidelity: exact (the averaged instance on the probe menu; any non-summable weighting)
Hyps: (a); `hf` -/
theorem averaged_value_probe_refuted (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (hdiv : Tendsto (prefixSum w) atTop atTop) :
    ¬ (weightedAverage w
        (fun i => (probeFollower T f s hs0.le i).expect (liaHistory (paperDP T)) i) ≳ₙ
      weightedAverage w
        (fun i => ((probeMenu T f s hs0.le).O 1 i).expect (liaHistory (paperDP T)) i)) := by
  simp only [probeMenu_O_one]
  refine not_asympGE_of_tendsto_neg (c := (s : ℝ) * s - s) ?_ ?_
  · have h0 : (0 : ℝ) < s := by exact_mod_cast hs0
    have h1 : (s : ℝ) < 1 := by exact_mod_cast hs1
    nlinarith
  · exact (averaged_probeFollower_tendsto T f s hf hs0 hs1 w hw hdiv).sub
      (averaged_const_tendsto T s ⟨hs0.le, hs1.le⟩ w hw hdiv)

/-- The bare schedule weighting `w ≡ 1` (the conjecture's own weighting).
Source: [[weak-loop-and-value-transport]] §1 ("with `w_i` the bare schedule indicator")
Kind: refuted
Fidelity: exact
Hyps: (a); `hf` -/
theorem averaged_value_probe_refuted_bare (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) :
    ¬ (weightedAverage (fun _ => (1 : ℝ))
        (fun i => (probeFollower T f s hs0.le i).expect (liaHistory (paperDP T)) i) ≳ₙ
      weightedAverage (fun _ => (1 : ℝ))
        (fun i => ((probeMenu T f s hs0.le).O 1 i).expect (liaHistory (paperDP T)) i)) :=
  averaged_value_probe_refuted T f s hf hs0 hs1 _ (fun _ => zero_le_one) tendsto_prefixSum_one

/-- **Two-option exact transport, averaged** (065(a)): a per-day identity survives every
weighting verbatim — `def-lattice`'s `twoOption_identity_above` is such an identity between the
Value difference on `{X, const t}` and the Total-Trust threshold difference at `t`, so its
`w`-average is the averaged identity.
Source: [[theorem-ss-streamlined]] §8 ("Two-option menus: exact transport")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem averaged_of_pointwise_identity (w a b : ℕ → ℝ) (h : ∀ i, a i = b i) :
    weightedAverage w a = weightedAverage w b := by
  have : a = b := funext h
  rw [this]

example : ¬ (weightedAverage (fun _ => (1 : ℝ))
      (fun i => (probeFollower 𝗣𝗔 succDeferral (1 / 2) (by norm_num) i).expect
        (liaHistory (paperDP 𝗣𝗔)) i) ≳ₙ
    weightedAverage (fun _ => (1 : ℝ))
      (fun i => ((probeMenu 𝗣𝗔 succDeferral (1 / 2) (by norm_num)).O 1 i).expect
        (liaHistory (paperDP 𝗣𝗔)) i)) :=
  averaged_value_probe_refuted_bare 𝗣𝗔 succDeferral (1 / 2)
    Cleanroom.Found.LiQuoteLane.succDeferral_strict (by norm_num) (by norm_num)

end

end Cleanroom.Deference.DefArgmaxValue
