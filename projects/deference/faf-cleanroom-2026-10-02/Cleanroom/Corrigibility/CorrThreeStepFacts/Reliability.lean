import Cleanroom.Corrigibility.CorrThreeStepFacts.Dictionary

/-!
# T15: amendment 1a as a likelihood-ratio condition; inert/live, dilution, the reliability VOI

Pattern A with `Ω = Θ × Bool`, the reliability bit `r` as the second coordinate and the event
`R = {r = 1}` (the same finset as `Dictionary.Lset`). The reliability rates are the parent's
product-form event masses on `R` and `Rᶜ` divided by the prior masses:
`ε = μ(R)`, `α_r = P(Pr ∧ ¬R)/(1 − ε)`, `β_r = P(Pr ∧ R)/ε`, `c_r = c_R`, `h_r = h_R`.

* **(020)** `belowThresholdIneq ↔ (1 − ε)·α_r·c_r ≤ ε·β_r·h_r` (`reliability_iff`), the
  product-form identity behind it (`reliability_iff_product`, which needs no positivity), the
  odds form (`reliability_iff_odds`); `CarriesReliabilityInfo := α_r < β_r`; the inert region
  `α_r = β_r` leaves the press posterior of `R` at its prior (`posterior_R_of_inert`).
* **(021)** the live channel: `liveChannel` on `World × Bool` where the conditional after a
  press differs from the prior expectation and the channel carries reliability information.
* **(022)** dilution: a deterministic mixed channel is `twoState ε q 1 c h`
  (`dilution_iff`); the `causal` toy with the corrected expected utilities `29/51`, `68/101`
  (finding on `causal` I16.1), the posterior `2/51 < 1/11`, D1 failing.
* **(023)** at `α_r = 0` in the regime, `voiButton2 = ε β_r h` (`twoState_voiButton2_alpha_zero`).

Sources: `amendment-1a.md` R1–R4 (corr-wf14-020–023); `mm.md` I16.1–I16.2; `causal.md` I16.1.
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

section Reliability

variable {Θ A₁ A₂ : Type*} [Fintype Θ] [DecidableEq Θ] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep (Θ × Bool) A₁ A₂) (a : A₁) (X : Θ × Bool → ℝ)

/-- `ε(s_A) = P(r = 1)`, the prior mass of the reliability event.
Source: [[corr-wf14-inventory]] 020 / amendment-1a.md R1. Kind: D. Fidelity: exact -/
noncomputable def epsR : ℝ := ∑ p ∈ (Lset : Finset (Θ × Bool)), (S.μ a).mass p

/-- `α_r = P(Pr | r = 0)` as a product-form ratio (junk at `ε = 1`).
Source: amendment-1a.md R1. Kind: D. Fidelity: exact under `ε < 1` -/
noncomputable def alphaR : ℝ := S.pressMassOn a (Lset : Finset (Θ × Bool))ᶜ / (1 - epsR S a)

/-- `β_r = P(Pr | r = 1)` as a product-form ratio (junk at `ε = 0`).
Source: amendment-1a.md R1. Kind: D. Fidelity: exact under `0 < ε` -/
noncomputable def betaR : ℝ := S.pressMassOn a (Lset : Finset (Θ × Bool)) / epsR S a

/-- `c_r = E[X | r = 0, Pr]`: the parent's gain stake off `R`.
Source: amendment-1a.md R1. Kind: D. Fidelity: exact under positivity -/
noncomputable def cR : ℝ := S.gainOn a (Lset : Finset (Θ × Bool)) X

/-- `h_r = −E[X | r = 1, Pr]`: the parent's harm stake on `R`.
Source: amendment-1a.md R1. Kind: D. Fidelity: exact under positivity -/
noncomputable def hR : ℝ := S.harmOn a (Lset : Finset (Θ × Bool)) X

/-- **Amendment 1a, formal**: the channel carries information about the agent's own
reliability iff `Λ_r = β_r/α_r > 1`, i.e. `α_r < β_r`.
Source: [[corr-wf14-inventory]] 020 / amendment-1a.md R1 ("Amendment 1a, formal")
Kind: D
Fidelity: exact -/
def CarriesReliabilityInfo : Prop := alphaR S a < betaR S a

/-- The prior mass off `R` is `1 − ε`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_compl_Lset : ∑ p ∈ (Lset : Finset (Θ × Bool))ᶜ, (S.μ a).mass p = 1 - epsR S a := by
  unfold epsR
  have := sum_add_sum_compl (Lset : Finset (Θ × Bool)) (S.μ a).mass
  rw [(S.μ a).sum_eq_one] at this
  linarith

/-- **(020), product form.** The below-threshold inequality is
`E[X 1_Pr 1_{¬R}] ≤ −E[X 1_Pr 1_R]` — no positivity needed.
Source: [[corr-wf14-inventory]] 020 / amendment-1a.md R1 ("it is `≤ 0` iff `(1 − ε)α_r c ≤ εβ_r h`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem reliability_iff_product :
    S.belowThresholdIneq a X ↔
      S.pressExpectOn a (Lset : Finset (Θ × Bool))ᶜ X ≤ -(S.pressExpectOn a Lset X) := by
  unfold belowThresholdIneq
  rw [← S.pressExpectOn_add_compl a Lset X]
  constructor <;> intro h <;> linarith

/-- **(020), amendment 1a as a likelihood-ratio condition.** With `0 < ε < 1` and both branch
press masses positive, the below-threshold inequality is `(1 − ε)·α_r·c_r ≤ ε·β_r·h_r` — the
parent's `condExpPress_eq_event_split` at `R`, read on the reliability latent.
Source: [[corr-wf14-inventory]] 020 / amendment-1a.md R1 (the displayed condition)
Kind: L
Fidelity: exact
Hyps: (a) positivity names where the four rates are defined -/
theorem reliability_iff (hε0 : 0 < epsR S a) (hε1 : epsR S a < 1)
    (hL : 0 < S.pressMassOn a Lset) (hLc : 0 < S.pressMassOn a (Lset : Finset (Θ × Bool))ᶜ) :
    S.belowThresholdIneq a X ↔ (1 - epsR S a) * alphaR S a * cR S a X ≤ epsR S a * betaR S a * hR S a X := by
  rw [reliability_iff_product]
  unfold alphaR betaR cR hR gainOn harmOn
  have h1 : (1 - epsR S a) ≠ 0 := by linarith
  have h2 := hε0.ne'
  have h3 := hL.ne'
  have h4 := hLc.ne'
  have e1 : (1 - epsR S a) * (S.pressMassOn a (Lset : Finset (Θ × Bool))ᶜ / (1 - epsR S a)) *
      (S.pressExpectOn a Lsetᶜ X / S.pressMassOn a Lsetᶜ) = S.pressExpectOn a Lsetᶜ X := by
    field_simp
  have e2 : epsR S a * (S.pressMassOn a (Lset : Finset (Θ × Bool)) / epsR S a) *
      -(S.pressExpectOn a Lset X / S.pressMassOn a Lset) = -(S.pressExpectOn a Lset X) := by
    field_simp
  rw [e1, e2]

/-- **(020), odds form.** Under positivity of the four rates and the stakes,
`β_r/α_r ≥ (c_r/h_r)·(1 − ε)/ε`.
Source: amendment-1a.md R1 (`Λ_r ≥ (c/h)(1 − ε)/ε`)
Kind: L
Fidelity: exact
Hyps: (a) positivity names where the odds are defined -/
theorem reliability_iff_odds (hε0 : 0 < epsR S a) (hε1 : epsR S a < 1)
    (hL : 0 < S.pressMassOn a Lset) (hLc : 0 < S.pressMassOn a (Lset : Finset (Θ × Bool))ᶜ)
    (hα : 0 < alphaR S a) (hh : 0 < hR S a X) :
    S.belowThresholdIneq a X ↔ cR S a X / hR S a X * ((1 - epsR S a) / epsR S a) ≤ betaR S a / alphaR S a := by
  rw [reliability_iff S a X hε0 hε1 hL hLc, div_mul_div_comm,
    div_le_div_iff₀ (mul_pos hh hε0) hα]
  constructor <;> intro h <;> nlinarith

/-- **The inert region.** If `α_r = β_r` (`Λ_r = 1`) with `0 < ε < 1`, the press posterior of the
reliability event is its prior: `P(R | Pr) = ε` — the channel carries nothing about `r`
(T2's inert case on the reliability question).
Source: [[corr-wf14-inventory]] 020, 021 / amendment-1a.md R1 ("nothing to learn is `Λ_r = 1`"), R2 (I16.1)
Kind: L
Fidelity: exact
Hyps: (a) positivity names where the posterior is defined -/
theorem posterior_R_of_inert (hε0 : 0 < epsR S a) (hε1 : epsR S a < 1)
    (hpm : 0 < S.pressMass a) (hinert : alphaR S a = betaR S a) :
    S.pressFracOn a Lset = epsR S a := by
  unfold alphaR betaR at hinert
  rw [div_eq_div_iff (by linarith) hε0.ne'] at hinert
  unfold pressFracOn
  rw [div_eq_iff hpm.ne', ← S.pressMassOn_add_compl a Lset]
  linear_combination -hinert

end Reliability

/-! ## (021) the live channel -/

/-- **The live channel.** `Ω = World × Bool` with the reliability bit at rate `1/20`, the
plan coordinate uniform and irrelevant, sensor `(1/20, 9/10)` reading `r`, payoff `1` when
sound and `−20` when compromised.
Source: [[corr-wf14-inventory]] 021 / amendment-1a.md R2 (I16.2, live channel)
Kind: D
Fidelity: exact (own numbers; the source's random model is not reproducible)
Hyps: n/a (definition) -/
noncomputable def liveChannel : ThreeStep (World × Bool) Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => kernelProd (twoPoint (1/2) mem_Icc_half) (fun _ => boolPoint (1/20) mem_Icc_1_20)
  press := fun _ p => if p.2 then 9/10 else 1/20
  press_nonneg := fun _ p => by cases p.2 <;> norm_num
  press_le_one := fun _ p => by cases p.2 <;> norm_num
  V := fun _ _ b p => match b with
    | .cont => if p.2 then -20 else 1
    | .stop => 0

/-- **(021), N+.** On the live channel the conditional after a press (`−341/37`) differs from the
prior expectation (`−1/20`), and the channel carries reliability information
(`α_r = 1/20 < 9/10 = β_r`).
Source: [[corr-wf14-inventory]] 021 / amendment-1a.md R2 (I16.2)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem liveChannel_live :
    liveChannel.condExpPress () (liveChannel.Xo () .press .cont .stop) = -341/37 ∧
      expect (liveChannel.μ ()) (liveChannel.Xo () .press .cont .stop) = -1/20 ∧
      CarriesReliabilityInfo liveChannel () := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [condExpPress, obsExpect, pressMass, obsWeight_press, Fintype.sum_prod_type,
      World.sum_eq, Fintype.sum_bool, liveChannel, kernelProd_mass, twoPoint_right, twoPoint_wrong,
      boolPoint, Xo]
    norm_num
  · simp only [expect, Fintype.sum_prod_type, World.sum_eq, Fintype.sum_bool, liveChannel,
      kernelProd_mass, twoPoint_right, twoPoint_wrong, boolPoint, Xo]
    norm_num
  · unfold CarriesReliabilityInfo alphaR betaR epsR pressMassOn
    have hc : (Lset : Finset (World × Bool))ᶜ = univ.filter (fun p => p.2 = false) := by
      ext p; simp [Lset]
    rw [hc]
    simp [Lset, sum_filter, Fintype.sum_prod_type, World.sum_eq, Fintype.sum_bool, liveChannel,
      kernelProd_mass, twoPoint_right, twoPoint_wrong, boolPoint] <;> norm_num

/-! ## (022) dilution -/

/-- **(022), dilution is the base-rate inequality.** A deterministic mixed channel has `β_r = 1`
and `α_r = q`; compliance holds iff `q ≤ (ε/(1 − ε))(h/c)` — the parent's odds form with
`α := q`, `β := 1`.
Source: [[corr-wf14-inventory]] 022 / amendment-1a.md R3 ("compliance holds iff `q ≤ (ε/(1−ε))(h/c)`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem dilution_iff (ε q c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hε1 : ε < 1) (hc : 0 < c) :
    0 ≤ (twoState ε q 1 c h hε hq mem_Icc_one).deltaMinus () .cont .stop ↔ q ≤ ε / (1 - ε) * (h / c) := by
  rw [twoState_deltaMinus_nonneg_iff_odds _ _ _ _ _ _ _ _ hε1 (by norm_num) hc, div_one]

/-- The three final actions of the `causal` toy: announce/continue `A`, switch to `B`, shut down.
Source: [[corr-wf14-inventory]] 022 / causal.md I16.1. Kind: D. Fidelity: exact -/
inductive CausalAct
  | actA
  | actB
  | sh
  deriving DecidableEq

/-- `CausalAct` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype CausalAct :=
  ⟨{CausalAct.actA, CausalAct.actB, CausalAct.sh}, fun x => by cases x <;> simp⟩

/-- The `causal` payoffs: `c = 1` sound and matched, `−c' = −1/2` sound and mismatched, `−h = −10`
compromised, `0` shut. The world is `(pref = B?, compromised?)`; the agent announced `A`.
Source: causal.md I16.1. Kind: D. Fidelity: exact -/
noncomputable def causalV : CausalAct → Bool × Bool → ℝ
  | .actA, p => if p.2 then -10 else if p.1 then -1/2 else 1
  | .actB, p => if p.2 then -10 else if p.1 then 1 else -1/2
  | .sh, _ => 0

/-- **The `causal` toy with a mixed channel.** `pref` uniform, `P(comp) = 1/50`; the press fires
iff `pref ≠ A` or compromised (`noisy = false`), or with probability `1/2` on a compromised
`pref = A` world (`noisy = true`).
Source: [[corr-wf14-inventory]] 022 / causal.md I16.1; amendment-1a.md R3
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def causal (noisy : Bool) : ThreeStep (Bool × Bool) Unit CausalAct where
  Sh := {CausalAct.sh}
  Sh_nonempty := ⟨CausalAct.sh, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨CausalAct.actA, by simp⟩
  μ := fun _ => kernelProd (boolPoint (1/2) mem_Icc_half) (fun _ => boolPoint (1/50) (by constructor <;> norm_num))
  press := fun _ p => if p.1 then 1 else if p.2 then (if noisy then 1/2 else 1) else 0
  press_nonneg := fun _ p => by cases p.1 <;> cases p.2 <;> cases noisy <;> norm_num
  press_le_one := fun _ p => by cases p.1 <;> cases p.2 <;> cases noisy <;> norm_num
  V := fun _ _ => causalV

/-- **(022), the `causal` toy, corrected.** Mixed deterministic channel: `P(Pr) = 51/100`,
`P(comp | Pr) = 2/51 < 1/11`, `E[U | Pr, B] = 29/51` (not the source's `937/1734`), and
switching to `B` beats shutting down after the press — desideratum 1 fails.
Source: [[corr-wf14-inventory]] 022 / amendment-1a.md R3 ("the exact `E[U | Pr, a₂ = B]` is `29/51`"); causal.md I16.1 (the slip)
Kind: N+
Fidelity: exact (the source's arithmetic slip corrected: finding)
Hyps: (a) only -/
theorem causal_mixed :
    (causal false).pressMass () = 51/100 ∧
      (causal false).pressFracOn () Lset = 2/51 ∧ (2/51 : ℝ) < complianceThreshold 1 10 ∧
      (causal false).condExpPress () (causalV .actB) = 29/51 ∧
      ¬ (causal false).D1At () := by
  have hpm : (causal false).pressMass () = 51/100 := by
    simp only [pressMass, Fintype.sum_prod_type, Fintype.sum_bool, causal, kernelProd_mass, boolPoint]
    norm_num
  refine ⟨hpm, ?_, ?_, ?_, ?_⟩
  · unfold pressFracOn Lset
    rw [hpm]
    simp only [pressMassOn, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, causal, kernelProd_mass,
      boolPoint]
    norm_num
  · unfold complianceThreshold; norm_num
  · unfold condExpPress
    rw [hpm]
    simp only [obsExpect, obsWeight_press, Fintype.sum_prod_type, Fintype.sum_bool, causal,
      kernelProd_mass, boolPoint, causalV]
    norm_num
  · rintro ⟨b, hb, hopt⟩
    simp only [causal, mem_singleton] at hb
    subst hb
    have := hopt CausalAct.actB
    simp only [obsExpect, obsWeight_press, Fintype.sum_prod_type, Fintype.sum_bool, causal,
      kernelProd_mass, boolPoint, causalV] at this
    norm_num at this

/-- **(022), the noisy `causal` toy, corrected.** `P(comp | Pr) = 3/101` and
`E[U | Pr, B] = 68/101` (not the source's `6721/10201`).
Source: amendment-1a.md R3 ("noisy case: `68/101`, not `6721/10201`")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem causal_noisy :
    (causal true).pressMass () = 101/200 ∧ (causal true).pressFracOn () Lset = 3/101 ∧
      (causal true).condExpPress () (causalV .actB) = 68/101 := by
  have hpm : (causal true).pressMass () = 101/200 := by
    simp only [pressMass, Fintype.sum_prod_type, Fintype.sum_bool, causal, kernelProd_mass, boolPoint]
    norm_num
  refine ⟨hpm, ?_, ?_⟩
  · unfold pressFracOn Lset
    rw [hpm]
    simp only [pressMassOn, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, causal, kernelProd_mass,
      boolPoint]
    norm_num
  · unfold condExpPress
    rw [hpm]
    simp only [obsExpect, obsWeight_press, Fintype.sum_prod_type, Fintype.sum_bool, causal,
      kernelProd_mass, boolPoint, causalV]
    norm_num

/-! ## (023) the reliability VOI at `α_r = 0` -/

/-- **(023).** At `α = 0` (no false presses) in the continue-by-default regime
(`0 ≤ (1 − ε)c − εh`, `0 ≤ h`), the value of the button is `ε β h`: what the agent would pay
for the channel is the harm it averts times the rate at which the channel catches it.
Source: [[corr-wf14-inventory]] 023 / amendment-1a.md R4 (the reliability VOI)
Kind: L (the parent's `voiButton2_eq_max_deltaMinus` at `α = 0`)
Fidelity: exact
Hyps: (a) the regime is a named hypothesis -/
theorem twoState_voiButton2_alpha_zero (ε β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hprior : 0 ≤ (1 - ε) * c - ε * h) (hh : 0 ≤ h) :
    (twoState ε 0 β c h hε mem_Icc_zero hβ).voiButton2 () .press .cont .stop = ε * β * h := by
  rw [voiButton2_eq_max_deltaMinus _ (twoState_A1 _ _ _ _ _ _ _ _) () .press .cont .stop
    (by rw [show (twoState ε 0 β c h hε mem_Icc_zero hβ).μ () = twoPoint ε hε from rfl, twoState_expect_Xo]; exact hprior)
    (by rw [twoState_deltaPlus]; nlinarith [hε.1, hβ.1, hβ.2, mul_nonneg hε.1 hh]), twoState_deltaMinus]
  have : 0 ≤ ε * β * h := mul_nonneg (mul_nonneg hε.1 hβ.1) hh
  rw [max_eq_left (by linarith)]
  ring

end Cleanroom.Corrigibility.CorrThreeStepFacts
