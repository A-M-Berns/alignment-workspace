import Cleanroom.Corrigibility.CorrLiShutdown.Identity
import Cleanroom.Deference.DefSelfTrust.Est
import LogicalInduction.Construction.Paper.Market

/-!
# `corr-li-shutdown` — Map (T8, T9, T20): Statement 2's corrected map, the thesis sentence, the
martingale clause

* **T8** (`selfTrust_is_anticipation`, L): FAF's Self-Trust (`thm:st`) is one-sided and its only
  quoted object is the inductor's own *deferred* confidence `P_{f n}(φ_n)`; the below-threshold
  inequality at threshold `0` for the self-expert is `def-self-trust`'s `est`
  (`selfSoftTotalTrustBelow`). **No day-`n` press appears**: the weight is a ramp of the day-`f(n)`
  self-estimate. So the "pointwise grade, self-instance" of the sources' I9.2 is anticipation of
  one's own verdict, not compliance with a press — Statement 2's corrected map (finding F4 of
  `corr-li-shutdown-findings`). Statement 2(ii)–(iv) are recorded, not re-proved: (ii) the
  quote-referencing coupled press is `def-obstruction`'s refutation; (iii) underivable-not-
  refuted; (iv) the sealed verdict on `G` is `def-tracking-pin` / `fa-theorem-a`'s.
* **T9** (`thesis_sentence_is_cee`, L): the thesis's central sentence — "whatever the agent
  expects its own future updated belief about `X_n` to be, it already believes" — is FAF's
  `thm:cee` on the toy family's indicator LUV, `E_n(1(φ_n)) ≈ₙ E_n(⌜E_{f n}(1(φ_n))⌝)`, with the
  toy rescaling (`thesis_sentence_is_cee_toy`). Self-pushes only; the external-push version is
  not an FAF theorem (corr-core-011's register). The identification of "no FUD" and "the FUD
  mechanism" as one theorem is a gloss (ATTRIBUTION-UNVETTED). T17's `noFUD_is_cee` is this
  declaration under its second name (`Richness.lean`).
* **T20** (`threeStep_tower_product_form`, L): on `corr-three-step`'s finite setting the tower
  identity `E[X·1_Pr] + E[X·1_¬Pr] = E[X]` in product form; it constrains the *sum* of the two
  observation terms and says nothing about the sign of either — the martingale clause. The
  Newcomblike exception is `corr-three-step-facts`' (pointer, row 013).
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc Cleanroom.Deference.DefSelfTrust
  Cleanroom.Found.CorrThreeStep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

section Paper

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **Self-Trust is anticipation, not compliance** (T8, the scope lemma): for the novice's own
future self `Expert.self … f` over the paper inductor, the soft below-threshold inequality at
threshold `0` holds for every e.c. family and every `WeightQuote` at the *deferred* ramp
`rampBelow δ 0` — `def-self-trust`'s `est`. The weight is `Ind_δ(E_{f n}(X_n) < 0)`, a ramp of
the inductor's **own day-`f(n)` estimate**: no day-`n` press of the overseers occurs in the
statement, and the conclusion is one-sided (`≲ₙ`). This is the sources' "pointwise grade,
self-instance" — anticipation of one's own verdict. Per-press compliance with a live press the
agent could not compute is forced nowhere in this formalism (finding F4); the surviving
neighbours are this anticipation and calibrated obedience (`Calibrated.lean`).
Source: [[corr-wf14-inventory]] 085 (`li-final.md` Statement 2(i)); [[corr-wf14-2-inventory]] 2-028; [[corr-wf13-inventory]] 060 (I9.2)
Kind: L
Fidelity: exact (a named re-export of `def-self-trust`'s `selfSoftTotalTrustBelow` at `s = 0`)
Hyps: (a); `hinj` -/
theorem selfTrust_is_anticipation (f : DeferralFunction) (hinj : Function.Injective f.f) {δ : ℚ}
    (hδ : 0 < δ) :
    SoftTotalTrustBelow (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) 0 δ :=
  selfSoftTotalTrustBelow T f hinj 0 hδ

/-- **The thesis sentence is `cee`** (T9): for every e.c. verdict family `φ`, the paper inductor's
day-`n` expectation of `1(φ_n)` is asymptotically its expectation of the quoted day-`f(n)`
expectation `⌜E_{f n}(1(φ_n))⌝` — "whatever the agent expects its own future updated belief to
be, it already believes". FAF's `thm:cee`, closed form, at the indicator LUV (its
world-valuedness is `LUV.indicatorOf_isIndicator`).
Source: [[corr-wf13-inventory]] 067; [[corr-core-inventory]] 011; [[corr-wf14-inventory]] 013/103 (the LI carrier); FAF `lic_expected_future_expectations_closed`
Kind: L
Fidelity: exact (self-pushes only; the external-push version is not an FAF theorem)
Hyps: (a) -/
theorem thesis_sentence_is_cee (f : DeferralFunction) (φ : ℕ → Sentence)
    (hφ : MachineSentenceCodes φ) :
    (fun n => (LUV.indicatorOf (φ n)).expect (liaHistory (paperDP T)) n) ≈ₙ
      fun n => ((paperDeferredExpectationQuoteCode T f (fun n => LUV.indicatorOf (φ n))
        (LUV.indicatorOf_machineThresholdCodeSeq hφ)).luv n).expect (liaHistory (paperDP T)) n :=
  lic_expected_future_expectations_closed T f (fun n => LUV.indicatorOf (φ n))
    (LUV.indicatorOf_machineThresholdCodeSeq hφ)
    (fun n _ hv => ⟨_, (LUV.indicatorOf_isIndicator (φ n) (paperDP T)).valuesAt hv⟩)

/-- **The thesis sentence on the toy family** (T9, rescaled): `E_n(X_n) ≈ₙ c − (c+h)·E_n(⌜E_{f n}
(1(φ_n))⌝)` for `X_n = c − (c+h)·1(φ_n)`.
Source: [[corr-wf13-inventory]] 067; [[corr-core-inventory]] 011
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem thesis_sentence_is_cee_toy (f : DeferralFunction) (c h : ℚ) (φ : ℕ → Sentence)
    (hφ : MachineSentenceCodes φ) :
    (fun n => (toyX c h φ n).expect (liaHistory (paperDP T)) n) ≈ₙ
      fun n => (c : ℝ) - ((c : ℝ) + h) *
        ((paperDeferredExpectationQuoteCode T f (fun n => LUV.indicatorOf (φ n))
          (LUV.indicatorOf_machineThresholdCodeSeq hφ)).luv n).expect (liaHistory (paperDP T)) n := by
  have hcee := thesis_sentence_is_cee T f φ hφ
  unfold AsympEq at hcee ⊢
  have := hcee.const_mul (-((c : ℝ) + h))
  rw [mul_zero] at this
  refine this.congr fun n => ?_
  simp only [toyX_expect]
  ring

end Paper

section Finite

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S : ThreeStep Ω A₁ A₂)

/-- **The martingale clause, finite form** (T20): on `corr-three-step`'s setting, the two
observation terms sum to the unconditional expectation, `E[X·1_Pr; a₁] + E[X·1_¬Pr; a₁] =
E_μ[X]` (product form, no denominators). The identity constrains only the sum: it does not rule
out `E[X·1_Pr] ≤ 0` for the one event — which is exactly what desideratum 1 asks and what the
tower leaves open. The LI carrier of the same clause is T9.
Source: [[corr-wf14-inventory]] 013, 103; [[corr-wf14-2-inventory]] 2-045 (duplicate); `corr-three-step` `obsExpect`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem threeStep_tower_product_form (a : A₁) (X : Ω → ℝ) :
    S.obsExpect a .press X + S.obsExpect a .silent X = expect (S.μ a) X := by
  unfold ThreeStep.obsExpect expect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  have := S.obsWeight_press_add_silent a ω
  calc (S.μ a).mass ω * S.obsWeight a .press ω * X ω +
        (S.μ a).mass ω * S.obsWeight a .silent ω * X ω
      = (S.μ a).mass ω * (S.obsWeight a .press ω + S.obsWeight a .silent ω) * X ω := by ring
    _ = (S.μ a).mass ω * X ω := by rw [this, mul_one]

end Finite

end Cleanroom.Corrigibility.CorrLiShutdown
