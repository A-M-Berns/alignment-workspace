import Cleanroom.Fa.FaDelayBsi.DeckTT
import Cleanroom.Li.LiDiagonal.Paper
import Cleanroom.Found.LiQuoteLane.PaperSelf
import LogicalInduction.Construction.Paper.Market

/-!
# `fa-delay-bsi` · SelfInstance (T6, W3, W4): deck-TT is inhabited by the self-trust instance

* **T6** `selfTrustQuote_deckTrustQuote`: FAF's `SelfTrustQuote` certificate (minus its `affine`
  field) *is* a `DeckTrustQuote` with expert `H`'s own future price and the indicator LUVs
  (`L`); `deckTT_self_paper`: over FAF's paper market, for every e.c. sentence family `φ`,
  `DeckTT` holds with expert `n ↦ P_{f n}(φ n)` — FAF's `thm:st` (`lic_self_trust_closed`)
  on the pair FAF's `paperConfidenceQuoteCode` builds, transported to every other reflecting
  pair by `deckTT_of_pair` (`C`). **One market, no joint clearing.**
* **W3** `deckTT_self_paper_nondegenerate`: at the deferred Kleene diagonal, thresholds
  `p' + δ < p`, both sides of the deck inequality have positive limits `p > p'` —
  `li-diagonal`'s `paper_soft_self_trust_nondegenerate`, re-packaged (`N+`).
* **W4** `deckTTConst_accelerator_paper_self`: the same-market accelerator instance of T7's
  `deckTT_const_accelerator` — `A' = H` over the paper market, the cross-quote package
  `li-quote-lane`'s `crossQuotePackage_paper_self` — every hypothesis derived (a).

This is the only file of the package importing `Construction.Paper.Market`.
-/

namespace Cleanroom.Fa.FaDelayBsi

open LogicalInduction LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Propositional
open Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Fa.FaTheoremA
open Cleanroom.Li.LiDiagonal
open Filter Topology

/-! ## A. T6: FAF's self-trust certificate is a deck-TT reflecting pair -/

/-- **T6 (headline, L). FAF's `thm:st` certificate is a deck-TT reflecting pair.** A
`SelfTrustQuote H DPH f φ δ p A B` (with `δ` machine-codeable) gives
`DeckTrustQuote H DPH (fun n => H (f n) (φ n)) (fun n => 𝟙(φ n)) p δ A B`: the
`confidence_reflected` / `product_reflected` fields match verbatim, the indicator's world value
being its payout (`LUV.indicatorOf_isIndicator`); the `affine` certificate is dropped (it is FAF's
proof device, not part of the notion). The deck's expert is the human's own future *price*
`P_{f n}(φ n)` — FAF's `thm:st` object (the future expectation of the indicator differs by the
price gap of `φ ⋏ ∼∼φ` against `φ`, which `thm:ei` closes asymptotically; findings).
Scope: same market; expert = own future price; indicator LUVs.
Source: [[delay-program]] §4 line 182, §6 T8 (root-fa-036: "with `E* := 𝔼^H_{f(n)}`, deck-TT is the paper's Self-Trust theorem `st` 4.12.4"); FAF `SelfTrustQuote` (`Properties/SelfTrust.lean:420`)
Kind: L
Fidelity: variant: expert is the future price (FAF's `thm:st` object); sentence families through their indicators
Hyps: (a) none (`hδ` is the width's own certificate) -/
theorem selfTrustQuote_deckTrustQuote {H : History} {DPH : DeductiveProcess}
    {f : DeferralFunction} {φ : ℕ → Sentence} {δ p : ℕ → ℚ} {A B : ℕ → LUV}
    (hst : SelfTrustQuote H DPH f φ δ p A B) (hδ : MachineRatCodes δ) :
    DeckTrustQuote H DPH (fun n => H (f.f n) (φ n)) (fun n => LUV.indicatorOf (φ n)) p δ A B where
  delta_pos := hst.delta_pos
  delta_codes := hδ
  threshold_mem := hst.probability_mem
  threshold_generable := hst.probability_generable
  value_codes := LUV.indicatorOf_machineThresholdCodeSeq hst.sentence_codes
  product_codes := hst.product_codes
  confidence_codes := hst.confidence_codes
  source_valued := fun n w hw => ⟨_, (LUV.indicatorOf_isIndicator (φ n) DPH).valuesAt hw⟩
  confidence_reflected := hst.confidence_reflected
  product_reflected := fun n w hw x hx => by
    have hxe : x = w.payout (φ n) :=
      hx.eq ((LUV.indicatorOf_isIndicator (φ n) DPH).valuesAt hw)
    rw [hxe]
    exact hst.product_reflected n w hw

/-! ## B. The paper-market instance -/

section Paper

variable (T : ArithmeticTheory) [T.Δ₁] [Entailment.Consistent T] [𝗜𝚺₁ ⪯ T]

omit [Entailment.Consistent T] in
/-- **FAF's own pair is a deck-TT reflecting pair over the paper market**: for an e.c. sentence
family `φ`, widths `δ` (positive, machine-codeable) and generable thresholds `v` in `[0,1]`, the
pair `(indicatorProductLUV (paperConfidenceQuoteCode …) φ, (paperConfidenceQuoteCode …).luv)`
satisfies `DeckTrustQuote` with expert `n ↦ P_{f n}(φ n)`. The reflecting fields are FAF's
`RationalQuoteCode.reflected` and `indicatorProductLUV_valuesAt`, cast by
`paperConfidence_value_cast`.
Scope: same market (the paper market); expert = own future price; indicator LUVs.
Source: FAF `lic_self_trust_closed` (`Construction/Paper/Market.lean`); [[fa-delay-bsi-mandate]] T6
Kind: L
Fidelity: exact (FAF's certificate, re-packaged)
Hyps: (a) none -/
theorem paper_pair_deckTrustQuote (f : DeferralFunction) (φ : ℕ → Sentence)
    (hφ : MachineSentenceCodes φ) (δ v : ℕ → ℚ) (hδpos : ∀ n, 0 < δ n) (hδ : MachineRatCodes δ)
    (hv : ∀ n, 0 ≤ v n ∧ v n ≤ 1) (hgen : PGenerableRat (liaHistory (paperDP T)) v) :
    DeckTrustQuote (liaHistory (paperDP T)) (paperDP T)
      (fun n => liaHistory (paperDP T) (f.f n) (φ n)) (fun n => LUV.indicatorOf (φ n)) v δ
      (fun n => indicatorProductLUV (paperConfidenceQuoteCode T f φ hφ δ v hδ.computable hgen) φ n)
      (paperConfidenceQuoteCode T f φ hφ δ v hδ.computable hgen).luv := by
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  refine
    { delta_pos := hδpos
      delta_codes := hδ
      threshold_mem := hv
      threshold_generable := hgen
      value_codes := LUV.indicatorOf_machineThresholdCodeSeq hφ
      product_codes := indicatorProductLUV_machineThresholdCodeSeq _ hφ
      confidence_codes := (paperConfidenceQuoteCode T f φ hφ δ v hδ.computable hgen).poly
      source_valued := fun n w hw => ⟨_, (LUV.indicatorOf_isIndicator (φ n) _).valuesAt hw⟩
      confidence_reflected := fun n w hw => ?_
      product_reflected := fun n w hw x hx => ?_ }
  · have h := RationalQuoteCode.reflected (paperQuotationPresentation T)
      (paperConfidenceQuoteCode T f φ hφ δ v hδ.computable hgen) n w hw
    rwa [← paperConfidence_value_cast T f φ δ v n] at h
  · have h := indicatorProductLUV_valuesAt (paperQuotationPresentation T)
      (paperConfidenceQuoteCode T f φ hφ δ v hδ.computable hgen) φ n w hw
    rw [← paperConfidence_value_cast T f φ δ v n] at h
    have hxe : x = w.payout (φ n) :=
      hx.eq ((LUV.indicatorOf_isIndicator (φ n) _).valuesAt hw)
    rw [hxe]
    exact h

/-- **T6 (headline). Deck-TT is inhabited, with one market, by the self-trust instance.** Over
FAF's paper market `P := liaHistory (paperDP T)`, for every e.c. sentence family `φ` and every
deferral `f`: `DeckTT P (paperDP T) (fun n => P (f n) (φ n)) (fun n => 𝟙(φ n))` — for the *full*
generable threshold family `v`, every positive machine-codeable width `δ`, and every reflecting
pair `(A, B)`: `𝔼_n(𝟙(φ_n)·Ind_δ(P_{f n}(φ_n) > v_n)) ≳ₙ v_n·𝔼_n(Ind_δ(P_{f n}(φ_n) > v_n))`. Proof:
FAF's `thm:st` closed form (`lic_self_trust_closed`) on FAF's own pair, transported to the given
pair by `deckTT_of_pair` (every reflecting pair has the same expectations). No joint clearing:
the "expert" is the human's own future self.
Scope: same market; expert = own future price; indicator LUVs; deferral `f` arbitrary.
Source: [[delay-program]] §4 line 182 ("the self-trust instance satisfies varying-question TT with one market and no joint clearing"), §6 T8 (root-fa-036); FAF `thm:st` (`lic_self_trust_closed`)
Kind: C
Fidelity: variant: as `selfTrustQuote_deckTrustQuote` (expert is the future price; indicator LUVs — the LUV-valued family form is `deckTT_self_luv_open`)
Hyps: (a) none (`hφ` is the family's e.c. certificate) -/
theorem deckTT_self_paper (f : DeferralFunction) (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) :
    DeckTT (liaHistory (paperDP T)) (paperDP T) (fun n => liaHistory (paperDP T) (f.f n) (φ n))
      (fun n => LUV.indicatorOf (φ n)) := by
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := paperLIA T
  intro v δ A B hq
  have hst := lic_self_trust_closed T f φ δ v hq.delta_pos hq.threshold_mem hφ hq.delta_codes
    hq.threshold_generable
  exact deckTT_of_pair (paper_pair_deckTrustQuote T f φ hφ δ v hq.delta_pos hq.delta_codes
    hq.threshold_mem hq.threshold_generable) hq (paperDP_hworld T) hst

omit [Entailment.Consistent T] in
/-- **T6, non-vacuity at every threshold pair.** `DeckTT` quantifies over reflecting pairs and
would hold vacuously where none exists; over the paper market a reflecting pair exists for *every*
positive machine-codeable width `δ` and generable threshold family `v` in `[0,1]` (FAF's
`paperConfidenceQuoteCode`), so `deckTT_self_paper` is a claim at every `(v, δ)` in its class.
Scope: same market; expert = own future price; indicator LUVs.
Source: [[fa-delay-bsi-mandate]] T6 (non-vacuity); [[STANDARDS]] §3 ("a definition that makes the headline trivially true is the worst failure")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem deckTT_self_paper_inhabited (f : DeferralFunction) (φ : ℕ → Sentence)
    (hφ : MachineSentenceCodes φ) (δ v : ℕ → ℚ) (hδpos : ∀ n, 0 < δ n) (hδ : MachineRatCodes δ)
    (hv : ∀ n, 0 ≤ v n ∧ v n ≤ 1) (hgen : PGenerableRat (liaHistory (paperDP T)) v) :
    ∃ A B : ℕ → LUV, DeckTrustQuote (liaHistory (paperDP T)) (paperDP T)
      (fun n => liaHistory (paperDP T) (f.f n) (φ n)) (fun n => LUV.indicatorOf (φ n)) v δ A B :=
  ⟨_, _, paper_pair_deckTrustQuote T f φ hφ δ v hδpos hδ hv hgen⟩

/-- **W3 (N+). The self-trust instance of deck-TT is non-degenerate.** At the deferred Kleene
diagonal `χ := defDiag (kleeneDiag T market p) succDeferral` (a deferred, non-constant family),
threshold `p'` and width `δ` with `0 < p'`, `p' + δ < p < 1`: there is a reflecting pair (FAF's
own) for which `𝔼_n(A_n) → p` and `p'·𝔼_n(B_n) → p'`, with `p' < p` — both sides positive, the
inequality holding with slack `p − p'`. `li-diagonal`'s `paper_soft_self_trust_nondegenerate`,
re-packaged into `DeckTrustQuote`. **The gate saturates:** since the expert `P_{n+1}(χ_n) → p` and
`p' + δ < p`, the ramp `Ind_δ(P_{n+1}(χ_n) > p')` is eventually `≡ 1`, so `𝔼_n(B_n) → 1` and the
witness exercises the above-threshold inequality with slack `p − p'` but not the ramp's interior;
a partially open gate (`p' < p < p' + δ`) would be the sharper exercise and is not built (audit r1
fidelity non-blocking 3, adversarial non-blocking 3).
Scope: same market; threshold `p`, deferral `n+1`; `defDiag` of the paper market's Kleene diagonal; gate saturated.
Source: [[delay-program]] §6 T8 (root-fa-036); [[fa-delay-bsi-mandate]] W3; `Cleanroom.Li.LiDiagonal.paper_soft_self_trust_nondegenerate`
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem deckTT_self_paper_nondegenerate (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) (δ p' : ℚ)
    (hδ : 0 < δ) (hp'0 : 0 < p') (hlt : p' + δ < p) :
    ∃ A B : ℕ → LUV,
      DeckTrustQuote (liaHistory (paperDP T)) (paperDP T)
        (fun n => liaHistory (paperDP T) (succDeferral.f n)
          (defDiag (kleeneDiag T (paperMarketComputation T) p) succDeferral n))
        (fun n => LUV.indicatorOf (defDiag (kleeneDiag T (paperMarketComputation T) p)
          succDeferral n))
        (fun _ => p') (fun _ => δ) A B ∧
      Tendsto (fun n => (A n).expect (liaHistory (paperDP T)) n) atTop (𝓝 (p : ℝ)) ∧
      Tendsto (fun n => (p' : ℝ) * (B n).expect (liaHistory (paperDP T)) n) atTop
        (𝓝 (p' : ℝ)) ∧
      (0 : ℝ) < p' ∧ (p' : ℝ) < p := by
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  refine ⟨_, _, paper_pair_deckTrustQuote T succDeferral _
    (defDiag_codes_succ (kleeneDiag_codes T (paperMarketComputation T) p)) (fun _ => δ)
    (fun _ => p') (fun _ => hδ) (MachineRatCodes.const δ) (fun _ => ⟨hp'0.le, by linarith⟩)
    (PGenerableRat.ofMachineRatCodes (MachineRatCodes.const p') _), ?_⟩
  exact paper_soft_self_trust_nondegenerate T p hp0 hp1 δ p' hδ hp'0 hlt

/-- **W4 (one-way instance of T7, at (a)).** Over the paper market with `A' = H`, the accelerator
`a_n := 𝔼^H_n(⌜𝔼^H_{f n}(V)⌝)` (FAF's `cee` quote, `li-quote-lane`'s `crossQuotePackage_paper_self`)
satisfies constant-threshold deck-TT for every e.c. valued `V`: every hypothesis of
`deckTT_const_accelerator` is derived on a real market — the ledger ("H reads A") is
`H` reading itself, and `pkg.reflected` is FAF's own Σ₁ quotation. N+ for the hypothesis
package; N− for the content (fixed `V`: the gate converges, and at a decided `V` both sides are
eventually constant).
Scope: same market (one-way, visibility by construction); fixed `V`.
Source: [[delay-program]] §6 T7 (root-fa-033: "the one-way instance at (a): `A' := H`"); [[fa-delay-bsi-mandate]] W4
Kind: N+
Fidelity: exact (instance of `deckTT_const_accelerator`)
Hyps: (a) `hcode`; (c) per FAF `hval` (`thm:ec`) -/
theorem deckTTConst_accelerator_paper_self (f : DeferralFunction) (V : LUV)
    (hcode : V.MachineThresholdCodes)
    (hval : ∀ w : PCWorld, w.ConsistentWithTheory (paperDP T) → ∃ x : ℝ, w.ValuesAt V x) :
    DeckTTConst (liaHistory (paperDP T)) (paperDP T)
      (accelerator (paperDeferredExpectationQuoteCode T f (fun _ => V)
        (machineThresholdCodeSeq_const hcode)).luv (liaHistory (paperDP T)))
      (fun _ => V) := by
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := paperLIA T
  exact deckTT_const_accelerator V hcode (paperDP_hworld T) hval (paperDP_hworld T)
    (crossQuotePackage_paper_self T f (fun _ => V) (machineThresholdCodeSeq_const hcode))

/-! ## C. A reflecting pair for the accelerator expert (T7's non-vacuity at W4) -/

/-- **The gate quote code of the accelerator**: FAF's `RationalQuoteCode` whose day-`n` value is
`ratCtsInd δ (𝔼^H_n(Y_n)) v`, the ramp of the market program's own exact expectation quote
(`expectQuoteAt Y n n`) — the same pattern as FAF's `paperConfidenceQuoteCode`, with the
expectation quote in place of the deferred price.
Source: FAF `paperConfidenceQuoteCode`, `MarketComputation.expectQuoteAt_computable`; [[fa-delay-bsi-mandate]] T7 (W4)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def accelGateCode (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) (δ v : ℚ) :
    RationalQuoteCode T (fun n =>
      ratCtsInd δ ((paperMarketComputation T).expectQuoteAt Y n n) v) :=
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  have hq : Computable fun n => (paperMarketComputation T).expectQuoteAt Y n n :=
    (((paperMarketComputation T).expectQuoteAt_computable hY).comp
      (Computable.id.pair Computable.id) : _)
  have hval : Computable fun n =>
      ratCtsInd δ ((paperMarketComputation T).expectQuoteAt Y n n) v :=
    (ratCtsInd_computable.comp ((Computable.const δ).pair (hq.pair (Computable.const v))) : _)
  RationalQuoteCode.ofComputable T hval (fun _ => ratCtsInd_mem_Icc _ _ _)

/-- **T7's reflecting pair exists over the paper market.** For any e.c. quote family `Y`, any
sentence `ψ`, constant threshold `v ∈ [0,1]` and width `δ > 0`, the pair
`(indicatorProductLUV (accelGateCode …) (fun _ => ψ), (accelGateCode …).luv)` is a
`DeckTrustQuote` for the expert `accelerator Y H` (`H` the paper market) on the constant family
`𝟙 ψ`: the gate LUV is valued at `Ind_δ(𝔼^H_n(Y_n) > v)` in every completed world
(`RationalQuoteCode.reflected`, `expectQuoteAt_cast`, `ratCtsInd_cast`) and the product at
`payout(ψ)` times it (`indicatorProductLUV_valuesAt`). So `deckTT_const_accelerator`'s inner
quantification over reflecting pairs is inhabited at the W4 instance — the theorem is not
vacuous there.
Scope: same market (the paper market); fixed `V = 𝟙 ψ`; constant thresholds.
Source: [[fa-delay-bsi-mandate]] T7 (W4); [[STANDARDS]] §3 (non-vacuity)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem accelerator_pair_paper (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) (ψ : Sentence)
    (δ v : ℚ) (hδ : 0 < δ) (hv : 0 ≤ v ∧ v ≤ 1) :
    DeckTrustQuote (liaHistory (paperDP T)) (paperDP T) (accelerator Y (liaHistory (paperDP T)))
      (fun _ => LUV.indicatorOf ψ) (fun _ => v) (fun _ => δ)
      (fun n => indicatorProductLUV (accelGateCode T Y hY δ v) (fun _ => ψ) n)
      (accelGateCode T Y hY δ v).luv := by
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  have hcast : ∀ n, ctsInd δ (accelerator Y (liaHistory (paperDP T)) n) (v : ℝ) =
      ((ratCtsInd δ ((paperMarketComputation T).expectQuoteAt Y n n) v : ℚ) : ℝ) := by
    intro n
    rw [accelerator_eq, (paperMarketComputation T).expectQuoteAt_cast Y n n, ratCtsInd_cast]
  refine
    { delta_pos := fun _ => hδ
      delta_codes := MachineRatCodes.const δ
      threshold_mem := fun _ => hv
      threshold_generable := PGenerableRat.ofMachineRatCodes (MachineRatCodes.const v) _
      value_codes := LUV.indicatorOf_machineThresholdCodeSeq (MachineSentenceCodes.const ψ)
      product_codes := indicatorProductLUV_machineThresholdCodeSeq _ (MachineSentenceCodes.const ψ)
      confidence_codes := (accelGateCode T Y hY δ v).poly
      source_valued := fun n w hw => ⟨_, (LUV.indicatorOf_isIndicator ψ _).valuesAt hw⟩
      confidence_reflected := fun n w hw => ?_
      product_reflected := fun n w hw x hx => ?_ }
  · rw [hcast n]
    exact RationalQuoteCode.reflected (paperQuotationPresentation T) (accelGateCode T Y hY δ v)
      n w hw
  · have h := indicatorProductLUV_valuesAt (paperQuotationPresentation T)
      (accelGateCode T Y hY δ v) (fun _ => ψ) n w hw
    have hxe : x = w.payout ψ := hx.eq ((LUV.indicatorOf_isIndicator ψ _).valuesAt hw)
    rw [hxe, hcast n]
    exact h

/-- **W4's inner quantifier is inhabited**: at the same-market accelerator instance
(`deckTTConst_accelerator_paper_self` with `V := 𝟙 ψ`), a reflecting pair exists for every
constant `v ∈ [0,1]`, `δ > 0`.
Source: [[fa-delay-bsi-mandate]] W4; [[STANDARDS]] §3
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem deckTTConst_accelerator_paper_self_inhabited (f : DeferralFunction) (ψ : Sentence)
    (hcode : (LUV.indicatorOf ψ).MachineThresholdCodes) (δ v : ℚ) (hδ : 0 < δ)
    (hv : 0 ≤ v ∧ v ≤ 1) :
    ∃ A B : ℕ → LUV, DeckTrustQuote (liaHistory (paperDP T)) (paperDP T)
      (accelerator (paperDeferredExpectationQuoteCode T f (fun _ => LUV.indicatorOf ψ)
        (machineThresholdCodeSeq_const hcode)).luv (liaHistory (paperDP T)))
      (fun _ => LUV.indicatorOf ψ) (fun _ => v) (fun _ => δ) A B :=
  ⟨_, _, accelerator_pair_paper T _ (paperDeferredExpectationQuoteCode T f _
    (machineThresholdCodeSeq_const hcode)).poly ψ δ v hδ hv⟩

end Paper

end Cleanroom.Fa.FaDelayBsi
