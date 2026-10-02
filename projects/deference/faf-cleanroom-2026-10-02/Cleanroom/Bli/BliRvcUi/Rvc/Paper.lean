import Cleanroom.Bli.BliRvcUi.Rvc.LimitB
import Cleanroom.Bli.BliRvcUi.Rvc.Finite
import Cleanroom.Bli.BliFound.StateSentence

/-!
# `bli-rvc-ui` · Rvc/Paper: real-value coherence (B) at FAF's paper market (T2.3 instance, T2.1 for quote LUVs)

* `quoteLuv_gt_atom` / `quoteLuv_gt_inj`: `bli-found`'s quote LUVs `quoteLuv T m φ` have a single
  quotation atom per threshold, injective in the threshold — so T2.1's `hatom`/`hinj` are
  discharged for them (`rvcB_iff_twoAxiom_quoteLuv`).
* `rvcB_limit_lia`: T2.3 at `liaHistory (paperDP T)` for every quote LUV, on thresholds avoiding
  `1`, grade (a) by `quoteLuv_valuesAt`.
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO.Propositional Finset Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-- A quote-LUV threshold is a single quotation atom.
Source: FAF `arithmeticThresholdLUV`, `quoteAtom`
Kind: L
Fidelity: n/a -/
lemma quoteLuv_gt_atom (m : ℕ) (φ : Sentence) (r : ℚ) :
    ∃ a, (quoteLuv T m φ).gt r = Formula.atom a := ⟨_, rfl⟩

/-- Quote-LUV thresholds are injective in the threshold.
Source: FAF `quotationClaimCode` (a `Nat.pair` code)
Kind: L
Fidelity: n/a -/
lemma quoteLuv_gt_inj (m : ℕ) (φ : Sentence) {r r' : ℚ}
    (h : (quoteLuv T m φ).gt r = (quoteLuv T m φ).gt r') : r = r' := by
  have h1 : quotationClaimCode universalQuotePos universalQuoteNeg
      (Nat.pair (marketQuoteCode T).code (Nat.pair (Nat.pair m (Encodable.encode φ))
        (Encodable.encode r))) =
      quotationClaimCode universalQuotePos universalQuoteNeg
      (Nat.pair (marketQuoteCode T).code (Nat.pair (Nat.pair m (Encodable.encode φ))
        (Encodable.encode r'))) :=
    Formula.atom.inj h
  unfold quotationClaimCode at h1
  simp only [Nat.pair_eq_pair, true_and] at h1
  exact Encodable.encode_inj.mp h1

/-- **T2.1 for quote LUVs**: `RVC_B` ⟺ a two-axiom-coherent extension, with the injectivity
hypotheses discharged.
Source: mandate T2.1 ("discharged … by every FAF quote LUV")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem rvcB_iff_twoAxiom_quoteLuv (m : ℕ) (φ : Sentence) {V : Sentence → ℚ} {R : Finset ℚ} :
    (∃ V' : Sentence → ℚ, (∀ r ∈ R, V' ((quoteLuv T m φ).gt r) = V ((quoteLuv T m φ).gt r)) ∧
      TwoAxiomCoherent V' (thresholdAtoms (quoteLuv T m φ) R)
        (monoFacts (quoteLuv T m φ) R ∪ rangeFacts (quoteLuv T m φ) R)) ↔
    RVC_B (fun ψ => (V ψ : ℝ)) (quoteLuv T m φ) R :=
  rvcB_iff_twoAxiom (fun r _ => quoteLuv_gt_atom T m φ r) (fun _ _ _ _ h => quoteLuv_gt_inj T m φ h)

variable [𝗣𝗔⁻ ⪯ T] [LO.Entailment.Consistent T]

/-- **T2.3 at the paper market**: FAF's inductor `liaHistory (paperDP T)` is `RVC_B` in the limit
on every quote LUV `quoteLuv T m φ`, for every threshold set avoiding `1`. Grade (a): the
representation hypothesis is `bli-found`'s `quoteLuv_valuesAt`.
Source: mandate T2.3; [[bli-program]] M8 (limit form)
Kind: C
Fidelity: exact (with `1 ∉ R`)
Hyps: (a) -/
theorem rvcB_limit_lia (m : ℕ) (φ : Sentence) {R : Finset ℚ} (h1 : (1 : ℚ) ∉ R) :
    RVC_B (limitingBelief (liaHistory (paperDP T))) (quoteLuv T m φ) R :=
  haveI := paperLIA T
  rvcB_limit (paperDP_hworld T) (fun v hv => ⟨_, quoteLuv_valuesAt T m φ v hv⟩) h1

end Cleanroom.Bli.BliRvcUi
