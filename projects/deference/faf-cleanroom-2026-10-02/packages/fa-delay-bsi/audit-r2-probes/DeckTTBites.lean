import Cleanroom.Fa.FaDelayBsi.DeckTT
import LogicalInduction.Construction.Paper.Market

/-!
# fa-delay-bsi · audit r2 (adversarial) · probe: deck-TT is falsifiable (an over-advertising
expert on a refutable family violates it)

The dual of audit r1's `ExpertZero.lean` (deck-TT is free for a silent expert). Over FAF's paper
market, the expert `≡ 1` with the constant refutable family `V ≡ 𝟙⊥` **fails** `DeckTT`: at
threshold `½`, width `¼`, the pair `(A, B) := (𝟙⊥, 𝟙⊤)` is a reflecting pair (the gate
`Ind_{¼}(1 > ½)` is `1`, `𝟙⊤` is valued at `1` and `𝟙⊥ · 1 = 𝟙⊥` in every world), and the deck
inequality `𝔼_n(𝟙⊥) ≳ₙ ½ · 𝔼_n(𝟙⊤)` fails because `𝔼_n(𝟙⊥) → 0` and `𝔼_n(𝟙⊤) → 1`
(the package's own `expect_tendsto_of_determinedVia_tendsto`). So `DeckTT`'s universal
quantifier over reflecting pairs is inhabited for this expert and the notion *bites*: the
definition of record is not satisfied by every expert on every family, which the silent-expert
probe alone left open. Also a check that `DeckTrustQuote`'s fields do not smuggle the conclusion
(a pair satisfying every field can violate the inequality). Not imported by the library.
-/

namespace Cleanroom.Fa.FaDelayBsi.AuditR2

open LogicalInduction LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Propositional
open Cleanroom.Found.LiAsympCalc Cleanroom.Fa.FaDelayBsi
open Filter Topology

section Paper

variable (T : ArithmeticTheory) [T.Δ₁] [Entailment.Consistent T] [𝗜𝚺₁ ⪯ T]

/-- Every world consistent with the theory values `𝟙⊥` at `0`. -/
theorem indicator_bot_valued (DP : DeductiveProcess) (w : PCWorld) (hw : w.ConsistentWithTheory DP) :
    w.ValuesAt (LUV.indicatorOf (⊥ : Sentence)) 0 := by
  have h := (LUV.indicatorOf_isIndicator (⊥ : Sentence) DP).valuesAt hw
  have hnb : ¬ w.Holds (⊥ : Sentence) := fun h => h
  rwa [show w.payout (⊥ : Sentence) = 0 from if_neg hnb] at h

/-- Every world consistent with the theory values `𝟙⊤` at `1`. -/
theorem indicator_top_valued (DP : DeductiveProcess) (w : PCWorld) (hw : w.ConsistentWithTheory DP) :
    w.ValuesAt (LUV.indicatorOf (⊤ : Sentence)) 1 := by
  have h := (LUV.indicatorOf_isIndicator (⊤ : Sentence) DP).valuesAt hw
  rwa [show w.payout (⊤ : Sentence) = 1 from if_pos (PCWorld.holds_top w)] at h

/-- `(𝟙⊥, 𝟙⊤)` is a reflecting pair for the expert `≡ 1` on `V ≡ 𝟙⊥` at `(v, δ) = (½, ¼)`. -/
theorem overadvertising_pair :
    DeckTrustQuote (liaHistory (paperDP T)) (paperDP T) (fun _ => (1 : ℝ))
      (fun _ => LUV.indicatorOf (⊥ : Sentence)) (fun _ => (1 / 2 : ℚ)) (fun _ => (1 / 4 : ℚ))
      (fun _ => LUV.indicatorOf (⊥ : Sentence)) (fun _ => LUV.indicatorOf (⊤ : Sentence)) := by
  have hgate : ctsInd (1 / 4 : ℚ) (1 : ℝ) ((1 / 2 : ℚ) : ℝ) = 1 :=
    (ctsInd_eq_one_iff (by norm_num) _ _).2 (by norm_num)
  exact
    { delta_pos := fun _ => by norm_num
      delta_codes := MachineRatCodes.const _
      threshold_mem := fun _ => by norm_num
      threshold_generable := PGenerableRat.ofMachineRatCodes (MachineRatCodes.const _) _
      value_codes := LUV.indicatorOf_machineThresholdCodeSeq (MachineSentenceCodes.const _)
      product_codes := LUV.indicatorOf_machineThresholdCodeSeq (MachineSentenceCodes.const _)
      confidence_codes := LUV.indicatorOf_machineThresholdCodeSeq (MachineSentenceCodes.const _)
      source_valued := fun _ w hw => ⟨_, indicator_bot_valued (paperDP T) w hw⟩
      confidence_reflected := fun _ w hw => by
        show w.ValuesAt _ (ctsInd (1 / 4 : ℚ) (1 : ℝ) ((1 / 2 : ℚ) : ℝ))
        rw [hgate]
        exact indicator_top_valued (paperDP T) w hw
      product_reflected := fun _ w hw x hx => by
        show w.ValuesAt _ (x * ctsInd (1 / 4 : ℚ) (1 : ℝ) ((1 / 2 : ℚ) : ℝ))
        rw [hgate, mul_one]
        exact hx }

/-- **Deck-TT fails for the over-advertising expert on the refutable family.** -/
theorem deckTT_overadvertising_false :
    ¬ DeckTT (liaHistory (paperDP T)) (paperDP T) (fun _ => (1 : ℝ))
      (fun _ => LUV.indicatorOf (⊥ : Sentence)) := by
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := paperLIA T
  intro h
  have hq := overadvertising_pair T
  have hge := h _ _ _ _ hq
  have hA : Tendsto (fun n => (LUV.indicatorOf (⊥ : Sentence)).expect (liaHistory (paperDP T)) n)
      atTop (𝓝 0) :=
    expect_tendsto_of_determinedVia_tendsto (liaHistory (paperDP T)) (paperDP T) _
      hq.product_codes (fun _ => 0) (fun _ w hw => indicator_bot_valued (paperDP T) w hw) 0
      tendsto_const_nhds (paperDP_hworld T)
  have hB : Tendsto (fun n => (LUV.indicatorOf (⊤ : Sentence)).expect (liaHistory (paperDP T)) n)
      atTop (𝓝 1) :=
    expect_tendsto_of_determinedVia_tendsto (liaHistory (paperDP T)) (paperDP T) _
      hq.confidence_codes (fun _ => 1) (fun _ w hw => indicator_top_valued (paperDP T) w hw) 1
      tendsto_const_nhds (paperDP_hworld T)
  have hev := hge (1 / 8) (by norm_num)
  have hA' := (Metric.tendsto_nhds.1 hA) (1 / 8) (by norm_num)
  have hB' := (Metric.tendsto_nhds.1 hB) (1 / 8) (by norm_num)
  obtain ⟨n, h1, h2, h3⟩ := (hev.and (hA'.and hB')).exists
  dsimp only at h1
  rw [Real.dist_eq, _root_.sub_zero, abs_lt] at h2
  rw [Real.dist_eq, abs_lt] at h3
  push_cast at h1
  linarith [h1, h2.2, h3.1]

end Paper

end Cleanroom.Fa.FaDelayBsi.AuditR2

#print axioms Cleanroom.Fa.FaDelayBsi.AuditR2.deckTT_overadvertising_false
