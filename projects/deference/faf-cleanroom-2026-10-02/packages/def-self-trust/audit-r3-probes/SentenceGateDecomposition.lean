import Cleanroom.Deference.DefSelfTrust.Legitimacy

/-!
# Audit probe (def-self-trust, round 3, fidelity): the modified-Tower decomposition needs no
generable gate

`modifiedTower_decomposition` (`Legitimacy.lean`, target 4b) proves the note's modified Tower
`E_n(X_n) ≈ₙ E_n(⌜E_{f n}(X_n)·w_{f n}⌝) + E_n(⌜E_{f n}(X_n)·(1 − w_{f n})⌝)` for a `[0,1]`
**P-generable** weight `w`, and finding F6 / `correctionFunction_idle` conclude that "the
proposal has content only for a non-generable gate". But the note's legitimacy
(`li-deference.md` 51–65) is a property of *worlds* ("illegitimate worlds", "corrupt feedback"),
i.e. a sentence, not a feature of prices — and the decomposition is a **pointwise identity**
(`e = e·1[L] + e·1[¬L]` in every world), so it holds at any e.c. *sentence* gate `L_n` with no
generability at all: FAF's `indicatorProductLUV` of the deferred-expectation quote with `L_n`
and with `∼L_n`, one exact `thm:expprovind` bet, and `cee`. This probe proves exactly that,
with the package's own tools (`constComb`, `deferredExpectationQuote_reflected`,
`lic_expect_combination_provind_eq`) and no `PGenerableRat` anywhere.

Consequence for F6: the correction function is idle at expectation level for a single inductor
at *every* e.c. legitimacy sentence, generable or not; generability is where `ccee` enters the
*gated tower* (4a / 4c(ii)), not the decomposition (4b). F6's sentence "the program's content is
the non-generable case" is right for 4a and wrong for 4b. Not imported by the library. -/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-- The payout of a negation is one minus the payout. -/
theorem payout_neg (v : PCWorld) (φ : Sentence) : v.payout (∼φ) = 1 - v.payout φ := by
  by_cases h : v.Holds φ
  · have h' : ¬ v.Holds (∼φ) := fun hn => ((PCWorld.holds_neg v φ).1 hn) h
    simp [PCWorld.payout, h, h']
  · have h' : v.Holds (∼φ) := (PCWorld.holds_neg v φ).2 h
    simp [PCWorld.payout, h, h']

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- The left summand: `⌜E_{f n}(X_n) · 1[L_n]⌝` (FAF's exact indicator product). -/
def sentenceGateLeft (f : DeferralFunction) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    (L : ℕ → Sentence) : ℕ → LUV :=
  fun n => indicatorProductLUV (paperDeferredExpectationQuoteCode T f X hX) L n

/-- The right summand: `⌜E_{f n}(X_n) · 1[¬L_n]⌝`. -/
def sentenceGateRight (f : DeferralFunction) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    (L : ℕ → Sentence) : ℕ → LUV :=
  fun n => indicatorProductLUV (paperDeferredExpectationQuoteCode T f X hX) (fun n => ∼(L n)) n

/-- **The modified-Tower decomposition at a sentence gate, no generability:** for every e.c.
world-valued `X` and every e.c. sentence family `L`,
`E_n(X_n) ≈ₙ E_n(⌜E_{f n}(X_n)·1[L_n]⌝) + E_n(⌜E_{f n}(X_n)·1[¬L_n]⌝)`. -/
theorem modifiedTower_decomposition_sentenceGate (f : DeferralFunction) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X)
    (L : ℕ → Sentence) (hL : MachineSentenceCodes L) :
    (fun n => (X n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (sentenceGateLeft T f hX L n).expect (liaHistory (paperDP T)) n +
        (sentenceGateRight T f hX L n).expect (liaHistory (paperDP T)) n) := by
  set Q := (paperDeferredExpectationQuoteCode T f X hX).luv with hQ
  set ZL := sentenceGateLeft T f hX L with hZL
  set ZN := sentenceGateRight T f hX L with hZN
  have hcee := lic_expected_future_expectations_closed T f X hX hval
  set terms : List (ℚ × (ℕ → LUV)) := [(1, Q), (-1, ZL), (-1, ZN)] with hterms
  have hcodes : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact (paperDeferredExpectationQuoteCode T f X hX).poly
    · exact indicatorProductLUV_machineThresholdCodeSeq _ hL
    · exact indicatorProductLUV_machineThresholdCodeSeq _ hL.neg
  have hQr := deferredExpectationQuote_reflected T f X hX
  have hZLr : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      v.ValuesAt (ZL n) (v.payout (L n) * (X n).expect (liaHistory (paperDP T)) (f n)) := by
    intro n v hv
    have h := indicatorProductLUV_valuesAt (paperQuotationPresentation T)
      (paperDeferredExpectationQuoteCode T f X hX) L n v hv
    -- `convert` leaves the `set`-local unfolding (`rfl`) and the cast identity
    -- `LUV.expect … = ↑(expectQuoteAt …)` (FAF's `expectQuoteAt_cast`)
    have hc := (paperMarketComputation T).expectQuoteAt_cast X n (f.f n)
    convert h using 3
    all_goals first | rfl | exact hc
  have hZNr : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      v.ValuesAt (ZN n) ((1 - v.payout (L n)) * (X n).expect (liaHistory (paperDP T)) (f n)) := by
    intro n v hv
    have h := indicatorProductLUV_valuesAt (paperQuotationPresentation T)
      (paperDeferredExpectationQuoteCode T f X hX) (fun n => ∼(L n)) n v hv
    simp only [payout_neg] at h
    -- `convert` leaves the `set`-local unfolding (`rfl`) and the cast identity
    -- `LUV.expect … = ↑(expectQuoteAt …)` (FAF's `expectQuoteAt_cast`)
    have hc := (paperMarketComputation T).expectQuoteAt_cast X n (f.f n)
    convert h using 3
    all_goals first | rfl | exact hc
  have hwv : LUVCombination.WorldValued (constComb 0 terms) (paperDP T) := fun n v hv => by
    refine ⟨worldValue v, fun p hp => ?_⟩
    obtain ⟨q, hq, hpq⟩ := mem_constComb_terms hp
    rw [hpq]
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact valuesAt_worldValue (hQr n v hv)
    · exact valuesAt_worldValue (hZLr n v hv)
    · exact valuesAt_worldValue (hZNr n v hv)
  have hvalb : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      ∀ ν, (constComb 0 terms n).ValuesAt v ν →
        (constComb 0 terms n).value (liaHistory (paperDP T)) ν = 0 := by
    intro n v hv ν hν
    have e₁ := (hν (EF.const 1, Q n) (by simp [constComb, hterms])).eq (hQr n v hv)
    have e₂ := (hν (EF.const (-1), ZL n) (by simp [constComb, hterms])).eq (hZLr n v hv)
    have e₃ := (hν (EF.const (-1), ZN n) (by simp [constComb, hterms])).eq (hZNr n v hv)
    rw [constComb_value]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e₁, e₂, e₃]
    push_cast
    ring
  have hbet := lic_expect_combination_provind_eq
    (constComb_boundedSequence (liaHistory (paperDP T)) 0 terms hcodes) hwv 0 hvalb
    (paperDP_hworld T)
  have hE : (fun n => (constComb 0 terms n).expect (liaHistory (paperDP T)) n) =
      (fun n => (Q n).expect (liaHistory (paperDP T)) n -
        ((ZL n).expect (liaHistory (paperDP T)) n + (ZN n).expect (liaHistory (paperDP T)) n)) := by
    funext n
    rw [constComb_expect]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring
  rw [hE] at hbet
  have hQZ : (fun n => (Q n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (ZL n).expect (liaHistory (paperDP T)) n +
        (ZN n).expect (liaHistory (paperDP T)) n) := by
    unfold AsympEq at hbet ⊢
    simpa using hbet
  exact hcee.trans hQZ

end

end Cleanroom.Deference.DefSelfTrust
