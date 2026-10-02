import Cleanroom.Found.DefLattice.TwoOptionLUV
import LogicalInduction.Construction.Paper.Market
import LogicalInduction.Framework.Machine.Witnesses

/-!
# The N+ witness: FAF's self-trust package over the paper's inductor is a ramp `WeightQuote`

Package `def-lattice`, the one file importing `LogicalInduction.Construction.Paper.Market`.

Over the constructed inductor `liaHistory (paperDP T)` (`T` a `Δ₁` arithmetic theory
extending `𝗣𝗔⁻`, consistent), with the **day-varying** sentence source `φ n := ⌜aₙ⌝` (the
atom family, `machineSentenceCodes_atom`), constant width `δ > 0` and constant threshold
`s ∈ [0,1]`:

* `selfTrustQuoteWitness` — FAF's complete `thm:st` package `SelfTrustQuote`, assembled by
  FAF's `selfTrustQuoteOfRepresentation` from the market's own confidence-quote code
  (`paperConfidenceQuoteCode`) and its indicator-product LUV (`indicatorProductLUV`);
* `weightQuoteWitness` — its image under `WeightQuote.of_selfTrustQuote`: a `WeightQuote` for
  the self-expert, source `literalIndicator ∘ φ`, weight `rampAbove δ s`, **`slack ≡ 0`**
  (`weightQuoteWitness_slack`) — the full hypothesis package of `ThresholdIneqAbove` at
  `SoftTotalTrustAbove … s δ`, inhabited (`softTotalTrustAbove_package_inhabited`);
* `witness_twoOption_value` — the closed `st` conclusion **is** Value against the constant on
  the hedged two-option menu: `E^H_n(twoOptionComb s XW W n) ≳ₙ s`.

Grade **N+**: a real inductor, a source that varies with the day (`witnessSource_nonconstant`),
positive width, no constant sequences anywhere but the threshold and width the mandate fixes.
-/

namespace Cleanroom.Found.DefLattice.Witness

open LogicalInduction Filter Topology
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- The paper's constructed market is a logical inductor over `paperDP T` (FAF's `paperLIA`),
registered as an instance for this file so that `Expert.self` can be formed in statements.
Source: FAF `Construction/Paper/TheoremDP.lean` `paperLIA`
Kind: L
Fidelity: n/a -/
instance instPaperLIA : IsLogicalInductor (liaHistory (paperDP T)) (paperDP T) := paperLIA T

/-- The day-varying source sentences: the atom family `n ↦ ⌜aₙ⌝`.
Source: FAF `Framework/Machine/Witnesses.lean` (`machineSentenceCodes_atom`)
Kind: D
Fidelity: n/a -/
abbrev atomFamily : ℕ → Sentence := fun n => (Formula.atom n : Sentence)

/-- The constant threshold `s` is P-generable (a constant is a `MachineRatCodes`).
Source: FAF `PGenerableRat.ofMachineRatCodes`, `MachineRatCodes.const`
Kind: L
Fidelity: n/a -/
def sGenerable (s : ℚ) : PGenerableRat (liaHistory (paperDP T)) (fun _ => s) :=
  PGenerableRat.ofMachineRatCodes (MachineRatCodes.const s) _

variable (f : DeferralFunction) (δ s : ℚ)

/-- FAF's confidence-quote code of the paper market at the deferred day: the quoted rational
`ratCtsInd δ (P_{f(n)}(⌜aₙ⌝)) s`.
Source: FAF `paperConfidenceQuoteCode` (`Construction/Paper/Market.lean`)
Kind: D
Fidelity: n/a -/
def confidenceCode :=
  paperConfidenceQuoteCode T f atomFamily machineSentenceCodes_atom (fun _ => δ) (fun _ => s)
    (MachineRatCodes.const δ).computable (sGenerable T s)

/-- The weight LUV `W n = ⌜ctsind_δ(P_{f(n)}(aₙ) > s)⌝` (FAF's `B`).
Source: FAF `RationalQuoteCode.luv`
Kind: D
Fidelity: n/a -/
def witnessW (n : ℕ) : LUV := (confidenceCode T f δ s).luv n

/-- The product LUV `XW n = ⌜1(aₙ) · ctsind_δ(P_{f(n)}(aₙ) > s)⌝` (FAF's `A`).
Source: FAF `indicatorProductLUV`
Kind: D
Fidelity: n/a -/
def witnessXW (n : ℕ) : LUV := indicatorProductLUV (confidenceCode T f δ s) atomFamily n

/-- The source `X n = literalIndicator ⌜aₙ⌝`.
Source: `Expert.lean` `literalIndicator`
Kind: D
Fidelity: n/a -/
abbrev witnessSource : ℕ → LUV := fun n => literalIndicator (atomFamily n)

omit [Entailment.Consistent T] in
/-- The confidence quote reflects the ramp of the deferred price, in every consistent world.
Source: FAF `RationalQuoteCode.reflected`, `paperConfidence_value_cast`
Kind: L
Fidelity: n/a -/
lemma witnessW_reflected (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (witnessW T f δ s n)
      (ctsInd ((fun _ => δ) n) (liaHistory (paperDP T) (f n) (atomFamily n))
        (((fun _ => s) n : ℚ) : ℝ)) := by
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T) (confidenceCode T f δ s)
    n v hv
  rwa [← paperConfidence_value_cast T f atomFamily (fun _ => δ) (fun _ => s) n] at h

omit [Entailment.Consistent T] in
/-- The product quote reflects `payout(aₙ) · ramp`, in every consistent world.
Source: FAF `indicatorProductLUV_valuesAt`, `paperConfidence_value_cast`
Kind: L
Fidelity: n/a -/
lemma witnessXW_reflected (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (witnessXW T f δ s n)
      (v.payout (atomFamily n) *
        ctsInd ((fun _ => δ) n) (liaHistory (paperDP T) (f n) (atomFamily n))
          (((fun _ => s) n : ℚ) : ℝ)) := by
  have h := indicatorProductLUV_valuesAt (paperQuotationPresentation T) (confidenceCode T f δ s)
    atomFamily n v hv
  rwa [← paperConfidence_value_cast T f atomFamily (fun _ => δ) (fun _ => s) n] at h

/-- **FAF's complete `thm:st` package over the paper's inductor**, at constant width `δ > 0`
and constant threshold `s ∈ [0,1]`, for the day-varying atom source — assembled by FAF's own
constructor from the market's quote codes (this is what `lic_self_trust_closed` builds
internally).
Source: FAF `selfTrustQuoteOfRepresentation` (`Construction/Quotation/Packages.lean`);
mandate T6 (N+ witness)
Kind: N+
Fidelity: n/a -/
def selfTrustQuoteWitness (hδ : 0 < δ) (hs : 0 ≤ s ∧ s ≤ 1) :
    SelfTrustQuote (liaHistory (paperDP T)) (paperDP T) f atomFamily (fun _ => δ) (fun _ => s)
      (witnessXW T f δ s) (witnessW T f δ s) :=
  selfTrustQuoteOfRepresentation f atomFamily (fun _ => δ) (fun _ => s)
    (witnessXW T f δ s) (witnessW T f δ s) (fun _ => hδ) (fun _ => hs)
    machineSentenceCodes_atom (MachineRatCodes.const (1 / δ))
    (sGenerable T s).choose (sGenerable T s).choose_spec
    (indicatorProductLUV_machineThresholdCodeSeq _ machineSentenceCodes_atom)
    (confidenceCode T f δ s).poly
    (witnessW_reflected T f δ s) (witnessXW_reflected T f δ s)
    (paperDP_hworld T)

/-- **The N+ witness for T3/T6c's hypothesis package:** the ramp `WeightQuote` for the
self-expert over the paper's inductor, projected from FAF's package by
`WeightQuote.of_selfTrustQuote`; its slack is literally `0` (`weightQuoteWitness_slack`).
Source: mandate T6 (N+ witness); `Expert.lean` `WeightQuote.of_selfTrustQuote`
Kind: N+
Fidelity: n/a -/
def weightQuoteWitness (hδ : 0 < δ) (hs : 0 ≤ s ∧ s ≤ 1) :
    WeightQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (witnessSource) (rampAbove δ s) (witnessW T f δ s) (witnessXW T f δ s) :=
  WeightQuote.of_selfTrustQuote (selfTrustQuoteWitness T f δ s hδ hs)

/-- The witness's product slack is identically `0` (the exact instance of `dd:mesh`).
Source: mandate T6 (N+ witness: "`slack ≡ 0`")
Kind: L
Fidelity: n/a -/
lemma weightQuoteWitness_slack (hδ : 0 < δ) (hs : 0 ≤ s ∧ s ≤ 1) :
    (weightQuoteWitness T f δ s hδ hs).slack = fun _ => 0 := rfl

/-- The source varies with the day: `literalIndicator ⌜a₀⌝ ≠ literalIndicator ⌜a₁⌝` (not a
constant sequence — AUDIT §3.8's degenerate-witness pattern is avoided).
Source: mandate T6 (N+: "a constant sentence is N−")
Kind: N+
Fidelity: n/a -/
lemma witnessSource_nonconstant : witnessSource 0 ≠ witnessSource 1 := by
  intro h
  have h' := congrArg (fun L : LUV => L.gt (1 / 2)) h
  simp only [witnessSource, literalIndicator] at h'
  norm_num at h'

/-- The source is pairwise distinct across days (`Formula.atom` is injective): strictly more
than `witnessSource_nonconstant` (audit round 1, N10).
Source: mandate T6 (N+: "the witness varies with `n`")
Kind: N+
Fidelity: n/a -/
lemma witnessSource_injective : Function.Injective witnessSource := by
  intro m n h
  have h' := congrArg (fun L : LUV => L.gt (1 / 2)) h
  simp only [witnessSource, literalIndicator] at h'
  norm_num at h'
  simpa using h'

/-- **The hypothesis package of `SoftTotalTrustAbove … s δ` is inhabited** over a real inductor
by an e.d. source and a ramp quote with zero slack.
Source: mandate T3 (non-vacuity of `ThresholdIneqAbove`)
Kind: N+
Fidelity: n/a -/
theorem softTotalTrustAbove_package_inhabited (hδ : 0 < δ) (hs : 0 ≤ s ∧ s ≤ 1) :
    ∃ X W XW : ℕ → LUV, LUV.MachineThresholdCodeSeq X ∧
      Nonempty (WeightQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
        X (rampAbove δ s) W XW) :=
  ⟨witnessSource, witnessW T f δ s, witnessXW T f δ s,
    literalIndicator_machineThresholdCodeSeq machineSentenceCodes_atom,
    ⟨weightQuoteWitness T f δ s hδ hs⟩⟩

/-- **FAF's self-trust conclusion in the product form of `ThresholdIneqAbove`:**
`E^H_n(XW_n) − s·E^H_n(W_n) ≳ₙ 0` over the paper's inductor — `lic_self_trust` (`thm:st`) on
the witness package, moved to the product form by `soft_above_iff_unnormalized`.
Source: FAF `lic_self_trust`; [[deference-notions]] §Total Trust ("the self-trust instance of
Total Trust is the paper's Self-Trust `st` 4.12.4")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem witness_selfTrust_productForm (hδ : 0 < δ) (hs : 0 ≤ s ∧ s ≤ 1) :
    (fun n => (witnessXW T f δ s n).expect (liaHistory (paperDP T)) n -
        (s : ℝ) * (witnessW T f δ s n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun _ => (0 : ℝ)) := by
  have h := lic_self_trust (liaHistory (paperDP T)) (paperDP T) f atomFamily (fun _ => δ)
    (fun _ => s) (witnessXW T f δ s) (witnessW T f δ s) (paperDP_hworld T)
    (selfTrustQuoteWitness T f δ s hδ hs)
  exact (soft_above_iff_unnormalized (liaHistory (paperDP T)) s _ _).mpr h

/-- **The closed `st` conclusion is Value against the constant on the hedged two-option menu**
(T6c on the witness): `E^H_n(twoOptionComb s XW W n) ≳ₙ s` over the paper's inductor.
Source: [[two-option-value-iff-total-trust]] §Soft/LI form; mandate T6 (N+ witness)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem witness_twoOption_value (hδ : 0 < δ) (hs : 0 ≤ s ∧ s ≤ 1) :
    (fun n => (twoOptionComb s (witnessXW T f δ s) (witnessW T f δ s) n).expect
        (liaHistory (paperDP T)) n) ≳ₙ (fun _ => (s : ℝ)) :=
  (twoOptionComb_value_iff_productForm (liaHistory (paperDP T)) s _ _).mpr
    (witness_selfTrust_productForm T f δ s hδ hs)

end

end Cleanroom.Found.DefLattice.Witness
