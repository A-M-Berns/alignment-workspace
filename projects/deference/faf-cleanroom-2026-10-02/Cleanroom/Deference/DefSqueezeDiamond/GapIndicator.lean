import Cleanroom.Deference.DefSqueezeDiamond.PaperExpert

/-!
# `def-squeeze-diamond` · GapIndicator: the gap quote of a literal-indicator source (target 4b's
one new construction, for the indicator class)

The arrows' `GapQuote DP E Z Y a G` asks for an e.c. LUV `G` valued within a vanishing slack of
the rescaled signed gap `(a (z − E*(Z_n)) + 1)/2` whenever `Z n` is valued at `z`. For a
general `[0,1]`-source this needs a mesh over the quoted expectation (the shape of FAF's
`meshProductLUV`, not built here). For a **literal-indicator source** `Z n = literalIndicator (φ n)`
the world value `z` is `payout(φ n) ∈ {0, 1}`, so the gap takes one of two *computable rational*
values — `u n := (a (1 − e_n) + 1)/2` when `φ n` holds, `w n := (1 − a e_n)/2` when it does not,
with `e_n := quote (f n) ⌜φ n⌝` the market's exact deferred-day price of `φ n` — and the gap LUV
is the **select** `selectLUV φ ⌜u⌝ ⌜w⌝` between FAF's quote codes of `u` and `w`:
`gt r := ∼(∼(φ ⋏ ⌜u > r⌝) ⋏ ∼(∼φ ⋏ ⌜w > r⌝))` (the disjunction `(φ ⋏ ⌜u > r⌝) ⋎ (∼φ ⋏ ⌜w > r⌝)`
written with `⋏` and `∼` only, so that FAF's `MachineSentenceCodes.and/.neg` certify it). Exact
(`slack ≡ 0`).

Consequences: `gapQuote_indicator` (the `GapQuote` for the self-expert on every e.c.
literal-indicator source, both signs, (a)); `pinnedGapPackages_indicator` (pins by
`selfPinGap`, ramp quotes by `paperRampQuote`); and the squeeze with **every** input a theorem
on this class (`squeeze_self_indicator`). The diagonal family's gap of `Witness.lean` is an
instance. Construction-facing; single market (self).
-/

namespace Cleanroom.Deference.DefSqueezeDiamond

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefSelfTrust
open Cleanroom.Deference.DefLatticeArrows Cleanroom.Deference.DefLatticeArrows.Witness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional

noncomputable section

/-! ## The select LUV -/

/-- **The select between two LUV families by a sentence family**: `A n` where `φ n` holds,
`B n` where it does not — threshold sentence
`∼(∼(φ n ⋏ ⌜A n > r⌝) ⋏ ∼(∼(φ n) ⋏ ⌜B n > r⌝))`.
Source: mandate target 4b ("`hardSelectionLuv`-style case split on a decided comparison")
Kind: D
Fidelity: exact -/
def selectLUV (φ : ℕ → Sentence) (A B : ℕ → LUV) (n : ℕ) : LUV where
  gt r := ∼(∼(φ n ⋏ (A n).gt r) ⋏ ∼(∼(φ n) ⋏ (B n).gt r))

open Classical in
/-- A world holds the select's threshold iff it holds the selected family's threshold.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem selectLUV_holds_iff (φ : ℕ → Sentence) (A B : ℕ → LUV) (n : ℕ) (r : ℚ) (v : PCWorld) :
    v.Holds ((selectLUV φ A B n).gt r) ↔
      (if v.Holds (φ n) then v.Holds ((A n).gt r) else v.Holds ((B n).gt r)) := by
  simp only [selectLUV, PCWorld.holds_neg, PCWorld.holds_and]
  by_cases hφ : v.Holds (φ n) <;> simp [hφ]

open Classical in
/-- **The select is valued at the selected value**.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem selectLUV_valuesAt (φ : ℕ → Sentence) (A B : ℕ → LUV) (n : ℕ) (v : PCWorld) {a b : ℝ}
    (ha : v.ValuesAt (A n) a) (hb : v.ValuesAt (B n) b) :
    v.ValuesAt (selectLUV φ A B n) (if v.Holds (φ n) then a else b) := by
  by_cases hφ : v.Holds (φ n)
  · rw [if_pos hφ]
    refine ⟨ha.1, ha.2.1, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
    · rw [selectLUV_holds_iff, if_pos hφ]; exact (ha.2.2 r).1 hr
    · rw [selectLUV_holds_iff, if_pos hφ]; exact (ha.2.2 r).2 hr
  · rw [if_neg hφ]
    refine ⟨hb.1, hb.2.1, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
    · rw [selectLUV_holds_iff, if_neg hφ]; exact (hb.2.2 r).1 hr
    · rw [selectLUV_holds_iff, if_neg hφ]; exact (hb.2.2 r).2 hr

/-- **The select is e.c.** when the sentence family and both LUV families are (FAF's
`MachineSentenceCodes.and`/`.neg` on the three streams, the sentence stream read at the
paired index's day).
Source: none: infrastructure (FAF `Framework/Machine/WriteOutMachine.lean`)
Kind: L
Fidelity: n/a -/
theorem selectLUV_codes {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ) {A B : ℕ → LUV}
    (hA : LUV.MachineThresholdCodeSeq A) (hB : LUV.MachineThresholdCodeSeq B) :
    LUV.MachineThresholdCodeSeq (selectLUV φ A B) := by
  have hφ' : MachineSentenceCodes (fun m : ℕ => φ m.unpair.1) := hφ.comp UnaryRuler.unpairFst
  unfold LUV.MachineThresholdCodeSeq at hA hB ⊢
  exact (((hφ'.and hA).neg.and (hφ'.neg.and hB).neg).neg).of_eq (fun m => rfl)

/-! ## The two branch values of the indicator gap -/

section Branches

variable {P : History} (market : MarketComputation P)

/-- The market's exact day-`g n` price of `φ n`, as a rational sequence.
Source: none: infrastructure (FAF `MarketComputation.quote`)
Kind: D
Fidelity: exact -/
def priceSeq (g : ℕ → ℕ) (φ : ℕ → Sentence) (n : ℕ) : ℚ :=
  market.quote (g n) (Encodable.encode (φ n))

/-- The price sequence is computable along a computable day map and an e.c. family.
Source: none: infrastructure (FAF `quote_comp_computable`)
Kind: L
Fidelity: n/a -/
theorem priceSeq_computable {g : ℕ → ℕ} (hg : Computable g) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) : Computable (priceSeq market g φ) :=
  market.quote_comp_computable hg hφ.primrec.to_comp

/-- The price sequence lies in `[0,1]`.
Source: none: infrastructure (FAF `quote_mem_Icc`)
Kind: L
Fidelity: n/a -/
theorem priceSeq_mem (g : ℕ → ℕ) (φ : ℕ → Sentence) (n : ℕ) :
    0 ≤ priceSeq market g φ n ∧ priceSeq market g φ n ≤ 1 :=
  market.quote_mem_Icc (g n) (φ n)

/-- As a real, the price sequence is the market's price.
Source: none: infrastructure (FAF `quote_exact`)
Kind: L
Fidelity: n/a -/
theorem priceSeq_cast (g : ℕ → ℕ) (φ : ℕ → Sentence) (n : ℕ) :
    ((priceSeq market g φ n : ℚ) : ℝ) = P (g n) (φ n) :=
  (market.quote_exact (g n) (φ n)).symm

/-- The gap's value where the indicator source is `1`: `(a (1 − e) + 1)/2`.
Source: mandate target 4b (the gap LUV); `def-lattice-arrows` `gapValue`
Kind: D
Fidelity: exact -/
def gapTop (a : ℚ) (e : ℕ → ℚ) (n : ℕ) : ℚ := (a * (1 - e n) + 1) / 2

/-- The gap's value where the indicator source is `0`: `(1 − a e)/2`.
Source: mandate target 4b
Kind: D
Fidelity: exact -/
def gapBot (a : ℚ) (e : ℕ → ℚ) (n : ℕ) : ℚ := (1 - a * e n) / 2

/-- `gapTop` is computable when `e` is (FAF's rational arithmetic is primitive recursive).
Source: none: infrastructure (FAF `ratSub_prim`, `ratMul_prim`, `ratAdd_prim`, `ratDiv_prim`)
Kind: L
Fidelity: n/a -/
theorem gapTop_computable (a : ℚ) {e : ℕ → ℚ} (he : Computable e) : Computable (gapTop a e) := by
  have h1 : Computable fun n => 1 - e n := (ratSub_prim.to_comp.comp (Computable.const 1) he : _)
  have h2 : Computable fun n => a * (1 - e n) := (ratMul_prim.to_comp.comp (Computable.const a) h1 : _)
  have h3 : Computable fun n => a * (1 - e n) + 1 := (ratAdd_prim.to_comp.comp h2 (Computable.const 1) : _)
  exact (ratDiv_prim.to_comp.comp h3 (Computable.const 2) : _)

/-- `gapBot` is computable when `e` is.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gapBot_computable (a : ℚ) {e : ℕ → ℚ} (he : Computable e) : Computable (gapBot a e) := by
  have h1 : Computable fun n => a * e n := (ratMul_prim.to_comp.comp (Computable.const a) he : _)
  have h2 : Computable fun n => 1 - a * e n := (ratSub_prim.to_comp.comp (Computable.const 1) h1 : _)
  exact (ratDiv_prim.to_comp.comp h2 (Computable.const 2) : _)

/-- For `a = ±1` and `e ∈ [0,1]`, `gapTop` lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gapTop_mem {a : ℚ} (ha : a = 1 ∨ a = -1) {e : ℕ → ℚ} (he : ∀ n, 0 ≤ e n ∧ e n ≤ 1)
    (n : ℕ) : 0 ≤ gapTop a e n ∧ gapTop a e n ≤ 1 := by
  have := he n
  unfold gapTop
  rcases ha with rfl | rfl <;> constructor <;> linarith

/-- For `a = ±1` and `e ∈ [0,1]`, `gapBot` lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gapBot_mem {a : ℚ} (ha : a = 1 ∨ a = -1) {e : ℕ → ℚ} (he : ∀ n, 0 ≤ e n ∧ e n ≤ 1)
    (n : ℕ) : 0 ≤ gapBot a e n ∧ gapBot a e n ≤ 1 := by
  have := he n
  unfold gapBot
  rcases ha with rfl | rfl <;> constructor <;> linarith

end Branches

/-! ## The gap quote of a literal-indicator source, for the self-expert -/

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- FAF's quote code of the gap's top branch along the deferral `f`.
Source: mandate target 4b; FAF `RationalQuoteCode.ofComputable`
Kind: D
Fidelity: exact -/
def gapTopCode (f : DeferralFunction) {a : ℚ} (ha : a = 1 ∨ a = -1) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) :
    RationalQuoteCode T (gapTop a (priceSeq (paperMarketComputation T) f.f φ)) :=
  RationalQuoteCode.ofComputable T (gapTop_computable a (priceSeq_computable _ f.computable hφ))
    (gapTop_mem ha (priceSeq_mem _ f.f φ))

/-- FAF's quote code of the gap's bottom branch along `f`.
Source: mandate target 4b
Kind: D
Fidelity: exact -/
def gapBotCode (f : DeferralFunction) {a : ℚ} (ha : a = 1 ∨ a = -1) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) :
    RationalQuoteCode T (gapBot a (priceSeq (paperMarketComputation T) f.f φ)) :=
  RationalQuoteCode.ofComputable T (gapBot_computable a (priceSeq_computable _ f.computable hφ))
    (gapBot_mem ha (priceSeq_mem _ f.f φ))

/-- **The indicator gap LUV**: the select between the two quoted branches by `φ`.
Source: mandate target 4b (the gap LUV `(a(Z − ⌜E*(Z)⌝) + 1)/2` for an indicator source)
Kind: D
Fidelity: exact (`slack ≡ 0`) -/
def indicatorGap (f : DeferralFunction) {a : ℚ} (ha : a = 1 ∨ a = -1) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) : ℕ → LUV :=
  selectLUV φ (gapTopCode T f ha hφ).luv (gapBotCode T f ha hφ).luv

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The self-expert's estimate of the literal-indicator source is the quoted deferred price.
Source: none: infrastructure (`literalIndicator_expect`, `priceSeq_cast`)
Kind: L
Fidelity: n/a -/
theorem estimate_literalIndicator_eq (f : DeferralFunction) (φ : ℕ → Sentence) (n : ℕ) :
    (Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate
        (fun n => literalIndicator (φ n)) n =
      ((priceSeq (paperMarketComputation T) f.f φ n : ℚ) : ℝ) := by
  rw [priceSeq_cast]
  simp [Expert.estimate, literalIndicator_expect]

open Classical in
/-- **The gap quote of a literal-indicator source, for the self-expert, both signs** (the gap
package of target 4b on the indicator class, (a), exact): `indicatorGap` is e.c.
(`selectLUV_codes`), valued at `gapValue a (payout φ_n) (E*(X_n))` in every completed-theory
world (the select picks the quoted top branch where `φ n` holds and the quoted bottom branch
where it does not), with FAF's closed quote as `Y`.
Source: mandate target 4b ("the gap LUV … build it; this is the one new construction");
[[total-trust-implies-mart]] §Proof (the gap bet `D_n`)
Kind: C
Fidelity: exact (`slack ≡ 0`; the indicator class only)
Hyps: (a) -/
def gapQuote_indicator (f : DeferralFunction) {a : ℚ} (ha : a = 1 ∨ a = -1) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) :
    GapQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (fun n => literalIndicator (φ n))
      ((paperDeferredExpectationQuoteCode T f (fun n => literalIndicator (φ n))
        (literalIndicator_machineThresholdCodeSeq hφ)).luv)
      a (indicatorGap T f ha hφ) where
  codes := selectLUV_codes hφ (gapTopCode T f ha hφ).poly (gapBotCode T f ha hφ).poly
  slack := fun _ => 0
  slack_tendsto := tendsto_const_nhds
  source_valued := fun n v hv => ⟨_, literalIndicator_valuesAt (φ n) (paperDP T) hv⟩
  reflects := closedQuote_reflects T f _ (literalIndicator_machineThresholdCodeSeq hφ)
  gap_reflected := fun n v hv z hz => by
    have hz' : z = v.payout (φ n) := hz.eq (literalIndicator_valuesAt (φ n) (paperDP T) hv)
    have hu := RationalQuoteCode.reflected (paperQuotationPresentation T) (gapTopCode T f ha hφ)
      n v hv
    have hw := RationalQuoteCode.reflected (paperQuotationPresentation T) (gapBotCode T f ha hφ)
      n v hv
    refine ⟨_, selectLUV_valuesAt φ _ _ n v hu hw, ?_⟩
    rw [estimate_literalIndicator_eq, hz']
    unfold PCWorld.payout gapValue gapTop gapBot
    by_cases hφv : v.Holds (φ n)
    · simp only [if_pos hφv]
      push_cast
      ring_nf
      simp
    · simp only [if_neg hφv]
      push_cast
      ring_nf
      simp

/-- **The pinned gap packages hold on the indicator class** (a): for every e.c. sentence family
`φ` and e.c. quote `Y` of the self-expert's estimate of `literalIndicator ∘ φ`, both gap quotes
exist (`gapQuote_indicator`, with `Y` replaced through `expect_reflects_congr`-free route: the
package's own `Y` is FAF's closed quote, and `GapQuote` does not depend on which `Y` reflects —
its `reflects` field is restated for the given `Y`), are pinned at `½` by `selfPinGap`, and
have ramp quotes by `paperRampQuote`.
Source: mandate target 4b (the pinned forms, design decision 4); target 2e
Kind: C
Fidelity: exact (the indicator class only)
Hyps: (a); `hf` -/
theorem pinnedGapPackages_indicator (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ) (Y : ℕ → LUV)
    (hY : LUV.MachineThresholdCodeSeq Y)
    (hR : Reflects (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (fun n => literalIndicator (φ n)) Y) :
    ∃ G G' : ℕ → LUV,
      ∃ _qP : GapQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
        (fun n => literalIndicator (φ n)) Y 1 G,
      ∃ _qM : GapQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
        (fun n => literalIndicator (φ n)) Y (-1) G',
        ExpertPin (Expert.self (liaHistory (paperDP T)) (paperDP T) f) G (1 / 2) ∧
        ExpertPin (Expert.self (liaHistory (paperDP T)) (paperDP T) f) G' (1 / 2) ∧
        RampQuotesAvailable (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) G ∧
        RampQuotesAvailable (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) G' := by
  let qP0 := gapQuote_indicator T f (Or.inl rfl) hφ
  let qM0 := gapQuote_indicator T f (Or.inr rfl) hφ
  let qP : GapQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (fun n => literalIndicator (φ n)) Y 1 (indicatorGap T f (Or.inl rfl) hφ) :=
    { codes := qP0.codes, slack := qP0.slack, slack_tendsto := qP0.slack_tendsto,
      source_valued := qP0.source_valued, reflects := hR, gap_reflected := qP0.gap_reflected }
  let qM : GapQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (fun n => literalIndicator (φ n)) Y (-1) (indicatorGap T f (Or.inr rfl) hφ) :=
    { codes := qM0.codes, slack := qM0.slack, slack_tendsto := qM0.slack_tendsto,
      source_valued := qM0.source_valued, reflects := hR, gap_reflected := qM0.gap_reflected }
  have hXcodes := literalIndicator_machineThresholdCodeSeq hφ
  refine ⟨_, _, qP, qM, selfPinGap T f hf (Or.inl rfl) hXcodes qP,
    selfPinGap T f hf (Or.inr rfl) hXcodes qM,
    paperExpert_rampQuotesAvailable T f (extendsBase_self T) hf.injective qP.codes qP.gap_valued,
    paperExpert_rampQuotesAvailable T f (extendsBase_self T) hf.injective qM.codes qM.gap_valued⟩

/-- **The squeeze runs with every input a theorem on the indicator class**: for an e.c.
sentence family `φ` and an e.c. quote `Y` of the self-expert's deferred price of `φ`,
`E_n(1(φ_n)) ≈ₙ E_n(Y_n)` through `tower_instance_of_totalTrust_gapBets` with the gap quotes
`gapQuote_indicator`, the pins `selfPinGap`, the ramp packages `paperRampQuote` and the TT
instances `selfTotalTrust` — root-007's Steps 0–3 over FAF, no hypothesis. (The conclusion is
also `towerValued_self` directly; this is the squeeze *run*.)
Source: mandate target 2e; [[centered-bet-squeeze]] §2; root-deference-007 Steps 0–3
Kind: C
Fidelity: exact (rescaled; the indicator class)
Hyps: (a) none; `hf` -/
theorem squeeze_self_indicator (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ) (Y : ℕ → LUV)
    (hY : LUV.MachineThresholdCodeSeq Y)
    (hR : Reflects (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (fun n => literalIndicator (φ n)) Y) :
    (fun n => (literalIndicator (φ n)).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (Y n).expect (liaHistory (paperDP T)) n) := by
  obtain ⟨G, G', qP, qM, -, -, -, -⟩ := pinnedGapPackages_indicator T f hf hφ Y hY hR
  exact squeeze_self_of_gapQuotes T f hf (literalIndicator_machineThresholdCodeSeq hφ) hY qP qM

end

end Cleanroom.Deference.DefSqueezeDiamond
