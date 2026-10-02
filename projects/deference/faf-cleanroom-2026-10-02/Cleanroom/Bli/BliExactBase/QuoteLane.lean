import Cleanroom.Bli.BliExactBase.Tables
import Cleanroom.Bli.BliLinkageB.InstanceB2
import Cleanroom.Bli.BliFound.Emitter

/-!
# `bli-exact-base` — K7c (a)–(c): the splice's own quote lane; the pinned set; stage freshness

**Construction-facing module** (mandate § Memory): it builds FAF quote codes
(`RationalQuoteCode.ofComputable`, `BooleanQuoteCode.ofComputable`) for the spliced market.

**Why `bli-found`'s `quoteAt`/`cellSentence` cannot be used.** They are built from
`marketValue 𝗜𝚺₁`, the paper market's own value family: their literals are reflected at the
price of FAF's **LIA** (`cellSentence_reflected`). On a segment day the splice's prices differ
from the LIA's — on day `4` the LIA's cell for some small tautology is the `0` cell while the
splice's is the `1` cell (`lia_splice_cells_disagree_day4`) — so a linkage claim written with
the LIA's literals would be about the wrong market. The splice therefore gets **its own** value
family `spliceValue H t` (the splice's exact table at `⟨m, c⟩`, through `sentenceOfCode` so
every value is a price), its own `RationalQuoteCode` (`spliceQuoteCode`), its own cell truth,
cell quote code and cell literals (`spliceCellSentence`, tag-`2` quotation atoms of the
splice's decider), reflected at the **splice's** rounded price in every completed-theory world
of `paperDP 𝗜𝚺₁` (`spliceCellSentence_reflected`), entering a stage when true
(`spliceCellSentence_enters`), negated in a stage when false (`_neg_enters`). The proofs are
`bli-found`'s with `spliceValue` in place of `marketValue`; a value-parametric `cellQuoteOf` in
`bli-found` would make the four of them one lemma each (**API request**, findings F11).

**The cell family** `spliceCF` (the B2 template `cellFamilyB2` at the splice): parametric in a
computable rounding with cells it is total into, and representatives. **The pinned set**
(`pinned_eventually_splice`): at `halfRound`/`twoCells`, the three coordinates of the index
`segmentIndex = [⌜freshCoord⌝, ⌜⊥⌝, ⌜⊤⌝]` are pinned from some day `N₀` on — their day-`(n+1)`
literals are small on day `n` (`spliceCellSentence_eventually_small`, through `bli-found`'s
emitter bridge: the literal of a fixed coordinate is a machine-metered family in the day).
`N₀` depends on the quote code's program code and is an `∃`, never a numeral — and it depends on
the horizon `H` through that code, so `exists_segment_day` (arithmetic in an abstract `N₀`) does
**not** witness a pinned day before any horizon: that is the OPEN `Segment.linked_segment_day_exists`
(findings F16 (b)). The same mechanism at an arbitrary coordinate makes the splice's lane *live*
on the small codes (`Live.spliceCF_live`).

**Stage freshness** (K7c (c)): `StageFresh` says no sentence of `(paperDP 𝗜𝚺₁).D n` mentions the
atom of a day-`(n+1)` cell literal of a pinned coordinate. **Proved** (continuation 1,
`stageFresh_splice`, from `quotationClaimCode_fresh_of_lt`): the stage at which a quotation
literal enters `paperDP` is bounded below by its *input*, whatever the decider's running time
(findings F18). No K7d statement takes it as a hypothesis; round 0 had it OPEN.
-/

namespace Cleanroom.Bli.BliExactBase

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliLinkageB

variable (H : ℕ) (t : ℕ → Sentence → ℚ)

/-! ## The splice's value family and quote code -/

/-- **The splice's value family** indexed by `z = ⟨m, c⟩`: the splice's exact quote on day `m` of
the sentence with code `c` (through `sentenceOfCode`, so every value is a genuine price). The
`value` of the splice's own `RationalQuoteCode`.
Source: mandate § Definitions (`spliceValue`); bli-found `StateSentence.marketValue` (template)
Kind: D
Fidelity: exact -/
noncomputable def spliceValue (z : ℕ) : ℚ :=
  spliceQuote H t z.unpair.1 (Encodable.encode (sentenceOfCode z.unpair.2))

/-- At a genuine code the value is the splice's quote of that sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceValue_pair (m : ℕ) (φ : Sentence) :
    spliceValue H t (Nat.pair m (Encodable.encode φ)) = spliceQuote H t m (Encodable.encode φ) := by
  simp [spliceValue, Nat.unpair_pair]

/-- The value family's cast at a genuine code is the spliced market's price.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceValue_eq_history (m : ℕ) (φ : Sentence) :
    (spliceValue H t (Nat.pair m (Encodable.encode φ)) : ℝ) = spliceHistory H t m φ := by
  rw [spliceValue_pair]; rfl

/-- `spliceValue H t` is a total computable rational function (the splice's program along the
paired input, decoded).
Source: mandate § 3 (a); `Splice.spliceQuote_computable`
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma spliceValue_computable : Computable (spliceValue H t) := by
  have hg : Computable fun z : ℕ =>
      Nat.pair z.unpair.1 (Encodable.encode (sentenceOfCode z.unpair.2)) :=
    Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.unpair)
      (Computable.encode.comp (sentenceOfCode_computable.comp (Computable.snd.comp Computable.unpair)))
  have henc : Computable fun z : ℕ => Encodable.encode (spliceValue H t z) := by
    refine ((spliceQuote_computable H t).comp hg).of_eq fun z => ?_
    simp [spliceValue, Nat.unpair_pair]
  have hdec : Computable fun z : ℕ =>
      (Encodable.decode (α := ℚ) (Encodable.encode (spliceValue H t z))).getD 0 :=
    Computable.option_getD (Computable.decode.comp henc) (Computable.const 0)
  exact hdec.of_eq fun z => by simp

/-- Every value is a price in `[0, 1]` (tables in `[0,1]` on the small sentences).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceValue_mem (ht : ∀ n < H, ∀ φ ∈ smallSet n, 0 ≤ t n φ ∧ t n φ ≤ 1) (z : ℕ) :
    0 ≤ spliceValue H t z ∧ spliceValue H t z ≤ 1 :=
  lookupOr_mem_Icc (f := paperQuote 𝗜𝚺₁) (segmentEntries_inUnit ht) (paperQuote_mem 𝗜𝚺₁ _ _)

/-- **The splice's own `RationalQuoteCode`**: FAF's quote code naming the splice's program.
Source: mandate § Definitions (`spliceQuoteCode`); FAF `RationalQuoteCode.ofComputable`
(`Construction/Quotation/MarketQuoteCodes.lean:136`); bli-found `marketQuoteCode` (template)
Kind: D
Fidelity: exact -/
noncomputable def spliceQuoteCode (ht : ∀ n < H, ∀ φ ∈ smallSet n, 0 ≤ t n φ ∧ t n φ ≤ 1) :
    RationalQuoteCode 𝗜𝚺₁ (spliceValue H t) :=
  RationalQuoteCode.ofComputable 𝗜𝚺₁ (spliceValue_computable H t) (spliceValue_mem H t ht)

/-! ## Cell truth, cell quote code, cell literals -/

/-- **The splice's cell truth** `⟨m, ⟨c, r⟩⟩`: on day `m` the splice's quote of the sentence with
code `c` rounds to `r`.
Source: mandate § Definitions (`spliceCellTruth`); bli-found `StateSentence.cellTruth` (template)
Kind: D
Fidelity: exact -/
def spliceCellTruth (round : ℕ → ℚ → ℕ) (z : ℕ) : Prop :=
  round z.unpair.1 (spliceValue H t (Nat.pair z.unpair.1 z.unpair.2.unpair.1)) = z.unpair.2.unpair.2

/-- The splice's cell truth is a computable predicate.
Source: bli-found `cellTruth_computable` (the same proof at `spliceValue`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem spliceCellTruth_computable (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) :
    ComputablePred (spliceCellTruth H t round) := by
  rw [ComputablePred.computable_iff]
  have hm : Computable fun z : ℕ => z.unpair.1 := Computable.fst.comp Computable.unpair
  have hc : Computable fun z : ℕ => z.unpair.2.unpair.1 :=
    Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))
  have hr : Computable fun z : ℕ => z.unpair.2.unpair.2 :=
    Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))
  have hpair : Computable fun z : ℕ => Nat.pair z.unpair.1 z.unpair.2.unpair.1 :=
    Primrec₂.natPair.to_comp.comp hm hc
  have hval : Computable fun z : ℕ =>
      spliceValue H t (Nat.pair z.unpair.1 z.unpair.2.unpair.1) :=
    (spliceValue_computable H t).comp hpair
  have hround' : Computable fun z : ℕ =>
      round z.unpair.1 (spliceValue H t (Nat.pair z.unpair.1 z.unpair.2.unpair.1)) :=
    hround.comp (hm.pair hval)
  refine ⟨fun z => decide
    (round z.unpair.1 (spliceValue H t (Nat.pair z.unpair.1 z.unpair.2.unpair.1)) =
      z.unpair.2.unpair.2), ?_, ?_⟩
  · exact ((Primrec.eq.decide.to_comp).comp hround' hr : _)
  · funext z
    simp [spliceCellTruth]

/-- **The splice's cell quote code.**
Source: mandate § Definitions; FAF `BooleanQuoteCode.ofComputable`
Kind: D
Fidelity: exact -/
noncomputable def spliceCellQuote (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) :
    BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H t round) :=
  BooleanQuoteCode.ofComputable (spliceCellTruth_computable H t round hround)

/-- **The splice's cell literal** `⌜round_m(spliceQuote_m(⌜c⌝)) = r⌝`: the tag-`2` quotation atom of the
splice's cell quote code at `⟨m, ⟨c, r⟩⟩`.
Source: mandate § Definitions (`spliceCellSentence`)
Kind: D
Fidelity: exact -/
noncomputable def spliceCellSentence (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (m c r : ℕ) : Sentence :=
  (spliceCellQuote H t round hround).sentence (Nat.pair m (Nat.pair c r))

/-- **Cell reflection at the splice.** Every completed-theory world of `paperDP 𝗜𝚺₁` holds the
splice's cell literal iff the **splice's** quote of `c`'s sentence rounds to `r` on day `m`.
Source: mandate § 3 (a) (`spliceCellSentence_reflected`); FAF `BooleanQuoteCode.reflected`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem spliceCellSentence_reflected (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (m c r : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) :
    v.Holds (spliceCellSentence H t round hround m c r) ↔
      round m (spliceValue H t (Nat.pair m c)) = r := by
  have := (spliceCellQuote H t round hround).reflected (paperQuotationPresentation 𝗜𝚺₁)
    (Nat.pair m (Nat.pair c r)) v hv
  simpa [spliceCellSentence, spliceCellTruth, Nat.unpair_pair] using this

/-- A true splice cell literal enters a stage of `paperDP 𝗜𝚺₁`.
Source: FAF `QuotationTheoryPresentation.quote_positive_enters`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem spliceCellSentence_enters (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) {m c r : ℕ}
    (h : round m (spliceValue H t (Nat.pair m c)) = r) :
    ∃ k, spliceCellSentence H t round hround m c r ∈ (paperDP 𝗜𝚺₁).D k :=
  (paperQuotationPresentation 𝗜𝚺₁).quote_positive_enters _ _
    ((spliceCellQuote H t round hround).pos_complete (Nat.pair m (Nat.pair c r))
      (by simpa [spliceCellTruth, Nat.unpair_pair] using h))

/-- A false splice cell literal is negated in a stage of `paperDP 𝗜𝚺₁`.
Source: FAF `QuotationTheoryPresentation.quote_negative_refutes`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem spliceCellSentence_neg_enters (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) {m c r : ℕ}
    (h : round m (spliceValue H t (Nat.pair m c)) ≠ r) :
    ∃ k, (∼ spliceCellSentence H t round hround m c r) ∈ (paperDP 𝗜𝚺₁).D k :=
  (paperQuotationPresentation 𝗜𝚺₁).quote_negative_refutes _ _
    ((spliceCellQuote H t round hround).neg_complete (Nat.pair m (Nat.pair c r))
      (by simpa [spliceCellTruth, Nat.unpair_pair] using h))

/-! ## The cell family -/

/-- **The splice's cell family** (the B2 template `cellFamilyB2` at the splice): literals
`spliceCellSentence m ⌜φ⌝ r`, exclusive and exhaustive in every completed-theory world by
reflection and the rounding's totality into `cells`.
Source: mandate § Definitions (`spliceCellFamily`); bli-linkage `InstanceB2.cellFamilyB2`
Kind: D
Fidelity: exact -/
noncomputable def spliceCF (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) : CellFamilyT (paperDP 𝗜𝚺₁) where
  literal m φ r := spliceCellSentence H t round hround m (Encodable.encode φ) r
  cells := cells
  rep := rep
  excl := by
    intro m φ r r' hne v hv ⟨h, h'⟩
    rw [spliceCellSentence_reflected H t round hround m _ r v hv] at h
    rw [spliceCellSentence_reflected H t round hround m _ r' v hv] at h'
    exact hne (h.symm.trans h')
  exh := by
    intro m φ v hv
    exact ⟨_, hcells m _, (spliceCellSentence_reflected H t round hround m _ _ v hv).2 rfl⟩

/-- The splice cell family's literal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceCF_literal (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) (m : ℕ) (φ : Sentence) (r : ℕ) :
    (spliceCF H t round hround cells hcells rep).literal m φ r =
      spliceCellSentence H t round hround m (Encodable.encode φ) r := rfl

/-- The splice cell family's cells and representatives.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceCF_cells (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) :
    (spliceCF H t round hround cells hcells rep).cells = cells ∧
      (spliceCF H t round hround cells hcells rep).rep = rep := ⟨rfl, rfl⟩

/-! ## The cell literals and the cell family under an arbitrary cell quote code (repair round 2)

`spliceCellQuote` is FAF's `BooleanQuoteCode.ofComputable`, which selects its decider and then its
`Nat.Partrec.Code` by `Classical.choose`; nothing bounds the chosen code's size in either
direction (audit r2 fidelity B1). Every statement about the splice's cell family that depends on
the code's *size* (the pinned set before the horizon) is therefore stated below over an arbitrary
cell quote code `q` of the splice's cell truth, with the `ofComputable` family as the instance
(`spliceCF_eq_q`). Every reflection, freshness and shape lemma is proved for arbitrary `q`. -/

/-- **The splice's cell literal under an arbitrary cell quote code `q`** of its cell truth: the
quotation atom of `q` at the folded input `⟨m, ⟨c, r⟩⟩`. `spliceCellSentence` is the instance at
FAF's `ofComputable` code (`spliceCellSentence_eq_q`).
Source: mandate § Definitions (`spliceCellSentence`); audit r2 fidelity B1 (the code as a parameter)
Kind: D
Fidelity: exact -/
noncomputable def spliceCellSentenceQ (round : ℕ → ℚ → ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H t round)) (m c r : ℕ) : Sentence :=
  q.sentence (Nat.pair m (Nat.pair c r))

/-- `spliceCellSentence` is `spliceCellSentenceQ` at the `ofComputable` code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceCellSentence_eq_q (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (m c r : ℕ) :
    spliceCellSentence H t round hround m c r =
      spliceCellSentenceQ H t round (spliceCellQuote H t round hround) m c r := rfl

/-- **Cell reflection at the splice, for every cell quote code**: every completed-theory world of
`paperDP 𝗜𝚺₁` holds the literal of `q` iff the **splice's** quote of `c`'s sentence rounds to `r`
on day `m`.
Source: mandate § 3 (a); FAF `BooleanQuoteCode.reflected`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem spliceCellSentenceQ_reflected (round : ℕ → ℚ → ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H t round)) (m c r : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) :
    v.Holds (spliceCellSentenceQ H t round q m c r) ↔
      round m (spliceValue H t (Nat.pair m c)) = r := by
  have := q.reflected (paperQuotationPresentation 𝗜𝚺₁) (Nat.pair m (Nat.pair c r)) v hv
  simpa [spliceCellSentenceQ, spliceCellTruth, Nat.unpair_pair] using this

/-- **The splice's cell family under an arbitrary cell quote code `q`**: literals
`spliceCellSentenceQ q m ⌜φ⌝ r`, exclusive and exhaustive in every completed-theory world by
reflection and the rounding's totality into `cells`. `spliceCF` is the instance at the
`ofComputable` code (`spliceCF_eq_q`).
Source: mandate § Definitions (`spliceCellFamily`); audit r2 fidelity B1
Kind: D
Fidelity: exact -/
noncomputable def spliceCFq (round : ℕ → ℚ → ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H t round)) (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) : CellFamilyT (paperDP 𝗜𝚺₁) where
  literal m φ r := spliceCellSentenceQ H t round q m (Encodable.encode φ) r
  cells := cells
  rep := rep
  excl := by
    intro m φ r r' hne v hv ⟨h, h'⟩
    rw [spliceCellSentenceQ_reflected H t round q m _ r v hv] at h
    rw [spliceCellSentenceQ_reflected H t round q m _ r' v hv] at h'
    exact hne (h.symm.trans h')
  exh := by
    intro m φ v hv
    exact ⟨_, hcells m _, (spliceCellSentenceQ_reflected H t round q m _ _ v hv).2 rfl⟩

/-- The generic splice cell family's literal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceCFq_literal (round : ℕ → ℚ → ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H t round)) (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) (m : ℕ) (φ : Sentence) (r : ℕ) :
    (spliceCFq H t round q cells hcells rep).literal m φ r =
      spliceCellSentenceQ H t round q m (Encodable.encode φ) r := rfl

/-- The generic splice cell family's cells and representatives.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceCFq_cells (round : ℕ → ℚ → ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H t round)) (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) :
    (spliceCFq H t round q cells hcells rep).cells = cells ∧
      (spliceCFq H t round q cells hcells rep).rep = rep := ⟨rfl, rfl⟩

/-- `spliceCF` is `spliceCFq` at the `ofComputable` code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceCF_eq_q (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) :
    spliceCF H t round hround cells hcells rep =
      spliceCFq H t round (spliceCellQuote H t round hround) cells hcells rep := rfl

/-! ## The pinned set -/

/-- **The index of the segment**: the uncertain coordinate and the two decided ones.
Source: mandate § Definitions (`segmentIndex`: "a sublist containing the uncertain coordinate
`φ₀` and `⌜⊥⌝`, `⌜⊤⌝`")
Kind: D
Fidelity: exact -/
def segmentIndex (_n : ℕ) : List ℕ :=
  [Encodable.encode freshCoord, Encodable.encode (⊥ : Sentence), Encodable.encode (⊤ : Sentence)]

/-- The segment index lists genuine codes, without repetition.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma segmentIndex_indexCodes (n : ℕ) : IndexCodes segmentIndex n := by
  intro c hc
  simp only [segmentIndex, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> simp

/-- A splice cell literal of a fixed sentence code at `halfRound` is a machine-metered family in
the day: the atom index is a `Nat.pair`-nest of constants and the day.
Source: bli-linkage `InstanceB2.cellSentence_machineSentenceCodes` (the same proof at the splice's code)
Kind: L
Fidelity: n/a -/
theorem spliceCellSentenceQ_machineSentenceCodes
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H t halfRound)) (c r : ℕ) :
    MachineSentenceCodes fun n => spliceCellSentenceQ H t halfRound q (n + 1) c r := by
  have hd : MachineDigits fun n => quotationClaimCode universalQuotePos universalQuoteNeg
      (Nat.pair q.code (Nat.pair (n + 1) (Nat.pair c r))) :=
    (MachineDigits.natPair (MachineDigits.const 2)
      (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuotePos))
        (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuoteNeg))
          (MachineDigits.natPair
            (MachineDigits.const q.code)
            (MachineDigits.natPair
              ((MachineDigits.ofUnaryRuler UnaryRuler.id).add (MachineDigits.const 1))
              (MachineDigits.const (Nat.pair c r))))))).of_eq (fun _ => rfl)
  exact MachineSentenceCodes.ofCanonical
    (MachineTokenStream.of_eq (hd.add (MachineDigits.const 5)) (fun _ => rfl))

/-- The instance of `spliceCellSentenceQ_machineSentenceCodes` at the `ofComputable` code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem spliceCellSentence_machineSentenceCodes (c r : ℕ) :
    MachineSentenceCodes fun n => spliceCellSentence H t halfRound halfRound_computable (n + 1) c r :=
  spliceCellSentenceQ_machineSentenceCodes H t (spliceCellQuote H t halfRound halfRound_computable) c r

/-- The day-`(n+1)` cell literal of a fixed coordinate under any cell quote code is eventually
day-`n` small. The day from which depends on the code.
Source: bli-found `Emitter.machineSentenceCodes_eventually_small`
Kind: L
Fidelity: n/a -/
theorem spliceCellSentenceQ_eventually_small
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H t halfRound)) (c r : ℕ) :
    ∃ N, ∀ n ≥ N, SmallOn n (spliceCellSentenceQ H t halfRound q (n + 1) c r) :=
  machineSentenceCodes_eventually_small (spliceCellSentenceQ_machineSentenceCodes H t q c r)

/-- The splice's day-`(n+1)` cell literal of a fixed coordinate is eventually day-`n` small.
Source: bli-found `Emitter.machineSentenceCodes_eventually_small`
Kind: L
Fidelity: n/a -/
theorem spliceCellSentence_eventually_small (c r : ℕ) :
    ∃ N, ∀ n ≥ N, SmallOn n (spliceCellSentence H t halfRound halfRound_computable (n + 1) c r) :=
  spliceCellSentenceQ_eventually_small H t (spliceCellQuote H t halfRound halfRound_computable) c r

/-- **The pinned set of the splice at `halfRound` is eventually the whole segment index** (K7c (b)),
**for every cell quote code `q`** of the splice's cell truth: from some day `N₀` on,
`⌜freshCoord⌝`, `⌜⊥⌝` and `⌜⊤⌝` are pinned — their day-`(n+1)` cell literals of both cells are
small on day `n`. `N₀` depends on `q` (through the token size of `q.code`): an `∃`, no numeral.
Source: mandate § 3 (b); bli-linkage `InstanceB2.pinned_eventually_B2` (template)
Kind: C
Fidelity: exact (`∃ N₀`, for every code)
Hyps: (a) -/
theorem pinned_eventually_spliceQ (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H t halfRound))
    (rep : ℕ → ℕ → ℚ) :
    ∃ N₀, ∀ n ≥ N₀,
      Encodable.encode freshCoord ∈
        pinned (spliceCFq H t halfRound q twoCells halfRound_mem_twoCells rep) segmentIndex n ∧
      Encodable.encode (⊥ : Sentence) ∈
        pinned (spliceCFq H t halfRound q twoCells halfRound_mem_twoCells rep) segmentIndex n ∧
      Encodable.encode (⊤ : Sentence) ∈
        pinned (spliceCFq H t halfRound q twoCells halfRound_mem_twoCells rep) segmentIndex n := by
  obtain ⟨N₀, h₀⟩ := spliceCellSentenceQ_eventually_small H t q (Encodable.encode freshCoord) 0
  obtain ⟨N₁, h₁⟩ := spliceCellSentenceQ_eventually_small H t q (Encodable.encode freshCoord) 1
  obtain ⟨N₂, h₂⟩ := spliceCellSentenceQ_eventually_small H t q (Encodable.encode (⊥ : Sentence)) 0
  obtain ⟨N₃, h₃⟩ := spliceCellSentenceQ_eventually_small H t q (Encodable.encode (⊥ : Sentence)) 1
  obtain ⟨N₄, h₄⟩ := spliceCellSentenceQ_eventually_small H t q (Encodable.encode (⊤ : Sentence)) 0
  obtain ⟨N₅, h₅⟩ := spliceCellSentenceQ_eventually_small H t q (Encodable.encode (⊤ : Sentence)) 1
  refine ⟨max (max (max N₀ N₁) (max N₂ N₃)) (max N₄ N₅), fun n hn => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hn
  obtain ⟨⟨⟨hn0, hn1⟩, hn2, hn3⟩, hn4, hn5⟩ := hn
  refine ⟨?_, ?_, ?_⟩ <;> rw [mem_pinned] <;> refine ⟨by simp [segmentIndex], fun r hr => ?_⟩ <;>
    simp only [spliceCFq_cells, twoCells, Finset.mem_insert, Finset.mem_singleton] at hr <;>
    rw [spliceCFq_literal, sentenceOfCode_encode]
  · rcases hr with rfl | rfl
    · exact h₀ n hn0
    · exact h₁ n hn1
  · rcases hr with rfl | rfl
    · exact h₂ n hn2
    · exact h₃ n hn3
  · rcases hr with rfl | rfl
    · exact h₄ n hn4
    · exact h₅ n hn5

/-- `pinned_eventually_spliceQ` at the `ofComputable` code: the pinned set of the splice's own
cell family is eventually the whole segment index, from an `N₀` that depends on the chosen code.
Source: mandate § 3 (b)
Kind: C
Fidelity: exact (`∃ N₀`)
Hyps: (a) -/
theorem pinned_eventually_splice (rep : ℕ → ℕ → ℚ) :
    ∃ N₀, ∀ n ≥ N₀,
      Encodable.encode freshCoord ∈
        pinned (spliceCF H t halfRound halfRound_computable twoCells halfRound_mem_twoCells rep)
          segmentIndex n ∧
      Encodable.encode (⊥ : Sentence) ∈
        pinned (spliceCF H t halfRound halfRound_computable twoCells halfRound_mem_twoCells rep)
          segmentIndex n ∧
      Encodable.encode (⊤ : Sentence) ∈
        pinned (spliceCF H t halfRound halfRound_computable twoCells halfRound_mem_twoCells rep)
          segmentIndex n :=
  pinned_eventually_spliceQ H t (spliceCellQuote H t halfRound halfRound_computable) rep

/-- **Arithmetic in an abstract `N₀`**: `[N₀, N₀ + 3)` contains a day `≥ 2`. Round 0 cited this as
the N+ of `pinned_eventually_splice`; it is not — `N₀` there depends on the horizon through the
splice's quote code, so this does **not** witness a pinned day of the splice before any horizon
(the OPEN `Segment.linked_segment_day_exists`, findings F16 (b)). Kept for the record of the
mandate's `H := N₀ + 2` correction (`N₀ + 2` has no day `≥ 2` at `N₀ = 0`).
Source: mandate § 3 (b) (the `H := N₀ + 2` shape); findings F15 (ii), F16 (b)
Kind: L
Fidelity: n/a (does not witness a pinned day)
Hyps: (a) -/
theorem exists_segment_day (N₀ : ℕ) : ∃ n, N₀ ≤ n ∧ n < N₀ + 3 ∧ 2 ≤ n :=
  ⟨N₀ + 2, by omega, by omega, by omega⟩

/-! ## The LIA's cells are not the splice's -/

/-- **The LIA's cell literals are the wrong literals for the splice**: on day `4` (any horizon
`H > 4`, the segment tables), some small tautology rounds to the `0` cell at the LIA and to the `1`
cell at the splice, so `bli-found`'s `cellSentence` and the splice's `spliceCellSentence` for that
coordinate have opposite truth values in every completed-theory world.
Source: mandate § 3 (a) (`not_segment_in_lia_cells`; findings F4)
Kind: N-
Fidelity: exact (one day, one coordinate; the mandate's "no segment table lies in the LIA's cells" needs the support bound on every day, not proved)
Hyps: (a) -/
theorem lia_splice_cells_disagree_day4 (hH : 4 < H) :
    ∃ c, sentenceOfCode c ∈ smallSet 4 ∧
      halfRound 4 (marketValue 𝗜𝚺₁ (Nat.pair 4 c)) = 0 ∧
      halfRound 4 (spliceValue H segmentPrice (Nat.pair 4 c)) = 1 ∧
      ∀ v : PCWorld, v.ConsistentWithTheory (paperDP 𝗜𝚺₁) →
        (v.Holds (cellSentence 𝗜𝚺₁ halfRound halfRound_computable 4 c 0) ∧
          ¬ v.Holds (spliceCellSentence H segmentPrice halfRound halfRound_computable 4 c 0)) := by
  obtain ⟨k, hk, hoff⟩ := exists_tautChain_offSupport_day4 (paperDP 𝗜𝚺₁)
  have hsmall := Cleanroom.Bli.BliLinkage.tautChain_mem_smallSet hk
  have hlia : marketValue 𝗜𝚺₁ (Nat.pair 4 (Encodable.encode (Cleanroom.Bli.BliLinkage.tautChain k))) = 0 := by
    rw [marketValue_pair]
    have h := paperQuote_eq_liaHistory 𝗜𝚺₁ 4 (Cleanroom.Bli.BliLinkage.tautChain k)
    rw [liaHistory_eq_quote_cast] at h
    change (((liaStates (paperDP 𝗜𝚺₁) 4).quote _ : ℚ) : ℝ) = _ at h
    rw [RationalBeliefState.quote_eq_zero_of_not_mem _ hoff] at h
    exact_mod_cast h.symm
  have hspl : spliceValue H segmentPrice (Nat.pair 4 (Encodable.encode (Cleanroom.Bli.BliLinkage.tautChain k))) = 1 := by
    rw [spliceValue_pair]
    have h1 : ((segmentPrice 4 (Cleanroom.Bli.BliLinkage.tautChain k) : ℚ) : ℝ) = 1 :=
      Cleanroom.Bli.BliLinkage.coherentOn_valid_one (segmentPrice_coherentOn 4 (smallAtoms 4))
        (atoms_subset_smallAtoms hsmall) (fun v => Cleanroom.Bli.BliLinkage.holds_tautChain v k)
    have h2 := spliceHistory_eq_tbl_of_lt (t := segmentPrice) hH hsmall
    rw [h1] at h2
    change ((spliceQuote H segmentPrice 4 (Encodable.encode _) : ℚ) : ℝ) = 1 at h2
    exact_mod_cast h2
  refine ⟨Encodable.encode (Cleanroom.Bli.BliLinkage.tautChain k), by simpa using hsmall, ?_, ?_, ?_⟩
  · rw [hlia]; norm_num [halfRound]
  · rw [hspl]; norm_num [halfRound]
  · intro v hv
    constructor
    · rw [cellSentence_reflected 𝗜𝚺₁ halfRound halfRound_computable 4 _ 0 v hv, hlia]
      norm_num [halfRound]
    · rw [spliceCellSentence_reflected H segmentPrice halfRound halfRound_computable 4 _ 0 v hv, hspl]
      norm_num [halfRound]

/-! ## Stage freshness -/

/-- **A quotation atom with input `w > n` is mentioned by no sentence of stage `n` of
`paperDP T`.** `theoremDP`'s stage `n` is a dovetail naming only the events `e ≤ n`
(`mem_dovetailStage`): a quote event's atom has input `e.unpair.2 ≤ e ≤ n < w`, and the halting
events' atoms carry the claim tags `0`/`1`; `paperTheoryDP`'s atoms carry tag `5`
(`paperTheoryDP_atom_tag`). The quotation tag is `2`. So the stage at which a quotation literal
enters is bounded below by its *input*, whatever the decider's running time — the mandate's
worry that a table-lookup decider "fires early" does not arise.
Source: mandate § 3 (c) (route (i)); FAF `DeductiveDovetail.mem_dovetailStage`,
`ComputationDP.eventAtom`, `TheoremDP.paperTheoryDP_atom_tag`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem quotationClaimCode_fresh_of_lt (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] {n w : ℕ}
    (hw : n < w) :
    ∀ φ ∈ (paperDP T).D n,
      quotationClaimCode universalQuotePos universalQuoteNeg w ∉ sentenceAtomCodes φ := by
  intro φ hφ ha
  rw [paperDP, DeductiveProcess.union_stage, Finset.mem_union] at hφ
  rcases hφ with hφ | hφ
  · simp only [theoremDP, dovetailProcess_D, mem_dovetailStage] at hφ
    obtain ⟨e, ⟨he, -⟩, rfl⟩ := hφ
    have hle : e.unpair.2 ≤ n := (Nat.unpair_right_le e).trans (by omega)
    rcases h : e.unpair.1 with _ | _ | _ | _ | _ | _ | m
    all_goals simp only [eventAtom, h, sentenceAtomCodes_neg] at ha
    · have := sentenceAtomCodes_computationClaimSentence _ _ ha
      simp [haltingClaim, ComputationClaimKind.godelCode, quotationClaimCode] at this
    · have := sentenceAtomCodes_computationClaimSentence _ _ ha
      simp [haltingClaim, ComputationClaimKind.godelCode, quotationClaimCode] at this
    · have := sentenceAtomCodes_computationClaimSentence _ _ ha
      simp [boundedHaltingClaim, ComputationClaimKind.godelCode, quotationClaimCode] at this
    · have := sentenceAtomCodes_computationClaimSentence _ _ ha
      simp [boundedHaltingClaim, ComputationClaimKind.godelCode, quotationClaimCode] at this
    · rw [quoteAtom, quotationClaimSentence, sentenceAtomCodes_atom, Finset.mem_singleton] at ha
      have : w = e.unpair.2 := by simpa [quotationClaimCode, Nat.pair_eq_pair] using ha
      omega
    · rw [quoteAtom, quotationClaimSentence, sentenceAtomCodes_atom, Finset.mem_singleton] at ha
      have : w = e.unpair.2 := by simpa [quotationClaimCode, Nat.pair_eq_pair] using ha
      omega
    · simp at ha
  · have := paperTheoryDP_atom_tag T hφ ha
    simp [quotationClaimCode, paperPrimeTag] at this

/-- **Stage freshness of the day-`(n+1)` literals on the segment**: for `N₀ ≤ n < H` and every
pinned coordinate `c` and cell `r`, no sentence of the stage `(paperDP 𝗜𝚺₁).D n` mentions an atom
of the day-`(n+1)` cell literal of `c` at `r`. The condition the stage-level mixture of K7d needs
to set the day-`(n+1)` literal atoms freely inside its worlds (`Mixing.free_atom_undecided`).
Source: mandate § 3 (c) (`StageFresh H N₀`)
Kind: D
Fidelity: exact -/
def StageFresh (H N₀ : ℕ) (C : CellFamilyT (paperDP 𝗜𝚺₁)) (index : ℕ → List ℕ) : Prop :=
  ∀ n, N₀ ≤ n → n < H → ∀ c ∈ pinned C index n, ∀ r ∈ C.cells (n + 1),
    ∀ φ ∈ (paperDP 𝗜𝚺₁).D n,
      ∀ a ∈ sentenceAtomCodes (C.literal (n + 1) (sentenceOfCode c) r), a ∉ sentenceAtomCodes φ

/-- **K7c (c) — the splice's day-`(n+1)` cell literals are fresh at stage `n`** (all-days form,
every coordinate and cell, every rounding, every table, **every cell quote code `q`**). The
literal is the quotation atom of the input `⟨q.code, ⟨n+1, ⟨c, r⟩⟩⟩ ≥ n+1 > n`, and no sentence of
stage `n` mentions a quotation atom of input `> n` (`quotationClaimCode_fresh_of_lt`). Route (i) of the mandate, by the dovetailer's
*input* bound rather than by the decider's clock: a table-lookup decider halts fast, but
`theoremDP`'s stage `n` does not look at events `> n` at all. (Continuation 1 closed this OPEN of
round 0.)
Source: mandate § 3 (c) (`stageFresh_splice`)
Kind: C
Fidelity: stronger: all days, every coordinate and cell (implies `StageFresh H N₀ C index` for every `H`, `N₀`, `index`, `stageFresh_of_allDays`)
Hyps: (a) -/
theorem stageFresh_spliceQ (round : ℕ → ℚ → ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H t round)) :
    ∀ n c r, ∀ φ ∈ (paperDP 𝗜𝚺₁).D n,
      ∀ a ∈ sentenceAtomCodes (spliceCellSentenceQ H t round q (n + 1) c r),
        a ∉ sentenceAtomCodes φ := by
  intro n c r φ hφ a ha
  rw [spliceCellSentenceQ, BooleanQuoteCode.sentence, quoteAtom, quotationClaimSentence,
    sentenceAtomCodes_atom, Finset.mem_singleton] at ha
  subst ha
  refine quotationClaimCode_fresh_of_lt 𝗜𝚺₁ ?_ φ hφ
  calc n < n + 1 := Nat.lt_succ_self n
    _ ≤ Nat.pair (n + 1) (Nat.pair c r) := Nat.left_le_pair _ _
    _ ≤ Nat.pair _ (Nat.pair (n + 1) (Nat.pair c r)) := Nat.right_le_pair _ _

/-- `stageFresh_spliceQ` at the `ofComputable` code.
Source: mandate § 3 (c) (`stageFresh_splice`)
Kind: C
Fidelity: stronger: all days, every coordinate and cell
Hyps: (a) -/
theorem stageFresh_splice (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) :
    ∀ n c r, ∀ φ ∈ (paperDP 𝗜𝚺₁).D n,
      ∀ a ∈ sentenceAtomCodes (spliceCellSentence H t round hround (n + 1) c r),
        a ∉ sentenceAtomCodes φ :=
  stageFresh_spliceQ H t round (spliceCellQuote H t round hround)

/-- The all-days freshness gives `StageFresh` for every segment, index and cell family built from
the splice's literals.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem stageFresh_of_allDays (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) (index : ℕ → List ℕ)
    (hall : ∀ n c r, ∀ φ ∈ (paperDP 𝗜𝚺₁).D n,
      ∀ a ∈ sentenceAtomCodes (spliceCellSentence H t round hround (n + 1) c r),
        a ∉ sentenceAtomCodes φ)
    (H' N₀ : ℕ) :
    StageFresh H' N₀ (spliceCF H t round hround cells hcells rep) index :=
  fun n _ _ _ _ r _ φ hφ a ha => hall n _ r φ hφ a ha

end Cleanroom.Bli.BliExactBase
