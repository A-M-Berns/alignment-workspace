import Cleanroom.Bli.BliFound.Constraints
import LogicalInduction.Construction.Paper.TheoremDP
import LogicalInduction.Construction.Quotation.Packages
import LogicalInduction.Construction.Quotation.MarketQuoteCodes

/-!
# `bli-found` · StateSentence: B2, the linked state sentence (T7)

**The claim.** The BLI's state sentence "`𝑸_m = Q̂`" can be encoded so that the LIA's *own*
deductive process decides it and proves its linkage to the market's quotes — the B2 encoding
of [[bli-program]] F5, as opposed to B1's fresh atom `stateAtom m q` (`State.lean`), which no
process decides and which is linked to nothing by construction.

**The construction, over FAF's single market `paperDP T` (`T` a `Δ₁`, `𝗥₀`-extending
arithmetic theory such as `𝗜𝚺₁`).**

* `paperQuote T m c` is the exact rational quote of the paper market's own program
  (`paperMarketComputation T`), with `liaHistory (paperDP T) m φ = paperQuote T m ⌜φ⌝`.
* `marketQuoteCode T : RationalQuoteCode T (marketValue T)` names that program as a quote
  code (`RationalQuoteCode.ofComputable`); `quoteLuv T m φ` is its LUV at `⟨m, ⌜φ⌝⌝`, valued
  at `paperQuote T m ⌜φ⌝` in every completed-theory world (`quoteLuv_valuesAt`); and
  `quoteAt T m φ lo hi := (quoteLuv T m φ).gt lo ⋏ ∼(quoteLuv T m φ).gt hi` is the interval
  quote "`lo < 𝑸_m(φ) ≤ hi`", forced in every completed-theory world when
  `lo < paperQuote < hi` (`holds_quoteAt_of_lt_of_lt`) and forcing `lo ≤ paperQuote ≤ hi`
  (`le_of_holds_quoteAt`).
* A *rounding* `round : ℕ → ℚ → ℕ` (day, exact quote ↦ grid index; computable data supplied
  by `bli-trajectory`) gives the **cell truth** `cellTruth T round ⟨m, ⟨c, r⟩⟩` — "on day `m` the
  market's quote of the sentence with code `c` rounds to `r`" — a `ComputablePred` because the
  market program is (`cellTruth_computable`), hence a `BooleanQuoteCode` (`cellQuote`) whose
  literals `cellSentence T round m c r` are tag-`2` quotation atoms that `paperDP T` puts into
  a stage when true, and negates in a stage when false (`cellSentence_enters`,
  `cellSentence_neg_enters`), and which every completed-theory world reads as the truth
  (`cellSentence_reflected`).
* A **written-out state** is a table `List (ℕ × ℕ)` of (sentence code, grid index) pairs with
  code `q = ⌜table⌝`; the **B2 state sentence** `stateSentence T round m q` is the conjunction
  of the cell literals of `q`'s table. It is *decided* by `paperDP T` in the semantic sense
  this package uses throughout (findings F-7): every conjunct literal (or its negation) enters
  a stage, so every completed-theory world holds the sentence iff the table is the rounded
  quote table (`stateSentence_reflected`, `stateSentence_decided`, `stateSentence_refuted`),
  and the actual rounded table's sentence holds in every such world
  (`stateSentence_actual_holds`); distinct candidates are exclusive on their common keys
  (`stateSentence_exclusive`).
* **Linkage.** `LNKcell σ quoteAt S cellOf DP` (the cell form of `Constraints.LNK`, over an
  abstract state-sentence family `σ`): in every completed-theory world, the state sentence of
  `(m, q)` forces the interval quote of `φ` for the cell `q` assigns to `φ`. It is proved for
  the B2 encoding (`LNKcell_stateSentence`) from the two reflection lemmas and a hypothesis on
  the rounding (`round m x = r → x ∈ (cellLo m r, cellHi m r)`, on `x ∈ [0, 1]`).

**Why the cell form and not `Constraints.LNK`.** `LNK` (first pass) quantifies over *every*
closed rational interval `[lo, hi]` containing `S.val m q φ`, and hard-codes B1's fresh atom
`stateAtom` as the antecedent. Paired with this file's `quoteAt T` it is **refutable for every
state system** over `paperDP T` (`Unlinked.lnk_quoteAt_refutable`, audit r1): at `lo = hi` the
interval quote `⌜Q > lo⌝ ⋏ ∼⌜Q > lo⌝` is a propositional contradiction, the fresh atom is free
(`Unlinked.stateAtom_free`), and whichever side of the exact quote `S.val` falls on, some
containing closed interval has a refuted quote. The mandate's own `LNK` (D5) took a single value
`quoteAt m φ (S.val m q φ)` — "the quote is in the cell of `Q̂[φ]`" — which is what `LNKcell`
renders. Recorded as findings F-13. `Constraints.LNK` is kept only so that the mandate's D5 name
resolves; it is `flagged` in the ledger and `bli-linkage` should state linkage as `LNKcell`.

**The scope `Sminus` and this file's quote atoms** (findings F-14). `Size.atomDay` reads the day
of a tag-`2` atom as its whole packed `input`; the quote atoms built here pack
`input = ⟨⟨m, ⌜φ⌝⟩, ⌜r⌝⟩` (`quoteAt`) and `input = ⟨m, ⟨c, r⟩⟩` (`cellSentence`), so
`quoteAt_mem_Sminus_imp`/`cellSentence_mem_Sminus_imp` show that `Sminus n k` admits one of
these atoms only when `k` exceeds the *packed input*, not the day: on this file's families
`Sminus m m` contains no interval quote of any day. Conservative (the tag-2 reading is `≥` the
day, so `Sminus` is a subset of the prose scope and E2x is weaker, never inconsistent), disclosed.
Since repair round 2 the same holds of FAF's product atoms (`Size.atomDay` reads their day
exactly, `PaperInstances.productAtom_notMem_Sminus`); before it, `atomDay` read `0` off tag `3`
and `Sminus` was incomparable with the prose scope (audit r2 fidelity B1).

**What is not here.** No claim that B2's state sentence is *large* (that is B1's story: the
fresh atom's write-out length); no `IsLogicalInductor` statement; and the linkage is stated as
a process fact about worlds, not as a market fact — `bli-linkage` owns the theorems that use
it. Imports are narrow (`TheoremDP`, `Quotation.Packages`, `Quotation.MarketQuoteCodes`; never
`Construction.LIACompiler`).

Sources: bli-paper-032, bli-paper-038; bli-soto-a-003; [[bli-program]] §2.3 (F5, B2); mandate D4
(B2) and T7.
-/

namespace Cleanroom.Bli.BliFound

open LogicalInduction LO.Propositional

section MarketQuotes

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁]

/-- **The paper market's exact rational quote** at day `m` and sentence code `c`: the `quote`
field of FAF's certified program `paperMarketComputation T` for `liaHistory (paperDP T)`.
Source: mandate D4 (B2); FAF `paperMarketComputation` (`Construction/Paper/TheoremDP.lean:449`)
Kind: D
Fidelity: exact -/
noncomputable def paperQuote (m c : ℕ) : ℚ := (paperMarketComputation T).quote m c

/-- The paper market's price *is* its exact quote: `liaHistory (paperDP T) m φ = paperQuote T m ⌜φ⌝`.
Source: FAF `MarketComputation.quote_exact`
Kind: L
Fidelity: exact -/
lemma paperQuote_eq_liaHistory (m : ℕ) (φ : Sentence) :
    liaHistory (paperDP T) m φ = (paperQuote T m (Encodable.encode φ) : ℝ) :=
  (paperMarketComputation T).quote_exact m φ

/-- Every quote of a sentence is a price in `[0, 1]`.
Source: FAF `MarketComputation.quote_mem_Icc`
Kind: L
Fidelity: exact -/
lemma paperQuote_mem (m : ℕ) (φ : Sentence) :
    0 ≤ paperQuote T m (Encodable.encode φ) ∧ paperQuote T m (Encodable.encode φ) ≤ 1 :=
  (paperMarketComputation T).quote_mem_Icc m φ

/-- The sentence with code `c` (`⊥` when `c` is not a code).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def sentenceOfCode (c : ℕ) : Sentence := (Encodable.decode c).getD ⊥

/-- `sentenceOfCode_encode`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma sentenceOfCode_encode (φ : Sentence) :
    sentenceOfCode (Encodable.encode φ) = φ := by
  simp [sentenceOfCode, Encodable.encodek]

/-- `sentenceOfCode` is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sentenceOfCode_computable : Computable sentenceOfCode :=
  Computable.option_getD Computable.decode (Computable.const ⊥)

/-- **The market value family** indexed by `z = ⟨m, c⟩`: the paper market's quote on day `m`
of the sentence with code `c` (through `sentenceOfCode`, so that every value is a genuine price
in `[0, 1]`). This is the `value` of the market's own `RationalQuoteCode`.
Source: mandate D4 (B2: "a `RationalQuoteCode` of the market's own price family")
Kind: D
Fidelity: exact -/
noncomputable def marketValue (z : ℕ) : ℚ :=
  paperQuote T z.unpair.1 (Encodable.encode (sentenceOfCode z.unpair.2))

/-- `marketValue T` is a total computable rational function (from the market program's
`Nat.Partrec.Code`, via FAF's `MarketComputation.quote_comp_computable`).
Source: FAF `MarketComputation.quote_comp_computable`
Kind: L
Fidelity: exact -/
lemma marketValue_computable : Computable (marketValue T) := by
  have hd : Computable fun z : ℕ => z.unpair.1 := Computable.fst.comp Computable.unpair
  have hg : Computable fun z : ℕ => Encodable.encode (sentenceOfCode z.unpair.2) :=
    Computable.encode.comp (sentenceOfCode_computable.comp (Computable.snd.comp Computable.unpair))
  exact (paperMarketComputation T).quote_comp_computable hd hg

/-- Every market value is a price in `[0, 1]`.
Source: FAF `MarketComputation.quote_mem_Icc`
Kind: L
Fidelity: exact -/
lemma marketValue_mem (z : ℕ) : 0 ≤ marketValue T z ∧ marketValue T z ≤ 1 :=
  (paperMarketComputation T).quote_mem_Icc _ _

/-- At a genuine sentence code the market value is the quote of that sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma marketValue_pair (m : ℕ) (φ : Sentence) :
    marketValue T (Nat.pair m (Encodable.encode φ)) = paperQuote T m (Encodable.encode φ) := by
  simp [marketValue, Nat.unpair_pair]

variable [𝗥₀ ⪯ T]

/-- **The market's own quote code**: FAF's `RationalQuoteCode` naming the paper market's price
program, whose threshold literals `⌜𝑸_m(φ) > r⌝` are tag-`2` quotation atoms that `paperDP T`
decides.
Source: mandate D4 (B2); FAF `RationalQuoteCode.ofComputable` (`Quotation/MarketQuoteCodes.lean:136`)
Kind: D
Fidelity: exact -/
noncomputable def marketQuoteCode : RationalQuoteCode T (marketValue T) :=
  RationalQuoteCode.ofComputable T (marketValue_computable T) (marketValue_mem T)

/-- The LUV "`𝑸_m(φ)`": the market quote code's threshold family at `⟨m, ⌜φ⌝⟩`.
Source: mandate D4 (B2)
Kind: D
Fidelity: exact -/
noncomputable def quoteLuv (m : ℕ) (φ : Sentence) : LUV :=
  (marketQuoteCode T).luv (Nat.pair m (Encodable.encode φ))

/-- **Quote reflection.** Every completed-theory world of `paperDP T` values `quoteLuv T m φ` at
the market's exact quote `paperQuote T m ⌜φ⌝` — i.e. at the market's own price
(`paperQuote_eq_liaHistory`).
Source: FAF `RationalQuoteCode.reflected` at `paperQuotationPresentation`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem quoteLuv_valuesAt (m : ℕ) (φ : Sentence) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (quoteLuv T m φ) (paperQuote T m (Encodable.encode φ) : ℝ) := by
  have := (marketQuoteCode T).reflected (paperQuotationPresentation T)
    (Nat.pair m (Encodable.encode φ)) v hv
  simpa [quoteLuv, marketValue_pair] using this

/-- **The interval quote** "`lo < 𝑸_m(φ) ≤ hi`": the threshold literal at `lo` and the negated
threshold literal at `hi`. This is the `quoteAt` family `Constraints.LNK`/`D_NNU` are parametric
in, instantiated by the market's own quote code.
Source: mandate D4 (B2: "an interval-quote sentence `quoteAt`, a threshold pair from a `RationalQuoteCode`")
Kind: D
Fidelity: exact -/
noncomputable def quoteAt (m : ℕ) (φ : Sentence) (lo hi : ℚ) : Sentence :=
  (quoteLuv T m φ).gt lo ⋏ ∼ (quoteLuv T m φ).gt hi

/-- A completed-theory world holds the interval quote whenever the exact quote lies strictly
inside the interval.
Source: mandate D4 (B2)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem holds_quoteAt_of_lt_of_lt {m : ℕ} {φ : Sentence} {lo hi : ℚ}
    (hlo : lo < paperQuote T m (Encodable.encode φ))
    (hhi : paperQuote T m (Encodable.encode φ) < hi)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (quoteAt T m φ lo hi) := by
  obtain ⟨-, -, hval⟩ := quoteLuv_valuesAt T m φ v hv
  rw [quoteAt, PCWorld.holds_and, PCWorld.holds_neg]
  exact ⟨(hval lo).1 (by exact_mod_cast hlo), (hval hi).2 (by exact_mod_cast hhi)⟩

/-- A completed-theory world that holds the interval quote has the exact quote in the closed
interval.
Source: mandate D4 (B2)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem le_of_holds_quoteAt {m : ℕ} {φ : Sentence} {lo hi : ℚ} (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) (h : v.Holds (quoteAt T m φ lo hi)) :
    lo ≤ paperQuote T m (Encodable.encode φ) ∧ paperQuote T m (Encodable.encode φ) ≤ hi := by
  obtain ⟨-, -, hval⟩ := quoteLuv_valuesAt T m φ v hv
  rw [quoteAt, PCWorld.holds_and, PCWorld.holds_neg] at h
  constructor
  · by_contra hcon
    exact (hval lo).2 (by exact_mod_cast not_le.mp hcon) h.1
  · by_contra hcon
    exact h.2 ((hval hi).1 (by exact_mod_cast not_le.mp hcon))

end MarketQuotes

section CellTruth

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁]

/-- **Cell truth.** `cellTruth T round ⟨m, ⟨c, r⟩⟩`: on day `m`, the market's quote of the
sentence with code `c` rounds (by `round m`) to the grid index `r`. The rounding is abstract
computable data (`bli-trajectory`'s).
Source: bli-paper-032/034 ("`D_n(𝑸_n(φ))`"); mandate D4 (B2: "the rounded day-`m` table")
Kind: D
Fidelity: exact -/
def cellTruth (round : ℕ → ℚ → ℕ) (z : ℕ) : Prop :=
  round z.unpair.1 (marketValue T (Nat.pair z.unpair.1 z.unpair.2.unpair.1)) = z.unpair.2.unpair.2

/-- **Cell truth is a computable predicate**, because the market program is computable
(`marketValue_computable`) and the rounding is.
Source: mandate D4 (B2: "a `ComputablePred` of the packed input")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem cellTruth_computable (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) :
    ComputablePred (cellTruth T round) := by
  rw [ComputablePred.computable_iff]
  have hm : Computable fun z : ℕ => z.unpair.1 := Computable.fst.comp Computable.unpair
  have hc : Computable fun z : ℕ => z.unpair.2.unpair.1 :=
    Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))
  have hr : Computable fun z : ℕ => z.unpair.2.unpair.2 :=
    Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))
  have hpair : Computable fun z : ℕ => Nat.pair z.unpair.1 z.unpair.2.unpair.1 :=
    Primrec₂.natPair.to_comp.comp hm hc
  have hval : Computable fun z : ℕ =>
      marketValue T (Nat.pair z.unpair.1 z.unpair.2.unpair.1) :=
    (marketValue_computable T).comp hpair
  have hround' : Computable fun z : ℕ =>
      round z.unpair.1 (marketValue T (Nat.pair z.unpair.1 z.unpair.2.unpair.1)) :=
    hround.comp (hm.pair hval)
  refine ⟨fun z => decide
    (round z.unpair.1 (marketValue T (Nat.pair z.unpair.1 z.unpair.2.unpair.1)) =
      z.unpair.2.unpair.2), ?_, ?_⟩
  · exact ((Primrec.eq.decide.to_comp).comp hround' hr : _)
  · funext z
    simp [cellTruth]

variable [𝗥₀ ⪯ T]

/-- **The cell quote code**: FAF's `BooleanQuoteCode` naming a decider of `cellTruth T round`.
Source: mandate D4 (B2); FAF `BooleanQuoteCode.ofComputable` (`Quotation/Packages.lean:313`)
Kind: D
Fidelity: exact -/
noncomputable def cellQuote (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) :
    BooleanQuoteCode T (cellTruth T round) :=
  BooleanQuoteCode.ofComputable (cellTruth_computable T round hround)

/-- **The cell literal** `⌜round_m(𝑸_m(⌜c⌝)) = r⌝`: the tag-`2` quotation atom of the cell quote
code at `⟨m, ⟨c, r⟩⟩`.
Source: mandate D4 (B2)
Kind: D
Fidelity: exact -/
noncomputable def cellSentence (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (m c r : ℕ) : Sentence :=
  (cellQuote T round hround).sentence (Nat.pair m (Nat.pair c r))

/-- **Cell reflection.** Every completed-theory world of `paperDP T` holds the cell literal iff
the market's quote of `c`'s sentence rounds to `r` on day `m`.
Source: FAF `BooleanQuoteCode.reflected` at `paperQuotationPresentation`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem cellSentence_reflected (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (m c r : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (cellSentence T round hround m c r) ↔
      round m (marketValue T (Nat.pair m c)) = r := by
  have := (cellQuote T round hround).reflected (paperQuotationPresentation T)
    (Nat.pair m (Nat.pair c r)) v hv
  simpa [cellSentence, cellTruth, Nat.unpair_pair] using this

/-- **A true cell literal enters a stage of `paperDP T`** (through `theoremDP`'s event tag `4`).
Source: FAF `QuotationTheoryPresentation.quote_positive_enters`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem cellSentence_enters (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) {m c r : ℕ}
    (h : round m (marketValue T (Nat.pair m c)) = r) :
    ∃ k, cellSentence T round hround m c r ∈ (paperDP T).D k :=
  (paperQuotationPresentation T).quote_positive_enters _ _
    ((cellQuote T round hround).pos_complete (Nat.pair m (Nat.pair c r))
      (by simpa [cellTruth, Nat.unpair_pair] using h))

/-- **A false cell literal is negated in a stage of `paperDP T`** (event tag `5`).
Source: FAF `QuotationTheoryPresentation.quote_negative_refutes`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem cellSentence_neg_enters (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) {m c r : ℕ}
    (h : round m (marketValue T (Nat.pair m c)) ≠ r) :
    ∃ k, (∼ cellSentence T round hround m c r) ∈ (paperDP T).D k :=
  (paperQuotationPresentation T).quote_negative_refutes _ _
    ((cellQuote T round hround).neg_complete (Nat.pair m (Nat.pair c r))
      (by simpa [cellTruth, Nat.unpair_pair] using h))

end CellTruth

section StateSentence

/-- The written-out table with code `q`: a list of (sentence code, grid index) pairs (`[]` when
`q` is not a code).
Source: mandate D4 (B2: "the written-out state with code `q`"); bli-paper-032
Kind: D
Fidelity: exact -/
def tableOfCode (q : ℕ) : List (ℕ × ℕ) := (Encodable.decode q).getD []

/-- `tableOfCode_encode`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma tableOfCode_encode (l : List (ℕ × ℕ)) : tableOfCode (Encodable.encode l) = l := by
  simp [tableOfCode]

/-- Finite conjunction of a list of sentences (`⊤` for the empty list).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def conjList : List Sentence → Sentence
  | [] => ⊤
  | φ :: l => φ ⋏ conjList l

/-- A world holds a finite conjunction iff it holds every conjunct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_conjList (v : PCWorld) :
    ∀ l : List Sentence, v.Holds (conjList l) ↔ ∀ φ ∈ l, v.Holds φ
  | [] => by simp [conjList, PCWorld.holds_top]
  | φ :: l => by
      rw [conjList, PCWorld.holds_and, holds_conjList v l]
      simp

/-- The grid index a table assigns to a sentence code (first match).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def entryOf (c : ℕ) : List (ℕ × ℕ) → Option ℕ
  | [] => none
  | e :: l => if e.1 = c then some e.2 else entryOf c l

/-- An assigned entry is a member of the table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_of_entryOf_eq_some :
    ∀ {l : List (ℕ × ℕ)} {c r : ℕ}, entryOf c l = some r → (c, r) ∈ l
  | [], _, _, h => by simp [entryOf] at h
  | e :: l, c, r, h => by
      by_cases hc : e.1 = c
      · rw [entryOf, if_pos hc] at h
        obtain rfl := Option.some.inj h
        subst hc
        simp
      · rw [entryOf, if_neg hc] at h
        exact List.mem_cons_of_mem _ (mem_of_entryOf_eq_some h)

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-- **The B2 state sentence** "`𝑸_m = Q̂`" for the table with code `q`: the conjunction of the
cell literals `⌜round_m(𝑸_m(⌜c⌝)) = r⌝` over the table's entries `(c, r)`. Unlike B1's fresh atom
`stateAtom m q`, this is built from tag-`2` quotation atoms that the LIA's own process
`paperDP T` decides (`cellSentence_enters`/`_neg_enters`), so it is *linked* to the market's
quotes (`LNKcell_stateSentence`).
Source: bli-paper-032, bli-paper-038; bli-soto-a-003; [[bli-program]] §2.3 (F5, B2); mandate D4 (B2)
Kind: D
Fidelity: variant: the state is a rounded table over an explicit index list, and "decided" is the semantic reading (each conjunct literal enters a stage; findings F-7) -/
noncomputable def stateSentence (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (m q : ℕ) : Sentence :=
  conjList ((tableOfCode q).map fun e => cellSentence T round hround m e.1 e.2)

/-- **State reflection (the D-DP theorem for B2).** Every completed-theory world of `paperDP T`
holds `stateSentence T round m q` iff every entry `(c, r)` of `q`'s table is the rounded quote
of `c`'s sentence on day `m`.
Source: mandate D4 (B2: `stateSentence_reflected`); bli-paper-038
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem stateSentence_reflected (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (m q : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (stateSentence T round hround m q) ↔
      ∀ e ∈ tableOfCode q, round m (marketValue T (Nat.pair m e.1)) = e.2 := by
  rw [stateSentence, holds_conjList]
  constructor
  · intro h e he
    exact (cellSentence_reflected T round hround m e.1 e.2 v hv).1
      (h _ (List.mem_map.2 ⟨e, he, rfl⟩))
  · intro h ψ hψ
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hψ
    exact (cellSentence_reflected T round hround m e.1 e.2 v hv).2 (h e he)

/-- **The actual rounded table** on day `m` over the index list `index m`: the pairs
`(c, round m (𝑸_m(⌜c⌝)))`.
Source: mandate D4 (B2: "the rounded day-`m` table")
Kind: D
Fidelity: exact -/
noncomputable def actualTable (round : ℕ → ℚ → ℕ) (index : ℕ → List ℕ) (m : ℕ) :
    List (ℕ × ℕ) :=
  (index m).map fun c => (c, round m (marketValue T (Nat.pair m c)))

/-- The code of the actual rounded table.
Source: mandate D4 (B2)
Kind: D
Fidelity: exact -/
noncomputable def actualCode (round : ℕ → ℚ → ℕ) (index : ℕ → List ℕ) (m : ℕ) : ℕ :=
  Encodable.encode (actualTable T round index m)

/-- **The actual state's sentence holds in every completed-theory world.**
Source: mandate D4 (B2: `stateSentence_decided`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem stateSentence_actual_holds (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (index : ℕ → List ℕ) (m : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (stateSentence T round hround m (actualCode T round index m)) := by
  rw [stateSentence_reflected T round hround m _ v hv]
  intro e he
  simp only [actualCode, tableOfCode_encode, actualTable, List.mem_map] at he
  obtain ⟨c, -, rfl⟩ := he
  rfl

/-- **Decided, positively**: a true state sentence holds in every completed-theory world (its
conjunct literals each enter a stage: `stateSentence_conjuncts_enter`).
Source: mandate D4 (B2: `stateSentence_decided`); findings F-7 (semantic "decided")
Kind: C
Fidelity: variant: semantic decision (see the module docstring)
Hyps: (a) -/
theorem stateSentence_decided (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (m q : ℕ)
    (h : ∀ e ∈ tableOfCode q, round m (marketValue T (Nat.pair m e.1)) = e.2) :
    ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) → v.Holds (stateSentence T round hround m q) :=
  fun v hv => (stateSentence_reflected T round hround m q v hv).2 h

/-- **Decided, negatively**: a false state sentence fails in every completed-theory world (the
negation of some conjunct literal enters a stage: `cellSentence_neg_enters`).
Source: mandate D4 (B2); findings F-7
Kind: C
Fidelity: variant: semantic decision
Hyps: (a) -/
theorem stateSentence_refuted (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (m q : ℕ)
    (h : ∃ e ∈ tableOfCode q, round m (marketValue T (Nat.pair m e.1)) ≠ e.2) :
    ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) →
      ¬ v.Holds (stateSentence T round hround m q) := by
  intro v hv hstate
  obtain ⟨e, he, hne⟩ := h
  exact hne ((stateSentence_reflected T round hround m q v hv).1 hstate e he)

/-- **Stage membership**: every conjunct literal of a true state sentence enters a stage of
`paperDP T` (this is the process-level content behind `stateSentence_decided`).
Source: mandate D4 (B2: `theoremDP_covers` + `eventFires`, event tag `4`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem stateSentence_conjuncts_enter (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (m q : ℕ)
    (h : ∀ e ∈ tableOfCode q, round m (marketValue T (Nat.pair m e.1)) = e.2) :
    ∀ e ∈ tableOfCode q, ∃ k, cellSentence T round hround m e.1 e.2 ∈ (paperDP T).D k :=
  fun e he => cellSentence_enters T round hround (h e he)

/-- **Exclusivity**: two state sentences that both hold in a completed-theory world agree on
every sentence code they both list.
Source: bli-paper-038 (exclusivity), mandate D4 (B2)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem stateSentence_exclusive (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (m q q' : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T))
    (hq : v.Holds (stateSentence T round hround m q))
    (hq' : v.Holds (stateSentence T round hround m q')) {c r r' : ℕ}
    (hr : (c, r) ∈ tableOfCode q) (hr' : (c, r') ∈ tableOfCode q') : r = r' := by
  have h1 := (stateSentence_reflected T round hround m q v hv).1 hq (c, r) hr
  have h2 := (stateSentence_reflected T round hround m q' v hv).1 hq' (c, r') hr'
  exact h1.symm.trans h2

end StateSentence

section Linkage

/-- **LNKcell — the state sentence entails its quotes, cell form** (flag `linked`). The cell form
of `Constraints.LNK`, over an abstract state-sentence family `σ m q` and a cell assignment
`cellOf m q φ = (lo, hi)` ("the cell state `q` assigns `φ` on day `m`"): in every
completed-theory world of `DP`, the state sentence of `(m, q)` forces the interval quote
`quoteAt m φ lo hi` of every day-`m` small sentence. `LNK` (closed intervals around `S.val`) is
refutable for every state system with the package's own `quoteAt T` (`Unlinked.lnk_quoteAt_refutable`,
findings F-13); this is the form the mandate's single-value `quoteAt m φ (S.val m q φ)` intended.
True of the B2 encoding (`LNKcell_stateSentence`); for B1's fresh atom it collapses to
unconditional forcing (`Unlinked.lnkcell_stateAtom_iff_unconditional`). **Not stated here:** any
tie between `cellOf m q φ` and `S.val m q φ` — a dependent conjoining faith with linkage adds
`S.val m q φ ∈ cellOf m q φ` itself (`b2StateSystem_val_mem_cellOfTable` for the B2 system).
That conjunction must use the **σ-parametric** faith predicates (`Constraints.E2xσ σ S P` etc.,
repair round 2) at the *same* `σ`: `Constraints.E2x` conditions on B1's `stateAtom m q`, which is
never the B2 `stateSentence` (`Grid.stateSentence_ne_stateAtom`), so `E2x ∧ LNKcell` for B2 would
tie the cell of one sentence to the faith in another (audit r2 adversarial N1).
Source: mandate D5 (`LNK`); [[bli-program]] §2.3/§2.6
Kind: D
Fidelity: variant: cells instead of every containing closed interval; abstract `σ`; silent on `S.val` -/
def LNKcell (σ : ℕ → ℕ → Sentence) (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence)
    (S : StateSystem) (cellOf : ℕ → ℕ → Sentence → ℚ × ℚ) (DP : DeductiveProcess) : Prop :=
  ∀ m, ∀ q ∈ S.states m, ∀ φ ∈ smallSet m, ∀ v : PCWorld, v.ConsistentWithTheory DP →
    v.Holds (σ m q) → v.Holds (quoteAt m φ (cellOf m q φ).1 (cellOf m q φ).2)

/-- The cell a table assigns a sentence: the bounds `(cellLo m r, cellHi m r)` of its grid index
`r`, or the vacuous `(-1, 2)` (every price lies strictly inside) when the sentence is not listed.
Source: mandate D4 (B2)
Kind: D
Fidelity: exact -/
def cellOfTable (cellLo cellHi : ℕ → ℕ → ℚ) (m q : ℕ) (φ : Sentence) : ℚ × ℚ :=
  match entryOf (Encodable.encode φ) (tableOfCode q) with
  | some r => (cellLo m r, cellHi m r)
  | none => (-1, 2)

/-- Off the table, `cellOfTable` is the default cell `(-1, 2)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellOfTable_unlisted (cellLo cellHi : ℕ → ℕ → ℚ) (m q : ℕ) (φ : Sentence)
    (h : entryOf (Encodable.encode φ) (tableOfCode q) = none) :
    cellOfTable cellLo cellHi m q φ = (-1, 2) := by
  simp [cellOfTable, h]

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-- The default cell's interval quote `quoteAt T m φ (-1) 2` holds in every completed-theory
world (every price lies in `[0, 1]`): `LNKcell_stateSentence` is a tautology for sentences the
table does not list.
Source: none: infrastructure; audit r1 (fidelity §3.5, adversarial N4)
Kind: L
Fidelity: n/a -/
theorem quoteAt_default_cell (m : ℕ) (φ : Sentence) : ∀ v : PCWorld,
    v.ConsistentWithTheory (paperDP T) → v.Holds (quoteAt T m φ (-1) 2) := fun v hv =>
  holds_quoteAt_of_lt_of_lt T (by linarith [(paperQuote_mem T m φ).1])
    (by linarith [(paperQuote_mem T m φ).2]) v hv

/-- **The B2 state system**: candidate table codes `states m` (containing the actual rounded
table's code), the value a table assigns a sentence is the representative `rep m r` of its grid
index (`0` if unlisted), and the realized state is the actual rounded table. A dependent should
keep `states m` to genuine table codes (`Encodable.encode` of a `List (ℕ × ℕ)`): a non-code `q`
has `tableOfCode q = []`, so its state sentence is `⊤` and holds in every world (audit r2
fidelity §3.6).
Source: mandate D4 (B2), D5 (`StateSystem`)
Kind: D
Fidelity: exact -/
noncomputable def b2StateSystem (round : ℕ → ℚ → ℕ) (index : ℕ → List ℕ)
    (states : ℕ → Finset ℕ) (hact : ∀ m, actualCode T round index m ∈ states m)
    (rep : ℕ → ℕ → ℚ) : StateSystem where
  states := states
  val m q φ := ((((entryOf (Encodable.encode φ) (tableOfCode q)).map (rep m)).getD 0 : ℚ) : ℝ)
  actual := actualCode T round index
  actual_mem := hact

omit [𝗥₀ ⪯ T] in
/-- **The B2 system's values lie in the cells the table assigns**: if every representative
`rep m r` lies strictly inside `(cellLo m r, cellHi m r)`, then `S.val m q φ` lies strictly
inside `cellOfTable cellLo cellHi m q φ` for every `φ` (listed: the representative in its cell;
unlisted: the default `0 ∈ (-1, 2)`). This is the `S.val`-to-`cellOf` tie that `LNKcell` does
not state and that a dependent conjoining `E2x` with `LNKcell` needs.
Source: mandate D4 (B2); audit r1 (fidelity §3.4)
Kind: L
Fidelity: exact -/
theorem b2StateSystem_val_mem_cellOfTable (round : ℕ → ℚ → ℕ) (index : ℕ → List ℕ)
    (states : ℕ → Finset ℕ) (hact : ∀ m, actualCode T round index m ∈ states m)
    (rep : ℕ → ℕ → ℚ) (cellLo cellHi : ℕ → ℕ → ℚ)
    (hrep : ∀ m r, cellLo m r < rep m r ∧ rep m r < cellHi m r) (m q : ℕ) (φ : Sentence) :
    ((cellOfTable cellLo cellHi m q φ).1 : ℝ) <
        (b2StateSystem T round index states hact rep).val m q φ ∧
      (b2StateSystem T round index states hact rep).val m q φ <
        (cellOfTable cellLo cellHi m q φ).2 := by
  simp only [b2StateSystem]
  unfold cellOfTable
  rcases hent : entryOf (Encodable.encode φ) (tableOfCode q) with _ | r
  · simp
  · obtain ⟨h1, h2⟩ := hrep m r
    simp only [Option.map_some, Option.getD_some]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- **Linkage for the B2 encoding (LNK proved as a process fact).** If the rounding sends every
price `x ∈ [0, 1]` with `round m x = r` strictly inside the cell `(cellLo m r, cellHi m r)`,
then in every completed-theory world of `paperDP T`, the B2 state sentence of `(m, q)` forces,
for every sentence `φ` the table lists, the interval quote of `φ` for the cell `q` assigns it —
the market's quote of `φ` lies in an **open neighbourhood of the rounding cell** the state says
it is in. The content is exactly the tightness of the dependent's cells: `hcell` cannot be met by
a partition (FAF's `PCWorld.ValuesAt` leaves `⌜X > r⌝` undetermined at `r = x`, so a forced
interval quote must be strictly open around every price of the cell, and open supersets of
adjacent rounding cells overlap — `Grid.hcell_forces_overlap` for `halfRound`; at the vacuous
cells `(-1, 2)` the theorem is a tautology, `Grid.lnkcell_default_cell_tautology`). For a
sentence the table does not list the forced quote is the default cell's, a tautology
(`quoteAt_default_cell`).
Source: mandate D4 (B2: "the linkage `stateSentence m q → quoteAt m φ (Q̂ φ)`"), D5 (`LNK`), T7
Kind: C
Fidelity: variant: cell form (`LNKcell`), see the module docstring; the forced cells are open neighbourhoods that necessarily overlap; vacuous off the index list
Hyps: (a); `hcell` is a condition on the abstract rounding (discharged by the witness) -/
theorem LNKcell_stateSentence (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (index : ℕ → List ℕ)
    (states : ℕ → Finset ℕ) (hact : ∀ m, actualCode T round index m ∈ states m)
    (rep : ℕ → ℕ → ℚ) (cellLo cellHi : ℕ → ℕ → ℚ)
    (hcell : ∀ m (x : ℚ) r, 0 ≤ x → x ≤ 1 → round m x = r → cellLo m r < x ∧ x < cellHi m r) :
    LNKcell (stateSentence T round hround) (quoteAt T)
      (b2StateSystem T round index states hact rep) (cellOfTable cellLo cellHi) (paperDP T) := by
  intro m q _ φ _ v hv hstate
  rw [stateSentence_reflected T round hround m q v hv] at hstate
  have hx := paperQuote_mem T m φ
  unfold cellOfTable
  rcases hent : entryOf (Encodable.encode φ) (tableOfCode q) with _ | r
  · dsimp only
    exact holds_quoteAt_of_lt_of_lt T (by linarith [hx.1]) (by linarith [hx.2]) v hv
  · dsimp only
    have hmem := mem_of_entryOf_eq_some hent
    have hround_eq := hstate _ hmem
    simp only [marketValue_pair] at hround_eq
    obtain ⟨hlo, hhi⟩ := hcell m _ r hx.1 hx.2 hround_eq
    exact holds_quoteAt_of_lt_of_lt T hlo hhi v hv

end Linkage

section Witness

/-! ## N+ at `𝗜𝚺₁`: a two-cell rounding, two candidate states a day -/

/-- Two-cell rounding at `1/2`: grid index `0` below `1/2`, `1` at or above.
Source: mandate T7 (witness)
Kind: D
Fidelity: n/a -/
def halfRound (_m : ℕ) (x : ℚ) : ℕ := if x < 1 / 2 then 0 else 1

/-- `halfRound` is computable (rational order is primitive recursive: FAF's `ratLE_prim`).
Source: mandate T7 (witness)
Kind: L
Fidelity: n/a -/
lemma halfRound_computable : Computable fun p : ℕ × ℚ => halfRound p.1 p.2 := by
  have hlt : PrimrecPred fun p : ℕ × ℚ => p.2 < (1 / 2 : ℚ) := by
    have h : PrimrecPred fun p : ℕ × ℚ => (1 / 2 : ℚ) ≤ p.2 :=
      ratLE_prim.comp (Primrec.const (1 / 2 : ℚ)) Primrec.snd
    exact h.not.of_eq fun p => by simp [not_le]
  exact (Primrec.ite hlt (Primrec.const 0) (Primrec.const 1)).to_comp

/-- Lower cell bounds for `halfRound`: `-1` for index `0`, `1/4` for index `1`.
Source: mandate T7 (witness)
Kind: D
Fidelity: n/a -/
def halfLo (_m r : ℕ) : ℚ := if r = 0 then -1 else 1 / 4

/-- Upper cell bounds for `halfRound`: `1/2` for index `0`, `2` for index `1`.
Source: mandate T7 (witness)
Kind: D
Fidelity: n/a -/
def halfHi (_m r : ℕ) : ℚ := if r = 0 then 1 / 2 else 2

/-- `halfRound` sends every price strictly inside its cell.
Source: mandate T7 (witness)
Kind: L
Fidelity: n/a -/
lemma halfRound_cell (m : ℕ) (x : ℚ) (r : ℕ) (h0 : 0 ≤ x) (h1 : x ≤ 1)
    (hr : halfRound m x = r) : halfLo m r < x ∧ x < halfHi m r := by
  unfold halfRound at hr
  split_ifs at hr with hx
  · subst hr
    simp only [halfLo, halfHi, if_true]
    constructor <;> linarith
  · subst hr
    simp only [halfLo, halfHi, one_ne_zero, if_false]
    constructor <;> linarith [not_lt.mp hx]

/-- The witness index list: `⊥` and `⊤` on every day.
Source: mandate T7 (witness)
Kind: D
Fidelity: n/a -/
def witnessIndex (_m : ℕ) : List ℕ :=
  [Encodable.encode (⊥ : Sentence), Encodable.encode (⊤ : Sentence)]

/-- `halfRound` only produces the grid indices `0` and `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma halfRound_le_one (m : ℕ) (x : ℚ) : halfRound m x ≤ 1 := by
  unfold halfRound; split_ifs <;> omega

/-- Flipping a `halfRound` index (`r ↦ 1 − r`) changes it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma halfRound_ne_flip (m : ℕ) (x : ℚ) : halfRound m x ≠ 1 - halfRound m x := by
  unfold halfRound; split_ifs <;> omega

/-- **The flipped candidate table**: every indexed sentence assigned the *other* `halfRound`
cell. It is a table the rounding can write out (every grid index is `0` or `1`,
`flippedCode_legitimate`), it differs from the actual table (`flippedCode_ne_actualCode`), and
which of the two holds is decided by the market's rounded quote of `⊥` (`flippedCode_refuted`,
`actualCode_holds`). Replaces the first pass's `wrongCode` (grid index `5`, a table no rounding
produces, whose refutation never consulted the market — audit r1, adversarial B1).
Source: mandate T7 (witness); audit r1 (adversarial B1, probe P3)
Kind: D
Fidelity: n/a -/
noncomputable def flippedCode (m : ℕ) : ℕ :=
  Encodable.encode ((witnessIndex m).map fun c =>
    (c, 1 - halfRound m (marketValue 𝗜𝚺₁ (Nat.pair m c))))

/-- Every entry of the flipped table is a grid index `halfRound` can produce.
Source: mandate T7 (witness); audit r1 (adversarial B1)
Kind: L
Fidelity: n/a -/
theorem flippedCode_legitimate (m : ℕ) : ∀ e ∈ tableOfCode (flippedCode m), e.2 ≤ 1 := by
  intro e he
  simp only [flippedCode, tableOfCode_encode, List.mem_map] at he
  obtain ⟨c, -, rfl⟩ := he
  simp only
  omega

/-- Two candidate states a day: the actual rounded table and the flipped one.
Source: mandate T7 (witness)
Kind: D
Fidelity: n/a -/
noncomputable def witnessStates (m : ℕ) : Finset ℕ :=
  {actualCode 𝗜𝚺₁ halfRound witnessIndex m, flippedCode m}

/-- The actual table is a candidate.
Source: mandate T7 (witness)
Kind: L
Fidelity: n/a -/
lemma actualCode_mem_witnessStates (m : ℕ) :
    actualCode 𝗜𝚺₁ halfRound witnessIndex m ∈ witnessStates m :=
  Finset.mem_insert_self _ _

/-- The flipped table is a candidate.
Source: mandate T7 (witness)
Kind: L
Fidelity: n/a -/
lemma flippedCode_mem_witnessStates (m : ℕ) : flippedCode m ∈ witnessStates m :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The flipped table differs from the actual one (they disagree on `⌜⊥⌝`'s grid index).
Source: mandate T7 (witness)
Kind: L
Fidelity: n/a -/
lemma flippedCode_ne_actualCode (m : ℕ) :
    flippedCode m ≠ actualCode 𝗜𝚺₁ halfRound witnessIndex m := by
  intro h
  have := Encodable.encode_injective h
  simp only [actualTable, witnessIndex, List.map_cons, List.map_nil,
    List.cons.injEq, Prod.mk.injEq, true_and, and_true] at this
  exact halfRound_ne_flip _ _ this.1.symm

/-- Two candidates a day.
Source: mandate T7 (witness)
Kind: L
Fidelity: n/a -/
lemma witnessStates_card (m : ℕ) : (witnessStates m).card = 2 :=
  Finset.card_pair (flippedCode_ne_actualCode m).symm

/-- Cell representatives: `1/4` and `3/4`.
Source: mandate T7 (witness)
Kind: D
Fidelity: n/a -/
def witnessRep (_m r : ℕ) : ℚ := if r = 0 then 1 / 4 else 3 / 4

/-- Each representative lies strictly inside its `halfRound` cell (`1/4 ∈ (-1, 1/2)`,
`3/4 ∈ (1/4, 2)`).
Source: mandate T7 (witness); audit r1 (fidelity §3.4)
Kind: L
Fidelity: n/a -/
lemma witnessRep_mem_cell (m r : ℕ) : halfLo m r < witnessRep m r ∧ witnessRep m r < halfHi m r := by
  unfold halfLo halfHi witnessRep
  split_ifs <;> norm_num

/-- The witness B2 state system over `paperDP 𝗜𝚺₁`.
Source: mandate T7 (witness)
Kind: D
Fidelity: n/a -/
noncomputable def witnessSystem : StateSystem :=
  b2StateSystem 𝗜𝚺₁ halfRound witnessIndex witnessStates actualCode_mem_witnessStates witnessRep

/-- The witness system's values lie strictly inside the cells `LNKcell_witness` forces (the
`S.val`-to-`cellOf` tie `LNKcell` itself does not state).
Source: mandate T7 (witness); audit r1 (fidelity §3.4)
Kind: L
Fidelity: n/a -/
theorem witnessSystem_val_mem_cell (m q : ℕ) (φ : Sentence) :
    ((cellOfTable halfLo halfHi m q φ).1 : ℝ) < witnessSystem.val m q φ ∧
      witnessSystem.val m q φ < (cellOfTable halfLo halfHi m q φ).2 :=
  b2StateSystem_val_mem_cellOfTable 𝗜𝚺₁ halfRound witnessIndex witnessStates
    actualCode_mem_witnessStates witnessRep halfLo halfHi witnessRep_mem_cell m q φ

/-- **N+ (T7): linkage at a real theory, a real rounding and two candidate states a day.**
`LNKcell` holds for the B2 state sentence over `paperDP 𝗜𝚺₁` with the two-cell rounding.
Source: mandate T7 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem LNKcell_witness :
    LNKcell (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) (quoteAt 𝗜𝚺₁) witnessSystem
      (cellOfTable halfLo halfHi) (paperDP 𝗜𝚺₁) :=
  LNKcell_stateSentence 𝗜𝚺₁ halfRound halfRound_computable witnessIndex witnessStates
    actualCode_mem_witnessStates witnessRep halfLo halfHi halfRound_cell

/-- **N+ (T7): the encoding separates the candidates.** The flipped candidate's state sentence
fails in every completed-theory world of `paperDP 𝗜𝚺₁`: on `⌜⊥⌝` it claims the cell the market's
rounded quote is not in (`halfRound_ne_flip`) …
Source: mandate T7 (witness); audit r1 (adversarial B1)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem flippedCode_refuted (m : ℕ) : ∀ v : PCWorld, v.ConsistentWithTheory (paperDP 𝗜𝚺₁) →
    ¬ v.Holds (stateSentence 𝗜𝚺₁ halfRound halfRound_computable m (flippedCode m)) :=
  stateSentence_refuted 𝗜𝚺₁ halfRound halfRound_computable m (flippedCode m)
    ⟨(Encodable.encode (⊥ : Sentence),
        1 - halfRound m (marketValue 𝗜𝚺₁ (Nat.pair m (Encodable.encode (⊥ : Sentence))))),
      by
        simp only [flippedCode, tableOfCode_encode, witnessIndex, List.map_cons, List.map_nil]
        exact List.mem_cons_self .., halfRound_ne_flip _ _⟩

/-- … and the actual candidate's holds in every such world.
Source: mandate T7 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem actualCode_holds (m : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) :
    v.Holds (stateSentence 𝗜𝚺₁ halfRound halfRound_computable m
      (actualCode 𝗜𝚺₁ halfRound witnessIndex m)) :=
  stateSentence_actual_holds 𝗜𝚺₁ halfRound halfRound_computable witnessIndex m v hv

/-- **N+ (T7): of the two candidate tables, exactly the actual one holds.** In every
completed-theory world of `paperDP 𝗜𝚺₁`, a candidate `q ∈ witnessStates m` has its state
sentence hold iff `q` is the actual rounded table: both candidates are tables `halfRound` can
write out, and the market's rounded quote of `⊥` decides between them.
Source: mandate T7 (witness); bli-paper-038; audit r1 (adversarial B1)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem witnessStates_decided (m : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) :
    ∀ q ∈ witnessStates m,
      (v.Holds (stateSentence 𝗜𝚺₁ halfRound halfRound_computable m q) ↔
        q = actualCode 𝗜𝚺₁ halfRound witnessIndex m) := by
  intro q hq
  simp only [witnessStates, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact ⟨fun _ => rfl, fun _ => actualCode_holds m v hv⟩
  · exact ⟨fun h => absurd h (flippedCode_refuted m v hv),
      fun h => absurd h (flippedCode_ne_actualCode m)⟩

end Witness

section Scope

/-! ## `Sminus` on this file's quote atoms (findings F-14) -/

/-- The day `atomDay` reads off a quotation atom is the whole packed `input` of `w = ⟨code, input⟩`.
Source: none: infrastructure; audit r1 (adversarial N3)
Kind: L
Fidelity: n/a -/
lemma atomDay_quotationClaimCode (w : ℕ) :
    atomDay (quotationClaimCode universalQuotePos universalQuoteNeg w) = w.unpair.2 := by
  simp [atomDay, atomDayBase, quotationClaimCode, cleanroomBaseTag]

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-- If a day-`m` interval quote of `φ` lies in `Sminus n k`, then `k` exceeds the packed
`⟨⟨m, ⌜φ⌝⟩, ⌜lo⌝⟩` — not merely `m`. So `Sminus m m` contains no interval quote of any day
(`Nat.pair` is monotone in both arguments, and `⌜φ⌝ ≥ 0` gives `⟨⟨m, ⌜φ⌝⟩, ⌜lo⌝⟩ ≥ m`).
Source: findings F-14; audit r1 (adversarial N3, probe P5)
Kind: L
Fidelity: n/a -/
theorem quoteAt_mem_Sminus_imp {m : ℕ} {φ : Sentence} {lo hi : ℚ} {n k : ℕ}
    (h : quoteAt T m φ lo hi ∈ Sminus n k) :
    Nat.pair (Nat.pair m (Encodable.encode φ)) (Encodable.encode lo) < k := by
  rw [mem_Sminus] at h
  have := h.2 (quotationClaimCode universalQuotePos universalQuoteNeg
    (Nat.pair (marketQuoteCode T).code
      (Nat.pair (Nat.pair m (Encodable.encode φ)) (Encodable.encode lo))))
    (by simp [quoteAt, quoteLuv, RationalQuoteCode.luv, arithmeticThresholdLUV, quoteAtom,
      quotationClaimSentence])
  rwa [atomDay_quotationClaimCode, Nat.unpair_pair] at this

/-- No interval quote of day `m` lies in `Sminus n m`: the packed input is `≥ m`.
Source: findings F-14; audit r1 (adversarial N3)
Kind: L
Fidelity: n/a -/
theorem quoteAt_notMem_Sminus (m : ℕ) (φ : Sentence) (lo hi : ℚ) (n : ℕ) :
    quoteAt T m φ lo hi ∉ Sminus n m := by
  intro h
  have h0 := quoteAt_mem_Sminus_imp T h
  have h1 : m ≤ Nat.pair m (Encodable.encode φ) := Nat.left_le_pair _ _
  have h2 : Nat.pair m (Encodable.encode φ) ≤
      Nat.pair (Nat.pair m (Encodable.encode φ)) (Encodable.encode lo) := Nat.left_le_pair _ _
  omega

/-- If a day-`m` cell literal about code `c` lies in `Sminus n k`, then `k` exceeds the packed
`⟨m, ⟨c, r⟩⟩` — not merely `m`.
Source: findings F-14; audit r1 (adversarial N3, probe P5)
Kind: L
Fidelity: n/a -/
theorem cellSentence_mem_Sminus_imp (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2)
    {m c r n k : ℕ} (h : cellSentence T round hround m c r ∈ Sminus n k) :
    Nat.pair m (Nat.pair c r) < k := by
  rw [mem_Sminus] at h
  have := h.2 (quotationClaimCode universalQuotePos universalQuoteNeg
    (Nat.pair (cellQuote T round hround).code (Nat.pair m (Nat.pair c r))))
    (by simp [cellSentence, BooleanQuoteCode.sentence, quoteAtom, quotationClaimSentence])
  rwa [atomDay_quotationClaimCode, Nat.unpair_pair] at this

end Scope

end Cleanroom.Bli.BliFound
