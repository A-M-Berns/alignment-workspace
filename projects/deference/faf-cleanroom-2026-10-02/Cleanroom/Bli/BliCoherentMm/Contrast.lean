import Cleanroom.Bli.BliCoherentMm.Maker
import Cleanroom.Bli.BliCoherentMm.AttemptA.Contrast
import Cleanroom.Bli.BliCoherentMm.AttemptB.Contrast

/-!
# `bli-coherent-mm` · Contrast (reconciled): T4(a)–(c) — FAF's maker is forced incoherent on
the pair strategy; the coherent makers are not; the responsive strategy pins the price at `1/2`

**Of record: attempt B's general-sentence forms**, with attempt A's atom instances kept. Both
attempts proved the same contrast; attempt B stated it for an arbitrary sentence `φ`
(`pairStrategy n φ`: one share of `φ`, one of `∼φ`, constant coefficients) where attempt A
fixed `φ := atom a` — the two strategies coincide at an atom (`pairStrategy_atom_eq`, by
`rfl`), so attempt A's results are instances. The record also carries:

* **T4(a)** `marketMakerAccepts_pair_sum_ge` (every FAF-accepted table at `ε` has
  `quote φ + quote (∼φ) ≥ 2 − ε`), `marketMaker_incoherent_on_pair` (FAF's `MarketMaker` at
  `ε < 1` sums above `1`), `marketMaker_not_worldMarginal_on_pair`, and in the record's
  coherence notion `marketMakerAccepts_not_coherentQuoteOn`; attempt A's
  `marketMakerStates_pair_incoherent` (every day of FAF's recursive market on the pair trader).
  **Finding of record** (N− for FAF's maker): bli-slides-044's gap and Soto's PDF 05 fn. 1 as
  theorems.
* **T4(b)** every world measure makes `T_pair` worth exactly `0` in every world
  (`pair_value_eq_zero`), hence is coherently accepted at every `ε ≥ 0`
  (`pair_coherentAccepts`); the record maker prices `φ + ∼φ = 1` at any stage
  (`coherentMarketMaker_pair_sum_one`), its table is **rejected** by FAF's all-Boolean test at
  every `ε < 1` (`coherent_pair_not_marketMakerAccepts`: the two predicates are different
  objects), and the interior maker quotes an undecided atom strictly inside `(0,1)` with
  `|W_∅| = 2^B ≥ 2` worlds (`interior_pair_quote_mem_Ioo`, N+ for T2/T3). The grid maker too
  (`gridCoherentMarketMaker_pair_sum_one`).
* **T4(c)** against the price-responsive strategy (buy `1 − 2·price φ` shares of `φ`), every
  coherently accepted price of an undecided `φ` is within `ε` of `1/2`
  (`responsive_near_half`): T1's fixed point is not a boundary artifact.

Sources: [[bli-coherent-mm-mandate]] T4(a)–(c); Soto PDF 05 fn. 1 (bli-soto-a-044);
bli-slides-044.
-/

namespace Cleanroom.Bli.BliCoherentMm

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-! ## The pair strategy -/

/-- **`T_pair` (of record)**: buy one share of `φ` and one of `∼φ` at constant coefficients
(`EF.const 1`, rank `0`).
Source: [[bli-coherent-mm-mandate]] T4(a); Soto PDF 05 fn. 1
Kind: D
Fidelity: exact -/
abbrev pairStrategy (n : ℕ) (φ : Sentence) : Strategy n := AttemptB.pairStrategy n φ

/-- **The two attempts' pair strategies agree** at an atom (attempt A fixed `φ := atom a`).
Source: [[bli-coherent-mm-mandate]] §Deliverables (cross-check)
Kind: L
Fidelity: exact -/
theorem pairStrategy_atom_eq (a n : ℕ) :
    pairStrategy n (Formula.atom a) = AttemptA.pairStrategy a n :=
  rfl

/-- `φ` and `∼φ` are the sentences `T_pair` mentions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_mentionedSet_pair (n : ℕ) (φ : Sentence) :
    φ ∈ mentionedSet (pairStrategy n φ) ∧ ∼φ ∈ mentionedSet (pairStrategy n φ) :=
  ⟨mem_mentionedSet_iff.mpr ((AttemptB.mentionedBy_pairStrategy_iff n φ φ).mpr (Or.inl rfl)),
    mem_mentionedSet_iff.mpr ((AttemptB.mentionedBy_pairStrategy_iff n φ _).mpr (Or.inr rfl))⟩

/-! ## T4(a): FAF's acceptance forces incoherence on the pair -/

/-- **T4(a), the engine.** Every table FAF's `MarketMakerAccepts` accepts at `ε` against
`T_pair` has `quote φ + quote (∼φ) ≥ 2 − ε`: the acceptance clause at the Boolean support
table in which `φ` and `∼φ` both pay `1` — a table no `PCWorld` realises.
Source: [[bli-coherent-mm-mandate]] T4(a); Soto PDF 05 fn. 1; bli-slides-044
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem marketMakerAccepts_pair_sum_ge {n : ℕ} {φ : Sentence} (past : List RationalBeliefState)
    (ε : ℚ) (Bs : RationalBeliefState) (h : MarketMakerAccepts (pairStrategy n φ) past ε Bs) :
    2 - ε ≤ Bs.quote φ + Bs.quote (∼φ) :=
  AttemptB.marketMakerAccepts_pair_sum_ge past ε Bs h

/-- **T4(a) (finding of record; N− for FAF's maker). FAF's `MarketMaker` is provably incoherent
on `T_pair` at every `ε < 1`**: it prices `φ` and `∼φ` to a sum above `1`. bli-slides-044's gap
("FAF's construction is not exactly coherent at finite times") as a theorem.
Source: [[bli-coherent-mm-mandate]] T4(a); Soto PDF 05 fn. 1 (bli-soto-a-044); bli-slides-044
Kind: N-
Fidelity: exact (for FAF's own maker and acceptance predicate)
Hyps: (a) `hε1 : ε < 1` (true of FAF's `marketMakerError n`) -/
theorem marketMaker_incoherent_on_pair (n : ℕ) (φ : Sentence) (past : List RationalBeliefState)
    {ε : ℚ} (hε : 0 < ε) (hε1 : ε < 1) :
    1 < (MarketMaker (pairStrategy n φ) past ε hε).quote φ +
      (MarketMaker (pairStrategy n φ) past ε hε).quote (∼φ) :=
  AttemptB.marketMaker_incoherent_on_pair n φ past hε hε1

/-- **T4(a), marginal form.** FAF's `MarketMaker` on `T_pair` at `ε < 1` is not a world marginal
on `{φ, ∼φ}` relative to any stage `D` and atom bound `B`.
Source: [[bli-coherent-mm-mandate]] T4(a)
Kind: N-
Fidelity: exact
Hyps: (a) -/
theorem marketMaker_not_worldMarginal_on_pair (n : ℕ) (φ : Sentence)
    (past : List RationalBeliefState) {ε : ℚ} (hε : 0 < ε) (hε1 : ε < 1) (D : Finset Sentence)
    (B : ℕ) :
    ¬ IsWorldMarginal (MarketMaker (pairStrategy n φ) past ε hε).quote {φ, ∼φ} D B :=
  AttemptB.marketMaker_not_worldMarginal_on_pair n φ past hε hε1 D B

/-- **T4(a) at FAF's day-`n` error** `marketMakerError n = 2^{-(n+1)} < 1`.
Source: [[bli-coherent-mm-mandate]] T4(a)
Kind: N-
Fidelity: exact
Hyps: (a) -/
theorem marketMaker_incoherent_on_pair_error (n : ℕ) (φ : Sentence)
    (past : List RationalBeliefState) :
    1 < (MarketMaker (pairStrategy n φ) past (marketMakerError n) (marketMakerError_pos n)).quote φ
      + (MarketMaker (pairStrategy n φ) past (marketMakerError n)
          (marketMakerError_pos n)).quote (∼φ) :=
  AttemptB.marketMaker_incoherent_on_pair_error n φ past

/-- **T4(a) in the record's coherence notion.** No table FAF's `MarketMakerAccepts` accepts
against `T_pair` at `ε < 1` is coherent on `{φ, ∼φ}` (`CoherentQuoteOn`, any stage, any atom
bound): a world marginal has `π φ + π (∼φ) = 1 < 2 − ε`.
Source: [[bli-coherent-mm-mandate]] T4(a); bli-slides-044
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem marketMakerAccepts_not_coherentQuoteOn {n : ℕ} {φ : Sentence}
    (past : List RationalBeliefState) {ε : ℚ} (hε1 : ε < 1) (Bs : RationalBeliefState)
    (h : MarketMakerAccepts (pairStrategy n φ) past ε Bs) (D : Finset Sentence) (B : ℕ) :
    ¬ CoherentQuoteOn Bs.quote {φ, ∼φ} D B := by
  rintro ⟨w, hw, hV⟩
  have hsum := marketMakerAccepts_pair_sum_ge past ε Bs h
  rw [hV _ (Finset.mem_insert_self _ _),
    hV _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)),
    AttemptA.marginal_neg_add hw] at hsum
  linarith

/-- The trader playing `T_pair` on `atom a` every day (attempt A's).
Source: [[bli-coherent-mm-mandate]] T4(a)
Kind: D
Fidelity: exact -/
abbrev pairTrader (a : ℕ) : Trader := AttemptA.pairTrader a

/-- **T4(a) at FAF's recursive market**: every day's state of `marketMakerStates (pairTrader a)`
is incoherent on `{atom a, ∼atom a}` — FAF's construction is not exactly coherent at any finite
time on this trader (attempt A).
Source: [[bli-coherent-mm-mandate]] T4(a); bli-slides-044
Kind: N-
Fidelity: n/a (a finding of record about FAF's construction)
Hyps: (a) -/
theorem marketMakerStates_pair_incoherent (a n : ℕ) (D : Finset Sentence) (B : ℕ) :
    ¬ CoherentQuoteOn (marketMakerStates (pairTrader a) n).quote
      {Formula.atom a, ∼(Formula.atom a)} D B :=
  AttemptA.marketMakerStates_pair_incoherent a n D B

/-! ## T4(b): the coherent makers on the pair (N+ for T2/T3) -/

/-- **T4(b). Every world measure makes `T_pair` worth exactly `0` in every finite world**
(`payout φ + payout (∼φ) = 1 = π φ + π (∼φ)`), on the record's candidate table.
Source: [[bli-coherent-mm-mandate]] T4(b)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem pair_value_eq_zero {n : ℕ} {φ : Sentence} {D : Finset Sentence} {B : ℕ}
    {S : Finset Sentence} {w : FiniteWorld B → ℚ} (hw : IsWorldMeasure w D) (hφ : φ ∈ S)
    (hnφ : ∼φ ∈ S) (past : List RationalBeliefState) (u : FiniteWorld B) :
    (pairStrategy n φ).marketValueRat (candidateTable past n S w) u.payoutRat = 0 := by
  rw [candidateTable_eq_attemptB past n S hw]
  exact AttemptB.pair_coherent_value_eq_zero hw.toB hφ hnφ past u

/-- **T4(b). Every world measure is coherently accepted on `T_pair` at every `ε ≥ 0`** (on any
`S ⊇ mentionedSet T_pair`).
Source: [[bli-coherent-mm-mandate]] T4(b)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem pair_coherentAccepts {n : ℕ} {φ : Sentence} {D : Finset Sentence} {B : ℕ}
    {S : Finset Sentence} {w : FiniteWorld B → ℚ} (hw : IsWorldMeasure w D)
    (hS : mentionedSet (pairStrategy n φ) ⊆ S) (past : List RationalBeliefState) {ε : ℚ}
    (hε : 0 ≤ ε) : CoherentAccepts (pairStrategy n φ) past D B S ε w :=
  (coherentAccepts_iff_attemptB _ past D B S ε hw hS).mpr
    (AttemptB.pair_coherentAccepts hw.toB hS past hε)

/-- **T4(b). The record maker on `T_pair` prices `φ` and `∼φ` to sum exactly `1`**, at any stage
with a consistent world — the contrast with `marketMaker_incoherent_on_pair` on the same
strategy.
Source: [[bli-coherent-mm-mandate]] T4(b)
Kind: N+
Fidelity: exact
Hyps: (a) `hW`, `hε` -/
theorem coherentMarketMaker_pair_sum_one {n : ℕ} (φ : Sentence) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D)
    {ε : ℚ} (hε : 0 < ε) :
    (coherentMarketMaker (pairStrategy n φ) past D B (mentionedSet (pairStrategy n φ))
        subset_rfl hW hε).quote φ +
      (coherentMarketMaker (pairStrategy n φ) past D B (mentionedSet (pairStrategy n φ))
        subset_rfl hW hε).quote (∼φ) = 1 := by
  rw [coherentMarketMaker_quote_eq_pi _ _ _ _ _ _ _ _ (mem_mentionedSet_pair n φ).1,
    coherentMarketMaker_quote_eq_pi _ _ _ _ _ _ _ _ (mem_mentionedSet_pair n φ).2]
  exact marginal_neg_add (coherentMarketMaker_isWorldMeasure _ _ _ _ _ _ _ _) _

/-- **T4(b). The grid maker on `T_pair` prices `φ` and `∼φ` to sum exactly `1`** (attempt B's
maker; the same contrast).
Source: [[bli-coherent-mm-mandate]] T4(b)
Kind: N+
Fidelity: exact
Hyps: (a) `hB`, `hW`, `hε` -/
theorem gridCoherentMarketMaker_pair_sum_one (n : ℕ) (φ : Sentence)
    (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ)
    (hB : ∀ ψ ∈ mentionedSet (pairStrategy n φ) ∪ D, atomBound ψ ≤ B)
    (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) (ε : ℚ) (hε : 0 < ε) :
    (gridCoherentMarketMaker (pairStrategy n φ) past D B hB hW (mentionedSet (pairStrategy n φ))
        (Finset.Subset.refl _) ε hε).quote φ +
      (gridCoherentMarketMaker (pairStrategy n φ) past D B hB hW (mentionedSet (pairStrategy n φ))
        (Finset.Subset.refl _) ε hε).quote (∼φ) = 1 :=
  AttemptB.coherentMarketMaker_pair_sum n φ past D B hB hW ε hε

section Atom

variable (a n : ℕ) (past : List RationalBeliefState) (B : ℕ) {ε : ℚ} (hε : 0 < ε)

/-- The empty stage: every finite world is consistent, so `hW` is free.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hW_empty : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith ∅ :=
  AttemptA.hW_empty B

/-- `WD ∅ B` has `2^B` elements: the witness is not a one-world simplex.
Source: [[bli-coherent-mm-mandate]] T3 traps ("the N+ needs `|W_D| ≥ 2`")
Kind: N+
Fidelity: n/a -/
theorem card_WD_empty : (WD ∅ B).card = 2 ^ B :=
  AttemptA.card_WD_empty B

/-- **T4(b). The record maker on `T_pair` at `atom a`, the empty stage, is accepted in every
world** at every `ε > 0` (attempt A's instance).
Source: [[bli-coherent-mm-mandate]] T4(b)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem coherent_pair_accepts :
    ∀ u : FiniteWorld B,
      (pairStrategy n (Formula.atom a)).marketValueRat
        (candidateRationalHistory past n (coherentMarketMaker (pairStrategy n (Formula.atom a))
          past ∅ B (mentionedSet (pairStrategy n (Formula.atom a))) subset_rfl (hW_empty B) hε))
        u.payoutRat ≤ ε :=
  AttemptA.coherent_pair_accepts a n past B hε

/-- **The two predicates are different objects**: the record maker's table on `T_pair` is
*rejected* by FAF's all-Boolean `MarketMakerAccepts` at every `ε < 1` (it is accepted by D3 at
every `ε > 0`).
Source: [[bli-coherent-mm-mandate]] T4(a) (fake-success trap), D3
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem coherent_pair_not_marketMakerAccepts (hε1 : ε < 1) :
    ¬ MarketMakerAccepts (pairStrategy n (Formula.atom a)) past ε
      (coherentMarketMaker (pairStrategy n (Formula.atom a)) past ∅ B
        (mentionedSet (pairStrategy n (Formula.atom a))) subset_rfl (hW_empty B) hε) :=
  AttemptA.coherent_pair_not_marketMakerAccepts a n past B hε hε1

/-- **T4(b). The interior maker on `T_pair` quotes `atom a` strictly inside `(0,1)`** (`a < B`,
`D = ∅`: the all-true world holds it, the all-false world refutes it; `2^B ≥ 2` worlds). The
N+ witness of T3.
Source: [[bli-coherent-mm-mandate]] T4(b); T3
Kind: N+
Fidelity: n/a
Hyps: (a) `hB : a < B`, `hε` -/
theorem interior_pair_quote_mem_Ioo (hB : a < B) :
    0 < (interiorCoherentMarketMaker (pairStrategy n (Formula.atom a)) past ∅ B
      (mentionedSet (pairStrategy n (Formula.atom a))) subset_rfl (hW_empty B) hε).quote
        (Formula.atom a) ∧
    (interiorCoherentMarketMaker (pairStrategy n (Formula.atom a)) past ∅ B
      (mentionedSet (pairStrategy n (Formula.atom a))) subset_rfl (hW_empty B) hε).quote
        (Formula.atom a) < 1 :=
  AttemptA.interior_pair_quote_mem_Ioo a n past B hε hB

end Atom

/-- **T4(b), grid interior maker (attempt B's instance)**: at `atom a`, the empty stage and
`B = a + 1`, the grid interior maker quotes the atom strictly inside `(0,1)`.
Source: [[bli-coherent-mm-mandate]] T4(b)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem gridInterior_pair_atom_nonDogmatic (n a : ℕ) (past : List RationalBeliefState) (ε : ℚ)
    (hε : 0 < ε) :
    0 < (gridInteriorCoherentMarketMaker (pairStrategy n (Formula.atom a)) past ∅ (a + 1)
        (AttemptB.pair_atom_hB n a) ⟨fun _ => false, AttemptB.consistentWith_empty _⟩
        (mentionedSet (pairStrategy n (Formula.atom a))) (Finset.Subset.refl _) ε hε).quote
          (Formula.atom a) ∧
      (gridInteriorCoherentMarketMaker (pairStrategy n (Formula.atom a)) past ∅ (a + 1)
        (AttemptB.pair_atom_hB n a) ⟨fun _ => false, AttemptB.consistentWith_empty _⟩
        (mentionedSet (pairStrategy n (Formula.atom a))) (Finset.Subset.refl _) ε hε).quote
          (Formula.atom a) < 1 :=
  AttemptB.interior_pair_atom_nonDogmatic n a past ε hε

/-! ## T4(c): a price-responsive strategy -/

/-- **The responsive strategy (of record)**: buy `1 − 2·price φ n` shares of `φ` (a `price` leaf
of rank `n`); it sells above `1/2` and buys below.
Source: [[bli-coherent-mm-mandate]] T4(c)
Kind: D
Fidelity: exact -/
abbrev responsiveStrategy (n : ℕ) (φ : Sentence) : Strategy n := AttemptB.responsiveStrategy n φ

/-- **T4(c). Every coherently accepted price of an undecided `φ` against the responsive strategy
is within `ε` of `1/2`**: in a world holding `φ` the value is `(1 − 2p)(1 − p)`, in one refuting
it `(1 − 2p)(−p)`; both `≤ ε` forces `|p − 1/2| ≤ ε`. T1's fixed point is not a boundary
artifact. Attempt B's general form, over the record's D3.
Source: [[bli-coherent-mm-mandate]] T4(c)
Kind: N+
Fidelity: exact
Hyps: (a) `hS`, `hacc`, `h1`/`h0` (`φ` undecided by `D` over `B` atoms) -/
theorem responsive_near_half {n : ℕ} {φ : Sentence} {D : Finset Sentence} {B : ℕ}
    {S : Finset Sentence} {w : FiniteWorld B → ℚ}
    (hS : mentionedSet (responsiveStrategy n φ) ⊆ S) (past : List RationalBeliefState) {ε : ℚ}
    (hε : 0 ≤ ε) (hacc : CoherentAccepts (responsiveStrategy n φ) past D B S ε w)
    (h1 : ∃ u ∈ WD D B, (worldOf u).Holds φ) (h0 : ∃ u ∈ WD D B, ¬ (worldOf u).Holds φ) :
    |marginal w φ - 1 / 2| ≤ ε := by
  have hacc' := (coherentAccepts_iff_attemptB _ past D B S ε hacc.isWorldMeasure hS).mp hacc
  rw [WD_eq_attemptB] at h1 h0
  exact AttemptB.coherentAccepts_responsive_near_half hacc.isWorldMeasure.toB past hε hacc' h1 h0

/-- **T4(c) at an atom and the empty stage** (attempt A's instance): every coherently accepted
price of `atom a` against the responsive strategy is within `ε` of `1/2`.
Source: [[bli-coherent-mm-mandate]] T4(c)
Kind: N+
Fidelity: n/a
Hyps: (a) `hB : a < B`, `hS : atom a ∈ S`, `hacc` -/
theorem responsive_atom_accepted_near_half (a n : ℕ) (past : List RationalBeliefState) (B : ℕ)
    (hB : a < B) (S : Finset Sentence) (hS : Formula.atom a ∈ S) {ε : ℚ}
    {w : FiniteWorld B → ℚ}
    (hacc : CoherentAccepts (responsiveStrategy n (Formula.atom a)) past ∅ B S ε w) :
    |marginal w (Formula.atom a) - 1 / 2| ≤ ε :=
  AttemptA.responsive_accepted_near_half a n past B hB S hS hacc

end Cleanroom.Bli.BliCoherentMm
