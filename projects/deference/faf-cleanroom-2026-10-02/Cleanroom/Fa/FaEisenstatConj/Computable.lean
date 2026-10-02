import Cleanroom.Fa.FaEisenstatConj.Defs
import LogicalInduction.Construction.Primcodable

/-!
# `fa-eisenstat-conj` · Computable: the merge market is a computable market (T2)

The market half of FAF's criterion for `𝔼^∗ = mergeMarket A Q`: `ComputableMarket (mergeMarket A Q)`
from `ComputableMarket A` and a uniform program for the quote thresholds (`QuoteTable Q`). With
this proved, the OPEN inductor half (`Open.lean`) sits on `noExploit` alone — the mandate's trap
(iv): a `sorry` covering `marketComputable` would be weaker than the question.

Route: `mergeMarket A Q n φ = (n+1)⁻¹ ∑_{i<n+1} A n ((Q φ n).gt (i/(n+1)))`; with `A`'s exact
rational program `M : MarketComputation A`, the rational table
`mergeTable M Q n ⌜φ⌝ := (∑_i M.quote n ⌜(Q φ n).gt (i/(n+1))⌝) / (n+1)` is exact
(`mergeTable_exact`) and `Computable` (`mergeTable_computable`, FAF's `expectQuoteAt_computable`
argument with the `MachineThresholdCodeSeq` input replaced by the plain `Computable` table —
only computability of the codes is used, never a polynomial bound), and FAF's own constructor
`ComputableMarket.ofComputableTable` produces the `Nat.Partrec.Code`.

`QuoteTable` is the uniformity in `φ` that `CrossQuotePackage`'s per-`φ` `quote_codes` does not
give and `ComputableMarket` needs: one program writes every threshold sentence of every quote.
It is weaker than the uniform *machine* certificate `LUV.MachineThresholdCodeSeq` on the paired
family (no metering), which is what `ComputableMarket` asks for. Scope: one-way.
-/

namespace Cleanroom.Fa.FaEisenstatConj

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc

/-- **The quote table is computable**: one program maps `((φ, n), r)` to the threshold sentence
`⌜Q φ n > r⌝` (Mathlib's `Computable` over FAF's `Primcodable Sentence` and `Primcodable ℚ`). The
uniformity-in-`φ` certificate the market half of the criterion needs; a `CrossQuotePackage`'s
`quote_codes` is per sentence and does not give it.
Source: lean-deference-075 ("the sequence of quotes must first be a market"); mandate T1/T2 (`QuoteTable`)
Kind: D
Fidelity: exact (plain computability, no metering — all `ComputableMarket` asks)
Hyps: n/a -/
def QuoteTable (Q : Sentence → ℕ → LUV) : Prop :=
  Computable fun p : (Sentence × ℕ) × ℚ => (Q p.1.1 p.1.2).gt p.2

/-- The exact rational merge table: `A`'s day-`n` expectation of `Q φ n`, computed through `A`'s
exact rational quote program on the day's grid, indexed by the sentence code `c` (junk `⊤` on a
non-code, harmless as `ComputableMarket`'s docstring says of its own table).
Source: none: infrastructure (FAF `MarketComputation.expectQuoteAt`, re-indexed by sentence code)
Kind: D
Fidelity: n/a -/
def mergeTable {A : History} (M : MarketComputation A) (Q : Sentence → ℕ → LUV) (n c : ℕ) : ℚ :=
  (∑ i ∈ Finset.range (n + 1),
      M.quote n (Encodable.encode ((Q (decodeSentence c) n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))))) /
    ((n + 1 : ℕ) : ℚ)

/-- The merge table is exact: its cast at `⌜φ⌝` is `mergeMarket A Q n φ` (FAF's `quote_exact` on
every grid cell).
Source: none: infrastructure (FAF `expectQuoteAt_cast`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem mergeTable_exact {A : History} (M : MarketComputation A) (Q : Sentence → ℕ → LUV)
    (n : ℕ) (φ : Sentence) :
    mergeMarket A Q n φ = (mergeTable M Q n (Encodable.encode φ) : ℝ) := by
  unfold mergeTable
  rw [decodeSentence_encode, mergeMarket_apply, LUV.expect, LUV.expectApprox]
  have h : ∀ i ∈ Finset.range (n + 1),
      A n ((Q φ n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))) =
        ((M.quote n (Encodable.encode ((Q φ n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)))) : ℚ) : ℝ) :=
    fun i _ => M.quote_exact n _
  rw [Finset.sum_congr rfl h, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast, div_eq_inv_mul]

/-- The exact rational quote of a certified market program along computable day and sentence-code
streams is computable (FAF's `MarketComputation.quote_comp_computable`, restated so that this file
imports no `Construction.Quotation` module).
Source: none: infrastructure (FAF `MarketComputation.quote_comp_computable`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem quote_comp_computable {A : History} (M : MarketComputation A) {α : Type*} [Primcodable α]
    {d g : α → ℕ} (hd : Computable d) (hg : Computable g) :
    Computable fun a => M.quote (d a) (g a) := by
  have hin : Computable fun a => Nat.pair (d a) (g a) :=
    Primrec₂.natPair.to_comp.comp hd hg
  have heval : Partrec fun a => M.code.eval (Nat.pair (d a) (g a)) :=
    Nat.Partrec.Code.eval_part.comp (Computable.const M.code) hin
  have henc : Computable fun a => Encodable.encode (M.quote (d a) (g a)) :=
    heval.of_eq fun a => Part.eq_some_iff.mpr
      (by simpa [Nat.unpair_pair] using M.code_spec (Nat.pair (d a) (g a)))
  have hdec : Computable fun a =>
      (Encodable.decode (α := ℚ) (Encodable.encode (M.quote (d a) (g a)))).getD 0 :=
    Computable.option_getD (Computable.decode.comp henc) (Computable.const 0)
  exact hdec.of_eq fun a => by simp

/-- The sentence decoder is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem decodeSentence_computable : Computable decodeSentence :=
  (Computable.option_getD (Computable.decode (α := Sentence)) (Computable.const (⊤ : Sentence))).of_eq
    fun _ => rfl

/-- **The merge table is computable** from `A`'s market program and the quote table: each grid
cell's threshold sentence from `hQ`, its exact quote from `M`'s program, the bounded sum by
primitive recursion on the day, and the final average by `ratDiv_prim` — FAF's
`expectQuoteAt_computable` argument with the machine certificate replaced by `QuoteTable`.
Source: mandate T2 (the plain-`Computable` route); FAF `MarketComputation.expectQuoteAt_computable`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem mergeTable_computable {A : History} (M : MarketComputation A) {Q : Sentence → ℕ → LUV}
    (hQ : QuoteTable Q) : Computable fun a : ℕ × ℕ => mergeTable M Q a.1 a.2 := by
  -- `a = (n, c)`: the day and the sentence code.
  have hratio : Computable fun z : (ℕ × ℕ) × ℕ => ((z.2 : ℚ) / ((z.1.1 + 1 : ℕ) : ℚ)) :=
    ratDiv_prim.to_comp.comp (ratNatCast_prim.to_comp.comp Computable.snd)
      (ratNatCast_prim.to_comp.comp
        (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.fst)))
  have harg : Computable fun z : (ℕ × ℕ) × ℕ =>
      ((decodeSentence z.1.2, z.1.1), ((z.2 : ℚ) / ((z.1.1 + 1 : ℕ) : ℚ))) :=
    ((decodeSentence_computable.comp (Computable.snd.comp Computable.fst)).pair
      (Computable.fst.comp Computable.fst)).pair hratio
  have hgt : Computable fun z : (ℕ × ℕ) × ℕ =>
      (Q (decodeSentence z.1.2) z.1.1).gt ((z.2 : ℚ) / ((z.1.1 + 1 : ℕ) : ℚ)) :=
    (hQ.comp harg : _)
  -- The per-cell exact quote.
  have hcell : Computable fun z : (ℕ × ℕ) × ℕ =>
      M.quote z.1.1
        (Encodable.encode ((Q (decodeSentence z.1.2) z.1.1).gt
          ((z.2 : ℚ) / ((z.1.1 + 1 : ℕ) : ℚ)))) :=
    (quote_comp_computable M (Computable.fst.comp Computable.fst)
      (Computable.encode.comp hgt) : _)
  -- The bounded sum, by primitive recursion on the day.
  have hstep : Computable fun q : (ℕ × ℕ) × (ℕ × ℚ) =>
      q.2.2 + M.quote q.1.1
        (Encodable.encode ((Q (decodeSentence q.1.2) q.1.1).gt
          ((q.2.1 : ℚ) / ((q.1.1 + 1 : ℕ) : ℚ)))) := by
    have hc : Computable fun q : (ℕ × ℕ) × (ℕ × ℚ) =>
        M.quote q.1.1
          (Encodable.encode ((Q (decodeSentence q.1.2) q.1.1).gt
            ((q.2.1 : ℚ) / ((q.1.1 + 1 : ℕ) : ℚ)))) :=
      (hcell.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)) : _)
    exact (ratAdd_prim.to_comp.comp (Computable.snd.comp Computable.snd) hc : _)
  have hsum : Computable fun a : ℕ × ℕ => ∑ i ∈ Finset.range (a.1 + 1),
      M.quote a.1
        (Encodable.encode ((Q (decodeSentence a.2) a.1).gt
          ((i : ℚ) / ((a.1 + 1 : ℕ) : ℚ)))) := by
    have hrec := Computable.nat_rec (Primrec.succ.to_comp.comp Computable.fst)
      (Computable.const (0 : ℚ)) hstep.to₂
    refine hrec.of_eq fun a => ?_
    have key : ∀ m : ℕ, (Nat.rec (motive := fun _ => ℚ) 0
        (fun i s => s + M.quote a.1
          (Encodable.encode ((Q (decodeSentence a.2) a.1).gt
            ((i : ℚ) / ((a.1 + 1 : ℕ) : ℚ))))) m) =
        ∑ i ∈ Finset.range m,
          M.quote a.1
            (Encodable.encode ((Q (decodeSentence a.2) a.1).gt
              ((i : ℚ) / ((a.1 + 1 : ℕ) : ℚ)))) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ← ih]
    exact key (a.1 + 1)
  -- The final average.
  exact ((ratDiv_prim.to_comp.comp hsum
    (ratNatCast_prim.to_comp.comp (Primrec.succ.to_comp.comp Computable.fst)) : _) :
    Computable fun a : ℕ × ℕ => mergeTable M Q a.1 a.2)

/-- **T2 (headline). The merge market is a computable market** — the market half of FAF's
criterion for `𝔼^∗`: from `ComputableMarket A` (every inductor's `marketComputable`) and the
quote table `hQ`, through FAF's own constructor `ComputableMarket.ofComputableTable` on the exact
rational table `mergeTable`. No hypothesis about `H`, `f` or what the quotes name: the market
half holds for *every* quote assignment, which is why the OPEN inductor half is stated on
`noExploit` alone (`Open.lean`).
Scope: one-way, mirror direction — `A` reads `H` through the ledger; `H` never reads `A`. This is
the lookahead construction in the **corpus construal (Abram's version)**, not Sam Eisenstat's
intended information structure ([[eisenstat-conjecture-attribution]] §2, §5); claims about Sam's
intent are ATTRIBUTION-UNVETTED. Computable branch: FAF's criterion makes both inductors
computable markets over computable processes (attribution page §2, "the computability fork").
Source: lean-deference-075 (ill-posedness note: "the quote sequence must first be a market"); vq-wiki-044; mandate T2
Kind: C
Fidelity: exact
Hyps: (a) `hA` (every inductor's `marketComputable`), `hQ` (the uniform quote program; discharged at the all-sentences ledger witness, `Witnesses.lean`) -/
theorem mergeMarket_computableMarket {A : History} (hA : ComputableMarket A)
    {Q : Sentence → ℕ → LUV} (hQ : QuoteTable Q) : ComputableMarket (mergeMarket A Q) := by
  obtain ⟨M⟩ := hA.nonemptyComputation
  refine ComputableMarket.ofComputableTable (mergeTable M Q)
    (fun n φ => mergeMarket_mem_Icc (fun n s => hA.price_mem_Icc n s) Q n φ)
    (fun n φ => mergeTable_exact M Q n φ) ?_
  exact (Computable.encode.comp ((mergeTable_computable M hQ).comp
    ((Computable.fst.comp Computable.unpair).pair
      (Computable.snd.comp Computable.unpair)))).of_eq fun z => rfl

/-- T2 at an inductor `A`: the market half of the criterion for `𝔼^∗` from `A`'s own
`marketComputable`.
Source: mandate T2
Kind: L
Fidelity: exact
Hyps: (a) `hQ` -/
theorem mergeMarket_computableMarket_of_inductor {A : History} {DPA : DeductiveProcess}
    [hA : IsLogicalInductor A DPA] {Q : Sentence → ℕ → LUV} (hQ : QuoteTable Q) :
    ComputableMarket (mergeMarket A Q) :=
  mergeMarket_computableMarket hA.marketComputable hQ

end Cleanroom.Fa.FaEisenstatConj
