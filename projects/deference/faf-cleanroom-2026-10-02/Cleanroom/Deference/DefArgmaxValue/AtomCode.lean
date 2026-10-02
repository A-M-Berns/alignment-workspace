import Cleanroom.Deference.DefArgmaxValue.Selector

/-!
# `def-argmax-value` · AtomCode: computing the market's quote of a selector atom

The quotes lists of the selector (`Selector.lean`) read the market's own day-`f n` price of the
public atoms `quoteAtom ⟨c, ⟨n, j⟩⟩` of a *candidate* code `c`. FAF's
`diagonalPriceDecisionPart_partrec` shows the sentence code of such an atom is primitive
recursive in `(c, n)` through the concrete payload encoding; `quoteAtom_encode_primrec` is that
step for an arbitrary primitive-recursive payload, and `quote_of_atom_computable` composes it
with FAF's `MarketComputation.quote_comp_computable`.

Construction-facing infrastructure.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction

/-- The sentence code of `quoteAtom (g a)` is primitive recursive in `a` for primitive-recursive
`g` (FAF's `hsentence` step of `diagonalPriceDecisionPart_partrec`, with a general payload).
Source: none: infrastructure (FAF `diagonalPriceDecisionPart_partrec`)
Kind: L
Fidelity: n/a -/
theorem quoteAtom_encode_primrec {α : Type*} [Primcodable α] {g : α → ℕ} (hg : Primrec g) :
    Primrec fun a => Encodable.encode (quoteAtom (g a)) := by
  have hpayload : Primrec fun a =>
      quotationClaimCode universalQuotePos universalQuoteNeg (g a) :=
    Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.const (Encodable.encode universalQuotePos))
        (Primrec₂.natPair.comp (Primrec.const (Encodable.encode universalQuoteNeg)) hg))
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) hpayload)).of_eq
    fun _ => rfl

/-- The market's quote of a selector atom along computable day and payload streams is
computable.
Source: none: infrastructure (FAF `MarketComputation.quote_comp_computable`)
Kind: L
Fidelity: n/a -/
theorem quote_of_atom_computable {P : History} (market : MarketComputation P) {α : Type*}
    [Primcodable α] {d g : α → ℕ} (hd : Computable d) (hg : Primrec g) :
    Computable fun a => market.quote (d a) (Encodable.encode (quoteAtom (g a))) :=
  market.quote_comp_computable hd (quoteAtom_encode_primrec hg).to_comp

/-- The payload `⟨encode c, ⟨n, j⟩⟩` of the atom of candidate `c` at day `n`, option `j`, is
primitive recursive in `(c, n)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem atomPayload_primrec (j : ℕ) :
    Primrec fun z : Nat.Partrec.Code × ℕ =>
      Nat.pair (Encodable.encode z.1) (Nat.pair z.2 j) :=
  Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
    (Primrec₂.natPair.comp Primrec.snd (Primrec.const j))

end Cleanroom.Deference.DefArgmaxValue
