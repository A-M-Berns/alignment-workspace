import Cleanroom.Deference.DefArgmaxValue.Open

/-!
# Audit r3 (adversarial) probe: `WorldOnly` discriminates

`WorldOnlyRefuted.lean` refutes the world-only conjecture on `foMenu`, a liar rebuilt through
`T`'s theorem lane (tag `5`). The refutation has content only if the syntactic predicate
`WorldOnly` actually *rejects* the ordinary quotation-lane liar menu `probeMenu` (tag `2`);
otherwise "world-only" would be satisfied by every menu and the theorem-lane rebuild would be
theatre. This probe checks that `probeMenu` is **not** world-only: its option `0` at threshold
`½` is the liar atom `quoteAtom ⟨code, ⟨n, 1⟩⟩`, whose single atom code carries tag `2`
(FAF `sentenceAtomCodes_quoteAtom`).

Not imported by the library.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction
open Cleanroom.Found.DefLattice
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-- A quotation literal has an atom code of tag `2`. -/
theorem quoteAtom_has_tag2_atom (w : ℕ) :
    ∃ a ∈ sentenceAtomCodes (quoteAtom w), a.unpair.1 = 2 := by
  refine ⟨quotationClaimCode universalQuotePos universalQuoteNeg w, ?_, ?_⟩
  · rw [quoteAtom, quotationClaimSentence, sentenceAtomCodes_atom]
    exact Finset.mem_singleton_self _
  · simp [quotationClaimCode]

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
variable (f : DeferralFunction) (s : ℚ)

/-- **The quotation-lane probe menu is not world-only**: the predicate of record rejects the
package's own liar menu, so `foMenu_worldOnly` + `condStableOn_foMenu_refuted` is a genuine
refutation through a lane the predicate does not see. -/
theorem probeMenu_not_worldOnly (hs : 0 ≤ s) : ¬ WorldOnly (probeMenu T f s hs) := by
  intro h
  have key := h 0 0 (1 / 2)
  rw [probeMenu_O_zero] at key
  have hgt : (literalIndicator (liarSentence T f s hs 0)).gt (1 / 2) =
      liarSentence T f s hs 0 := by
    simp only [literalIndicator]
    rw [if_neg (by norm_num), if_pos (by norm_num)]
  rw [hgt] at key
  unfold liarSentence selectorAtom BooleanQuoteCode.sentence at key
  obtain ⟨a, ha, ha2⟩ := quoteAtom_has_tag2_atom
    (Nat.pair (selectorQuoteCode (probeQuotes T f s) eqRel T (probeQuotes_computable T f s hs)
      eqRel_primrec).code (Nat.pair 0 1))
  exact key a ha ha2

/-- Instance line at `𝗣𝗔`, `succDeferral`, `s = ½`. -/
example : ¬ WorldOnly (probeMenu 𝗣𝗔 succDeferral (1 / 2) (by norm_num)) :=
  probeMenu_not_worldOnly 𝗣𝗔 succDeferral (1 / 2) (by norm_num)

#print axioms probeMenu_not_worldOnly

end

end Cleanroom.Deference.DefArgmaxValue
