import Cleanroom.Bli.BliOverlay.Mentioned
import Cleanroom.Bli.BliOverlay.AttemptA.FirmSupport
import Cleanroom.Bli.BliOverlay.AttemptB.FirmSupport

/-!
# `bli-overlay` · FirmSupport (reconciled): T2, the firm-support lemma F2

Both attempts prove the same statement of F2 (`∃ N₀, ∀ n ≥ N₀, ∀ DP Q φ, MentionedBy
(TradingFirmAt DP Q n) φ → SmallOn n φ`) by the same three steps (structure, size per index,
arithmetic on `progClock`), differing only in the arithmetic estimate and hence the constant:
attempt A reaches `N₀ = 2^10 + 4C + 32` (`1096` at the structured constant `C = 10`), attempt B
`N₀ = (C + 16)^2` (`676` at `C = 10`). The record takes attempt B's proof for the headline (the
smaller constant, exposed by `firm_mentioned_small_from`) and derives the finite-set and
support corollaries from it; attempt A's proof stands as the independent second derivation
(`AttemptA.firm_mentioned_small`), and the witness and the structure lemma are attempt A's
(they are stated over the record's `mentionedSet`).

Sources: [[bli-overlay-mandate]] T2; [[bli-program]] §2.1 (F2), §4 row F2.
-/

namespace Cleanroom.Bli.BliOverlay

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## Structure: the firm's mentioned set -/

/-- **The firm's mentioned set, characterised** (Known issue 5): the union over `j ≤ n` of the
enumerated traders' day-`n` mentioned sets — independent of `DP` and `Q`.
Source: [[bli-overlay-mandate]] T2 step 1; Known issue 5
Kind: L
Fidelity: exact -/
theorem mentionedSet_TradingFirmAt_eq (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    mentionedSet (TradingFirmAt DP Q n) =
      (Finset.range (n + 1)).biUnion fun j => mentionedSet ((enumeratedTrader j).strat n) :=
  AttemptA.mentionedSet_TradingFirmAt_eq DP Q n

/-- The firm's mentioned set does not depend on the process or the table (attempt B's form,
transported).
Source: [[bli-overlay-mandate]] Known issue 5
Kind: L
Fidelity: exact -/
theorem mentionedSet_TradingFirmAt_indep (DP DP' : DeductiveProcess) (Q Q' : ℕ → Sentence → ℚ)
    (n : ℕ) : mentionedSet (TradingFirmAt DP Q n) = mentionedSet (TradingFirmAt DP' Q' n) := by
  rw [mentionedSet_eq_attemptB, mentionedSet_eq_attemptB]
  exact AttemptB.mentionedSet_TradingFirmAt_eq DP DP' Q Q' n

/-! ## T2: the firm-support lemma -/

/-- **T2 with the constant exposed.** For the structured-escape constant `C` (bli-found's
`tokenSize_le_of_structured`, proved with `C = 10`), from day `(C + 16)^2` on the firm's
day-`n` strategy mentions only day-`n`-small sentences, for every process and every table.
Attempt B's estimate: `(C+6)(progClock j n + 1) ≤ (C+6)(2√n+1)(n+1)^{√n} ≤ 4^{√n}(n+1)^{√n} ≤
2^{√n·√n} ≤ 2^n`, with both `Nat.unpair` components `≤ Nat.sqrt`.
Source: [[bli-overlay-mandate]] T2
Kind: C
Fidelity: exact
Hyps: (a) — `hC` is `tokenSize_le_of_structured`'s conclusion (proved in bli-found), passed
explicitly to expose `C` -/
theorem firm_mentioned_small_from {C : ℕ}
    (hC : ∀ (ts : List ℕ) (φ : Sentence) (rest : List ℕ),
      parseStructuredPaperPrime ts = some (φ, rest) →
        tokenSize φ ≤ 2 ^ (C * (ts.length - rest.length)) + C) :
    ∀ n ≥ (C + 16) ^ 2, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ) (φ : Sentence),
      MentionedBy (TradingFirmAt DP Q n) φ → SmallOn n φ :=
  AttemptB.firm_mentioned_small_from hC

/-- **T2 (F2, headline, load-bearing). The firm-support lemma.** From some day `N₀` on, every
sentence FAF's trading firm's day-`n` strategy `TradingFirmAt DP Q n` mentions — traded, or read
at a price leaf of one of its coefficients — is small on day `n`, uniformly in the process `DP`
and the table `Q` (the overlaid table included). `N₀ = (C + 16)^2` (`676` at `C = 10`) by
attempt B's estimate; attempt A's independent proof (`AttemptA.firm_mentioned_small`) gives
`N₀ = 2^10 + 4C + 32` (`1096`). The `MentionedBy` form is the headline (Known issue 2).
Source: [[bli-overlay-mandate]] T2; [[bli-program]] §2.1 (F2), §4 row F2
Kind: C
Fidelity: exact
Hyps: (a) — nothing assumed: the structure lemma, bli-found's size bounds and the clock
estimate are all proved -/
theorem firm_mentioned_small :
    ∃ N₀, ∀ n ≥ N₀, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ) (φ : Sentence),
      MentionedBy (TradingFirmAt DP Q n) φ → SmallOn n φ :=
  AttemptB.firm_mentioned_small

/-- **T2, finite-set form with the constant.** `mentionedSet (TradingFirmAt DP Q n) ⊆ smallSet n`
from `(C + 16)^2` on.
Source: [[bli-overlay-mandate]] T2; [[bli-program]] §3.3 (i)
Kind: C
Fidelity: exact
Hyps: (a) — `hC` as in `firm_mentioned_small_from` -/
theorem firm_mentionedSet_subset_smallSet_from {C : ℕ}
    (hC : ∀ (ts : List ℕ) (φ : Sentence) (rest : List ℕ),
      parseStructuredPaperPrime ts = some (φ, rest) →
        tokenSize φ ≤ 2 ^ (C * (ts.length - rest.length)) + C) :
    ∀ n ≥ (C + 16) ^ 2, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ),
      mentionedSet (TradingFirmAt DP Q n) ⊆ smallSet n := by
  intro n hn DP Q φ hφ
  exact mem_smallSet.mpr (firm_mentioned_small_from hC n hn DP Q φ (mem_mentionedSet_iff.mp hφ))

/-- **T2, finite-set form.** `mentionedSet (TradingFirmAt DP Q n) ⊆ smallSet n` from `N₀` on —
what [[bli-program]] §3.3 (i) uses.
Source: [[bli-overlay-mandate]] T2; [[bli-program]] §3.3 (i)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem firm_mentionedSet_subset_smallSet :
    ∃ N₀, ∀ n ≥ N₀, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ),
      mentionedSet (TradingFirmAt DP Q n) ⊆ smallSet n := by
  obtain ⟨C, hC⟩ := tokenSize_le_of_structured
  exact ⟨(C + 16) ^ 2, firm_mentionedSet_subset_smallSet_from hC⟩

/-- **T2, the plan's wording.** `(TradingFirmAt DP Q n).support ⊆ smallSet n` from `N₀` on —
the traded sentences only; weaker than the `MentionedBy` form (Known issue 2).
Source: [[bli-overlay-mandate]] T2; [[bli-program]] §4 row F2
Kind: C
Fidelity: weaker: traded sentences only (the plan's F2 wording); the headline is the
`MentionedBy` form
Hyps: (a) -/
theorem firm_support_subset_smallSet :
    ∃ N₀, ∀ n ≥ N₀, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ),
      (TradingFirmAt DP Q n).support ⊆ smallSet n := by
  obtain ⟨N₀, hN₀⟩ := firm_mentionedSet_subset_smallSet
  exact ⟨N₀, fun n hn DP Q => (support_subset_mentionedSet _).trans (hN₀ n hn DP Q)⟩

/-! ## The witness -/

/-- **N+ for T2.** The firm's mentioned set is not empty: from the enumeration index `i` of
FAF's `buyAtomDaily` on (`exists_enumeratedTrader_eq`; existential, not computed), the firm's
day-`n` strategy mentions `⌜aₙ⌝`, for every `DP` and `Q`; the mentioned sentence changes with
the day. Both attempts prove this; the record takes attempt A's (stated over the record's
`mentionedSet`).
Source: [[bli-overlay-mandate]] T2 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem firm_mentions_something :
    ∃ i, ∀ n ≥ i, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ),
      Formula.atom n ∈ mentionedSet (TradingFirmAt DP Q n) :=
  AttemptA.firm_mentions_something

end Cleanroom.Bli.BliOverlay
