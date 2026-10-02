import Cleanroom.Bli.BliOverlay.AttemptA.Mentioned
import Cleanroom.Bli.BliOverlay.AttemptB.Mentioned

/-!
# `bli-overlay` · Mentioned (reconciled): D1 the mentioned set, T1 value congruence

The package's definitions of record for D1 and T1, taken from attempt A (the two attempts'
`mentionedSet` are the same term; `mentionedSet_eq_attemptB` records the identity so that
attempt B's results transport). Everything here is stated once over the record's names and
proved by the attempt's declaration.

Sources: [[bli-overlay-mandate]] D1, T1; [[bli-overlay-report]] §Two attempts.
-/

namespace Cleanroom.Bli.BliOverlay

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## D1: the mentioned set -/

/-- **D1 (of record). The mentioned set** of a day-`n` strategy: its traded sentences together
with the sentences of every price leaf (of every rank) of every coefficient, as a `Finset`.
The predicate form is `bli-found`'s `MentionedBy` (`mem_mentionedSet_iff`). Attempt A's term;
attempt B's is the same term (`mentionedSet_eq_attemptB`).
Source: [[bli-overlay-mandate]] D1
Kind: D
Fidelity: exact -/
abbrev mentionedSet {n : ℕ} (s : Strategy n) : Finset Sentence := AttemptA.mentionedSet s

/-- `φ ∈ mentionedSet s ↔ MentionedBy s φ` — D1 does not redefine `MentionedBy`.
Source: [[bli-overlay-mandate]] D1
Kind: L
Fidelity: exact -/
theorem mem_mentionedSet_iff {n : ℕ} {s : Strategy n} {φ : Sentence} :
    φ ∈ mentionedSet s ↔ MentionedBy s φ :=
  AttemptA.mem_mentionedSet_iff

/-- Every traded sentence is mentioned: `s.support ⊆ mentionedSet s` (Known issue 2: the
support form of F2 is the weaker corollary).
Source: [[bli-overlay-mandate]] D1; Known issue 2
Kind: L
Fidelity: exact -/
theorem support_subset_mentionedSet {n : ℕ} (s : Strategy n) : s.support ⊆ mentionedSet s :=
  AttemptA.support_subset_mentionedSet s

/-- **The two attempts' D1 agree**: attempt B's `mentionedSet` is the record's (both are the
finite carrier of `MentionedBy`). This is what lets attempt B's theorems transport to the
definitions of record.
Source: [[bli-overlay-mandate]] D1; reconciliation
Kind: L
Fidelity: exact -/
theorem mentionedSet_eq_attemptB {n : ℕ} (s : Strategy n) :
    mentionedSet s = AttemptB.mentionedSet s := by
  ext φ
  rw [mem_mentionedSet_iff, AttemptB.mem_mentionedSet_iff]

/-! ## T1: value congruence on mentioned cells -/

/-- **T1, leaf level (real semantics).** A feature cannot distinguish two histories that agree
on every cell it queries, under any environment `ρ` (so the lemma goes through shared `letE`
bindings, as FAF's `EF.denoteWith_eq_of_eqUpTo` does). `bli-transfer` proves the same lemma
under the name `denote_eq_of_agree_on_leaves`; not cited (concurrent).
Source: [[bli-overlay-mandate]] T1
Kind: L
Fidelity: exact -/
theorem EF.denoteWith_eq_of_eqOn_priceQueries (e : EF) (ρ : List ℝ) (V W : History)
    (h : ∀ q ∈ e.priceQueries, V q.1 q.2 = W q.1 q.2) :
    e.denoteWith ρ V = e.denoteWith ρ W :=
  AttemptA.EF.denoteWith_eq_of_eqOn_priceQueries e ρ V W h

/-- **T1, leaf level (rational semantics).**
Source: [[bli-overlay-mandate]] T1
Kind: L
Fidelity: exact -/
theorem EF.denoteRatWith_eq_of_eqOn_priceQueries (e : EF) (ρ : List ℚ)
    (Q R : ℕ → Sentence → ℚ) (h : ∀ q ∈ e.priceQueries, Q q.1 q.2 = R q.1 q.2) :
    e.denoteRatWith ρ Q = e.denoteRatWith ρ R :=
  AttemptA.EF.denoteRatWith_eq_of_eqOn_priceQueries e ρ Q R h

/-- **T1 (strategy level, real semantics).** A day-`n` strategy's value depends on the history
only through the cells `(k ≤ n, φ)` with `φ` mentioned: the exact locality of the market-maker
check.
Source: [[bli-overlay-mandate]] T1; [[bli-program]] §3.3 (i)
Kind: L
Fidelity: exact -/
theorem Strategy.value_eq_of_eqOn_mentioned {n : ℕ} (T : Strategy n) (V W : History)
    (w : Sentence → ℝ) (h : ∀ φ, MentionedBy T φ → ∀ k ≤ n, V k φ = W k φ) :
    T.value V w = T.value W w :=
  AttemptA.Strategy.value_eq_of_eqOn_mentioned T V W w h

/-- **T1 (strategy level, rational semantics).** The `marketValueRat` twin.
Source: [[bli-overlay-mandate]] T1
Kind: L
Fidelity: exact -/
theorem Strategy.marketValueRat_eq_of_eqOn_mentioned {n : ℕ} (T : Strategy n)
    (Q R : ℕ → Sentence → ℚ) (w : Sentence → ℚ)
    (h : ∀ φ, MentionedBy T φ → ∀ k ≤ n, Q k φ = R k φ) :
    T.marketValueRat Q w = T.marketValueRat R w :=
  AttemptA.Strategy.marketValueRat_eq_of_eqOn_mentioned T Q R w h

end Cleanroom.Bli.BliOverlay
