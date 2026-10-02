import Cleanroom.Bli.BliFound.Bridge
import LogicalInduction.Construction.MarketMaker

/-!
# `bli-overlay` (attempt A) · Mentioned: the mentioned set and value congruence on mentioned cells

**D1 and T1 of the mandate.** A day-`n` strategy's value on a history depends on the history only
through finitely many cells: the price leaves `price φ k` of its coefficients and the day-`n`
prices of its traded sentences. `bli-found`'s `MentionedBy s φ` names exactly the sentences of
those cells; this file packages them as a `Finset` (`mentionedSet`, D1) and proves the
congruence lemmas (T1): two histories agreeing on every mentioned cell of days `≤ n` give the same
strategy value (`Strategy.value_eq_of_eqOn_mentioned`), and the rational twin for
`marketValueRat` (`Strategy.marketValueRat_eq_of_eqOn_mentioned`). Both come from the leaf-level
congruence `EF.denoteWith_eq_of_eqOn_priceQueries`, proved by the induction of FAF's
`EF.denoteWith_eq_of_eqUpTo` (`MarketMaker.lean:558`) with the leaf case taken from the
agreement hypothesis instead of the rank bound. `bli-transfer` proves the same leaf congruence
under the name `denote_eq_of_agree_on_leaves` (concurrent package; not cited here).

Nothing here is a headline: every declaration is `L` or `D`.

Sources: [[bli-overlay-mandate]] D1, T1; [[bli-program]] §3.3 (i).
-/

namespace Cleanroom.Bli.BliOverlay.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## Leaves are below the rank -/

/-- Every price leaf of a feature reads a day at most its rank.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EF.priceQueries_fst_le_rank (e : EF) {k : ℕ} {φ : Sentence}
    (h : (k, φ) ∈ e.priceQueries) : k ≤ e.rank := by
  induction e with
  | price ψ day =>
      simp only [EF.priceQueries, List.mem_singleton, Prod.mk.injEq] at h
      simp [EF.rank, h.1]
  | const q => simp [EF.priceQueries] at h
  | add a b iha ihb =>
      simp only [EF.priceQueries, List.mem_append] at h
      simp only [EF.rank]
      rcases h with h | h
      · exact le_trans (iha h) (Nat.le_max_left _ _)
      · exact le_trans (ihb h) (Nat.le_max_right _ _)
  | mul a b iha ihb =>
      simp only [EF.priceQueries, List.mem_append] at h
      simp only [EF.rank]
      rcases h with h | h
      · exact le_trans (iha h) (Nat.le_max_left _ _)
      · exact le_trans (ihb h) (Nat.le_max_right _ _)
  | max a b iha ihb =>
      simp only [EF.priceQueries, List.mem_append] at h
      simp only [EF.rank]
      rcases h with h | h
      · exact le_trans (iha h) (Nat.le_max_left _ _)
      · exact le_trans (ihb h) (Nat.le_max_right _ _)
  | safeRecip a iha =>
      simp only [EF.priceQueries] at h
      simpa [EF.rank] using iha h
  | var i => simp [EF.priceQueries] at h
  | letE x body ihx ihbody =>
      simp only [EF.priceQueries, List.mem_append] at h
      simp only [EF.rank]
      rcases h with h | h
      · exact le_trans (ihx h) (Nat.le_max_left _ _)
      · exact le_trans (ihbody h) (Nat.le_max_right _ _)

/-! ## T1: value congruence on the price leaves -/

/-- **T1, leaf level (real semantics).** A feature cannot distinguish two histories that agree
on every cell it queries; the environment `ρ` is arbitrary, so the lemma goes through shared
`letE` bindings. The induction of FAF's `EF.denoteWith_eq_of_eqUpTo`, with the leaf case read
off the agreement hypothesis.
Source: [[bli-overlay-mandate]] T1
Kind: L
Fidelity: exact -/
lemma EF.denoteWith_eq_of_eqOn_priceQueries (e : EF) (ρ : List ℝ) (V W : History)
    (h : ∀ q ∈ e.priceQueries, V q.1 q.2 = W q.1 q.2) :
    e.denoteWith ρ V = e.denoteWith ρ W := by
  induction e generalizing ρ with
  | price φ day => exact h (day, φ) (by simp [EF.priceQueries])
  | const q => rfl
  | add a b iha ihb =>
      simp only [EF.priceQueries, List.mem_append] at h
      simp [EF.denoteWith, iha ρ (fun q hq => h q (Or.inl hq)),
        ihb ρ (fun q hq => h q (Or.inr hq))]
  | mul a b iha ihb =>
      simp only [EF.priceQueries, List.mem_append] at h
      simp [EF.denoteWith, iha ρ (fun q hq => h q (Or.inl hq)),
        ihb ρ (fun q hq => h q (Or.inr hq))]
  | max a b iha ihb =>
      simp only [EF.priceQueries, List.mem_append] at h
      simp [EF.denoteWith, iha ρ (fun q hq => h q (Or.inl hq)),
        ihb ρ (fun q hq => h q (Or.inr hq))]
  | safeRecip a iha =>
      simp only [EF.priceQueries] at h
      simp [EF.denoteWith, iha ρ h]
  | var i => rfl
  | letE x body ihx ihbody =>
      simp only [EF.priceQueries, List.mem_append] at h
      simp only [EF.denoteWith]
      rw [ihx ρ (fun q hq => h q (Or.inl hq))]
      exact ihbody _ (fun q hq => h q (Or.inr hq))

/-- The closed-environment form of `EF.denoteWith_eq_of_eqOn_priceQueries`.
Source: [[bli-overlay-mandate]] T1
Kind: L
Fidelity: exact -/
lemma EF.denote_eq_of_eqOn_priceQueries (e : EF) (V W : History)
    (h : ∀ q ∈ e.priceQueries, V q.1 q.2 = W q.1 q.2) :
    e.denote V = e.denote W :=
  EF.denoteWith_eq_of_eqOn_priceQueries e [] V W h

/-- **T1, leaf level (rational semantics).** The `denoteRatWith` twin of
`EF.denoteWith_eq_of_eqOn_priceQueries`.
Source: [[bli-overlay-mandate]] T1
Kind: L
Fidelity: exact -/
lemma EF.denoteRatWith_eq_of_eqOn_priceQueries (e : EF) (ρ : List ℚ)
    (Q R : ℕ → Sentence → ℚ) (h : ∀ q ∈ e.priceQueries, Q q.1 q.2 = R q.1 q.2) :
    e.denoteRatWith ρ Q = e.denoteRatWith ρ R := by
  induction e generalizing ρ with
  | price φ day => exact h (day, φ) (by simp [EF.priceQueries])
  | const q => rfl
  | add a b iha ihb =>
      simp only [EF.priceQueries, List.mem_append] at h
      simp [EF.denoteRatWith, iha ρ (fun q hq => h q (Or.inl hq)),
        ihb ρ (fun q hq => h q (Or.inr hq))]
  | mul a b iha ihb =>
      simp only [EF.priceQueries, List.mem_append] at h
      simp [EF.denoteRatWith, iha ρ (fun q hq => h q (Or.inl hq)),
        ihb ρ (fun q hq => h q (Or.inr hq))]
  | max a b iha ihb =>
      simp only [EF.priceQueries, List.mem_append] at h
      simp [EF.denoteRatWith, iha ρ (fun q hq => h q (Or.inl hq)),
        ihb ρ (fun q hq => h q (Or.inr hq))]
  | safeRecip a iha =>
      simp only [EF.priceQueries] at h
      simp [EF.denoteRatWith, iha ρ h]
  | var i => rfl
  | letE x body ihx ihbody =>
      simp only [EF.priceQueries, List.mem_append] at h
      simp only [EF.denoteRatWith]
      rw [ihx ρ (fun q hq => h q (Or.inl hq))]
      exact ihbody _ (fun q hq => h q (Or.inr hq))

/-- The closed-environment form of `EF.denoteRatWith_eq_of_eqOn_priceQueries`.
Source: [[bli-overlay-mandate]] T1
Kind: L
Fidelity: exact -/
lemma EF.denoteRat_eq_of_eqOn_priceQueries (e : EF) (Q R : ℕ → Sentence → ℚ)
    (h : ∀ q ∈ e.priceQueries, Q q.1 q.2 = R q.1 q.2) :
    e.denoteRat Q = e.denoteRat R :=
  EF.denoteRatWith_eq_of_eqOn_priceQueries e [] Q R h

/-- **T1 (strategy level, real semantics).** A day-`n` strategy has the same value on two
histories that agree, on every day `k ≤ n`, at every sentence the strategy mentions. This is
the exact locality of the market-maker check: nothing off the mentioned cells matters.
Source: [[bli-overlay-mandate]] T1; [[bli-program]] §3.3 (i)
Kind: L
Fidelity: exact -/
lemma Strategy.value_eq_of_eqOn_mentioned {n : ℕ} (T : Strategy n) (V W : History)
    (w : Sentence → ℝ) (h : ∀ φ, MentionedBy T φ → ∀ k ≤ n, V k φ = W k φ) :
    T.value V w = T.value W w := by
  unfold Strategy.value
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hleaf : p.1.denote V = p.1.denote W := by
    apply EF.denote_eq_of_eqOn_priceQueries
    intro q hq
    have hmem : MentionedBy T q.2 := Or.inr ⟨p, hp, q.1, by simpa using hq⟩
    exact h q.2 hmem q.1 (le_trans (EF.priceQueries_fst_le_rank p.1 (by simpa using hq))
      (T.rank_le p hp))
  have htrade : V n p.2 = W n p.2 := h p.2 (Or.inl ⟨p.1, hp⟩) n le_rfl
  rw [hleaf, htrade]

/-- **T1 (strategy level, rational semantics).** The `marketValueRat` twin of
`Strategy.value_eq_of_eqOn_mentioned`.
Source: [[bli-overlay-mandate]] T1
Kind: L
Fidelity: exact -/
lemma Strategy.marketValueRat_eq_of_eqOn_mentioned {n : ℕ} (T : Strategy n)
    (Q R : ℕ → Sentence → ℚ) (w : Sentence → ℚ)
    (h : ∀ φ, MentionedBy T φ → ∀ k ≤ n, Q k φ = R k φ) :
    T.marketValueRat Q w = T.marketValueRat R w := by
  unfold Strategy.marketValueRat
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hleaf : p.1.denoteRat Q = p.1.denoteRat R := by
    apply EF.denoteRat_eq_of_eqOn_priceQueries
    intro q hq
    have hmem : MentionedBy T q.2 := Or.inr ⟨p, hp, q.1, by simpa using hq⟩
    exact h q.2 hmem q.1 (le_trans (EF.priceQueries_fst_le_rank p.1 (by simpa using hq))
      (T.rank_le p hp))
  have htrade : Q n p.2 = R n p.2 := h p.2 (Or.inl ⟨p.1, hp⟩) n le_rfl
  rw [hleaf, htrade]

/-! ## D1: the mentioned set -/

/-- **D1. The mentioned set** of a day-`n` strategy: its traded sentences together with the
sentences of every price leaf (of every rank) of every coefficient, as a `Finset`. The predicate
form is `bli-found`'s `MentionedBy` (`mem_mentionedSet_iff`); this is its finite carrier. Leaves of
every rank are included, so the set does not depend on the day.
Source: [[bli-overlay-mandate]] D1
Kind: D
Fidelity: exact -/
def mentionedSet {n : ℕ} (s : Strategy n) : Finset Sentence :=
  (s.trades.map Prod.snd).toFinset ∪
    (s.trades.flatMap fun p => p.1.priceQueries.map Prod.snd).toFinset

/-- `φ ∈ mentionedSet s ↔ MentionedBy s φ`.
Source: [[bli-overlay-mandate]] D1
Kind: L
Fidelity: exact -/
lemma mem_mentionedSet_iff {n : ℕ} {s : Strategy n} {φ : Sentence} :
    φ ∈ mentionedSet s ↔ MentionedBy s φ := by
  unfold mentionedSet MentionedBy
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_flatMap]
  constructor
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, q, hq, rfl⟩)
    · exact Or.inl ⟨p.1, hp⟩
    · exact Or.inr ⟨p, hp, q.1, hq⟩
  · rintro (⟨e, he⟩ | ⟨p, hp, k, hk⟩)
    · exact Or.inl ⟨(e, φ), he, rfl⟩
    · exact Or.inr ⟨p, hp, (k, φ), hk, rfl⟩

/-- Every traded sentence is mentioned: `s.support ⊆ mentionedSet s`.
Source: [[bli-overlay-mandate]] D1; Known issue 2
Kind: L
Fidelity: exact -/
lemma support_subset_mentionedSet {n : ℕ} (s : Strategy n) :
    s.support ⊆ mentionedSet s := by
  intro φ hφ
  rw [mem_mentionedSet_iff]
  simp only [Strategy.support, Finset.mem_image, List.mem_toFinset] at hφ
  obtain ⟨p, hp, rfl⟩ := hφ
  exact Or.inl ⟨p.1, hp⟩

/-- The `mentionedSet` form of `Strategy.value_eq_of_eqOn_mentioned`.
Source: [[bli-overlay-mandate]] T1
Kind: L
Fidelity: exact -/
lemma Strategy.value_eq_of_eqOn_mentionedSet {n : ℕ} (T : Strategy n) (V W : History)
    (w : Sentence → ℝ) (h : ∀ φ ∈ mentionedSet T, ∀ k ≤ n, V k φ = W k φ) :
    T.value V w = T.value W w :=
  Strategy.value_eq_of_eqOn_mentioned T V W w fun φ hφ => h φ (mem_mentionedSet_iff.mpr hφ)

end Cleanroom.Bli.BliOverlay.AttemptA
