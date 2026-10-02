import Cleanroom.Bli.BliFound.Bridge
import LogicalInduction.Construction.MarketMaker

/-!
# `bli-overlay` (attempt B) · Mentioned: the mentioned set (D1) and value congruence on mentioned cells (T1)

* **D1.** `mentionedSet s : Finset Sentence` — the traded sentences of the day strategy `s`
  together with the sentences of every price leaf of every coefficient, with
  `mem_mentionedSet_iff : φ ∈ mentionedSet s ↔ Cleanroom.Bli.BliFound.MentionedBy s φ`.
  `MentionedBy` is bli-found's predicate and is not redefined here.
* **T1.** `EF.denoteWith_eq_of_eqOn_priceQueries` (an expressible feature cannot distinguish
  two histories agreeing on its price leaves — the induction of FAF's
  `EF.denoteWith_eq_of_eqUpTo` with the leaf case taken from the agreement hypothesis instead
  of the rank bound), its rational twin, and the strategy forms
  `Strategy.value_eq_of_eqOn_mentioned` / `Strategy.marketValueRat_eq_of_eqOn_mentioned`:
  a day-`n` strategy's value depends on the history only through the cells `(k, φ)` with
  `k ≤ n` and `φ` mentioned. `bli-transfer` proves the same lemma under the name
  `denote_eq_of_agree_on_leaves`; the two packages run concurrently and neither cites the other.

Everything here is infrastructure (Kind L/D); nothing is a headline.
-/

namespace Cleanroom.Bli.BliOverlay.AttemptB

open LogicalInduction Cleanroom.Bli.BliFound

/-! ## D1: the mentioned set -/

/-- **D1. The mentioned set** of a day strategy: its traded sentences together with the
sentences of all price leaves (`EF.priceQueries`, every rank) of all its coefficients.
Source: [[bli-overlay-mandate]] D1; [[bli-program]] §3.3 (i)
Kind: D
Fidelity: exact -/
def mentionedSet {n : ℕ} (s : Strategy n) : Finset Sentence :=
  (s.trades.map Prod.snd).toFinset ∪
    (s.trades.flatMap fun p => p.1.priceQueries.map Prod.snd).toFinset

/-- `mentionedSet` is the finite-set form of bli-found's `MentionedBy`.
Source: [[bli-overlay-mandate]] D1
Kind: L
Fidelity: exact -/
lemma mem_mentionedSet_iff {n : ℕ} (s : Strategy n) (φ : Sentence) :
    φ ∈ mentionedSet s ↔ MentionedBy s φ := by
  unfold mentionedSet MentionedBy
  rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset, List.mem_map, List.mem_flatMap]
  constructor
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, hφ⟩)
    · exact Or.inl ⟨p.1, hp⟩
    · rw [List.mem_map] at hφ
      obtain ⟨q, hq, rfl⟩ := hφ
      exact Or.inr ⟨p, hp, q.1, hq⟩
  · rintro (⟨e, h⟩ | ⟨p, hp, k, hk⟩)
    · exact Or.inl ⟨(e, φ), h, rfl⟩
    · exact Or.inr ⟨p, hp, List.mem_map.mpr ⟨(k, φ), hk, rfl⟩⟩

/-- A traded sentence is mentioned.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mentionedBy_of_mem_trades {n : ℕ} {s : Strategy n} {p : EF × Sentence}
    (hp : p ∈ s.trades) : MentionedBy s p.2 :=
  Or.inl ⟨p.1, hp⟩

/-- A price-leaf sentence of a coefficient is mentioned.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mentionedBy_of_mem_priceQueries {n : ℕ} {s : Strategy n} {p : EF × Sentence}
    (hp : p ∈ s.trades) {k : ℕ} {φ : Sentence} (hq : (k, φ) ∈ p.1.priceQueries) :
    MentionedBy s φ :=
  Or.inr ⟨p, hp, k, hq⟩

/-- The support (traded sentences) sits inside the mentioned set.
Source: [[bli-overlay-mandate]] D1
Kind: L
Fidelity: exact -/
lemma support_subset_mentionedSet {n : ℕ} (s : Strategy n) : s.support ⊆ mentionedSet s := by
  intro φ hφ
  rw [mem_mentionedSet_iff]
  simp only [Strategy.support, Finset.mem_image, List.mem_toFinset] at hφ
  obtain ⟨p, hp, rfl⟩ := hφ
  exact mentionedBy_of_mem_trades hp

/-- Membership in the support in terms of `MentionedBy`'s first disjunct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_support_iff' {n : ℕ} (s : Strategy n) (φ : Sentence) :
    φ ∈ s.support ↔ ∃ e, (e, φ) ∈ s.trades := by
  simp only [Strategy.support, Finset.mem_image, List.mem_toFinset, Prod.exists]
  constructor
  · rintro ⟨e, ψ, h, rfl⟩; exact ⟨e, h⟩
  · rintro ⟨e, h⟩; exact ⟨e, φ, h, rfl⟩

/-! ## Price leaves and rank -/

namespace EF

/-- A price leaf `(k, φ)` of a feature has `k ≤` the feature's rank.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma le_rank_of_mem_priceQueries (e : LogicalInduction.EF) {k : ℕ} {φ : Sentence}
    (h : (k, φ) ∈ e.priceQueries) : k ≤ e.rank := by
  induction e with
  | price ψ m =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_singleton, Prod.mk.injEq] at h
      rw [h.1]
      simp
  | const q => simp [LogicalInduction.EF.priceQueries] at h
  | add a b iha ihb =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      rcases h with h | h
      · exact le_trans (iha h) (by simp)
      · exact le_trans (ihb h) (by simp)
  | mul a b iha ihb =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      rcases h with h | h
      · exact le_trans (iha h) (by simp)
      · exact le_trans (ihb h) (by simp)
  | max a b iha ihb =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      rcases h with h | h
      · exact le_trans (iha h) (by simp)
      · exact le_trans (ihb h) (by simp)
  | safeRecip a iha =>
      simp only [LogicalInduction.EF.priceQueries] at h
      exact le_trans (iha h) (by simp)
  | var i => simp [LogicalInduction.EF.priceQueries] at h
  | letE x body ihx ihbody =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      rcases h with h | h
      · exact le_trans (ihx h) (by simp)
      · exact le_trans (ihbody h) (by simp)

/-- **T1 (real, environment form).** A feature cannot distinguish two histories that agree on
every one of its price leaves, under any variable environment. The induction of FAF's
`EF.denoteWith_eq_of_eqUpTo` (`MarketMaker.lean:558`) with the leaf case taken from the
agreement hypothesis instead of the rank bound.
Source: [[bli-overlay-mandate]] T1
Kind: L
Fidelity: exact -/
lemma denoteWith_eq_of_eqOn_priceQueries (e : LogicalInduction.EF) (ρ : List ℝ) (V W : History)
    (h : ∀ q ∈ e.priceQueries, V q.1 q.2 = W q.1 q.2) :
    e.denoteWith ρ V = e.denoteWith ρ W := by
  induction e generalizing ρ with
  | price φ k => exact h (k, φ) (by simp [LogicalInduction.EF.priceQueries])
  | const q => rfl
  | add a b iha ihb =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp [LogicalInduction.EF.denoteWith, iha ρ (fun q hq => h q (Or.inl hq)),
        ihb ρ (fun q hq => h q (Or.inr hq))]
  | mul a b iha ihb =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp [LogicalInduction.EF.denoteWith, iha ρ (fun q hq => h q (Or.inl hq)),
        ihb ρ (fun q hq => h q (Or.inr hq))]
  | max a b iha ihb =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp [LogicalInduction.EF.denoteWith, iha ρ (fun q hq => h q (Or.inl hq)),
        ihb ρ (fun q hq => h q (Or.inr hq))]
  | safeRecip a iha =>
      simp only [LogicalInduction.EF.priceQueries] at h
      simp [LogicalInduction.EF.denoteWith, iha ρ h]
  | var i => rfl
  | letE x body ihx ihbody =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp only [LogicalInduction.EF.denoteWith]
      rw [ihx ρ (fun q hq => h q (Or.inl hq))]
      exact ihbody _ (fun q hq => h q (Or.inr hq))

/-- **T1 (rational, environment form).** The exact-rational twin of
`denoteWith_eq_of_eqOn_priceQueries`.
Source: [[bli-overlay-mandate]] T1
Kind: L
Fidelity: exact -/
lemma denoteRatWith_eq_of_eqOn_priceQueries (e : LogicalInduction.EF) (ρ : List ℚ)
    (Q R : ℕ → Sentence → ℚ)
    (h : ∀ q ∈ e.priceQueries, Q q.1 q.2 = R q.1 q.2) :
    e.denoteRatWith ρ Q = e.denoteRatWith ρ R := by
  induction e generalizing ρ with
  | price φ k => exact h (k, φ) (by simp [LogicalInduction.EF.priceQueries])
  | const q => rfl
  | add a b iha ihb =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp [LogicalInduction.EF.denoteRatWith, iha ρ (fun q hq => h q (Or.inl hq)),
        ihb ρ (fun q hq => h q (Or.inr hq))]
  | mul a b iha ihb =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp [LogicalInduction.EF.denoteRatWith, iha ρ (fun q hq => h q (Or.inl hq)),
        ihb ρ (fun q hq => h q (Or.inr hq))]
  | max a b iha ihb =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp [LogicalInduction.EF.denoteRatWith, iha ρ (fun q hq => h q (Or.inl hq)),
        ihb ρ (fun q hq => h q (Or.inr hq))]
  | safeRecip a iha =>
      simp only [LogicalInduction.EF.priceQueries] at h
      simp [LogicalInduction.EF.denoteRatWith, iha ρ h]
  | var i => rfl
  | letE x body ihx ihbody =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp only [LogicalInduction.EF.denoteRatWith]
      rw [ihx ρ (fun q hq => h q (Or.inl hq))]
      exact ihbody _ (fun q hq => h q (Or.inr hq))

end EF

/-! ## T1 at strategy level -/

namespace Strategy

/-- **T1 (strategy, real).** A day-`n` strategy's value in a world depends on the history only
through the cells `(k, φ)` with `k ≤ n` and `φ` mentioned by the strategy.
Source: [[bli-overlay-mandate]] T1; [[bli-program]] §3.3 (i) (the honest form of "indifferent
off the support": indifferent off the *mentioned* cells)
Kind: L
Fidelity: exact -/
lemma value_eq_of_eqOn_mentioned {n : ℕ} (T : Strategy n) (V W : History)
    (w : Sentence → ℝ) (h : ∀ φ, MentionedBy T φ → ∀ k ≤ n, V k φ = W k φ) :
    T.value V w = T.value W w := by
  unfold Strategy.value
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have h1 : p.1.denote V = p.1.denote W := by
    unfold LogicalInduction.EF.denote
    apply EF.denoteWith_eq_of_eqOn_priceQueries
    rintro ⟨k, ψ⟩ hq
    exact h ψ (mentionedBy_of_mem_priceQueries hp hq) k
      (le_trans (EF.le_rank_of_mem_priceQueries p.1 hq) (T.rank_le p hp))
  rw [h1, h p.2 (mentionedBy_of_mem_trades hp) n le_rfl]

/-- **T1 (strategy, rational).** The exact-rational twin of `value_eq_of_eqOn_mentioned`, for
`MarketMakerAccepts`' `marketValueRat`.
Source: [[bli-overlay-mandate]] T1
Kind: L
Fidelity: exact -/
lemma marketValueRat_eq_of_eqOn_mentioned {n : ℕ} (T : Strategy n) (Q R : ℕ → Sentence → ℚ)
    (w : Sentence → ℚ) (h : ∀ φ, MentionedBy T φ → ∀ k ≤ n, Q k φ = R k φ) :
    T.marketValueRat Q w = T.marketValueRat R w := by
  unfold Strategy.marketValueRat
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have h1 : p.1.denoteRat Q = p.1.denoteRat R := by
    unfold LogicalInduction.EF.denoteRat
    apply EF.denoteRatWith_eq_of_eqOn_priceQueries
    rintro ⟨k, ψ⟩ hq
    exact h ψ (mentionedBy_of_mem_priceQueries hp hq) k
      (le_trans (EF.le_rank_of_mem_priceQueries p.1 hq) (T.rank_le p hp))
  rw [h1, h p.2 (mentionedBy_of_mem_trades hp) n le_rfl]

end Strategy

end Cleanroom.Bli.BliOverlay.AttemptB
