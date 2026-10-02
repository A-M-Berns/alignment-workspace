import Cleanroom.Bli.BliOverlay.AttemptB.Mentioned

/-!
# `bli-overlay` (attempt B) · Subst: the past-substituted strategy and MarketMaker congruence

Angle B's device. `EF.substPast n Q e` rewrites every price leaf `price φ k` with `k < n` in
the feature `e` to the constant `Q k φ`, keeping the day-`n` leaves (the fixed-point
variables of the market maker); `Strategy.substPast Q T` does it coefficient-wise. The
substituted strategy evaluated on a history `V` is the original strategy evaluated on the
**past view** `pastView n Q V` — `Q` on days `< n`, `V` from day `n` on — exactly
(`Strategy.value_substPast`, `Strategy.marketValueRat_substPast`), its rank does not grow
(`EF.rank_substPast_le`) and its support is unchanged (`Strategy.support_substPast`).

`MarketMaker_congr` is the general congruence FAF's `MarketMaker` satisfies: two acceptance
predicates that agree pointwise give the same first accepted candidate (the same `Nat.find`).
With `marketMakerAccepts_substPast_iff` (the substituted strategy is accepted against `past`
iff the original is, when `Q` agrees with `past` on the mentioned past cells) it is what the
sanity identity `overlayQuote_zero_eq_liaQuote` (`Recursion.lean`) runs on. Infrastructure
(Kind L/D); nothing is a headline.
-/

namespace Cleanroom.Bli.BliOverlay.AttemptB

open LogicalInduction Cleanroom.Bli.BliFound

/-! ## Substitution on features -/

namespace EF

/-- **Past substitution.** Replace every price leaf of a day `< n` by the constant the table
`Q` holds there; leaves of day `≥ n` are kept.
Source: [[bli-overlay-mandate]] §Attempt angles (B)
Kind: D
Fidelity: exact -/
def substPast (n : ℕ) (Q : ℕ → Sentence → ℚ) : LogicalInduction.EF → LogicalInduction.EF
  | .price φ k => if k < n then .const (Q k φ) else .price φ k
  | .const q => .const q
  | .add a b => .add (substPast n Q a) (substPast n Q b)
  | .mul a b => .mul (substPast n Q a) (substPast n Q b)
  | .max a b => .max (substPast n Q a) (substPast n Q b)
  | .safeRecip a => .safeRecip (substPast n Q a)
  | .var i => .var i
  | .letE x body => .letE (substPast n Q x) (substPast n Q body)

/-- Substitution does not raise the rank (a constant has rank `0`; kept leaves keep theirs).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rank_substPast_le (n : ℕ) (Q : ℕ → Sentence → ℚ) (e : LogicalInduction.EF) :
    (substPast n Q e).rank ≤ e.rank := by
  induction e with
  | price φ k =>
      simp only [substPast]
      split_ifs <;> simp
  | const q => simp [substPast]
  | add a b iha ihb =>
      simp only [substPast, LogicalInduction.EF.rank_add]
      exact max_le_max iha ihb
  | mul a b iha ihb =>
      simp only [substPast, LogicalInduction.EF.rank_mul]
      exact max_le_max iha ihb
  | max a b iha ihb =>
      simp only [substPast, LogicalInduction.EF.rank_max]
      exact max_le_max iha ihb
  | safeRecip a iha => simpa [substPast] using iha
  | var i => simp [substPast]
  | letE x body ihx ihbody =>
      simp only [substPast, LogicalInduction.EF.rank_letE]
      exact max_le_max ihx ihbody

/-- **The past view** of a real history: the table `Q` (cast) on days `< n`, `V` from day `n` on.
Source: [[bli-overlay-mandate]] §Attempt angles (B)
Kind: D
Fidelity: exact -/
def pastView (n : ℕ) (Q : ℕ → Sentence → ℚ) (V : History) : History :=
  fun k φ => if k < n then (Q k φ : ℝ) else V k φ

/-- The rational past view: `Q` on days `< n`, `R` from day `n` on.
Source: [[bli-overlay-mandate]] §Attempt angles (B)
Kind: D
Fidelity: exact -/
def pastViewRat (n : ℕ) (Q R : ℕ → Sentence → ℚ) : ℕ → Sentence → ℚ :=
  fun k φ => if k < n then Q k φ else R k φ

/-- Below `n` the past view reads `Q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pastView_of_lt {n k : ℕ} (h : k < n) (Q : ℕ → Sentence → ℚ) (V : History)
    (φ : Sentence) : pastView n Q V k φ = (Q k φ : ℝ) := by
  simp [pastView, h]

/-- From `n` on the past view reads `V`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pastView_of_not_lt {n k : ℕ} (h : ¬ k < n) (Q : ℕ → Sentence → ℚ) (V : History)
    (φ : Sentence) : pastView n Q V k φ = V k φ := by
  simp [pastView, h]

/-- On day `n` the past view reads `V`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pastView_self (n : ℕ) (Q : ℕ → Sentence → ℚ) (V : History) (φ : Sentence) :
    pastView n Q V n φ = V n φ := by
  simp [pastView]

/-- Below `n` the rational past view reads `Q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pastViewRat_of_lt {n k : ℕ} (h : k < n) (Q R : ℕ → Sentence → ℚ) (φ : Sentence) :
    pastViewRat n Q R k φ = Q k φ := by
  simp [pastViewRat, h]

/-- From `n` on the rational past view reads `R`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pastViewRat_of_not_lt {n k : ℕ} (h : ¬ k < n) (Q R : ℕ → Sentence → ℚ) (φ : Sentence) :
    pastViewRat n Q R k φ = R k φ := by
  simp [pastViewRat, h]

/-- On day `n` the rational past view reads `R`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pastViewRat_self (n : ℕ) (Q R : ℕ → Sentence → ℚ) (φ : Sentence) :
    pastViewRat n Q R n φ = R n φ := by
  simp [pastViewRat]

/-- **The substitution lemma (real).** The substituted feature on `V` is the feature on the
past view of `V`, under any environment.
Source: [[bli-overlay-mandate]] §Attempt angles (B), `denoteWith_substPast`
Kind: L
Fidelity: stronger: stated as an exact equality with the past view (no agreement hypothesis) -/
lemma denoteWith_substPast (n : ℕ) (Q : ℕ → Sentence → ℚ) (e : LogicalInduction.EF)
    (ρ : List ℝ) (V : History) :
    (substPast n Q e).denoteWith ρ V = e.denoteWith ρ (pastView n Q V) := by
  induction e generalizing ρ with
  | price φ k =>
      simp only [substPast]
      split_ifs with h <;> simp [LogicalInduction.EF.denoteWith, pastView, h]
  | const q => rfl
  | add a b iha ihb => simp [substPast, LogicalInduction.EF.denoteWith, iha, ihb]
  | mul a b iha ihb => simp [substPast, LogicalInduction.EF.denoteWith, iha, ihb]
  | max a b iha ihb => simp [substPast, LogicalInduction.EF.denoteWith, iha, ihb]
  | safeRecip a iha => simp [substPast, LogicalInduction.EF.denoteWith, iha]
  | var i => rfl
  | letE x body ihx ihbody =>
      simp only [substPast, LogicalInduction.EF.denoteWith]
      rw [ihx ρ, ihbody]

/-- **The substitution lemma (rational).**
Source: [[bli-overlay-mandate]] §Attempt angles (B)
Kind: L
Fidelity: exact -/
lemma denoteRatWith_substPast (n : ℕ) (Q : ℕ → Sentence → ℚ) (e : LogicalInduction.EF)
    (ρ : List ℚ) (R : ℕ → Sentence → ℚ) :
    (substPast n Q e).denoteRatWith ρ R = e.denoteRatWith ρ (pastViewRat n Q R) := by
  induction e generalizing ρ with
  | price φ k =>
      simp only [substPast]
      split_ifs with h <;> simp [LogicalInduction.EF.denoteRatWith, pastViewRat, h]
  | const q => rfl
  | add a b iha ihb => simp [substPast, LogicalInduction.EF.denoteRatWith, iha, ihb]
  | mul a b iha ihb => simp [substPast, LogicalInduction.EF.denoteRatWith, iha, ihb]
  | max a b iha ihb => simp [substPast, LogicalInduction.EF.denoteRatWith, iha, ihb]
  | safeRecip a iha => simp [substPast, LogicalInduction.EF.denoteRatWith, iha]
  | var i => rfl
  | letE x body ihx ihbody =>
      simp only [substPast, LogicalInduction.EF.denoteRatWith]
      rw [ihx ρ, ihbody]

/-- A price leaf of the substituted feature is a day-`≥ n` leaf of the original.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_priceQueries_substPast {n : ℕ} {Q : ℕ → Sentence → ℚ} {e : LogicalInduction.EF}
    {k : ℕ} {φ : Sentence} (h : (k, φ) ∈ (substPast n Q e).priceQueries) :
    (k, φ) ∈ e.priceQueries ∧ ¬ k < n := by
  induction e with
  | price ψ m =>
      simp only [substPast] at h
      split_ifs at h with hm
      · simp [LogicalInduction.EF.priceQueries] at h
      · simp only [LogicalInduction.EF.priceQueries, List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp [LogicalInduction.EF.priceQueries], hm⟩
  | const q => simp [substPast, LogicalInduction.EF.priceQueries] at h
  | add a b iha ihb =>
      simp only [substPast, LogicalInduction.EF.priceQueries, List.mem_append] at h ⊢
      rcases h with h | h
      · exact ⟨Or.inl (iha h).1, (iha h).2⟩
      · exact ⟨Or.inr (ihb h).1, (ihb h).2⟩
  | mul a b iha ihb =>
      simp only [substPast, LogicalInduction.EF.priceQueries, List.mem_append] at h ⊢
      rcases h with h | h
      · exact ⟨Or.inl (iha h).1, (iha h).2⟩
      · exact ⟨Or.inr (ihb h).1, (ihb h).2⟩
  | max a b iha ihb =>
      simp only [substPast, LogicalInduction.EF.priceQueries, List.mem_append] at h ⊢
      rcases h with h | h
      · exact ⟨Or.inl (iha h).1, (iha h).2⟩
      · exact ⟨Or.inr (ihb h).1, (ihb h).2⟩
  | safeRecip a iha =>
      simp only [substPast, LogicalInduction.EF.priceQueries] at h ⊢
      exact iha h
  | var i => simp [substPast, LogicalInduction.EF.priceQueries] at h
  | letE x body ihx ihbody =>
      simp only [substPast, LogicalInduction.EF.priceQueries, List.mem_append] at h ⊢
      rcases h with h | h
      · exact ⟨Or.inl (ihx h).1, (ihx h).2⟩
      · exact ⟨Or.inr (ihbody h).1, (ihbody h).2⟩

end EF

/-! ## Substitution on strategies -/

namespace Strategy

/-- **The past-substituted strategy**: every coefficient's day-`< n` price leaves replaced by
the constants `Q` holds there; trades and traded sentences unchanged.
Source: [[bli-overlay-mandate]] §Attempt angles (B)
Kind: D
Fidelity: exact -/
def substPast {n : ℕ} (Q : ℕ → Sentence → ℚ) (T : Strategy n) : Strategy n where
  trades := T.trades.map fun p => (EF.substPast n Q p.1, p.2)
  rank_le := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact le_trans (EF.rank_substPast_le n Q q.1) (T.rank_le q hq)

/-- The trade list of the substituted strategy, unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma trades_substPast {n : ℕ} (Q : ℕ → Sentence → ℚ) (T : Strategy n) :
    (Strategy.substPast Q T).trades = T.trades.map fun p => (EF.substPast n Q p.1, p.2) := rfl

/-- Substitution keeps the support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma support_substPast {n : ℕ} (Q : ℕ → Sentence → ℚ) (T : Strategy n) :
    (Strategy.substPast Q T).support = T.support := by
  unfold Strategy.support
  rw [trades_substPast, List.toFinset_map, Finset.image_image]
  rfl

/-- Substitution shrinks the mentioned set (kept leaves are leaves of the original).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mentionedBy_substPast {n : ℕ} {Q : ℕ → Sentence → ℚ} {T : Strategy n} {φ : Sentence}
    (h : MentionedBy (Strategy.substPast Q T) φ) : MentionedBy T φ := by
  rcases h with ⟨e, he⟩ | ⟨p, hp, k, hk⟩
  · rw [trades_substPast, List.mem_map] at he
    obtain ⟨q, hq, hq'⟩ := he
    have : q.2 = φ := (Prod.mk.inj hq').2
    exact Or.inl ⟨q.1, by rw [← this]; exact hq⟩
  · rw [trades_substPast, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact Or.inr ⟨q, hq, k, (EF.mem_priceQueries_substPast hk).1⟩

/-- **Value of the substituted strategy (real):** the original strategy on the past view.
Source: [[bli-overlay-mandate]] §Attempt angles (B)
Kind: L
Fidelity: exact -/
lemma value_substPast {n : ℕ} (Q : ℕ → Sentence → ℚ) (T : Strategy n) (V : History)
    (w : Sentence → ℝ) :
    (Strategy.substPast Q T).value V w = T.value (EF.pastView n Q V) w := by
  unfold Strategy.value
  rw [trades_substPast, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply]
  unfold LogicalInduction.EF.denote
  rw [EF.denoteWith_substPast, EF.pastView_self]

/-- **Value of the substituted strategy (rational).**
Source: [[bli-overlay-mandate]] §Attempt angles (B)
Kind: L
Fidelity: exact -/
lemma marketValueRat_substPast {n : ℕ} (Q : ℕ → Sentence → ℚ) (T : Strategy n)
    (R : ℕ → Sentence → ℚ) (w : Sentence → ℚ) :
    (Strategy.substPast Q T).marketValueRat R w = T.marketValueRat (EF.pastViewRat n Q R) w := by
  unfold Strategy.marketValueRat
  rw [trades_substPast, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply]
  unfold LogicalInduction.EF.denoteRat
  rw [EF.denoteRatWith_substPast, EF.pastViewRat_self]

end Strategy

/-! ## Acceptance transport and MarketMaker congruence -/

/-- A support bit table transported along an equality of supports is the same table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma supportBitWorldRat_congr {n : ℕ} {S T : Strategy n} (hs : S.support = T.support)
    (b : ↥S.support → Bool) :
    supportBitWorldRat T (fun ψ => b ⟨ψ.1, by rw [hs]; exact ψ.2⟩) = supportBitWorldRat S b := by
  funext φ
  unfold supportBitWorldRat
  by_cases hφ : φ ∈ S.support
  · have hφ' : φ ∈ T.support := by rw [← hs]; exact hφ
    rw [dif_pos hφ, dif_pos hφ']
  · have hφ' : φ ∉ T.support := by rw [← hs]; exact hφ
    rw [dif_neg hφ, dif_neg hφ']

/-- Acceptance transports between two strategies with the same support and the same exact
rational value on the candidate histories.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma MarketMakerAccepts.of_support_eq {n : ℕ} {T T' : Strategy n} (hs : T'.support = T.support)
    {past past' : List RationalBeliefState} {ε : ℚ} {B : RationalBeliefState}
    (hval : ∀ w : Sentence → ℚ,
      T'.marketValueRat (candidateRationalHistory past' n B) w =
        T.marketValueRat (candidateRationalHistory past n B) w)
    (h : MarketMakerAccepts T past ε B) : MarketMakerAccepts T' past' ε B := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [hs]; exact h1, fun b' => ?_⟩
  rw [hval, ← supportBitWorldRat_congr hs b']
  exact h2 _

/-- **Acceptance of the substituted strategy.** Against a past `past` with which `Q` agrees on
every past cell the strategy mentions, the substituted strategy is accepted iff the original
is. This is the wrong-market guard in acceptance form: the substitution is invisible to the
market maker exactly when the substituted constants are the past it is checking against.
Source: [[bli-overlay-mandate]] §Attempt angles (B); T4 traps (i)
Kind: L
Fidelity: exact -/
lemma marketMakerAccepts_substPast_iff {n : ℕ} (T : Strategy n) (Q : ℕ → Sentence → ℚ)
    (past : List RationalBeliefState) (ε : ℚ) (B : RationalBeliefState)
    (hQ : ∀ φ, MentionedBy T φ → ∀ k < n, Q k φ = rationalHistory past k φ) :
    MarketMakerAccepts (Strategy.substPast Q T) past ε B ↔ MarketMakerAccepts T past ε B := by
  have hval : ∀ w : Sentence → ℚ,
      (Strategy.substPast Q T).marketValueRat (candidateRationalHistory past n B) w =
        T.marketValueRat (candidateRationalHistory past n B) w := by
    intro w
    rw [Strategy.marketValueRat_substPast]
    apply Strategy.marketValueRat_eq_of_eqOn_mentioned
    intro φ hφ k hk
    rcases lt_or_eq_of_le hk with hlt | rfl
    · rw [EF.pastViewRat_of_lt hlt, hQ φ hφ k hlt]
      simp only [candidateRationalHistory, Function.update_of_ne hlt.ne]
    · rw [EF.pastViewRat_self]
  constructor
  · exact MarketMakerAccepts.of_support_eq (Strategy.support_substPast Q T).symm
      (fun w => (hval w).symm)
  · exact MarketMakerAccepts.of_support_eq (Strategy.support_substPast Q T) hval

/-- **MarketMaker congruence.** Two invocations whose acceptance predicates agree on every
candidate state return the same state: `MarketMaker` is the first accepted candidate in a
fixed enumeration, so it is a function of the acceptance predicate alone.
Source: [[bli-overlay-mandate]] T4 (v) (`MarketMaker_eq_of_eqOn_mentioned`'s engine)
Kind: L
Fidelity: stronger: stated for arbitrary pointwise-equivalent acceptance predicates -/
lemma MarketMaker_congr {n : ℕ} {T T' : Strategy n} {past past' : List RationalBeliefState}
    {ε : ℚ} (hε : 0 < ε)
    (h : ∀ B, MarketMakerAccepts T past ε B ↔ MarketMakerAccepts T' past' ε B) :
    MarketMaker T past ε hε = MarketMaker T' past' ε hε := by
  have hidx : marketMakerIndex T past ε hε = marketMakerIndex T' past' ε hε := by
    unfold marketMakerIndex
    apply le_antisymm
    · obtain ⟨B, hB, hacc⟩ := Nat.find_spec (exists_marketMakerCandidateAccepts T' past' hε)
      exact Nat.find_min' _ ⟨B, hB, (h B).mpr hacc⟩
    · obtain ⟨B, hB, hacc⟩ := Nat.find_spec (exists_marketMakerCandidateAccepts T past hε)
      exact Nat.find_min' _ ⟨B, hB, (h B).mp hacc⟩
  have h1 := MarketMaker_candidate T past ε hε
  have h2 := MarketMaker_candidate T' past' ε hε
  rw [hidx, h2] at h1
  exact (Option.some.inj h1).symm

end Cleanroom.Bli.BliOverlay.AttemptB
