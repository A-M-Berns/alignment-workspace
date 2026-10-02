import Cleanroom.Bli.BliLeak.Leak
import Cleanroom.Bli.BliFound.Bridge

/-!
# `bli-leak` · Neighbour: a trader that never reads a leak is unaffected (L3.7)

The surviving neighbour of the refuted transfer at this package's level: for a trader none of
whose strategies *mentions* a leak atom (`bli-found`'s `MentionedBy`: traded, or read in a `price`
leaf), the net worth on the leak market equals the net worth on `Q` in every world on every day
(`netWorth_leakHistory_eq`), so it exploits the leak market iff it exploits `Q`
(`exploits_leakHistory_iff`). The criterion-level survivors — every e.c. trader, for an
*expressible* overlay (`bli-transfer` L1) or for the restricted class that never reads a price
large on the day read (L4) — are `bli-transfer`'s; cited, not proved.

The engine is the congruence of `EF.denoteWith` on histories agreeing at the feature's
`priceQueries` (`denoteWith_congr_of_priceQueries`), which FAF lacks (an FAF API request).
-/

namespace Cleanroom.Bli.BliLeak

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound

/-! ## Feature congruence on the queried cells -/

/-- **Congruence of `denoteWith` on the queried cells**: two histories agreeing at every
`(day, sentence)` in `e.priceQueries` give `e` the same value, under every environment.
Source: mandate L3.7 (`EF.denote` congruence; FAF API request)
Kind: L
Fidelity: exact -/
theorem denoteWith_congr_of_priceQueries (e : EF) {V V' : History}
    (h : ∀ q ∈ e.priceQueries, V q.1 q.2 = V' q.1 q.2) :
    ∀ ρ, e.denoteWith ρ V = e.denoteWith ρ V' := by
  induction e with
  | price φ n => intro ρ; exact h (n, φ) (by simp [EF.priceQueries])
  | const q => intro ρ; rfl
  | add a b iha ihb =>
      intro ρ
      simp only [EF.denoteWith_add]
      rw [iha (fun q hq => h q (by simp [EF.priceQueries, hq])) ρ,
        ihb (fun q hq => h q (by simp [EF.priceQueries, hq])) ρ]
  | mul a b iha ihb =>
      intro ρ
      simp only [EF.denoteWith_mul]
      rw [iha (fun q hq => h q (by simp [EF.priceQueries, hq])) ρ,
        ihb (fun q hq => h q (by simp [EF.priceQueries, hq])) ρ]
  | max a b iha ihb =>
      intro ρ
      simp only [EF.denoteWith_max]
      rw [iha (fun q hq => h q (by simp [EF.priceQueries, hq])) ρ,
        ihb (fun q hq => h q (by simp [EF.priceQueries, hq])) ρ]
  | safeRecip a iha =>
      intro ρ
      simp only [EF.denoteWith_safeRecip]
      rw [iha (fun q hq => h q (by simp [EF.priceQueries, hq])) ρ]
  | var i => intro ρ; rfl
  | letE x body ihx ihbody =>
      intro ρ
      simp only [EF.denoteWith_letE]
      rw [ihx (fun q hq => h q (by simp [EF.priceQueries, hq])) ρ,
        ihbody (fun q hq => h q (by simp [EF.priceQueries, hq])) _]

/-- `denote` congruence on the queried cells.
Source: mandate L3.7
Kind: L
Fidelity: exact -/
theorem denote_congr_of_priceQueries (e : EF) {V V' : History}
    (h : ∀ q ∈ e.priceQueries, V q.1 q.2 = V' q.1 q.2) : e.denote V = e.denote V' :=
  denoteWith_congr_of_priceQueries e h []

variable {Q : History} {ℓ : ℕ → Sentence} {e : ℕ → ℕ} {t : ℕ → ℝ}

/-- A strategy mentioning no leak atom has the same value on the leak market as on `Q`, in every
world.
Source: mandate L3.7
Kind: L
Fidelity: exact -/
theorem value_leakHistory_eq {n : ℕ} (s : Strategy n)
    (h : ∀ φ, MentionedBy s φ → ∀ m, φ ≠ ℓ m) (w : Sentence → ℝ) :
    s.value (leakHistory Q ℓ e t) w = s.value Q w := by
  unfold Strategy.value
  congr 1
  apply List.map_congr_left
  intro p hp
  have h1 : p.1.denote (leakHistory Q ℓ e t) = p.1.denote Q :=
    denote_congr_of_priceQueries p.1 (fun q hq =>
      leakHistory_eq_of_ne (h q.2 (Or.inr ⟨p, hp, q.1, by simpa using hq⟩)) q.1)
  have h2 : leakHistory Q ℓ e t n p.2 = Q n p.2 :=
    leakHistory_eq_of_ne (h p.2 (Or.inl ⟨p.1, by simpa using hp⟩)) n
  rw [h1, h2]

/-- **L3.7. A trader that never reads a leak is unaffected**: its net worth on the leak market is
its net worth on `Q`, in every world on every day.
Source: mandate L3.7 (`netWorth_leakHistory_eq`); [[bli-program]] §3.1 (the congruence idea)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem netWorth_leakHistory_eq (Tr : Trader)
    (hTr : ∀ n φ, MentionedBy (Tr.strat n) φ → ∀ m, φ ≠ ℓ m) :
    ∀ (v : PCWorld) n, Tr.netWorth (leakHistory Q ℓ e t) v n = Tr.netWorth Q v n := by
  intro v n
  unfold Trader.netWorth
  apply Finset.sum_congr rfl
  intro i _
  exact value_leakHistory_eq _ (hTr i) _

/-- The plausible assessments of such a trader are the same on both markets.
Source: mandate L3.7
Kind: L
Fidelity: exact -/
theorem plausibleAssessments_leakHistory_eq (Tr : Trader)
    (hTr : ∀ n φ, MentionedBy (Tr.strat n) φ → ∀ m, φ ≠ ℓ m) (DP : DeductiveProcess) :
    Tr.plausibleAssessments (leakHistory Q ℓ e t) DP = Tr.plausibleAssessments Q DP := by
  ext y
  simp only [Trader.plausibleAssessments, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, v, hv, rfl⟩
    exact ⟨n, v, hv, netWorth_leakHistory_eq Tr hTr v n⟩
  · rintro ⟨n, v, hv, rfl⟩
    exact ⟨n, v, hv, (netWorth_leakHistory_eq Tr hTr v n).symm⟩

/-- **L3.7, exploitation form**: a trader that never reads a leak exploits the leak market iff it
exploits `Q`. The rule-3 survivor at this package's level (the criterion-level survivors are
`bli-transfer`'s L1 and L4).
Source: mandate L3.7 (`exploits_leakHistory_iff`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem exploits_leakHistory_iff (Tr : Trader)
    (hTr : ∀ n φ, MentionedBy (Tr.strat n) φ → ∀ m, φ ≠ ℓ m) (DP : DeductiveProcess) :
    Tr.Exploits (leakHistory Q ℓ e t) DP ↔ Tr.Exploits Q DP := by
  unfold Trader.Exploits
  rw [plausibleAssessments_leakHistory_eq Tr hTr DP]

end Cleanroom.Bli.BliLeak
