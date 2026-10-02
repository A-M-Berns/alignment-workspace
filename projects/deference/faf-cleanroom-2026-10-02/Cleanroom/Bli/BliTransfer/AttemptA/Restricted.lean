import Cleanroom.Bli.BliTransfer.AttemptA.Transfer

/-!
# `bli-transfer` (attempt A) · Restricted: the restricted-class transfer, a disclosed `(c)` (T2)

bli-slides-002's first reading — "traders never read large prices" — as a theorem about the class
it names: no `RestrictedEC` trader (`Defs.lean`: efficiently computable, every price leaf on every
day reads a sentence small on the day read) exploits `overlay Q ov`, for **every** `[0,1]`-valued
re-pricing `ov` — no expression map, no certificate. The rewrite is the identity: every leaf reads a
small price, which the overlay leaves alone (`Strategy.value_congr_of_small`); the bridge lemma
handles the settlement term from some day on; the generic finite-prefix accounting finishes.

**This is not the criterion.** `IsLogicalInductor` quantifies over `EfficientlyComputable`, of
which `RestrictedEC` is a proper subclass (`Witnesses.restrictedEC_separation`), so no
`IsLogicalInductor` conclusion is stated here; the theorem that makes the headline true under the
real quantifier is T1 (`Headline.lean`).

Sources: bli-slides-002 (reading "traders never read large prices"); [[bli-program]] `C:I4`;
mandate T2.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-- The denotation depends only on the prices at the feature's own price queries.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EF.denoteWith_congr_prices (e : EF) (V V' : History)
    (h : ∀ p ∈ e.priceQueries, V p.1 p.2 = V' p.1 p.2) :
    ∀ ρ : List ℝ, e.denoteWith ρ V = e.denoteWith ρ V' := by
  induction e with
  | price φ n =>
      intro ρ
      simp only [EF.denoteWith]
      exact h (n, φ) (by simp [EF.priceQueries])
  | const q => intro ρ; rfl
  | add a b iha ihb =>
      intro ρ
      simp only [EF.priceQueries] at h
      simp [EF.denoteWith, iha (fun p hp => h p (List.mem_append_left _ hp)) ρ,
        ihb (fun p hp => h p (List.mem_append_right _ hp)) ρ]
  | mul a b iha ihb =>
      intro ρ
      simp only [EF.priceQueries] at h
      simp [EF.denoteWith, iha (fun p hp => h p (List.mem_append_left _ hp)) ρ,
        ihb (fun p hp => h p (List.mem_append_right _ hp)) ρ]
  | max a b iha ihb =>
      intro ρ
      simp only [EF.priceQueries] at h
      simp [EF.denoteWith, iha (fun p hp => h p (List.mem_append_left _ hp)) ρ,
        ihb (fun p hp => h p (List.mem_append_right _ hp)) ρ]
  | safeRecip a iha =>
      intro ρ
      simp only [EF.priceQueries] at h
      simp [EF.denoteWith, iha h ρ]
  | var i => intro ρ; rfl
  | letE x b ihx ihb =>
      intro ρ
      simp only [EF.priceQueries] at h
      simp only [EF.denoteWith]
      rw [ihx (fun p hp => h p (List.mem_append_left _ hp)) ρ,
        ihb (fun p hp => h p (List.mem_append_right _ hp))]

/-- A strategy whose leaves all read small prices and whose traded sentences are small on its
day has the same value on the overlay and on `Q` — the identity rewrite's value law.
Source: mandate T2 ("`Tr' = Tr`, `spliceOn_value` degenerates")
Kind: L
Fidelity: exact -/
lemma Strategy.value_congr_of_small {n : ℕ} (T : Strategy n) (Q : History)
    (ov : ℕ → Sentence → ℚ) (w : Sentence → ℝ)
    (hleaves : ∀ p ∈ T.trades, ∀ q ∈ p.1.priceQueries, SmallOn q.1 q.2)
    (hsettle : ∀ p ∈ T.trades, SmallOn n p.2) :
    T.value (overlay Q ov) w = T.value Q w := by
  simp only [Strategy.value]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [EF.denote, EF.denote, EF.denoteWith_congr_prices p.1 (overlay Q ov) Q
    (fun q hq => overlay_small (hleaves p hp q hq)) [], overlay_small (hsettle p hp)]

/-- **Restricted-class transfer (L4) — for the restricted class `RestrictedEC`, not the
criterion.** If `Q` is a logical inductor, no `RestrictedEC` trader exploits `overlay Q ov`, for
every `[0,1]`-valued `ov`: the trader is its own rewrite, every leaf reads a small price the
overlay leaves alone, the bridge lemma makes its traded sentences small from some day on, and
the finite-prefix accounting transports exploitation to `Q`.
Source: bli-slides-002 (reading "traders never read large prices"); [[bli-program]] `C:I4`; mandate T2
Kind: C
Fidelity: variant: (c) quantified over `RestrictedEC`, a proper subclass of `EfficientlyComputable`
Hyps: (a) `hQ`, `hov`; (c) `hTr : RestrictedEC Tr` — the restricted class, not the criterion's class -/
theorem restrictedEC_not_exploits_overlay (Q : History) (DP : DeductiveProcess)
    [hQ : IsLogicalInductor Q DP] (ov : ℕ → Sentence → ℚ)
    (hov : ∀ k ψ, 0 ≤ ov k ψ ∧ ov k ψ ≤ 1) (Tr : Trader) (hTr : RestrictedEC Tr) :
    ¬ Tr.Exploits (overlay Q ov) DP := by
  intro hexp
  obtain ⟨N, hN⟩ := exists_settle_day Tr hTr.1
  have hQr : ∀ k ψ, 0 ≤ Q k ψ ∧ Q k ψ ≤ 1 := fun k ψ => hQ.marketComputable.1 k ψ
  refine hQ.noExploit Tr hTr.1 (Trader.Exploits.of_boundedDifference hexp
    (∑ d ∈ Finset.range N, ((Tr.strat d).magnitude (overlay Q ov) + (Tr.strat d).magnitude Q))
    (fun n v _ => ?_))
  exact Trader.netWorth_difference_le_of_tail_eq Tr Tr (overlay Q ov) Q
    (overlay_range hov hQr) hQr N v
    (fun day hge => Strategy.value_congr_of_small (Tr.strat day) Q ov v.payout (hTr.2 day)
      (hN day hge)) n

end Cleanroom.Bli.BliTransfer.AttemptA
