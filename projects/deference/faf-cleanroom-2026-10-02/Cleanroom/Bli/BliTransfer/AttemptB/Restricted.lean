import Cleanroom.Bli.BliTransfer.AttemptB.Transfer

/-!
# `bli-transfer` · attempt B · Restricted: the restricted-class transfer (T2), disclosed `(c)`

**Claim (bli-slides-002, reading "traders never read large prices"; [[bli-program]] `C:I4`).**
If `Q` is a logical inductor, no `RestrictedEC` trader exploits `overlay Q ov`, for **every**
`ov` with prices in `[0, 1]` — no expression map, no certificate: the rewritten trader is the
trader itself. Every leaf reads a price small on the day read, which the overlay copies from
`Q` (`denoteWith_eq_of_leaves_agree`); the bridge lemma makes every *traded* sentence small
from some day `N` on, so settlement agrees too; days `< N` are bounded by the magnitudes
(`netWorth_difference_le_of_eventually_eq`); `of_boundedDifference` finishes.

**This is not the criterion.** `IsLogicalInductor` quantifies over `EfficientlyComputable`,
and `RestrictedEC` is a strictly smaller class (`Witnesses.lean`: `largeReader` is e.c. and
not restricted). The ledger row says "for the restricted class"; kind `C`, hypothesis `(c)`:
the class.

Sources: bli-slides-002; [[bli-program]] §3.2(a), `C:I4`; mandate T2.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptB

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

namespace Strategy

/-- **Two markets agreeing on every leaf and every settlement of a strategy give it the same
value.**
Source: [[bli-program]] §3.1 (`denote_eq_of_agree_on_leaves`, strategy level); mandate T2
Kind: L
Fidelity: exact -/
lemma value_eq_of_agree {P Q : History} {n : ℕ} (T : LogicalInduction.Strategy n)
    (w : Sentence → ℝ)
    (h : ∀ p ∈ T.trades, (∀ q ∈ p.1.priceQueries, P q.1 q.2 = Q q.1 q.2) ∧ P n p.2 = Q n p.2) :
    T.value P w = T.value Q w := by
  simp only [LogicalInduction.Strategy.value]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [LogicalInduction.EF.denote]
  rw [EF.denoteWith_eq_of_leaves_agree p.1 (h p hp).1 [], (h p hp).2]

end Strategy

/-- **Restricted-class transfer** (T2): for the restricted class `RestrictedEC` — **not the
criterion** — no restricted trader exploits the overlay of a logical inductor, for every
re-pricing `ov` of the large sentences with values in `[0, 1]`. The trader is its own rewrite:
its leaves read only day-small prices, which the overlay copies from `Q`; its traded sentences
are day-small from the bridge day on; the finitely many earlier days are bounded by magnitude.
Source: bli-slides-002 (reading "traders never read large prices"); [[bli-program]] `C:I4`; mandate T2
Kind: C
Fidelity: weaker: for the class `RestrictedEC`, not for `EfficientlyComputable`
Hyps: (a) `hQ`; (a) `hov`; (c) `hTr` — the class `RestrictedEC`, strictly smaller than the
criterion's (`largeReader_not_restrictedEC`) -/
theorem restrictedEC_not_exploits_overlay (Q : History) (DP : DeductiveProcess)
    [hQ : IsLogicalInductor Q DP] (ov : ℕ → Sentence → ℚ)
    (hov : ∀ k ψ, 0 ≤ ov k ψ ∧ ov k ψ ≤ 1) (Tr : Trader) (hTr : RestrictedEC Tr) :
    ¬ Tr.Exploits (overlay Q ov) DP := by
  intro hex
  obtain ⟨N, hN⟩ := bridge_lemma Tr hTr.1
  refine hQ.noExploit Tr hTr.1 (hex.of_boundedDifference
    (∑ d ∈ Finset.range N, ((Tr.strat d).magnitude (overlay Q ov) + (Tr.strat d).magnitude Q))
    (fun n v _ => ?_))
  refine netWorth_difference_le_of_eventually_eq Tr Tr (overlay Q ov) Q N
    (overlay_mem_Icc (fun k ψ => hQ.price_mem_Icc k ψ) hov) (fun d φ => hQ.price_mem_Icc d φ)
    v (fun d hd => ?_) n
  exact Strategy.value_eq_of_agree (Tr.strat d) v.payout (fun p hp =>
    ⟨fun q hq => overlay_small (hTr.2 d p hp q hq),
     overlay_small (hN d hd p.2 (Or.inl ⟨p.1, hp⟩))⟩)

/-- A restricted trader is unchanged by any splice that fires only on large sentences: its
leaves are all small on their day, so no leaf is rewritten. (What makes T2 a special case of
T1's accounting with the identity rewrite.)
Source: mandate T2 ("`Tr' = Tr`")
Kind: L
Fidelity: n/a -/
lemma RestrictedEC.spliceOn_eq (Tr : Trader) (hTr : RestrictedEC Tr)
    (expr : ℕ → Sentence → Option LogicalInduction.EF)
    (hr : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k)
    (hlarge : ∀ k ψ, SmallOn k ψ → expr k ψ = none) :
    Trader.spliceOn expr hr Tr = Tr := by
  apply LogicalInduction.Trader.ext
  funext n
  apply LogicalInduction.Strategy.ext
  simp only [Trader.spliceOn_strat, Strategy.spliceOn_trades]
  conv_rhs => rw [← List.map_id (Tr.strat n).trades]
  apply List.map_congr_left
  intro p hp
  have key : ∀ e : LogicalInduction.EF, (∀ q ∈ e.priceQueries, SmallOn q.1 q.2) →
      EF.spliceOn expr e = e := by
    intro e
    induction e with
    | price φ k =>
        intro h
        have := h (k, φ) (by simp [LogicalInduction.EF.priceQueries])
        simp [hlarge k φ this]
    | const q => intro _; rfl
    | add a b iha ihb =>
        intro h
        simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
        simp [iha (fun q hq => h q (Or.inl hq)), ihb (fun q hq => h q (Or.inr hq))]
    | mul a b iha ihb =>
        intro h
        simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
        simp [iha (fun q hq => h q (Or.inl hq)), ihb (fun q hq => h q (Or.inr hq))]
    | max a b iha ihb =>
        intro h
        simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
        simp [iha (fun q hq => h q (Or.inl hq)), ihb (fun q hq => h q (Or.inr hq))]
    | safeRecip a iha =>
        intro h
        simp only [LogicalInduction.EF.priceQueries] at h
        simp [iha h]
    | var i => intro _; rfl
    | letE x b ihx ihb =>
        intro h
        simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
        simp [ihx (fun q hq => h q (Or.inl hq)), ihb (fun q hq => h q (Or.inr hq))]
  simp only [id]
  rw [key p.1 (hTr.2 n p hp)]

end Cleanroom.Bli.BliTransfer.AttemptB
