import Cleanroom.Bli.BliTransfer.AttemptA.Transfer

/-!
# `bli-transfer` (attempt A) · Clamp: the clamped re-pricing (T3, partial)

L5's clamped market `clamp Q` (`Defs.lean`: every day-`k` price pulled into `[ε_k, 1 − ε_k]`,
`ε_k = 2^{-2^k}`) is a *perturbation* of `Q`, not an overlay: the rewrite replaces **every** leaf
`price φ k` by `letE (price φ k) (clampE k)`, so the rewritten trader reads on `Q` exactly what the
original reads on `clamp Q` (`clampSpec`: `clampE k` reads the bound price as `var 0`, which is why
`Splice.SpliceSpec` allows one free variable). The residual is the settlement term:
`|clamp Q n φ − Q n φ| ≤ ε_n` (`Defs.abs_clamp_sub_le`), so the day-`n` value gap is at most
`magnitude · ε_n` (`Strategy.clamp_value_sub_le`) and net worths differ by the partial sums of
`magnitude_n · ε_n` (`Trader.clamp_netWorth_sub_le`).

**What is proved here and what is not.** The headline `clamp_isLogicalInductor_of` is
conditional on three named hypotheses, each the mandate's own next step, none discharged in this
attempt (recorded as `partial` in the ledger, with the stall points in the findings):

1. `hec` — the clamp certificate (T1.3's shape with a **day-aware** oracle: the emitted body has
   length `Θ(k)`, so the pass must emit at `min k n` and close the gap on rank-valid streams; the
   parameter block `pair (F x) x` of `Certificate.lean` already carries the day for it);
2. `hbound` — bounded partial sums of `magnitude_n · ε_n`, which the mandate's new lemma
   `magnitude_le_of_ec` (`magnitude ≤ 2^{p(n)}` for e.c. traders, from the `FP` output-length
   metering and a bound on decoded constants) plus `∑ 2^{p(n)} 2^{-2^n} < ∞` would give;
3. `hcomp` — computability of the clamped table (rational `max`/`min`/`pow` on `Q`'s table).

A Lipschitz argument that does not go through the rewrite would be wrong (mandate T3's trap: a
day-`n` leaf reading `price φ 0` sees `ε_0 = 1/2` of clamping); the accounting here goes through
the rewrite, so the only residual is the day-`n` settlement term.

Sources: [[bli-program]] §3.2(d); bli-paper-033/039, bli-slides-006/008, bli-soto-a-002 (reading C);
mandate T3.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound
open scoped BigOperators

/-- The clamp's expression map: every leaf of day `k` gets the body `clampE k`.
Source: [[bli-program]] §3.2(d); mandate T3
Kind: D
Fidelity: exact -/
def clampExpr (k : ℕ) (_ : Sentence) : Option EF := some (clampE k)

/-- The clamp bodies have rank `0 ≤ k` (no price leaves).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clampExpr_rank : ∀ k ψ e, clampExpr k ψ = some e → e.rank ≤ k := by
  intro k ψ e h
  obtain rfl := Option.some.inj h
  exact EF.rank_le_of_priceQueries _ _ (by simp [clampE_priceQueries])

/-- **The clamp is a splice specification** with target `clamp Q`: `clampE k` reads the bound
price as `var 0` and denotes the clamped price.
Source: [[bli-program]] §3.2(d); mandate T3
Kind: L
Fidelity: exact -/
lemma clampSpec (Q : History) : SpliceSpec clampExpr Q (clamp Q) where
  bound := fun k ψ e h => by
    obtain rfl := Option.some.inj h
    rw [clampE_freeBound]
  fires := fun k ψ e h => by
    obtain rfl := Option.some.inj h
    rw [clampE_denoteWith]
    rfl
  silent := fun k ψ h => absurd h (by simp [clampExpr])

/-- Triangle inequality for a difference of mapped sums.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma abs_sum_map_sub_le {α : Type*} (l : List α) (f g h : α → ℝ)
    (hfg : ∀ x ∈ l, |f x - g x| ≤ h x) :
    |(l.map f).sum - (l.map g).sum| ≤ (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      have ha := hfg a (List.mem_cons_self ..)
      have ht := ih (fun x hx => hfg x (List.mem_cons_of_mem _ hx))
      calc |f a + (t.map f).sum - (g a + (t.map g).sum)|
          = |(f a - g a) + ((t.map f).sum - (t.map g).sum)| := by ring_nf
        _ ≤ |f a - g a| + |(t.map f).sum - (t.map g).sum| := abs_add_le _ _
        _ ≤ h a + (t.map h).sum := add_le_add ha ht

/-- **The day-`n` value gap is at most `magnitude · ε_n`**: the rewritten strategy on `Q` reads
exactly what the original reads on `clamp Q`; only the settlement term differs, by at most `ε_n`
per share.
Source: [[bli-program]] §3.2(d); mandate T3 ("the day-`n` value gap is `≤ magnitude · ε_n`")
Kind: C
Fidelity: exact
Hyps: (a) `hQ` is the base's price range -/
lemma Strategy.clamp_value_sub_le {n : ℕ} (T : Strategy n) (Q : History)
    (hQ : ∀ k ψ, 0 ≤ Q k ψ ∧ Q k ψ ≤ 1) (w : Sentence → ℝ) :
    |(Strategy.spliceOn clampExpr clampExpr_rank T).value Q w - T.value (clamp Q) w| ≤
      T.magnitude (clamp Q) * (epsK n : ℝ) := by
  simp only [Strategy.value, Strategy.spliceOn_trades, List.map_map, Strategy.magnitude]
  rw [← List.sum_map_mul_right]
  refine abs_sum_map_sub_le T.trades _ _ _ (fun p _ => ?_)
  simp only [Function.comp_apply]
  rw [EF.spliceOn_denote (clampSpec Q) p.1]
  have hgap := abs_clamp_sub_le Q n p.2 (hQ n p.2)
  calc |p.1.denote (clamp Q) * (w p.2 - Q n p.2) - p.1.denote (clamp Q) * (w p.2 - clamp Q n p.2)|
      = |p.1.denote (clamp Q)| * |clamp Q n p.2 - Q n p.2| := by
        rw [← abs_mul]; ring_nf
    _ ≤ |p.1.denote (clamp Q)| * (epsK n : ℝ) :=
        mul_le_mul_of_nonneg_left hgap (abs_nonneg _)

/-- Net worths of a trader on `clamp Q` and of its rewrite on `Q` differ by at most the partial
sum of `magnitude_i · ε_i`.
Source: mandate T3
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma Trader.clamp_netWorth_sub_le (Tr : Trader) (Q : History)
    (hQ : ∀ k ψ, 0 ≤ Q k ψ ∧ Q k ψ ≤ 1) (v : PCWorld) (n : ℕ) :
    |Tr.netWorth (clamp Q) v n - (Trader.spliceOn clampExpr clampExpr_rank Tr).netWorth Q v n| ≤
      ∑ i ∈ Finset.range (n + 1), (Tr.strat i).magnitude (clamp Q) * (epsK i : ℝ) := by
  simp only [Trader.netWorth, Trader.spliceOn_strat]
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_sub_comm]
  exact Strategy.clamp_value_sub_le (Tr.strat i) Q hQ v.payout

/-- **The clamped re-pricing is a logical inductor — conditional form.** Given the clamp's
efficiency transport (`hec`, the day-aware certificate), bounded partial sums of
`magnitude · ε` for every e.c. trader (`hbound`, what `magnitude_le_of_ec` and the summability
of `2^{p(n)} 2^{-2^n}` would supply) and the clamped table's computability (`hcomp`),
`clamp Q` is a logical inductor. The clamp is applied to every sentence; `ε_k = 2^{-2^k}`.
Source: [[bli-program]] §3.2(d); bli-paper-033/039, bli-slides-006/008; mandate T3
Kind: C
Fidelity: exact (the program's clamped statement), conditional
Hyps: (a) except `hec`, `hbound`, `hcomp` — named, not discharged in this attempt (see the findings) -/
theorem clamp_isLogicalInductor_of (Q : History) (DP : DeductiveProcess)
    [hQ : IsLogicalInductor Q DP]
    (hec : ∀ Tr : Trader, EfficientlyComputable Tr →
      EfficientlyComputable (Trader.spliceOn clampExpr clampExpr_rank Tr))
    (hbound : ∀ Tr : Trader, EfficientlyComputable Tr → ∃ C : ℝ, ∀ n,
      ∑ i ∈ Finset.range (n + 1), (Tr.strat i).magnitude (clamp Q) * (epsK i : ℝ) ≤ C)
    (hcomp : ComputableMarket (clamp Q)) :
    IsLogicalInductor (clamp Q) DP where
  marketComputable := hcomp
  processComputable := hQ.processComputable
  noExploit := by
    intro Tr hTr hexp
    obtain ⟨C, hC⟩ := hbound Tr hTr
    refine hQ.noExploit _ (hec Tr hTr) (Trader.Exploits.of_boundedDifference hexp C
      (fun n v _ => ?_))
    exact (Trader.clamp_netWorth_sub_le Tr Q (fun k ψ => hQ.marketComputable.1 k ψ) v n).trans
      (hC n)

end Cleanroom.Bli.BliTransfer.AttemptA
