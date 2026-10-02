import Cleanroom.Bli.BliOverlay

/-!
# `bli-coherent-mm` (attempt A) · Waived: the stage-relative waived-days lemma (T0)

**T0 of the mandate.** `bli-overlay`'s waived-days lemma `not_exploits_of_dayValue_le_off_finite`
takes the per-day bound in **every** `PCWorld`. A coherent market maker cannot supply that: it
prices `φ ⋏ ∼φ` at `0`, and a (propositionally impossible, but `PCWorld`-typed) world where both
`φ` and `∼φ` "hold" is not in the type — yet the worlds that *are* in the type and are
inconsistent with the stage `DP.D n` can pay a trader arbitrarily, and the coherent maker's
bound is only over `DP.D n`-consistent worlds. FAF's `Exploits` quantifies over exactly those
(`plausibleAssessments`: `v.ConsistentWith (DP.D n)` on day `n`), so the accounting of
`bli-overlay` goes through unchanged with one extra step: a world consistent with `DP.D n` is
consistent with `DP.D i` for every `i ≤ n` (`DeductiveProcess.mono_le`), so each summand of
`netWorth P v n` is bounded on the plausible worlds.

* **`not_exploits_of_dayValue_le_consistent_off_finite`** (headline, Kind P): the lemma.
* `firm_not_exploits_of_coherentAccepted_off_finite`, `no_ec_trader_exploits_of_firm_coherentAccepted_off_finite`
  (Kind C): the firm corollaries mirroring `bli-overlay`'s `Waived.lean`, through FAF's
  `trading_firm_dominance`.

Sources: [[bli-coherent-mm-mandate]] T0; [[bli-overlay-mandate]] T3; [[bli-program]] §3.3 (iii).
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliOverlay

/-! ## T0: the stage-relative waived-days lemma -/

/-- **T0 (headline). The stage-relative waived-days lemma.** If on every day `n` outside a finite
set `W` the trader's day-`n` strategy has value `≤ marketMakerError n = 2^{-(n+1)}` on the `[0,1]`
history `P` in every world **consistent with the stage `DP.D n`**, then the trader does not
exploit `P` relative to `DP`: on a day `n` and a world `v` consistent with `DP.D n`, `v` is
consistent with every earlier stage (`mono_le`), so its net worth is at most
`1 + ∑_{i ∈ W} absBound (Tr.strat i)`. The scope clause "over `DP.D n`-consistent worlds" is the
whole difference from `bli-overlay`'s all-worlds form, and it is what a coherent maker can supply.
Source: [[bli-coherent-mm-mandate]] T0; [[bli-overlay-mandate]] T3(a)
Kind: P
Fidelity: exact
Hyps: (a) — `hP` is the `def:market` range clause (without it `Strategy.abs_value_le` does not
apply), `hacc` the per-day bound the lemma is about; nothing assumed beyond the statement -/
theorem not_exploits_of_dayValue_le_consistent_off_finite (Tr : Trader) (P : History)
    (DP : DeductiveProcess) (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      (Tr.strat n).value P v.payout ≤ (marketMakerError n : ℝ)) :
    ¬ Tr.Exploits P DP := by
  intro hex
  apply hex.2
  refine ⟨1 + ∑ i ∈ W, ((Tr.strat i).absBound : ℝ), ?_⟩
  rintro x ⟨n, v, hv, rfl⟩
  have hday : ∀ i ≤ n, (Tr.strat i).value P v.payout ≤
      (marketMakerError i : ℝ) + (if i ∈ W then ((Tr.strat i).absBound : ℝ) else 0) := by
    intro i hi
    by_cases hiW : i ∈ W
    · rw [if_pos hiW]
      have h1 := (Tr.strat i).abs_value_le P hP v.payout (fun φ => payout_mem_Icc v φ)
      have h2 : (0 : ℝ) ≤ (marketMakerError i : ℝ) := by
        exact_mod_cast (marketMakerError_pos i).le
      have h3 := le_abs_self ((Tr.strat i).value P v.payout)
      linarith
    · rw [if_neg hiW, add_zero]
      exact hacc i hiW v (fun φ hφ => hv φ (DP.mono_le hi hφ))
  unfold Trader.netWorth
  calc ∑ i ∈ Finset.range (n + 1), (Tr.strat i).value P v.payout
      ≤ ∑ i ∈ Finset.range (n + 1),
          ((marketMakerError i : ℝ) + (if i ∈ W then ((Tr.strat i).absBound : ℝ) else 0)) :=
        Finset.sum_le_sum (fun i hi => hday i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    _ = ∑ i ∈ Finset.range (n + 1), (marketMakerError i : ℝ) +
          ∑ i ∈ Finset.range (n + 1) ∩ W, ((Tr.strat i).absBound : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem]
    _ ≤ 1 + ∑ i ∈ W, ((Tr.strat i).absBound : ℝ) := by
        apply add_le_add (sum_marketMakerError_lt_one n).le
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro i _ _
        exact_mod_cast (Tr.strat i).absBound_nonneg

/-! ## The firm corollaries -/

/-- The static firm on an exactly rational `[0,1]` table each of whose days outside the finite
set `W` bounds the firm's value by `marketMakerError` in every world consistent with that day's
stage does not exploit that table: T0 at `tradingFirmTrader DP Q`.
Source: [[bli-coherent-mm-mandate]] T0 (corollaries); [[bli-overlay-mandate]] T3(c)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem firm_not_exploits_of_coherentAccepted_off_finite (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, 0 ≤ Q day φ ∧ Q day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      (TradingFirmAt DP Q n).value (fun d φ => (Q d φ : ℝ)) v.payout ≤ (marketMakerError n : ℝ)) :
    ¬ (tradingFirmTrader DP Q).Exploits (fun d φ => (Q d φ : ℝ)) DP :=
  not_exploits_of_dayValue_le_consistent_off_finite (tradingFirmTrader DP Q) _ DP
    (BliOverlay.AttemptA.castTable_range Q hQ) W (fun n hn v hv => hacc n hn v hv)

/-- **T0, the firm corollary.** An exactly rational `[0,1]` table `Q` on which the trading firm's
day-`n` strategy — built from `Q` and evaluated on `Q` — has value at most `marketMakerError n`
in every world consistent with `DP.D n`, on every day outside a finite set `W`, is exploited by no
efficiently computable trader: the firm does not exploit it (T0) and by FAF's
`trading_firm_dominance` neither does any e.c. trader. The entry point of T6.
Source: [[bli-coherent-mm-mandate]] T0 (corollaries); [[bli-overlay-mandate]] T3(c)
Kind: C
Fidelity: exact
Hyps: (a) — `trading_firm_dominance` is FAF's theorem, applied -/
theorem no_ec_trader_exploits_of_firm_coherentAccepted_off_finite (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, 0 ≤ Q day φ ∧ Q day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      (TradingFirmAt DP Q n).value (fun d φ => (Q d φ : ℝ)) v.payout ≤ (marketMakerError n : ℝ)) :
    ∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits (fun d φ => (Q d φ : ℝ)) DP := by
  intro Tr hTr hex
  have hfirm := trading_firm_dominance DP _ (BliOverlay.AttemptA.castTable_range Q hQ) Q
    (fun _ _ => rfl) Tr hTr hex
  exact firm_not_exploits_of_coherentAccepted_off_finite DP Q hQ W hacc hfirm

end Cleanroom.Bli.BliCoherentMm.AttemptA
