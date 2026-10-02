import Cleanroom.Bli.BliOverlay
import LogicalInduction.Construction.TradingFirm

/-!
# `bli-coherent-mm` (attempt B) · Waived: the stage-relative waived-days lemma (T0)

`bli-overlay`'s waived-days lemma `not_exploits_of_dayValue_le_off_finite` bounds the day value
in **every** `PCWorld`. A propositionally coherent maker cannot supply that: it prices `φ ⋏ ∼φ`
at `0`, and a (propositionally inconsistent) world in which both `φ` and `∼φ` hold pays a trader
holding that bundle. FAF's `Trader.Exploits` only ever looks at worlds consistent with the day's
stage (`v.ConsistentWith (DP.D n)`), so the honest hypothesis is **stage-relative**: the day-`n`
bound is required only in worlds consistent with `DP.D n`. The accounting is the same as the
overlay's, plus one observation: a world consistent with `DP.D n` is consistent with `DP.D i` for
every `i ≤ n` (`DeductiveProcess.mono_le`), so every summand of the day-`n` net worth is bounded
on the worlds `Exploits` quantifies over.

Sources: [[bli-coherent-mm-mandate]] T0; [[bli-overlay-mandate]] T3(a) (the all-worlds form).
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptB

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliOverlay

/-! ## T0: the stage-relative waived-days lemma -/

/-- **T0 (headline, infrastructure). The stage-relative waived-days lemma.** If on every day `n`
outside a finite set `W` the trader's day-`n` strategy has value `≤ marketMakerError n` on the
`[0,1]` history `P` in every world **consistent with the day's stage `DP.D n`**, then the trader
does not exploit `P` relative to `DP`: its net worth on day `n`, in any world consistent with
`DP.D n`, is at most `1 + ∑_{i ∈ W} absBound (Tr.strat i)` (each day `i ≤ n` is bounded in that
world because `DP.D i ⊆ DP.D n`). Weaker hypothesis than `bli-overlay`'s all-worlds lemma; same
conclusion. Over `D`-consistent worlds only, by design.
Source: [[bli-coherent-mm-mandate]] T0; [[bli-overlay-mandate]] T3(a)
Kind: P
Fidelity: exact
Hyps: (a) — `hP` is the `def:market` range clause (without it `Strategy.abs_value_le` does not
apply), `hacc` the per-day stage-relative bound the lemma is about -/
theorem not_exploits_of_dayValue_le_consistent_off_finite (Tr : Trader) (P : History)
    (DP : DeductiveProcess) (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      (Tr.strat n).value P v.payout ≤ (marketMakerError n : ℝ)) :
    ¬ Tr.Exploits P DP := by
  intro hex
  apply hex.2
  refine ⟨1 + ∑ i ∈ W, ((Tr.strat i).absBound : ℝ), ?_⟩
  rintro x ⟨n, v, hv, rfl⟩
  have hday : ∀ i ∈ Finset.range (n + 1), (Tr.strat i).value P v.payout ≤
      (marketMakerError i : ℝ) + (if i ∈ W then ((Tr.strat i).absBound : ℝ) else 0) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hvi : v.ConsistentWith (DP.D i) := fun φ hφ => hv φ (DP.mono_le hin hφ)
    by_cases hiW : i ∈ W
    · rw [if_pos hiW]
      have h1 := (Tr.strat i).abs_value_le P hP v.payout (fun φ => payout_mem_Icc v φ)
      have h2 : (0 : ℝ) ≤ (marketMakerError i : ℝ) := by
        exact_mod_cast (marketMakerError_pos i).le
      have h3 := le_abs_self ((Tr.strat i).value P v.payout)
      linarith
    · rw [if_neg hiW, add_zero]
      exact hacc i hiW v hvi
  unfold Trader.netWorth
  calc ∑ i ∈ Finset.range (n + 1), (Tr.strat i).value P v.payout
      ≤ ∑ i ∈ Finset.range (n + 1),
          ((marketMakerError i : ℝ) + (if i ∈ W then ((Tr.strat i).absBound : ℝ) else 0)) :=
        Finset.sum_le_sum hday
    _ = ∑ i ∈ Finset.range (n + 1), (marketMakerError i : ℝ) +
          ∑ i ∈ Finset.range (n + 1) ∩ W, ((Tr.strat i).absBound : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem]
    _ ≤ 1 + ∑ i ∈ W, ((Tr.strat i).absBound : ℝ) := by
        apply add_le_add (sum_marketMakerError_lt_one n).le
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro i _ _
        exact_mod_cast (Tr.strat i).absBound_nonneg

/-! ## Corollaries for the firm (the shapes of `bli-overlay`'s `Waived.lean`, stage-relative) -/

/-- The cast of a `[0,1]` rational table is a `[0,1]` history.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma castTable_range (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, 0 ≤ Q day φ ∧ Q day φ ≤ 1) :
    ∀ day φ, 0 ≤ (fun d φ => (Q d φ : ℝ)) day φ ∧ (fun d φ => (Q d φ : ℝ)) day φ ≤ 1 := by
  intro d φ
  show (0 : ℝ) ≤ (Q d φ : ℝ) ∧ (Q d φ : ℝ) ≤ 1
  exact ⟨by exact_mod_cast (hQ d φ).1, by exact_mod_cast (hQ d φ).2⟩

/-- The static firm on an exactly rational `[0,1]` table each of whose days outside the finite
set `W` bounds the firm's value by `marketMakerError` in every world consistent with that day's
stage does not exploit that table: T0 at `tradingFirmTrader DP Q`.
Source: [[bli-coherent-mm-mandate]] T0 (corollary)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem firm_not_exploits_of_coherentAccepted_off_finite (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, 0 ≤ Q day φ ∧ Q day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      (TradingFirmAt DP Q n).value (fun d φ => (Q d φ : ℝ)) v.payout ≤ (marketMakerError n : ℝ)) :
    ¬ (tradingFirmTrader DP Q).Exploits (fun d φ => (Q d φ : ℝ)) DP :=
  not_exploits_of_dayValue_le_consistent_off_finite (tradingFirmTrader DP Q) _ DP
    (castTable_range Q hQ) W (fun n hn v hv => hacc n hn v hv)

/-- **T0, firm corollary.** An exactly rational `[0,1]` table `Q` on which the trading firm's
day-`n` strategy — built from `Q` and evaluated on `Q` — has value at most `marketMakerError n`
in every world consistent with `DP.D n`, on every day outside a finite set `W`, is exploited by
no efficiently computable trader: the firm does not exploit it (T0), and by FAF's
`trading_firm_dominance` neither does any e.c. trader.
Source: [[bli-coherent-mm-mandate]] T0 (corollary); [[bli-program]] §3.3 (iii)
Kind: C
Fidelity: exact
Hyps: (a) — `trading_firm_dominance` is FAF's theorem, applied -/
theorem no_ec_trader_exploits_of_firm_coherentAccepted_off_finite (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, 0 ≤ Q day φ ∧ Q day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      (TradingFirmAt DP Q n).value (fun d φ => (Q d φ : ℝ)) v.payout ≤ (marketMakerError n : ℝ)) :
    ∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits (fun d φ => (Q d φ : ℝ)) DP := by
  intro Tr hTr hex
  have hfirm := trading_firm_dominance DP _ (castTable_range Q hQ) Q (fun _ _ => rfl) Tr hTr hex
  exact firm_not_exploits_of_coherentAccepted_off_finite DP Q hQ W hacc hfirm

/-- The all-worlds form implies the stage-relative one (so every customer of `bli-overlay`'s
lemma can switch): T0 is strictly more applicable.
Source: [[bli-coherent-mm-mandate]] T0
Kind: L
Fidelity: n/a -/
theorem not_exploits_of_dayValue_le_off_finite_of_consistent (Tr : Trader) (P : History)
    (DP : DeductiveProcess) (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld, (Tr.strat n).value P v.payout ≤ (marketMakerError n : ℝ)) :
    ¬ Tr.Exploits P DP :=
  not_exploits_of_dayValue_le_consistent_off_finite Tr P DP hP W (fun n hn v _ => hacc n hn v)

end Cleanroom.Bli.BliCoherentMm.AttemptB
