import Cleanroom.Bli.BliOverlay.AttemptA.Mentioned
import LogicalInduction.Construction.TradingFirm

/-!
# `bli-overlay` (attempt A) · Waived: the waived-days lemma and the acceptance bridge

**T3 of the mandate.** Three results, all with hypotheses of provenance (a):

* **T3(a), `not_exploits_of_dayValue_le_off_finite`** (headline, Kind P): a trader whose
  day-`n` strategy has value at most `marketMakerError n = 2^{-(n+1)}` in **every** p.c. world on
  every day outside a finite set `W`, on a `[0,1]` history, does not exploit that history. Its
  net worth is bounded by `1 + ∑_{i ∈ W} absBound (strat i)` uniformly in the day and the world
  (`Strategy.abs_value_le` on the waived days, `sum_marketMakerError_lt_one` on the rest), so its
  plausible assessments are bounded above, contradicting `Exploits.2`. No consistency of the
  world with the process is needed (FAF's `marketMaker_day_value_le` is likewise unconditional).
* **T3(b), `dayValue_le_of_accepts`** (Kind L): the honest form of "a history accepted by the
  market maker against the firm *evaluated on the history itself*": `MarketMakerAccepts T past ε B`
  bounds `T`'s value on a history `P` by `ε` in every p.c. world **provided** `P` agrees with the
  candidate history `candidateRationalHistory past n B` on every cell `T` mentions (days `≤ n`).
  The agreement hypothesis is the wrong-market trap made explicit. Its general form,
  `dayValue_le_of_accepted_state`, takes any rational table `Q` with the acceptance-style bound
  on the support worlds — it is the entry point for `bli-coherent-mm`, whose market maker is a
  different fixed point.
* **T3(c), `no_ec_trader_exploits_of_firm_accepted_off_finite`** (headline, Kind C): (a) applied
  to the static firm `tradingFirmTrader DP Q` on the cast of an exactly rational `[0,1]` table
  `Q`, then FAF's `trading_firm_dominance`: no efficiently computable trader exploits `Q`.

`W` is an explicit `Finset ℕ` (D4): a `W` that is not finite would not give a uniform bound.

Sources: [[bli-overlay-mandate]] T3, D4; [[bli-program]] §3.3 (iii).
-/

namespace Cleanroom.Bli.BliOverlay.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## T3(a): the waived-days lemma -/

/-- **T3(a). The waived-days lemma.** If, outside a finite set `W` of days, the trader's day-`n`
strategy has value `≤ marketMakerError n` on the `[0,1]` history `P` in every propositionally
consistent world, then the trader does not exploit `P` (relative to any process): its net worth
is at most `1 + ∑_{i ∈ W} absBound (Tr.strat i)` on every day in every world.
Source: [[bli-overlay-mandate]] T3(a); [[bli-program]] §3.3 (iii)
Kind: P
Fidelity: exact
Hyps: (a) — `hP` is the `def:market` range clause, `hacc` the per-day bound; nothing assumed
beyond the statement -/
theorem not_exploits_of_dayValue_le_off_finite (Tr : Trader) (P : History)
    (DP : DeductiveProcess) (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld, (Tr.strat n).value P v.payout ≤ (marketMakerError n : ℝ)) :
    ¬ Tr.Exploits P DP := by
  intro hex
  apply hex.2
  refine ⟨1 + ∑ i ∈ W, ((Tr.strat i).absBound : ℝ), ?_⟩
  rintro x ⟨n, v, _, rfl⟩
  have hday : ∀ i, (Tr.strat i).value P v.payout ≤
      (marketMakerError i : ℝ) + (if i ∈ W then ((Tr.strat i).absBound : ℝ) else 0) := by
    intro i
    by_cases hi : i ∈ W
    · rw [if_pos hi]
      have h1 := (Tr.strat i).abs_value_le P hP v.payout (fun φ => payout_mem_Icc v φ)
      have h2 : (0 : ℝ) ≤ (marketMakerError i : ℝ) := by
        exact_mod_cast (marketMakerError_pos i).le
      have h3 := le_abs_self ((Tr.strat i).value P v.payout)
      linarith
    · rw [if_neg hi, add_zero]
      exact hacc i hi v
  unfold Trader.netWorth
  calc ∑ i ∈ Finset.range (n + 1), (Tr.strat i).value P v.payout
      ≤ ∑ i ∈ Finset.range (n + 1),
          ((marketMakerError i : ℝ) + (if i ∈ W then ((Tr.strat i).absBound : ℝ) else 0)) :=
        Finset.sum_le_sum (fun i _ => hday i)
    _ = ∑ i ∈ Finset.range (n + 1), (marketMakerError i : ℝ) +
          ∑ i ∈ Finset.range (n + 1) ∩ W, ((Tr.strat i).absBound : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem]
    _ ≤ 1 + ∑ i ∈ W, ((Tr.strat i).absBound : ℝ) := by
        apply add_le_add (sum_marketMakerError_lt_one n).le
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro i _ _
        exact_mod_cast (Tr.strat i).absBound_nonneg

/-! ## T3(b): the acceptance bridge -/

open Classical in
/-- **The customer's entry point (T3(b), general form).** A day-`n` strategy `T` whose exact
rational value on the table `Q` is at most `ε` in every Boolean world on its support (the shape
of `MarketMakerAccepts`'s second conjunct, for an *arbitrary* accepted table — not only
`MarketMaker`'s output) has value at most `ε` in every propositionally consistent world on any
real history `P` that agrees with `Q` on every cell `T` mentions (days `≤ n`). The agreement
hypothesis is what "the firm evaluated on the history itself" means; without it the bound says
nothing about `P`.
Source: [[bli-overlay-mandate]] T3(b), § Lifecycle (`dayValue_le_of_accepted_state`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem dayValue_le_of_accepted_state {n : ℕ} (T : Strategy n) (Q : ℕ → Sentence → ℚ) (ε : ℚ)
    (hB : ∀ b : ↥T.support → Bool, T.marketValueRat Q (supportBitWorldRat T b) ≤ ε)
    (P : History) (hagree : ∀ φ, MentionedBy T φ → ∀ k ≤ n, P k φ = (Q k φ : ℝ)) :
    ∀ v : PCWorld, T.value P v.payout ≤ (ε : ℝ) := by
  intro v
  let b : ↥T.support → Bool := fun ψ => decide (v.Holds ψ)
  have hrat := hB b
  have hcast : T.value (fun d φ => (Q d φ : ℝ)) (supportBitWorld T b) =
      (T.marketValueRat Q (supportBitWorldRat T b) : ℝ) :=
    T.value_eq_marketRatCast (fun d φ => (Q d φ : ℝ)) Q (fun _ _ => rfl)
      (supportBitWorld T b) (supportBitWorldRat T b) (supportBitWorld_eq_ratCast T b)
  have h1 : T.value (fun d φ => (Q d φ : ℝ)) (supportBitWorld T b) ≤ (ε : ℝ) := by
    rw [hcast]
    exact_mod_cast hrat
  have h2 : T.value (fun d φ => (Q d φ : ℝ)) (supportBitWorld T b) =
      T.value (fun d φ => (Q d φ : ℝ)) v.payout :=
    T.value_eq_of_world_eqOn_support _ _ _ (fun φ hφ => supportBitWorld_pcWorld_eq T v φ hφ)
  have h3 : T.value (fun d φ => (Q d φ : ℝ)) v.payout = T.value P v.payout :=
    Strategy.value_eq_of_eqOn_mentioned T _ _ _ (fun φ hφ k hk => (hagree φ hφ k hk).symm)
  rw [h2, h3] at h1
  exact h1

/-- **T3(b). The acceptance bridge.** A candidate state `B` accepted by the market maker against
`T` and the past `past` (`MarketMakerAccepts T past ε B`) bounds `T`'s value by `ε` in every
p.c. world on every real history that agrees with `candidateRationalHistory past n B` on the
cells `T` mentions. This is `dayValue_le_of_accepted_state` at `MarketMaker`'s own table.
Source: [[bli-overlay-mandate]] T3(b)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem dayValue_le_of_accepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (ε : ℚ) (B : RationalBeliefState) (hacc : MarketMakerAccepts T past ε B) (P : History)
    (hagree : ∀ φ, MentionedBy T φ → ∀ k ≤ n,
      P k φ = (candidateRationalHistory past n B k φ : ℝ)) :
    ∀ v : PCWorld, T.value P v.payout ≤ (ε : ℝ) :=
  dayValue_le_of_accepted_state T (candidateRationalHistory past n B) ε hacc.2 P hagree

/-! ## T3(c): the firm corollary -/

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
set `W` bounds the firm's value by `marketMakerError` in every p.c. world does not exploit that
table. T3(a) at `tradingFirmTrader DP Q`.
Source: [[bli-overlay-mandate]] T3(c)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem firm_not_exploits_of_accepted_off_finite (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, 0 ≤ Q day φ ∧ Q day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld,
      (TradingFirmAt DP Q n).value (fun d φ => (Q d φ : ℝ)) v.payout ≤ (marketMakerError n : ℝ)) :
    ¬ (tradingFirmTrader DP Q).Exploits (fun d φ => (Q d φ : ℝ)) DP :=
  not_exploits_of_dayValue_le_off_finite (tradingFirmTrader DP Q) _ DP (castTable_range Q hQ) W
    (fun n hn v => hacc n hn v)

/-- **T3(c). The firm corollary.** An exactly rational `[0,1]` table `Q` on which the trading
firm's day-`n` strategy — built from `Q` and evaluated on `Q` — has value at most
`marketMakerError n` in every p.c. world on every day outside a finite set `W` is exploited by no
efficiently computable trader: the firm does not exploit it (T3(a)), and by FAF's
`trading_firm_dominance` neither does any e.c. trader.
Source: [[bli-overlay-mandate]] T3(c); [[bli-program]] §3.3 (iii)
Kind: C
Fidelity: exact
Hyps: (a) — `trading_firm_dominance` is FAF's theorem, applied -/
theorem no_ec_trader_exploits_of_firm_accepted_off_finite (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, 0 ≤ Q day φ ∧ Q day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld,
      (TradingFirmAt DP Q n).value (fun d φ => (Q d φ : ℝ)) v.payout ≤ (marketMakerError n : ℝ)) :
    ∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits (fun d φ => (Q d φ : ℝ)) DP := by
  intro Tr hTr hex
  have hfirm := trading_firm_dominance DP _ (castTable_range Q hQ) Q (fun _ _ => rfl) Tr hTr hex
  exact firm_not_exploits_of_accepted_off_finite DP Q hQ W hacc hfirm

end Cleanroom.Bli.BliOverlay.AttemptA
