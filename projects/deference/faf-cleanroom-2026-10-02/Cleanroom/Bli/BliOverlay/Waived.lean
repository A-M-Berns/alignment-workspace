import Cleanroom.Bli.BliOverlay.Mentioned
import Cleanroom.Bli.BliOverlay.AttemptA.Waived
import Cleanroom.Bli.BliOverlay.AttemptB.Waived

/-!
# `bli-overlay` · Waived (reconciled): T3, the waived-days lemma and the acceptance bridge

The two attempts state T3(a) and T3(c) identically (over FAF's objects only) and prove them by
the same accounting; the record takes attempt A's declarations. For the customer's entry point
`dayValue_le_of_accepted_state` the attempts chose different shapes: attempt A's takes an
**arbitrary rational table** `Q` with the acceptance-style bound (no `RationalBeliefState`,
no `MarketMaker` — the most general form, of record here); attempt B's takes a past and an
accepted day state with the agreement split into past cells and day-`n` cells
(`dayValue_le_of_accepted_state_split` here), and a form for the past-substituted strategy
(`dayValue_le_of_accepted_state_subst`). All are kept: `bli-coherent-mm`'s M2 fixed point
can enter through whichever fits.

Sources: [[bli-overlay-mandate]] T3(a)–(c), §Lifecycle; [[bli-program]] §3.3 (iii).
-/

namespace Cleanroom.Bli.BliOverlay

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## T3(a): the waived-days lemma -/

/-- **T3(a) (headline, load-bearing). The waived-days lemma.** If on every day `n` outside a
finite set `W` the trader's day-`n` strategy has value `≤ marketMakerError n = 2^{-(n+1)}` on
the `[0,1]` history `P` in every propositionally consistent world (**every** `PCWorld`, no
consistency with the process needed, as in FAF's `marketMaker_day_value_le`), then the trader
does not exploit `P` relative to any process: its net worth is at most
`1 + ∑_{i ∈ W} absBound (Tr.strat i)` on every day in every world.
Source: [[bli-overlay-mandate]] T3(a); [[bli-program]] §3.3 (iii)
Kind: P
Fidelity: exact
Hyps: (a) — `hP` is the `def:market` range clause (without it `Strategy.abs_value_le` does not
apply and the lemma is false for unbounded prices), `hacc` the per-day bound the lemma is
about -/
theorem not_exploits_of_dayValue_le_off_finite (Tr : Trader) (P : History)
    (DP : DeductiveProcess) (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld, (Tr.strat n).value P v.payout ≤ (marketMakerError n : ℝ)) :
    ¬ Tr.Exploits P DP :=
  AttemptA.not_exploits_of_dayValue_le_off_finite Tr P DP hP W hacc

/-! ## T3(b): the acceptance bridge and the customer's entry point -/

/-- **The customer's entry point (T3(b), general form; of record).** A day-`n` strategy `T`
whose exact rational value on an *arbitrary* table `Q` is at most `ε` in every Boolean world on
its support (the shape of `MarketMakerAccepts`'s second conjunct, for any accepted table — not
only `MarketMaker`'s output) has value at most `ε` in every p.c. world on any real history `P`
agreeing with `Q` on every cell `T` mentions (days `≤ n`). The agreement hypothesis is what
"the firm evaluated on the history itself" means; without it the bound says nothing about `P`
(the wrong-market trap, made a hypothesis). `bli-coherent-mm`'s M2 market maker only has to
produce a table with this bound.
Source: [[bli-overlay-mandate]] T3(b), §Lifecycle
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem dayValue_le_of_accepted_state {n : ℕ} (T : Strategy n) (Q : ℕ → Sentence → ℚ) (ε : ℚ)
    (hB : ∀ b : ↥T.support → Bool, T.marketValueRat Q (supportBitWorldRat T b) ≤ ε)
    (P : History) (hagree : ∀ φ, MentionedBy T φ → ∀ k ≤ n, P k φ = (Q k φ : ℝ)) :
    ∀ v : PCWorld, T.value P v.payout ≤ (ε : ℝ) :=
  AttemptA.dayValue_le_of_accepted_state T Q ε hB P hagree

/-- **T3(b). The acceptance bridge.** A candidate state `B` accepted by the market maker against
`T` and `past` (`MarketMakerAccepts T past ε B`) bounds `T`'s value by `ε` in every p.c. world
on every real history that agrees with `candidateRationalHistory past n B` on the cells `T`
mentions.
Source: [[bli-overlay-mandate]] T3(b)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem dayValue_le_of_accepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (ε : ℚ) (B : RationalBeliefState) (hacc : MarketMakerAccepts T past ε B) (P : History)
    (hagree : ∀ φ, MentionedBy T φ → ∀ k ≤ n,
      P k φ = (candidateRationalHistory past n B k φ : ℝ)) :
    ∀ v : PCWorld, T.value P v.payout ≤ (ε : ℝ) :=
  AttemptA.dayValue_le_of_accepts T past ε B hacc P hagree

/-- **The entry point, split form** (attempt B's shape): the agreement is given separately on
the mentioned past cells (`P` reads `rationalHistory past`) and on the mentioned day-`n` cells
(`P` reads the accepted state's quote).
Source: [[bli-overlay-mandate]] §Lifecycle, T3(b)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem dayValue_le_of_accepted_state_split {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (B : RationalBeliefState)
    (hacc : MarketMakerAccepts T past ε B) (P : History)
    (hpast : ∀ φ, MentionedBy T φ → ∀ k < n, P k φ = (rationalHistory past k φ : ℝ))
    (hnow : ∀ φ, MentionedBy T φ → P n φ = (B.quote φ : ℝ)) :
    ∀ v : PCWorld, T.value P v.payout ≤ (ε : ℝ) :=
  AttemptB.dayValue_le_of_accepted_state T past ε B hacc P hpast hnow

/-- **The entry point for a past-substituted strategy** (attempt B's angle): acceptance of
`AttemptB.Strategy.substPast Q T` against `past` bounds `T`'s value on any history that reads
`Q` at the mentioned past cells and `B.quote` at the mentioned day-`n` cells.
Source: [[bli-overlay-mandate]] §Attempt angles (B), §Lifecycle
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem dayValue_le_of_accepted_state_subst {n : ℕ} (T : Strategy n) (Q : ℕ → Sentence → ℚ)
    (past : List RationalBeliefState) (ε : ℚ) (B : RationalBeliefState)
    (hacc : MarketMakerAccepts (AttemptB.Strategy.substPast Q T) past ε B) (P : History)
    (hpast : ∀ φ, MentionedBy T φ → ∀ k < n, P k φ = (Q k φ : ℝ))
    (hnow : ∀ φ, MentionedBy T φ → P n φ = (B.quote φ : ℝ)) :
    ∀ v : PCWorld, T.value P v.payout ≤ (ε : ℝ) :=
  AttemptB.dayValue_le_of_accepted_state_subst T Q past ε B hacc P hpast hnow

/-! ## T3(c): the firm corollary -/

/-- The static firm on an exactly rational `[0,1]` table each of whose days outside the finite
set `W` bounds the firm's value by `marketMakerError` in every p.c. world does not exploit that
table: T3(a) at `tradingFirmTrader DP Q`.
Source: [[bli-overlay-mandate]] T3(c)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem firm_not_exploits_of_accepted_off_finite (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, 0 ≤ Q day φ ∧ Q day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld,
      (TradingFirmAt DP Q n).value (fun d φ => (Q d φ : ℝ)) v.payout ≤ (marketMakerError n : ℝ)) :
    ¬ (tradingFirmTrader DP Q).Exploits (fun d φ => (Q d φ : ℝ)) DP :=
  AttemptA.firm_not_exploits_of_accepted_off_finite DP Q hQ W hacc

/-- **T3(c). The firm corollary.** An exactly rational `[0,1]` table `Q` on which the trading
firm's day-`n` strategy — built from `Q` and evaluated on `Q` — has value at most
`marketMakerError n` in every p.c. world on every day outside a finite set `W` is exploited by
no efficiently computable trader: the firm does not exploit it (T3(a)), and by FAF's
`trading_firm_dominance` neither does any e.c. trader. Not stated over `liaQuote` (that is FAF's
`lia_no_efficient_trader_exploits`).
Source: [[bli-overlay-mandate]] T3(c); [[bli-program]] §3.3 (iii)
Kind: C
Fidelity: exact
Hyps: (a) — `trading_firm_dominance` is FAF's theorem, applied -/
theorem no_ec_trader_exploits_of_firm_accepted_off_finite (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, 0 ≤ Q day φ ∧ Q day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld,
      (TradingFirmAt DP Q n).value (fun d φ => (Q d φ : ℝ)) v.payout ≤ (marketMakerError n : ℝ)) :
    ∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits (fun d φ => (Q d φ : ℝ)) DP :=
  AttemptA.no_ec_trader_exploits_of_firm_accepted_off_finite DP Q hQ W hacc

end Cleanroom.Bli.BliOverlay
