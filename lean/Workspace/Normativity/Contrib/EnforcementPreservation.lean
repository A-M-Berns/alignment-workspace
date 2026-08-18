/-
# Enforcement preservation

The composition the whole architecture turns on, at the type it is actually needed
at.  The market prices the generalized trading firm **plus** an added trader `E`
with no budget, no weight discount and no efficient-computability requirement.  The
market maker's guarantee then bounds the *sum*, so the ordinary aggregate's
plausible upside is bounded by the market maker's own constant plus whatever `E`
loses at the assessed worlds — and by nothing else.

If that loss is uniformly bounded on the assessment process, dominance still runs
and no efficiently computable trader exploits the market.  Nothing about the
*source* of `E`'s position enters: it is not required to be an enforcement trader,
only to have bounded assessed cumulative liability.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.AssessmentFirm

namespace Workspace.Normativity.Contrib.EnforcementPreservation

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Workspace.Normativity.Contrib.AssessmentFirm

/-! ## The market that prices the firm and one more trader -/

/-- The day-`n` priced aggregate: the generalized firm's action joined with `E`'s. -/
noncomputable def aggregateAt (L : Assessment) (E : AdaptiveTrader) (n : ℕ)
    (past : List RationalBeliefState) : Strategy n :=
  Strategy.join [(TradingFirm L).action n past, E.action n past]

/-- The recursive rational states of the modified algorithm. -/
noncomputable def states (L : Assessment) (E : AdaptiveTrader) :
    ℕ → RationalBeliefState
  | n =>
      let past := List.ofFn fun i : Fin n => states L E i
      MarketMaker (aggregateAt L E n past) past
        (marketMakerError n) (marketMakerError_pos n)
termination_by n => n
decreasing_by exact i.isLt

/-- The exact rational quote table of the modified algorithm. -/
noncomputable def quote (L : Assessment) (E : AdaptiveTrader) : ℕ → Sentence → ℚ :=
  fun n => (states L E n).quote

/-- The real-valued market history of the modified algorithm. -/
noncomputable def history (L : Assessment) (E : AdaptiveTrader) : History :=
  fun n => (states L E n).toValuation

/-- The realized ordinary aggregate: the generalized firm run against the actual
prefix. -/
noncomputable def realizedFirm (L : Assessment) (E : AdaptiveTrader) : Trader where
  strat n := (TradingFirm L).action n (List.ofFn fun i : Fin n => states L E i)

/-- The realized added trader. -/
noncomputable def realizedEnforcer (L : Assessment) (E : AdaptiveTrader) : Trader where
  strat n := E.action n (List.ofFn fun i : Fin n => states L E i)

/-- The realized priced aggregate. -/
noncomputable def realizedAggregate (L : Assessment) (E : AdaptiveTrader) : Trader where
  strat n := aggregateAt L E n (List.ofFn fun i : Fin n => states L E i)

lemma states_eq_marketMakerStates (L : Assessment) (E : AdaptiveTrader) (n : ℕ) :
    states L E n = marketMakerStates (realizedAggregate L E) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hpast : (List.ofFn fun i : Fin n => states L E i) =
          List.ofFn fun i : Fin n => marketMakerStates (realizedAggregate L E) i := by
        apply List.ext_getElem
        · simp
        · intro i hi₁ hi₂
          simp only [List.getElem_ofFn]
          exact ih i (by simpa using hi₁)
      rw [states, marketMakerStates]
      change MarketMaker (aggregateAt L E n (List.ofFn fun i : Fin n => states L E i))
          (List.ofFn fun i : Fin n => states L E i)
          (marketMakerError n) (marketMakerError_pos n) =
        MarketMaker (aggregateAt L E n (List.ofFn fun i : Fin n => states L E i))
          (List.ofFn fun i : Fin n => marketMakerStates (realizedAggregate L E) i)
          (marketMakerError n) (marketMakerError_pos n)
      rw [hpast]

lemma history_eq_marketMakerHistory (L : Assessment) (E : AdaptiveTrader) :
    history L E = marketMakerHistory (realizedAggregate L E) := by
  funext n φ
  rw [history, marketMakerHistory, states_eq_marketMakerStates]

lemma history_range (L : Assessment) (E : AdaptiveTrader) (day : ℕ) (φ : Sentence) :
    0 ≤ history L E day φ ∧ history L E day φ ≤ 1 :=
  (states L E day).toValuation_mem_Icc φ

lemma history_eq_quote_cast (L : Assessment) (E : AdaptiveTrader) (day : ℕ)
    (φ : Sentence) : history L E day φ = (quote L E day φ : ℝ) := rfl

/-! ## The aggregate splits -/

lemma realizedAggregate_value (L : Assessment) (E : AdaptiveTrader) (n : ℕ)
    (P : History) (w : Sentence → ℝ) :
    ((realizedAggregate L E).strat n).value P w =
      ((realizedFirm L E).strat n).value P w +
        ((realizedEnforcer L E).strat n).value P w := by
  change (aggregateAt L E n (List.ofFn fun i : Fin n => states L E i)).value P w = _
  rw [aggregateAt, Strategy.join_value]
  simp [realizedFirm, realizedEnforcer]

/-- The realized aggregate's net worth is the ordinary aggregate's plus the added
trader's, in every world. -/
theorem realizedAggregate_netWorth (L : Assessment) (E : AdaptiveTrader) (n : ℕ)
    (P : History) (v : PCWorld) :
    (realizedAggregate L E).netWorth P v n =
      (realizedFirm L E).netWorth P v n + (realizedEnforcer L E).netWorth P v n := by
  unfold Trader.netWorth
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => realizedAggregate_value L E i P v.payout

/-- Prefix invariance: the adaptive realized firm is the static complete-table firm
the dominance theorem is stated for. -/
lemma tradingFirmTrader_quote_eq_realizedFirm (L : Assessment) (E : AdaptiveTrader) :
    AssessmentFirm.tradingFirmTrader L (quote L E) = realizedFirm L E := by
  unfold AssessmentFirm.tradingFirmTrader realizedFirm
  congr 1
  funext n
  change AssessmentFirm.TradingFirmAt L (quote L E) n =
    AssessmentFirm.TradingFirmAt L
      (rationalHistory (List.ofFn fun i : Fin n => states L E i)) n
  apply AssessmentFirm.TradingFirmAt_eq_of_eq_prefix
  intro day hday φ
  simp [rationalHistory, quote, hday]

/-! ## The composition -/

/-- **The ordinary aggregate's plausible upside is the market maker's constant plus
the added trader's assessed liability.**

`B` bounds the added trader's cumulative value from below at the assessed worlds;
the conclusion bounds the ordinary aggregate's cumulative value from above at the
same worlds.  The market maker's own constant is `1` and is not a hypothesis: it is
the pinned dependency's `lem:mm`, whose bound holds at *every* propositionally
consistent world. -/
theorem realizedFirm_netWorth_le (L : Assessment) (E : AdaptiveTrader) (B : ℝ)
    (hliab : ∀ n (v : PCWorld), L.Live n v →
      -B ≤ (realizedEnforcer L E).netWorth (history L E) v n)
    (n : ℕ) (v : PCWorld) (hv : L.Live n v) :
    (realizedFirm L E).netWorth (history L E) v n ≤ 1 + B := by
  have hmm : (realizedAggregate L E).netWorth (history L E) v n < 1 := by
    rw [history_eq_marketMakerHistory]
    exact marketMaker_netWorth_lt_one (realizedAggregate L E) v n
  have hsplit := realizedAggregate_netWorth L E n (history L E) v
  have hE := hliab n v hv
  rw [hsplit] at hmm
  linarith

/-- **Enforcement preservation.**  If the added trader's assessed cumulative value
is bounded below by `-B` on the assessment process, then no efficiently computable
trader exploits the modified market relative to that process.

Every dependency is exposed: the assessment-process hypotheses live in `L`, the
liability bound is `hliab`, and the market maker's constant enters through the
pinned dependency's `lem:mm`. -/
theorem no_efficient_trader_exploits (L : Assessment) (E : AdaptiveTrader) (B : ℝ)
    (hliab : ∀ n (v : PCWorld), L.Live n v →
      -B ≤ (realizedEnforcer L E).netWorth (history L E) v n)
    (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ L.Exploits Tr (history L E) := by
  intro hEx
  have hfirm := AssessmentFirm.trading_firm_dominance L (history L E)
    (history_range L E) (quote L E) (history_eq_quote_cast L E) Tr hTr hEx
  rw [tradingFirmTrader_quote_eq_realizedFirm] at hfirm
  apply hfirm.2
  refine ⟨1 + B, ?_⟩
  rintro x ⟨n, v, hv, rfl⟩
  exact realizedFirm_netWorth_le L E B hliab n v hv

/-- The criterion form. -/
theorem isLogicalInductor_of_computableMarket (L : Assessment) (E : AdaptiveTrader)
    (B : ℝ)
    (hliab : ∀ n (v : PCWorld), L.Live n v →
      -B ≤ (realizedEnforcer L E).netWorth (history L E) v n)
    (hmarket : ComputableMarket (history L E)) :
    L.IsLogicalInductor (history L E) :=
  ⟨hmarket, fun Tr hTr => no_efficient_trader_exploits L E B hliab Tr hTr⟩

/-- **The zero-liability case.**  When the added trader never loses at an assessed
world, the bound is the market maker's own constant and the criterion holds with no
further hypothesis.  This is the shape the deductive special case instantiates:
there `B = 0` because every deductively plausible world satisfies every row of the
coherence polytope, so the enforcement position's value at it is nonnegative
(`Contrib.TraderizedEnforcement.pair_nonneg_of_mem`). -/
theorem no_efficient_trader_exploits_of_nonneg (L : Assessment) (E : AdaptiveTrader)
    (hliab : ∀ n (v : PCWorld), L.Live n v →
      0 ≤ (realizedEnforcer L E).netWorth (history L E) v n)
    (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ L.Exploits Tr (history L E) :=
  no_efficient_trader_exploits L E 0 (fun n v hv => by
    simpa using hliab n v hv) Tr hTr

/-- Cumulative nonnegativity follows from per-date nonnegativity, which is what the
force algebra delivers. -/
theorem netWorth_nonneg_of_day_nonneg (E : AdaptiveTrader) (L : Assessment)
    (hday : ∀ n (v : PCWorld), L.Live n v →
      0 ≤ ((realizedEnforcer L E).strat n).value (history L E) v.payout)
    (hnest : ∀ n (v : PCWorld), L.Live (n + 1) v → L.Live n v)
    (n : ℕ) (v : PCWorld) (hv : L.Live n v) :
    0 ≤ (realizedEnforcer L E).netWorth (history L E) v n := by
  induction n with
  | zero =>
      simpa [Trader.netWorth] using hday 0 v hv
  | succ m ih =>
      rw [Trader.netWorth, Finset.sum_range_succ]
      have hprev : 0 ≤ (realizedEnforcer L E).netWorth (history L E) v m :=
        ih (hnest m v hv)
      have hcur := hday (m + 1) v hv
      change 0 ≤ (realizedEnforcer L E).netWorth (history L E) v m +
        ((realizedEnforcer L E).strat (m + 1)).value (history L E) v.payout
      linarith


/-! ## What computability of the modified market still needs

`isLogicalInductor_of_computableMarket` takes `ComputableMarket (history L E)` as its
one remaining hypothesis, which is exactly the shape of the dependency's own
`lia_isLogicalInductor_of_computableMarket`.  Three of the four things a compiler
for it needs are already here or in the dependency.

* **The emission side is executable.**  `AssessmentProcess.BudgeterAt`,
  `AssessmentFirm.TradingFirmAt` and `EnforcementStrategy.enforcementStrategy` are
  `def`s, not `noncomputable def`s: given the assessment process's restriction lists
  and the presentation as data, Lean compiles the day-`n` strategy term.  The
  dependency's `BudgeterAt` and `TradingFirmAt` have the same status.
* **The search side is generic in the strategy.**
  `LogicalInduction.marketMakerSearchUpTo` is an executable bounded search and
  `LogicalInduction.MarketMaker_search_clock` says it returns the market maker's
  answer at a finite clock, for *every* `Strategy n`.  Nothing about the aggregate
  enters.
* **The recursion is prefix-determined**, which is what lets a clocked emitter exist:
  the day-`n` aggregate depends on the first `n` belief states only, and that is
  `aggregateAt_eq_of_eq_prefix` below.

What is *not* here is the erasure: the first-order, `Nat`-and-`List`-valued
presentation of the whole recursion that the dependency's
`Construction/LIACompiler.lean` builds for its own aggregate.  That is transcription
against a large file rather than a mathematical gap, and this pass does not do it.
Note also the distinction the theorem needs and the paper does not:
`EfficientlyComputable` is required of the traders the criterion quantifies over,
and the enforcement trader is not one of them -- it may be computable without being
efficiently computable, and presenting a coherence polytope may cost exponentially
in the priced fragment. -/

/-- The day-`n` aggregate depends on the market prefix and nothing later.  The
enforcement trader's own prefix-invariance is a hypothesis because an arbitrary
`AdaptiveTrader` need not have it. -/
theorem aggregateAt_eq_of_eq_prefix (L : Assessment) (E : AdaptiveTrader) (n : ℕ)
    (past past' : List RationalBeliefState)
    (hE : E.action n past = E.action n past')
    (h : ∀ day, day < n → ∀ φ,
      rationalHistory past day φ = rationalHistory past' day φ) :
    aggregateAt L E n past = aggregateAt L E n past' := by
  have hfirm : (TradingFirm L).action n past = (TradingFirm L).action n past' :=
    AssessmentFirm.TradingFirmAt_eq_of_eq_prefix L _ _ n h
  unfold aggregateAt
  rw [hE, hfirm]

end Workspace.Normativity.Contrib.EnforcementPreservation

#print axioms Workspace.Normativity.Contrib.EnforcementPreservation.states_eq_marketMakerStates
#print axioms Workspace.Normativity.Contrib.EnforcementPreservation.history_eq_marketMakerHistory
#print axioms Workspace.Normativity.Contrib.EnforcementPreservation.realizedAggregate_netWorth
#print axioms Workspace.Normativity.Contrib.EnforcementPreservation.tradingFirmTrader_quote_eq_realizedFirm
#print axioms Workspace.Normativity.Contrib.EnforcementPreservation.realizedFirm_netWorth_le
#print axioms Workspace.Normativity.Contrib.EnforcementPreservation.no_efficient_trader_exploits
#print axioms Workspace.Normativity.Contrib.EnforcementPreservation.isLogicalInductor_of_computableMarket
#print axioms Workspace.Normativity.Contrib.EnforcementPreservation.no_efficient_trader_exploits_of_nonneg
#print axioms Workspace.Normativity.Contrib.EnforcementPreservation.netWorth_nonneg_of_day_nonneg
#print axioms Workspace.Normativity.Contrib.EnforcementPreservation.aggregateAt_eq_of_eq_prefix
