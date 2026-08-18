/-
# Traderized deduction

The deductive special case, run against the **source's** `TradingFirm` and the
**source's** dominance theorem rather than the generalized ones, so that its
conclusion is the original Logical Induction Criterion and not a generalization of
it.

The market prices `TradingFirm DP + E`.  The market maker's bound applies to the
sum, so the firm's plausible upside is `1` plus whatever `E` loses at a
deductively plausible world.  When the enforced region contains every such world —
which is what the coherence polytope of `PC(D_n)` is — `E`'s value there is
nonnegative at every date, the liability is exactly zero, and the modified market
satisfies `def:lic` over `DP` with the source's own constant.

Every theorem the paper states for an arbitrary logical inductor over `DP` then
applies to it, because it satisfies the definition those theorems are conditioned
on.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.AssessmentProcess
import Workspace.Normativity.Contrib.EnforcementStrategy

namespace Workspace.Normativity.Contrib.DeductiveEnforcement

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Workspace.Normativity.Contrib.EnforcementStrategy
open Workspace.Normativity.Contrib.TraderizedEnforcement

/-! ## The market that prices the source firm and one more trader -/

/-- The day-`n` priced aggregate: the source firm's action joined with `E`'s. -/
noncomputable def aggregateAt (DP : DeductiveProcess) (E : AdaptiveTrader) (n : ℕ)
    (past : List RationalBeliefState) : Strategy n :=
  Strategy.join [(LogicalInduction.TradingFirm DP).action n past, E.action n past]

/-- The recursive rational states of the modified deductive algorithm. -/
noncomputable def states (DP : DeductiveProcess) (E : AdaptiveTrader) :
    ℕ → RationalBeliefState
  | n =>
      let past := List.ofFn fun i : Fin n => states DP E i
      MarketMaker (aggregateAt DP E n past) past
        (marketMakerError n) (marketMakerError_pos n)
termination_by n => n
decreasing_by exact i.isLt

noncomputable def quote (DP : DeductiveProcess) (E : AdaptiveTrader) :
    ℕ → Sentence → ℚ := fun n => (states DP E n).quote

noncomputable def history (DP : DeductiveProcess) (E : AdaptiveTrader) : History :=
  fun n => (states DP E n).toValuation

noncomputable def realizedFirm (DP : DeductiveProcess) (E : AdaptiveTrader) :
    Trader where
  strat n := (LogicalInduction.TradingFirm DP).action n
    (List.ofFn fun i : Fin n => states DP E i)

noncomputable def realizedEnforcer (DP : DeductiveProcess) (E : AdaptiveTrader) :
    Trader where
  strat n := E.action n (List.ofFn fun i : Fin n => states DP E i)

noncomputable def realizedAggregate (DP : DeductiveProcess) (E : AdaptiveTrader) :
    Trader where
  strat n := aggregateAt DP E n (List.ofFn fun i : Fin n => states DP E i)

lemma states_eq_marketMakerStates (DP : DeductiveProcess) (E : AdaptiveTrader)
    (n : ℕ) : states DP E n = marketMakerStates (realizedAggregate DP E) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hpast : (List.ofFn fun i : Fin n => states DP E i) =
          List.ofFn fun i : Fin n => marketMakerStates (realizedAggregate DP E) i := by
        apply List.ext_getElem
        · simp
        · intro i hi₁ hi₂
          simp only [List.getElem_ofFn]
          exact ih i (by simpa using hi₁)
      rw [states, marketMakerStates]
      change MarketMaker (aggregateAt DP E n (List.ofFn fun i : Fin n => states DP E i))
          (List.ofFn fun i : Fin n => states DP E i)
          (marketMakerError n) (marketMakerError_pos n) =
        MarketMaker (aggregateAt DP E n (List.ofFn fun i : Fin n => states DP E i))
          (List.ofFn fun i : Fin n => marketMakerStates (realizedAggregate DP E) i)
          (marketMakerError n) (marketMakerError_pos n)
      rw [hpast]

lemma history_eq_marketMakerHistory (DP : DeductiveProcess) (E : AdaptiveTrader) :
    history DP E = marketMakerHistory (realizedAggregate DP E) := by
  funext n φ
  rw [history, marketMakerHistory, states_eq_marketMakerStates]

lemma history_range (DP : DeductiveProcess) (E : AdaptiveTrader) (day : ℕ)
    (φ : Sentence) : 0 ≤ history DP E day φ ∧ history DP E day φ ≤ 1 :=
  (states DP E day).toValuation_mem_Icc φ

lemma history_eq_quote_cast (DP : DeductiveProcess) (E : AdaptiveTrader) (day : ℕ)
    (φ : Sentence) : history DP E day φ = (quote DP E day φ : ℝ) := rfl

lemma realizedAggregate_value (DP : DeductiveProcess) (E : AdaptiveTrader) (n : ℕ)
    (P : History) (w : Sentence → ℝ) :
    ((realizedAggregate DP E).strat n).value P w =
      ((realizedFirm DP E).strat n).value P w +
        ((realizedEnforcer DP E).strat n).value P w := by
  change (aggregateAt DP E n (List.ofFn fun i : Fin n => states DP E i)).value P w = _
  rw [aggregateAt, Strategy.join_value]
  simp [realizedFirm, realizedEnforcer]

theorem realizedAggregate_netWorth (DP : DeductiveProcess) (E : AdaptiveTrader)
    (n : ℕ) (P : History) (v : PCWorld) :
    (realizedAggregate DP E).netWorth P v n =
      (realizedFirm DP E).netWorth P v n + (realizedEnforcer DP E).netWorth P v n := by
  unfold Trader.netWorth
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => realizedAggregate_value DP E i P v.payout

lemma tradingFirmTrader_quote_eq_realizedFirm (DP : DeductiveProcess)
    (E : AdaptiveTrader) :
    LogicalInduction.tradingFirmTrader DP (quote DP E) = realizedFirm DP E := by
  unfold LogicalInduction.tradingFirmTrader realizedFirm
  congr 1
  funext n
  change LogicalInduction.TradingFirmAt DP (quote DP E) n =
    LogicalInduction.TradingFirmAt DP
      (rationalHistory (List.ofFn fun i : Fin n => states DP E i)) n
  apply LogicalInduction.TradingFirmAt_eq_of_eq_prefix
  intro day hday φ
  simp [rationalHistory, quote, hday]

/-! ## Preservation of the original criterion -/

/-- The source firm's plausible upside is the market maker's constant plus the added
trader's deductively assessed liability. -/
theorem realizedFirm_netWorth_le (DP : DeductiveProcess) (E : AdaptiveTrader) (B : ℝ)
    (hliab : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      -B ≤ (realizedEnforcer DP E).netWorth (history DP E) v n)
    (n : ℕ) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    (realizedFirm DP E).netWorth (history DP E) v n ≤ 1 + B := by
  have hmm : (realizedAggregate DP E).netWorth (history DP E) v n < 1 := by
    rw [history_eq_marketMakerHistory]
    exact marketMaker_netWorth_lt_one (realizedAggregate DP E) v n
  have hsplit := realizedAggregate_netWorth DP E n (history DP E) v
  have hE := hliab n v hv
  rw [hsplit] at hmm
  linarith

/-- **Traderized deduction satisfies the original criterion.**  The dominance step
is the pinned dependency's `trading_firm_dominance`, at its own `DeductiveProcess`;
nothing generalized is used. -/
theorem no_efficient_trader_exploits (DP : DeductiveProcess) (E : AdaptiveTrader)
    (B : ℝ)
    (hliab : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      -B ≤ (realizedEnforcer DP E).netWorth (history DP E) v n)
    (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (history DP E) DP := by
  intro hEx
  have hfirm := LogicalInduction.trading_firm_dominance DP (history DP E)
    (history_range DP E) (quote DP E) (history_eq_quote_cast DP E) Tr hTr hEx
  rw [tradingFirmTrader_quote_eq_realizedFirm] at hfirm
  apply hfirm.2
  refine ⟨1 + B, ?_⟩
  rintro x ⟨n, v, hv, rfl⟩
  exact realizedFirm_netWorth_le DP E B hliab n v hv

/-- The criterion form: with the market's program supplied, the modified deductive
market **is a logical inductor over `DP`** in the source's own sense, so every
theorem the paper states for an arbitrary logical inductor over `DP` applies. -/
theorem isLogicalInductor_of_computableMarket (DP : DeductiveProcess)
    (E : AdaptiveTrader) (B : ℝ) (hDP : ComputableDeductiveProcess DP)
    (hliab : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      -B ≤ (realizedEnforcer DP E).netWorth (history DP E) v n)
    (hmarket : ComputableMarket (history DP E)) :
    IsLogicalInductor (history DP E) DP where
  marketComputable := hmarket
  processComputable := hDP
  noExploit := fun Tr hTr => no_efficient_trader_exploits DP E B hliab Tr hTr

/-! ## Zero liability from a world-inclusive presentation

The enforcement position's value at a world the enforced region contains is
nonnegative, whatever the ordinary traders did — the force algebra's
`pair_nonneg_of_mem`.  A presentation every deductively plausible world satisfies
therefore has `B = 0`. -/

/-- One date's enforcement value is nonnegative at a world the rows admit. -/
theorem enforcement_day_value_nonneg (pres : Presentation) (n : ℕ) (P : History)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (v : PCWorld)
    (hrows : ∀ i ∈ pres.rowIndex,
      pres.rhss i ≤ pair pres.coords (pres.normals i) (ratPayout v)) :
    0 ≤ (enforcementStrategy pres n).value P v.payout := by
  have hpay : (fun φ => ((ratPayout v φ : ℚ) : ℝ)) = v.payout := by
    funext φ
    exact (payout_eq_ratPayout v φ).symm
  have hval := value_enforcementStrategy pres n P Q hQ (ratPayout v)
  rw [hpay] at hval
  rw [hval]
  have := pair_nonneg_of_mem (rows := pres.rowIndex) (coords := pres.coords)
    (c := pres.normals) (r := pres.rhss) (β := pres.intensities)
    (p := Q n) (x := ratPayout v) pres.intensities_nonneg hrows
  exact_mod_cast this

/-- **World-inclusive presentations give zero liability.**  Summing the per-date
bound: an enforcement trader whose region admits every deductively plausible world
has nonnegative cumulative value at every such world, so `B = 0`. -/
theorem enforcement_netWorth_nonneg (DP : DeductiveProcess) (E : AdaptiveTrader)
    (hday : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      0 ≤ ((realizedEnforcer DP E).strat n).value (history DP E) v.payout)
    (n : ℕ) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    0 ≤ (realizedEnforcer DP E).netWorth (history DP E) v n := by
  induction n with
  | zero => simpa [Trader.netWorth] using hday 0 v hv
  | succ m ih =>
      have hvm : v.ConsistentWith (DP.D m) := fun φ hφ => hv φ (DP.mono m hφ)
      have hprev := ih hvm
      have hcur := hday (m + 1) v hv
      rw [Trader.netWorth, Finset.sum_range_succ]
      change 0 ≤ (realizedEnforcer DP E).netWorth (history DP E) v m +
        ((realizedEnforcer DP E).strat (m + 1)).value (history DP E) v.payout
      linarith

/-- **Traderized deduction, end to end.**  A per-date world-inclusive enforcement
trader leaves the original criterion intact with the source's own constant `1`. -/
theorem no_efficient_trader_exploits_of_worldInclusive (DP : DeductiveProcess)
    (E : AdaptiveTrader)
    (hday : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      0 ≤ ((realizedEnforcer DP E).strat n).value (history DP E) v.payout)
    (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (history DP E) DP :=
  no_efficient_trader_exploits DP E 0
    (fun n v hv => by simpa using enforcement_netWorth_nonneg DP E hday n v hv) Tr hTr

end Workspace.Normativity.Contrib.DeductiveEnforcement

#print axioms Workspace.Normativity.Contrib.DeductiveEnforcement.states_eq_marketMakerStates
#print axioms Workspace.Normativity.Contrib.DeductiveEnforcement.realizedAggregate_netWorth
#print axioms Workspace.Normativity.Contrib.DeductiveEnforcement.tradingFirmTrader_quote_eq_realizedFirm
#print axioms Workspace.Normativity.Contrib.DeductiveEnforcement.realizedFirm_netWorth_le
#print axioms Workspace.Normativity.Contrib.DeductiveEnforcement.no_efficient_trader_exploits
#print axioms Workspace.Normativity.Contrib.DeductiveEnforcement.isLogicalInductor_of_computableMarket
#print axioms Workspace.Normativity.Contrib.DeductiveEnforcement.enforcement_day_value_nonneg
#print axioms Workspace.Normativity.Contrib.DeductiveEnforcement.enforcement_netWorth_nonneg
#print axioms Workspace.Normativity.Contrib.DeductiveEnforcement.no_efficient_trader_exploits_of_worldInclusive
