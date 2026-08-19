/-
# Discharging the modified market's bounded evaluator

`EnforcedComputation` reduces the modified market's computability to one object,
`EnforcedBoundedEvaluatorCompiler` — the analogue of the boundary the pinned source
isolates for ordinary LIA.  This file instantiates it.

The construction is the source's own, with one extra list append in the day's aggregate,
and it is proved against the public computability interface the pinned dependency exports
(`efAbsBound_primrec`, `tradingFirmTradesFromStageTradeLists_primrec`,
`marketMakerSearchUpToTradeList_primrec`, and the rest).  Nothing here re-derives that
interface, and nothing here is new mathematics: the soundness of the modified recurrence
was already proved in `EnforcedComputation`, and what remains is that the recurrence is
primitive recursive in its inputs.

The single hypothesis is `Primrec₂ E.trades` — that the enforcer really is an effective
function from the date and the ordinary trade list to its own trade list.  That is the
honest content of "the enforcer is given as effective data", and it is carried by
`EffectiveEnforcerComputation` rather than assumed silently.

Names are provisional (`AGENTS.md` standard 6).
-/

import LogicalInduction.Construction.LIACompiler
import Workspace.Normativity.Contrib.EnforcedComputation

namespace Workspace.Normativity.Contrib.EnforcedCompiler

open LogicalInduction
open Workspace.Normativity.Contrib.DeductiveEnforcement
open Workspace.Normativity.Contrib.EnforcedComputation

/-- The enforcer is an effective function of the date and the ordinary trade list. -/
structure EffectiveEnforcerComputation (E : EffectiveEnforcer) where
  /-- The day's enforcement trade list is primitive recursive in the date and the ordinary
  aggregate's trade list. -/
  tradesComputable : Primrec₂ E.trades

/-! ## The fully erased recurrence -/

/-- The modified recurrence over raw trade lists: the firm's day trade list with the
enforcer's appended.  Same shape as the source's erased recurrence. -/
def enfPrefixFromTradeListsAtFuel (D : ℕ → Finset Sentence)
    (hook : ℕ → List (EF × Sentence) → List (EF × Sentence)) (fuel : ℕ) :
    ℕ → Option (List RationalBeliefState)
  | 0 => some []
  | n + 1 => do
      let past ← enfPrefixFromTradeListsAtFuel D hook fuel n
      let state ← marketMakerSearchUpToTradeList
        (tradingFirmTradesFromStageTradeLists D (rationalHistory past) n ++
          hook n (tradingFirmTradesFromStageTradeLists D (rationalHistory past) n))
        n past (marketMakerError n) fuel
      some (past ++ [state])

lemma enfAggregateFromStages_trades (D : ℕ → Finset Sentence) (E : EffectiveEnforcer)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    (enfAggregateFromStages D E Q n).trades =
      tradingFirmTradesFromStageTradeLists D Q n ++
        E.trades n (tradingFirmTradesFromStageTradeLists D Q n) := by
  have hfirm : tradingFirmTradesFromStageTradeLists D Q n =
      (TradingFirmAtFromStages D Q n).trades := by
    rw [tradingFirmTradesFromStageTradeLists_eq, TradingFirmAtFromStageLists_eq]
  simp [enfAggregateFromStages, Strategy.join, EffectiveEnforcer.strategy, hfirm]

lemma enfPrefixFromTradeListsAtFuel_eq (D : ℕ → Finset Sentence) (E : EffectiveEnforcer)
    (fuel n : ℕ) :
    enfPrefixFromTradeListsAtFuel D E.trades fuel n =
      enfPrefixFromStagesAtFuel D E fuel n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [enfPrefixFromTradeListsAtFuel, enfPrefixFromStagesAtFuel, ih]
      apply Option.bind_congr
      intro past _
      rw [← enfAggregateFromStages_trades D E (rationalHistory past) n,
        marketMakerSearchUpToTradeList_eq, marketMakerSearchUpToFromLists_eq]

/-! ## Primitive recursivity -/

section
attribute [local irreducible] Nat.sqrt enfPrefixFromTradeListsAtFuel
  tradingFirmTradesFromStageTradeLists marketMakerSearchUpToTradeList

private lemma enfPrefixFromTradeListsAtFuel_prim
    {hook : ℕ → List (EF × Sentence) → List (EF × Sentence)} (hhook : Primrec₂ hook) :
    Primrec fun p : (List (Finset Sentence) × ℕ) × ℕ =>
      enfPrefixFromTradeListsAtFuel (decodedStageTable p.1.1) hook p.1.2 p.2 := by
  let C := List (Finset Sentence) × ℕ
  have hbase : Primrec fun _ctx : C =>
      (some [] : Option (List RationalBeliefState)) :=
    Primrec.const (some [])
  have hstep : Primrec₂ fun (ctx : C)
      (ni : ℕ × Option (List RationalBeliefState)) =>
      ni.2.bind fun past =>
        (marketMakerSearchUpToTradeList
          (tradingFirmTradesFromStageTradeLists
            (decodedStageTable ctx.1) (rationalHistory past) ni.1 ++
            hook ni.1 (tradingFirmTradesFromStageTradeLists
              (decodedStageTable ctx.1) (rationalHistory past) ni.1))
          ni.1 past (marketMakerError ni.1) ctx.2).bind fun state =>
            some (past ++ [state]) := by
    let X := C × (ℕ × Option (List RationalBeliefState))
    have hfirm : Primrec₂ fun (x : X) (past : List RationalBeliefState) =>
        tradingFirmTradesFromStageTradeLists
          (decodedStageTable x.1.1) (rationalHistory past) x.2.1 := by
      have hinput : Primrec fun z : X × List RationalBeliefState =>
          (((z.1.1.1, z.2), z.1.2.1) :
            (List (Finset Sentence) × List RationalBeliefState) × ℕ) :=
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          Primrec.snd).pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      exact (tradingFirmTradesFromStageTradeLists_primrec.comp hinput).to₂
    have hsearch : Primrec₂ fun (x : X) (past : List RationalBeliefState) =>
        marketMakerSearchUpToTradeList
          (tradingFirmTradesFromStageTradeLists
            (decodedStageTable x.1.1) (rationalHistory past) x.2.1 ++
            hook x.2.1 (tradingFirmTradesFromStageTradeLists
              (decodedStageTable x.1.1) (rationalHistory past) x.2.1))
          x.2.1 past (marketMakerError x.2.1) x.1.2 := by
      have hord : Primrec fun z : X × List RationalBeliefState =>
          tradingFirmTradesFromStageTradeLists
            (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1 :=
        hfirm.comp Primrec.fst Primrec.snd
      have hn : Primrec fun z : X × List RationalBeliefState => z.1.2.1 :=
        Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
      have hpast : Primrec fun z : X × List RationalBeliefState => z.2 :=
        Primrec.snd
      have hhk : Primrec fun z : X × List RationalBeliefState =>
          hook z.1.2.1 (tradingFirmTradesFromStageTradeLists
            (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1) :=
        hhook.comp hn hord
      have htrades : Primrec fun z : X × List RationalBeliefState =>
          tradingFirmTradesFromStageTradeLists
            (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1 ++
            hook z.1.2.1 (tradingFirmTradesFromStageTradeLists
              (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1) :=
        Primrec.list_append.comp hord hhk
      have hepsilon : Primrec fun z : X × List RationalBeliefState =>
          marketMakerError z.1.2.1 :=
        marketMakerError_primrec.comp hn
      have hfuel : Primrec fun z : X × List RationalBeliefState => z.1.1.2 :=
        Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
      have hinput : Primrec fun z : X × List RationalBeliefState =>
          ((((tradingFirmTradesFromStageTradeLists
              (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1 ++
              hook z.1.2.1 (tradingFirmTradesFromStageTradeLists
                (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1),
            z.1.2.1), z.2), marketMakerError z.1.2.1),
              z.1.1.2) := (((htrades.pair hn).pair hpast).pair hepsilon).pair hfuel
      exact (marketMakerSearchUpToTradeList_primrec.comp hinput).to₂
    have hout : Primrec₂ fun
        (y : (X × List RationalBeliefState))
        (state : RationalBeliefState) =>
        some (y.2 ++ [state]) :=
      Primrec₂.option_some_iff.mpr
        (Primrec.list_concat.comp₂
          (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)
    have hinner : Primrec₂ fun (x : X) (past : List RationalBeliefState) =>
        (marketMakerSearchUpToTradeList
          (tradingFirmTradesFromStageTradeLists
            (decodedStageTable x.1.1) (rationalHistory past) x.2.1 ++
            hook x.2.1 (tradingFirmTradesFromStageTradeLists
              (decodedStageTable x.1.1) (rationalHistory past) x.2.1))
          x.2.1 past (marketMakerError x.2.1) x.1.2).bind fun state =>
            some (past ++ [state]) :=
      (Primrec.option_bind (hsearch.comp Primrec.fst Primrec.snd) hout).to₂
    exact (Primrec.option_bind (Primrec.snd.comp Primrec.snd) hinner).to₂
  have hrec : Primrec₂ fun (ctx : C) n =>
      enfPrefixFromTradeListsAtFuel (decodedStageTable ctx.1) hook ctx.2 n := by
    exact (Primrec.nat_rec hbase hstep).of_eq fun ctx n => by
      induction n with
      | zero => simp [enfPrefixFromTradeListsAtFuel]
      | succ n ih => simp [enfPrefixFromTradeListsAtFuel, ih]
  exact hrec.comp Primrec.fst Primrec.snd

end

private lemma enfPrefixFromStagesAtFuel_prim {E : EffectiveEnforcer}
    (hE : EffectiveEnforcerComputation E) :
    Primrec fun p : (List (Finset Sentence) × ℕ) × ℕ =>
      enfPrefixFromStagesAtFuel (decodedStageTable p.1.1) E p.1.2 p.2 :=
  (enfPrefixFromTradeListsAtFuel_prim hE.tradesComputable).of_eq fun p => by
    rw [enfPrefixFromTradeListsAtFuel_eq]

private lemma enfPrefixAtFuel_prim {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) {E : EffectiveEnforcer}
    (hE : EffectiveEnforcerComputation E) :
    Primrec₂ fun fuel n => enfPrefixAtFuel process E fuel n := by
  let X := ℕ × ℕ
  have hstages : Primrec fun x : X =>
      processStagePrefixAtFuel process x.1 x.2 :=
    (processStagePrefixAtFuel_primrec process).comp Primrec.fst Primrec.snd
  have hrun : Primrec₂ fun (x : X) (stages : List (Finset Sentence)) =>
      enfPrefixFromStagesAtFuel (decodedStageTable stages) E x.1 x.2 := by
    have hinput : Primrec fun z : X × List (Finset Sentence) =>
        (((z.2, z.1.1), z.1.2) : (List (Finset Sentence) × ℕ) × ℕ) :=
      ((Primrec.snd.pair (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp Primrec.fst))
    exact ((enfPrefixFromStagesAtFuel_prim hE).comp hinput).to₂
  exact ((Primrec.option_bind hstages hrun).to₂).of_eq fun fuel n => by rfl

section
attribute [local irreducible] Nat.sqrt enfEncodedQuoteAtFuel

private lemma enfEncodedQuoteAtFuel_prim {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) {E : EffectiveEnforcer}
    (hE : EffectiveEnforcerComputation E) :
    Primrec fun p : (ℕ × ℕ) × ℕ =>
      enfEncodedQuoteAtFuel process E p.1.1 p.1.2 p.2 := by
  let P := (ℕ × ℕ) × ℕ
  have hfuel : Primrec fun p : P => p.1.1 := Primrec.fst.comp Primrec.fst
  have hday : Primrec fun p : P => p.1.2 := Primrec.snd.comp Primrec.fst
  have hdaySucc : Primrec fun p : P => p.1.2 + 1 :=
    Primrec.nat_add.comp hday (Primrec.const 1)
  have hprefix : Primrec fun p : P =>
      enfPrefixAtFuel process E p.1.1 (p.1.2 + 1) :=
    (enfPrefixAtFuel_prim process hE).comp hfuel hdaySucc
  let Y := P × List RationalBeliefState
  have hlookup : Primrec fun y : Y => y.2[y.1.1.2]? :=
    Primrec.list_getElem?.comp Primrec.snd (hday.comp Primrec.fst)
  have hfinish : Primrec₂ fun (y : Y) (state : RationalBeliefState) =>
      some (match Encodable.decode (α := Sentence) y.1.2 with
        | some phi => state.quote phi
        | none => 0) := by
    let Z := Y × RationalBeliefState
    have hdecode : Primrec fun z : Z =>
        Encodable.decode (α := Sentence) z.1.1.2 :=
      (Primrec.decode : Primrec fun n : ℕ =>
        Encodable.decode (α := Sentence) n).comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hquote : Primrec₂ fun (z : Z) (phi : Sentence) => z.2.quote phi :=
      rationalBeliefStateQuote_primrec.comp₂ (Primrec.snd.comp₂ Primrec₂.left)
        Primrec₂.right
    have hcase : Primrec fun z : Z =>
        match Encodable.decode (α := Sentence) z.1.1.2 with
        | some phi => z.2.quote phi
        | none => 0 :=
      (Primrec.option_casesOn hdecode (Primrec.const (0 : ℚ)) hquote).of_eq
        fun z => by cases Encodable.decode (α := Sentence) z.1.1.2 <;> rfl
    exact (Primrec.option_some.comp hcase).to₂
  exact ((Primrec.option_bind hprefix
    (Primrec.option_bind hlookup hfinish).to₂).of_eq fun p => by
      unfold enfEncodedQuoteAtFuel
      rfl)

end

section
attribute [local irreducible] Nat.sqrt enfEncodedQuoteNatAtFuel

private lemma enfEncodedQuoteNatAtFuel_prim {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) {E : EffectiveEnforcer}
    (hE : EffectiveEnforcerComputation E) :
    Primrec₂ (enfEncodedQuoteNatAtFuel process E) := by
  let X := ℕ × ℕ
  have hleft : Primrec fun p : X => p.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hright : Primrec fun p : X => p.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hinput : Primrec fun p : X =>
      (((p.2, p.1.unpair.1), p.1.unpair.2) : (ℕ × ℕ) × ℕ) :=
    (Primrec.snd.pair hleft).pair hright
  have hquote : Primrec fun p : X =>
      enfEncodedQuoteAtFuel process E p.2 p.1.unpair.1 p.1.unpair.2 :=
    (enfEncodedQuoteAtFuel_prim process hE).comp hinput
  have hencode : Primrec₂ fun (_p : X) (q : ℚ) => Encodable.encode q :=
    Primrec.encode.comp₂ Primrec₂.right
  exact ((Primrec.option_map hquote hencode).to₂).of_eq fun z fuel => by
    unfold enfEncodedQuoteNatAtFuel
    rfl

end

/-- **The bounded evaluator is computable.**  This is what
`EnforcedComputation.EnforcedBoundedEvaluatorCompiler` asked for. -/
def compiler {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
    {E : EffectiveEnforcer} (hE : EffectiveEnforcerComputation E) :
    EnforcedBoundedEvaluatorCompiler process E where
  computable := (enfEncodedQuoteNatAtFuel_prim process hE).to_comp

/-- **The modified market is computable, unconditionally in the effective data.** -/
theorem computableMarket {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) {E : EffectiveEnforcer}
    (hE : EffectiveEnforcerComputation E) :
    ComputableMarket (history DP (E.adaptive DP)) :=
  (compiler process hE).toComputableMarket

/-- **Traderized deduction with an effective enforcer is a logical inductor**, in the
source's original sense, with no computability premise at all. -/
theorem isLogicalInductor {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) {E : EffectiveEnforcer}
    (hE : EffectiveEnforcerComputation E)
    (hday : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      0 ≤ ((realizedEnforcer DP (E.adaptive DP)).strat n).value
        (history DP (E.adaptive DP)) v.payout) :
    IsLogicalInductor (history DP (E.adaptive DP)) DP :=
  isLogicalInductor_of_compiler_of_worldInclusive process E (compiler process hE) hday

end Workspace.Normativity.Contrib.EnforcedCompiler

#print axioms Workspace.Normativity.Contrib.EnforcedCompiler.enfPrefixFromTradeListsAtFuel_eq
#print axioms Workspace.Normativity.Contrib.EnforcedCompiler.compiler
#print axioms Workspace.Normativity.Contrib.EnforcedCompiler.computableMarket
#print axioms Workspace.Normativity.Contrib.EnforcedCompiler.isLogicalInductor
