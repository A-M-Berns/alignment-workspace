/-
# Computable schedule data

This file supplies the computable-level path used by the paper-facing API.  The backend
keeps its stronger primitive-recursive compiler facts; here the enforcement trade hook is
only required to be `Computable`, and the modified bounded recurrence is consequently
proved `Computable` rather than `Primrec`.
-/

import Workspace.Normativity.Contrib.DeductiveEffective

namespace TraderizedConstraints.Computability

open LogicalInduction
open Workspace.Normativity.Contrib.DeductiveEnforcement
open Workspace.Normativity.Contrib.EnforcedComputation
open Workspace.Normativity.Contrib.EnforcedCompiler
open Workspace.Normativity.Contrib.ProjectionForce
open Workspace.Normativity.Contrib.ProjectionCompiler
open Workspace.Normativity.Contrib.ProjectionCalibrated
open Workspace.Normativity.Contrib.ProjectionPrimrec
open Workspace.Normativity.Contrib.ProjectionEnforcer
open Workspace.Normativity.Contrib.EffectiveRepresentation
open Workspace.Normativity.Contrib.DeductiveEffective
open Workspace.Normativity.Contrib.ConstraintSchedule

/-- A computable enforcement-trade hook. -/
structure ComputableEnforcer (E : EffectiveEnforcer) where
  tradesComputable : Computable fun
    z : (ℕ × Finset Sentence) × List (EF × Sentence) =>
      E.trades z.1.1 z.1.2 z.2

section

attribute [local irreducible] Nat.sqrt enfPrefixFromTradeListsAtFuel
  tradingFirmTradesFromStageTradeLists marketMakerSearchUpToTradeList

/-- The bounded modified-LIA recurrence is computable from a computable enforcement
trade hook. -/
theorem prefixFromTradeLists_computable
    {hook : ℕ → Finset Sentence → List (EF × Sentence) → List (EF × Sentence)}
    (hhook : Computable fun z : (ℕ × Finset Sentence) × List (EF × Sentence) =>
      hook z.1.1 z.1.2 z.2) :
    Computable fun p : (List (Finset Sentence) × ℕ) × ℕ =>
      enfPrefixFromTradeListsAtFuel (decodedStageTable p.1.1) hook p.1.2 p.2 := by
  let C := List (Finset Sentence) × ℕ
  have hbase : Computable fun _ctx : C =>
      (some [] : Option (List RationalBeliefState)) :=
    Computable.const (some [])
  let step := fun (ctx : C)
      (ni : ℕ × Option (List RationalBeliefState)) =>
      ni.2.bind fun past =>
        (marketMakerSearchUpToTradeList
          (tradingFirmTradesFromStageTradeLists
            (decodedStageTable ctx.1) (rationalHistory past) ni.1 ++
            hook ni.1 (decodedStageTable ctx.1 ni.1)
              (tradingFirmTradesFromStageTradeLists
                (decodedStageTable ctx.1) (rationalHistory past) ni.1))
          ni.1 past (marketMakerError ni.1) ctx.2).bind fun state =>
            some (past ++ [state])
  have hstep : Computable₂ step := by
    let X := C × (ℕ × Option (List RationalBeliefState))
    have hfirm : Computable₂ fun (x : X) (past : List RationalBeliefState) =>
        tradingFirmTradesFromStageTradeLists
          (decodedStageTable x.1.1) (rationalHistory past) x.2.1 := by
      have hinput : Computable fun z : X × List RationalBeliefState =>
          (((z.1.1.1, z.2), z.1.2.1) :
            (List (Finset Sentence) × List RationalBeliefState) × ℕ) :=
        ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
          Computable.snd).pair
            (Computable.fst.comp (Computable.snd.comp Computable.fst))
      exact (tradingFirmTradesFromStageTradeLists_primrec.to_comp.comp hinput).to₂
    have hsearch : Computable₂ fun (x : X) (past : List RationalBeliefState) =>
        marketMakerSearchUpToTradeList
          (tradingFirmTradesFromStageTradeLists
            (decodedStageTable x.1.1) (rationalHistory past) x.2.1 ++
            hook x.2.1 (decodedStageTable x.1.1 x.2.1)
              (tradingFirmTradesFromStageTradeLists
                (decodedStageTable x.1.1) (rationalHistory past) x.2.1))
          x.2.1 past (marketMakerError x.2.1) x.1.2 := by
      have hord : Computable fun z : X × List RationalBeliefState =>
          tradingFirmTradesFromStageTradeLists
            (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1 :=
        hfirm.comp Computable.fst Computable.snd
      have hn : Computable fun z : X × List RationalBeliefState => z.1.2.1 :=
        Computable.fst.comp (Computable.snd.comp Computable.fst)
      have hpast : Computable fun z : X × List RationalBeliefState => z.2 :=
        Computable.snd
      have hstage : Computable fun z : X × List RationalBeliefState =>
          decodedStageTable z.1.1.1 z.1.2.1 :=
        Primrec.list_getD (∅ : Finset Sentence) |>.to_comp.comp
          (Computable.fst.comp (Computable.fst.comp Computable.fst)) hn
      have hhk : Computable fun z : X × List RationalBeliefState =>
          hook z.1.2.1 (decodedStageTable z.1.1.1 z.1.2.1)
            (tradingFirmTradesFromStageTradeLists
              (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1) :=
        hhook.comp ((hn.pair hstage).pair hord)
      have htrades : Computable fun z : X × List RationalBeliefState =>
          tradingFirmTradesFromStageTradeLists
            (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1 ++
            hook z.1.2.1 (decodedStageTable z.1.1.1 z.1.2.1)
              (tradingFirmTradesFromStageTradeLists
                (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1) :=
        Computable.list_append.comp hord hhk
      have hepsilon : Computable fun z : X × List RationalBeliefState =>
          marketMakerError z.1.2.1 :=
        marketMakerError_primrec.to_comp.comp hn
      have hfuel : Computable fun z : X × List RationalBeliefState => z.1.1.2 :=
        Computable.snd.comp (Computable.fst.comp Computable.fst)
      have hinput : Computable fun z : X × List RationalBeliefState =>
          ((((tradingFirmTradesFromStageTradeLists
              (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1 ++
              hook z.1.2.1 (decodedStageTable z.1.1.1 z.1.2.1)
                (tradingFirmTradesFromStageTradeLists
                  (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1),
            z.1.2.1), z.2), marketMakerError z.1.2.1), z.1.1.2) :=
        (((htrades.pair hn).pair hpast).pair hepsilon).pair hfuel
      exact (marketMakerSearchUpToTradeList_primrec.to_comp.comp hinput).to₂
    have hout : Computable₂ fun
        (y : X × List RationalBeliefState) (state : RationalBeliefState) =>
        some (y.2 ++ [state]) :=
      Computable.option_some_iff.mpr
        (Computable.list_concat.comp₂
          (Computable.snd.comp₂ (Primrec₂.left.to_comp)) (Primrec₂.right.to_comp))
    have hinner : Computable₂ fun (x : X) (past : List RationalBeliefState) =>
        (marketMakerSearchUpToTradeList
          (tradingFirmTradesFromStageTradeLists
            (decodedStageTable x.1.1) (rationalHistory past) x.2.1 ++
            hook x.2.1 (decodedStageTable x.1.1 x.2.1)
              (tradingFirmTradesFromStageTradeLists
                (decodedStageTable x.1.1) (rationalHistory past) x.2.1))
          x.2.1 past (marketMakerError x.2.1) x.1.2).bind fun state =>
            some (past ++ [state]) :=
      (Computable.option_bind (hsearch.comp Computable.fst Computable.snd) hout).to₂
    exact (Computable.option_bind
      (Computable.snd.comp Computable.snd) hinner).to₂
  have hstep' : Computable₂ fun (p : C × ℕ)
      (ni : ℕ × Option (List RationalBeliefState)) => step p.1 ni :=
    (hstep.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  have hrec : Computable₂ fun (ctx : C) n =>
      enfPrefixFromTradeListsAtFuel (decodedStageTable ctx.1) hook ctx.2 n := by
    refine (Computable.nat_rec Computable.snd (hbase.comp Computable.fst) hstep').to₂.of_eq ?_
    rintro ⟨ctx, n⟩
    induction n with
    | zero => simp [enfPrefixFromTradeListsAtFuel]
    | succ n ih => simp [enfPrefixFromTradeListsAtFuel, ih, step]
  exact hrec.comp Computable.fst Computable.snd

end

/-- The stage-table recurrence using an `EffectiveEnforcer` is computable. -/
theorem prefixFromStages_computable {E : EffectiveEnforcer} (hE : ComputableEnforcer E) :
    Computable fun p : (List (Finset Sentence) × ℕ) × ℕ =>
      enfPrefixFromStagesAtFuel (decodedStageTable p.1.1) E p.1.2 p.2 :=
  (prefixFromTradeLists_computable hE.tradesComputable).of_eq fun p => by
    rw [enfPrefixFromTradeListsAtFuel_eq]

/-- The bounded modified recurrence, including source-style deductive-stage decoding, is
computable. -/
theorem prefixAtFuel_computable {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) {E : EffectiveEnforcer}
    (hE : ComputableEnforcer E) :
    Computable₂ fun fuel n => enfPrefixAtFuel process E fuel n := by
  let X := ℕ × ℕ
  have hstages : Computable fun x : X => processStagePrefixAtFuel process x.1 x.2 :=
    (processStagePrefixAtFuel_primrec process).to_comp.comp Computable.fst Computable.snd
  have hrun : Computable₂ fun (x : X) (stages : List (Finset Sentence)) =>
      enfPrefixFromStagesAtFuel (decodedStageTable stages) E x.1 x.2 := by
    have hinput : Computable fun z : X × List (Finset Sentence) =>
        (((z.2, z.1.1), z.1.2) : (List (Finset Sentence) × ℕ) × ℕ) :=
      ((Computable.snd.pair (Computable.fst.comp Computable.fst)).pair
        (Computable.snd.comp Computable.fst))
    exact ((prefixFromStages_computable hE).comp hinput).to₂
  exact (Computable.option_bind hstages hrun).of_eq fun _ => rfl

section

attribute [local irreducible] Nat.sqrt enfEncodedQuoteAtFuel

private theorem encodedQuoteAtFuel_computable {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) {E : EffectiveEnforcer}
    (hE : ComputableEnforcer E) :
    Computable fun p : (ℕ × ℕ) × ℕ =>
      enfEncodedQuoteAtFuel process E p.1.1 p.1.2 p.2 := by
  let P := (ℕ × ℕ) × ℕ
  have hfuel : Computable fun p : P => p.1.1 := Computable.fst.comp Computable.fst
  have hday : Computable fun p : P => p.1.2 := Computable.snd.comp Computable.fst
  have hdaySucc : Computable fun p : P => p.1.2 + 1 :=
    Primrec.nat_add.to_comp.comp hday (Computable.const 1)
  have hprefix : Computable fun p : P => enfPrefixAtFuel process E p.1.1 (p.1.2 + 1) :=
    (prefixAtFuel_computable process hE).comp hfuel hdaySucc
  let Y := P × List RationalBeliefState
  have hlookup : Computable fun y : Y => y.2[y.1.1.2]? :=
    Computable.list_getElem?.comp Computable.snd (hday.comp Computable.fst)
  have hfinish : Computable₂ fun (y : Y) (state : RationalBeliefState) =>
      some (match Encodable.decode (α := Sentence) y.1.2 with
        | some phi => state.quote phi
        | none => 0) := by
    let Z := Y × RationalBeliefState
    have hdecode : Computable fun z : Z => Encodable.decode (α := Sentence) z.1.1.2 :=
      Computable.decode.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
    have hquote : Computable₂ fun (z : Z) (phi : Sentence) => z.2.quote phi :=
      rationalBeliefStateQuote_primrec.to_comp.comp₂
        (Computable.snd.comp₂ (Primrec₂.left.to_comp)) (Primrec₂.right.to_comp)
    have hcase : Computable fun z : Z =>
        match Encodable.decode (α := Sentence) z.1.1.2 with
        | some phi => z.2.quote phi
        | none => 0 :=
      (Computable.option_casesOn hdecode (Computable.const (0 : ℚ)) hquote).of_eq
        fun z => by cases Encodable.decode (α := Sentence) z.1.1.2 <;> rfl
    exact (Computable.option_some.comp hcase).to₂
  exact (Computable.option_bind hprefix
    (Computable.option_bind hlookup hfinish).to₂).of_eq fun p => by
      unfold enfEncodedQuoteAtFuel
      rfl

end


section


attribute [local irreducible] Nat.sqrt enfEncodedQuoteNatAtFuel

/-- The bounded evaluator used by the modified market is computable. -/
theorem encodedQuoteNatAtFuel_computable {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) {E : EffectiveEnforcer}
    (hE : ComputableEnforcer E) :
    Computable₂ (enfEncodedQuoteNatAtFuel process E) := by
  let X := ℕ × ℕ
  have hleft : Computable fun p : X => p.1.unpair.1 :=
    Computable.fst.comp (Computable.unpair.comp Computable.fst)
  have hright : Computable fun p : X => p.1.unpair.2 :=
    Computable.snd.comp (Computable.unpair.comp Computable.fst)
  have hinput : Computable fun p : X =>
      (((p.2, p.1.unpair.1), p.1.unpair.2) : (ℕ × ℕ) × ℕ) :=
    (Computable.snd.pair hleft).pair hright
  have hquote : Computable fun p : X =>
      enfEncodedQuoteAtFuel process E p.2 p.1.unpair.1 p.1.unpair.2 :=
    (encodedQuoteAtFuel_computable process hE).comp hinput
  have hencode : Computable₂ fun (_p : X) (q : ℚ) => Encodable.encode q :=
    Computable.encode.comp₂ (Primrec₂.right.to_comp)
  exact (Computable.option_map hquote hencode).of_eq fun p => by
    unfold enfEncodedQuoteNatAtFuel
    rfl

end


/-- Compile a computable enforcement hook to the backend's bounded-evaluator interface. -/
def compiler {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
    {E : EffectiveEnforcer} (hE : ComputableEnforcer E) :
    EnforcedBoundedEvaluatorCompiler process E :=
  ⟨encodedQuoteNatAtFuel_computable process hE⟩

/-- The modified LIA market is computable from a computable enforcement hook. -/
theorem computableMarket {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) {E : EffectiveEnforcer}
    (hE : ComputableEnforcer E) :
    ComputableMarket (history DP (E.adaptive DP)) :=
  (compiler process hE).toComputableMarket

/-! ## Computable schedule data -/

/-- Ordinary computability data for a projection schedule.  This deliberately parallels,
but does not weaken, the backend's primitive-recursive certificate. -/
structure ComputableProjectionSchedule (S : ProjectionSchedule) where
  coordsComputable : Computable S.coords
  tolComputable : Computable S.tol
  repsComputable : Computable₂ S.reps

private theorem calibratedIntensity_computable {alpha : Type} [Primcodable alpha]
    {day : alpha → Nat} {bound tol : alpha → Rat}
    (hday : Computable day) (hbound : Computable bound) (htol : Computable tol) :
    Computable fun a => calibratedIntensity (day a) (bound a) (tol a) := by
  have hres : Computable fun a => resistance (day a) (bound a) :=
    resistance_primrec.to_comp.comp hday hbound
  have hsq : Computable fun a => tol a * tol a :=
    ratMul_prim.to_comp.comp htol htol
  exact (ratDiv_prim.to_comp.comp hres hsq).of_eq fun _ => by
    simp only [calibratedIntensity]
    ring

private theorem repLookup_computable {alpha : Type} [Primcodable alpha]
    {coords : alpha → List Sentence} {reps : alpha → List Rep} {phi : alpha → Sentence}
    (dflt : Rep) (hcoords : Computable coords) (hreps : Computable reps)
    (hphi : Computable phi) :
    Computable fun a => (reps a).getD ((coords a).idxOf (phi a)) dflt := by
  have hidx : Computable fun a => (coords a).idxOf (phi a) :=
    Primrec.list_idxOf.to_comp.comp hphi hcoords
  exact (Primrec.list_getD dflt).to_comp.comp hreps hidx

private theorem coefEFof_computable {alpha : Type} [Primcodable alpha]
    {coords : alpha → List Sentence} {day : alpha → Nat} {lam : alpha → Rat}
    {rep : alpha → Rep} {phi : alpha → Sentence}
    (hcoords : Computable coords) (hday : Computable day) (hlam : Computable lam)
    (hrep : Computable rep) (hphi : Computable phi) :
    Computable fun a => coefEFof (coords a) (day a) (lam a) (rep a) (phi a) := by
  have hconst : Computable fun a => EF.const (lam a) := efConst_primrec.to_comp.comp hlam
  have hrepEF : Computable fun a => repEFof (coords a) (day a) (rep a) :=
    repEFof_primrec.to_comp.comp ((hcoords.pair hday).pair hrep)
  have hprice : Computable fun a => EF.price (phi a) (day a) :=
    efPrice_primrec.to_comp.comp hphi hday
  have hneg : Computable fun a => EF.neg (EF.price (phi a) (day a)) :=
    efNeg_primrec.to_comp.comp hprice
  have hadd : Computable fun a =>
      EF.add (repEFof (coords a) (day a) (rep a)) (EF.neg (EF.price (phi a) (day a))) :=
    efAdd_primrec.to_comp.comp hrepEF hneg
  exact (efMul_primrec.to_comp.comp hconst hadd).of_eq fun _ => rfl

private def mapState {alpha beta sigma : Type} (g : alpha → beta → sigma)
    (a : alpha) : List beta → Nat → List beta × List sigma
  | l, 0 => (l, [])
  | l, n + 1 =>
      match mapState g a l n with
      | ([], out) => ([], out)
      | (b :: rest, out) => (rest, out ++ [g a b])

private lemma mapState_eq {alpha beta sigma : Type} (g : alpha → beta → sigma)
    (a : alpha) (l : List beta) (n : Nat) :
    mapState g a l n = (l.drop n, (l.take n).map (g a)) := by
  induction n generalizing l with
  | zero => simp [mapState]
  | succ n ih =>
      rw [mapState, ih]
      cases h : l.drop n with
      | nil =>
          have hn : l.length ≤ n := List.drop_eq_nil_iff.mp h
          simp only [List.drop_eq_nil_iff.mpr (Nat.le_trans hn (Nat.le_succ n))]
          rw [(List.take_eq_self_iff l).mpr hn,
            (List.take_eq_self_iff l).mpr (Nat.le_trans hn (Nat.le_succ n))]
      | cons b rest =>
          have hn : n < l.length := by
            by_contra hnot
            have hnil : l.drop n = [] := List.drop_eq_nil_iff.mpr (Nat.le_of_not_gt hnot)
            simp [h] at hnil
          have hdrop : l.drop (n + 1) = rest := by
            rw [← List.drop_drop, h]
            rfl
          rw [hdrop]
          rw [List.take_add_one, List.getElem?_eq_getElem hn]
          simp only [Option.toList_some, List.map_append, List.map_singleton]
          have hb : l[n] = b := by
            have hbopt : l[n]? = some b := by
              simpa [List.head?_eq_getElem?, List.getElem?_drop] using congrArg List.head? h
            rw [List.getElem?_eq_getElem hn] at hbopt
            exact Option.some.inj hbopt
          rw [hb]

private theorem listMap_computable {alpha beta sigma : Type}
    [Primcodable alpha] [Primcodable beta] [Primcodable sigma]
    {f : alpha → List beta} {g : alpha → beta → sigma}
    (hf : Computable f) (hg : Computable₂ g) :
    Computable fun a => (f a).map (g a) := by
  have hlen : Computable fun a => (f a).length := Computable.list_length.comp hf
  have hbase : Computable fun a => (f a, ([] : List sigma)) :=
    hf.pair (Computable.const [])
  have hstep : Computable₂ fun (a : alpha) (p : Nat × (List beta × List sigma)) =>
      match p.2.1 with
      | [] => ([], p.2.2)
      | b :: rest => (rest, p.2.2 ++ [g a b]) := by
    let Z := alpha × (Nat × (List beta × List sigma))
    have hrest : Computable fun z : Z => z.2.2.1 :=
      Computable.fst.comp (Computable.snd.comp (Computable.snd))
    have htail : Computable fun z : Z => z.2.2.1.tail :=
      Primrec.list_tail.to_comp.comp hrest
    have hhead : Computable fun z : Z => z.2.2.1.head? :=
      Primrec.list_head?.to_comp.comp hrest
    have hout : Computable fun z : Z => z.2.2.2 :=
      Computable.snd.comp (Computable.snd.comp Computable.snd)
    have hnone : Computable fun z : Z => (([] : List beta), z.2.2.2) :=
      (Computable.const []).pair hout
    have hsome : Computable₂ fun (z : Z) (b : beta) =>
        (z.2.2.1.tail, z.2.2.2 ++ [g z.1 b]) := by
      have hg' : Computable₂ fun (z : Z) (b : beta) => g z.1 b :=
        hg.comp₂ (Computable.fst.comp₂ (Primrec₂.left.to_comp))
          (Primrec₂.right.to_comp)
      have hout' : Computable₂ fun (z : Z) (_b : beta) => z.2.2.2 :=
        (hout.comp₂ (Primrec₂.left.to_comp))
      have happ : Computable₂ fun (z : Z) (b : beta) => z.2.2.2 ++ [g z.1 b] :=
        Computable.list_concat.comp₂ hout' hg'
      exact (Computable.pair (htail.comp₂ (Primrec₂.left.to_comp)) happ).to₂
    refine ((Computable.option_casesOn hhead hnone hsome).of_eq
      (g := fun z : Z => match z.2.2.1 with
        | [] => ([], z.2.2.2)
        | b :: rest => (rest, z.2.2.2 ++ [g z.1 b])) ?_).to₂
    intro z
    rcases h : z.2.2.1 with _ | ⟨b, rest⟩ <;> simp
  have hstate : Computable fun a => mapState g a (f a) (f a).length := by
    exact (Computable.nat_rec hlen hbase hstep).of_eq fun a => by
      induction (f a).length with
      | zero => rfl
      | succ n ih =>
          simp only [mapState, ih]
          cases mapState g a (f a) n with
          | mk rest out => cases rest <;> rfl
  exact (Computable.snd.comp hstate).of_eq fun a => by
    rw [mapState_eq, List.take_length, List.drop_length]

/-- A computable schedule produces a genuinely computable enforcement-trade hook. -/
theorem scheduleTrades_computable (S : ProjectionSchedule)
    (hS : ComputableProjectionSchedule S) :
    Computable fun z : (Nat × Finset Sentence) × List (EF × Sentence) =>
      S.enforcer.trades z.1.1 z.1.2 z.2 := by
  let X := (Nat × Finset Sentence) × List (EF × Sentence)
  have hcoords : Computable fun z : X => S.coords z.1.1 :=
    hS.coordsComputable.comp (Computable.fst.comp Computable.fst)
  have hday : Computable fun z : X => z.1.1 :=
    Computable.fst.comp Computable.fst
  have hreps : Computable fun z : X => S.reps z.1.1 z.1.2 :=
    hS.repsComputable.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.fst)
  have hbound : Computable fun z : X => Strategy.tradeListAbsBound z.2 :=
    tradeListAbsBound_primrec.to_comp.comp Computable.snd
  have htol : Computable fun z : X => S.tol z.1.1 :=
    hS.tolComputable.comp hday
  have hlam : Computable fun z : X =>
      calibratedIntensity z.1.1 (Strategy.tradeListAbsBound z.2) (S.tol z.1.1) :=
    calibratedIntensity_computable hday hbound htol
  let Y := X × Sentence
  have hcoordsY : Computable fun y : Y => S.coords y.1.1.1 :=
    hcoords.comp Computable.fst
  have hdayY : Computable fun y : Y => y.1.1.1 := hday.comp Computable.fst
  have hlamY : Computable fun y : Y =>
      calibratedIntensity y.1.1.1 (Strategy.tradeListAbsBound y.1.2) (S.tol y.1.1.1) :=
    hlam.comp Computable.fst
  have hrepsY : Computable fun y : Y => S.reps y.1.1.1 y.1.1.2 :=
    hreps.comp Computable.fst
  have hphi : Computable fun y : Y => y.2 := Computable.snd
  have hrepY : Computable fun y : Y =>
      (S.reps y.1.1.1 y.1.1.2).getD ((S.coords y.1.1.1).idxOf y.2) S.dflt :=
    repLookup_computable S.dflt hcoordsY hrepsY hphi
  have hef : Computable fun y : Y =>
      coefEFof (S.coords y.1.1.1) y.1.1.1
        (calibratedIntensity y.1.1.1 (Strategy.tradeListAbsBound y.1.2) (S.tol y.1.1.1))
        ((S.reps y.1.1.1 y.1.1.2).getD ((S.coords y.1.1.1).idxOf y.2) S.dflt) y.2 :=
    coefEFof_computable hcoordsY hdayY hlamY hrepY hphi
  have hbody : Computable₂ fun (z : X) (phi : Sentence) =>
      (coefEFof (S.coords z.1.1) z.1.1
        (calibratedIntensity z.1.1 (Strategy.tradeListAbsBound z.2) (S.tol z.1.1))
        ((S.reps z.1.1 z.1.2).getD ((S.coords z.1.1).idxOf phi) S.dflt) phi, phi) :=
    (hef.pair hphi).to₂
  exact (listMap_computable hcoords hbody).of_eq fun _ => rfl

/-- The computable enforcement hook associated with a computable schedule. -/
def computableEnforcer (S : ProjectionSchedule) (hS : ComputableProjectionSchedule S) :
    ComputableEnforcer S.enforcer :=
  ⟨scheduleTrades_computable S hS⟩

/-- Ordinary computability data for a rational-polytope constraint schedule. -/
structure ComputableConstraintSchedule (C : RationalConstraintSchedule) where
  coordsComputable : Computable C.coords
  tolComputable : Computable C.tol
  vertsComputable : Computable C.vertexData

/-- The finite-data primitive-recursive projector compiler composes with ordinary
computable schedule data. -/
def projectionScheduleOfConstraints (C : RationalConstraintSchedule)
    (hC : ComputableConstraintSchedule C) :
    ComputableProjectionSchedule (C.schedule (effectiveRepresentation C)) where
  coordsComputable := hC.coordsComputable
  tolComputable := hC.tolComputable
  repsComputable := by
    have h : Computable fun n => compileOf (C.coords n) (C.vertexData n) :=
      compileOf_primrec.to_comp.comp hC.coordsComputable hC.vertsComputable
    exact (h.comp Computable.fst).to₂

/-- The deductive representation schedule is computable from ordinary computable fragment
and tolerance schedules, while reading each finite deductive stage from the recurrence. -/
def deductiveSchedule (coords : Nat → List Sentence)
    (nodup : ∀ n, (coords n).Nodup) (tol : Nat → Rat) (tol_pos : ∀ n, 0 < tol n)
    (hcoords : Computable coords) (htol : Computable tol) :
    ComputableProjectionSchedule
      (deductiveProjectionSchedule coords nodup tol tol_pos) where
  coordsComputable := hcoords
  tolComputable := htol
  repsComputable := by
    have h : Computable fun z : Nat × Finset Sentence =>
        deductiveReps z.2 (coords z.1) :=
      deductiveReps_primrec.to_comp.comp Computable.snd (hcoords.comp Computable.fst)
    exact h.to₂

end TraderizedConstraints.Computability

#print axioms TraderizedConstraints.Computability.prefixFromTradeLists_computable
#print axioms TraderizedConstraints.Computability.prefixAtFuel_computable
#print axioms TraderizedConstraints.Computability.encodedQuoteNatAtFuel_computable
#print axioms TraderizedConstraints.Computability.computableMarket
#print axioms TraderizedConstraints.Computability.scheduleTrades_computable
#print axioms TraderizedConstraints.Computability.projectionScheduleOfConstraints
#print axioms TraderizedConstraints.Computability.deductiveSchedule
