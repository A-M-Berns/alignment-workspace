import Cleanroom.Li.LiCoupledPair.Defs
import Cleanroom.Found.LiQuoteLane.Ledger
import LogicalInduction.Construction.LIAComputation

/-!
# `li-coupled-pair` · A/Joint: the two-way pair by one staggered recursion on the day (T5.1, the
unconditional part)

The two-way pair's processes are **jointly defined**: `A`'s stage `t` holds the ledger of `H`'s
realized day-`f n` expectations of `XH n` for `(σ j).e n ≤ t` (available, since
`f n < (σ j).e n ≤ t`), and `H`'s stage `t` holds the ledger of `A`'s day-`n` prices of
`quotedA j n` for `(e j).e n ≤ t` (available, including same-day `n = t`, since `A`'s day-`t`
state is computed first). `jointDay` is that recursion: by strong recursion on the day it produces
`((dA t, sA t), (dH t, sH t))` — `A`'s stage and state, then `H`'s — running FAF's own day step
(`MarketMaker` of `TradingFirmAtFromStages` against the explicit stage table built so far, the
form the bounded evaluator of `Construction/LIAComputation.lean` runs) with no fixed
`DeductiveProcess` in hand. The one-stage delay `f n < (σ j).e n` is what makes it staggered:
nothing at day `t` references a day-`t` price of the *other* market before that market's day-`t`
state exists, and **no Brouwer step** beyond FAF's own per-market one is needed — exactly
[[frozen-deliberation-deference-v6]] §4's remark ("delay each published quote by one stage …
the recursion is well-founded").

The payoff is the **identification**: with the tables read off the recursion,
`aA j n := sA n .quote (quotedA j n)` and `aH j n := 𝔼(sH (f n), XH n, f n)`, the two processes
are *literally* `li-quote-lane`'s `ledgerProcess DPA0 aH σ` and `ledgerProcess DPH0 aA e`
(`jointDay_dA_eq`, `jointDay_dH_eq`), and FAF's semantic LIA over each of them is the recursion's
state sequence (`jointDay_states`, through prefix invariance `liaStates_eq_marketMaker_fromStages`:
the firm on day `t` reads stages `≤ t` only). Hence `A := liaHistory (jointDPA P)` and
`H := liaHistory (jointDPH P)` satisfy every field of `TwoWayPair` **except** the two inductor
fields (`joint_aA_eq`, `joint_aH_eq`, `joint_hworldA/H`, `joint_determinedA/H`), unconditionally.
The inductor fields need `ComputableDeductiveProcess` of the joint processes, i.e. computability
of `aA`/`aH`, i.e. of the recursion — which is where FAF's private uniform evaluator enters
(`UniformLIAEvaluator`, `A/JointInductor.lean`).

Scope: **two-way, timed both ways.** This file imports `Construction.LIAComputation` only
(plan §0.5): no compiler, no `paperDP`.
-/

namespace Cleanroom.Li.LiCoupledPair.A

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair

/-! ## The specification of a two-way pair -/

/-- **The data of a two-way pair** (everything but the markets): the two base processes, what each
side reads of the other, the schedules, and the one timing constraint `f n < (σ j).e n` (payout
after the lookahead) that makes the joint recursion staggered. Scope: two-way.
Source: mandate T5.1; [[deference-in-logical-induction-v6]] §5.2 (root-deference-037: "delay each published quote by one stage")
Kind: D
Fidelity: exact
Hyps: n/a -/
structure TwoWaySpec where
  /-- `A`'s base process. -/
  DPA0 : DeductiveProcess
  /-- `H`'s base process. -/
  DPH0 : DeductiveProcess
  /-- What `H` reads of `A`. -/
  quotedA : ℕ → ℕ → Sentence
  /-- Publication schedules of `A`'s quotes into `H`'s process. -/
  e : ℕ → PublicationSchedule
  /-- What `A` reads of `H`: the LUVs whose day-`f n` expectations are published. -/
  XH : ℕ → LUV
  /-- The lookahead. -/
  f : DeferralFunction
  /-- Payout schedules of `H`'s realized expectations into `A`'s process. -/
  σ : ℕ → PublicationSchedule
  /-- Payout after the lookahead (the stagger). -/
  payout_after_lookahead : ∀ j n, f.f n < (σ j).e n

/-! ## Reading a state -/

/-- The empty belief state (quotes `0` everywhere): the default for list reads beyond the prefix,
which the recursion never reaches at a published entry.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def emptyState : RationalBeliefState :=
  ⟨[], by simp, fun _ h => absurd h (List.not_mem_nil)⟩

/-- The exact rational day-`day` expectation of a LUV read off a belief state: the average of the
state's quotes of the thresholds `i/(day+1)`, `i ≤ day` — FAF's `MarketComputation.expectQuoteAt`
with the state's `quote` in place of the program's.
Source: none: infrastructure (FAF `LUV.expect`, `MarketComputation.expectQuoteAt`)
Kind: D
Fidelity: exact -/
def stateExpect (B : RationalBeliefState) (X : LUV) (day : ℕ) : ℚ :=
  (∑ i ∈ Finset.range (day + 1), B.quote (X.gt ((i : ℚ) / ((day + 1 : ℕ) : ℚ)))) /
    ((day + 1 : ℕ) : ℚ)

/-- Reading the expectation off FAF's LIA state *is* the market's expectation (the analogue of
`expectQuoteAt_cast`).
Source: none: infrastructure (FAF `liaHistory_eq_quote_cast`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem stateExpect_cast (DP : DeductiveProcess) (X : LUV) (day : ℕ) :
    X.expect (liaHistory DP) day = (stateExpect (liaStates DP day) X day : ℝ) := by
  have hq : ∀ i : ℕ, liaHistory DP day (X.gt ((i : ℚ) / ((day + 1 : ℕ) : ℚ))) =
      (((liaStates DP day).quote (X.gt ((i : ℚ) / ((day + 1 : ℕ) : ℚ))) : ℚ) : ℝ) :=
    fun i => liaHistory_eq_quote_cast DP day _
  simp only [LUV.expect, LUV.expectApprox, stateExpect]
  rw [Rat.cast_div, Rat.cast_sum]
  simp only [hq]
  push_cast
  ring

/-! ## The tables and stages read off past states -/

/-- `H`'s realized-expectation table read off a list of `H`'s states: item `j`, day `n` ↦ the
day-`f n` expectation of `XH n` from the day-`f n` entry (junk `emptyState` beyond the list, never
reached at a published entry).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tableH (P : TwoWaySpec) (pastH : List RationalBeliefState) (_j n : ℕ) : ℚ :=
  stateExpect (pastH.getD (P.f.f n) emptyState) (P.XH n) (P.f.f n)

/-- `A`'s quote table read off a list of `A`'s states: item `j`, day `n` ↦ the day-`n` entry's
quote of `quotedA j n`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tableA (P : TwoWaySpec) (pastA : List RationalBeliefState) (j n : ℕ) : ℚ :=
  (pastA.getD n emptyState).quote (P.quotedA j n)

/-- `A`'s stage `t` from `H`'s states so far: `DPA0.D t` plus the ledger of `tableH` at the payout
schedules (the stage of `li-quote-lane`'s `ledgerProcess`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def stageA (P : TwoWaySpec) (pastH : List RationalBeliefState) (t : ℕ) : Finset Sentence :=
  (ledgerProcess P.DPA0 (tableH P pastH) P.σ).D t

/-- `H`'s stage `t` from `A`'s states so far: `DPH0.D t` plus the ledger of `tableA` at the
publication schedules.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def stageH (P : TwoWaySpec) (pastA : List RationalBeliefState) (t : ℕ) : Finset Sentence :=
  (ledgerProcess P.DPH0 (tableA P pastA) P.e).D t

/-! ## The staggered joint recursion -/

/-- One day of the joint recursion: `((A's stage, A's state), (H's stage, H's state))`. A product
(not a structure) so that it is `Primcodable` for the computability argument.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev JointDay : Type :=
  (Finset Sentence × RationalBeliefState) × (Finset Sentence × RationalBeliefState)

/-- **The staggered joint recursion on the day** (T5.1): day `t` computes, from the days `< t`,
`A`'s stage `dA` (from `H`'s past states), `A`'s state `sA` (FAF's `MarketMaker` of the firm run
against `A`'s stage table so far), then `H`'s stage `dH` (from `A`'s states *including* `sA`) and
`H`'s state `sH`. FAF's own day step, with the stage table explicit
(`TradingFirmAtFromStages`), no fixed `DeductiveProcess`; well-founded on the day. Scope: two-way.
Source: [[deference-in-logical-induction-v6]] §5.2 (root-deference-037); [[frozen-deliberation-deference-v6]] §4 (anson-017); `bli-found-liacomputation.md` §4 ("one well-founded recursion on the day computing states and stages together")
Kind: D
Fidelity: exact (the source's recursion, at FAF's day step)
Hyps: n/a -/
noncomputable def jointDay (P : TwoWaySpec) : ℕ → JointDay
  | t =>
    let pastA := List.ofFn fun i : Fin t => (jointDay P i).1.2
    let pastH := List.ofFn fun i : Fin t => (jointDay P i).2.2
    let dA := stageA P pastH t
    let tblA : ℕ → Finset Sentence := fun m => if _h : m < t then (jointDay P m).1.1 else dA
    let sA := MarketMaker (TradingFirmAtFromStages tblA (rationalHistory pastA) t) pastA
      (marketMakerError t) (marketMakerError_pos t)
    let dH := stageH P (pastA ++ [sA]) t
    let tblH : ℕ → Finset Sentence := fun m => if _h : m < t then (jointDay P m).2.1 else dH
    let sH := MarketMaker (TradingFirmAtFromStages tblH (rationalHistory pastH) t) pastH
      (marketMakerError t) (marketMakerError_pos t)
    ((dA, sA), (dH, sH))
termination_by t => t
decreasing_by all_goals first | exact i.isLt | exact _h

/-- `A`'s states on days `< t`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def pastA (P : TwoWaySpec) (t : ℕ) : List RationalBeliefState :=
  List.ofFn fun i : Fin t => (jointDay P i).1.2

/-- `H`'s states on days `< t`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def pastH (P : TwoWaySpec) (t : ℕ) : List RationalBeliefState :=
  List.ofFn fun i : Fin t => (jointDay P i).2.2

/-- `A`'s stage table as the day-`t` step sees it.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def tblA (P : TwoWaySpec) (t : ℕ) : ℕ → Finset Sentence :=
  fun m => if _ : m < t then (jointDay P m).1.1 else stageA P (pastH P t) t

/-- `H`'s stage table as the day-`t` step sees it.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def tblH (P : TwoWaySpec) (t : ℕ) : ℕ → Finset Sentence :=
  fun m => if _ : m < t then (jointDay P m).2.1 else
    stageH P (pastA P t ++ [MarketMaker (TradingFirmAtFromStages (tblA P t)
      (rationalHistory (pastA P t)) t) (pastA P t) (marketMakerError t) (marketMakerError_pos t)]) t

/-- The recursion's `A`-stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem jointDay_dA (P : TwoWaySpec) (t : ℕ) : (jointDay P t).1.1 = stageA P (pastH P t) t := by
  rw [jointDay]
  rfl

/-- The recursion's `A`-state.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem jointDay_sA (P : TwoWaySpec) (t : ℕ) :
    (jointDay P t).1.2 = MarketMaker (TradingFirmAtFromStages (tblA P t)
      (rationalHistory (pastA P t)) t) (pastA P t) (marketMakerError t) (marketMakerError_pos t) := by
  rw [jointDay]
  rfl

/-- The recursion's `H`-stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem jointDay_dH (P : TwoWaySpec) (t : ℕ) :
    (jointDay P t).2.1 = stageH P (pastA P t ++ [(jointDay P t).1.2]) t := by
  rw [jointDay_sA]
  rw [jointDay]
  rfl

/-- The recursion's `H`-state.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem jointDay_sH (P : TwoWaySpec) (t : ℕ) :
    (jointDay P t).2.2 = MarketMaker (TradingFirmAtFromStages (tblH P t)
      (rationalHistory (pastH P t)) t) (pastH P t) (marketMakerError t) (marketMakerError_pos t) := by
  rw [jointDay]
  rfl

/-! ## The tables and processes of record -/

/-- **`A`'s published table of the two-way pair:** `A`'s day-`n` quote of `quotedA j n`, read off
the recursion.
Source: mandate T5.1
Kind: D
Fidelity: exact -/
noncomputable def aA (P : TwoWaySpec) (j n : ℕ) : ℚ := ((jointDay P n).1.2).quote (P.quotedA j n)

/-- **`H`'s realized-expectation table of the two-way pair:** `H`'s day-`f n` expectation of
`XH n`, read off the recursion.
Source: mandate T5.1
Kind: D
Fidelity: exact -/
noncomputable def aH (P : TwoWaySpec) (_j n : ℕ) : ℚ :=
  stateExpect ((jointDay P (P.f.f n)).2.2) (P.XH n) (P.f.f n)

/-- **`A`'s process of the two-way pair:** `li-quote-lane`'s `ledgerProcess DPA0 aH σ` at the
recursion's table — `A`'s base plus the ledger of `H`'s realized expectations.
Source: mandate T5.1
Kind: D
Fidelity: exact -/
noncomputable def jointDPA (P : TwoWaySpec) : DeductiveProcess := ledgerProcess P.DPA0 (aH P) P.σ

/-- **`H`'s process of the two-way pair:** `ledgerProcess DPH0 aA e` at the recursion's table.
Source: mandate T5.1
Kind: D
Fidelity: exact -/
noncomputable def jointDPH (P : TwoWaySpec) : DeductiveProcess := ledgerProcess P.DPH0 (aA P) P.e

/-- **The market `A` of the two-way pair:** FAF's LIA over `jointDPA P`.
Source: mandate T5.1
Kind: D
Fidelity: exact -/
noncomputable def jointA (P : TwoWaySpec) : History := liaHistory (jointDPA P)

/-- **The market `H` of the two-way pair:** FAF's LIA over `jointDPH P`.
Source: mandate T5.1
Kind: D
Fidelity: exact -/
noncomputable def jointH (P : TwoWaySpec) : History := liaHistory (jointDPH P)

/-! ## Identification of the stages -/

/-- Reading the past-state list at a day below its length gives that day's state.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma getD_pastH (P : TwoWaySpec) (t : ℕ) {m : ℕ} (hm : m < t) :
    (pastH P t).getD m emptyState = (jointDay P m).2.2 := by
  unfold pastH
  rw [List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_ofFn]

/-- Reading `A`'s past-state list at a day below its length gives that day's state.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma getD_pastA (P : TwoWaySpec) (t : ℕ) {m : ℕ} (hm : m < t) :
    (pastA P t).getD m emptyState = (jointDay P m).1.2 := by
  unfold pastA
  rw [List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_ofFn]

/-- At a published entry (`f n < t`), the table read off `H`'s past is the table of record.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableH_pastH (P : TwoWaySpec) (t j n : ℕ) (hn : P.f.f n < t) :
    tableH P (pastH P t) j n = aH P j n := by
  unfold tableH aH
  rw [getD_pastH P t hn]

/-- At a published entry (`n ≤ t`), the table read off `A`'s past extended by its day-`t` state is
the table of record.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableA_pastA_succ (P : TwoWaySpec) (t j n : ℕ) (hn : n ≤ t) :
    tableA P (pastA P t ++ [(jointDay P t).1.2]) j n = aA P j n := by
  unfold tableA aA
  rcases lt_or_eq_of_le hn with h | rfl
  · rw [List.getD_append _ _ _ _ (by simp [pastA]; omega), getD_pastA P t h]
  · rw [List.getD_append_right _ _ _ _ (by simp [pastA])]
    simp [pastA]

/-- Two tables agreeing at every published entry give the same ledger stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ledgerEntries_toFinset_congr {a a' : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule} {s : ℕ}
    (h : ∀ j n, (e j).e n ≤ s → a j n = a' j n) :
    (ledgerEntries a e s).toFinset = (ledgerEntries a' e s).toFinset := by
  ext x
  simp only [List.mem_toFinset, mem_ledgerEntries]
  constructor
  · rintro ⟨n, j, c, hn, hj, hc, he, hd, rfl⟩
    exact ⟨n, j, c, hn, hj, hc, he, hd, by simp only [ledgerEntry, h j n he]⟩
  · rintro ⟨n, j, c, hn, hj, hc, he, hd, rfl⟩
    exact ⟨n, j, c, hn, hj, hc, he, hd, by simp only [ledgerEntry, h j n he]⟩

/-- **The recursion's `A`-stage is the stage of `A`'s process of record** (the stagger
`f n < (σ j).e n` makes every published entry readable from `H`'s past).
Source: mandate T5.1 (identification)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem jointDay_dA_eq (P : TwoWaySpec) (t : ℕ) : (jointDay P t).1.1 = (jointDPA P).D t := by
  rw [jointDay_dA]
  unfold stageA jointDPA
  simp only [ledgerProcess_D]
  rw [ledgerEntries_toFinset_congr fun j n hle =>
    tableH_pastH P t j n (lt_of_lt_of_le (P.payout_after_lookahead j n) hle)]

/-- **The recursion's `H`-stage is the stage of `H`'s process of record** (same-day publication
is fine: `A`'s day-`t` state is already in hand).
Source: mandate T5.1 (identification)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem jointDay_dH_eq (P : TwoWaySpec) (t : ℕ) : (jointDay P t).2.1 = (jointDPH P).D t := by
  rw [jointDay_dH]
  unfold stageH jointDPH
  simp only [ledgerProcess_D]
  rw [ledgerEntries_toFinset_congr fun j n hle =>
    tableA_pastA_succ P t j n (le_trans ((P.e j).le n) hle)]

/-! ## Identification of the states -/

/-- One-step unfolding of FAF's recursion in explicit-stage-table form: the day-`t` state is the
market maker's answer to the firm run against any table agreeing with the process on days `≤ t`,
against the realized past.
Source: none: infrastructure (FAF `liaStates`, `TradingFirmAtFromStages_eq_of_eq_prefix`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem liaStates_eq_marketMaker_fromStages (DP : DeductiveProcess) (D : ℕ → Finset Sentence)
    (t : ℕ) (hD : ∀ m, m ≤ t → D m = DP.D m) (past : List RationalBeliefState)
    (hpast : past = List.ofFn fun i : Fin t => liaStates DP i) :
    liaStates DP t = MarketMaker (TradingFirmAtFromStages D (rationalHistory past) t) past
      (marketMakerError t) (marketMakerError_pos t) := by
  rw [liaStates]
  subst hpast
  show MarketMaker (TradingFirmAt DP _ t) _ _ _ = _
  rw [TradingFirmAtFromStages_eq_of_eq_prefix DP D _ t hD]

/-- **T5.1, identification (headline of this file): FAF's semantic LIA over each process of record
is the joint recursion's state sequence.** Strong induction on the day: the realized pasts are
the recursion's pasts, the stage tables the step sees agree with the processes on days `≤ t`
(`jointDay_dA_eq`, `jointDay_dH_eq`), and FAF's day step is prefix-invariant
(`liaStates_eq_marketMaker_fromStages`). Scope: two-way.
Source: mandate T5.1 ("prove `liaStates DPA t = stateA t` and `liaStates DPH t = stateH t`"); [[deference-in-logical-induction-v6]] §5.2
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem jointDay_states (P : TwoWaySpec) :
    ∀ t, liaStates (jointDPA P) t = (jointDay P t).1.2 ∧
      liaStates (jointDPH P) t = (jointDay P t).2.2 := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    have hpastA : (List.ofFn fun i : Fin t => liaStates (jointDPA P) i) = pastA P t := by
      unfold pastA
      congr 1
      funext i
      exact (ih i i.isLt).1
    have hpastH : (List.ofFn fun i : Fin t => liaStates (jointDPH P) i) = pastH P t := by
      unfold pastH
      congr 1
      funext i
      exact (ih i i.isLt).2
    have htblA : ∀ m, m ≤ t → tblA P t m = (jointDPA P).D m := by
      intro m hm
      unfold tblA
      split_ifs with h
      · exact jointDay_dA_eq P m
      · have hmt : m = t := by omega
        subst hmt
        rw [← jointDay_dA, jointDay_dA_eq]
    have htblH : ∀ m, m ≤ t → tblH P t m = (jointDPH P).D m := by
      intro m hm
      unfold tblH
      split_ifs with h
      · exact jointDay_dH_eq P m
      · have hmt : m = t := by omega
        subst hmt
        rw [← jointDay_sA, ← jointDay_dH, jointDay_dH_eq]
    exact ⟨by rw [jointDay_sA]; exact liaStates_eq_marketMaker_fromStages _ _ t htblA _ hpastA.symm,
      by rw [jointDay_sH]; exact liaStates_eq_marketMaker_fromStages _ _ t htblH _ hpastH.symm⟩

/-! ## The `TwoWayPair` fields, unconditionally (all but the two inductor fields) -/

/-- **`aA` is `A`'s prices** (`TwoWayPair.aA_eq`).
Source: mandate T5.1
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem joint_aA_eq (P : TwoWaySpec) (j n : ℕ) : (aA P j n : ℝ) = jointA P n (P.quotedA j n) := by
  unfold jointA aA
  rw [liaHistory_eq_quote_cast]
  unfold liaQuote
  rw [(jointDay_states P n).1]

/-- **`aH` is `H`'s realized day-`f n` expectation of `XH n`** (`TwoWayPair.aH_eq`).
Source: mandate T5.1
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem joint_aH_eq (P : TwoWaySpec) (j n : ℕ) :
    (aH P j n : ℝ) = (P.XH n).expect (jointH P) (P.f.f n) := by
  unfold jointH aH
  rw [stateExpect_cast, (jointDay_states P (P.f.f n)).2]

/-- `aA` lies in `[0,1]` (it is a LIA price).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem aA_mem (P : TwoWaySpec) (j n : ℕ) : 0 ≤ aA P j n ∧ aA P j n ≤ 1 := by
  have h := liaHistory_range (jointDPA P) n (P.quotedA j n)
  have h' := joint_aA_eq P j n
  unfold jointA at h'
  rw [← h'] at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- `aH` lies in `[0,1]` (it is an expectation of a market with prices in `[0,1]`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem aH_mem (P : TwoWaySpec) (j n : ℕ) : 0 ≤ aH P j n ∧ aH P j n ≤ 1 := by
  have h := LUV.expect_mem_Icc (liaHistory (jointDPH P)) (P.f.f n) (P.XH n)
    (fun s => liaHistory_range _ _ s)
  have h' := joint_aH_eq P j n
  unfold jointH at h'
  rw [← h'] at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- **`A`'s ledger LUVs are determined at `H`'s realized expectations** (`TwoWayPair.determinedA`).
Source: mandate T5.1
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem joint_determinedA (P : TwoWaySpec) (j n : ℕ) :
    LUV.DeterminedVia (ledgerLuv j n) (jointDPA P) (aH P j n) :=
  ledgerLuv_determinedVia P.DPA0 (aH P) P.σ (aH_mem P) j n

/-- **`H`'s ledger LUVs are determined at `A`'s prices** (`TwoWayPair.determinedH`).
Source: mandate T5.1
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem joint_determinedH (P : TwoWaySpec) (j n : ℕ) :
    LUV.DeterminedVia (ledgerLuv j n) (jointDPH P) (aA P j n) :=
  ledgerLuv_determinedVia P.DPH0 (aA P) P.e (aA_mem P) j n

/-- **Every stage of `A`'s process has a consistent world** (`TwoWayPair.hworldA`), for a base free
of family `3` and satisfiable.
Source: mandate T5.1
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem joint_hworldA (P : TwoWaySpec) (hfree : ProcessFreeOf (ledgerSchedule (aH P) P.σ) P.DPA0)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (P.DPA0.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((jointDPA P).D n) :=
  ledgerProcess_hworld hfree h

/-- **Every stage of `H`'s process has a consistent world** (`TwoWayPair.hworldH`).
Source: mandate T5.1
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem joint_hworldH (P : TwoWaySpec) (hfree : ProcessFreeOf (ledgerSchedule (aA P) P.e) P.DPH0)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (P.DPH0.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((jointDPH P).D n) :=
  ledgerProcess_hworld hfree h

/-- **The two-way pair, given the two inductor facts**: every other field of `TwoWayPair` is
derived here; the constructor takes only `IsLogicalInductor` of the two markets over the two
processes of record (what `A/JointInductor.lean` supplies under `UniformLIAEvaluator`).
Source: mandate T5.1
Kind: C
Fidelity: exact
Hyps: (a) none except the two inductor facts, which are the package's named-hypothesis rows -/
noncomputable def twoWayPair_of_inductors (P : TwoWaySpec)
    (hA : IsLogicalInductor (jointA P) (jointDPA P))
    (hH : IsLogicalInductor (jointH P) (jointDPH P))
    (hfreeA : ProcessFreeOf (ledgerSchedule (aH P) P.σ) P.DPA0)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (P.DPA0.D n))
    (hfreeH : ProcessFreeOf (ledgerSchedule (aA P) P.e) P.DPH0)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (P.DPH0.D n)) : TwoWayPair where
  DPA0 := P.DPA0
  DPH0 := P.DPH0
  quotedA := P.quotedA
  e := P.e
  XH := P.XH
  f := P.f
  σ := P.σ
  payout_after_lookahead := P.payout_after_lookahead
  A := jointA P
  H := jointH P
  aA := aA P
  aH := aH P
  aA_eq := joint_aA_eq P
  aH_eq := joint_aH_eq P
  A_inductor := hA
  H_inductor := hH
  hworldA := joint_hworldA P hfreeA hworldA
  hworldH := joint_hworldH P hfreeH hworldH
  determinedA := joint_determinedA P
  determinedH := joint_determinedH P

end Cleanroom.Li.LiCoupledPair.A
