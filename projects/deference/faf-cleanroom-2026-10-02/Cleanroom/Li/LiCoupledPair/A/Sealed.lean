import Cleanroom.Li.LiCoupledPair.Defs
import Cleanroom.Li.LiCoupledPair.A.Joint

/-!
# `li-coupled-pair` · A/Sealed: the sealed-sibling system by an `A`-side recursion on the day
(T4.3, the unconditional part)

The sealed-sibling system ([[frozen-deliberation-deference-v6]] §3–§5) has three kinds of market on
one clock: `A` over `DPA0 ⊕ (contract ledger)`, `H⁺` over `base ⊕ (full quote ledger of A)`, and the
family `H^{[N]}` over `base ⊕ Q^{<N}` (the quote ledger **frozen** at day `N`). The circularity is
`Y ↔ a`: the contract `C_n` settles, at stage `σ n`, to `Y n := H^{[n]}_{F n}(P^{(n)})`, the sibling
`n`'s exact day-`F n` quote of the contract sentence — and sibling `n` reads `A`'s table `a`, which
is `A`'s prices, which depend on `A`'s process, which carries the settled `Y`.

**Only `A`'s side needs a recursion.** The siblings and `H⁺` read a *fixed* table; only `A`'s stage
`t` reads back (`Y k` for `σ.e k ≤ t`). And `Y k` depends on `A`'s states at days `< k` only:
sibling `k`'s process is frozen at day `k`, so it never reads `a j m` for `m ≥ k`
(`siblingSchedule_mem_iff`); with `k < F k < σ.e k ≤ t` (the `DeferralFunction` and `F_lt_σ`),
every `Y k` that `A`'s stage `t` needs is a function of `A`'s states at days `< k < t`. So
`sealedDay` is `A/Joint.lean`'s `jointDay` with one side: by strong recursion on the day it computes
`A`'s stage (the contract ledger read off `A`'s past states, each `Y k` by running FAF's LIA over
sibling `k`'s frozen process to day `F k`), then `A`'s state by FAF's own day step (`MarketMaker` of
`TradingFirmAtFromStages` against the stage table so far). No Brouwer step beyond FAF's own.

The payoff, as in `A/Joint.lean`, is the **identification**: with `A`'s table `aS j n := sA n
.quote (quoted j n)` read off the recursion and `Y n := liaQuote (siblingProcess base aS e n) (F n)
(contract n)` (the sibling's exact quote, no grid rounding), `A`'s process of record
`ledgerProcess DPA0 (fun _ n => Y n) (fun _ => σ)` has the recursion's stages (`sealedDay_d_eq`, via
`siblingQuote_congr`: sibling `k`'s quote depends on the table at days `< k` only) and FAF's semantic
LIA over it is the recursion's state sequence (`sealedDay_states`). Every `SealedSiblingSystem` field
but the three inductor facts and the sibling-side world/determinacy facts (which need `A/Sibling.lean`
and go in `A/SealedInductor.lean`) is derived here, **unconditionally**. The inductor facts need
`ComputableDeductiveProcess` of the processes of record, i.e. computability of `aS` and `Y`, i.e. of
the recursion — `UniformLIAEvaluator` (`A/SealedInductor.lean`).

Scope: **two-way** — `A` reads the siblings (through `Y`), the siblings and `H⁺` read `A` (through
`aS`). This file imports `Construction.LIAComputation` only (through `A/Joint.lean`; plan §0.5):
no compiler, no `paperDP`.
-/

namespace Cleanroom.Li.LiCoupledPair.A

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair

/-! ## The specification of a sealed-sibling system -/

/-- **The data of a sealed-sibling system** (everything but the markets and the tables): the two
base processes, the quoted and contract sentences, and the schedules with the two timing
constraints `(e j).e n < F n` (publication before the sibling's horizon) and `F n < σ.e n`
(settlement after the horizon), which with `n < F n` (`DeferralFunction.lt`) make the `A`-side
recursion well-founded: `Y k` is needed at stage `σ.e k > F k > k`, and depends on `A`'s days
`< k`. Scope: two-way.
Source: [[frozen-deliberation-deference-v6]] §3–§4 (anson-016/017); mandate T4.3
Kind: D
Fidelity: exact
Hyps: n/a -/
structure SealedSpec where
  /-- The weaker reasoner's base process (shared by `H⁺` and every sibling). -/
  base : DeductiveProcess
  /-- `A`'s base process. -/
  DPA0 : DeductiveProcess
  /-- Per-item publication schedules of `A`'s quotes into the `H`-side processes. -/
  e : ℕ → PublicationSchedule
  /-- The horizon `F`: sibling `n` is read at day `F n`. -/
  F : DeferralFunction
  /-- The settlement schedule of the contract into `A`'s process. -/
  σ : PublicationSchedule
  /-- Publication precedes the horizon. -/
  e_lt_F : ∀ j n, (e j).e n < F.f n
  /-- The horizon precedes settlement. -/
  F_lt_σ : ∀ n, F.f n < σ.e n
  /-- The quoted sentences: item `j`, day `n`. -/
  quoted : ℕ → ℕ → Sentence
  /-- The contract sentences `P^{(n)}`. -/
  contract : ℕ → Sentence

/-! ## The table, the contract and `A`'s stage read off `A`'s past states -/

/-- `A`'s quote table read off a list of `A`'s states: item `j`, day `n` ↦ the day-`n` entry's quote
of `quoted j n` (junk `emptyState` beyond the list, never reached at a day the recursion reads).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def sTable (S : SealedSpec) (past : List RationalBeliefState) (j n : ℕ) : ℚ :=
  (past.getD n emptyState).quote (S.quoted j n)

/-- The contract value read off `A`'s past states: sibling `k`'s exact day-`F k` quote of
`contract k`, where sibling `k` is FAF's LIA over `base ⊕ Q^{<k}` at the table read off the past.
Source: none: infrastructure (the corpus's `Y_n := H^{[n]}_{F(n)}(P^{(n)})`, anson-016)
Kind: D
Fidelity: n/a -/
noncomputable def sContract (S : SealedSpec) (past : List RationalBeliefState) (k : ℕ) : ℚ :=
  liaQuote (siblingProcess S.base (sTable S past) S.e k) (S.F.f k) (S.contract k)

/-- `A`'s stage `t` from `A`'s past states: `DPA0.D t` plus the contract ledger of `sContract` at
the settlement schedule (the stage of `li-quote-lane`'s `ledgerProcess`, one item).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def sStage (S : SealedSpec) (past : List RationalBeliefState) (t : ℕ) :
    Finset Sentence :=
  (ledgerProcess S.DPA0 (fun _ k => sContract S past k) (fun _ => S.σ)).D t

/-! ## The `A`-side recursion on the day -/

/-- One day of the sealed recursion: `(A's stage, A's state)`. A product, so that it is
`Primcodable` for the computability argument.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev SealedDay : Type := Finset Sentence × RationalBeliefState

/-- **The `A`-side recursion on the day** (T4.3): day `t` computes, from `A`'s days `< t`, `A`'s
stage `d` (the contract ledger, each `Y k` by running FAF's LIA over sibling `k`'s frozen process at
the table read off the past) and `A`'s state `s` (FAF's `MarketMaker` of the firm run against
`A`'s stage table so far). FAF's own day step with the stage table explicit, no fixed
`DeductiveProcess`; well-founded on the day. Scope: two-way.
Source: [[frozen-deliberation-deference-v6]] §4 (anson-017: "delay each published quote by one stage … the recursion is well-founded"); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037); mandate T4.3
Kind: D
Fidelity: exact (the source's recursion, at FAF's day step; the contract is the sibling's exact rational quote)
Hyps: n/a -/
noncomputable def sealedDay (S : SealedSpec) : ℕ → SealedDay
  | t =>
    let past := List.ofFn fun i : Fin t => (sealedDay S i).2
    let d := sStage S past t
    let tbl : ℕ → Finset Sentence := fun m => if _h : m < t then (sealedDay S m).1 else d
    let s := MarketMaker (TradingFirmAtFromStages tbl (rationalHistory past) t) past
      (marketMakerError t) (marketMakerError_pos t)
    (d, s)
termination_by t => t
decreasing_by all_goals first | exact i.isLt | exact _h

/-- `A`'s states on days `< t`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def sPast (S : SealedSpec) (t : ℕ) : List RationalBeliefState :=
  List.ofFn fun i : Fin t => (sealedDay S i).2

/-- `A`'s stage table as the day-`t` step sees it.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def sTbl (S : SealedSpec) (t : ℕ) : ℕ → Finset Sentence :=
  fun m => if _ : m < t then (sealedDay S m).1 else sStage S (sPast S t) t

/-- The recursion's stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sealedDay_d (S : SealedSpec) (t : ℕ) : (sealedDay S t).1 = sStage S (sPast S t) t := by
  rw [sealedDay]
  rfl

/-- The recursion's state.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sealedDay_s (S : SealedSpec) (t : ℕ) :
    (sealedDay S t).2 = MarketMaker (TradingFirmAtFromStages (sTbl S t)
      (rationalHistory (sPast S t)) t) (sPast S t) (marketMakerError t) (marketMakerError_pos t) := by
  rw [sealedDay]
  rfl

/-! ## The tables, processes and markets of record -/

/-- **`A`'s quote table of the sealed system:** `A`'s day-`n` quote of `quoted j n`, read off the
recursion. The table every sibling and `H⁺` reads.
Source: mandate T4.3
Kind: D
Fidelity: exact -/
noncomputable def aS (S : SealedSpec) (j n : ℕ) : ℚ := ((sealedDay S n).2).quote (S.quoted j n)

/-- **The settled values of the sealed system:** `Y n`, sibling `n`'s exact day-`F n` quote of
`contract n` over `base ⊕ Q^{<n}` at the table of record. No grid rounding (FAF quotes are exact
rationals; anson-2-014's flag).
Source: [[frozen-deliberation-deference-v6]] §3 (anson-016: `Y_n := H^{[n]}_{F(n)}(P^{(n)})`); mandate T4.3
Kind: D
Fidelity: variant: exact rational contract -/
noncomputable def sealedY (S : SealedSpec) (n : ℕ) : ℚ :=
  liaQuote (siblingProcess S.base (aS S) S.e n) (S.F.f n) (S.contract n)

/-- **`A`'s process of record:** `li-quote-lane`'s `ledgerProcess DPA0 (fun _ n => Y n) (fun _ => σ)` —
`A`'s base plus the contract ledger settled at `σ`.
Source: mandate T4.3
Kind: D
Fidelity: exact -/
noncomputable def sealedDPA (S : SealedSpec) : DeductiveProcess :=
  ledgerProcess S.DPA0 (fun _ n => sealedY S n) (fun _ => S.σ)

/-- **The market `A` of the sealed system:** FAF's LIA over `sealedDPA S`.
Source: mandate T4.3
Kind: D
Fidelity: exact -/
noncomputable def sealedA (S : SealedSpec) : History := liaHistory (sealedDPA S)

/-- **`H⁺`'s process of record:** `base ⊕ (the full quote ledger of A)` at the table of record.
Source: mandate T4.3
Kind: D
Fidelity: exact -/
noncomputable def sealedDPH (S : SealedSpec) : DeductiveProcess := ledgerProcess S.base (aS S) S.e

/-- **The market `H⁺` of the sealed system:** FAF's LIA over `sealedDPH S`.
Source: mandate T4.3
Kind: D
Fidelity: exact -/
noncomputable def sealedHplus (S : SealedSpec) : History := liaHistory (sealedDPH S)

/-- **The sealed-sibling family of the sealed system:** `H^{[N]}` over `base ⊕ Q^{<N}` at the table
of record (`siblingHistory`).
Source: mandate T4.3
Kind: D
Fidelity: exact -/
noncomputable abbrev sealedSib (S : SealedSpec) (N : ℕ) : History :=
  siblingHistory S.base (aS S) S.e N

/-! ## Sibling `k`'s quote depends on the table at days `< k` only -/

/-- Two tables agreeing at every day `< N` give the same frozen entry set at every stage.
Source: none: infrastructure (`siblingSchedule_mem_iff`: the frozen schedule never reads days `≥ N`)
Kind: L
Fidelity: n/a -/
lemma siblingEntries_toFinset_congr {a a' : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule} {N s : ℕ}
    (h : ∀ j n, n < N → a j n = a' j n) :
    (siblingEntries a e N s).toFinset = (siblingEntries a' e N s).toFinset := by
  ext x
  simp only [List.mem_toFinset, mem_siblingEntries, mem_ledgerEntries]
  constructor
  · rintro ⟨⟨n, j, c, hn, hj, hc, he, hd, rfl⟩, hday⟩
    rw [entryDay_ledgerEntry] at hday
    exact ⟨⟨n, j, c, hn, hj, hc, he, hd, by simp only [ledgerEntry, h j n hday]⟩,
      by rw [entryDay_ledgerEntry]; exact hday⟩
  · rintro ⟨⟨n, j, c, hn, hj, hc, he, hd, rfl⟩, hday⟩
    rw [entryDay_ledgerEntry] at hday
    exact ⟨⟨n, j, c, hn, hj, hc, he, hd, by simp only [ledgerEntry, h j n hday]⟩,
      by rw [entryDay_ledgerEntry]; exact hday⟩

/-- Two tables agreeing at every day `< N` give the same frozen process stage-for-stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma siblingProcess_D_congr {base : DeductiveProcess} {a a' : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} {N : ℕ} (h : ∀ j n, n < N → a j n = a' j n) (s : ℕ) :
    (siblingProcess base a e N).D s = (siblingProcess base a' e N).D s := by
  rw [siblingProcess_D, siblingProcess_D, siblingEntries_toFinset_congr h]

/-- Two processes with the same stages have the same LIA states (strong induction through
`liaStates_eq_marketMaker_fromStages`: the day-`n` step reads the stage table and the realized
past only).
Source: none: infrastructure (FAF `liaStates`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem liaStates_congr (DP DP' : DeductiveProcess) (h : ∀ m, DP.D m = DP'.D m) :
    ∀ n, liaStates DP n = liaStates DP' n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hpast : (List.ofFn fun i : Fin n => liaStates DP i) =
        List.ofFn fun i : Fin n => liaStates DP' i := by
      congr 1
      funext i
      exact ih i i.isLt
    rw [liaStates_eq_marketMaker_fromStages DP DP.D n (fun _ _ => rfl) _ rfl,
      liaStates_eq_marketMaker_fromStages DP' DP.D n (fun m _ => h m) _ hpast]

/-- **Sibling `N`'s quotes depend on the table at days `< N` only** — the frozen process never
mentions a later day, so two tables agreeing below `N` give the same `H^{[N]}` outright.
Source: [[frozen-deliberation-deference-v6]] §3 (anson-016: quotes of index `≥ N` are never injected); mandate T4.3 (handoff: the truncation lemma)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem siblingQuote_congr (base : DeductiveProcess) {a a' : ℕ → ℕ → ℚ}
    (e : ℕ → PublicationSchedule) (N : ℕ) (h : ∀ j n, n < N → a j n = a' j n) (m : ℕ)
    (φ : Sentence) :
    liaQuote (siblingProcess base a e N) m φ = liaQuote (siblingProcess base a' e N) m φ := by
  unfold liaQuote
  rw [liaStates_congr _ _ (siblingProcess_D_congr h) m]

/-! ## Identification of the stages -/

/-- Reading `A`'s past-state list at a day below its length gives that day's state.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma getD_sPast (S : SealedSpec) (t : ℕ) {m : ℕ} (hm : m < t) :
    (sPast S t).getD m emptyState = (sealedDay S m).2 := by
  unfold sPast
  rw [List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_ofFn]

/-- At a day `n < t`, the table read off `A`'s past is the table of record.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sTable_sPast (S : SealedSpec) (t j n : ℕ) (hn : n < t) :
    sTable S (sPast S t) j n = aS S j n := by
  unfold sTable aS
  rw [getD_sPast S t hn]

/-- At a day `k < t`, the contract value read off `A`'s past is the settled value of record
(sibling `k` reads days `< k < t` only, `siblingQuote_congr`).
Source: mandate T4.3 (handoff step 1)
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma sContract_sPast (S : SealedSpec) (t k : ℕ) (hk : k < t) :
    sContract S (sPast S t) k = sealedY S k := by
  unfold sContract sealedY
  exact siblingQuote_congr S.base S.e k (fun j n hn => sTable_sPast S t j n (lt_trans hn hk)) _ _

/-- **The recursion's stage is the stage of `A`'s process of record:** every `Y k` settled by
stage `t` (`σ.e k ≤ t`) has `k < F k < σ.e k ≤ t`, so it is read off `A`'s past correctly.
Source: mandate T4.3 (identification)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem sealedDay_d_eq (S : SealedSpec) (t : ℕ) : (sealedDay S t).1 = (sealedDPA S).D t := by
  rw [sealedDay_d]
  unfold sStage sealedDPA
  simp only [ledgerProcess_D]
  rw [ledgerEntries_toFinset_congr fun _ k hle =>
    sContract_sPast S t k (lt_of_lt_of_le (lt_trans (S.F.lt k) (S.F_lt_σ k)) hle)]

/-! ## Identification of the states -/

/-- **T4.3, identification (headline of this file): FAF's semantic LIA over `A`'s process of
record is the `A`-side recursion's state sequence.** Strong induction on the day: the realized past
is the recursion's past, the stage table the step sees agrees with the process on days `≤ t`
(`sealedDay_d_eq`), and FAF's day step is prefix-invariant (`liaStates_eq_marketMaker_fromStages`).
Scope: two-way.
Source: mandate T4.3 ("identify the components with `liaStates` of the final processes"); [[frozen-deliberation-deference-v6]] §4
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem sealedDay_states (S : SealedSpec) : ∀ t, liaStates (sealedDPA S) t = (sealedDay S t).2 := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    have hpast : (List.ofFn fun i : Fin t => liaStates (sealedDPA S) i) = sPast S t := by
      unfold sPast
      congr 1
      funext i
      exact ih i i.isLt
    have htbl : ∀ m, m ≤ t → sTbl S t m = (sealedDPA S).D m := by
      intro m hm
      unfold sTbl
      split_ifs with h
      · exact sealedDay_d_eq S m
      · have hmt : m = t := by omega
        subst hmt
        rw [← sealedDay_d, sealedDay_d_eq]
    rw [sealedDay_s]
    exact liaStates_eq_marketMaker_fromStages _ _ t htbl _ hpast.symm

/-! ## The `SealedSiblingSystem` fields, unconditionally (all but the inductor and sibling-side
facts) -/

/-- **`aS` is `A`'s prices** (`SealedSiblingSystem.a_eq`).
Source: mandate T4.3
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem sealed_a_eq (S : SealedSpec) (j n : ℕ) : (aS S j n : ℝ) = sealedA S n (S.quoted j n) := by
  unfold sealedA aS
  rw [liaHistory_eq_quote_cast]
  unfold liaQuote
  rw [sealedDay_states S n]

/-- **`Y n` is sibling `n`'s exact day-`F n` quote of the contract** (`SealedSiblingSystem.Y_eq`),
by definition.
Source: mandate T4.3
Kind: L
Fidelity: variant: exact rational contract
Hyps: (a) none -/
theorem sealedY_eq (S : SealedSpec) (n : ℕ) :
    sealedY S n = liaQuote (siblingProcess S.base (aS S) S.e n) (S.F.f n) (S.contract n) := rfl

/-- `aS` lies in `[0,1]` (it is a LIA price).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem aS_mem (S : SealedSpec) (j n : ℕ) : 0 ≤ aS S j n ∧ aS S j n ≤ 1 := by
  have h := liaHistory_range (sealedDPA S) n (S.quoted j n)
  have h' := sealed_a_eq S j n
  unfold sealedA at h'
  rw [← h'] at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- `Y` lies in `[0,1]` (it is a LIA quote).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sealedY_mem (S : SealedSpec) (n : ℕ) : 0 ≤ sealedY S n ∧ sealedY S n ≤ 1 := by
  have h := liaHistory_range (siblingProcess S.base (aS S) S.e n) (S.F.f n) (S.contract n)
  rw [liaHistory_eq_quote_cast] at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- **`A`'s contract LUV `C_n` is determined, in `A`'s process, at `Y n`**
(`SealedSiblingSystem.determinedA`).
Source: mandate T4.3
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem sealed_determinedA (S : SealedSpec) (n : ℕ) :
    LUV.DeterminedVia (ledgerLuv 0 n) (sealedDPA S) (sealedY S n) :=
  ledgerLuv_determinedVia S.DPA0 (fun _ n => sealedY S n) (fun _ => S.σ)
    (fun _ n => sealedY_mem S n) 0 n

/-- **`H⁺`'s ledger LUVs are determined at `A`'s prices** (`SealedSiblingSystem.determinedH`).
Source: mandate T4.3
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem sealed_determinedH (S : SealedSpec) (j n : ℕ) :
    LUV.DeterminedVia (ledgerLuv j n) (sealedDPH S) (aS S j n) :=
  ledgerLuv_determinedVia S.base (aS S) S.e (aS_mem S) j n

/-- **Every stage of `A`'s process has a consistent world** (`SealedSiblingSystem.hworldA`), for a
base free of family `3` and satisfiable.
Source: mandate T4.3
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem sealed_hworldA (S : SealedSpec)
    (hfree : ProcessFreeOf (ledgerSchedule (fun _ n => sealedY S n) (fun _ => S.σ)) S.DPA0)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (S.DPA0.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((sealedDPA S).D n) :=
  ledgerProcess_hworld hfree h

/-- **Every stage of `H⁺`'s process has a consistent world** (`SealedSiblingSystem.hworldH`).
Source: mandate T4.3
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem sealed_hworldH (S : SealedSpec) (hfree : ProcessFreeOf (ledgerSchedule (aS S) S.e) S.base)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (S.base.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((sealedDPH S).D n) :=
  ledgerProcess_hworld hfree h

end Cleanroom.Li.LiCoupledPair.A
