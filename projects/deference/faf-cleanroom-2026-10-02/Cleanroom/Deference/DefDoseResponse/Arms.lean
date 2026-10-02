import Cleanroom.Deference.DefDoseResponse.Defs
import Cleanroom.Li.LiProjection.Certificate
import Cleanroom.Li.LiProjection.LemmaA
import Cleanroom.Li.LiProjection.Marginal
import Cleanroom.Li.LiProjection.Underdetermination
import Cleanroom.Found.LiQuoteLane.Ledger
import Cleanroom.Found.LiQuoteLane.Computability
import LogicalInduction.Construction.LIACompiler

/-!
# `def-dose-response` · Arms: the design as FAF objects and non-attribution (T6)

The arms of `Defs.lean` as FAF markets: the exposure ledger is satisfiable, computable and
free of the protected atom; the arm's weight meets every hypothesis of `li-projection`'s Lemma A
(`project_isLogicalInductor`), so the arm is a logical inductor over its exposure ledger — **modulo
`li-projection`'s two OPEN `Complexity.FP` stream rewriters (section (A) of
`li-projection-open.txt`)**, which is the only thing any "arm is an inductor" conclusion in this
package rests on; and the arm prices every `u`-free sentence exactly as its base LIA
(`arm_restrict`). **`non_attribution`** (T2(e)'s content): on every ledger whose exposed
formative quotes are `v`, the content-steered arm and the content-blind twin with slope
`s = γ(v − ½)` are *the same market* — equality of `History`s, hence of every record either
produces — by the jump-target identity (∗) and `congrArg`. The zip's `non_attribution` quantified
over a schematic recursion `run step target init` whose `step` was an arbitrary function (zip
AUDIT §3.4); this one quantifies over the FAF markets `liaHistory` and `project` build.

**The confound** (§3(C), T2(e)'s evaluation consequence): `(γ, v)` and `s` are not separately
identified — `armWeight_confound` says two advisees of susceptibilities `γ, γ'` pushed to `v, v'`
with `γ(v − ½) = γ'(v' − ½)` jump to the same weight on every ledger.

Scope: **one-way** (the arms read a fixed committed stream `a`).

A note on the mandate's "check by `rfl` that `armBlind base s N c a = armBlind base s N c a'`":
that equation is **false** as a statement about markets — the blind arm's *base* is the LIA over
the exposure ledger, which records `c_n · a_n`, so the two blind arms sit on different ledgers.
What is true, and what the mandate means, is that the blind *weight* does not read the stream: the
type of `blindWeight s N c` has no stream argument. Recorded in the findings (F8).
-/

namespace Cleanroom.Deference.DefDoseResponse

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Li.LiProjection
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## The exposure ledger as a FAF process -/

/-- The exposure table is computable from a computable coin and a computable stream.
Source: mandate T6 ("`exposureTable c a` and the schedule computable — so `c` and `a` computable")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem exposureTable_computable {c : ℕ → Bool} {a : ℕ → ℚ} (hc : Computable c)
    (ha : Computable a) : Computable fun p : ℕ × ℕ => exposureTable c a p.1 p.2 := by
  have hc' : Computable fun p : ℕ × ℕ => c p.2 := hc.comp Computable.snd
  have ha' : Computable fun p : ℕ × ℕ => a p.2 := ha.comp Computable.snd
  have h0 : Computable fun p : ℕ × ℕ => (p.1 == 0) :=
    (Primrec.beq.comp Primrec.fst (Primrec.const 0)).to_comp
  have h1 : Computable fun p : ℕ × ℕ => (p.1 == 1) :=
    (Primrec.beq.comp Primrec.fst (Primrec.const 1)).to_comp
  have inner1 : Computable fun p : ℕ × ℕ => cond (c p.2) (a p.2) 0 :=
    Computable.cond hc' ha' (Computable.const 0)
  have inner2 : Computable fun p : ℕ × ℕ => cond (c p.2) (1 : ℚ) 0 :=
    Computable.cond hc' (Computable.const 1) (Computable.const 0)
  have inner3 : Computable fun p : ℕ × ℕ => cond (p.1 == 1) (cond (c p.2) (1 : ℚ) 0) 0 :=
    Computable.cond h1 inner2 (Computable.const 0)
  refine (Computable.cond h0 inner1 inner3).of_eq ?_
  intro p
  simp only [exposureTable]
  by_cases h0' : p.1 = 0 <;> by_cases h1' : p.1 = 1 <;> cases hcp : c p.2 <;>
    simp [h0', h1', Bool.cond_eq_ite]

/-- The arms' next-day schedule is computable.
Source: none: infrastructure (`li-quote-lane`'s `succSchedule_computable`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem armSchedule_computable :
    Computable fun p : ℕ × ℕ => (armSchedule p.1).e p.2 :=
  (Primrec.succ.comp Primrec.snd).to_comp

/-- **The exposure ledger is a computable deductive process** when the base, the coin and the
stream are (`li-quote-lane`'s `ledgerProcess_computable`).
Source: mandate T6 (`armProcess_computable`); [[dose-response]] §2.3
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem armProcess_computable {base : DeductiveProcess} (hbase : ComputableDeductiveProcess base)
    {c : ℕ → Bool} {a : ℕ → ℚ} (hc : Computable c) (ha : Computable a) :
    ComputableDeductiveProcess (armProcess base c a) :=
  ledgerProcess_computable hbase (exposureTable_computable hc ha) armSchedule_computable

/-- **Every stage of the exposure ledger is satisfiable** when the base is free of the ledger
family and satisfiable (`li-quote-lane`'s `ledgerProcess_hworld`) — the `hworld` every arm-side
headline carries.
Source: mandate T6 (`armProcess_hworld`); `li-quote-lane` T1.5
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem armProcess_hworld {base : DeductiveProcess} {c : ℕ → Bool} {a : ℕ → ℚ}
    (hfree : ProcessFreeOf (ledgerSchedule (exposureTable c a) armSchedule) base)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base c a).D n) :=
  ledgerProcess_hworld hfree h

/-- The same for a clean-room-free base (every `paperDP T`).
Source: mandate T6
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem armProcess_hworld_of_cleanroomFree {base : DeductiveProcess} (hcf : CleanroomFreeProcess base)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base.D n)) (c : ℕ → Bool) (a : ℕ → ℚ) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base c a).D n) :=
  armProcess_hworld (processFreeOf_ledgerSchedule_of_cleanroomFree hcf) h

/-- **The exposure ledger never mentions the protected atom** when the base does not
(`li-projection`'s `atomFreeProcess_ledgerProcess`): `u` stays fresh for every arm.
Source: mandate T6 (`armProcess_atomFree`); [[dose-response]] §2.1 ("no deductive process ever decides it")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem armProcess_atomFree {base : DeductiveProcess} (hbase : AtomFreeProcess protAtom base)
    (c : ℕ → Bool) (a : ℕ → ℚ) : AtomFreeProcess protAtom (armProcess base c a) :=
  atomFreeProcess_ledgerProcess 0 hbase

/-- **The arm's base is a logical inductor over the exposure ledger** (FAF's
`LIA_is_logical_inductor` at the computable ledger process).
Source: [[dose-response]] §6.2 ("run the standard base construction [LI 5.4.2]"); FAF `thm:lia`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem armBase_isLogicalInductor {base : DeductiveProcess} (hbase : ComputableDeductiveProcess base)
    {c : ℕ → Bool} {a : ℕ → ℚ} (hc : Computable c) (ha : Computable a) :
    IsLogicalInductor (armBase base c a) (armProcess base c a) :=
  LIA_is_logical_inductor _ (armProcess_computable hbase hc ha)

/-! ## The arm's weight meets Lemma A -/

/-- The arm's weight is e.c. (`MachineRatCodes`): a finite table and a constant
(`li-projection`'s `MachineRatCodes.ofFiniteTable`) — Lemma A's hypothesis (i). **What is
certified** (fidelity audit r1, N9): the certificate is a hard-coded table — the realized jump
value `response γ (testimony c a N)` as a *constant* for this ledger — not a program that reads
the day-`N` published data and computes the testimony from it. The Lean `def armWeight` is one
program on the ledger; its e.c. certificate is per-ledger. The note's Lemma A (i) ("computable
from day-`n`-published data by a `𝒞`-machine") is therefore matched at the level the inductor
theorem needs (`project_isLogicalInductor` consumes only `MachineRatCodes`), not as a
ledger-reading policy; `li-projection`'s `project_isLogicalInductor` docstring discloses the same.
Source: [[dose-response]] §6.1 Lemma A (i); mandate D3
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem armWeight_machineRatCodes (γ : ℚ) (N : ℕ) (c : ℕ → Bool) (a : ℕ → ℚ) :
    MachineRatCodes (armWeight γ N c a) :=
  MachineRatCodes.ofFiniteTable _ N (response γ (testimony c a N))
    (fun _ hn => armWeight_of_le γ N c a hn)

/-- The blind weight is e.c.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem blindWeight_machineRatCodes (s : ℚ) (N : ℕ) (c : ℕ → Bool) :
    MachineRatCodes (blindWeight s N c) :=
  MachineRatCodes.ofFiniteTable _ N (1 / 2 + s * realizedDose c N)
    (fun _ hn => blindWeight_of_le s N c hn)

/-- **T6 (headline). The arm is a logical inductor over its exposure ledger** — every hypothesis
of `li-projection`'s Lemma A discharged from the design: freshness of `u`
(`armProcess_atomFree`), the weight's range `[(1−γ)/2, 1 − (1−γ)/2]` with `(1−γ)/2 > 0`
(`armWeight_mem`, `γ < 1`), its e.c. certificate (`armWeight_machineRatCodes`) and the jump at
`N` (`armWeight_jump`), with the base inductor FAF's LIA (`armBase_isLogicalInductor`).
**Rests on `li-projection` (A)** — the two OPEN `FP` stream rewriters inside
`project_isLogicalInductor` — and on nothing else. Scope: one-way (a fixed stream `a`).
Source: [[dose-response]] §6.2 ("By Lemma A, `M(ledger)` is a logical inductor … for every ledger realization"); anson-048; anson-2-025 (A); anson-2-028/029 (the arms as a second N+ instance of Lemma A over a ledger process)
Kind: C
Fidelity: exact
Hyps: (a) all; rests on the OPEN rewriters through `project_isLogicalInductor` -/
theorem arm_isLogicalInductor {base : DeductiveProcess} (hbase : ComputableDeductiveProcess base)
    (hfree : AtomFreeProcess protAtom base) {γ : ℚ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (N : ℕ)
    {c : ℕ → Bool} {a : ℕ → ℚ} (hc : Computable c) (ha : Computable a)
    (hmem : ∀ n, 0 ≤ a n ∧ a n ≤ 1) :
    IsLogicalInductor (arm base γ N c a) (armProcess base c a) :=
  haveI := armBase_isLogicalInductor hbase hc ha
  project_isLogicalInductor (armBase base c a) (armProcess base c a) protAtom
    (armProcess_atomFree hfree c a) (armWeight γ N c a) ((1 - γ) / 2) (by linarith)
    (armWeight_mem γ hγ0.le N c a hmem) (armWeight_machineRatCodes γ N c a) N
    (armWeight_jump γ N c a)

/-- The content-blind twin is a logical inductor over the same ledger, for `|s| ≤ γ/2`,
`0 < γ < 1`. Rests on `li-projection` (A).
Source: [[dose-response]] §6.3 T2(e) ("`M̃` … identical to `M` except the jump target")
Kind: C
Fidelity: exact
Hyps: (a) all; rests on the OPEN rewriters through `project_isLogicalInductor` -/
theorem armBlind_isLogicalInductor {base : DeductiveProcess} (hbase : ComputableDeductiveProcess base)
    (hfree : AtomFreeProcess protAtom base) {s γ : ℚ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hs : |s| ≤ γ / 2) (N : ℕ) {c : ℕ → Bool} {a : ℕ → ℚ} (hc : Computable c) (ha : Computable a) :
    IsLogicalInductor (armBlind base s N c a) (armProcess base c a) :=
  haveI := armBase_isLogicalInductor hbase hc ha
  project_isLogicalInductor (armBase base c a) (armProcess base c a) protAtom
    (armProcess_atomFree hfree c a) (blindWeight s N c) ((1 - γ) / 2) (by linarith)
    (blindWeight_mem s γ hγ0.le hs N c) (blindWeight_machineRatCodes s N c) N
    (blindWeight_jump s N c)

/-! ## Restriction: the arm prices `u`-free sentences as its base -/

/-- **The arm prices every `u`-free sentence exactly as its base LIA**, every day
(`li-projection`'s `project_restrict`): the disposition on `u` costs nothing on the base language.
Source: [[dose-response]] §6.1 Lemma A ("restriction: `𝕡_n ↾ base = 𝕡̄_n` exactly")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem arm_restrict (base : DeductiveProcess) (γ : ℚ) (N : ℕ) (c : ℕ → Bool) (a : ℕ → ℚ) (n : ℕ)
    {φ : Sentence} (hφ : AtomFreeSentence protAtom φ) :
    arm base γ N c a n φ = armBase base c a n φ :=
  project_restrict _ _ _ _ hφ

/-- The arm prices every ledger threshold exactly as its base (the ledger atoms are family `3`,
the projection atom family `4`).
Source: [[dose-response]] §6.1 Lemma A (restriction)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem arm_restrict_ledgerLuv (base : DeductiveProcess) (γ : ℚ) (N : ℕ) (c : ℕ → Bool)
    (a : ℕ → ℚ) (n j m : ℕ) (r : ℚ) :
    arm base γ N c a n ((ledgerLuv j m).gt r) = armBase base c a n ((ledgerLuv j m).gt r) :=
  arm_restrict base γ N c a n (atomFreeSentence_ledgerLuv_gt 0 j m r)

/-! ## T2(e): non-attribution -/

/-- **T2(e), `non_attribution` (headline).** On every ledger `(c, a)` whose exposed formative
quotes are `v`, the content-steered arm `M(γ, N)` and the content-blind twin `M̃(s, N)` with
`s := γ(v − ½)` are **the same market**: equal as `History`s, so every record either produces —
every price, every expectation, every ledger it feeds — coincides. The two weight formulas agree
as numbers on every such ledger by (∗) (`jump_target_eq`), and the arm is `project` applied to the
weight (`congrArg`). Two different programs; one market on every ledger of this shape. Scope:
one-way.
Source: [[dose-response]] §6.3 T2(e) ("the system `(M̃, A_v)` produces the bit-for-bit identical joint record to `(M, A_v)`"); anson-2-025; anson-054
Kind: P
Fidelity: exact (the two arms are FAF markets, not a schematic recursion — zip AUDIT §3.4)
Hyps: (a) none -/
theorem non_attribution (base : DeductiveProcess) (γ : ℚ) {N : ℕ} (hN : 0 < N) {c : ℕ → Bool}
    {a : ℕ → ℚ} {v : ℚ} (hv : ∀ j < N, c j = true → a j = v) :
    arm base γ N c a = armBlind base (γ * (v - 1 / 2)) N c a := by
  unfold arm armBlind
  congr 1
  funext n
  unfold armWeight blindWeight
  split_ifs with h
  · rfl
  · exact jump_target_eq γ hN hv

/-- The blind weight reads nothing of the stream: stated as the (trivial) congruence that is all
the mandate's `rfl` check can mean — the weight is literally the same term for every stream.
Source: mandate T6 trap (i)
Kind: L
Fidelity: exact (the market-level equation `armBlind … a = armBlind … a'` is false — module docstring)
Hyps: (a) none -/
theorem armBlind_weight_streamFree (base : DeductiveProcess) (s : ℚ) (N : ℕ) (c : ℕ → Bool)
    (a a' : ℕ → ℚ) :
    armBlind base s N c a = project (armBase base c a) protAtom (blindWeight s N c) ∧
      armBlind base s N c a' = project (armBase base c a') protAtom (blindWeight s N c) :=
  ⟨rfl, rfl⟩

/-- **The susceptibility/push confound** (§3(C)): advisees of susceptibility `γ` and `γ'`, pushed
to `v` and `v'` on their exposed formative days, with `γ(v − ½) = γ'(v' − ½)`, have the same
weight sequence on any two ledgers with the same coin — `(γ, v)` and `(γ', v')` are not separately
identified from anything the arms do on `u`.
Source: [[dose-response]] §3 (C) ("the measured slope `s = γ(v − ½)` factors … into the advisor's push and the advisee's susceptibility"); §6.3 T2(e) alignment reading
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem armWeight_confound {N : ℕ} (hN : 0 < N) {c : ℕ → Bool} {a a' : ℕ → ℚ} {γ γ' v v' : ℚ}
    (hv : ∀ j < N, c j = true → a j = v) (hv' : ∀ j < N, c j = true → a' j = v')
    (h : γ' * (v' - 1 / 2) = γ * (v - 1 / 2)) :
    armWeight γ' N c a' = armWeight γ N c a := by
  funext n
  unfold armWeight
  split_ifs with hn
  · rfl
  · rw [jump_target_eq γ' hN hv', jump_target_eq γ hN hv, h]

/-- **The joint record** of a design: the exposure tables of all arms and the arms' price
tables, indexed by the arm index `ι`.
Source: [[dose-response]] §2.3 step 4 ("the auditor … retains the joint record of all arms")
Kind: D
Fidelity: exact
Hyps: n/a -/
def jointRecord {ι : Type*} (coins : ι → ℕ → Bool) (a : ℕ → ℚ) (arms : ι → History) :
    (ι → ℕ → ℕ → ℚ) × (ι → History) :=
  (fun i => exposureTable (coins i) a, arms)

/-- **T2(e), corollary: the joint records coincide.** The joint record of the content-steered
design and of the content-blind design with slope `γ(v − ½)` are equal, for any family of coins
and any stream whose exposed formative quotes are `v`.
Source: [[dose-response]] §6.3 T2(e) ("no statistic of the joint record … separates")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem jointRecord_eq {ι : Type*} (base : DeductiveProcess) (γ : ℚ) {N : ℕ} (hN : 0 < N)
    (coins : ι → ℕ → Bool) {a : ℕ → ℚ} {v : ℚ}
    (hv : ∀ i, ∀ j < N, coins i j = true → a j = v) :
    jointRecord coins a (fun i => arm base γ N (coins i) a) =
      jointRecord coins a (fun i => armBlind base (γ * (v - 1 / 2)) N (coins i) a) := by
  unfold jointRecord
  congr 1
  funext i
  exact non_attribution base γ hN (hv i)

/-! ## The arm is a function of its exposure ledger (the semantic form of "same algorithm,
different ledgers") -/

/-- Equal exposure tables have equal coins (item `1`).
Source: none: infrastructure (adversarial audit r1, N3's probe `ArmLedgerDetermined.lean`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem coin_of_exposureTable_eq {c c' : ℕ → Bool} {a a' : ℕ → ℚ}
    (h : exposureTable c a = exposureTable c' a') : c = c' := by
  funext n
  have h1 := congrFun (congrFun h 1) n
  simp only [exposureTable_one] at h1
  cases hc : c n <;> cases hc' : c' n
  · rfl
  · simp [hc, hc'] at h1
  · simp [hc, hc'] at h1
  · rfl

/-- Equal exposure tables with the same coin have equal streams on the exposed days (item `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem stream_of_exposureTable_eq {c : ℕ → Bool} {a a' : ℕ → ℚ}
    (h : exposureTable c a = exposureTable c a') {n : ℕ} (hn : c n = true) : a n = a' n := by
  have h0 := congrFun (congrFun h 0) n
  simp only [exposureTable_zero] at h0
  rw [if_pos hn, if_pos hn] at h0
  exact h0

/-- Equal exposure tables give equal testimony.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem testimony_of_exposureTable_eq {c : ℕ → Bool} {a a' : ℕ → ℚ}
    (h : exposureTable c a = exposureTable c a') (N : ℕ) :
    testimony c a N = testimony c a' N := by
  unfold testimony
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : c j = true
  · rw [if_pos hj, if_pos hj, stream_of_exposureTable_eq h hj]
  · rw [if_neg hj, if_neg hj]

/-- **The arm is determined by its exposure ledger.** `arm base γ N c a` takes `(c, a)` as
parameters; the content of "same algorithm, different ledgers" is that the arm reads nothing
beyond the ledger: two parameter pairs with the same exposure table give the same market (item
`1` forces the coins equal, item `0` the streams on exposed days, hence equal testimony, weight,
base and arm). The honest form of the mandate's "`rfl` check" (F8) — a theorem, not a `rfl`.
Source: [[dose-response]] §2.3 step 3, §6.3 T2(e) ("same algorithm, different ledgers"); mandate T6; adversarial audit r1 N3
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem arm_of_exposureTable_eq {c c' : ℕ → Bool} {a a' : ℕ → ℚ}
    (h : exposureTable c a = exposureTable c' a') (base : DeductiveProcess) (γ : ℚ) (N : ℕ) :
    arm base γ N c a = arm base γ N c' a' := by
  have hc := coin_of_exposureTable_eq h
  subst hc
  unfold arm armBase armProcess
  rw [h]
  congr 1
  funext n
  unfold armWeight
  rw [testimony_of_exposureTable_eq h N]

end Cleanroom.Deference.DefDoseResponse
