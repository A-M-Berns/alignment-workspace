import Cleanroom.Fa.FaForcingTrader.B.Defs
import Cleanroom.Fa.FaTheoremA.Analysis

/-!
# `fa-forcing-trader` · angle B · Witnesses: the schedule objects are inhabited and non-trivial

Non-vacuity for the pieces angle B owns. What is **not** here, and why, is in
`fa-forcing-trader-report-B.md` § Witnesses: no inhabitant of the full hypothesis package of
`theoremSS_fullLimit` (its two certificates `CA`, `CH` are the OPEN of `Open.lean`), so the
headline ships as a conditional of record.

* `linearSchedule` — `d k = 2k + 2`, a `DeferralFunction` (graph by `UnaryRuler.eqFlag`),
  window-disjoint for the successor lookahead: angle A's T2 shape, exercised.
* `scheduleIndicator_divergent` — **every** deferral function's schedule indicator is a divergent
  weighting of every market (the image is infinite), so `scheduleIndicator d` is a genuine
  `PGenerableWeighting ∧ DivergentWeighting` (N+: `doublingDeferral`'s image has density `0`).
* `legibleOn_schedGate_self` — the same-market instance of (L): the scheduled gate is legible on
  the market whose quotes it reads (N− for the content of (L), N+ for the hypothesis shape).
-/

namespace Cleanroom.Fa.FaForcingTrader.B

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- **A linear schedule** `d k = 2k + 2` as a `DeferralFunction`: it defers (`k < 2k + 2`) and its
graph `2n + 2 = m` is decided on the unary pair by `UnaryRuler.eqFlag` (FAF's `succDeferral`
pattern).
Source: mandate T2 (`linearSchedule c` at `c = 2`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def linearSchedule : DeferralFunction where
  f k := 2 * k + 2
  lt k := by omega
  graph_fp :=
    ⟨fun z : List Bool =>
        List.replicate (if 2 * z.length.unpair.1 + 2 = z.length.unpair.2 then 1 else 0) false,
      UnaryRuler.eqFlag (((UnaryRuler.const 2).mul UnaryRuler.unpairFst).add (UnaryRuler.const 2))
        UnaryRuler.unpairSnd,
      fun n m => by simp⟩

/-- **N+ for `WindowDisjoint`**: the linear schedule is window-disjoint for the successor lookahead
(`2k + 2 + 1 < 2(k+1) + 2`).
Source: mandate T2 (the N+ schedule)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem windowDisjoint_succ_linear : WindowDisjoint succDeferral linearSchedule := by
  refine ⟨strictMono_nat_of_lt_succ (fun k => ?_), fun k => ?_⟩
  · show 2 * k + 2 < 2 * (k + 1) + 2
    omega
  · show 2 * k + 2 + 1 < 2 * (k + 1) + 2
    omega

/-- **Every schedule indicator is a divergent weighting of every market**: it is `{0,1}`-valued and
`1` at the infinitely many days `d k` (`d k ≥ k`), so its prefix sums diverge
(`fa-theorem-a`'s `tendsto_prefixSum_atTop_of_frequently_one`). With `scheduleIndicator_pgenerable`
this makes `scheduleIndicator d` a legal divergent weighting in FAF's sense for *any* deferral
function — the schedule alone never kills the mass; only the gate factor can.
Source: mandate T4 witness ("`G := scheduleIndicator d` (mass divergent)")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem scheduleIndicator_divergent (d : DeferralFunction) (P : History) :
    DivergentWeighting (scheduleIndicator d) P := by
  refine ⟨scheduleIndicator_mem_Icc d P, ?_⟩
  apply tendsto_prefixSum_atTop_of_frequently_one (fun i => (scheduleIndicator_mem_Icc d P i).1)
  rw [Filter.frequently_atTop]
  intro N
  refine ⟨d N, (d.lt N).le, ?_⟩
  rw [scheduleIndicator_denote_of_mem]

/-- The doubling schedule `2^n` (FAF's `doublingDeferral`, image of density `0`) carries divergent
mass: a sparse schedule whose indicator is nonetheless a divergent generable weighting.
Source: mandate T2 (the sparse N+ schedule); FAF `doublingDeferral`
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem scheduleIndicator_doubling_divergent (P : History) :
    PGenerableWeighting (scheduleIndicator doublingDeferral) ∧
      DivergentWeighting (scheduleIndicator doublingDeferral) P :=
  ⟨scheduleIndicator_pgenerable doublingDeferral, scheduleIndicator_divergent doublingDeferral P⟩

/-- **The same-market instance of (L)**: the scheduled gate of `A`'s own quotes is legible on `A`.
N+ for the hypothesis shape `LegibleOn`, N− for its content (the corpus's (L) is about a *second*
market reading the numbers; that instance is `Open.lean`'s `exists_twoMarket_legible_pair`).
Source: mandate T1 (`legibleOn_quote_self`), T3 witness ("the same-market instance")
Kind: N-
Fidelity: exact (same market)
Hyps: (a) `hY` -/
theorem legibleOn_schedGate_self (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y)
    (d : DeferralFunction) (t δ : ℚ) (A : History) :
    LegibleOn A (fun n => (schedGate Y d t δ n).denote A) :=
  legibleOn_self A (schedGate_pgenerable Y hY d t δ)

end Cleanroom.Fa.FaForcingTrader.B
