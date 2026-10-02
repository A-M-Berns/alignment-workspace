import Cleanroom.Fa.FaAdaptiveJoint.Counting
import Cleanroom.Fa.FaForcingTrader.Bridge

/-!
# `fa-adaptive-joint` · Bridge: the one-position `H`-side bridge (T4, OPEN)

[[fa-adaptive-joint-mandate]] T4. The exploitation half of (A4): for an `H`-generable
**one-position** weighting with divergent mass (the adaptive firing weighting is one, T1/T2), the
weighted average of what a trader banks by buying the day-`n` threshold mesh of `X_n` at `n` and
selling it at `f n` tends to `0`. The dependency's `hSideBridge` proves this when the weighting is
supported on a window-disjoint `DeferralFunction` schedule, because FAF's `feedbackTrader` runs
one chain of consecutive round trips; an adaptive weighting opens a piece on *any* day `n` and
closes it at `f n`, with several pieces nested open at once, so the trader it needs is new over
FAF (FAF's own corrected 4.8.16, `luv_wubexp_ofComputation`, also asks for
`WeightingSupportedOnDeferralImage`). The statement of record `AdaptiveBridgeHolds` is **OPEN**
(`adaptiveBridge`, listed in `fa-adaptive-joint-open.txt`); its hard instance — any window-disjoint
schedule-supported weighting is one-position (`onePosition_of_windowDisjoint_support`) and there
the bridge is `hSideBridge` (`adaptiveBridge_of_schedule`) — is proved, so the OPEN row is a
strict generalization of a proved one. The budget accounting that the open proof needs is
described in [[fa-adaptive-joint-report]] § T4.

The microscope clause, verbatim (mandate § Docstring template): "no `hbias`, `hbdd`, `hNoExp`,
`hMirror`; the LI content enters only through FAF's criterion on `adaptiveTrader`".
-/

namespace Cleanroom.Fa.FaAdaptiveJoint

open LogicalInduction Cleanroom.Fa.FaForcingTrader Cleanroom.Fa.FaTheoremA
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Filter Topology

/-- **The one-position `H`-side bridge, as a statement about a market `H`, a lookahead `f` and an
e.c. family `X`**: for every `H`-generable weighting `G` that is one-position for `f`
(`OnePosition f (G·denote H)`: nonnegative, pieces open on any day summing to `≤ 1`) and divergent
in `H`'s prices, the `G`-weighted average of `price^H_{f n}(bundle X n) − 𝔼^H_n(X_n)` tends to `0`
(`WeightedApprox`, the dependency's T4 shape). T3 consumes it as a named hypothesis `hbridge`.
`OnePosition` carries content only through `f`: at `f = succDeferral` it is nonnegativity alone and
the statement is one-day-ahead unbiasedness over *every* `H`-generable divergent weighting — not
covered by `hSideBridge`, whose `WindowDisjoint` excludes `d = id` — so that instance, a single
non-overlapping Kelly chain in FAF's `feedbackTrader` shape, is the easiest one for a continuation
to attack first (audit r1 adversarial N8).
Source: [[fa-positive-results-corrected-v3]] §4 ("exactly the computation of §3 … with `u` in place of the scheduled `w`, and with one open position by construction"); vq-wiki-057 Theorem 5.2; [[fa-adaptive-joint-mandate]] § T4
Kind: D
Fidelity: exact (the T4 statement as a predicate)
Hyps: n/a -/
def AdaptiveBridgeHolds (H : History) (f : DeferralFunction) (X : ℕ → LUV) : Prop :=
  ∀ (G : ℕ → EF), PGenerableWeighting G → OnePosition f (fun n => (G n).denote H) →
    DivergentWeighting G H →
    WeightedApprox (fun n => (G n).denote H) (fun n => (bundle X n).price H (f.f n))
      (fun n => (X n).expect H n)

/-- **T4 (headline, load-bearing) — OPEN. The one-position `H`-side bridge.** For
`[IsLogicalInductor H DPH]`, an e.c. family `X` (every stage of `DPH` satisfiable) and any
lookahead `f`, `AdaptiveBridgeHolds H f X`: every `H`-generable one-position divergent weighting
averages the round-trip gap `price^H_{f n}(bundle X n) − 𝔼^H_n(X_n)` to `0`. No `hbias`, `hbdd`,
`hNoExp`, `hMirror`; the LI content enters only through FAF's criterion on `adaptiveTrader` — the
trader this needs (day-`n` strategy: join over `k ≤ n` of "open piece `k` at day `k` of size
`c_k`, close at `f k`" with `c_k` an `EF` sized by the free cash) is not in FAF and not built here:
the Kelly product over closed trips does not telescope across overlapping pieces, and the
`EfficientlyComputable` certificate of the joined trader is a second `MachineSpliceStream`
construction of the size of FAF's `feedbackTrader_ec`. What is proved: the hard instance
`adaptiveBridge_of_schedule` (window-disjoint schedule support), which inhabits the hypothesis
package (`onePosition_of_windowDisjoint_support`). Listed in `fa-adaptive-joint-open.txt`.
Scope: one-way (`H` alone). Family: e.c. family `X` (`MachineThresholdCodeSeq`). Lookahead: any
`DeferralFunction f` (v3: `2^n`). Grade: full limit.
(A4): expressibility proved in T1; exploitation is this statement (OPEN).
Source: [[fa-positive-results-corrected-v3]] §4 Theorem 2's proof ("one open position by construction"); vq-wiki-057 Theorem 5.2; trust-lab-066 (the microscope); [[fa-adaptive-joint-mandate]] § T4
Kind: OPEN
Fidelity: exact
Hyps: (a) `hcode`, `hworldH` (FAF's own premises); no (b), no (c) — the statement is open, not conditioned. -/
theorem adaptiveBridge {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    {X : ℕ → LUV} (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) (f : DeferralFunction) :
    AdaptiveBridgeHolds H f X := by
  sorry

/-- **A window-disjoint schedule-supported `[0,1]` weighting is one-position**: on any day at most
one scheduled piece is open (if `d k < n < f (d k)` and `d k' < n < f (d k')` with `k < k'`, then
`d k' ≥ d (k+1) > f (d k) > n`, contradiction), so the open mass is one value `≤ 1`. Hence the
dependency's T4 hypothesis package is an instance of `AdaptiveBridgeHolds`'s.
Source: [[fa-positive-results-corrected-v3]] §3 ("at most one position is ever open"); [[fa-adaptive-joint-mandate]] § T4 (the hard instance)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem onePosition_of_windowDisjoint_support {f d : DeferralFunction} (hwd : WindowDisjoint f d)
    {u : ℕ → ℝ} (hu : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1) (hsupp : ∀ n, u n ≠ 0 → ∃ k, d.f k = n) :
    OnePosition f u := by
  classical
  intro n
  refine ⟨(hu n).1, ?_⟩
  set S := ((Finset.range n).filter (fun m => n < f.f m)).filter (fun m => u m ≠ 0) with hS
  have hsum : openMass f.f u n = ∑ m ∈ S, u m := by
    rw [openMass, hS, Finset.sum_filter_ne_zero, Finset.sum_filter]
  have hcard : S.card ≤ 1 := by
    refine Finset.card_le_one.2 (fun a ha b hb => ?_)
    rw [hS, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at ha hb
    obtain ⟨⟨han, hfa⟩, hua⟩ := ha
    obtain ⟨⟨hbn, hfb⟩, hub⟩ := hb
    obtain ⟨ka, rfl⟩ := hsupp a hua
    obtain ⟨kb, rfl⟩ := hsupp b hub
    rcases lt_trichotomy ka kb with hlt | heq | hgt
    · exfalso
      have h1 : d.f (ka + 1) ≤ d.f kb := hwd.1.monotone (Nat.succ_le_of_lt hlt)
      have h2 := hwd.2 ka
      omega
    · rw [heq]
    · exfalso
      have h1 : d.f (kb + 1) ≤ d.f ka := hwd.1.monotone (Nat.succ_le_of_lt hgt)
      have h2 := hwd.2 kb
      omega
  rw [hsum]
  calc ∑ m ∈ S, u m ≤ S.card • (1 : ℝ) :=
        Finset.sum_le_card_nsmul S u 1 (fun m _ => (hu m).2)
    _ = (S.card : ℝ) := by rw [nsmul_eq_mul, mul_one]
    _ ≤ 1 := by exact_mod_cast hcard

/-- **T4, the hard instance (proved): the bridge on a window-disjoint schedule-supported
weighting is the dependency's `hSideBridge`** — FAF's criterion on FAF's own Kelly round-trip
trader `feedbackTrader` along `interleave f d`. Together with
`onePosition_of_windowDisjoint_support`, this is `AdaptiveBridgeHolds` restricted to weightings
supported on `im d`, so the OPEN statement strictly generalizes a proved one.
Scope: one-way (`H` alone). e.c. family `X`. Schedule: window-disjoint `DeferralFunction`.
Grade: full limit. No `hbias`, `hbdd`, `hNoExp`, `hMirror`.
Source: [[fa-adaptive-joint-mandate]] § T4 ("Fallback … `adaptiveBridge_of_schedule := hSideBridge`"); `fa-forcing-trader` T4
Kind: C
Fidelity: weaker: the schedule-supported case of `AdaptiveBridgeHolds` only
Hyps: (a) all: `hcode`, `hworldH`, `hwd`, `hG`, `hsupp`, `hdiv`; no (b), no (c). -/
theorem adaptiveBridge_of_schedule {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    {X : ℕ → LUV} (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    {f d : DeferralFunction} (hwd : WindowDisjoint f d)
    {G : ℕ → EF} (hG : PGenerableWeighting G)
    (hsupp : ∀ n, (G n).denote H ≠ 0 → ∃ k, d.f k = n)
    (hdiv : DivergentWeighting G H) :
    WeightedApprox (fun n => (G n).denote H) (fun n => (bundle X n).price H (f.f n))
      (fun n => (X n).expect H n) :=
  hSideBridge hcode hworldH hwd hG hsupp hdiv

/-- The hypothesis package of `adaptiveBridge_of_schedule` inhabits that of `AdaptiveBridgeHolds`:
a schedule-supported divergent weighting is one-position.
Source: [[fa-adaptive-joint-mandate]] § T4
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem onePosition_of_schedule_supported {H : History} {f d : DeferralFunction}
    (hwd : WindowDisjoint f d) {G : ℕ → EF} (hdiv : DivergentWeighting G H)
    (hsupp : ∀ n, (G n).denote H ≠ 0 → ∃ k, d.f k = n) :
    OnePosition f (fun n => (G n).denote H) :=
  onePosition_of_windowDisjoint_support hwd (fun n => hdiv.1 n) hsupp

end Cleanroom.Fa.FaAdaptiveJoint
