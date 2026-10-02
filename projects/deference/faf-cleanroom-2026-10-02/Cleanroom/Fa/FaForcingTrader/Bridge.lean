import Cleanroom.Fa.FaForcingTrader.A.Bridge
import Cleanroom.Fa.FaForcingTrader.A.Mesh

/-!
# `fa-forcing-trader` · Bridge: the `H`-side of record (T4, T5)

Main module of the reconciled package ([[fa-forcing-trader-mandate]] T4, T5). Both targets are
angle A's, restated verbatim in the package namespace and proved `:= A.…`; angle B has no
counterpart of T4 at grade (a) (its `selfSide_fullLimit` reaches the same full limit on `H`'s side
at the price of FAF's `cee` carrier `hq` and a timing certificate `CH`, graded (b); see
`TheoremSS.lean`, where the reconciler shows the trader route makes both unnecessary).

* `hSideBridge` (T4, load-bearing): FAF's criterion on FAF's own Kelly round-trip trader
  (`lic_not_frequently_positive_feedback_return` on `bundle X` along `interleave f d`) forces
  the scheduled average of the realized cash to `0`, both signs, no `hbias`/`hbdd`/`hNoExp`/`hMirror`.
* `bundle_price_sub_realized_tendsto` (T5): the closing-grid mesh term vanishes (FAF's `lem:mesh`),
  and its donor corollary `weightedApprox_bundle_realized`.
* `forcingTrader`: the abbreviation naming FAF's trader (alias of `A.forcingTrader`).
-/

namespace Cleanroom.Fa.FaForcingTrader

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Filter Topology

export A (forcingTrader)

/-- **T4 (headline, of record). The `H`-side bridge: the criterion forces the Kelly round trip's
realized cash to average to zero.** For `[IsLogicalInductor H DPH]`, an e.c. family `X` of `H`'s
LUVs, a window-disjoint schedule `d` for the lookahead `f`, and any `PGenerableWeighting G` of
`H`'s market supported on `im d` and divergent in `H`'s prices: the `G`-weighted average of
`price^H_{f n}((X n).expectAffine (n+1)) − 𝔼^H_n(X_n)` — what the trader banks per scheduled day,
buying the day-`n` threshold mesh at `n` and selling it at `f n` — tends to `0` (two-sided full
limit, `WeightedApprox`). Angle A's theorem, restated.
Scope: one-way (`H`'s own market only; nothing about `A`). e.d. family `X`. Schedule:
window-disjoint `DeferralFunction`. Grade: full limit.
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`
(the microscope, trust-lab-066: `hbdd` → FAF's `feedbackTrader_plausible_bddBelow`,
`hNoExp`/`hMirror` → `IsLogicalInductor.noExploit` on FAF's `feedbackTrader` and its
`PolySequence.neg`, inside `lic_not_frequently_positive_feedback_return`).
Source: vq-wiki-049 (trader variant); vq-wiki-057 Theorem 5.2 (one-position case); lean-deference-036 (`kelly_round_trip` with `hNoExp`/`hMirror` discharged); trust-lab-066; [[theorem-ss-streamlined]] §3 Remark; [[fa-positive-results-corrected-v3]] §3 "The human-side trader"
Kind: C
Fidelity: variant: the trader sells the day-`n` mesh at its day-`f n` *price* (the opening grid), not at `𝔼^H_{f n}(X_n)` as v3 §3 writes (F-A9); the trader is FAF's D.4 round trip on that mesh, and the gap is the mesh term T5, washed out of every divergent average
Hyps: (a) all: `hcode`, `hworldH`, `hG`, `hsupp`, `hdiv`; no (b), no (c). -/
theorem hSideBridge {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    {X : ℕ → LUV} (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    {f d : DeferralFunction} (hwd : WindowDisjoint f d)
    {G : ℕ → EF} (hG : PGenerableWeighting G)
    (hsupp : ∀ n, (G n).denote H ≠ 0 → ∃ k, d.f k = n)
    (hdiv : DivergentWeighting G H) :
    WeightedApprox (fun n => (G n).denote H) (fun n => (bundle X n).price H (f.f n))
      (fun n => (X n).expect H n) :=
  A.hSideBridge hcode hworldH hwd hG hsupp hdiv

/-- **T5 (of record). The closing-grid mesh term vanishes**: the day-`f n` price of the day-`n`
threshold mesh of `X_n` and the day-`f n` expectation `𝔼^H_{f n}(X_n)` become indistinguishable —
FAF's `lem:mesh` (`BoundedSequence.mesh_independence`) for the constant-coefficient family
`0 + 1·X_n`. Angle A's theorem, restated.
Scope: one-way (`H` alone). e.d. family `X`. Any deferral `f`. Grade: full limit.
Source: [[route-recurring-ccee]] §5.4 ("Mesh Independence Lemma (appendix E.2)"); lean-deference-036 (`hmesh`); FAF `lem:mesh`
Kind: C
Fidelity: exact
Hyps: (a) `hcode`, `hworldH`, `hval` (FAF's own premises of `lem:mesh`); no (b), no (c). -/
theorem bundle_price_sub_realized_tendsto {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH] {X : ℕ → LUV} (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (f : DeferralFunction) :
    Tendsto (fun n => (bundle X n).price H (f.f n) - (X n).expect H (f.f n)) atTop (𝓝 0) :=
  A.bundle_price_sub_realized_tendsto hcode hworldH hval f

/-- **T5, donor corollary (of record)**: under any nonnegative weighting with divergent mass, the
bundle's sale price and the realized expectation `Y_n = 𝔼^H_{f n}(X_n)` agree in `WeightedApprox`.
Angle A's theorem, restated.
Source: [[theorem-ss-streamlined]] §1 (the donor rule); lean-deference-036 (`hmesh` washed out)
Kind: C
Fidelity: exact
Hyps: (a) as `bundle_price_sub_realized_tendsto`, plus `hw`, `hdiv`; no (b), no (c). -/
theorem weightedApprox_bundle_realized {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH] {X : ℕ → LUV} (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (f : DeferralFunction) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) :
    WeightedApprox w (fun n => (bundle X n).price H (f.f n)) (realized H f X) :=
  A.weightedApprox_bundle_realized hcode hworldH hval f hw hdiv

end Cleanroom.Fa.FaForcingTrader
