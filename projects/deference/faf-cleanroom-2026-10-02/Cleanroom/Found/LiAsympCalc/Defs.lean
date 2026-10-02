import LogicalInduction.Properties.Support.WeightedAverages
import LogicalInduction.Properties.Calibration
import LogicalInduction.Properties.SelfTrust
import LogicalInduction.Properties.ExpectationProperties
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

/-!
# `li-asymp-calc`: definitions of record

The definitions module of the package `Cleanroom.Found.LiAsympCalc` ([[li-asymp-calc-mandate]]).
Only definitions live here; theorem files import this one. Every object is stated over FAF's
carriers (`prefixSum`, `weightedAverage`, `ctsInd`, `EF`, `LUVCombination`, `PCWorld.ValuesAt`),
so a dependent's statement about an inductor's prices composes with FAF's endpoints without a
modelling substitution.

**Conventions pinned here** (dependents rely on them):

* `weightedAverage w x n` (FAF) is `0` when `prefixSum w n = 0`; `prefixSum` is *inclusive*
  (`∑ i ∈ range (n+1)`), while `cesaro x N` below is *exclusive* (`∑ i ∈ range N`) so that
  Mathlib's `Filter.Tendsto.cesaro` transfers; `cesaro x 0 = 0` is a junk value, harmless at
  `atTop`.
* `HasLimitPoint f x` (FAF) is `MapClusterPt x atTop f`: a subsequential limit along `atTop`.
* `ctsInd δ x y` (FAF) is `min 1 (max 0 ((x - y) / δ))` with `δ : ℚ`; the ramp is one-sided
  (`ctsInd δ t t = 0`), and a *rational* width is statement content (the countable family the
  compactness lemma quantifies over). **A negative width reverses the ramp** (FAF's `(x - y)/δ`
  changes sign): the range/continuity lemmas hold for every `δ`, but every semantic headline
  (`ctsInd_eq_zero_iff`, `ctsInd_pos_iff`, `ctsInd_eq_one_iff`, `dsWeight_pos_imp`,
  `dsWeight_eq_one`, `dsFeature_denote`, E1) carries `0 < δ`; never drop it.
* `WeightedApprox w x y` is stated over the *total* `weightedAverage`, so at the zero weighting
  every pair is `WeightedApprox` (`weightedApprox_zero_total`): a dependent's `WeightedApprox`
  conclusion says nothing unless a nonnegative divergent weighting is in scope alongside it.
* `LUVCombination.expect A P n = A.expectAt P (n+1) n` (FAF): day-`n` prices at precision `n+1`.
* `runningSup` is a `Finset.sup'`, never `⨆` (whose `sSup` of an unbounded set is junk).
* `UpperDensityGE S d` (`∃ᶠ N, d * N ≤ countIn S N`) is unsatisfiable for `d > 1`
  (`upperDensityGE_gt_one_false`) and holds for every `S` when `d ≤ 0`
  (`upperDensityGE_of_nonpos`); `density_lemma` carries `0 < d`.
-/

namespace Cleanroom.Found.LiAsympCalc

open LogicalInduction Filter Topology

/-! ## A. Weighted approximation over FAF's `weightedAverage` -/

/-- The notes' `x ≈_{w̄} y`: the `w`-weighted average of `x - y` tends to `0`. Stated over FAF's
total `weightedAverage`, which is `0` while `prefixSum w n = 0`; under a divergent nonnegative
`w` that branch is eventually never taken. **Warning:** at the zero weighting every pair is
`WeightedApprox` (`weightedApprox_zero_total`), so a `WeightedApprox` conclusion carries no
information unless a divergence hypothesis on `w` is in scope with it.
Source: [[theorem-ss-streamlined]] §1; `lean-deference` `StreamlinedSS.lean:137`
Kind: D
Fidelity: exact
Hyps: n/a -/
def WeightedApprox (w x y : ℕ → ℝ) : Prop :=
  Tendsto (weightedAverage w (fun i => x i - y i)) atTop (𝓝 0)

/-- Exclusive Cesàro mean `(∑ i < N, x i) / N`; `cesaro x 0 = 0` (junk, harmless at `atTop`).
Matches Mathlib's `Filter.Tendsto.cesaro` (`n⁻¹ * ∑ i ∈ range n`).
Source: none: infrastructure (anson-052; `lean-deference` `StalenessDensity.lean:27`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def cesaro (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ i ∈ Finset.range N, x i) / N

/-- `#(S ∩ [0, N))`, the number of days below `N` in `S` (classical decidability of `S`).
Source: none: infrastructure (`lean-deference` `StalenessDensity.lean:27`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def countIn (S : Set ℕ) (N : ℕ) : ℕ :=
  by classical exact ((Finset.range N).filter (fun i => i ∈ S)).card

/-- `S` has upper density at least `d`: `d * N ≤ countIn S N` for infinitely many `N`
(`∃ᶠ N in atTop`). This is a `limsup`-type condition stated without a `limsup`.
Source: `lean-deference` `StalenessDensity.lean:27`; [[delay-program]] §6 T3
Kind: D
Fidelity: exact
Hyps: n/a -/
def UpperDensityGE (S : Set ℕ) (d : ℝ) : Prop :=
  ∃ᶠ N in atTop, d * N ≤ countIn S N

/-! ## D. The ramp and the doubly-soft gate -/

/-- The doubly-soft weight `Ind_δ(a > t) · Ind_δ(p < t - ε)`, both ramps FAF's `ctsInd`
(width `δ : ℚ`). Positive weight forces `t < a` and `p < t - ε` (`dsWeight_pos_imp`, in
`Ramp.lean`).
Source: [[faithful-acceleration]] §5; `lean-deference` `FaithfulAcceleration.lean:152`
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def dsWeight (t ε : ℝ) (δ : ℚ) (a p : ℝ) : ℝ :=
  ctsInd δ a t * ctsInd δ (t - ε) p

/-- The ramp `ctsInd δ x y` as an expressible feature of two features `x y : EF`:
`clip01 ((x - y) · (1/δ))`. Same shape as FAF's `ctsIndFeature` (`Construction/Quotation/
DeferralFibre.lean`), restated here so that `Defs` imports no `Construction.*` module.
Denotes `ctsInd δ (x.denote P) (y.denote P)` when `0 < δ` (`rampFeature_denote`, `Ramp.lean`).
Source: none: infrastructure (FAF `calibrationLower`, `ctsIndFeature`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def rampFeature (δ : ℚ) (x y : EF) : EF :=
  clip01 (EF.mul (EF.add x (EF.mul (EF.const (-1)) y)) (EF.const (1 / δ)))

/-- The doubly-soft weight as a feature of the day-`n` prices of `φ` and `ψ` in **one**
history: `Ind_δ(P n φ > t) · Ind_δ(P n ψ < t - ε)`. Denotes
`dsWeight t ε δ (P n φ) (P n ψ)` when `0 < δ` (`dsFeature_denote`, `Ramp.lean`), and is a
`PGenerableWeighting` for machine-coded `φ ψ` (`dsFeature_pgenerable`, `Feature.lean`).
Scope: legality in one market — the corpus's `Ind_δ(a_n > t)·Ind_δ(E^H_n(X) < t-ε)` mixes
`A`'s quote with `H`'s expectation and is a feature of `H`'s market only once the quote is
ledgered (`li-quote-lane`).
Source: [[faithful-acceleration]] §5, §9; [[deference-in-logical-induction-v6]] §5.9
Kind: D
Fidelity: exact (one-market form)
Hyps: n/a -/
def dsFeature (φ ψ : Sentence) (t ε δ : ℚ) (n : ℕ) : EF :=
  EF.mul (rampFeature δ (EF.price φ n) (EF.const t))
    (rampFeature δ (EF.const (t - ε)) (EF.price ψ n))

/-! ## H. Running supremum and the amplifier -/

/-- `max_{i ≤ T} a i`, as a `Finset.sup'` over `range (T+1)` (never `⨆`, whose `sSup` of an
unbounded set is junk).
Source: `research/deference-trust-lab/run2/lean/averaging-hides-spikes.lean`
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def runningSup (a : ℕ → ℝ) (T : ℕ) : ℝ :=
  (Finset.range (T + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos T)⟩ a

/-- The trust-lab amplifier `e ↦ (1 + 2c) e - c`.
Source: `lean-deference` `FrozenDeliberation.lean:123`; trust-lab-2-044
Kind: D
Fidelity: exact
Hyps: n/a -/
def amp (c e : ℝ) : ℝ := (1 + 2 * c) * e - c

/-! ## G. LUV-combination wrappers and per-LUV determinacy -/

/-- A single LUV as a `LUVCombination`: `0 + 1 · X`. FAF has no singleton constructor (grep
2026-09-29: only the three-term `linearityLUVComb`).
Source: [[li-deference]] line 92; root-deference-2-003
Kind: D
Fidelity: exact
Hyps: n/a -/
def LUVCombination.ofLUV (X : LUV) : LUVCombination :=
  ⟨EF.const 0, [(EF.const 1, X)]⟩

/-- The affine image `α · X + β` of a LUV as a `LUVCombination` (rational `α β`).
Source: [[li-deference]] line 92; [[faithful-acceleration]] §5 line 113
Kind: D
Fidelity: exact
Hyps: n/a -/
def LUVCombination.affineImage (α β : ℚ) (X : LUV) : LUVCombination :=
  ⟨EF.const β, [(EF.const α, X)]⟩

/-- `g · X` for an expressible-feature scalar `g : EF`: the only product FAF's combinations
carry exactly (a product of two undecided LUVs is not a combination).
Source: [[faithful-acceleration]] §5 line 113 (root-fa-008)
Kind: D
Fidelity: exact
Hyps: n/a -/
def LUVCombination.scaleByFeature (g : EF) (X : LUV) : LUVCombination :=
  ⟨EF.const 0, [(g, X)]⟩

/-- The per-LUV exact determinacy package: every completed-theory world values `X` at `y`
(FAF's `PCWorld.ValuesAt`: `y ∈ [0,1]`, thresholds below `y` affirmed, above `y` denied; a
threshold *equal* to `y` is unconstrained). This is what `li-quote-lane` / `li-coupled-pair`
discharge and what the bridges of `Luv.lean` consume.
Source: [[li-asymp-calc-mandate]] G3; FAF `Framework/Expectations.lean` (`PCWorld.ValuesAt`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def LUV.DeterminedVia (X : LUV) (DP : DeductiveProcess) (y : ℝ) : Prop :=
  ∀ v : PCWorld, v.ConsistentWithTheory DP → v.ValuesAt X y

end Cleanroom.Found.LiAsympCalc
