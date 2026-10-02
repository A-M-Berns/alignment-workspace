import Cleanroom.Found.LiAsympCalc.Defs
import Cleanroom.Found.LiAsympCalc.WeightedAverage
import Cleanroom.Found.LiAsympCalc.LimitPoint
import Cleanroom.Found.LiAsympCalc.Density
import Cleanroom.Found.LiAsympCalc.Ramp
import Cleanroom.Found.LiAsympCalc.Feature
import Cleanroom.Found.LiAsympCalc.Compactness
import Cleanroom.Found.LiAsympCalc.LogBudget
import Cleanroom.Found.LiAsympCalc.Luv
import Cleanroom.Found.LiAsympCalc.Spikes
import Cleanroom.Found.LiAsympCalc.Amplifier

/-!
# `li-asymp-calc`: asymptotic calculus over FAF price sequences

Root module of the package `Cleanroom.Found.LiAsympCalc`; dependents import this one name.
Mandate: `run/wp/li-asymp-calc/li-asymp-calc-mandate.md`; report, findings and ledger beside it.

* `Defs`: the definitions of record — `WeightedApprox`, `cesaro`, `countIn`, `UpperDensityGE`,
  `dsWeight`, `rampFeature`, `dsFeature`, `runningSup`, `amp`, `LUVCombination.ofLUV` /
  `.affineImage` / `.scaleByFeature`, `LUV.DeterminedVia`.
* `WeightedAverage` (A): the `≈_{w̄}` calculus, the universal donor rule (no boundedness),
  the Cesàro bridge, Kronecker's lemma (conditional form) with its witness.
* `LimitPoint` (B): `HasLimitPoint … 0` as `∀ ε, ∃ᶠ`, the wash-out lemma at the limit point
  with its `weightedBias` corollary, adverse-prefix witnesses, limit point ≠ limit.
* `Density` (C): the density lemma and its quantitative contrapositive, evens witness.
* `Ramp` (D1–D3): the ramp is `ctsInd`, the doubly-soft weight's support law and feature form,
  a hard price indicator is not an `EF`.
* `Feature` (D2, legality): `dsFeature` is a `PGenerableWeighting`.
* `Compactness` (E): rational-parameter violation weights vanish iff dominance iff
  `0 ≤ liminf (e - a)`; summability packaging; schedule form; the `t ∈ [0,1]` family suffices
  for `[0,1]`-valued streams; witnesses (non-constant).
* `LogBudget` (F): `x - x² ≤ log (1+x)` on `[-1/2, ∞)`, the log-product bound, the
  frequent-excess exploitation shape, witnesses (everyday excess and sparse excess).
* `Luv` (G1–G3): expectation/value laws of the wrappers, `WorldValued` and determinacy bridges,
  the precision-`(n+1)` mesh (approximate; exact only off-grid — refuted on the grid by
  `not_determined_mesh_ofLUV_onGrid`).
* `Spikes` (H1): running sup, spike family, the false near-miss (the source's own refutation
  re-proved), Markov, spike frequency; the C1 density witness with infinitely many exceptions.
* `Amplifier` (H2): the amplifier integrals in `intervalIntegral`, affine rigidity (the
  amplifiers pass the cuts and fail only the range), the bounded impostor.

Repaired after audit round 1 (2026-09-30): see `li-asymp-calc-report.md` §Repair round 1.
-/
