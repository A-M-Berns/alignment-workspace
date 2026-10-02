import Cleanroom.Corrigibility.CorrTrajectory.Process
import Cleanroom.Corrigibility.CorrTrajectory.Potential
import Cleanroom.Corrigibility.CorrTrajectory.Certificate
import Cleanroom.Corrigibility.CorrTrajectory.Hazard
import Cleanroom.Corrigibility.CorrTrajectory.HazardWitness
import Cleanroom.Corrigibility.CorrTrajectory.LossToy
import Cleanroom.Corrigibility.CorrTrajectory.ObsToy
import Cleanroom.Corrigibility.CorrTrajectory.LegitToy
import Cleanroom.Corrigibility.CorrTrajectory.Corruption
import Cleanroom.Corrigibility.CorrTrajectory.Coverage
import Cleanroom.Corrigibility.CorrTrajectory.Grades
import Cleanroom.Corrigibility.CorrTrajectory.Basin
import Cleanroom.Corrigibility.CorrTrajectory.ProductLaw
import Cleanroom.Corrigibility.CorrTrajectory.Horizon
import Cleanroom.Corrigibility.CorrTrajectory.Margin
import Cleanroom.Corrigibility.CorrTrajectory.HorizonWitness
import Cleanroom.Corrigibility.CorrTrajectory.Sequences
import Cleanroom.Corrigibility.CorrTrajectory.Accounting
import Cleanroom.Corrigibility.CorrTrajectory.Martingale
import Cleanroom.Corrigibility.CorrTrajectory.TestA
import Cleanroom.Corrigibility.CorrTrajectory.Inclusion
import Cleanroom.Corrigibility.CorrTrajectory.Identifiability

/-!
# `corr-trajectory`: trajectories, certificates and basins — root module

The `invariant` thread of run 2 (`invariant-final.md`), stated over FAF's `Distr` in Layer F
(finite filtrations by atoms, product-form conditional sums) with the certificate theorems also in
Layer M (Mathlib's `Supermartingale`). Namespace `Cleanroom.Corrigibility.CorrTrajectory`.
Undiscounted throughout.

* `Process` (T1): `Atoms`, `FinFiltered`, `condSum`, `ShutdownProc` (S2 with `executed`, `loss`,
  `Harm`, `Omit`, `Reg` derived; S2′'s `executedWL`), `AgentView` (`Ψ`, `Z`, `Δ`, the Mart identities).
* `Potential` (D4/D5): supermartingale, potential, barrier, forward invariance with hazard; the
  finite Ville inequality `ville_finite` and `barrier_bound`.
* `Certificate` (T7, Layer F): the chain (a), the expectation bound and Ville on `Z` (b), the backward
  induction (c), the legitimacy budget (e), and the develop's 8(b) parenthetical under 8(a)
  (`drift_eq_zero_of_uncondMart_of_calibrated`). `LossToy` (A1, A8, A2 with its scope `a2_not_uncondMart`,
  C6, and the zero-stakes N− inhabitant of `ville_Z`), `LegitToy` (A3, F2), `ObsToy` (the N+ witnesses
  of the certificate theorems: A8's agent for two rounds with `ℓ₀` observed at time `1`; `ObsToy.Updating`
  the same with the agent updating on the revealed `W₀`, `Ψ₁` atom-dependent).
* `Martingale` (T7, Layer M): the certificate expectation bound, Ville by optional stopping + Markov,
  a.s. convergence of nonnegative supermartingales, Lévy's conditional Borel–Cantelli (cited).
* `Hazard` (T6): the per-round union bound (a), the budget potential as a barrier certificate (b),
  the factorization (d); `HazardWitness`: the first-passage process, harmonic (N−), geometric (N+),
  and `Factor` (the factorization with the factor `1/2 < 1` active, tight).
* `Corruption` (T5): the A7 law and its derived posterior, floor, dogmatic schedule, residue; `Dogmatic`
  (T5(d) on one object: `κ_t` the rule on the schedule, defiance from `t = 9`, `harm_linear` tight).
* `Coverage` (T8): set algebra, the gap bound, A4 over `voiSensor`.
* `Grades` (T2): tail / safety / liveness, Statement 1 with the topology sharpened, 1(b) in D2's vocabulary.
* `Basin` (T9): forward invariance (non-label N+), the tracking recursion, two coverages separated.
* `Horizon` (T3, both halves: harm under `(βmin)` and omission under `(αmax)`, each with its `(MI)`
  equality and display form) with `ProductLaw`, `HorizonWitness` (A6, C7 through both halves);
  `Margin` (T4, with E1 on a two-round process).
* `Sequences` (T10), `Accounting` (T11), `TestA` (T12), `Inclusion` (T13), `Identifiability` (T14).
-/
