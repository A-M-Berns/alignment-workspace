/-
  Root module of the `dp-local-opt` package: local optimality — v2 §8's Theorems 1–2,
  Definition 22 (mixed, A30), Proposition 5 / Definition 21, Definition 23 / Proposition 13, and
  the anthropic 2×2 — over `dp-core-tree`'s objects (`Cleanroom.Found.DpCoreTree`).

  - `Sia`: Theorem 1's functional `siaSum` (`∑_{q : d_q = d} R_q G_q`), the bridge to
    `forcedBelow`, `∑_q R_q = 𝔼[#_d]`, and the predicates `Thm1At`/`Thm1`, `CoherentAt`/`Coherent`
    (Definition 22 of record, mixed), `CoherentPureAt`/`CoherentPure` (v2 as written),
    `IsOptimal`.
  - `ChainRule`: T2 (the chain rule as a finite-difference expansion with bounded remainder),
    T3(b) `thm1At_of_coherentAt` (ZO-6 / A31), T4 `thm1_of_isOptimal` (Theorem 1).
  - `Trees`: the new catalogue trees (`amdShape`, `mergedStag`, `twoStag`, `threeCoal`, `kfold`,
    `deathDamascus`, `fairDepth2`) and their value closed forms.
  - `Ssa`: T6 (Theorem 2 for every procedure: `ssaValue`, `ssaNum`, `offOcc`, the decomposition,
    the cancellation, `ssaValue_le_iff`).
  - `Coherence`: T3(c) third clause (the three conditions coincide on almost-fair trees).
  - `AmdWitness`: one-point helpers and every AMD-shape number (T3(a), T3(c), T4's table,
    T6's N−, T8(a) Wei Dai, T8(b) merged Stag Hunt, T16(i)).
  - `TwoPointWitness`: T7 (off-path vacuity), T8(d) (two-point Stag Hunt), T11 (local maxima).
  - `Assignments`: T1 (Proposition 5, Remark 6.2).
  - `Optima`: T5(b)(d) (Definition 21's vertex clause; the nested tree with a pure optimum).
  - `Coalition`: T10 (coalition Lemma 1, Definition 23, Proposition 13(i), antitonicity).
  - `Witnesses`: T8(c)/T9 (`k`-fold mugging), T8(e) (Death in Damascus), T15 (weak node-SSC).
  - `Cells`: T12(a)(b)(d) (the anthropic 2×2, SE-21), T13(a) (own-draw conditioning is forcing).
  - `NestedWitness` (repair r1): T12's two diagonal cells evaluated on the AMD (they differ);
    T6's CA-22′ check on a nested tree with `μ(occ) = 1/2`.
  - `StrongFair` (repair r1, r2): `twoStag` is not strongly fair; strict local maxima
    (`IsStrictLocalMax`, inhabited and bounded in r2), the gated shape lemma, `twoPoint` strict
    local maxima are global.
  - `GatedInduction` (repair r2): **on a strongly fair tree every strict local maximum of `V_B`
    is global** (`stronglyFair_strictLocalMax_isOptimal`, the strongly-fair form of dp-cf-2-026's
    extension question, stated open in r1), by induction on the set of moving points with the
    gated shape `value_deviate_eq_gated` at the point whose node has the smallest subtree.
  - `CoalitionWitness` (repair r1): the Definition 23 spectrum is strict on two points.
  - `ThreeCoalWitness` (repair r1): HA-9′'s three-point strictness table on `threeCoal` (T10(c)).
-/

import Cleanroom.Decision.DpLocalOpt.Sia
import Cleanroom.Decision.DpLocalOpt.ChainRule
import Cleanroom.Decision.DpLocalOpt.Trees
import Cleanroom.Decision.DpLocalOpt.Ssa
import Cleanroom.Decision.DpLocalOpt.Coherence
import Cleanroom.Decision.DpLocalOpt.AmdWitness
import Cleanroom.Decision.DpLocalOpt.TwoPointWitness
import Cleanroom.Decision.DpLocalOpt.Assignments
import Cleanroom.Decision.DpLocalOpt.Optima
import Cleanroom.Decision.DpLocalOpt.Coalition
import Cleanroom.Decision.DpLocalOpt.Witnesses
import Cleanroom.Decision.DpLocalOpt.Cells
import Cleanroom.Decision.DpLocalOpt.NestedWitness
import Cleanroom.Decision.DpLocalOpt.StrongFair
import Cleanroom.Decision.DpLocalOpt.GatedInduction
import Cleanroom.Decision.DpLocalOpt.CoalitionWitness
import Cleanroom.Decision.DpLocalOpt.ThreeCoalWitness
