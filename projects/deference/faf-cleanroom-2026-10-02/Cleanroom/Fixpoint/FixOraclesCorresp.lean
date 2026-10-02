import Cleanroom.Fixpoint.FixOraclesCorresp.Defs
import Cleanroom.Fixpoint.FixOraclesCorresp.Existence
import Cleanroom.Fixpoint.FixOraclesCorresp.Lifts
import Cleanroom.Fixpoint.FixOraclesCorresp.OracleDefs
import Cleanroom.Fixpoint.FixOraclesCorresp.OracleExists
import Cleanroom.Fixpoint.FixOraclesCorresp.Liar
import Cleanroom.Fixpoint.FixOraclesCorresp.NashReflective
import Cleanroom.Fixpoint.FixOraclesCorresp.Correlated
import Cleanroom.Fixpoint.FixOraclesCorresp.Composition
import Cleanroom.Fixpoint.FixOraclesCorresp.TaylorOlah
import Cleanroom.Fixpoint.FixOraclesCorresp.Operator
import Cleanroom.Fixpoint.FixOraclesCorresp.PenniesGadget
import Cleanroom.Fixpoint.FixOraclesCorresp.GameR
import Cleanroom.Fixpoint.FixOraclesCorresp.Sandwich
import Cleanroom.Fixpoint.FixOraclesCorresp.CorrelatedEq
import Cleanroom.Fixpoint.FixOraclesCorresp.GameBridge
import Cleanroom.Fixpoint.FixOraclesCorresp.Elementary
import Cleanroom.Fixpoint.FixOraclesCorresp.BrouwerOnly

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp`: convex-graph correspondences and finite reflective oracles

Root module of the `fix-oracles-corresp` work package (faf-cleanroom run, 2026-09-30). Part A refutes
and repairs the `internal-fixpoint/reflective-oracles-project/` claims about correspondences
`Δ(X) ⇉ Δ²(X)` with convex graphs; Part B formalizes the finite abstract core of
Fallenstein–Taylor–Christiano 2015 (*Reflective Oracles*) over `fix-kakutani` and EconCSLib's mixed
Nash equilibrium. See `run/wp/fix-oracles-corresp/fix-oracles-corresp-report.md`.

* `Defs`: `FinMeasure` (Δ² as finitely supported measures), `bary`, `dirac`, `Graph`,
  `HasConvexGraph`, `IsDiracFixedPoint`, `IsCollapseFixedPoint`, `diracLift`, `baryLift`.
* `Existence`: the "generalized Kakutani" refuted as stated (`not_generalizedKakutaniClaim_fin2`,
  also with closed and compact graph), and the repair `exists_collapse_fixed_point` via
  `kakutani_findim`.
* `Lifts`: the Dirac lift has convex graph iff `f` is constant (and `negation`'s Dirac lift has none:
  `not_hasConvexGraph_diracLift_negation`); the barycentric lift has convex graph iff `f` is affine
  and its Dirac and collapse fixed points are `Fix f`; negation and identity.
* `OracleDefs`: `Reflective`, `signStep`, `oracleCorr`, the cube; fixed points of `oracleCorr` in the
  cube are the reflective vectors; closedness of a sign-step graph.
* `OracleExists`: `exists_reflective` (continuous evaluation maps, via `kakutani_pi_Icc`, closed
  graph proved), the polynomial corollary, matching pennies (N+, cross-checked with `mpBR`); Theorem
  2.1 (ii)'s finite analogue `exists_reflectiveOn` (App. B's route: reflective on a finite `R`,
  prescribed off `R`; `I` arbitrary, continuity only on `R`) with its two-query and self-referential
  witnesses and its degenerate ends (`R = ∅`, `R = univ`).
* `Liar`: the liar's unique reflective answer `1 − p`, no deterministic answer, non-strict variant
  unsatisfiable; whole-graph convexification destroys reflectivity; the set-valued N+ witness of
  `exists_collapse_fixed_point`.
* `NashReflective`: two-action games over EconCSLib (`twoActionGame`, FAF form `twoActionFAF`),
  `toCube`/`ofCube`, linearity of `expectedPayoff`, `gain`/`evOf`; Theorem 3.1 as a sign identity;
  Theorem 4.1 `isMixedNashEq_iff_reflective`; two-action Nash existence; matching pennies.
* `Correlated`: correlated fixed points of a relation; Kakutani-free existence for total relations
  (periodic orbit of a selection); negation (unique, mass on 50 %), identity (diagonal measures,
  marginal onto `Δ(X)`), a non-total relation with none.
* `Composition`: `comp`; total convex-graph relations compose, closedness composes over a compact
  middle set; a Kakutani pair whose composite is not convex-valued; fixed points of total closed
  convex-graph relations; cyclic points of a cycle of Kakutani maps and the composite's fixed point,
  instantiated on the two-cycle `x ↦ {1 − x}`, `y ↦ {y}` (unique cyclic point `![1/2, 1/2]`).
* `TaylorOlah`: the objective `v_d(d')`, optimality, existence via `kakutani_findim` (argmax
  correspondence: nonempty, convex, closed graph proved), the four-action example's unique optimum
  `![1/2, 0, 1/2, 0]` and no pure optimum.
* `Operator`: `Fix` is not Hausdorff-continuous along the affine sup-norm-continuous family
  `shrinkTo c ε`, and neither is the Dirac fixed-point set of the `CGC` members
  `baryLift (shrinkTo c ε)` (the notes' own objects); the notes' `g_ε` is neither continuous nor a
  self-map, the corrected `h_ε`, and `Fix (x ↦ x³)` is not convex.
* `PenniesGadget`: Lemma A.1 (the variant Matching Pennies forces `P(Row = Down) = P(Matrix = Back)`)
  in an ambient two-action game, with the marginalization lemma `sum_prod_agreeInd`.
* `GameR`: Theorem 5.1, abstract polynomial version — every mixed Nash equilibrium of `G_R` induces a
  reflective answer vector for `polyEv c d` (copy forcing, independent copies give the powers); on
  the liar's `G_R` every equilibrium has the main player at `1 − p` (`gameR_liar_forces_main`); the
  `G_R`-based analogue of Theorem 2.1 (ii) that FTC §5 omits (`substOff`, `restrictDeg`,
  `polyEv_extendBy`, `gameR_nash_reflectiveOn`, `exists_reflectiveOn_via_gameR`), with the witness
  `gameR_prodLiar_forces_main_one/_zero` where the prescription off `R` changes the forced answer.
* `Sandwich`: the finite-state eval sandwich, the a.s.-halting corollary, the two-state loop.
* `CorrelatedEq`: correlated equilibria, convexity of the CE set, Nash ⊆ CE (product weights), the
  two-action CE set is nonempty, the bridge to FAF's `Game.Correlated`.
* `GameBridge`: mixed Nash agrees across `twoActionGame u` and `(twoActionFAF u).toStrategic`.
* `Elementary`: fixpoint-lit-013's two elementary facts.
* `BrouwerOnly` (target 19, the extension): Kakutani-free existence of reflective oracles —
  Brouwer (FAF's `brouwer_fixed_point`, transported by `brouwer_findim`) on the clamp step
  `x ↦ clamp₀₁ (x + (ev x − p))`, whose fixed points in the cube are *exactly* the reflective
  vectors (`clampStep_eq_iff_reflective`); hence polynomial reflective oracles, two-action Nash
  equilibria, Theorem 5.1's route and both analogues of Theorem 2.1 (ii) (App. B's and the `G_R`
  one) all exist with Brouwer alone (Kakutani-freeness probe-checked at the proof-term level); and
  Nash's own normalized map (`nashStep`), whose fixed points are reflective for `evOf` at `1/2`, gives
  two-action Nash existence independently of the clamp step (`exists_isMixedNashEq_nashMap`), so
  Theorem 5.1's `G_R` route is a genuinely independent second proof
  (`exists_reflective_via_gameR_nashMap`, probe-checked).
-/
