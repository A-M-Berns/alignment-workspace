import Cleanroom.Found.FixKakutani.Defs
import Cleanroom.Found.FixKakutani.Selection
import Cleanroom.Found.FixKakutani.ClosedGraph
import Cleanroom.Found.FixKakutani.Kakutani
import Cleanroom.Found.FixKakutani.Transport
import Cleanroom.Found.FixKakutani.Witness
import Cleanroom.Found.FixKakutani.WitnessSimplex

/-!
# `Cleanroom.Found.FixKakutani`: Kakutani's fixed-point theorem from FAF's Brouwer

Root module of the `fix-kakutani` work package (faf-cleanroom run, 2026-09-29). Dependents
import this one name.

* `Defs`: `HasClosedGraphOn F K` (the definition of record), its sequential characterization,
  section closedness, and `restrictTo`.
* `Selection`: `exists_approx_selection`, the approximate continuous selection lemma (proved).
* `ClosedGraph`: the hemicontinuity bridge to Mathlib's `UpperHemicontinuousOn` and the
  closed-graph limit step `mem_of_hasClosedGraphOn_of_tendsto_approx`.
* `Kakutani`: `kakutani_euclidean`, on `EuclideanSpace ℝ (Fin d)`, from
  `LogicalInduction.brouwer_fixed_point`.
* `Transport`: `kakutani_findim` (any finite-dimensional real normed space),
  `kakutani_pi_stdSimplex` (products of standard simplices), `kakutani_pi_Icc` (the cube).
* `Witness`: matching pennies on the cube (N+, with no continuous selection), the round trip to
  Brouwer, three sharpness examples, and `wedgeF` on `Icc 0 1` (a second N+ witness whose
  unique fixed point has a singleton value and which has no continuous selection; also a direct
  instance of `exists_approx_selection`).
* `WitnessSimplex`: matching pennies on the product of simplices (N+ for
  `kakutani_pi_stdSimplex`, transported from the cube, with the same certificates).

Discharge recipe for consumers: state your domain as one of `K ⊆ EuclideanSpace ℝ (Fin d)`,
`K ⊆ E` finite-dimensional, `Set.univ.pi (fun i => stdSimplex ℝ (A i))` or
`Set.univ.pi (fun _ : Q => Icc 0 1)`; prove values-in-domain, nonempty, convex, and
`HasClosedGraphOn F domain` (usually via `hasClosedGraphOn_iff_seq_of_isClosed`); then `exact`
the matching theorem above.
-/
