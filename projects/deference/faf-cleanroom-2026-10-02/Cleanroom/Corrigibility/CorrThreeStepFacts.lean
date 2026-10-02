import Cleanroom.Corrigibility.CorrThreeStepFacts.Basic
import Cleanroom.Corrigibility.CorrThreeStepFacts.StopWorld
import Cleanroom.Corrigibility.CorrThreeStepFacts.Erosion
import Cleanroom.Corrigibility.CorrThreeStepFacts.Identification
import Cleanroom.Corrigibility.CorrThreeStepFacts.Partition
import Cleanroom.Corrigibility.CorrThreeStepFacts.CommonPrior
import Cleanroom.Corrigibility.CorrThreeStepFacts.Hull
import Cleanroom.Corrigibility.CorrThreeStepFacts.Scan
import Cleanroom.Corrigibility.CorrThreeStepFacts.Accounting
import Cleanroom.Corrigibility.CorrThreeStepFacts.Dictionary
import Cleanroom.Corrigibility.CorrThreeStepFacts.Reliability
import Cleanroom.Corrigibility.CorrThreeStepFacts.WitnessesA
import Cleanroom.Corrigibility.CorrThreeStepFacts.WitnessesB
import Cleanroom.Corrigibility.CorrThreeStepFacts.WitnessesC
import Cleanroom.Corrigibility.CorrThreeStepFacts.WitnessesD
import Cleanroom.Corrigibility.CorrThreeStepFacts.Stretch

/-!
# `corr-three-step-facts`: the three-step model's facts — root module

The facts the corrigibility corpus built on the parent's Setting S (`Cleanroom.Found.CorrThreeStep`),
faf-cleanroom run, 2026-09-30. Namespace `Cleanroom.Corrigibility.CorrThreeStepFacts`.

* `Basic`: `Fintype Obs`, support positivity of the press-weighted expectation, `kernelProd`
  (prior ⊗ kernel on a product), `jointDistr` (the joint on `Ω × Obs`).
* `StopWorld` (T1–T3): the stop-world precondition and Prop. 8.1's R1 failure; the inert
  channel (a sensor constant in the world); the stop-hypothesis theorem as a well-posed pair on
  `Option Ωin` (necessity with lower-bound margins, sufficiency with exact margins, the collapse
  to `twoState`), the catastrophe tail.
* `Erosion` (T4): the silence update `erode`, the odds identity in product form, the erosion
  theorem, the crossing criterion, the per-decision hazard.
* `Identification` (T5, T6): the compliance record's fibre and the `[0, 1]` sweep of
  `P(W | Pr)`; scale invariance of the press branch, the silence-side monotonicity, the
  total-expectation theorem, the mixed sensor.
* `Partition` (T16): Good's theorem on a finite partition — value, coarsening, strictness — and
  the bridge to the parent's `voiButton`.
* `CommonPrior` (T8, T9, T11): Prop. 4.3 with its converse as an iff (refinement modulo null
  worlds), mm I9.5's screening-off sufficiency; disclosure as a sufficient statistic; the basin
  as finitely many linear inequalities with an explicit radius.
* `Hull` (mm open problem 6, repair round 1): the hull condition on pressed unions of cells —
  sufficient for question-relative deference (proved), strictly weaker than screening-off
  (`h3_hull`), and its necessity as the package's one OPEN statement.
* `Scan` (T18): pointwise trust after a scan in product form.
* `Accounting` (T7): the two accountings, `c + h = 1 + κ`.
* `Dictionary` (T13, T14, T17): the transform, the naive combination, the Gandhi anchor; the
  misspecification reading and I5.4; reflection toward oneself and Brier accuracy.
* `Reliability` (T15): amendment 1a as a likelihood-ratio condition, the live channel, dilution
  and the corrected `causal` toy, the reliability VOI.
* `Stretch` (T10, T12, T19–T25): the dictionary items, elementary limits, the OSG identities,
  Turner's toy, the coherence bound, the band lemma.
* `WitnessesA`–`D`: every N+/N− instance (see the report).
-/
