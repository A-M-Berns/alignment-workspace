import Cleanroom.Corrigibility.CorrReflectFrames.Defs
import Cleanroom.Corrigibility.CorrReflectFrames.Basic
import Cleanroom.Corrigibility.CorrReflectFrames.Collapse
import Cleanroom.Corrigibility.CorrReflectFrames.Selection
import Cleanroom.Corrigibility.CorrReflectFrames.Twist
import Cleanroom.Corrigibility.CorrReflectFrames.Support
import Cleanroom.Corrigibility.CorrReflectFrames.Legit
import Cleanroom.Corrigibility.CorrReflectFrames.Compose
import Cleanroom.Corrigibility.CorrReflectFrames.Good
import Cleanroom.Corrigibility.CorrReflectFrames.Bridge
import Cleanroom.Corrigibility.CorrReflectFrames.MetaBelief
import Cleanroom.Corrigibility.CorrReflectFrames.Accuracy
import Cleanroom.Corrigibility.CorrReflectFrames.Viability
import Cleanroom.Corrigibility.CorrReflectFrames.Clarity
import Cleanroom.Corrigibility.CorrReflectFrames.Slips
import Cleanroom.Corrigibility.CorrReflectFrames.SelfRef
import Cleanroom.Corrigibility.CorrReflectFrames.WitnessesA
import Cleanroom.Corrigibility.CorrReflectFrames.WitnessesB
import Cleanroom.Corrigibility.CorrReflectFrames.WitnessesC
import Cleanroom.Corrigibility.CorrReflectFrames.Dominance
import Cleanroom.Corrigibility.CorrReflectFrames.Expanded
import Cleanroom.Corrigibility.CorrReflectFrames.WitnessesD
import Cleanroom.Corrigibility.CorrReflectFrames.WitnessesE
import Cleanroom.Corrigibility.CorrReflectFrames.WitnessesF

/-!
# corr-reflect-frames — root module

Reflection forms, superconditioning and legitimizing events on `lit-ddb-frames`' finite frames
and `udt-supercondition`'s anticipation structures (faf-cleanroom run, 2026-09-30).

* `Defs`: value/estimate cells, `ValueReflects`, `VarReflects`, `EstimateMatching`,
  `CandsIntrospective` (INT at candidates), `restrict` and the homogeneity lemmas,
  `LegitimizingVal`/`LegitimizingTT`, `condRow`/`refineFrame`/`selectFrame`/`RetainsGrounds`.
* `Basic`: cell-grouped sums, INT consequences, `reflects_cell_sum`.
* `Collapse` (T1, T2(a)): the seven arrows of Theorem I4.1 / Theorem A, `collapse` (TFAE),
  the INT-free forms `Reflects ↔ Φ ∧ CandsIntrospective`, Theorem A(c), stationarity.
* `Selection` (T9(a)): refinements are reflective and immodest; the selection theorem in per-`k`
  retention form; R1.1 as a corollary.
* `Twist` (T2(b)(c)): the twist family (estimate-matching, not introspective, not reflected);
  fn 18's two witnesses.
* `Support` (T4): zero → positive forbidden (Reflection, value form, Total Trust; ddb L-A).
* `Legit` (T6, T11): ratio forms, closure structure, defect decomposition, per-cell mass bounds
  and the summed finite bound; partition lemma; the two senses coincide under INT.
* `Compose` (T7): the mixture identity; function form composes; the T16 transport identity.
* `Good` (T10): finite Jensen for `max`, Good's theorem, Prop 5′.
* `Bridge` (T3(a), T0): `Introspective`, Theorem A over anticipation structures, the frame bridge.
* `MetaBelief` (T3(b)–(e)): `metaJoint`, the existence form, uniqueness, the refuted fixed-joint
  reading, D–Z finite re-exported.
* `Accuracy` (T5(a)): Brier accuracy from value-form reflection.
* `Viability` (T8): conditional independence given the cell partition; `σ(O)`-events; Blackwell
  legitimizing events.
* `Clarity` (T12, T13(a), T16(a)): clarity TFAE, the world-independent push, the transport squeeze.
* `Slips` (T17): MM's Table 2 recomputed.
* `SelfRef` (T13(c)): `SelfRefSpace`, `IsUniversal`, the OPEN universal existence (repair r1).
* `Dominance` (T9(e)): cell-constant choices (the twisted successor's) are weakly dominated by
  the refinement's cellwise maximizer (repair r1).
* `Expanded` (T14): factorization identity, the convex-hull characterization of mixed
  utilities, the point martingale (repair r1).
* `Witnesses*`: the N+ witnesses (see the report); `WitnessesD`–`F` were built in repair round 1
  (T8(b)(c), T16(b), T9(b)(c)(g), T10's instances, the positive T7 witness, the twist instance).
-/
