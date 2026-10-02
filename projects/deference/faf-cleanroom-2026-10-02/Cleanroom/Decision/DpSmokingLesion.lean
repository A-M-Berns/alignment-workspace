import Cleanroom.Decision.DpSmokingLesion.Defs
import Cleanroom.Decision.DpSmokingLesion.General
import Cleanroom.Decision.DpSmokingLesion.Lemma3
import Cleanroom.Decision.DpSmokingLesion.Prop11
import Cleanroom.Decision.DpSmokingLesion.Prop13
import Cleanroom.Decision.DpSmokingLesion.Prop13Mug
import Cleanroom.Decision.DpSmokingLesion.Prop14E13
import Cleanroom.Decision.DpSmokingLesion.Prop14E2a
import Cleanroom.Decision.DpSmokingLesion.Prop14
import Cleanroom.Decision.DpSmokingLesion.Tickle12
import Cleanroom.Decision.DpSmokingLesion.Mixture
import Cleanroom.Decision.DpSmokingLesion.Steelman
import Cleanroom.Decision.DpSmokingLesion.Witnesses
import Cleanroom.Decision.DpSmokingLesion.Pooled
import Cleanroom.Decision.DpSmokingLesion.Stretch

/-!
# `dp-smoking-lesion`: Smoking Lesion — recording, the two consistent homes, Proposition 13

Root module of the package `Cleanroom.Decision.DpSmokingLesion`; dependents (`dp-two-lesions`)
import this one name. Files:

* `Defs` — definitions of record ([[dp-smoking-lesion-mandate]] §3): events, `O_d = ⊤`, (S2),
  the lesion parameters and the catalogue trees (`slOne`, `cexA`, `e2a`, `e13`, `slOneCausal`),
  the predicate forms of (S1) (`LesionOnlyAt`, `PostQueryIndep`), the referents (R1-state,
  R2-SIA, R2-real in both readings), `Σ_SL(S1–S3)` and `Σ_SL(S1–S4)`.
* `General` — the finite-tree theorems: EV = R1-state under `RecordsFor` for `C` alone (T3(a)),
  EV = R2-SIA = R2-real under `H*` (T3(b)), post-query screening at a recorded `O_d = ⊤` point
  (T1(c)).
* `Lemma3` — T1: Lemma 3 as printed refuted by coverage failure (counterexample A), the
  repaired lemma on `slOne` (shape form and through the general theorems), the flipped table.
* `Prop11` — T2: Proposition 11 refuted as printed (E2a: (S2) at the calibrated state for every
  procedure, all three OC grades; `Σ_SL(S1–S3)` consistent for every `C`) and true under (S4)
  (general, on `slOne`, and as `¬ Consistent κ ⊤ Σ_SL(S1–S4) C`).
* `Prop13` — T3(c)(d)(f): the shared argmax on `A_d^+` (R1-state under recording for `C`,
  R2-SIA under `H*`) as iffs of orders; the limit, masked (recording for the self-model) and
  SSC grades (`H*`; per-occurrence via almost-fairness on positive runs); the headline corollary
  (no calibrated state has the textbook contrast) and the `α`-gap on `slOne`.
* `Prop13Mug` — T3(e): the mugging refutes the R2-SIA clause under `RecordsFor` alone; R2-real
  reading 2 agrees with EV there; the act-recording mugging separates the two readings.
* `Prop14E13` — T4(c)(d): the compulsion E13 (honest at all five grades, covered but not
  recorded, R2-real undefined) and `e13Rec` with the draw recorded; T11's `occ = univ` bridge.
* `Prop14E2a` — T4(b): the reference class E2a (honest at the OC grades, not covered, screened
  at both SSC grades; the verdicts at `δ_refrain`, `δ_smoke` and `½`).
* `Prop14` — T4(a)(e): the only-if at the three OC grades and the two homes separated.
* `Tickle12` — T5, T6: the sign law, calibrated EDT populations (smoke–smoke, Rosa's split),
  Proposition 12's flatness at each point, recording on the tickle tree, the strict-grade
  vacuity finding and the masked rider.
* `Mixture` — T7: Appendix B item 4 under (S4) (finite mixtures of recording instantiations
  violate (S2)) and its failure with one non-recording component.
* `Steelman` — T8, T9, T12: the two-type tree, `T_opt` from the bilinear value (E3 `−45`, E4
  `5`, E8 `500 500`), act-event UDT at a Definition-11 prior, the steelman's clause-2 failure
  iff under (M) with its exact boundary, R1-state vs the tremble limit at `(1, 0)`.
* `Witnesses` — T10, T13, T14: "Why Ain'cha Rich" on the four trees, the unobserved parent as
  coverage failure, the cosmic-ray tree.
* `Pooled` — T15: no OC sense gives the label alone at a pooled point; the per-run state knows
  the type.
* `Stretch` — T17, T19: E2a's closed forms in the share `π` (at `C(d) = ½`, refrain iff
  `π < 783/784`; at `δ_smoke`, `V(smoke) − V(refrain) = 1000(π − 783)/(π + 1) < 0`); the
  hidden-state action law is flat in the lesion on `slOne` for every procedure and
  `ℓ`-dependent on the tickle tree iff `q₁ ≠ q₀`.
-/
