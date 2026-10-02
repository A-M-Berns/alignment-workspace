import Cleanroom.Uea.UeaSelfGame.Defs
import Cleanroom.Uea.UeaSelfGame.FinSums
import Cleanroom.Uea.UeaSelfGame.Tables
import Cleanroom.Uea.UeaSelfGame.TablesMixed
import Cleanroom.Uea.UeaSelfGame.Repaired
import Cleanroom.Uea.UeaSelfGame.Static
import Cleanroom.Uea.UeaSelfGame.TheoremA
import Cleanroom.Uea.UeaSelfGame.Tightness
import Cleanroom.Uea.UeaSelfGame.TightnessT3
import Cleanroom.Uea.UeaSelfGame.Attainment
import Cleanroom.Uea.UeaSelfGame.StagHunt
import Cleanroom.Uea.UeaSelfGame.Existence
import Cleanroom.Uea.UeaSelfGame.Herrmann
import Cleanroom.Uea.UeaSelfGame.Section6
import Cleanroom.Uea.UeaSelfGame.Witness8801
import Cleanroom.Uea.UeaSelfGame.Floored
import Cleanroom.Uea.UeaSelfGame.ChosenEnacted
import Cleanroom.Uea.UeaSelfGame.Witnesses
import Cleanroom.Uea.UeaSelfGame.FlooredFamily
import Cleanroom.Uea.UeaSelfGame.Regimes
import Cleanroom.Uea.UeaSelfGame.FlooredBridge
import Cleanroom.Uea.UeaSelfGame.T3Family
import Cleanroom.Uea.UeaSelfGame.Open

/-!
# `Cleanroom.Uea.UeaSelfGame`: the updateless self-game — UDT1.0 that believes it is UDT1.1

Root module of the `uea-self-game` work package (faf-cleanroom run, 2026-09-30). A separate finite
formalism from `uea-cole-shadow`'s sequential model by design ([[plan]] §0.4 rule 10): no bridge, no
import from that package.

* `Defs`: the finite updateless self-game (`Game`), beliefs `muSelf`/`mu`, the Herrmann conditional
  `cond`/`avail`/`IsArgmaxH`/`Realizes`/`TB`, pure and floored pure fixed points; mixed policies, the
  product self-hypothesis, `Ucoord`, the extended conditional `Fext`, `IsFPext`/`IsFPherr`, floored mixed
  fixed points; the pure/mixed bridge and `FP_ext ⊆ FP_Herr` (definitions of record).
* `FinSums`, `Tables`, `TablesMixed`: instance infrastructure (sums over `Fin n → A`, tables, `Ucoord` as
  explicit sums).
* `Repaired`: the self-posterior identity proved; self-evidence; Theorems C, C′ (Herrmann and extension),
  D (pure).
* `Static`: Theorem B (the margin theorem) with converse.
* `TheoremA`: the proposed theorem refuted, uniformly in `δ`.
* `Tightness`, `TightnessT3`, `Attainment`: T1, T2 at symbolic `δ`; the §5.5 conjecture refuted by exact
  `T3` instances; the constant `δ/(1−δ)` never attained.
* `StagHunt`: both pure fixed points at every `δ`; the trust bound rejects `HH` iff `δ < (15−√97)/16`.
* `Existence`: mixed plain and floored fixed points for every instance by Kakutani under the continuous
  extension, closed graph proved.
* `Herrmann`: the `|S| = 1` witness; the Herrmann map has no closed graph.
* `Section6`, `Witness8801`: the §6 instance has no pure fixed point (plain or floored, any convention) and
  the exact mixed fixed point `q = (86 + √8801)/180`.
* `Floored`: Theorem D's mixed claim refuted exactly (`section_5`).
* `ChosenEnacted`: reading C1 (Theorem E, the near-tie instance), C2 (the reduction), C0; Prop 2's
  threshold as the C1 threshold.
* `Witnesses` (repair round 1): N+ witnesses for Theorem B (fixed-`η` table, deviation available), its
  converse (the note's margin-zero instance), Theorem D pure (`T2.isPureFPfloored`; `T1` is *not* floored),
  Theorem E (a margin-satisfying C1 instance); Theorem A's support clause and the `Bel` row.
* `FlooredFamily` (repair round 1): the mandate's `stretch` family for Theorem D's mixed claim at symbolic
  `δ ∈ (0, 1/4]` — a floored extension fixed point with gap `2q(1−q) ∈ [2δ − 8δ³, 2δ + 2δ³/(1−δ)]`, so no
  bound `U* − cδ/(1−δ)` holds with `c < 2` (`constant_ge_two`); consistent with `floored_mixed_bound_open`.
* `Regimes` (repair round 2): the two regimes of Theorem C's constant — the gap is `≤ 1` always, so the
  previous form of `sup_limit_open` was false above `δ = 1/2` (`sup_limit_previous_form_false_above_half`);
  the content regions of Theorems C/C′/D (`δ < 1/2`) and of the open mixed bound (`δ < 1/3`); above `1/2`
  the maximal gap `1` is attained — a symbolic family on `Fin 3` for `δ ∈ [2/3, 1)`
  (`GapOne.gap_one_attained`) and the auditor's exact instance at `δ = 3/4` (`GapOneAttained`).
* `FlooredBridge` (repair round 2): `IsFlooredFPext (pureMix π) → IsPureFPfloored π` (the extension floored
  notion is the stronger at pure policies; the converse fails on the `|S| = 1` instance), and the inclusion
  conjecture holds unconditionally at `|S| = 1` (`exists_isFPext_pureMix_fin1`).
* `T3Family` (repair round 2, continuation): the general `T3(n, θ, g)` family at symbolic parameters —
  the eight conditionals in closed form, the exact fixed-point and trust-bound conditions
  (`isPureFP_iff`, `TB_zero_iff`, `TB_succ_iff`), the parametric theorem `family`; **`sup_limit`**: on
  `δ ≤ 1/2` the gap approaches `δ/(1−δ)` (formerly the OPEN `sup_limit_open`), so with
  `Attainment.theoremC_strict` the constant is the exact, unattained supremum there; and
  **`gap_one_attained_above_half`**: for every `δ ∈ (1/2, 1)` the gap `1` is attained.
* `Open`: the open statements (inclusion conjecture, corrected mixed floored bound).
-/
