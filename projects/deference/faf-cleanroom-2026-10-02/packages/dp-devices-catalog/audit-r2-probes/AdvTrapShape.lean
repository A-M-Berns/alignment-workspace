import Cleanroom.Decision.DpDevicesCatalog.Remark314
import Cleanroom.Decision.DpDevicesCatalog.Values

set_option autoImplicit false

/-!
# `dp-devices-catalog` · audit round 2 (adversarial) · probe II: the shape of `Trap`/`Dilemma`

Evidence file for `dp-devices-catalog-audit-r2-adversarial.md`. **Not imported by the library.**
(The parallel fidelity probe `DilemmaNoSelection.lean` covers the all-procedures class; these
are the complementary checks.)

* Q3 — the zero-respecting class is non-empty at **every** instantiation (`edtProc` is always a
  member), so `FailsRegardlessOfLabel`'s universal over the class is never discharged by an empty
  class; together with round 1's P4 (a calibrated member exists) the trap verdicts' first
  conjunct is substantive.
* Q4 — the strict-dilemma witness label `tysStateOne` puts mass `1` at `d₅` on the world
  `(5,10)`, which no procedure realizes with positive probability: the `π = 1` label is certain
  of an unreachable world, and its strict calibration at `d₅` is Definition 8's unconstrained
  clause only (round 1's P3), as SL-17 itself says.
* Q5 — threshold sensitivity of `Dilemma`: lowering the "good outcome" to `5` makes masked
  Told-You-So a `Dilemma` (the class attains `5` at a calibrated label). `Dilemma v` reads
  "the class attains `v` somewhere", not "the verdict depends on the label".
* Q6 — SL-17's third application ("a two-round tree punishing every crossing is a trap and no
  dilemma") is rendered by **neither** definition, as the docstrings disclose: on `coinQuery`
  (every payoff `0`) with the class of all procedures and good outcome `1`, the class fails
  regardless of label, no procedure is outside the class, and no member attains `1` — so
  `¬ Trap ∧ ¬ Dilemma ∧ FailsRegardlessOfLabel`.
-/

namespace Cleanroom.Decision.DpDevicesCatalog.AuditR2

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpDevicesCatalog

/-- Q3: the zero-respecting class is inhabited at every instantiation. -/
theorem Q3_zeroRespClass_nonempty (I : Instance TysW Five10 (fun _ => Five10) ℚ) :
    (zeroRespClass I).Nonempty :=
  ⟨edtProc I.s tysActEv, edtProc_zeroRespecting I.s tysActEv⟩

/-- Q4: the `π = 1` label is certain of `(5,10)`, a world of probability `0` under every
procedure. -/
theorem Q4_tysStateOne_unreachable :
    (tysStateOne .five).pr {(Five10.five, Five10.ten)} = 1 ∧
    ∀ C : Proc Five10 (fun _ => Five10) ℚ, nu C toldYouSo {(Five10.five, Five10.ten)} = 0 := by
  constructor
  · simp only [tysStateOne]; rw [State.dirac_pr]; simp
  · intro C; rw [tys_nu]; simp

/-- Q5: with the good outcome lowered to `5`, masked Told-You-So is a `Dilemma` for the
zero-respecting class (`C₀` attains `5` at the stipulated, masked-calibrated label). -/
theorem Q5_dilemma_at_five : Dilemma .masked tysObs sigmaTys zeroRespClass 5 :=
  ⟨⟨toldYouSo, tysState⟩, rfl, procFiveTen, tys_zeroRespecting.1, tys_fiveTen_maskedOC,
    by rw [procFiveTen_value]⟩

/-- Q6: a problem that fails regardless of label with no way out is neither a `Trap` nor a
`Dilemma` (SL-17's "a trap and no dilemma" is not rendered, as disclosed). -/
theorem Q6_coinQuery_neither :
    FailsRegardlessOfLabel .strict cqObs {I | I.B = coinQuery} (fun _ => Set.univ) 1 ∧
    ¬ Trap .strict cqObs {I | I.B = coinQuery} (fun _ => Set.univ) 1 ∧
    ¬ Dilemma .strict cqObs {I | I.B = coinQuery} (fun _ => Set.univ) 1 := by
  refine ⟨fun I hI C _ _ => ?_, fun h => ?_, fun h => ?_⟩
  · have hB : I.B = coinQuery := hI
    rw [hB, coinQuery_value]; norm_num
  · obtain ⟨-, I, -, C, hC, -, -⟩ := h
    exact hC (Set.mem_univ C)
  · obtain ⟨I, hI, C, -, -, hv⟩ := h
    have hB : I.B = coinQuery := hI
    rw [hB, coinQuery_value] at hv
    norm_num at hv

end Cleanroom.Decision.DpDevicesCatalog.AuditR2
