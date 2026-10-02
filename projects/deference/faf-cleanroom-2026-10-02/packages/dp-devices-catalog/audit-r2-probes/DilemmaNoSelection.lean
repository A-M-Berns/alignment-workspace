import Cleanroom.Decision.DpDevicesCatalog.Remark314

/-!
Audit round 2 (fidelity) probe for `dp-devices-catalog`, `Remark314.lean`.

Claim probed: `Dilemma κ obs AP 𝒞 v` (= "some member of the class attains `v` at some
`κ`-calibrated instantiation") carries no "selection" half: it is satisfied by a class that
*never* fails at any label. Witness: the class of **all** procedures (`fun _ => Set.univ`) is
a `Dilemma` on `Σ_{B_P}` at every sense at which `C*` is calibrated somewhere — strict (at
`tysStateOne`), limit (at `tysState`), masked (at `tysStateWayOut`). So `tys_strict_dilemma`
proves exactly "the zero-respecting class does not fail regardless of label", and the other
half of SL-17's "dilemma of selection" (a calibrated label at which the class *does* fail,
`π = 0`) lives in `tys_value_of_zeroRespecting` + `tys_fiveTen_strictOC`, outside `Dilemma`.
Not imported by the library. -/

namespace Cleanroom.Decision.DpDevicesCatalog

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

/-- P1: the all-procedures class is a strict `Dilemma` on `Σ_{B_P}`. -/
theorem probe_dilemma_univ_strict : Dilemma .strict tysObs sigmaTys (fun _ => Set.univ) 10 :=
  ⟨⟨toldYouSo, tysStateOne⟩, rfl, procTake10, Set.mem_univ _, procTake10_strictOC_one,
    by rw [procTake10_value]⟩

/-- P2: the all-procedures class is a limit `Dilemma` on `Σ_{B_P}` (at the stipulated label). -/
theorem probe_dilemma_univ_limit : Dilemma .limit tysObs sigmaTys (fun _ => Set.univ) 10 :=
  ⟨⟨toldYouSo, tysState⟩, rfl, procTake10, Set.mem_univ _, tys_take10_limitOC,
    by rw [procTake10_value]⟩

/-- P3: the all-procedures class is a masked `Dilemma` on `Σ_{B_P}` (at the way-out label). -/
theorem probe_dilemma_univ_masked : Dilemma .masked tysObs sigmaTys (fun _ => Set.univ) 10 :=
  ⟨⟨toldYouSo, tysStateWayOut⟩, rfl, procTake10, Set.mem_univ _, procTake10_maskedOC_wayOut,
    by rw [procTake10_value]⟩

/-- P4: the strict "selection" half the package proves outside `Dilemma`: at the stipulated
label `π = 0` every zero-respecting member gets `5 < 10`, and `C₀` is strictly calibrated there. -/
theorem probe_strict_failing_label :
    (∀ C, ZeroRespecting tysState tysActEv C → value C toldYouSo < 10) ∧
    StrictOC tysState tysObs procFiveTen toldYouSo :=
  ⟨fun C h => by rw [tys_value_of_zeroRespecting C h]; norm_num, tys_fiveTen_strictOC⟩

end Cleanroom.Decision.DpDevicesCatalog
