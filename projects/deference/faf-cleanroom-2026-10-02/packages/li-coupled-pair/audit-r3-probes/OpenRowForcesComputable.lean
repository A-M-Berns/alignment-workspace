import Cleanroom.Li.LiCoupledPair.A.Open

/-!
# Audit round 3 (adversarial) probe: no degenerate discharge of the OPEN two-way row

Audit r2 (adversarial N6) argued that the OPEN `twoWayPair_exists` cannot be met by a
non-computable or `Classical.choice` pair, because FAF's `IsLogicalInductor` carries
`processComputable` as a field. This probe machine-checks that argument at the pinned statement:
any inhabitant of the row makes `A`'s coupled process `ledgerProcess (paperDP 𝗜𝚺₁) aH
(fun _ => payoutSchedule)` — whose table `aH` is `H`'s realized expectations — a
`ComputableDeductiveProcess`, and likewise `H`'s. So a discharge must exhibit computable mutual
tables, which is exactly what `UniformLIAEvaluator` buys; the row is open for the stated reason and
not for want of a trick. Not imported by the library.
-/

namespace Cleanroom.Li.LiCoupledPair.AuditR3

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair

/-- Any pair meeting the OPEN row's pins has a computable `A`-side process. -/
theorem open_row_forces_computableA (p : TwoWayPair) (hA : p.DPA0 = paperDP 𝗜𝚺₁)
    (hσ : p.σ = fun _ => payoutSchedule) :
    ComputableDeductiveProcess (ledgerProcess (paperDP 𝗜𝚺₁) p.aH (fun _ => payoutSchedule)) := by
  have h := p.A_inductor.processComputable
  rwa [hA, hσ] at h

/-- Any pair meeting the OPEN row's pins has a computable `H`-side process. -/
theorem open_row_forces_computableH (p : TwoWayPair) (hH : p.DPH0 = paperDP 𝗜𝚺₁)
    (he : p.e = fun _ => PublicationSchedule.succ) :
    ComputableDeductiveProcess
      (ledgerProcess (paperDP 𝗜𝚺₁) p.aA (fun _ => PublicationSchedule.succ)) := by
  have h := p.H_inductor.processComputable
  rwa [hH, he] at h

end Cleanroom.Li.LiCoupledPair.AuditR3
