import Cleanroom.Deference.DefSqueezeDiamond.SelfInstance
import Cleanroom.Found.LiQuoteLane.Witnesses

/-!
# audit r2 (adversarial) probe: the mandate's 4d witness — the paper expert read by a genuinely
distinct novice (li-quote-lane's harmonic pair)

Repair round 1 wrote the instantiation of `towerValuedBase_of_totalTrustBase'` on
`P := liaHistory harmonicProcess`, `A := liaHistory (paperDP 𝗜𝚺₁)`, said it compiled in the full
build, and withdrew it from `Witness.lean` so that li-quote-lane's listed OPEN statement
(`readability_fails_without_generability`, imported through `Witnesses`) would not enter the
package's transitive axiom profile (report §4d, handoff item 5). The claim "it compiles" was not
machine-checked by anyone but the repairer. This probe elaborates it (the mandate's exact 4d
shape, both arrows, plus the gap clause with no antecedent), so the non-deference hypotheses of
load-bearing 3's arrows — the inductor instance, `hworld`, `ExtendsBase` — are shown inhabited
by a pair that is not the diagonal. The deference antecedent `hT` remains a hypothesis (N−
(diag), as the ledger says). Positive check; not imported by the library; its own axiom profile
would carry li-quote-lane's listed `sorryAx` only through the `Witnesses` import's closure, not
through any term used here.
-/

namespace Cleanroom.Deference.DefSqueezeDiamond.AuditR2

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefSelfTrust
open Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSqueezeDiamond
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-- The harmonic novice extends the paper expert's process. -/
theorem harmonic_extendsBase : ExtendsBase 𝗜𝚺₁ harmonicProcess :=
  extendsBase_ledger 𝗜𝚺₁ harmonicTable (fun _ => PublicationSchedule.succ)

/-- The pinned gap packages for the paper expert over the harmonic novice: no antecedent. -/
example : PinnedGapPackagesBase 𝗜𝚺₁ harmonicProcess
    (paperExpert 𝗜𝚺₁ succDeferral harmonicProcess) :=
  pinnedGapPackagesBase_paperExpert 𝗜𝚺₁ succDeferral succDeferral_strict harmonic_extendsBase

/-- Total Trust ⟹ Tower for the harmonic novice reading the paper expert (the 4d shape). -/
example (hT : TotalTrustBase 𝗜𝚺₁ (liaHistory harmonicProcess) harmonicProcess
      (paperExpert 𝗜𝚺₁ succDeferral harmonicProcess)) :
    TowerValuedBase 𝗜𝚺₁ (liaHistory harmonicProcess) harmonicProcess
      (paperExpert 𝗜𝚺₁ succDeferral harmonicProcess) :=
  haveI := harmonic_inductor
  towerValuedBase_of_totalTrustBase' 𝗜𝚺₁ succDeferral succDeferral_strict harmonic_extendsBase
    harmonic_hworld hT

/-- Tower ⟹ Total Trust for the harmonic novice reading the paper expert. -/
example (hT : TowerValuedBase 𝗜𝚺₁ (liaHistory harmonicProcess) harmonicProcess
      (paperExpert 𝗜𝚺₁ succDeferral harmonicProcess)) :
    TotalTrustBase 𝗜𝚺₁ (liaHistory harmonicProcess) harmonicProcess
      (paperExpert 𝗜𝚺₁ succDeferral harmonicProcess) :=
  haveI := harmonic_inductor
  totalTrustBase_of_towerValuedBase 𝗜𝚺₁ succDeferral succDeferral_strict harmonic_extendsBase
    harmonic_hworld hT

/-- The 4d instantiation as a named theorem, so its axiom profile can be printed: the round-2
fidelity audit's probe of the same name reported `[propext, Classical.choice, Quot.sound]` (no
`sorryAx` from li-quote-lane's listed OPEN); this file was overwritten by the adversarial
auditor before that probe was committed, and the named theorem is restored here so the
committed file carries the check both audits cite. -/
theorem probe_harmonic_novice
    (hT : TotalTrustBase 𝗜𝚺₁ (liaHistory harmonicProcess) harmonicProcess
      (paperExpert 𝗜𝚺₁ succDeferral harmonicProcess)) :
    TowerValuedBase 𝗜𝚺₁ (liaHistory harmonicProcess) harmonicProcess
      (paperExpert 𝗜𝚺₁ succDeferral harmonicProcess) :=
  haveI := harmonic_inductor
  towerValuedBase_of_totalTrustBase' 𝗜𝚺₁ succDeferral succDeferral_strict harmonic_extendsBase
    harmonic_hworld hT

#print axioms probe_harmonic_novice

end

end Cleanroom.Deference.DefSqueezeDiamond.AuditR2
