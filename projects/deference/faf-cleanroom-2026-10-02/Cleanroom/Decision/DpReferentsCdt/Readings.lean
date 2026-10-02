import Cleanroom.Decision.DpReferentsCdt.Defs

/-!
# The two readings of R2-real agree at F3′ points

Mandate T1(b): the two readings of dp-sl-2-058 — reading 1 (`refR2Real`, Definition F2's letter:
reach-weighted forcing over the node-action-veridical `d`-nodes, unconditioned on `O_d`) and reading
2 (`refR2RealObs`, both sums restricted to the leaves whose world lies in `O_d`) — coincide wherever
every node-action-veridical `d`-node is subtree-veridical (F3′'s first clause): the `O_d`-filter is
then the identity on every real-fiber subtree. They differ on the post-act coin tree (`Rows.lean`),
which fails that clause. Findings F1 records the ill-posedness; this file is the half that says
where it is harmless.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

section readings

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- Reading 2's numerator is reading 1's when every real-fiber node is subtree-veridical.
Source: dp-sl-2-058; mandate T1(b)
Kind: L -/
theorem realForcedObs_eq_realForced_of_subtreeVeridical {d : ι}
    (h : ∀ q ∈ realFiber actEv B d, SubtreeVeridical obs B q) (a : acts d) :
    realForcedObs obs actEv C B d a = realForced actEv C B d a := by
  unfold realForcedObs realForced
  refine Finset.sum_congr rfl fun q hq => ?_
  split_ifs with hpt
  · unfold forcedBelow
    rw [Finset.filter_true_of_mem]
    intro ℓ hℓ
    have := h q hq ℓ hℓ
    rwa [hpt] at this
  · rfl

/-- Reading 2's denominator is reading 1's (`R_q`) when every real-fiber node is subtree-veridical.
Source: dp-sl-2-058; mandate T1(b)
Kind: L -/
theorem realReachObs_eq_realReach_of_subtreeVeridical {d : ι}
    (h : ∀ q ∈ realFiber actEv B d, SubtreeVeridical obs B q) :
    realReachObs obs actEv C B d = realReach actEv C B d := by
  unfold realReachObs realReach
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [reach_eq_mass_leavesBelow, Finset.filter_true_of_mem]
  · rfl
  · intro ℓ hℓ
    have := h q hq ℓ hℓ
    rwa [((mem_realFiber actEv B d q).mp hq).1] at this

/-- **The two readings of R2-real agree wherever every node-action-veridical `d`-node is
subtree-veridical** (F3′'s first clause): the `O_d`-filter is the identity on every real-fiber
subtree, so reading 2 (`O_d`-conditioned forcing) is reading 1 (Definition F2's letter).
Source: dp-sl-2-058 (the two readings); `repair/C1.md` Open 3; mandate T1(b)
Kind: P
Fidelity: exact
Hyps: (a) subtree-veridicality of the real fiber -/
theorem refR2RealObs_eq_refR2Real_of_subtreeVeridical {d : ι}
    (h : ∀ q ∈ realFiber actEv B d, SubtreeVeridical obs B q) (a : acts d) :
    refR2RealObs obs actEv C B d a = refR2Real actEv C B d a := by
  unfold refR2RealObs refR2Real
  rw [realForcedObs_eq_realForced_of_subtreeVeridical obs actEv C B h,
    realReachObs_eq_realReach_of_subtreeVeridical obs actEv C B h]

/-- **At an F3′ point (for any procedure) the two readings of R2-real coincide**: `ActRecording`'s
first clause is exactly subtree-veridicality of the real fiber.
Source: dp-sl-2-058; `faithful.md` Definition F3′; mandate T1(b)
Kind: C
Fidelity: exact
Hyps: (a) `ActRecording obs actEv C' B d` for some `C'` (only its structural first clause is used) -/
theorem refR2RealObs_eq_refR2Real_of_actRecording {d : ι} {C' : Proc ι acts K}
    (hA : ActRecording obs actEv C' B d) (a : acts d) :
    refR2RealObs obs actEv C B d a = refR2Real actEv C B d a :=
  refR2RealObs_eq_refR2Real_of_subtreeVeridical obs actEv C B
    (fun q hq => hA.1 q ((mem_realFiber actEv B d q).mp hq).1 ((mem_realFiber actEv B d q).mp hq).2)
    a

/-- The same under F3′ structural. Source: mandate T1(b). Kind: C -/
theorem refR2RealObs_eq_refR2Real_of_structural {d : ι}
    (hS : ActRecordingStructural obs actEv B d) (a : acts d) :
    refR2RealObs obs actEv C B d a = refR2Real actEv C B d a :=
  refR2RealObs_eq_refR2Real_of_actRecording obs actEv C B (hS.actRecording C) a

end readings

end Cleanroom.Decision.DpReferentsCdt
