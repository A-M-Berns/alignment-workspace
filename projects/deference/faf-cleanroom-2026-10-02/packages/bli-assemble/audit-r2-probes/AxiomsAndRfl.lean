import Cleanroom.Bli.BliAssemble.Lia
import Cleanroom.Bli.BliAssemble.SmallList

/-!
# `bli-assemble` · audit round 2 (fidelity) probe: axioms of the proved rows, the `rfl`s the
package relies on, and that `smallList` is a compiled definition

Not imported by the library. Elaborated with `scripts/lean-check`.
-/

namespace Cleanroom.Bli.BliAssemble.AuditR2

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliTransfer
open Cleanroom.Bli.BliSuperbelief hiding smallIndex
open Cleanroom.Bli.BliAssemble

/-! ## Axioms: the proved rows must not use `sorryAx`; the open rows must -/

#print axioms bliHistory_eq_overlay
#print axioms denoteRat_chainExpr
#print axioms tentMap
#print axioms bliHistory_isLogicalInductor_of
#print axioms bli_hypotheses_paperDP
#print axioms bliHistory_ne_lia_from
#print axioms smallList_toFinset
#print axioms smallSorted_map_val
#print axioms writeOutCode_card_le_log
#print axioms exists_stateLearns_fixpoint_paperDP
#print axioms liaStates_eq_of_eq_prefix
#print axioms bliHistory_stateAtom_tendsto_one_of_stateLearns
#print axioms bliHistory_tent_package
#print axioms limitingBelief_bliHistory_eq
-- the open rows: `sorryAx` expected
#print axioms tentCertificate
#print axioms bliHistory_isLogicalInductor
#print axioms bli_package_paperDP
#print axioms bliHistory_isLogicalInductor_of_certificate

/-! ## The identities the package says are `rfl` -/

example : ratHistory liaBase = liaHistory (paperDP 𝗜𝚺₁) := rfl

example (Q : RatHistory) (𝓜 : Mesh) (sk : Skeleton smallIndex 𝓜.d) (c : StateCoding 𝓜)
    (n : ℕ) (ψ : Sentence) :
    bliPrice Q 𝓜 sk c n ψ = if SmallOn n ψ then Q n ψ else bliOv Q 𝓜 sk c n ψ := rfl

example (Q : History) (ov : ℕ → Sentence → ℚ) (k : ℕ) (ψ : Sentence) :
    overlay Q ov k ψ = if SmallOn k ψ then Q k ψ else (ov k ψ : ℝ) := rfl

/-! ## `smallList` is compiled: this `def` lives outside any `noncomputable section` -/

def smallListProbe (n : ℕ) : List Sentence := smallList n

/-! ## The dyadic mesh has `d 0 = 1` (program §7 item 11 asks `d ≥ 2`; day-`n` faces use `d (n+1)`) -/

example : dyadicMesh.d 0 = 1 := rfl
example : dyadicMesh.d 1 = 2 := rfl

end Cleanroom.Bli.BliAssemble.AuditR2
