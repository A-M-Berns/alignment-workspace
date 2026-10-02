import Cleanroom.Decision.DpFaithfulUdt.SelfConfirming
import Cleanroom.Decision.DpFaithfulUdt.Cluster

/-!
# Audit r2 (adversarial) probe: is `SelfConfirming` inhabited, and by what?

`SelfConfirming U B C' s₀ := MaskedPriorCalibrated (lift U C') (Rel_U B) s₀ ∧ TUdt s₀ (polEv U) C' B`
needs `FullSupport (lift U C')`, so no *deterministic* self-model is ever `SelfConfirming` as
defined — in particular the Stag Hunt's `(H,H)`, which the ledger's T4(a) row cites
(`twoStag_HH_fixedPoint`) as the witness of `selfConfirming_iff_nash`. That theorem shows
`Nash profHH` and `UDT = (H,H)` under a prior calibrated to the *trembled* `proc2 β β` (which is
not Nash for `β < ⅓`), i.e. it inhabits the negative side of the biconditional, not the positive
one. The predicate *is* inhabited: the tying full-support self-model `third = proc2 ⅓ ⅓` with its
prior-calibrated state (from `third_nash_coherent_not_udtProc` and the iff). Both facts below;
not imported by the library.
-/

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt

/-- `SelfConfirming` is inhabited (N+): the full-support Nash self-model `third` on the Stag Hunt
with a masked prior calibrated to it. -/
theorem third_selfConfirming :
    ∃ s₀ : State (RW MiniW (fun _ => Act2) Finset.univ) ℚ,
      SelfConfirming (Finset.univ : Finset Pt2) twoStag third s₀ := by
  obtain ⟨hnash, _, ⟨s₀, hcal⟩, _⟩ := third_nash_coherent_not_udtProc
  exact ⟨s₀, (selfConfirming_iff_nash _ _ _ s₀ twoStag_almostFair (Finset.subset_univ _)).mpr
    ⟨hcal, hnash⟩⟩

/-- A deterministic self-model is never `SelfConfirming` as defined: the mask needs full support of
`lift U C'`, whose root law at the tuple `(S,S)` is `0` under `profHH`. -/
theorem profHH_not_selfConfirming (s₀ : State (RW MiniW (fun _ => Act2) Finset.univ) ℚ) :
    ¬ SelfConfirming (Finset.univ : Finset Pt2) twoStag profHH s₀ := by
  rintro ⟨⟨hfs, _⟩, _⟩
  have hpos := hfs (.inr ()) (fun _ => Act2.a)
  have h1 := nu_polTuple_root (U := Finset.univ) (B := twoStag) (C'' := lift Finset.univ profHH)
    (fun _ => Act2.a)
  have h2 := nu_polTuple (U := Finset.univ) (B := twoStag) profHH (fun _ => Act2.a)
  rw [← h1, h2] at hpos
  refine absurd hpos (not_lt.mpr (le_of_eq ?_))
  apply Finset.prod_eq_zero
    (Finset.mem_univ (⟨Pt2.p1, Finset.mem_univ _⟩ : ↥(Finset.univ : Finset Pt2)))
  simp [profHH, proc2_p1]

end Cleanroom.Decision.DpFaithfulUdt

#print axioms Cleanroom.Decision.DpFaithfulUdt.third_selfConfirming
#print axioms Cleanroom.Decision.DpFaithfulUdt.profHH_not_selfConfirming
