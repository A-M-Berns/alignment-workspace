import Cleanroom.Decision.DpEdtUdtFair.Theorem3

/-!
# Open statements of `dp-edt-udt-fair` (listed in `run/wp/dp-edt-udt-fair/dp-edt-udt-fair-open.txt`)

* `fairClass_eventTremble_exists_open` — **T6(b), FR-13 existence**: some deterministic procedure
  is event-tremble-EDT-consistent on every `B ∈ 𝔉`. Route: leaves-up on CA-3′'s stratification,
  choosing at each point a lexicographic argmax of the trembled values (rational in `ε`:
  compare lowest-order coefficients via `dp-calibration`'s `PosTrail`/`natTrailingDegree`).
  Per-tree instances are proved: `fr12` (`(out, x)`, `fr12_eventTremble_iff`), `fantasy241`
  (`inX`), `dupPay 1 0` (`δ_a`), `twoPoint 4 4 4` (every procedure). Not attempted in round 0;
  repair round 1 proved the untrembled leaves-up argmax (`exists_pointwise_best`,
  `Assignment.lean`), which is the `ε = 0` shadow of this route — the remaining gap is the
  lexicographic tie-break in `ε` (the untrembled argmax need not survive the tremble: `fr12`'s
  `(out, y)` is a pointwise best response in `Q` and D2-rejected).

T5 (`stronglyFair_assignment_open`) and T12(b) (`fairClass_dfMasked_isOptimal_open`) were listed
here in round 0 and are **proved** in repair round 1: `stronglyFair_assignment` (`Assignment.lean`)
and `fairClass_dfMasked_isOptimal` (`DfTheorem.lean`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-- **OPEN (T6(b)): FR-13 existence on `𝔉`.** Some deterministic procedure is event-tremble-EDT-
consistent. Route in the module docstring; per-tree instances proved in `FairWitnesses.lean`.
Do not cite `dp-calibration`'s `testSeq_exists_open` for this (different device, over `ℝ`).
Source: `fair-repair.md` FR-13; `adversary-repair.md` A.3 ("FR-13 SURVIVES as existence");
A36 (i); `calibration.md` CA-12′ (ii)
Kind: OPEN
Fidelity: exact
Hyps: (a) `FairClass` -/
theorem fairClass_eventTremble_exists_open [∀ d, Nonempty (acts d)] {obs : ι → Finset Ω}
    {actEv : (d : ι) → acts d → Finset Ω} {B : Tree Ω ι acts K} (_h : FairClass obs actEv B) :
    ∃ σ : (d : ι) → acts d, EventTrembleEdtConsistent obs actEv (Proc.ofFun σ) B := by
  sorry

end Cleanroom.Decision.DpEdtUdtFair
