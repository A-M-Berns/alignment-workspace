import Cleanroom.Decision.DpEdtUdtFair

/-!
# `dp-edt-udt-fair` · audit round 2 (adversarial) · probe P1: axioms of the repair-round-1 headlines, and the DF rows are not vacuous

Evidence file for `dp-edt-udt-fair-audit-r2-adversarial.md`. **Not imported by the library.**

* `#print axioms` on every headline added or changed in repair round 1 (T5, T12(b), CA-3′,
  CA-2′(i), the D1 clauses, `permPay`, T16(b), ZO-2's chain, `N3 ↔ N1`, A.1's device rows, the
  pinned mugging witness) and on the two load-bearing theorems: none may rest on `sorryAx`.
* `fr12_outY_dfMasked_exists` — the universally quantified negative clause of
  `fr12_outY_isOptimal_not_dfMasked_tEdt` ("for every DF state assignment `s`, `T_EDT` fails")
  is not vacuous: `(out, y)` *has* a DF state assignment on `fr12`.
* `dfMasked_tEdt_exists_iff_forall` — on `𝔉` the DF verdict does not depend on the state
  assignment: "some DF `s` approves `C`" and "every DF `s` approves `C`" coincide (so the
  `∀ s` in the negative rows and the `∃ s` in the positive rows are the same device).
-/

namespace Cleanroom.Decision.DpEdtUdtFair.AuditR2

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

#print axioms stronglyFair_assignment
#print axioms stronglyFair_assignment_max
#print axioms exists_pointwise_best
#print axioms dupPay_assignment_witness
#print axioms fairClass_dfMasked_isOptimal
#print axioms FairClass.dfMasked_tEdt_iff
#print axioms FairClass.exists_dfMasked
#print axioms FairClass.exists_dfMasked_tEdt_ofFun
#print axioms FairClass.dfMasked_tEdt_of_eventTremble
#print axioms fr12_outY_isOptimal_not_dfMasked_tEdt
#print axioms dupPay_dfMasked_witness
#print axioms stronglyFair_size_lt_of_strictlyBelow
#print axioms outY_limitStateEdt
#print axioms threat_outY_untrembled_all
#print axioms fantasy_outY_untrembled_all
#print axioms permPay_theorem3_witness
#print axioms frec_not_subtreeVeridical_refuted
#print axioms FairClass.zo2_chain
#print axioms almostFair_N3_iff_N1
#print axioms a1Node_fr11_device
#print axioms a1Node_not_occTremble
#print axioms mug1_graded_witness_13
#print axioms claim32_refuted
#print axioms eventTrembleEdt_isOptimal_of_fairClass
#print axioms graded_fr11

/-- `(out, y)` has a DF state assignment on `fr12`, so the `∀ s, DFMasked s … → ¬ TEdt s …` clause
of `fr12_outY_isOptimal_not_dfMasked_tEdt` is a statement about a nonempty set of `s`. -/
theorem fr12_outY_dfMasked_exists : ∃ s, DFMasked s twoObs outY fr12 := by
  obtain ⟨hF, -, -, -, -, -, -⟩ := fr12_outY_isOptimal_not_eventTremble
  exact hF.exists_dfMasked outY

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]
variable {obs : ι → Finset Ω} {actEv : (d : ι) → acts d → Finset Ω}

/-- On `𝔉` the DF-`T_EDT` verdict is state-assignment-independent. -/
theorem dfMasked_tEdt_exists_iff_forall [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) (C : Proc ι acts K) :
    (∃ s, DFMasked s obs C B ∧ TEdt s actEv C B) ↔
      ∀ s, DFMasked s obs C B → TEdt s actEv C B := by
  constructor
  · rintro ⟨s, hs, hT⟩ s' hs'
    exact (h.dfMasked_tEdt_iff s' hs').mpr ((h.dfMasked_tEdt_iff s hs).mp hT)
  · intro H
    obtain ⟨s, hs⟩ := h.exists_dfMasked C
    exact ⟨s, hs, H s hs⟩

end Cleanroom.Decision.DpEdtUdtFair.AuditR2
