import Cleanroom.Decision.DpFirstpersonSc.Lift
import Cleanroom.Decision.DpFirstpersonSc.Grades
import Cleanroom.Decision.DpFirstpersonSc.WitnessesAudit

/-!
# Witnesses for T4, T5(b), T8: `B₁` matched, and Told-You-So at the limit grade

* **AN-2 / AN-11 on the matched mugging** (`q = q₀`, tails-certain state `mugState1`): forward
  absolute continuity `P_s ≪ ν` holds (`mug1_forward_ac`: `ν` is full-support), the forward
  density bound `‖dP_s/dν‖_∞ ≤ 1/μ(occ(d)) = 1` **fails** (`mug1_density_bound_fails`:
  `P_s(T,pay) = q₀` against `ν(T,pay) = q₀/2`, density `2 > 1`), and reverse absolute continuity
  fails (`mug1_reverse_ac_fails`: `P_s(H,⊥,1) = 0 < q₀/2 = ν(H,⊥,1)`), so **no same-ontology
  conditioning model leads from `s` to the audit's referent** (`mug1_no_sameOntology`) — "trust
  `s₀` over `s`" is replacement, not update (T8's three conditions as three declarations).
  With `perRunClause1_boundedDensity`: the D–Z bound is necessary only (the tails-certain state
  fails it and fails per-run clause 1, `mug1_tailsCertain_not_perRun`).
* **Definition 10 outside the hierarchy / AN-7 at the limit grade** (`tys_take5_limit_not_ac`,
  `tys_take5_limit_not_reachable`): under `procTake5` the limit-calibrated state at `d₁₀`,
  `δ_{(10,5)}` (`dp-calibration`'s `tys_take5_limitOC_at_ten_of_certain_105`), charges a world
  `ν_C = δ_{(5,5)}` gives mass `0`: no same-ontology model from `ν_C` reaches it, and Thm-4.5
  reachability (grade (i)) rejects it — absolute continuity is not preserved under `ε → 0`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree hiding mass mass_mono mass_union mass_univ mass_nonneg
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Cleanroom.Udt.UdtSupercondition
open scoped ENNReal
open Finset

/-! ## The matched mugging -/

section mug

variable (x y q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1)

/-- The prior state's atoms on `B₁` under `procQ q₀`. Source: none: infrastructure. Kind: L -/
theorem mug1_priorState_w (ω : MugW) :
    (priorState (procQ q₀ h0.le h1.le) (mug1 x y)).P.w ω = nu (procQ q₀ h0.le h1.le) (mug1 x y) {ω} := by
  have := priorState_pr (procQ q₀ h0.le h1.le) (mug1 x y) {ω}
  simp only [State.pr, probOf_singleton] at this
  exact this

/-- The tails-certain state's atoms: `(q₀, 1 − q₀, 0, 0)`.
Source: [[decision-problems-v2]] Proposition 6 (`P_s(T) = 1`, `P_s(pay) = q₀`)
Kind: L -/
theorem mugState1_w :
    (mugState1 x y q₀ h0.le h1.le).P.w .tPay = q₀ ∧
    (mugState1 x y q₀ h0.le h1.le).P.w .tRefuse = 1 - q₀ ∧
    (mugState1 x y q₀ h0.le h1.le).P.w .hOne = 0 ∧
    (mugState1 x y q₀ h0.le h1.le).P.w .hZero = 0 := by
  have hw : ∀ ω, (mugState1 x y q₀ h0.le h1.le).P.w ω =
      if ω ∈ mugObs () then nu (procQ q₀ h0.le h1.le) (mug1 x y) {ω} /
        nu (procQ q₀ h0.le h1.le) (mug1 x y) (mugObs ()) else 0 := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hw, mug1_nu, mugObs, procQ] <;> field_simp <;> ring

/-- **Forward absolute continuity holds** on the matched `B₁`: `ν` charges every world.
Source: `anticipation.md` AN-11 ("forward absolute continuity `P_s ≪ λ_*μ(· | occ(d))` holds")
Kind: N+ -/
theorem mug1_forward_ac (ω : MugW) :
    (priorState (procQ q₀ h0.le h1.le) (mug1 x y)).P.w ω = 0 →
      (mugState1 x y q₀ h0.le h1.le).P.w ω = 0 := by
  intro h
  rw [mug1_priorState_w x y q₀ h0 h1, mug1_nu] at h
  exfalso
  cases ω <;> simp [procQ] at h <;> linarith

/-- **The forward density bound fails** on the matched `B₁`: `μ(occ(d)) = 1`, so the bound is
`1`, but `P_s(T,pay)/ν(T,pay) = 2`.
Source: `anticipation.md` AN-2(ii), AN-11 ("the forward density bound … fails (`2 > 1`)")
Kind: N+ -/
theorem mug1_density_bound_fails :
    ¬ BoundedDensity (toPMF (mugState1 x y q₀ h0.le h1.le).P)
      (toPMF (priorState (procQ q₀ h0.le h1.le) (mug1 x y)).P)
      (ENNReal.ofReal ((Tree.mass (procQ q₀ h0.le h1.le) (mug1 x y) (occ () (mug1 x y)) : ℚ) : ℝ))⁻¹ := by
  rw [mug1_occ, Tree.mass_univ]
  intro hbd
  have h1' : BoundedDensity (toPMF (mugState1 x y q₀ h0.le h1.le).P)
      (toPMF (priorState (procQ q₀ h0.le h1.le) (mug1 x y)).P) (ENNReal.ofReal (1 : ℚ)) := by
    simpa using hbd
  rw [boundedDensity_toPMF_iff _ _ _ zero_le_one] at h1'
  have := h1' .tPay
  rw [(mugState1_w x y q₀ h0 h1).1, mug1_priorState_w x y q₀ h0 h1, mug1_nu] at this
  simp [procQ] at this
  linarith

/-- **Reverse absolute continuity fails**: the referent charges the heads world `(H,⊥,1)` that the
tails-certain state rules out.
Source: `anticipation.md` AN-2(iii), AN-11 ("reverse absolute continuity … fails")
Kind: N+ -/
theorem mug1_reverse_ac_fails :
    (mugState1 x y q₀ h0.le h1.le).P.w .hOne = 0 ∧
      0 < (priorState (procQ q₀ h0.le h1.le) (mug1 x y)).P.w .hOne := by
  refine ⟨(mugState1_w x y q₀ h0 h1).2.2.1, ?_⟩
  rw [mug1_priorState_w x y q₀ h0 h1, mug1_nu]
  simp [procQ]
  linarith

/-- **T8, AN-11: no conditioning model leads from the tails-certain state to the audit's
referent** — "trust `s₀` over `s`" is replacement, not update, from `s`'s standpoint.
Source: `anticipation.md` AN-11 ("No `𝓔`-compatible conditioning model exists with prior the
tails-certain `s` and posterior `λ_*μ(· | occ(d))`"); `firstperson.md` FP-23′
Kind: N+ -/
theorem mug1_no_sameOntology :
    ¬ Nonempty (SameOntologyModel (toPMF (mugState1 x y q₀ h0.le h1.le).P)
      (toPMF (priorState (procQ q₀ h0.le h1.le) (mug1 x y)).P)) :=
  not_sameOntology_of_zero _ _ .hOne (mug1_reverse_ac_fails x y q₀ h0 h1).1
    (mug1_reverse_ac_fails x y q₀ h0 h1).2

end mug

/-! ## Told-You-So at the limit grade -/

section tys

/-- Under take-5 at both points, `ν = δ_{(5,5)}`: the world `(10,5)` is null.
Source: [[decision-problems-v2]] Lemma 2 proof
Kind: L -/
theorem tys_take5_priorState_w_105 :
    (priorState procTake5 toldYouSo).P.w (Five10.ten, Five10.five) = 0 := by
  have := priorState_pr procTake5 toldYouSo {(Five10.ten, Five10.five)}
  simp only [State.pr, probOf_singleton] at this
  rw [this, tys_nu]
  simp [procTake5]

/-- **Definition 10 is outside the same-ontology hierarchy relative to `ν_C` at a null
observation**: the limit-calibrated state `δ_{(10,5)}` at `d₁₀` under take-5 charges a
`ν_C`-null world, so no same-ontology model from `ν_C` reaches it.
Source: `anticipation.md` AN-13 ("Def 10 … at `ν_C(O_d) = 0` outside the hierarchy relative to
`ν_C` (Told-You-So take-5-both `d₁₀`: limit state `δ_{(10,5)} ⊄ δ_{(5,5)}`)")
Kind: N+ -/
theorem tys_take5_limit_not_ac :
    ¬ Nonempty (SameOntologyModel (toPMF (priorState procTake5 toldYouSo).P)
      (toPMF (State.dirac ((Five10.ten, Five10.five) : TysW) (5 : ℚ)).P)) :=
  not_sameOntology_of_zero _ _ (Five10.ten, Five10.five) tys_take5_priorState_w_105 (by
    show (0 : ℚ) < if (Five10.ten, Five10.five) = (Five10.ten, Five10.five) then 1 else 0
    simp)

/-- **AN-7 at the limit grade fails**: Thm-4.5 reachability (grade (i)) rejects the
limit-calibrated state `δ_{(10,5)}` from the strict prior `ν_C = δ_{(5,5)}` — although it is
limit-calibrated at `d₁₀` (`tys_take5_limitOC_at_ten_of_certain_105`): absolute continuity is
not preserved under `ε → 0` (Lemma 2's separation in SC's vocabulary).
Source: `anticipation.md` AN-7 ("At the limit grade with `ν_C(O_d) = 0` this fails"), Dead 3
Kind: N+ -/
theorem tys_take5_limit_not_reachable (E : Finset TysW) :
    ¬ ∃ m : CondModel (toPMF (priorState procTake5 toldYouSo).P)
        (toPMF (State.dirac ((Five10.ten, Five10.five) : TysW) (5 : ℚ)).P),
      CMCalibrated m (condAnticipation (toPMF (priorState procTake5 toldYouSo).P) (evAtom E)) := by
  rw [reachable_iff_ac]
  intro h
  have := h (Five10.ten, Five10.five) tys_take5_priorState_w_105
  simp [State.dirac, State.ofConst] at this

end tys

end Cleanroom.Decision.DpFirstpersonSc
