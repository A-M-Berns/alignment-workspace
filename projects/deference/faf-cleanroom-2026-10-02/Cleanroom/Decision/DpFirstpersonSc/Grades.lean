import Cleanroom.Decision.DpFirstpersonSc.License
import Cleanroom.Decision.DpFirstpersonSc.Lift
import Cleanroom.Udt.UdtSupercondition.Landscape
import Cleanroom.Udt.UdtSupercondition.Calibration

/-!
# The audit in SC's landscape: the three grades (AN-6/7/8) — T5 of
[[dp-firstperson-sc-mandate]]

* **AN-6** (`audit_jeffreyOnA`): a state passing the audit is SC §4.6's Jeffrey update of the
  prior on the two-atom anticipation algebra `{E, Eᶜ}` with weights `(1, 0)` — `JeffreyOnA` with
  the evidence *fixed* to `E = occ(d)`. `L`: its bite is entirely in fixing the evidence; the
  syntax is SC's most restrictive evidence constraint.
* **Grade (i), Thm-4.5 reachability** (`reachable_iff_ac`): with the occurrence anticipation
  `condAnticipation (toPMF s₀.P) (evAtom E)` (calibrated by construction, prior-predictive `P_{s₀}`),
  *some* SC-calibrated conditioning model from `s₀` reaches `s` iff `P_s ≪ P_{s₀}` — by
  `udt-supercondition`'s `calibrated_condModel_iff` (Thm 4.5 as an iff) and finiteness. **AN-7**
  (`strictClausesAt_ac_priorState`): at the strict grade with `ν_C(O_d) > 0` every strict-OC state
  passes grade (i) — reachability rejects only fantasy states; at the limit grade with
  `ν_C(O_d) = 0` it fails (Told-You-So, `WitnessesLift.lean`). Thm 4.5 is idle for the audit
  because its models invent their own evidence (`reachable_evidence_idle`: the left side of
  `reachable_iff_ac` is the same proposition for every evidence event).
* **Grade (ii), the occurrence D–Z grade** (`ocState_boundedDensity_iff`,
  `mass_occ_le_nu_obs_iff`): the strict-OC state has density `≤ 1/μ(occ(d))` w.r.t. `ν` iff
  `ν(O_d) ≥ μ(occ(d))` iff `μ(occ(d) ∖ λ⁻¹O_d) ≤ μ(λ⁻¹O_d ∖ occ(d))` — the license test as an
  *inequality*.
* **Grade (iii)** is T2(a) (`audit_license_iff_nullDiff`): the inequality refined to an
  equality (both differences null).
* The four-row table is `WitnessesNewcomb.lean`.

Vocabulary: `AnticipationStructure.Calibrated`, `CMCalibrated` below are SC-internal
calibration (kernels = the prior's conditionals), never v2's external calibration.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree hiding mass mass_mono mass_union mass_univ mass_nonneg
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Cleanroom.Udt.UdtSupercondition
open scoped ENNReal
open Finset

/-! ## The two-atom evidence algebra -/

section evAtom

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The anticipation map of the two-atom algebra `{E, Eᶜ}`: `w ↦ [w ∈ E]`.
Source: `anticipation.md` AN-6 ("`Ā_occ` … the specific union `T_d`")
Kind: D -/
def evAtom (E : Finset W) : W → Bool := fun w => decide (w ∈ E)

/-- The `true` atom is `E`. Source: none: infrastructure. Kind: L -/
theorem evAtom_preimage_true (E : Finset W) : evAtom E ⁻¹' {true} = (↑E : Set W) := by
  ext w; simp [evAtom]

/-- **AN-6: audit-pass is SC's Jeffrey update with the evidence fixed.** A state that passes the
audit (one carrier) is `JeffreyOnA (P_{s₀}) (evAtom E) P_s` with weights `(1, 0)` on the atoms
`(E, Eᶜ)`: the §4.6 `Ā`-compatible posterior on the occurrence algebra. The converse is false
(a Jeffrey update may put weight on `Eᶜ`); the audit's content is the weight vector `(1,0)`, i.e.
the evidence `E`.
Source: `anticipation.md` AN-6 ("the audit … is SC §4.6's `Ā`-compatible Jeffrey update on
`Ā_occ` with the specific union `T_d`")
Kind: L
Fidelity: exact (`P`-clause; SC has no `V`)
Hyps: (a) audit-pass at `E` -/
theorem audit_jeffreyOnA (s₀ s : State W ℚ) (E : Finset W) (h : 0 < s₀.pr E)
    (hpass : AuditPassAt s₀ E h id s) :
    JeffreyOnA (toPMF s₀.P) (evAtom E) (toPMF s.P) := by
  have hag := (auditPassAt_id_iff s₀ E h s).mp hpass
  have hpos : 0 < mass (toPMF s₀.P) (evAtom E ⁻¹' {true}) := by
    rw [evAtom_preimage_true]; exact (mass_toPMF_pos_iff _ _).mpr h
  refine ⟨fun b => if b then 1 else 0, ?_, ?_, fun x => ?_⟩
  · rw [tsum_fintype, Fintype.sum_bool]; simp
  · intro b hb
    cases b
    · simp at hb
    · exact hpos
  · rw [tsum_fintype, Fintype.sum_bool]
    simp only [eq_self_iff_true, Bool.false_eq_true, if_true, if_false, one_mul, zero_mul,
      add_zero]
    rw [condKernel_of_pos _ _ _ hpos, condOn_congr _ (evAtom_preimage_true E) hpos,
      condOn_toPMF' _ _ h, ← jeffreyCond_P_eq_condDistr, hag.1]
    rfl

/-! ## Grade (i): Thm-4.5 reachability -/

/-- **Grade (i), Thm-4.5 reachability is absolute continuity.** With the occurrence anticipation
structure `(evAtom E, the prior's own conditionals)` — SC-calibrated by construction
(`AnticipationStructure.Calibrated`: its kernels are the prior's own conditionals; not v2's
external calibration), reflective, so its prior-predictive is `P_{s₀}` — an SC-calibrated
conditioning model (`CMCalibrated`) from `s₀` reaching `s` exists iff `P_s ≪ P_{s₀}` (every
`s₀`-null world is `s`-null). Through `udt-supercondition`'s Thm 4.5 as an iff
(`calibrated_condModel_iff`) and the finite D–Z reading (`boundedDensity_iff_of_fintype`). The
left side does not depend on `E` (`reachable_evidence_idle`).
Source: `anticipation.md` AN-7 ("a calibrated model from `s₀` reaches `s` iff
`P_s ≪ Q₀ = λ_*P_{s₀}`"), AN-8(i); `bridge-dossier.md` T21
Kind: C
Fidelity: exact (finite carrier)
Hyps: none -/
theorem reachable_iff_ac (s₀ s : State W ℚ) (E : Finset W) :
    (∃ m : CondModel (toPMF s₀.P) (toPMF s.P),
        CMCalibrated m (condAnticipation (toPMF s₀.P) (evAtom E))) ↔
      ∀ w, s₀.P.w w = 0 → s.P.w w = 0 := by
  have hr : (condAnticipation (toPMF s₀.P) (evAtom E)).priorPredictive = toPMF s₀.P :=
    reflective_condAnticipation (toPMF s₀.P) (evAtom E)
  rw [calibrated_condModel_iff, hr, boundedDensity_iff_of_fintype, toPMF_ac_iff]

/-- **Grade (i) does not see the evidence**: reachability under `evAtom E` is the same
proposition as under `evAtom E'` — AN-7's "Thm 4.5 is idle for the audit" made explicit.
Source: `anticipation.md` AN-7 ("reachability rejects only fantasy states"); audit r1
adversarial N8
Kind: L -/
theorem reachable_evidence_idle (s₀ s : State W ℚ) (E E' : Finset W) :
    (∃ m : CondModel (toPMF s₀.P) (toPMF s.P),
        CMCalibrated m (condAnticipation (toPMF s₀.P) (evAtom E))) ↔
      (∃ m : CondModel (toPMF s₀.P) (toPMF s.P),
        CMCalibrated m (condAnticipation (toPMF s₀.P) (evAtom E'))) := by
  rw [reachable_iff_ac, reachable_iff_ac]

/-- Degenerate check: the prior is reachable from itself under every evidence event.
Source: none: infrastructure (audit r1 adversarial N8). Kind: L -/
theorem reachable_self (s₀ : State W ℚ) (E : Finset W) :
    ∃ m : CondModel (toPMF s₀.P) (toPMF s₀.P),
      CMCalibrated m (condAnticipation (toPMF s₀.P) (evAtom E)) :=
  (reachable_iff_ac s₀ s₀ E).mpr fun _ h => h

end evAtom

/-! ## AN-7: the strict grade passes every strict-OC state -/

section an7

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]
  (obs : ι → Finset Ω) (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (d : ι)

/-- **AN-7 at the strict grade**: with `ν_C(O_d) > 0`, every state satisfying the strict clauses
at `d` is absolutely continuous w.r.t. the strict prior `ν_C` — so it passes grade (i)
(`reachable_iff_ac`): Thm-4.5 reachability rejects only states charging worlds no run reaches.
Source: `anticipation.md` AN-7 ("every observation-calibrated state is a conditional of the
audit's own prior-predictive, hence reachable: only … fantasy states are rejected")
Kind: P
Fidelity: exact (strict grade; the masked grade is the same statement under `C[d ↦ m]`)
Hyps: (a) `0 < ν(O_d)`, (a) `StrictClausesAt s obs C B d` -/
theorem strictClausesAt_ac_priorState (s : ι → State Ω ℚ) (hO : 0 < nu C B (obs d))
    (hs : StrictClausesAt s obs C B d) :
    ∀ ω, (priorState C B).P.w ω = 0 → (s d).P.w ω = 0 := by
  intro ω hω
  have hν : nu C B {ω} = 0 := by
    have := priorState_pr C B {ω}
    simp only [State.pr, probOf_singleton] at this
    rw [← this, hω]
  have h1 := hs.1 {ω}
  simp only [State.pr, probOf_singleton] at h1
  have hle : nu C B ({ω} ∩ obs d) ≤ nu C B {ω} := nu_mono C B Finset.inter_subset_left
  have hge : 0 ≤ nu C B ({ω} ∩ obs d) := nu_nonneg C B _
  have hzero : (s d).P.w ω * nu C B (obs d) = 0 := by linarith
  rcases mul_eq_zero.mp hzero with h | h
  · exact h
  · exact absurd h hO.ne'

/-- Grade (i) for a strict-OC state, packaged as the existence of an SC-calibrated model.
Source: `anticipation.md` AN-8(i) ("Thm-4.5 grade … passes")
Kind: C -/
theorem strictClausesAt_reachable (s : ι → State Ω ℚ) (hO : 0 < nu C B (obs d))
    (hs : StrictClausesAt s obs C B d) (E : Finset Ω) :
    ∃ m : CondModel (toPMF (priorState C B).P) (toPMF (s d).P),
      CMCalibrated m (condAnticipation (toPMF (priorState C B).P) (evAtom E)) :=
  (reachable_iff_ac (priorState C B) (s d) E).mpr (strictClausesAt_ac_priorState obs C B d s hO hs)

/-! ## Grade (ii): the occurrence D–Z grade -/

/-- `ν(O_d) ≥ μ(occ(d))` iff `μ(occ(d) ∖ λ⁻¹O_d) ≤ μ(λ⁻¹O_d ∖ occ(d))`.
Source: `anticipation.md` AN-8(ii) ("passes iff `ν(O_d) ≥ μ(occ(d))`, i.e. iff
`μ(occ(d) ∖ λ⁻¹O_d) ≤ μ(λ⁻¹O_d ∖ occ(d))`")
Kind: L -/
theorem mass_occ_le_nu_obs_iff :
    Tree.mass C B (occ d B) ≤ nu C B (obs d) ↔
      Tree.mass C B (occ d B \ worldEv B (obs d)) ≤ Tree.mass C B (worldEv B (obs d) \ occ d B) := by
  have hU : ∀ S T : Finset B.Leaves, S ∩ T ∪ S \ T = S := by
    intro S T; ext ℓ
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have h1 : Tree.mass C B (occ d B) =
      Tree.mass C B (occ d B ∩ worldEv B (obs d)) + Tree.mass C B (occ d B \ worldEv B (obs d)) := by
    rw [← Tree.mass_union C B (Finset.disjoint_sdiff_inter _ _).symm, hU]
  have h2 : nu C B (obs d) =
      Tree.mass C B (worldEv B (obs d) ∩ occ d B) + Tree.mass C B (worldEv B (obs d) \ occ d B) := by
    unfold nu
    rw [← Tree.mass_union C B (Finset.disjoint_sdiff_inter _ _).symm, hU]
  rw [h1, h2, Finset.inter_comm]
  constructor <;> intro h <;> linarith

/-- **Grade (ii), the occurrence D–Z grade for the strict-OC state**: `ν(· | O_d)` has density
bounded by `1/μ(occ(d))` w.r.t. `ν` iff `μ(occ(d)) ≤ ν(O_d)`. (The density of the OC state is
`1_{O_d}/ν(O_d)`, so the bound is `1/ν(O_d) ≤ 1/μ(occ(d))`.) Under coverage the right side of
`mass_occ_le_nu_obs_iff` is `0`: the grade passes iff simulation of `d` has `μ`-measure zero.
Source: `anticipation.md` AN-8(ii) ("the OC state's density is `1_{O_d}/ν(O_d)`, so it passes
iff `ν(O_d) ≥ μ(occ(d))`")
Kind: P
Fidelity: exact
Hyps: (a) `0 < ν(O_d)`, (a) `0 < μ(occ(d))` -/
theorem ocState_boundedDensity_iff (hO : 0 < nu C B (obs d)) (h : 0 < Tree.mass C B (occ d B)) :
    BoundedDensity (toPMF (calibratedState C B (obs d) hO).P) (toPMF (priorState C B).P)
        (ENNReal.ofReal ((Tree.mass C B (occ d B) : ℚ) : ℝ))⁻¹ ↔
      Tree.mass C B (occ d B) ≤ nu C B (obs d) := by
  rw [← ENNReal.ofReal_inv_of_pos (Rat.cast_pos.mpr h), ← Rat.cast_inv,
    boundedDensity_toPMF_iff _ _ _ (inv_nonneg.mpr h.le)]
  have hw : ∀ ω, (calibratedState C B (obs d) hO).P.w ω =
      if ω ∈ obs d then nu C B {ω} / nu C B (obs d) else 0 := fun _ => rfl
  have hp : ∀ ω, (priorState C B).P.w ω = nu C B {ω} := by
    intro ω
    have := priorState_pr C B {ω}
    simp only [State.pr, probOf_singleton] at this
    exact this
  simp only [hw, hp]
  constructor
  · intro hbd
    obtain ⟨ω, hωO, hων⟩ : ∃ ω ∈ obs d, 0 < nu C B {ω} := by
      by_contra hc
      push_neg at hc
      have : nu C B (obs d) = 0 := by
        rw [nu_eq_sum_singleton]
        exact Finset.sum_eq_zero fun ω hω => le_antisymm (hc ω hω) (nu_nonneg C B _)
      exact hO.ne' this
    have := hbd ω
    rw [if_pos hωO, div_eq_mul_inv, mul_comm] at this
    have := le_of_mul_le_mul_right this hων
    rwa [inv_le_inv₀ hO h] at this
  · intro hle ω
    split_ifs with hωO
    · rw [div_eq_mul_inv, mul_comm]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ h hle) (nu_nonneg C B _)
    · exact mul_nonneg (inv_nonneg.mpr h.le) (nu_nonneg C B _)

end an7

end Cleanroom.Decision.DpFirstpersonSc
