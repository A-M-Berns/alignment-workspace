import Cleanroom.Udt.UdtEndorsePolicy.Structure

/-!
# Audit r2 (adversarial) probe: `hsep` is not a squeeze

`policyEndorsed_of_udtRule_of_separable` (repair round 1) has hypotheses `UdtRule`, `hcons`
(external-only chosen policy) and `hsep` (policy utility additively separable across inputs,
`E[U | Π̈ = π] = ∑_ö X(ö, π ö)`), and concludes `PolicyEndorsed`. The adversarial question: does
`hcons ∧ hsep` already force `PolicyEndorsed` (so that the rule is decorative and the theorem a
squeeze)? No. `CB8S` is `CB8`'s eight worlds, weights and factorization fields with the utility
`U(room, (b₀, b₁)) = ½·[b₀ = 1] + ½·[b₁ = 1]` (independent of the room): the chosen policy is
external-only, the policy utility is separable with the action-dependent table `X(ö, ä) = ½·[ä = 1]`,
the realized policies have utilities `0, ½, ½, 1` (not policy endorsed), and the pointwise rule
fails (at room `0`, action `0` scores `1/4` against `5/8`) — exactly as the theorem demands, since
its conclusion is false here. So the rule is load-bearing, and the theorem has content beyond its
hypotheses. Not imported by the library.
-/

namespace Cleanroom.Udt.UdtEndorsePolicy.AuditR2.CB8S

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

noncomputable section

/-- `U(room, (b₀, b₁)) = ½·[b₀ = 1] + ½·[b₁ = 1]`. -/
def U (ω : CB8.Ω) : ℝ := (if ω.2.1 = 1 then 1 / 2 else 0) + (if ω.2.2 = 1 then 1 / 2 else 0)

/-- `CB8`'s structure with the utility `U` (factorization fields carry over). -/
def absDS : AbstractDS CB8.Ω (Fin 1) (Fin 2) (Fin 1) (Fin 2) (Fin 1) (Fin 2) (Fin 2 × Fin 2) (Fin 1)
    (Fin 1) :=
  { CB8.absDS with
    U := U
    U_mem := fun ω => by unfold U; split_ifs <;> norm_num }

theorem polE_eq (ω : CB8.Ω) : absDS.polE ω = CB8.pol ω.2 :=
  absDS.polE_eq_of (fun ω e => CB8.pol ω.2 e) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ω

theorem w_eq (ω : CB8.Ω) : absDS.μ.w ω = (if ω.2 = (1, 1) then 1 else 3) / 20 := CB8.w_eq ω

theorem U_eq (ω : CB8.Ω) : absDS.U ω = U ω := rfl

theorem polS_eq (ω : CB8.Ω) (oe : Fin 1 × Fin 2) : absDS.polS ω oe = (0, CB8.pol ω.2 oe.2) := rfl

/-- The chosen policy is external-only (`hcons`). -/
theorem hcons (ω : CB8.Ω) (o : Fin 1) (e : Fin 2) : absDS.polS ω (o, e) = (0, absDS.polE ω e) := by
  show (0, CB8.pol ω.2 e) = (0, absDS.polE ω e)
  rw [polE_eq]

/-- The policy utility of `(b₀, b₁)` is `U` itself (`U` ignores the room). -/
theorem policyUtility_eq (ω : CB8.Ω) : absDS.policyUtility (absDS.polE ω) = U ω := by
  rw [polE_eq]
  unfold AbstractDS.policyUtility AbstractDS.evPolE
  rw [condExpJunk, mass_event_eq, sum_event_eq]
  obtain ⟨e, b₀, b₁⟩ := ω
  fin_cases e <;> fin_cases b₀ <;> fin_cases b₁ <;>
  · simp +decide only [polE_eq, U_eq, U, w_eq, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.isValue, Prod.mk.injEq]
    norm_num

/-- `hsep` holds with the action-dependent table `X(ö, ä) = ½·[ä = 1]`. -/
theorem policyUtility_separable (ω : CB8.Ω) :
    absDS.policyUtility (absDS.polE ω) =
      ∑ e : Fin 2, (fun (_ : Fin 2) (a : Fin 2) => if a = 1 then (1 / 2 : ℝ) else 0) e
        (absDS.polE ω e) := by
  rw [policyUtility_eq, polE_eq, Fin.sum_univ_two]
  obtain ⟨e, b₀, b₁⟩ := ω
  fin_cases b₀ <;> fin_cases b₁ <;> simp [U, CB8.pol]

/-- Not policy endorsed: `E[U | Π̈ = (1,1)] = 1 > 0 = E[U | Π̈ = (0,0)]`. -/
theorem not_policyEndorsed : ¬ PolicyEndorsed absDS := by
  intro h
  have := h (0, (0, 0)) (0, (1, 1))
  rw [policyUtility_eq, policyUtility_eq] at this
  norm_num [U] at this

/-- The two scores at room `0`: action `0` scores `1/4`, action `1` scores `5/8`. -/
theorem score_e0 (b : Fin 2) : absDS.score 0 0 (0, b) = if b = 0 then 1 / 4 else 5 / 8 := by
  unfold AbstractDS.score AbstractDS.evS
  rw [condExpJunk, mass_event_eq, sum_event_eq]
  fin_cases b <;>
  · simp +decide only [polS_eq, U_eq, CB8.pol, U, w_eq, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.isValue, Prod.mk.injEq]
    norm_num

/-- The pointwise rule fails (as the theorem says it must, its conclusion being false). -/
theorem not_udtRule : ¬ absDS.UdtRule := by
  intro h
  have h1 : absDS.score 0 0 (0, 1) ≤ absDS.score 0 0 (0, CB8.pol (0, 0) 0) :=
    h (0, (0, 0)) 0 0 (0, 1)
  have h2 : CB8.pol (0, 0) 0 = 0 := by decide
  rw [h2, score_e0, score_e0] at h1
  norm_num at h1

/-- **The probe's statement**: `hcons ∧ hsep` (with an action-dependent table) is compatible with
`¬ PolicyEndorsed`, and then `¬ UdtRule` — the rule carries the conclusion in
`policyEndorsed_of_udtRule_of_separable`; the separability hypothesis does not. -/
theorem hsep_not_squeeze :
    (∀ ω o e, absDS.polS ω (o, e) = (0, absDS.polE ω e)) ∧
      (∀ ω, absDS.policyUtility (absDS.polE ω) =
        ∑ e : Fin 2, (fun (_ : Fin 2) (a : Fin 2) => if a = 1 then (1 / 2 : ℝ) else 0) e
          (absDS.polE ω e)) ∧
      ¬ PolicyEndorsed absDS ∧ ¬ absDS.UdtRule :=
  ⟨hcons, policyUtility_separable, not_policyEndorsed, not_udtRule⟩

end

end Cleanroom.Udt.UdtEndorsePolicy.AuditR2.CB8S

#print axioms Cleanroom.Udt.UdtEndorsePolicy.AuditR2.CB8S.hsep_not_squeeze
