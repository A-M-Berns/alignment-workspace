import Cleanroom.Decision.DpLearnerNr.RefuserTrap

/-!
# Audit r3 (adversarial) probe: DY-15's clause 2 as rendered is blind to the heads branch

`calibratedState C B O` reads only `ν_C(· ∩ O)` and `paySum_C(· ∩ O)` (`calibratedState_congr`),
so the refuser's Proposition-6 state at `O_T` is the `O_T`-conditional state of *every* mugging
whose tails leaves agree with `mug1`'s — including the pays-regardless mugging
`mugPaysRegardless`, under which the refuser's data are *informative*
(`refuser_informative_paysRegardless`: `hOne` has mass `½` there and `0` on `mug1`). So
`refuser_mixture_calibrated` exercises "the two trees agree on the tails leaves", not
"likelihood ratio 1" (`refuser_nu_eq`): clause 2 does not single out the pair `{h₁, h₀}` the
trap is about. A sharpening of the row's content, not a refutation — DY-15's clause is explicitly
calibration at `d` ("on its own data"), and the state at `d` is sealed by construction. Not
imported by the library.
-/

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Found.DpCoreTree.Catalogue
  Cleanroom.Decision.DpCalibration Finset

variable (x y : ℚ)

/-- `ν` on the pays-regardless mugging (the companion of `mugInert_nu`). -/
theorem mugPaysRegardless_nu (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    nu C (mugPaysRegardless x y) X =
      (if MugW.tPay ∈ X then (1/2 : ℚ) * (C ()).w .a else 0) +
      (if MugW.tRefuse ∈ X then (1/2 : ℚ) * (C ()).w .b else 0) +
      (if MugW.hOne ∈ X then (1/2 : ℚ) * ((C ()).w .a + (C ()).w .b) else 0) := by
  rw [nu_eq_sum, mugPaysRegardless_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, mugPaysRegardless, mugWorldPaysRegardless,
    FinDistr.fair, FinDistr.coin]
  split_ifs <;> ring

/-- Inside `O_T`, `mug1` and the pays-regardless mugging have the same `ν`. -/
theorem mugPaysRegardless_nu_obs_eq (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    nu C (mug1 x y) (X ∩ mugObs ()) = nu C (mugPaysRegardless x y) (X ∩ mugObs ()) := by
  rw [mug1_nu, mugPaysRegardless_nu]
  simp [mugObs]

/-- Inside `O_T`, `mug1` and the pays-regardless mugging have the same `paySum`. -/
theorem mugPaysRegardless_paySum_obs_eq (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    paySum C (mug1 x y) (X ∩ mugObs ()) = paySum C (mugPaysRegardless x y) (X ∩ mugObs ()) := by
  simp only [paySum_eq_sum_ite]
  rw [mug1_sum, mugPaysRegardless_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, mug1, mugWorld1, mugPaysRegardless,
    mugWorldPaysRegardless, mugPay, mugObs, FinDistr.fair, FinDistr.coin]

/-- `ν(O_T) = ½` on the pays-regardless mugging for every procedure. -/
theorem mugPaysRegardless_nu_obs (C : Proc Unit (fun _ => Act2) ℚ) :
    nu C (mugPaysRegardless x y) (mugObs ()) = 1 / 2 := by
  rw [mugPaysRegardless_nu]
  have := (C ()).sum_one
  rw [Act2.sum_univ] at this
  simp [mugObs]; linarith

/-- **The probe.** For every self-model `q₀`: the refuser's Proposition-6 state on `h₁` *is* the
`O_T`-conditional state of the pays-regardless mugging (clause 2's shape, with `h₀` replaced by a
hypothesis the refuser's data distinguish), while under `δ_refuse` the two muggings' laws differ
on `hOne` (`0` vs `½`). Clause 2 as rendered therefore holds for pairs with likelihood ratio `≠ 1`
too; its content is tails-leaf agreement. -/
theorem clause2_blind_to_heads (q₀ : ℚ) (h0 : 0 ≤ q₀) (h1 : q₀ ≤ 1) :
    mugState1 x y q₀ h0 h1 =
      calibratedState (procQ q₀ h0 h1) (mugPaysRegardless x y) (mugObs ())
        (by rw [mugPaysRegardless_nu_obs]; norm_num) ∧
    nu (procQ 0 le_rfl zero_le_one) (mug1 x y) {MugW.hOne}
      ≠ nu (procQ 0 le_rfl zero_le_one) (mugPaysRegardless x y) {MugW.hOne} := by
  refine ⟨calibratedState_congr _ _ _ _ _ _ (mugPaysRegardless_nu_obs_eq x y _)
      (mugPaysRegardless_paySum_obs_eq x y _), ?_⟩
  obtain ⟨h1', h2'⟩ := refuser_informative_paysRegardless x y
  rw [h1', h2']; norm_num

/-- The strict (Definition-8, actual-procedure) reading of Appendix B item 4 — `ν̄` built from
`ν_{B,C}` with `C := δ_refuse` itself rather than a self-model — is the instance `q₀ = 0` of
`refuser_mixture_calibrated`, which the theorem's hypotheses (`0 ≤ q₀ ≤ 1`) admit although its
docstring speaks of the Proposition-6 (masked) state. -/
example (lam : ℚ) (l0 : 0 ≤ lam) (l1 : lam ≤ 1) :
    mugMixState x y lam l0 l1 0 le_rfl zero_le_one = mugState1 x y 0 le_rfl zero_le_one ∧
    mugState1 x y 0 le_rfl zero_le_one = mugInertState x y 0 le_rfl zero_le_one :=
  refuser_mixture_calibrated x y 0 le_rfl zero_le_one lam l0 l1

end Cleanroom.Decision.DpLearnerNr
