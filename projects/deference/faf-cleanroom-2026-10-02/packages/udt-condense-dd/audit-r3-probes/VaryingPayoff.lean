import Cleanroom.Udt.UdtCondenseDd.Witness

/-!
# Audit r3 (adversarial) probe: the T4(b) witness's payoff makes the law-shift term invisible

`Witness.Varying` uses the correct-prediction indicator `u o a b = [a = b]` (`R = 1`). For that
payoff the prediction-dependent utility is `1 − (own error mass)`, so the gap between two
mechanisms is bounded by `δ` from the accuracy hypothesis alone — `hL` (Lipschitz law) and `hsupp`
(support) are not needed to beat the theorem's bound `1/2` on this instance (the gap is `7/32 = δ`).

1. `indicator_utility`: for the indicator payoff, `varyingUtility = 1 − mass (own law) (errSet)`.
2. `gap_le_delta_from_accuracy`: on `Varying`, `|U 0 − U 1| ≤ 7/32` from `accurate` alone.
3. A replacement payoff `u'` (zero at observation `0`, the correct-prediction indicator elsewhere):
   `U 0 = 3/4`, `U 1 = 1/2`, gap `1/4 > 7/32 = δ`, so the gap exceeds any own-accuracy bound and the
   law-shift term (`1/32` of mass moved from observation `3` to observation `0`) is load-bearing;
   `approxDD_varying` still applies with bound `1/2 < 1 = R`.

Not imported by the library.
-/

namespace Cleanroom.Udt.UdtCondenseDd.AuditR3

open Cleanroom.Udt.UdtPolicyCalc Finset

/-- For the correct-prediction indicator payoff, the prediction-dependent utility is one minus the
mechanism's own error mass. -/
theorem indicator_utility {M O A : Type} [Fintype O] [DecidableEq O] [DecidableEq A]
    (Dof : (O → A) → FinDist O) (p pol : M → O → A) (m : M) :
    varyingUtility Dof (fun _ a b => if a = b then (1 : ℝ) else 0) p pol m =
      1 - mass (Dof (p m)).w (errSet p pol m) := by
  unfold varyingUtility errSet mass
  rw [Finset.sum_filter]
  have h1 : (1 : ℝ) = ∑ o, (Dof (p m)).w o := (Dof (p m)).sum_one.symm
  conv_rhs => rw [h1]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  by_cases h : p m o = pol m o <;> simp [h]

/-- On `Varying`, the gap is bounded by `δ = 7/32` from the accuracy hypothesis alone (no Lipschitz
or support hypothesis): the witness's payoff does not exercise the law-shift term. -/
theorem gap_le_delta_from_accuracy :
    |varyingUtility Varying.Dof Varying.u Varying.p Varying.pol 0 -
        varyingUtility Varying.Dof Varying.u Varying.p Varying.pol 1| ≤ 7 / 32 := by
  have h0 := indicator_utility Varying.Dof Varying.p Varying.pol 0
  have h1 := indicator_utility Varying.Dof Varying.p Varying.pol 1
  have hu : Varying.u = fun _ a b => if a = b then (1 : ℝ) else 0 := rfl
  rw [hu, h0, h1]
  have a0 := Varying.accurate 0
  have a1 := Varying.accurate 1
  have n0 := mass_nonneg (fun o => (Varying.Dof (Varying.p 0)).nonneg o) (errSet Varying.p Varying.pol 0)
  have n1 := mass_nonneg (fun o => (Varying.Dof (Varying.p 1)).nonneg o) (errSet Varying.p Varying.pol 1)
  rw [abs_le]
  constructor <;> linarith

/-! ### A payoff on which the law-shift term is load-bearing -/

/-- Zero payoff at observation `0`; the correct-prediction indicator elsewhere. -/
noncomputable def u' : Fin 4 → Fin 2 → Fin 2 → ℝ :=
  fun o a b => if o = 0 then 0 else if a = b then 1 else 0

theorem u'_mem : ∀ o a b, u' o a b ∈ Set.Icc (0 : ℝ) (0 + 1) := by
  intro o a b
  unfold u'
  split_ifs <;> norm_num

/-- `U 0 = 3/4`, `U 1 = 1/2`. -/
theorem utilities' :
    varyingUtility Varying.Dof u' Varying.p Varying.pol 0 = 3 / 4 ∧
      varyingUtility Varying.Dof u' Varying.p Varying.pol 1 = 1 / 2 := by
  constructor
  · rw [varyingUtility, Fin.sum_univ_four, Varying.Dof_p.1]
    simp only [unif4_w]
    simp [u', Varying.p, Varying.pol]
    norm_num
  · rw [varyingUtility, Fin.sum_univ_four, Varying.Dof_p.2, Varying.skew_w0, Varying.skew_w1,
      Varying.skew_w2, Varying.skew_w3]
    simp [u', Varying.p, Varying.pol]
    norm_num

/-- The gap `1/4` exceeds `δ = 7/32`: no own-accuracy argument bounds it; the moved mass matters. -/
theorem gap_exceeds_delta :
    (7 / 32 : ℝ) < |varyingUtility Varying.Dof u' Varying.p Varying.pol 0 -
        varyingUtility Varying.Dof u' Varying.p Varying.pol 1| := by
  rw [utilities'.1, utilities'.2]
  norm_num

/-- `approxDD_varying` on the same data with the payoff `u'`: bound `1/2 < 1 = R` for the gap `1/4`. -/
theorem bound_instance' :
    |varyingUtility Varying.Dof u' Varying.p Varying.pol 0 -
        varyingUtility Varying.Dof u' Varying.p Varying.pol 1| ≤
      1 * (2 * (7 / 32) + (1 / 32) * (2 * (7 / 32) / (7 / 32))) :=
  approxDD_varying Varying.Dof u' (by norm_num) (by norm_num) (by norm_num) u'_mem
    Varying.lipschitz Varying.support Varying.accurate rfl

end Cleanroom.Udt.UdtCondenseDd.AuditR3

#print axioms Cleanroom.Udt.UdtCondenseDd.AuditR3.gap_le_delta_from_accuracy
#print axioms Cleanroom.Udt.UdtCondenseDd.AuditR3.gap_exceeds_delta
#print axioms Cleanroom.Udt.UdtCondenseDd.AuditR3.bound_instance'
