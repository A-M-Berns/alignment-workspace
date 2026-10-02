import Cleanroom.Corrigibility.CorrIndifference.Witnesses

/-!
# Audit r3 (adversarial) probe — §2.1's `v_N` is a cell value; under it the weak global reading
of "(10) averts any incentives to steer" is unconditional on `O = {Pr, ¬Pr}`

Soares et al. §2.1 (`soares-2015-corrigibility.md` l. 165) define
`v_N(a₁) := U_N(a₁, ¬Pr, A₂(a₁, ¬Pr))` — a cell value, defined for every first action, no
conditional expectation; `E[U_N | O ∉ Press ; a₁]` is §3's *redefinition* (l. 207). Eq. (10) and
the sentence F2 refutes are §2.1's. With §2.1's `v_N` (`cellN` below; `twoObs_vN` shows it is the
package's quotient `vN` where `q a < 1`), (10) is `max_a cellN a`, always attained, and the
attaining action is a global optimum of the mixture at `c_high = M` with **no** hypothesis on the
press probabilities — certain-press actions included (`cellMax_is_global_optimum`). So F2's
clause "in the source's own terms `v_N(a₁)` is `0/0`" is false for §2.1, and the strict failure
`Witnesses.strict_cause_steering_twoObs` is a failure only under §3's reachability-aware reading
(or the package's quotient `vN`): on `MCeil`, §2.1's `v_N(sure) = 12` attains (10) and `sure` *is*
§2.1's `v_N`-maximiser (`MCeil_cellN`). Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrIndifference.AuditR3

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep SoaresModel

variable {A₁ A₂ : Type*} [Fintype A₂] [Nonempty A₂]

/-- §2.1's `v_N`: the best value of the silent cell, defined for every first action. -/
noncomputable def cellN (UN : A₁ → Obs → A₂ → ℝ) (a : A₁) : ℝ := best UN a .silent

/-- **Under §2.1's own `v_N`, the weak global reading needs no qualifier:** on `O = {Pr, ¬Pr}`,
for any press probabilities, some action's `cellN` attains (10) and that action is a global
optimum of the mixture at `c_high = M`. -/
theorem cellMax_is_global_optimum [Fintype A₁] [Nonempty A₁] [DecidableEq A₂]
    (q : A₁ → ℝ) (hq : ∀ a, q a ∈ Set.Icc (0 : ℝ) 1)
    (UN : A₁ → Obs → A₂ → ℝ) {Sh : Finset A₂} (hSh : Sh.Nonempty) {clow : ℝ}
    (hP : (twoObs (A₂ := A₂) q hq).Pressᶜ.Nonempty)
    (hc : clow < (twoObs (A₂ := A₂) q hq).silentMax UN hP) :
    ∃ a₀, cellN UN a₀ = (twoObs (A₂ := A₂) q hq).silentMax UN hP ∧
      ∀ a, (twoObs (A₂ := A₂) q hq).EU
          ((twoObs (A₂ := A₂) q hq).mixU UN Sh ((twoObs (A₂ := A₂) q hq).silentMax UN hP) clow) a ≤
        (twoObs (A₂ := A₂) q hq).EU
          ((twoObs (A₂ := A₂) q hq).mixU UN Sh ((twoObs (A₂ := A₂) q hq).silentMax UN hP) clow) a₀ := by
  obtain ⟨a₀, o, ho, hmax⟩ := (twoObs (A₂ := A₂) q hq).exists_eq_silentMax UN hP
  have hnp : o ∉ ({Obs.press} : Finset Obs) := by
    rw [← twoObs_Press (A₂ := A₂) q hq]; exact mem_compl.mp ho
  have hos : o = Obs.silent := by cases o <;> simp_all
  subst hos
  refine ⟨a₀, by unfold cellN; exact hmax.symm, fun a => ?_⟩
  have hbound := (twoObs (A₂ := A₂) q hq).EU_mixU_le_of_bound UN hSh hc
    (fun a o ho => (twoObs (A₂ := A₂) q hq).best_le_silentMax UN hP a ho) a
  have hEU₀ : (twoObs (A₂ := A₂) q hq).EU
      ((twoObs (A₂ := A₂) q hq).mixU UN Sh ((twoObs (A₂ := A₂) q hq).silentMax UN hP) clow) a₀ =
      (twoObs (A₂ := A₂) q hq).silentMax UN hP := by
    by_cases h1 : q a₀ < 1
    · exact (twoObs (A₂ := A₂) q hq).EU_mixU_eq_of_vN_eq UN hSh hc
        (by rw [twoObs_vN q hq UN a₀ h1, hmax])
    · have hone : (twoObs (A₂ := A₂) q hq).pressMass a₀ = 1 := by
        rw [twoObs_pressMass]; exact le_antisymm (hq a₀).2 (not_lt.mp h1)
      exact (twoObs (A₂ := A₂) q hq).EU_mixU_eq_of_press_one UN hSh hc hone
  rw [hEU₀]; exact hbound

/-- On the round-2 witness `MCeil`, §2.1's `v_N` is `12` at the certain-press action and `10` at
the honest one: `sure` is §2.1's `v_N`-maximiser, so under §2.1's own definition the preferred
action is the `v_N`-best one and no "steering" is visible; the strict incentive
`strict_cause_steering_twoObs` exhibits is measured against `E[U_N ; ·]` (`10 > 0`), i.e. under
the reachability-aware (§3 / quotient) reading. -/
theorem MCeil_cellN :
    cellN Witnesses.UNceil .sure = 12 ∧ cellN Witnesses.UNceil .star = 10 := by
  constructor <;> (unfold cellN; rw [Witnesses.best_UNceil]; rfl)

end Cleanroom.Corrigibility.CorrIndifference.AuditR3
