import Cleanroom.Decision.DpCalibLimits.WitnessesR2

/-!
# Audit r3 (adversarial) probe — `cqPay_condExp_deviate_nontrivial` instantiates
`condExp_deviate_eq` at the procedure's own label, where the deviation is the identity

`cqPay_condExp_deviate_nontrivial` (`WitnessesR2.lean`, graded `Kind: N+`, the repair-round-2 fix
of r2 adversarial B1) instantiates the corollary `condExp_deviate_eq` ("masked act values are
self-model-free": `condExp (C[d ↦ m]) (a ∧ O_d) = condExp C (a ∧ O_d)`) at `C = procQ ½` and
`m = FinDistr.uniform`. But `uniform` on `Act2` *is* `act2 ½`, i.e. `m = C(d)`, so
`C[d ↦ m] = C` (`Function.update_eq_self`, which the library's own `cancellation` proof uses as
`hself`), and the instance is `condExp C E = condExp C E` — reflexive, for a reason that has
nothing to do with the cancellation mechanism. Part 1 proves `C[d ↦ Unif] = C`; Part 2 proves the
shipped first conjunct by rewriting the deviation away (no cancellation lemma, no hypothesis
package); Part 3 does the same for the already-regraded `coinQuery_condExp_deviate`, which has the
same `(½, Unif)` pairing; Part 4 supplies a genuine instance on the same tree (`C = procQ ⅓`,
`m = (¼, ¾)`: the deviation moves the label), with both sides computed independently to `½`, and
the theorem applied to the full package.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-! ## Part 1: the self-model of the shipped witness is the procedure's own label -/

theorem procQ_half_deviate_uniform :
    (procQ (1/2) (by norm_num) (by norm_num)).deviate () FinDistr.uniform =
      procQ (1/2) (by norm_num) (by norm_num) := by
  funext d
  cases d
  rw [Proc.deviate_same]
  ext x
  cases x <;> simp [procQ, FinDistr.act2, FinDistr.uniform_w, act2_card_rat] <;> norm_num

/-! ## Part 2: the shipped statement is reflexive -/

/-- The first conjunct of `cqPay_condExp_deviate_nontrivial`, proved without
`condExp_deviate_eq` and without any of its hypotheses. -/
theorem cqPay_condExp_deviate_is_refl :
    condExp ((procQ (1/2) (by norm_num) (by norm_num)).deviate () FinDistr.uniform) cqPay
        (cqActEv () .a ∩ cqObs ()) =
      condExp (procQ (1/2) (by norm_num) (by norm_num)) cqPay (cqActEv () .a ∩ cqObs ()) := by
  rw [procQ_half_deviate_uniform]

/-! ## Part 3: the regraded N− `coinQuery_condExp_deviate` is reflexive for the same reason -/

theorem coinQuery_condExp_deviate_is_refl :
    condExp ((procQ (1/2) (by norm_num) (by norm_num)).deviate () FinDistr.uniform) coinQuery
        (cqActEv () .a ∩ cqObs ()) =
      condExp (procQ (1/2) (by norm_num) (by norm_num)) coinQuery (cqActEv () .a ∩ cqObs ()) := by
  rw [procQ_half_deviate_uniform]

/-! ## Part 4: a genuine instance — `C = procQ ⅓`, `m = (¼, ¾)` -/

/-- The deviation moves the label: `procQ ⅓ [d ↦ (¼, ¾)] ≠ procQ ⅓`. -/
theorem procQ_third_deviate_quarter_ne :
    (procQ (1/3) (by norm_num) (by norm_num)).deviate () quarter ≠
      procQ (1/3) (by norm_num) (by norm_num) := by
  intro h
  have := congrArg (fun C : Proc Unit (fun _ => Act2) ℚ => (C ()).w .a) h
  simp [Proc.deviate_same, quarter, FinDistr.act2, procQ] at this

/-- The masked value of `a` under `procQ ⅓ [d ↦ (¼, ¾)]` on `cqPay`, computed directly: `½`. -/
theorem cqPay_third_quarter_masked :
    condExp ((procQ (1/3) (by norm_num) (by norm_num)).deviate () quarter) cqPay
      (cqActEv () .a ∩ cqObs ()) = 1 / 2 := by
  unfold condExp
  rw [paySum_eq_sum_ite, nu_eq_sum, cqPay_sum, cqPay_sum]
  simp [cqPay, leafLaw, cqActEv, cqObs, Proc.deviate_same, quarter, FinDistr.act2,
    Fin.sum_univ_two, FinDistr.fair, FinDistr.coin]
  try norm_num

/-- The strict value of `a` under `procQ ⅓` on `cqPay`, computed directly: `½`. -/
theorem cqPay_third_strict :
    condExp (procQ (1/3) (by norm_num) (by norm_num)) cqPay (cqActEv () .a ∩ cqObs ()) = 1 / 2 := by
  unfold condExp
  rw [paySum_eq_sum_ite, nu_eq_sum, cqPay_sum, cqPay_sum]
  simp [cqPay, leafLaw, cqActEv, cqObs, procQ, FinDistr.act2, Fin.sum_univ_two,
    FinDistr.fair, FinDistr.coin]
  try norm_num

/-- `condExp_deviate_eq`'s package inhabited where the deviation is *not* the identity: the
masked value under `procQ ⅓ [d ↦ (¼, ¾)]` equals the strict value under `procQ ⅓` (through the
theorem), both are `½` (computed independently), and the two procedures differ. This is the
instance the N+ should be. -/
theorem cqPay_condExp_deviate_genuine :
    (procQ (1/3) (by norm_num) (by norm_num)).deviate () quarter ≠
      procQ (1/3) (by norm_num) (by norm_num) ∧
    condExp ((procQ (1/3) (by norm_num) (by norm_num)).deviate () quarter) cqPay
        (cqActEv () .a ∩ cqObs ()) =
      condExp (procQ (1/3) (by norm_num) (by norm_num)) cqPay (cqActEv () .a ∩ cqObs ()) ∧
    condExp (procQ (1/3) (by norm_num) (by norm_num)) cqPay (cqActEv () .a ∩ cqObs ()) = 1 / 2 := by
  refine ⟨procQ_third_deviate_quarter_ne, ?_, cqPay_third_strict⟩
  apply condExp_deviate_eq cqObs cqActEv _ cqPay () quarter .a
    (fun ℓ => (cqPay_count ℓ).le) (cqPay_covers _) cqPay_hav cqActEv_disjoint
  · rw [nu_eq_sum, cqPay_sum]
    simp [cqPay, leafLaw, cqActEv, cqObs, Proc.deviate_same, quarter, FinDistr.act2,
      Fin.sum_univ_two, FinDistr.fair, FinDistr.coin]
    try norm_num
  · rw [nu_eq_sum, cqPay_sum]
    simp [cqPay, leafLaw, cqActEv, cqObs, procQ, FinDistr.act2, Fin.sum_univ_two, FinDistr.fair,
      FinDistr.coin]
    try norm_num

end Cleanroom.Decision.DpCalibLimits
