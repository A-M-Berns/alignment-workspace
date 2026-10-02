import Cleanroom.Corrigibility.CorrOsgChai.Milli
import Mathlib.Algebra.BigOperators.Fin

/-!
# Audit r2 (adversarial) probe — `Rational` is load-bearing in `blindlyObedient_of_rational`

A one-parameter, two-action supervision model whose human always orders the worse action
(`R = ![0, 1]`, `πH = δ_0`). The robot `πR ≡ 1` is posterior-mean (`IsPosteriorMean`) and
tie-break-obedient (`TieBreakObedient`: the only order whose objective the order itself
maximises is the null order `1`, where `πR 1 = 1`), yet it disobeys order `0` and has
obedience `0`. So the conclusion of `blindlyObedient_of_rational` fails without `Rational`:
the tie-break hypothesis does not carry the conclusion on its own, and Theorem 3 (⇐) has
content. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrOsgChai.AuditR2

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrOsgChai
  Cleanroom.Corrigibility.CorrOsgChai.Supervision
open Finset hiding expect

/-- The human who always orders the worse action. -/
noncomputable def badHuman : Supervision (Fin 1) (Fin 2) where
  prior := Distr.uniform
  R := fun _ => ![0, 1]
  πH := fun _ => Distr.delta 0

/-- The posterior objective, closed form. -/
lemma badHuman_Q (o a : Fin 2) :
    badHuman.Q o a = if o = 0 then (![0, 1] : Fin 2 → ℝ) a else 0 := by
  simp only [Q, post, badHuman, Distr.uniform, Distr.delta_mass, Fintype.card_fin,
    Fin.sum_univ_one]
  split_ifs <;> simp

/-- The human is not rational: order `0` has positive probability but `R 0 1 > R 0 0`. -/
theorem badHuman_not_rational : ¬ badHuman.Rational := by
  intro h
  have := h 0 0 (by simp [badHuman, Distr.delta_mass]) 1
  norm_num [badHuman] at this

/-- The robot `πR ≡ 1` is posterior-mean. -/
theorem badHuman_posteriorMean : badHuman.IsPosteriorMean (fun _ => 1) := by
  intro o a
  rw [badHuman_Q, badHuman_Q]
  fin_cases o <;> fin_cases a <;> simp

/-- The robot `πR ≡ 1` is tie-break-obedient (Theorem 2's clause). -/
theorem badHuman_tieBreak : badHuman.TieBreakObedient (fun _ => 1) := by
  intro o ho
  fin_cases o
  · exfalso
    have := ho 1
    rw [badHuman_Q, badHuman_Q] at this
    norm_num at this
  · rfl

/-- Yet it is not blindly obedient: it disobeys order `0`, and its obedience is `0`. -/
theorem badHuman_disobeys :
    (fun _ : Fin 2 => (1 : Fin 2)) 0 ≠ 0 ∧ badHuman.obedience (fun _ => 1) = 0 := by
  refine ⟨by decide, ?_⟩
  simp only [obedience, post, badHuman, Distr.uniform, Distr.delta_mass, Fintype.card_fin,
    Fin.sum_univ_one, Fin.sum_univ_two]
  simp

/-- And its autonomy advantage is `1 > 0`: Theorem 1's strict side and Remark 1's contrapositive
(`Δ > 0 ⇒ O < 1`) exercised with non-degenerate numbers — the package ships no instance with
`Δ > 0` (the ledger's Witness column for `advantage_nonneg` is "—"). -/
theorem badHuman_advantage : badHuman.advantage (fun _ => 1) = 1 := by
  simp only [advantage, post, badHuman, Distr.uniform, Distr.delta_mass, Fintype.card_fin,
    Fin.sum_univ_one, Fin.sum_univ_two]
  simp

end Cleanroom.Corrigibility.CorrOsgChai.AuditR2
