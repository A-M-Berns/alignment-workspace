import Cleanroom.Lit.LitWeathersonFrames.Pooling
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
Audit round 1, adversarial lens — probe: `zhang_finite_upper` is not a squeeze over
`Defers C Y A ∧ BetweenUpper C Y A B` alone (the second deference hypothesis carries weight).

Three worlds, `C = (⅓, ⅓, ⅓)`, `Y = 𝟙_{0}`, `A ≡ ⅓` (deferred to: the average of `Y` is ⅓),
`B = (⅗, ⅗, 0)`. The cells are `(⅓, ⅗) = {0, 1}` with posterior `½ < ⅗` and `(⅓, 0) = {2}` with
posterior `0 < ⅓`, so `BetweenUpper` holds; but `C` does not defer to `B` (`C(Y | B = ⅗) = ½`),
and `A ≠ B` on the support. Together with `R8` (which has both deferences and fails exactly
the upper half, `R8NotBetweenUpper.lean`), every hypothesis of `zhang_finite_upper` is
load-bearing. Not imported by the library.
-/

namespace Cleanroom.Lit.LitWeathersonFrames.AuditR1Adv.Z3

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Lit.LitWeathersonFrames

noncomputable section

def C : Fin 3 → ℝ := ![1/3, 1/3, 1/3]
def Y : Fin 3 → ℝ := ![1, 0, 0]
def A : Fin 3 → ℝ := ![1/3, 1/3, 1/3]
def B : Fin 3 → ℝ := ![3/5, 3/5, 0]

theorem C_nonneg : ∀ w, 0 ≤ C w := by
  intro w; fin_cases w <;> norm_num [C]

theorem defersA : Defers C Y A := by
  intro a
  by_cases ha : a = 1/3
  · subst ha; norm_num [lev, sum_filter, Fin.sum_univ_succ, A, C, Y]
  · rw [lev, sum_filter]
    apply sum_eq_zero
    intro w _
    have hne : ¬ A w = a := fun h => ha (by rw [← h]; fin_cases w <;> norm_num [A])
    simp [hne]

theorem betweenUpper : BetweenUpper C Y A B := by
  intro a b
  by_cases h1 : a = 1/3 ∧ b = 3/5
  · obtain ⟨rfl, rfl⟩ := h1
    refine ⟨1/2, ?_, by norm_num [max_def], by norm_num [max_def]⟩
    norm_num [lev₂, sum_filter, Fin.sum_univ_succ, A, B, C, Y]
  by_cases h2 : a = 1/3 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h2
    refine ⟨0, ?_, by norm_num [max_def], by norm_num [max_def]⟩
    norm_num [lev₂, sum_filter, Fin.sum_univ_succ, A, B, C, Y]
  refine ⟨min a b, ?_, min_le_max, fun hab => min_lt_max.mpr hab⟩
  rw [lev₂, sum_filter]
  apply sum_eq_zero
  intro w _
  have hne : ¬ (A w = a ∧ B w = b) := by
    intro h
    fin_cases w
    · exact h1 ⟨by rw [← h.1]; norm_num [A], by rw [← h.2]; norm_num [B]⟩
    · exact h1 ⟨by rw [← h.1]; norm_num [A], by rw [← h.2]; norm_num [B]⟩
    · exact h2 ⟨by rw [← h.1]; norm_num [A], by rw [← h.2]; norm_num [B]⟩
  simp [hne]

theorem not_defersB : ¬ Defers C Y B := by
  intro h
  have := h (3/5)
  norm_num [lev, sum_filter, Fin.sum_univ_succ, B, C, Y] at this

theorem not_agreeAE : ¬ AgreeAE C A B := by
  intro h
  have := h 0 (by norm_num [C])
  norm_num [A, B] at this

/-- Deference to `A` and the upper betweenness constraint, without deference to `B`, do not force
agreement: the second deference hypothesis of `zhang_finite_upper` is load-bearing. -/
theorem summary :
    (∀ w, 0 ≤ C w) ∧ Defers C Y A ∧ BetweenUpper C Y A B ∧ ¬ Defers C Y B ∧ ¬ AgreeAE C A B :=
  ⟨C_nonneg, defersA, betweenUpper, not_defersB, not_agreeAE⟩

end

end Cleanroom.Lit.LitWeathersonFrames.AuditR1Adv.Z3
