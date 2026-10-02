import Cleanroom.Lit.LitWeathersonFrames.Pooling
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
Audit round 1, adversarial lens — probe: `gallow_finite` is not a squeeze over
`Defers C Y A ∧ Pools C Y A B λ` alone (with `λ = ½ ∉ {0, 1}`): the second deference hypothesis
carries weight.

Two worlds, `C = (½, ½)`, `Y = 𝟙_{0}`, `A ≡ ½` (deferred to), `B = (3/2, −½)` (real-valued, as
the package's `stronger` fidelity allows). The cells are singletons and on each the posterior is
exactly `½ A + ½ B` (`1 = ¼ + ¾`, `0 = ¼ − ¼`), so `Pools` holds; but `C(Y | B = 3/2) = 1 ≠ 3/2`,
and `A ≠ B` everywhere. Not imported by the library.
-/

namespace Cleanroom.Lit.LitWeathersonFrames.AuditR1Adv.G2

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Lit.LitWeathersonFrames

noncomputable section

def C : Fin 2 → ℝ := ![1/2, 1/2]
def Y : Fin 2 → ℝ := ![1, 0]
def A : Fin 2 → ℝ := ![1/2, 1/2]
def B : Fin 2 → ℝ := ![3/2, -1/2]

theorem C_nonneg : ∀ w, 0 ≤ C w := by
  intro w; fin_cases w <;> norm_num [C]

theorem defersA : Defers C Y A := by
  intro a
  by_cases ha : a = 1/2
  · subst ha; norm_num [lev, sum_filter, Fin.sum_univ_succ, A, C, Y]
  · rw [lev, sum_filter]
    apply sum_eq_zero
    intro w _
    have hne : ¬ A w = a := fun h => ha (by rw [← h]; fin_cases w <;> norm_num [A])
    simp [hne]

theorem pools : Pools C Y A B (1/2) := by
  intro a b
  by_cases h0 : a = 1/2 ∧ b = 3/2
  · obtain ⟨rfl, rfl⟩ := h0
    norm_num [lev₂, sum_filter, Fin.sum_univ_succ, A, B, C, Y]
  by_cases h1 : a = 1/2 ∧ b = -1/2
  · obtain ⟨rfl, rfl⟩ := h1
    norm_num [lev₂, sum_filter, Fin.sum_univ_succ, A, B, C, Y]
  rw [lev₂, sum_filter]
  apply sum_eq_zero
  intro w _
  have hne : ¬ (A w = a ∧ B w = b) := by
    intro h
    fin_cases w
    · exact h0 ⟨by rw [← h.1]; norm_num [A], by rw [← h.2]; norm_num [B]⟩
    · exact h1 ⟨by rw [← h.1]; norm_num [A], by rw [← h.2]; norm_num [B]⟩
  simp [hne]

theorem not_defersB : ¬ Defers C Y B := by
  intro h
  have := h (3/2)
  norm_num [lev, sum_filter, Fin.sum_univ_succ, B, C, Y] at this

theorem not_agreeAE : ¬ AgreeAE C A B := by
  intro h
  have := h 0 (by norm_num [C])
  norm_num [A, B] at this

/-- Deference to `A` and fixed linear pooling with `λ = ½`, without deference to `B`, do not
force agreement: the second deference hypothesis of `gallow_finite` is load-bearing. -/
theorem summary :
    (∀ w, 0 ≤ C w) ∧ Defers C Y A ∧ Pools C Y A B (1/2) ∧ (1/2 : ℝ) ≠ 0 ∧ (1/2 : ℝ) ≠ 1 ∧
      ¬ Defers C Y B ∧ ¬ AgreeAE C A B :=
  ⟨C_nonneg, defersA, pools, by norm_num, by norm_num, not_defersB, not_agreeAE⟩

end

end Cleanroom.Lit.LitWeathersonFrames.AuditR1Adv.G2
