/-
  aumann-modesty-attack.lean — HYPOTHESIS-INERTNESS / CONCLUSION-TRIVIALITY attacks.

  Method: take the ORIGINAL proof bodies VERBATIM, delete/weaken one hypothesis, and re-run.
  If the original script still closes the goal with NO sorry, that hypothesis was INERT ⇒ SHADOW.
  If it errors (unknown identifier / unsolved goal), the hypothesis was load-bearing ⇒ REAL.

  ATTACK 1 (partition_averaging_NO_HDISJ): delete `hdisj` (disjointness). The file claims
  disjointness is THE essential hypothesis. Expect: ERROR (uses hdisj twice).

  ATTACK 2 (partition_averaging_NO_HCOVER): delete `hcover`. Expect: ERROR.

  ATTACK 3 (partition_averaging_NO_HQ): drop hq₁/hq₂. Expect: ERROR (cannot conclude post C = q).

  ATTACK 4 (CONCLUSION-TRIVIALITY): try to prove `post C = q` for ARBITRARY q with no
  posterior hypotheses. Expect: UNPROVABLE (it is false; q is free).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

open Finset

namespace AumannAttack

def π : Fin 4 → ℚ := fun _ => 1/4

def X : Fin 4 → ℚ
  | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0

def C : Fin 4 → Bool := fun _ => true

def post (S : Fin 4 → Bool) : ℚ :=
  (∑ v, (if S v then π v * X v else 0)) / (∑ v, (if S v then π v else 0))

/-- ATTACK 1: original `partition_averaging` proof body VERBATIM, `hdisj` hypothesis DELETED.
    The body uses `hdisj v ⟨h1, ...⟩` twice; with hdisj gone this must error. -/
theorem partition_averaging_NO_HDISJ
    (S₁ S₂ : Fin 4 → Bool) (q : ℚ)
    (hcover : ∀ w, C w = true ↔ (S₁ w = true ∨ S₂ w = true))
    -- (hdisj  : ∀ w, ¬ (S₁ w = true ∧ S₂ w = true))   -- DELETED
    (hm₁ : 0 < ∑ v, (if S₁ v then π v else 0))
    (hm₂ : 0 < ∑ v, (if S₂ v then π v else 0))
    (hq₁ : post S₁ = q) (hq₂ : post S₂ = q) :
    post C = q := by
  have hnum : (∑ v, (if C v then π v * X v else 0))
            = (∑ v, (if S₁ v then π v * X v else 0)) + (∑ v, (if S₂ v then π v * X v else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hc := hcover v
    by_cases h1 : S₁ v = true
    · have h2 : S₂ v = false := by
        by_contra h2'; exact hdisj v ⟨h1, by simpa using h2'⟩
      simp [h1, h2, (hc.mpr (Or.inl h1))]
    · by_cases h2 : S₂ v = true
      · simp [h1, h2, (hc.mpr (Or.inr h2))]
      · have hC : C v = false := by
          by_contra hC'
          rcases (hc.mp (by simpa using hC')) with h | h
          · exact h1 h
          · exact h2 h
        simp [hC, h1, h2]
  have hden : (∑ v, (if C v then π v else 0))
            = (∑ v, (if S₁ v then π v else 0)) + (∑ v, (if S₂ v then π v else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hc := hcover v
    by_cases h1 : S₁ v = true
    · have h2 : S₂ v = false := by
        by_contra h2'; exact hdisj v ⟨h1, by simpa using h2'⟩
      simp [h1, h2, (hc.mpr (Or.inl h1))]
    · by_cases h2 : S₂ v = true
      · simp [h1, h2, (hc.mpr (Or.inr h2))]
      · have hC : C v = false := by
          by_contra hC'
          rcases (hc.mp (by simpa using hC')) with h | h
          · exact h1 h
          · exact h2 h
        simp [hC, h1, h2]
  have e1 : (∑ v, (if S₁ v then π v * X v else 0)) = q * (∑ v, (if S₁ v then π v else 0)) := by
    have h := hq₁; unfold post at h
    rw [div_eq_iff (ne_of_gt hm₁)] at h
    rw [h, mul_comm]
  have e2 : (∑ v, (if S₂ v then π v * X v else 0)) = q * (∑ v, (if S₂ v then π v else 0)) := by
    have h := hq₂; unfold post at h
    rw [div_eq_iff (ne_of_gt hm₂)] at h
    rw [h, mul_comm]
  unfold post
  rw [hnum, hden, e1, e2]
  have hden_pos : 0 < (∑ v, (if S₁ v then π v else 0)) + (∑ v, (if S₂ v then π v else 0)) := by
    linarith
  rw [← mul_add]
  exact mul_div_cancel_right₀ q (ne_of_gt hden_pos)

/-- ATTACK 4 (CONCLUSION-TRIVIALITY): can we prove `post C = q` for ARBITRARY q with NO
    posterior / cover hypotheses? If `sorry`-free-provable, the conclusion is trivial. It is
    NOT (q is a free variable, post C is a fixed rational 1/2). We attempt and expect failure,
    so we leave a deliberate `sorry` marker the axiom audit will catch — but FIRST we try a real
    proof attempt that should not close. We instead PROVE the negation to show non-triviality. -/
theorem conclusion_not_trivial : ∃ q : ℚ, post C ≠ q := by
  refine ⟨0, ?_⟩
  simp only [post, π, X, C, Fin.sum_univ_four]; norm_num

end AumannAttack
