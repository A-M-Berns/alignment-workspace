import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# E1: anticipation-robustness is branchwise dominance

Package `legit-neg-dynamic`, target 8 (load-bearing 4). Sources: `clusters/E/NEGATIVES.md` E1;
`clusters/E/VERIFY.md` "E1 — survives" (scope: branch credences independent of the act);
`clusters/E/fixtures/e1_anticipation.py:98-112`; pinned by [[corr-legit-neg-inventory]] item 053.

For finitely many revision branches `b : B` with the future evaluator's branch scores `VW b`
(comply) and `VP b` (violate), the complying act is weakly preferred under **every** credence over
the branches iff it is weakly preferred in **every** branch separately. The violating credences,
when there are any, contain a point mass and form a convex set. Scope (verifier): the credence
over branches does not depend on the act (E6's A3 is treated separately, by construction).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset

variable {B : Type} [Fintype B] [DecidableEq B]

/-- A credence over the branches: a non-negative vector summing to `1` (a probability vector; no
`stdSimplex`).
Source: [[corr-legit-neg-inventory]] item 053
Kind: D
Fidelity: exact -/
def IsCredence (μ : B → ℚ) : Prop := (∀ b, 0 ≤ μ b) ∧ ∑ b, μ b = 1

/-- The point mass on a branch is a credence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isCredence_pointMass (b₀ : B) : IsCredence (fun b => if b = b₀ then (1 : ℚ) else 0) :=
  ⟨fun b => by dsimp only; split_ifs <;> norm_num, by simp⟩

/-- **E1 (load-bearing 4): the complying act is chosen at every credence iff it is weakly
preferred in every branch.** `(∀ μ credence, 0 ≤ ∑ μ b (VW b − VP b)) ↔ ∀ b, VP b ≤ VW b`.
Scope: branch credences independent of the act.
Source: [[corr-legit-neg-inventory]] item 053 (E1); VERIFY E "E1 — survives"
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem robust_iff_branchwise (VW VP : B → ℚ) :
    (∀ μ : B → ℚ, IsCredence μ → 0 ≤ ∑ b, μ b * (VW b - VP b)) ↔ ∀ b, VP b ≤ VW b := by
  constructor
  · intro h b₀
    have := h _ (isCredence_pointMass b₀)
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    linarith
  · intro h μ hμ
    exact Finset.sum_nonneg fun b _ => mul_nonneg (hμ.1 b) (by linarith [h b])

/-- **The violating credences**: `{μ | ∑ μ b (VP b − VW b) > 0}`. When some branch `b₀` has
`VW b₀ < VP b₀`, this set contains the point mass on `b₀`; and it is convex (a mixture of two
violating credences violates). Not called "open" (no topology here).
Source: [[corr-legit-neg-inventory]] item 053 (E1, "an open half-space containing a point mass")
Kind: L
Fidelity: weaker: convexity and the point mass, not openness in the simplex
Hyps: (a) none -/
theorem violating_credences (VW VP : B → ℚ) (b₀ : B) (hb : VW b₀ < VP b₀) :
    (IsCredence (fun b => if b = b₀ then (1 : ℚ) else 0) ∧
      0 < ∑ b, (if b = b₀ then (1 : ℚ) else 0) * (VP b - VW b)) ∧
    ∀ μ ν : B → ℚ, IsCredence μ → IsCredence ν → 0 < ∑ b, μ b * (VP b - VW b) →
      0 < ∑ b, ν b * (VP b - VW b) → ∀ t, 0 ≤ t → t ≤ 1 →
      IsCredence (fun b => t * μ b + (1 - t) * ν b) ∧
      0 < ∑ b, (t * μ b + (1 - t) * ν b) * (VP b - VW b) := by
  refine ⟨⟨isCredence_pointMass b₀, ?_⟩, ?_⟩
  · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith
  · intro μ ν hμ hν hμv hνv t ht0 ht1
    refine ⟨⟨fun b => add_nonneg (mul_nonneg ht0 (hμ.1 b)) (mul_nonneg (by linarith) (hν.1 b)), ?_⟩, ?_⟩
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hμ.2, hν.2]; ring
    · have : ∑ b, (t * μ b + (1 - t) * ν b) * (VP b - VW b) =
          t * ∑ b, μ b * (VP b - VW b) + (1 - t) * ∑ b, ν b * (VP b - VW b) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [this]
      rcases lt_or_eq_of_le ht0 with h | h
      · have := mul_pos h hμv
        nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ 1 - t) hνv.le]
      · rw [← h]; simp; exact hνv

/-- **E1 on two branches** (the form every E result uses): with the credence `(ρ, 1 − ρ)` on
`(RELAX, KEEP)`, the complying act is preferred at every `ρ ∈ [0, 1]` iff it is weakly preferred on
both branches.
Source: [[corr-legit-neg-inventory]] item 053 (E1, two-branch check on 1,296 tables)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem robust_iff_branchwise_two (wR wK pR pK : ℚ) :
    (∀ ρ : ℚ, 0 ≤ ρ → ρ ≤ 1 → ρ * pR + (1 - ρ) * pK ≤ ρ * wR + (1 - ρ) * wK) ↔
      pR ≤ wR ∧ pK ≤ wK := by
  constructor
  · intro h
    have h1 := h 1 zero_le_one le_rfl
    have h0 := h 0 le_rfl zero_le_one
    constructor <;> linarith
  · rintro ⟨hR, hK⟩ ρ h0 h1
    nlinarith [mul_le_mul_of_nonneg_left hR h0, mul_le_mul_of_nonneg_left hK (by linarith : (0:ℚ) ≤ 1 - ρ)]

end Cleanroom.Corrigibility.LegitNegDynamic
