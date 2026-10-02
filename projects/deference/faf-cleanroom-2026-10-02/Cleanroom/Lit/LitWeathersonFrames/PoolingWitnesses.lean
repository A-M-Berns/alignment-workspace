import Cleanroom.Lit.LitWeathersonFrames.Pooling
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# Witnesses for the pooling theorems (T1 N+, T2 N+ refutation of R-open)

Package `lit-weatherson-frames`. `R8` is the eight-world model (worlds `(a, b, p)`, `h = 4/5`,
`l = 2/5`) that satisfies deference to both experts, strict betweenness on every cell where the
experts *disagree*, and `C(A = B) = 4/5 < 1`: reading R-open of Zhang's constraint 4 is false.
On the two agreement cells the novice is *more extreme* than the agreeing experts
(`17/20 > 4/5`, `7/20 < 2/5`), which is exactly why the closed reading `Between4` fails there.
`G5` inhabits Gallow's full hypothesis package non-degenerately: an uncertain expert value
(`1/2`, on a two-world level set), every `λ`, and a null world where the experts disagree (so
the conclusion is genuinely "on the support").
-/

namespace Cleanroom.Lit.LitWeathersonFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

/-! ## R8: the refutation of reading R-open -/

namespace R8

/-- The novice's weights on the eight worlds `(h,l,p) (h,l,¬p) (l,h,p) (l,h,¬p) (h,h,p) (h,h,¬p)
(l,l,p) (l,l,¬p)`.
Source: mandate T2 (R-open witness)
Kind: D
Fidelity: n/a -/
def C : Fin 8 → ℝ := ![3/50, 2/50, 3/50, 2/50, 17/50, 3/50, 7/50, 13/50]

/-- Expert `A`'s credence at each world (`h = 4/5`, `l = 2/5`).
Source: mandate T2
Kind: D
Fidelity: n/a -/
def A : Fin 8 → ℝ := ![4/5, 4/5, 2/5, 2/5, 4/5, 4/5, 2/5, 2/5]

/-- Expert `B`'s credence at each world.
Source: mandate T2
Kind: D
Fidelity: n/a -/
def B : Fin 8 → ℝ := ![2/5, 2/5, 4/5, 4/5, 4/5, 4/5, 2/5, 2/5]

/-- The indicator of `p` (true at the even worlds).
Source: mandate T2
Kind: D
Fidelity: n/a -/
def Y : Fin 8 → ℝ := ![1, 0, 1, 0, 1, 0, 1, 0]

/-- `C` is a probability vector.
Source: mandate T2
Kind: N+
Fidelity: n/a -/
theorem C_prob : (∀ w, 0 ≤ C w) ∧ ∑ w, C w = 1 := by
  refine ⟨fun w => ?_, ?_⟩
  · fin_cases w <;> norm_num [C]
  · norm_num [Fin.sum_univ_succ, C]

/-- `C` defers to `A`: `C(p | A = 4/5) = 4/5`, `C(p | A = 2/5) = 2/5`.
Source: mandate T2
Kind: N+
Fidelity: n/a -/
theorem defersA : Defers C Y A := by
  intro a
  by_cases h1 : a = 4/5
  · subst h1; norm_num [lev, sum_filter, Fin.sum_univ_succ, A, C, Y]
  by_cases h2 : a = 2/5
  · subst h2; norm_num [lev, sum_filter, Fin.sum_univ_succ, A, C, Y]
  · simp [lev, sum_filter, Fin.sum_univ_succ, A, C, Y, Ne.symm h1, Ne.symm h2]

/-- `C` defers to `B`.
Source: mandate T2
Kind: N+
Fidelity: n/a -/
theorem defersB : Defers C Y B := by
  intro b
  by_cases h1 : b = 4/5
  · subst h1; norm_num [lev, sum_filter, Fin.sum_univ_succ, B, C, Y]
  by_cases h2 : b = 2/5
  · subst h2; norm_num [lev, sum_filter, Fin.sum_univ_succ, B, C, Y]
  · simp [lev, sum_filter, Fin.sum_univ_succ, B, C, Y, Ne.symm h1, Ne.symm h2]

/-- Reading R-open holds: on the two disagreement cells the posterior is `3/5 ∈ (2/5, 4/5)`.
Source: mandate T2
Kind: N+
Fidelity: n/a -/
theorem betweenOpen : BetweenOpen C Y A B := by
  intro a b hab
  by_cases h1 : a = 4/5 ∧ b = 2/5
  · obtain ⟨rfl, rfl⟩ := h1
    refine ⟨3/5, ?_, by norm_num, by norm_num⟩
    norm_num [lev₂, sum_filter, Fin.sum_univ_succ, A, B, C, Y]
  by_cases h2 : a = 2/5 ∧ b = 4/5
  · obtain ⟨rfl, rfl⟩ := h2
    refine ⟨3/5, ?_, by norm_num, by norm_num⟩
    norm_num [lev₂, sum_filter, Fin.sum_univ_succ, A, B, C, Y]
  refine ⟨(a + b) / 2, ?_, ?_, ?_⟩
  · apply sum_eq_zero
    intro w hw
    rw [mem_lev₂] at hw
    exfalso
    fin_cases w <;> simp [A, B] at hw <;>
      first
      | exact h1 ⟨hw.1.symm, hw.2.symm⟩
      | exact h2 ⟨hw.1.symm, hw.2.symm⟩
      | exact hab (by rw [← hw.1, ← hw.2])
  · rcases lt_or_gt_of_ne hab with h | h
    · rw [min_eq_left h.le]; linarith
    · rw [min_eq_right h.le]; linarith
  · rcases lt_or_gt_of_ne hab with h | h
    · rw [max_eq_right h.le]; linarith
    · rw [max_eq_left h.le]; linarith

/-- The experts disagree on a positive-mass world (`C(A = B) = 40/50 < 1`).
Source: mandate T2
Kind: N+
Fidelity: n/a -/
theorem not_agreeAE : ¬ AgreeAE C A B := by
  intro h
  have := h 0 (by norm_num [C])
  norm_num [A, B] at this

/-- On the agreement cell `A = B = 4/5` the posterior is `17/20 > 4/5`: the novice is more
extreme than two agreeing experts, so reading R-closed fails here.
Source: mandate T2
Kind: N+
Fidelity: n/a -/
theorem extreme_high :
    ∑ w ∈ lev₂ A B (4/5) (4/5), C w * (Y w - 17/20) = 0 ∧ (4:ℝ)/5 < 17/20 := by
  constructor
  · norm_num [lev₂, sum_filter, Fin.sum_univ_succ, A, B, C, Y]
  · norm_num

/-- On the agreement cell `A = B = 2/5` the posterior is `7/20 < 2/5`.
Source: mandate T2
Kind: N+
Fidelity: n/a -/
theorem extreme_low :
    ∑ w ∈ lev₂ A B (2/5) (2/5), C w * (Y w - 7/20) = 0 ∧ (7:ℝ)/20 < 2/5 := by
  constructor
  · norm_num [lev₂, sum_filter, Fin.sum_univ_succ, A, B, C, Y]
  · norm_num

/-- The closed reading fails on `R8` (at the cell `A = B = 4/5`, whose posterior `17/20` exceeds
`max a b = 4/5`), as `zhang_finite` says it must.
Source: mandate T2
Kind: N+
Fidelity: n/a -/
theorem not_between4 : ¬ Between4 C Y A B := by
  intro h
  obtain ⟨c, hc, -, hle, -⟩ := h (4/5) (4/5)
  norm_num [lev₂, sum_filter, Fin.sum_univ_succ, A, B, C, Y] at hc hle
  linarith

/-- **T2, N+ refutation of reading R-open.** The eight-world model satisfies deference to both
experts, strict betweenness wherever the experts disagree, and `C(A = B) < 1` — so Zhang's
theorem is false under the reading "constraint 4 only when `a ≠ b`". The surviving neighbour
(reading R-closed, `zhang_finite`) fails on the model exactly at the agreement cells
(`extreme_high`, `extreme_low`, `not_between4`).
Source: [[Deference and Infinite Frames]] §1 l. 59 ("strictly between `a` and `b`"), reading
R-open; mandate T2
Kind: N+
Fidelity: n/a (refutation of a reading; ATTRIBUTION-UNVETTED as to Zhang's own statement)
Hyps: none -/
theorem refutes_open :
    (∀ w, 0 ≤ C w) ∧ ∑ w, C w = 1 ∧ Defers C Y A ∧ Defers C Y B ∧ BetweenOpen C Y A B ∧
      ¬ AgreeAE C A B ∧ ¬ Between4 C Y A B :=
  ⟨C_prob.1, C_prob.2, defersA, defersB, betweenOpen, not_agreeAE, not_between4⟩

end R8

/-! ## G5: a non-degenerate inhabitant of Gallow's hypothesis package -/

namespace G5

/-- Weights: four equiprobable worlds and a null fifth world.
Source: mandate T1 (witness)
Kind: D
Fidelity: n/a -/
def C : Fin 5 → ℝ := ![1/4, 1/4, 1/4, 1/4, 0]

/-- Expert `A`: certain at worlds `0`, `3`, uncertain (`1/2`) at `1`, `2`, and `1` at the null
world.
Source: mandate T1 (witness)
Kind: D
Fidelity: n/a -/
def A : Fin 5 → ℝ := ![1, 1/2, 1/2, 0, 1]

/-- Expert `B`: agrees with `A` on the support, disagrees at the null world.
Source: mandate T1 (witness)
Kind: D
Fidelity: n/a -/
def B : Fin 5 → ℝ := ![1, 1/2, 1/2, 0, 0]

/-- The event `p = {0, 1, 4}` as an indicator.
Source: mandate T1 (witness)
Kind: D
Fidelity: n/a -/
def Y : Fin 5 → ℝ := ![1, 1, 0, 0, 1]

/-- `C` defers to `A` (the `1/2` level set is `{1, 2}` with `Y = 1, 0`).
Source: mandate T1
Kind: N+
Fidelity: n/a -/
theorem defersA : Defers C Y A := by
  intro a
  by_cases h1 : a = 1
  · subst h1; norm_num [lev, sum_filter, Fin.sum_univ_succ, A, C, Y]
  by_cases h2 : a = 2⁻¹
  · subst h2; norm_num [lev, sum_filter, Fin.sum_univ_succ, A, C, Y]
  by_cases h3 : a = 0
  · subst h3; norm_num [lev, sum_filter, Fin.sum_univ_succ, A, C, Y]
  · simp [lev, sum_filter, Fin.sum_univ_succ, A, C, Y, Ne.symm h1, Ne.symm h2, Ne.symm h3]

/-- `C` defers to `B`.
Source: mandate T1
Kind: N+
Fidelity: n/a -/
theorem defersB : Defers C Y B := by
  intro b
  by_cases h1 : b = 1
  · subst h1; norm_num [lev, sum_filter, Fin.sum_univ_succ, B, C, Y]
  by_cases h2 : b = 2⁻¹
  · subst h2; norm_num [lev, sum_filter, Fin.sum_univ_succ, B, C, Y]
  by_cases h3 : b = 0
  · subst h3; norm_num [lev, sum_filter, Fin.sum_univ_succ, B, C, Y]
  · simp [lev, sum_filter, Fin.sum_univ_succ, B, C, Y, Ne.symm h1, Ne.symm h2, Ne.symm h3]

/-- Gallow's constraint 4 holds for every mixing weight `λ` (the experts agree on the support).
Source: mandate T1
Kind: N+
Fidelity: n/a -/
theorem pools (lam : ℝ) : Pools C Y A B lam := by
  intro a b
  by_cases h1 : a = 1 ∧ b = 1
  · obtain ⟨rfl, rfl⟩ := h1
    norm_num [lev₂, sum_filter, Fin.sum_univ_succ, A, B, C, Y]
  by_cases h2 : a = 2⁻¹ ∧ b = 2⁻¹
  · obtain ⟨rfl, rfl⟩ := h2
    norm_num [lev₂, sum_filter, Fin.sum_univ_succ, A, B, C, Y]
    ring
  by_cases h3 : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h3
    norm_num [lev₂, sum_filter, Fin.sum_univ_succ, A, B, C, Y]
  by_cases h4 : a = 1 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h4
    norm_num [lev₂, sum_filter, Fin.sum_univ_succ, A, B, C, Y]
  apply sum_eq_zero
  intro w hw
  rw [mem_lev₂] at hw
  exfalso
  fin_cases w <;> simp [A, B] at hw <;>
    first
    | exact h1 ⟨hw.1.symm, hw.2.symm⟩
    | exact h2 ⟨hw.1.symm, hw.2.symm⟩
    | exact h3 ⟨hw.1.symm, hw.2.symm⟩
    | exact h4 ⟨hw.1.symm, hw.2.symm⟩

/-- **T1, N+ witness**: Gallow's full hypothesis package is inhabited (for every `λ`), by a model
with a genuinely uncertain expert value, and its conclusion holds while `A ≠ B` as functions
(they differ at the null world `4`) — the theorem is about the support.
Source: [[Deference and Infinite Frames]] §1 l. 43 (the "experts agree" case); mandate T1
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem witness :
    (∀ w, 0 ≤ C w) ∧ ∑ w, C w = 1 ∧ Defers C Y A ∧ Defers C Y B ∧ (∀ lam, Pools C Y A B lam) ∧
      AgreeAE C A B ∧ A ≠ B ∧ A 1 = 1/2 ∧ Y 1 ≠ Y 2 := by
  refine ⟨fun w => ?_, ?_, defersA, defersB, pools, ?_, ?_, ?_, ?_⟩
  · fin_cases w <;> norm_num [C]
  · norm_num [Fin.sum_univ_succ, C]
  · exact gallow_finite (fun w => by fin_cases w <;> norm_num [C]) defersA defersB (pools 2)
      (by norm_num) (by norm_num)
  · intro h
    have := congrFun h 4
    simp [A, B, Matrix.cons_val] at this
  · simp [A]
  · simp [Y, Matrix.cons_val]

end G5

end

end Cleanroom.Lit.LitWeathersonFrames
