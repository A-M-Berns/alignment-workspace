import Cleanroom.Corrigibility.LegitNegStatic.Readouts
import Cleanroom.Corrigibility.LegitNegStatic.Toys
import Cleanroom.Corrigibility.LegitNegStatic.SealedBlind
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Toolkit for `legit-neg-pricing`

Package `legit-neg-pricing` (faf-cleanroom run, 2026-09-30). Infrastructure shared by the
headline files: the void-part decomposition of `P1` (the B6 identity), `argmaxOpt` helpers for
everywhere-defined proposals, and closed forms of the proposals on B's toy `toyB`. No headline
lives here; every declaration is `L`/`D` infrastructure over the `Problem` of record.
Imports: only the five static API modules plus `SealedBlind` for the `Fin 2` argmax helpers.
-/

namespace Cleanroom.Corrigibility.LegitNegPricing

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

variable {S A : Type} [Fintype S] [Fintype A]

/-! ### The void part of the standard -/

/-- `voidPart P a = ∑ s, π s · [¬leg s a] · u s a`: the part of `H a` that the floor drops
(`𝔼[(1 − ℓ_a) u_a]` of NEGATIVES B6).
Source: [[corr-legit-neg-inventory]] item 019 (B6)
Kind: D
Fidelity: exact -/
def voidPart (P : Problem S A) (a : A) : ℚ := ∑ s, P.prior s * ind (!P.leg s a) * P.u s a

/-- **The B6 identity** `P1 (S1 u) a = H a − 𝔼[(1 − ℓ_a) u_a]`, for every action of every problem.
Source: [[corr-legit-neg-inventory]] item 019 (B6, the identity)
Kind: L
Fidelity: exact -/
theorem P1_S1_eq_H_sub_voidPart (P : Problem S A) (a : A) :
    P.P1 (S1 P.u) a = P.H a - voidPart P a := by
  unfold Problem.P1 Problem.H Problem.W EU voidPart
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [S1_apply, ind_not]; ring

/-- `voidPart` is non-negative when `u ≥ 0` on the void terminals of `a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma voidPart_nonneg (P : Problem S A) (a : A) (h : ∀ s, P.leg s a = false → 0 ≤ P.u s a) :
    0 ≤ voidPart P a := by
  unfold voidPart
  refine Finset.sum_nonneg fun s _ => ?_
  by_cases hs : P.leg s a = false
  · simp only [hs, Bool.not_false, ind_true, mul_one]
    exact mul_nonneg (P.prior_nonneg s) (h s hs)
  · simp [Bool.not_eq_false] at hs; simp [hs]

/-- `voidPart` vanishes for a fully legitimate action.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma voidPart_eq_zero_of_allLeg (P : Problem S A) (a : A) (h : ∀ s, P.leg s a = true) :
    voidPart P a = 0 := by
  unfold voidPart
  exact Finset.sum_eq_zero fun s _ => by simp [h s]

/-- `voidPart ≤ D · P(¬L | a)` when `u ≤ D` on the void terminals of `a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma voidPart_le (P : Problem S A) (a : A) {D : ℚ}
    (h : ∀ s, P.leg s a = false → P.u s a ≤ D) :
    voidPart P a ≤ D * P.mass (fun s => !P.leg s a) := by
  unfold voidPart Problem.mass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  by_cases hs : P.leg s a = false
  · simp only [hs, Bool.not_false, ind_true, mul_one]
    have := mul_le_mul_of_nonneg_left (h s hs) (P.prior_nonneg s)
    linarith
  · simp [Bool.not_eq_false] at hs; simp [hs]

/-! ### `argmaxOpt` helpers -/

/-- An everywhere-defined `Option`-valued score has `argmaxOpt` equal to the `argmax` of its
values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmaxOpt_eq_argmax_of_forall_some {f : A → Option ℚ} {g : A → ℚ}
    (h : ∀ a, f a = some (g a)) : argmaxOpt f = argmax g := by
  rw [show f = fun a => some (g a) from funext h]
  exact argmaxOpt_some g

/-- `argmaxOpt (P2 V) = argmax (fun a => P1 V a / PL a)` when `P2` is defined everywhere
(exclusion convention: nothing is excluded here).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmaxOpt_P2_eq_argmax_div (P : Problem S A) (V : MenuVec S A) (h : ∀ a, P.PL a ≠ 0) :
    argmaxOpt (P.P2 V) = argmax (fun a => P.P1 V a / P.PL a) :=
  argmaxOpt_eq_argmax_of_forall_some fun a => P.P2_of_ne V a (h a)

/-- On a two-option menu the argmax is the whole menu iff the two scores tie.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmax_fin2_eq_univ_iff (f : Fin 2 → ℚ) : argmax f = univ ↔ f 0 = f 1 := by
  constructor
  · intro h
    have h0 : (0 : Fin 2) ∈ argmax f := by rw [h]; exact mem_univ _
    have h1 : (1 : Fin 2) ∈ argmax f := by rw [h]; exact mem_univ _
    rw [mem_argmax] at h0 h1
    exact le_antisymm (h1 0) (h0 1)
  · intro h
    ext a
    simp only [mem_argmax, mem_univ, iff_true, Fin.forall_fin_two]
    fin_cases a <;> simp [h]

/-- Extensionality for subsets of a two-option menu by literal indices (avoids `fin_cases`,
whose indices are not syntactic literals and block rewriting by the toy lemmas).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma finset_fin2_ext {s t : Finset (Fin 2)} (h0 : (0 : Fin 2) ∈ s ↔ 0 ∈ t)
    (h1 : (1 : Fin 2) ∈ s ↔ 1 ∈ t) : s = t :=
  Finset.ext_iff.2 (Fin.forall_fin_two.2 ⟨h0, h1⟩)

/-- The within-menu maximum over `Fin 2` is the `max` of the two values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sup'_fin2 (f : Fin 2 → ℚ) : univ.sup' univ_nonempty f = max (f 0) (f 1) := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun c _ => by fin_cases c <;> simp
  · exact max_le (Finset.le_sup' f (mem_univ 0)) (Finset.le_sup' f (mem_univ 1))

/-- The hybrid scoring of record for B16/C1: `S1` with a penalty `p` on option `a₁` written by
the humans at the terminal `(g, a₁)` (`fx_readouts.py` B16: `penalise(S1(P), [("g","a1")], "a1", p)`).
The penalty lives in `V` only; `H` is unpenalised. Not `toyC`, whose `p` sits in `u`.
Source: [[corr-legit-neg-inventory]] item 028 (B16); mandate "Targets" preamble
Kind: D
Fidelity: exact -/
def hybridV (P : Problem (Fin 2) (Fin 2)) (p : ℚ) : MenuVec (Fin 2) (Fin 2) :=
  Problem.penalise (S1 P.u) (fun s a => decide (s = 0 ∧ a = 1)) 1 p

/-! ### B's toy: closed forms -/

section ToyB

variable (v w ug0 ug1 πb : ℚ) (h0 : 0 ≤ πb) (h1 : πb ≤ 1)

/-- `toyB_prior`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma toyB_prior : (toyB v w ug0 ug1 πb h0 h1).prior = ![1 - πb, πb] := rfl

/-- `toyB_u`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma toyB_u (s a : Fin 2) :
    (toyB v w ug0 ug1 πb h0 h1).u s a = ![![ug0, ug1], ![v, w]] s a := rfl

/-- `toyB_leg`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma toyB_leg (s a : Fin 2) :
    (toyB v w ug0 ug1 πb h0 h1).leg s a = !(decide (s = 1) && decide (a = 1)) := rfl

/-- `P(L | a₀) = 1` on B's toy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyB_PL_zero : (toyB v w ug0 ug1 πb h0 h1).PL 0 = 1 := by
  simp [Problem.PL, Problem.mass, Fin.sum_univ_two]

/-- `P(L | a₁) = π_g = 1 − π_b` on B's toy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyB_PL_one : (toyB v w ug0 ug1 πb h0 h1).PL 1 = 1 - πb := by
  simp [Problem.PL, Problem.mass, Fin.sum_univ_two]

/-- `H a₀ = π_g ug0 + π_b v` on B's toy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyB_H_zero : (toyB v w ug0 ug1 πb h0 h1).H 0 = (1 - πb) * ug0 + πb * v := by
  simp [Problem.H, Problem.W, EU, Fin.sum_univ_two]

/-- `H a₁ = π_g ug1 + π_b w` on B's toy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyB_H_one : (toyB v w ug0 ug1 πb h0 h1).H 1 = (1 - πb) * ug1 + πb * w := by
  simp [Problem.H, Problem.W, EU, Fin.sum_univ_two]

/-- `P1 (S1 u) a₀ = π_g ug0 + π_b v` on B's toy (`a₀` legitimate everywhere).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyB_P1_S1_zero :
    (toyB v w ug0 ug1 πb h0 h1).P1 (S1 (toyB v w ug0 ug1 πb h0 h1).u) 0
      = (1 - πb) * ug0 + πb * v := by
  simp [Problem.P1, Fin.sum_univ_two]

/-- `P1 (S1 u) a₁ = π_g ug1` on B's toy (`a₁` void in `b`: the floor drops `w`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyB_P1_S1_one :
    (toyB v w ug0 ug1 πb h0 h1).P1 (S1 (toyB v w ug0 ug1 πb h0 h1).u) 1 = (1 - πb) * ug1 := by
  simp [Problem.P1, Fin.sum_univ_two]

/-- R2 scores from `a₀` under S1 are `H` on B's toy (`a₀` fully legitimate; sighted evaluators).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyB_R2scores_S1_zero (c : Fin 2) :
    (toyB v w ug0 ug1 πb h0 h1).R2scores (S1 (toyB v w ug0 ug1 πb h0 h1).u) 0 c
      = (toyB v w ug0 ug1 πb h0 h1).H c :=
  (toyB v w ug0 ug1 πb h0 h1).R2scores_S1_eq_H_of_allLeg 0 (fun s => by fin_cases s <;> rfl) c

/-- R2 scores from `a₁` under S1 read only `g`: `π_g · u(g, c)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyB_R2scores_S1_one (c : Fin 2) :
    (toyB v w ug0 ug1 πb h0 h1).R2scores (S1 (toyB v w ug0 ug1 πb h0 h1).u) 1 c
      = (1 - πb) * ![ug0, ug1] c := by
  simp [Problem.R2scores, Fin.sum_univ_two]

/-- `umax` in state `g` is `max ug0 ug1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyB_umax_zero : (toyB v w ug0 ug1 πb h0 h1).umax 0 = max ug0 ug1 := by
  unfold Problem.umax; rw [sup'_fin2]; simp

/-- `umax` in state `b` is `max v w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyB_umax_one : (toyB v w ug0 ug1 πb h0 h1).umax 1 = max v w := by
  unfold Problem.umax; rw [sup'_fin2]; simp

/-- Under the hybrid vector `P1 a₀` is unchanged (the penalty sits on `a₁`'s terminal).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyB_P1_hybrid_zero (p : ℚ) :
    (toyB v w ug0 ug1 πb h0 h1).P1 (hybridV (toyB v w ug0 ug1 πb h0 h1) p) 0
      = (1 - πb) * ug0 + πb * v := by
  simp [Problem.P1, hybridV, Problem.penalise, Fin.sum_univ_two]

/-- Under the hybrid vector `P1 a₁ = π_g (ug1 − p)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyB_P1_hybrid_one (p : ℚ) :
    (toyB v w ug0 ug1 πb h0 h1).P1 (hybridV (toyB v w ug0 ug1 πb h0 h1) p) 1
      = (1 - πb) * (ug1 - p) := by
  simp [Problem.P1, hybridV, Problem.penalise, Fin.sum_univ_two]

/-- R2 scores from `a₀` under the hybrid vector are still `H` (no penalty at `a₀`'s terminals).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyB_R2scores_hybrid_zero (p : ℚ) (c : Fin 2) :
    (toyB v w ug0 ug1 πb h0 h1).R2scores (hybridV (toyB v w ug0 ug1 πb h0 h1) p) 0 c
      = (toyB v w ug0 ug1 πb h0 h1).H c := by
  rw [← toyB_R2scores_S1_zero]
  simp [Problem.R2scores, hybridV, Problem.penalise, Fin.sum_univ_two]

/-- R2 scores from `a₁` under the hybrid vector: `π_g · (ug0, ug1 − p)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyB_R2scores_hybrid_one (p : ℚ) (c : Fin 2) :
    (toyB v w ug0 ug1 πb h0 h1).R2scores (hybridV (toyB v w ug0 ug1 πb h0 h1) p) 1 c
      = (1 - πb) * ![ug0, ug1 - p] c := by
  fin_cases c <;> simp [Problem.R2scores, hybridV, Problem.penalise, Fin.sum_univ_two]

end ToyB

end Cleanroom.Corrigibility.LegitNegPricing
