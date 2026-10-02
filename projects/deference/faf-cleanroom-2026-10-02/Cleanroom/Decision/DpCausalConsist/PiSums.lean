import FactoredSpaces.Probability
import Mathlib.Tactic.FinCases

/-!
# `dp-causal-consist`: sums over coordinate spaces

Infrastructure for the package `Cleanroom.Decision.DpCausalConsist`: how a sum over FAF's
coordinate space `Pt Val = ∀ i, Val i` splits when one coordinate, or a set `T` of coordinates,
is fixed (`sum_fix_coord`, `sum_split_agree`), and the explicit eight-term enumeration of
`Fin 3 → Bool` used by every witness (`pt3`, `forall_pt3`, `sum_pt3`). Nothing here reads a
decision-theoretic object; everything is stated over `FactoredSpaces.Pt`.
-/

namespace Cleanroom.Decision.DpCausalConsist

open FactoredSpaces Finset

section pi

variable {V : Type} [Fintype V] [DecidableEq V] {Val : V → Type} [∀ v, Fintype (Val v)]
  [∀ v, DecidableEq (Val v)]

/-- A sum over `Pt Val` equals the sum over points with coordinate `v` fixed to `c` of the sum
over the values of that coordinate: `∑_x F x = ∑_{x : x v = c} ∑_b F (x[v ↦ b])`.
Source: none: infrastructure
Kind: L -/
theorem sum_fix_coord (v : V) (c : Val v) (F : Pt Val → ℝ) :
    ∑ x, F x = ∑ x : Pt Val, if x v = c then ∑ b, F (Function.update x v b) else 0 := by
  have h1 : ∀ x : Pt Val, (if x v = c then ∑ b, F (Function.update x v b) else 0)
      = ∑ b : Val v, if x v = c then F (Function.update x v b) else 0 := by
    intro x; split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ b : Val v, (∑ x : Pt Val, if x v = c then F (Function.update x v b) else 0)
      = ∑ x : Pt Val, if x v = b then F x else 0 := by
    intro b
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun x => Function.update x v b) (fun x => Function.update x v c)
      ?_ ?_ ?_ ?_ ?_
    · intro x _; simp
    · intro x _; simp
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Function.update_idem, ← hx, Function.update_eq_self]
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Function.update_idem, ← hx, Function.update_eq_self]
    · intro x _; rfl
  simp_rw [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [Fintype V] [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] in
/-- A point agrees with `x₀` on `T` and with `y` off `T` iff it is `T.piecewise x₀ y`.
Source: none: infrastructure
Kind: L -/
theorem agree_iff_piecewise (T : Finset V) (x₀ y x : Pt Val) :
    ((∀ u ∈ T, x u = x₀ u) ∧ (∀ u ∉ T, y u = x u)) ↔ x = T.piecewise x₀ y := by
  constructor
  · rintro ⟨h1, h2⟩
    funext u
    by_cases hu : u ∈ T
    · simp [Finset.piecewise, hu, h1 u hu]
    · simp [Finset.piecewise, hu, h2 u hu]
  · rintro rfl
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · simp [Finset.piecewise, hu]
    · simp [Finset.piecewise, hu]

/-- **Splitting a sum over `Pt Val` at a coordinate set `T`**: sum over the points whose
`T`-coordinates are those of `x₀` (the representatives), and for each, over the points that
agree with it off `T`. Every point is counted exactly once.
Source: none: infrastructure
Kind: L -/
theorem sum_split_agree (T : Finset V) (x₀ : Pt Val) (h : Pt Val → ℝ) :
    ∑ x, h x = ∑ x : Pt Val, if (∀ u ∈ T, x u = x₀ u) then
      (∑ y : Pt Val, if (∀ u ∉ T, y u = x u) then h y else 0) else 0 := by
  have h1 : ∀ x : Pt Val, (if (∀ u ∈ T, x u = x₀ u) then
      (∑ y : Pt Val, if (∀ u ∉ T, y u = x u) then h y else 0) else 0)
      = ∑ y : Pt Val, if ((∀ u ∈ T, x u = x₀ u) ∧ (∀ u ∉ T, y u = x u)) then h y else 0 := by
    intro x
    by_cases hx : ∀ u ∈ T, x u = x₀ u
    · rw [if_pos hx]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : ∀ u ∉ T, y u = x u
      · rw [if_pos hy, if_pos ⟨hx, hy⟩]
      · rw [if_neg hy, if_neg (fun h => hy h.2)]
    · rw [if_neg hx]
      symm
      apply Finset.sum_eq_zero
      intro y _
      rw [if_neg (fun h => hx h.1)]
  simp_rw [h1]
  rw [Finset.sum_comm]
  symm
  refine Finset.sum_congr rfl fun y _ => ?_
  simp_rw [agree_iff_piecewise T x₀ y]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

/-- A sum over a set of points agreeing with `x` off `T` of a function that reads only the
coordinates off `T` is a constant times the number of such points; used in the form
"the weight factors out of an inner sum".
Source: none: infrastructure
Kind: L -/
theorem sum_agree_const_mul (T : Finset V) (x : Pt Val) (w : Pt Val → ℝ) (g : Pt Val → ℝ)
    (hw : ∀ y, (∀ u ∉ T, y u = x u) → w y = w x) :
    (∑ y : Pt Val, if (∀ u ∉ T, y u = x u) then w y * g y else 0)
      = w x * ∑ y : Pt Val, if (∀ u ∉ T, y u = x u) then g y else 0 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs with hy
  · rw [hw y hy]
  · simp

end pi

/-! ## The coordinate space `Fin 3 → Bool` of the witnesses -/

section pt3

/-- The point `(ℓ, m, k)` of `Fin 3 → Bool` (coordinates `0 = ℓ`, `1 = m`, `2 = k`).
Source: none: infrastructure (the witness coordinate space, mandate §3.1)
Kind: D -/
def pt3 (ℓ m k : Bool) : Pt (fun _ : Fin 3 => Bool) := ![ℓ, m, k]

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem pt3_zero (ℓ m k : Bool) : pt3 ℓ m k 0 = ℓ := rfl

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem pt3_one (ℓ m k : Bool) : pt3 ℓ m k 1 = m := rfl

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem pt3_two (ℓ m k : Bool) : pt3 ℓ m k 2 = k := rfl

/-- Every point of `Fin 3 → Bool` is a `pt3`.
Source: none: infrastructure
Kind: L -/
theorem eq_pt3 (x : Pt (fun _ : Fin 3 => Bool)) : x = pt3 (x 0) (x 1) (x 2) := by
  funext i; fin_cases i <;> rfl

/-- Quantifying over `Fin 3 → Bool` is quantifying over three booleans.
Source: none: infrastructure
Kind: L -/
theorem forall_pt3 (p : Pt (fun _ : Fin 3 => Bool) → Prop) :
    (∀ x, p x) ↔ ∀ ℓ m k, p (pt3 ℓ m k) := by
  constructor
  · intro h ℓ m k; exact h _
  · intro h x
    rw [eq_pt3 x]; exact h _ _ _

/-- `Fin 3 → Bool ≃ Bool × Bool × Bool`. Source: none: infrastructure. Kind: D -/
def pt3Equiv : Pt (fun _ : Fin 3 => Bool) ≃ Bool × Bool × Bool where
  toFun x := (x 0, x 1, x 2)
  invFun p := pt3 p.1 p.2.1 p.2.2
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

/-- A sum over `Fin 3 → Bool` as its eight terms.
Source: none: infrastructure
Kind: L -/
theorem sum_pt3 (f : Pt (fun _ : Fin 3 => Bool) → ℝ) :
    ∑ x, f x = f (pt3 false false false) + f (pt3 false false true) + f (pt3 false true false)
      + f (pt3 false true true) + f (pt3 true false false) + f (pt3 true false true)
      + f (pt3 true true false) + f (pt3 true true true) := by
  rw [← Equiv.sum_comp pt3Equiv.symm f, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  show f (pt3 true true true) + f (pt3 true true false)
    + (f (pt3 true false true) + f (pt3 true false false))
    + (f (pt3 false true true) + f (pt3 false true false)
    + (f (pt3 false false true) + f (pt3 false false false))) = _
  ring

/-- `P(X)` for a finite event `X` as an indicator sum (a `Finset` event needs no
`Set` decidability).
Source: none: infrastructure
Kind: L -/
theorem prob_eq_sum_ite {S : Type} [Fintype S] [DecidableEq S] (P : Distr S) (X : Finset S) :
    P.prob (↑X : Set S) = ∑ x, if x ∈ X then P.mass x else 0 := by
  unfold Distr.prob
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Set.indicator_apply]

/-- `P{x | p x}` as an indicator sum for a decidable predicate.
Source: none: infrastructure
Kind: L -/
theorem prob_setOf_eq_sum_ite {S : Type} [Fintype S] (P : Distr S) (p : S → Prop)
    [DecidablePred p] :
    P.prob {x | p x} = ∑ x, if p x then P.mass x else 0 := by
  unfold Distr.prob
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Set.indicator_apply]

end pt3

end Cleanroom.Decision.DpCausalConsist
