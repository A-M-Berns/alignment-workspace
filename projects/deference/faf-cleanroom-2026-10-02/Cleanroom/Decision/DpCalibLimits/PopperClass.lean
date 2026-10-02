import Cleanroom.Decision.DpCalibLimits.Rays

/-!
# T16 — Definition 10 and the Popper reading; the chance-conditional invariance

[[dp-calib-limits-mandate]] T16 (extension).

* `limitOCAt_iff_popper` (kind L): on every finite tree Definition 10 at a point coincides with
  its Popper reading where `O_d` is reachable — `popperLimit = limitCond` under the guard, and
  the `V`-clause is untouched. Not sold as more than that.
* **The necessary chance-conditional invariance** (`popperLimit_twin_leaves`): for two leaves
  with the same draw sequence and distinct worlds carried by no other leaf, the Popper reading
  of the uniform ray gives `P({λ(ℓ)} | {λ(ℓ), λ(ℓ')}) = c(ℓ)/(c(ℓ) + c(ℓ'))` with `c` the chance
  weights, for every procedure — T15's mechanism in general (the shared draw polynomial
  cancels). Any Popper function in the class `{popperLimit C B : C}` satisfies it; `ChanceTwin`'s
  `⅓` violates it.
* Sufficiency (the class question proper) is **not attempted**; see the report for the
  candidate statement and why it was not stated as an open declaration.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

section popperClass

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-- **Definition 10 at a point is its Popper reading where `O_d` is reachable**: the
definitions coincide (`popperLimit = limitCond` under the guard).
Source: P07 I2′; mandate T16
Kind: L
Fidelity: exact -/
theorem limitOCAt_iff_popper (s : ι → State Ω K) (obs : ι → Finset Ω) (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (d : ι) :
    LimitOCAt s obs C B d ↔
      (nuPoly C B (obs d) ≠ 0 →
        (∀ X, (s d).pr X = popperLimit C B X (obs d)) ∧
        (∀ X, 0 < limitCond C B X (obs d) →
          (s d).V X * (nuPoly C B (X ∩ obs d)).coeff (nuPoly C B (X ∩ obs d)).natTrailingDegree =
            (payPoly C B (X ∩ obs d)).coeff (nuPoly C B (X ∩ obs d)).natTrailingDegree)) := by
  unfold LimitOCAt popperLimit
  constructor
  · intro h hO
    obtain ⟨h1, h2⟩ := h hO
    exact ⟨fun X => by rw [if_pos hO]; exact h1 X, h2⟩
  · intro h hO
    obtain ⟨h1, h2⟩ := h hO
    exact ⟨fun X => by have := h1 X; rwa [if_pos hO] at this, h2⟩

/-- The draw polynomial of a draw list: the product of the tremble weights along it.
Source: none: infrastructure. Kind: D -/
noncomputable def drawsPoly (C : Proc ι acts K) (l : List (Σ d : ι, acts d)) : Polynomial K :=
  (l.map fun x => trembleW C x.1 x.2).prod

/-- The leaf polynomial factors as chance weight times the draw polynomial (the polynomial
form of `leafLaw_eq_chanceWeight_mul_drawsWeight`). Source: none: infrastructure. Kind: L -/
theorem leafLawPoly_eq_C_mul_drawsPoly (C : Proc ι acts K) :
    (B : Tree Ω ι acts K) → ∀ ℓ,
      leafLawPoly C B ℓ = Polynomial.C (chanceWeight B ℓ) * drawsPoly C (draws B ℓ)
  | .leaf _ _, _ => by simp [leafLawPoly, drawsPoly, chanceWeight]
  | .chance _ β child, ⟨i, ℓ⟩ => by
      simp only [leafLawPoly, chanceWeight_chance, draws_chance, Polynomial.C_mul]
      rw [leafLawPoly_eq_C_mul_drawsPoly C (child i) ℓ]; ring
  | .decision d child, ⟨a, ℓ⟩ => by
      simp only [leafLawPoly, chanceWeight_decision, draws_decision, drawsPoly, List.map_cons,
        List.prod_cons]
      rw [leafLawPoly_eq_C_mul_drawsPoly C (child a) ℓ]
      unfold drawsPoly; ring

/-- The draw polynomial is never zero (every `trembleW ≠ 0`). Source: none: infrastructure. Kind: L -/
theorem drawsPoly_ne_zero (C : Proc ι acts K) (l : List (Σ d : ι, acts d)) : drawsPoly C l ≠ 0 := by
  unfold drawsPoly
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_ne_zero (trembleW_ne_zero C x.1 x.2) ih

/-- **The chance-conditional invariance** (T15's mechanism, in general): for two leaves `ℓ, ℓ'`
with the same draw sequence, distinct worlds each carried by no other leaf, and positive
total chance weight, the Popper reading of Definition 10 gives
`P({λ(ℓ)} | {λ(ℓ), λ(ℓ')}) = c(ℓ) / (c(ℓ) + c(ℓ'))` for **every** procedure `C` — the shared
draw polynomial cancels. A necessary condition on the class `{popperLimit C B : C}`.
Source: mandate T16 ("chance-conditional invariance"); dp-sl-2-020
Kind: P
Fidelity: exact
Hyps: (a) same draws, (a) distinct worlds carried only by these leaves, (a) `0 < c(ℓ) + c(ℓ')` -/
theorem popperLimit_twin_leaves (C : Proc ι acts K) (B : Tree Ω ι acts K) (ℓ ℓ' : B.Leaves)
    (hdraws : draws B ℓ = draws B ℓ') (hne : world B ℓ ≠ world B ℓ')
    (huniq : ∀ ℓ'', world B ℓ'' = world B ℓ → ℓ'' = ℓ)
    (huniq' : ∀ ℓ'', world B ℓ'' = world B ℓ' → ℓ'' = ℓ')
    (hpos : 0 < chanceWeight B ℓ + chanceWeight B ℓ') :
    popperLimit C B {world B ℓ} {world B ℓ, world B ℓ'} =
      chanceWeight B ℓ / (chanceWeight B ℓ + chanceWeight B ℓ') := by
  -- the two event polynomials
  have hsing : ∀ ℓ₀ : B.Leaves, (∀ ℓ'', world B ℓ'' = world B ℓ₀ → ℓ'' = ℓ₀) →
      nuPoly C B {world B ℓ₀} = leafLawPoly C B ℓ₀ := fun ℓ₀ hu => by
    unfold nuPoly
    rw [Finset.sum_eq_single ℓ₀]
    · intro ℓ'' hℓ'' hne''
      rw [mem_worldEv, Finset.mem_singleton] at hℓ''
      exact absurd (hu ℓ'' hℓ'') hne''
    · intro h; exact absurd (by rw [mem_worldEv]; exact Finset.mem_singleton_self _) h
  have hpair : nuPoly C B {world B ℓ, world B ℓ'} = leafLawPoly C B ℓ + leafLawPoly C B ℓ' := by
    have hdisj : Disjoint ({world B ℓ} : Finset Ω) {world B ℓ'} := by
      rw [Finset.disjoint_singleton]; exact hne
    rw [Finset.insert_eq, nuPoly_union C B hdisj, hsing ℓ huniq, hsing ℓ' huniq']
  have hD := drawsPoly_ne_zero C (draws B ℓ)
  have hL := leafLawPoly_eq_C_mul_drawsPoly C B ℓ
  have hL' := leafLawPoly_eq_C_mul_drawsPoly C B ℓ'
  rw [← hdraws] at hL'
  have hnum : nuPoly C B ({world B ℓ} ∩ {world B ℓ, world B ℓ'}) =
      Polynomial.C (chanceWeight B ℓ) * drawsPoly C (draws B ℓ) := by
    rw [Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)),
      hsing ℓ huniq, hL]
  have hden : nuPoly C B {world B ℓ, world B ℓ'} =
      Polynomial.C (chanceWeight B ℓ + chanceWeight B ℓ') * drawsPoly C (draws B ℓ) := by
    rw [hpair, hL, hL', Polynomial.C_add]; ring
  have hden_ne : nuPoly C B {world B ℓ, world B ℓ'} ≠ 0 := by
    rw [hden]; exact mul_ne_zero (Polynomial.C_ne_zero.mpr hpos.ne') hD
  have hDk : (drawsPoly C (draws B ℓ)).coeff
      (Polynomial.C (chanceWeight B ℓ + chanceWeight B ℓ') * drawsPoly C (draws B ℓ)).natTrailingDegree ≠ 0 := by
    intro h0
    have := trailingCoeff_nuPoly_pos C B _ hden_ne
    rw [hden, Polynomial.trailingCoeff, Polynomial.coeff_C_mul, h0, mul_zero] at this
    exact lt_irrefl 0 this
  unfold popperLimit
  rw [if_pos hden_ne]
  unfold limitCond
  rw [hnum, hden, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, mul_div_mul_right _ _ hDk]

end popperClass

end Cleanroom.Decision.DpCalibLimits
