/-
  legitimacy.lean  —  UNCHECKED — for the Lean-verify agent.

  Finite-frame shadow of idea L2 (drug / addiction = anticipated deference failure)
  from findings/legitimacy-corrigibility-ideate.md.

  PLAIN-ENGLISH CLAIM (what the two theorems are meant to say):

  (1) `legitimacy_defect_decomp` — The "legitimacy defect" of an expert relative to a
      novice, on weight `w` and target `θ`, decomposes as a single signed weighted sum:
          E_π(θ · w) − E_π(Eθ · w)  =  Σ_w π_w · w_w · (θ_w − Eθ_w).
      Pure linearity, universal in a CommRing, no frame hypothesis. This is the legitimacy
      analog of `Deference.decomposition` in LeanDeference.lean.

  (2) `drug_defect_sign` — If the *drugged* expert systematically OVERSTATES the target
      relative to its realized value at every world the novice takes seriously
      (`Eθ_w ≥ θ_w`, with the novice's selection weight `w_w ≥ 0` and `π_w ≥ 0`), then the
      legitimacy defect is ≤ 0:  E_π(θ · w) − E_π(Eθ · w) ≤ 0.
      I.e. the drugged expert's high opinion of θ is NOT matched by θ's realized value, so
      "θ weighted by the expert's opinion" underperforms "the expert's opinion weighted the
      same way" — a sign-determined cross-martingale defect. Because every term is novice-side
      data (π, θ, Eθ, w), the novice can compute it: the failure is ANTICIPATED.

  FIDELITY NOTES (audited in §8 of the findings file):
   - (1) is faithful, universal, non-vacuous (mirrors `decomposition`).
   - (2) does NOT smuggle its conclusion: the hypothesis is POINTWISE (`Eθ_w ≥ θ_w`),
     the conclusion is about the SIGNED WEIGHTED SUM; the implication is a real (elementary)
     monotonicity step over the support. It is non-vacuous (drug streams with Eθ > θ exist).
   - This is a finite shadow of ONE inequality in L2. It does NOT model the LI asymptotic
     "anticipation" (𝔼_n(⌜𝔼^{drug}_{f(n)}(θ)⌝)≈1), nor no-Dutch-book abstention. Same honesty
     boundary as the existing LeanDeference.lean (orientation §3).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset

namespace Legitimacy

variable {R : Type*} {W : Type*} [Fintype W]

/-- The legitimacy defect: novice's expectation of `θ` weighted by `w`, minus novice's
    expectation of the expert's estimate `Eθ` weighted by the same `w`.
    `π` = novice distribution, `θ` = realized {0,1}-target (or any value), `Eθ` = expert's
    estimate of the target, `w` = novice-computable selection weight. -/
def defect [CommRing R] (π θ Eθ w : W → R) : R :=
  (∑ x, π x * (θ x * w x)) - (∑ x, π x * (Eθ x * w x))

/-- (1) The defect decomposes as a single signed weighted sum
    `Σ π_x · w_x · (θ_x − Eθ_x)`. Pure linearity, no frame hypothesis. -/
theorem legitimacy_defect_decomp [CommRing R] (π θ Eθ w : W → R) :
    defect π θ Eθ w = ∑ x, π x * (w x * (θ x - Eθ x)) := by
  unfold defect
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- (2) Sign of the defect under the "drug" hypothesis: if at every world the drugged
    expert overstates the target (`θ x ≤ Eθ x`) with nonnegative novice mass and weight,
    then the legitimacy defect is ≤ 0. The drugged expert's optimism is not matched by
    reality, so the cross-martingale defect has a definite (exploitable) sign.

    Proof strategy mirrors `LeanDeference.value_of_CM`: each summand is the negation of a
    product of three nonnegatives, so `Finset.sum_nonpos` + `mul_nonneg` close it, using only
    lemmas/instances the confirmed `LeanDeference.lean` relies on
    (`[LinearOrder R] [IsStrictOrderedRing R]`, `mul_nonneg`, `Finset.sum_*`). -/
theorem drug_defect_sign [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (π θ Eθ w : W → R)
    (hπ : ∀ x, 0 ≤ π x) (hw : ∀ x, 0 ≤ w x) (hover : ∀ x, θ x ≤ Eθ x) :
    defect π θ Eθ w ≤ 0 := by
  rw [legitimacy_defect_decomp]
  -- Sum of pointwise-nonpositive terms is nonpositive.  Each term equals the
  -- negation of a product of three nonnegatives, so it is ≤ 0.
  apply Finset.sum_nonpos
  intro x _
  have hsub : 0 ≤ Eθ x - θ x := by linarith [hover x]
  have hprod : 0 ≤ π x * (w x * (Eθ x - θ x)) :=
    mul_nonneg (hπ x) (mul_nonneg (hw x) hsub)
  have hneg : π x * (w x * (θ x - Eθ x)) = -(π x * (w x * (Eθ x - θ x))) := by ring
  rw [hneg]
  linarith [hprod]

end Legitimacy

#print axioms Legitimacy.legitimacy_defect_decomp
#print axioms Legitimacy.drug_defect_sign
