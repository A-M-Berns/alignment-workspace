import Cleanroom.Udt.UdtCondenseDd.Approx
import Mathlib.Algebra.BigOperators.Fin

/-!
# `Cleanroom.Udt.UdtCondenseDd.Witness`: layer-A witnesses (T2(b),(c), T3, T4(b), T12(a))

Work package `udt-condense-dd`. Every witness of the predictor-access layer, on `Fin n` carriers,
Mathlib only (the FAF-side witnesses are in `WitnessLatent.lean`, so a slice kill there costs one
file). Numerics by `norm_num` on `Fin.sum_univ_two`/`_four`; Finset identities by `decide`.

* `OffSupport` — T2(b): `O = Fin 2`, `D = δ₀`, two mechanisms with the same constant policy whose
  predictors agree on the support and differ at the unrealized observation `1`; accuracy on the
  support for both, `¬ Factors`, and a utility read off the unrealized branch that differs
  (transparent Newcomb's shape, in words only). T2(c): no `D`-expected loss separates them.
* `Attained` — T3: `O = Fin 4` uniform (`γ = 1/4`), `δ = 1/4`, the two predictors err on distinct
  observations, disagreement mass `1/2 = 2δ`: the bound is attained. `Strict`: overlapping error
  sets, disagreement mass `1/4 < 2δ`.
* `Varying` — T4(b): four observations, two mechanisms, the observation law genuinely depends on the
  prediction (`L = 1/32 > 0`, `Dof` non-constant), utilities differ (`1` vs `25/32`), and
  `approxDD_varying`'s bound `1/2` is strictly below the trivial range bound `R = 1` (repair round 1:
  the first witness sat where the bound was `≥ R`). Repair round 2: the reference-law variant
  `approxDD_varying_ref` is instantiated on the same data at `D₀ = unif4`, `δ = 1/4`, `η = 1/32`
  (`bound_instance_ref`, `bound_ref_lt_range`).
* `ConstPred` — T12(a): over two mechanisms sharing the identity policy, the constant predictor
  factors exactly and errs on mass exactly `1/2` (repair round 1: the first witness had one
  mechanism; repair round 2: the mass `1/2` is a conjunct of the statement).
-/

namespace Cleanroom.Udt.UdtCondenseDd

open Cleanroom.Udt.UdtPolicyCalc Finset

set_option linter.unusedSectionVars false

/-! ### T2(b),(c): the off-support counterexample -/

namespace OffSupport

/-- The shared constant policy (both mechanisms always act `0`).
Source: mandate T2(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pol : Fin 2 → Fin 2 → Fin 2 := fun _ _ => 0

/-- The predictor: agrees with the policy at the realized observation `0`, reads the mechanism's
name at the unrealized observation `1`.
Source: mandate T2(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def p : Fin 2 → Fin 2 → Fin 2 := fun m o => if o = 1 then m else 0

/-- The family's law: the point mass at observation `0` (`D(1) = 0`).
Source: mandate T2(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def D : FinDist (Fin 2) := FinDist.delta 0

/-- **Both mechanisms are exactly accurate on the support.**
Source: mandate T2(b) (udt-rep-030)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem accurate_on_support : ∀ m o, 0 < D.w o → p m o = pol m o := by
  intro m
  rw [Fin.forall_fin_two]
  refine ⟨fun _ => rfl, fun ho => ?_⟩
  simp [D] at ho

/-- **The two mechanisms have the same policy** (definitionally).
Source: mandate T2(b)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem pol_eq : pol 0 = pol 1 := rfl

/-- **The predictions differ at the unrealized observation.**
Source: mandate T2(b)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem p_ne : p 0 1 ≠ p 1 1 := by decide

/-- **The off-support counterexample (T2(b), load-bearing 5)**: on-support accuracy for every
mechanism does not give factoring — the predictor is unconstrained off the support.
Source: [[fair-environment-theorem]] "Obstruction … The Off-Support Problem" (lines 174–178); [[gap1-reframing-predictor-access]] §4 (udt-rep-030)
Kind: N+
Fidelity: exact (refutation of reading (ii)-exact without full support)
Hyps: none -/
theorem not_factors : ¬ Factors p pol := fun h => p_ne (congrFun (h 0 1 pol_eq) 1)

/-- The utility read off the unrealized branch: `U M = u(p(M, 1))` with `u a = a`. This is the
shape of transparent Newcomb (the box is filled according to the predicted behaviour on the
branch the agent never sees), in words only.
Source: mandate T2(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def U : Fin 2 → ℝ := fun m => ((p m 1 : Fin 2) : ℕ)

/-- **DD of the utility fails**: same policy, different utility.
Source: mandate T2(b) (udt-rep-030)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem U_ne : U 0 ≠ U 1 := by
  simp [U, p]

/-- **The encoding check (T2(c))**: for *every* loss `ℓ`, the `D`-expected loss of the two mechanisms
is the same — no `D`-expected-loss notion of optimality distinguishes them. The failure is not an
artifact of the encoding.
Source: mandate T2(c) ([[STANDARDS]] §3, impossibility check)
Kind: L
Fidelity: exact
Hyps: none -/
theorem offSupport_invisible_to_loss (ℓ : Fin 2 → Fin 2 → ℝ) :
    ∑ o, D.w o * ℓ (p 0 o) (pol 0 o) = ∑ o, D.w o * ℓ (p 1 o) (pol 1 o) := by
  simp [D, p, pol]

end OffSupport

/-! ### T3: the bound is attained -/

/-- The uniform distribution on `Fin 4`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def unif4 : FinDist (Fin 4) where
  w _ := 1 / 4
  nonneg _ := by norm_num
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num

/-- Supporting lemma: the weights of `unif4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem unif4_w (o : Fin 4) : unif4.w o = 1 / 4 := rfl

/-- The uniform law on two observations.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def unif2 : FinDist (Fin 2) := FinDist.halfHalf 0 1

/-- Supporting lemma: the weights of `unif2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem unif2_w : unif2.w 0 = 1 / 2 ∧ unif2.w 1 = 1 / 2 := by
  constructor
  · simp [unif2, FinDist.halfHalf, FinDist.bern_w]
  · simp [unif2, FinDist.halfHalf, FinDist.bern_w]; norm_num

namespace Attained

/-- The shared constant policy.
Source: mandate T3 (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pol : Fin 2 → Fin 4 → Fin 2 := fun _ _ => 0

/-- Mechanism `m`'s predictor errs exactly at observation `m` (`0` or `1`).
Source: mandate T3 (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def p : Fin 2 → Fin 4 → Fin 2 := fun m o => if o.val = m.val then 1 else 0

/-- Supporting lemma: the error sets.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem errSet_zero : errSet p pol 0 = {0} := by decide

/-- Supporting lemma: the error sets.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem errSet_one : errSet p pol 1 = {1} := by decide

/-- Supporting lemma: the disagreement set.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem disSet_eq : disSet p 0 1 = {0, 1} := by decide

/-- **Accuracy `δ = 1/4` for every mechanism under the uniform law.**
Source: mandate T3 (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem accurate : ∀ m, mass unif4.w (errSet p pol m) ≤ 1 / 4 := by
  rw [Fin.forall_fin_two]
  constructor
  · rw [errSet_zero]; simp [mass, unif4]
  · rw [errSet_one]; simp [mass, unif4]

/-- **The support bound `γ = 1/4`.**
Source: mandate T3 (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem support : ∀ o, 1 / 4 ≤ unif4.w o := fun _ => le_refl _

/-- **The disagreement mass equals `2δ = 1/2`: T3's bound is attained, not slack.**
Source: mandate T3 (witness, N+)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem disSet_mass : mass unif4.w (disSet p 0 1) = 2 * (1 / 4) := by
  rw [disSet_eq, mass, Finset.sum_pair (by decide)]
  simp [unif4]
  norm_num

/-- **The counting bound is attained too**: `|disSet| = 2 = 2δ/γ`.
Source: mandate T3 (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem disSet_card : ((disSet p 0 1).card : ℝ) = 2 * (1 / 4) / (1 / 4) := by
  rw [disSet_eq]
  norm_num

/-- **Non-degeneracy**: the predictions are non-constant and the disagreement set is non-empty.
Source: mandate T3 (witness, N+)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem nondegenerate : p 0 0 ≠ p 0 1 ∧ (disSet p 0 1).Nonempty ∧ pol 0 = pol 1 :=
  ⟨by decide, ⟨0, by rw [disSet_eq]; decide⟩, rfl⟩

end Attained

/-! ### T3: overlapping error sets, strict bound -/

namespace Strict

/-- The shared constant policy (three actions).
Source: mandate T3 (second instance)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pol : Fin 2 → Fin 4 → Fin 3 := fun _ _ => 0

/-- Both predictors err at observation `0`, with different wrong answers.
Source: mandate T3 (second instance)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def p : Fin 2 → Fin 4 → Fin 3 := fun m o => if o = 0 then m.succ else 0

/-- Supporting lemma: the error sets coincide.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem errSet_eq (m : Fin 2) : errSet p pol m = {0} := by
  revert m
  rw [Fin.forall_fin_two]
  exact ⟨by decide, by decide⟩

/-- Supporting lemma: the disagreement set.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem disSet_eq : disSet p 0 1 = {0} := by decide

/-- **Accuracy `δ = 1/4` and disagreement mass `1/4 < 2δ`: the bound is strict when the error sets
overlap.**
Source: mandate T3 (second instance)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem strict : (∀ m, mass unif4.w (errSet p pol m) ≤ 1 / 4) ∧
    mass unif4.w (disSet p 0 1) < 2 * (1 / 4) := by
  refine ⟨fun m => ?_, ?_⟩
  · rw [errSet_eq]; simp [mass, unif4]
  · rw [disSet_eq]; simp [mass, unif4]

end Strict

/-! ### T4(b): the prediction-dependent-observation witness -/

namespace Varying

/-! Repair round 1 (adversarial B2). The first witness had two observations, `δ = L = γ = 1/4`,
`R = 1`, where even the sharp bound `2δ + L · 2δ/γ = 1 = R` is the trivial range bound
(`|U₁ − U₂| ≤ R` holds from `hu` alone), so it inhabited the hypotheses but not the content. This
witness is the r1 probe `VaryingWitnessN.lean`'s: four observations, the uniform law against the
skew `(9/32, 8/32, 8/32, 7/32)` moved by the prediction at observation `3`, `L = 1/32`,
`γ = δ = 7/32`, `R = 1`; the bound is `1/2 < 1 = R` (`bound_lt_range`), the actual gap `7/32`. -/

/-- The shared constant policy.
Source: mandate T4(b) (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pol : Fin 2 → Fin 4 → Fin 2 := fun _ _ => 0

/-- Mechanism `0` is predicted perfectly; mechanism `1`'s predictor errs at observation `3`.
Source: mandate T4(b) (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def p : Fin 2 → Fin 4 → Fin 2 := fun m o => if m = 1 ∧ o = 3 then 1 else 0

/-- The skewed law `(9/32, 8/32, 8/32, 7/32)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def skew : FinDist (Fin 4) where
  w o := (if o = 0 then (9 : ℝ) else if o = 3 then 7 else 8) / 32
  nonneg o := by split_ifs <;> norm_num
  sum_one := by
    rw [Fin.sum_univ_four]
    rw [if_pos rfl, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_pos rfl]
    norm_num

/-- Supporting lemma: `skew.w 0 = 9/32`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem skew_w0 : skew.w 0 = 9 / 32 := by
  show (if (0 : Fin 4) = 0 then (9 : ℝ) else if (0 : Fin 4) = 3 then 7 else 8) / 32 = 9 / 32
  rw [if_pos rfl]

/-- Supporting lemma: `skew.w 1 = 1/4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem skew_w1 : skew.w 1 = 1 / 4 := by
  show (if (1 : Fin 4) = 0 then (9 : ℝ) else if (1 : Fin 4) = 3 then 7 else 8) / 32 = 1 / 4
  rw [if_neg (by decide), if_neg (by decide)]
  norm_num

/-- Supporting lemma: `skew.w 2 = 1/4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem skew_w2 : skew.w 2 = 1 / 4 := by
  show (if (2 : Fin 4) = 0 then (9 : ℝ) else if (2 : Fin 4) = 3 then 7 else 8) / 32 = 1 / 4
  rw [if_neg (by decide), if_neg (by decide)]
  norm_num

/-- Supporting lemma: `skew.w 3 = 7/32`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem skew_w3 : skew.w 3 = 7 / 32 := by
  show (if (3 : Fin 4) = 0 then (9 : ℝ) else if (3 : Fin 4) = 3 then 7 else 8) / 32 = 7 / 32
  rw [if_neg (by decide), if_pos rfl]

/-- **The observation law as a function of the prediction profile**: skewed when the predictor
predicts action `1` at observation `3`, uniform otherwise. This is the transparent-Newcomb shape:
what you see depends on the verdict.
Source: mandate T4(b) (witness); [[gap1-reframing-predictor-access]] §4 ("whether you *see* a full box is itself set by the predictor's verdict")
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def Dof (q : Fin 4 → Fin 2) : FinDist (Fin 4) := if q 3 = 1 then skew else unif4

/-- Supporting lemma: `tv skew unif4 = 1/32`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem tv_skew_unif4 : tv skew unif4 = 1 / 32 := by
  rw [tv, Fin.sum_univ_four, skew_w0, skew_w1, skew_w2, skew_w3]
  simp only [unif4_w]
  norm_num

/-- Supporting lemma: `tv unif4 skew = 1/32`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem tv_unif4_skew : tv unif4 skew = 1 / 32 := by
  rw [tv_symm, tv_skew_unif4]

/-- **The law is `L`-Lipschitz in the prediction profile with `L = 1/32`.**
Source: mandate T4(b) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem lipschitz : ∀ q q' : Fin 4 → Fin 2,
    tv (Dof q) (Dof q') ≤ (1 / 32) * (event fun o => q o ≠ q' o).card := by
  intro q q'
  have hcard : ∀ h : q 3 ≠ q' 3, (1 : ℝ) ≤ (event fun o => q o ≠ q' o).card := fun h => by
    have : 0 < (event fun o => q o ≠ q' o).card := Finset.card_pos.2 ⟨3, by simp [h]⟩
    exact_mod_cast this
  by_cases h1 : q 3 = 1 <;> by_cases h2 : q' 3 = 1
  · simp only [Dof, h1, h2, ↓reduceIte, tv_self]; positivity
  · have hc := hcard (by rw [h1]; exact Ne.symm h2)
    simp only [Dof, h1, h2, ↓reduceIte, tv_skew_unif4]
    linarith
  · have hc := hcard (by rw [h2]; exact h1)
    simp only [Dof, h1, h2, ↓reduceIte, tv_unif4_skew]
    linarith
  · simp only [Dof, h1, h2, ↓reduceIte, tv_self]; positivity

/-- Supporting lemma: the laws of the two mechanisms.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem Dof_p : Dof (p 0) = unif4 ∧ Dof (p 1) = skew := by
  constructor <;> simp [Dof, p]

/-- **Every law puts mass `≥ γ = 7/32` on every observation.**
Source: mandate T4(b) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem support : ∀ m o, (7 / 32 : ℝ) ≤ (Dof (p m)).w o := by
  rw [Fin.forall_fin_two]
  refine ⟨fun o => ?_, fun o => ?_⟩
  · rw [Dof_p.1, unif4_w]; norm_num
  · rw [Dof_p.2]
    show (7 / 32 : ℝ) ≤ (if o = 0 then (9 : ℝ) else if o = 3 then 7 else 8) / 32
    split_ifs <;> norm_num

/-- Supporting lemma: the error sets.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem errSet_eq : errSet p pol 0 = ∅ ∧ errSet p pol 1 = {3} := by
  constructor <;> decide

/-- **Accuracy `δ = 7/32` under each mechanism's own law.**
Source: mandate T4(b) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem accurate : ∀ m, mass (Dof (p m)).w (errSet p pol m) ≤ 7 / 32 := by
  rw [Fin.forall_fin_two]
  constructor
  · rw [errSet_eq.1]; simp [mass]; norm_num
  · rw [errSet_eq.2, Dof_p.2, mass, Finset.sum_singleton, skew_w3]

/-- The payoff: `1` for a correct prediction, `0` otherwise (values in `[0, 1]`, `R = 1`).
Source: mandate T4(b) (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def u : Fin 4 → Fin 2 → Fin 2 → ℝ := fun _ a b => if a = b then 1 else 0

/-- Supporting lemma: `u` takes values in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_mem : ∀ o a b, u o a b ∈ Set.Icc (0 : ℝ) (0 + 1) := by
  intro o a b
  unfold u
  split_ifs <;> norm_num

/-- Supporting lemma: the two utilities, `1` and `25/32`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem utilities : varyingUtility Dof u p pol 0 = 1 ∧ varyingUtility Dof u p pol 1 = 25 / 32 := by
  constructor
  · rw [varyingUtility, Fin.sum_univ_four, Dof_p.1]
    simp only [unif4_w]
    simp [u, p, pol]
    norm_num
  · rw [varyingUtility, Fin.sum_univ_four, Dof_p.2, skew_w0, skew_w1, skew_w2, skew_w3]
    simp [u, p, pol]
    norm_num

/-- **The T4(b) witness is non-degenerate**: `L = 1/32 > 0`, the law genuinely depends on the
prediction, the utilities differ, and the policies coincide.
Source: mandate T4(b) (witness, N+)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem nondegenerate : (0 : ℝ) < 1 / 32 ∧ Dof (p 0) ≠ Dof (p 1) ∧
    varyingUtility Dof u p pol 0 ≠ varyingUtility Dof u p pol 1 ∧ pol 0 = pol 1 := by
  refine ⟨by norm_num, ?_, ?_, rfl⟩
  · intro h
    have := congrArg (fun D : FinDist (Fin 4) => D.w 0) h
    simp only [Dof_p.1, Dof_p.2, unif4_w, skew_w0] at this
    norm_num at this
  · rw [utilities.1, utilities.2]; norm_num

/-- **`approxDD_varying` instantiated on the witness**: the bound `R (2δ + L · 2δ/γ) = 1/2` for the
actual difference `7/32`. The full hypothesis package is inhabited by a non-degenerate instance
*and* the bound is below the trivial range bound `R = 1` (`bound_lt_range`), so the instance
exercises the theorem's content.
Source: mandate T4(b) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem bound_instance :
    |varyingUtility Dof u p pol 0 - varyingUtility Dof u p pol 1| ≤
      1 * (2 * (7 / 32) + (1 / 32) * (2 * (7 / 32) / (7 / 32))) :=
  approxDD_varying Dof u (by norm_num) (by norm_num) (by norm_num) u_mem lipschitz support
    accurate rfl

/-- **The bound is strictly below the trivial range bound `R = 1`** (`1/2 < 1`): the instance is not
one where `|U₁ − U₂| ≤ R` from `hu` alone already gives the conclusion.
Source: mandate T4(b) (witness, N+); r1 adversarial audit B2
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem bound_lt_range : (1 : ℝ) * (2 * (7 / 32) + (1 / 32) * (2 * (7 / 32) / (7 / 32))) < 1 := by
  norm_num

/-- **The same, numerically**: `|1 − 25/32| = 7/32`, as a check that `bound_instance` is not vacuous.
Source: mandate T4(b) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem bound_numeric :
    |varyingUtility Dof u p pol 0 - varyingUtility Dof u p pol 1| = 7 / 32 := by
  rw [utilities.1, utilities.2]
  norm_num

/-- **The single-step form is also inhabited**: the witness satisfies the note's own Lipschitz
hypothesis with `L = 1/32`, and `approxDD_varying_single_step` gives the same bound.
Source: mandate T4(b) (witness); [[gap1-reframing-predictor-access]] §4
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem bound_instance_single_step :
    |varyingUtility Dof u p pol 0 - varyingUtility Dof u p pol 1| ≤
      1 * (2 * (7 / 32) + (1 / 32) * (2 * (7 / 32) / (7 / 32))) :=
  approxDD_varying_single_step Dof u (by norm_num) (by norm_num) (by norm_num) u_mem
    (fun q o a => by
      have h := lipschitz q (Function.update q o a)
      have hc : ((event fun o' => q o' ≠ Function.update q o a o').card : ℝ) ≤ 1 := by
        have hsub : (event fun o' => q o' ≠ Function.update q o a o') ⊆ {o} := by
          intro o' ho'
          rw [mem_event] at ho'
          rw [Finset.mem_singleton]
          by_contra hne
          exact ho' (by rw [Function.update_of_ne hne])
        have := Finset.card_le_card hsub
        rw [Finset.card_singleton] at this
        exact_mod_cast this
      linarith [mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 1 / 32)])
    support accurate rfl

/-! Repair round 2 (adversarial NB2). The reference-law variant `approxDD_varying_ref` is
instantiated on the same data at `D₀ = unif4`. The reference-law accuracy is `δ = 1/4`, not the
own-law `7/32`: under `unif4` mechanism `1`'s error set `{3}` has mass `1/4` (the r2 probe
`VaryingRef.lean`, lifted). -/

/-- Reference-law accuracy `δ = 1/4` under `unif4` for both mechanisms.
Source: mandate T4(c) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem accurate_ref : ∀ m, mass unif4.w (errSet p pol m) ≤ 1 / 4 := by
  rw [Fin.forall_fin_two]
  constructor
  · rw [errSet_eq.1]; simp [mass]
  · rw [errSet_eq.2, mass, Finset.sum_singleton, unif4_w]

/-- Both own laws are within `η = 1/32` of the reference law `unif4` in total variation.
Source: mandate T4(c) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem near_ref : ∀ m, tv (Dof (p m)) unif4 ≤ 1 / 32 := by
  rw [Fin.forall_fin_two]
  constructor
  · rw [Dof_p.1, tv_self]; norm_num
  · rw [Dof_p.2, tv_skew_unif4]

/-- The own-law accuracy `7/32` does **not** hold under the reference law: the reference-law
`δ` is genuinely larger (`1/4`), which is why `approxDD_varying_ref` is stated with its own `δ`.
Source: mandate T4(c) (witness); r2 adversarial audit §3.2
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_accurate_ref_at_own_delta : ¬ ∀ m, mass unif4.w (errSet p pol m) ≤ 7 / 32 := by
  intro h
  have := h 1
  rw [errSet_eq.2, mass, Finset.sum_singleton, unif4_w] at this
  norm_num at this

/-- **`approxDD_varying_ref` instantiated on the witness** at `D₀ = unif4`, `δ = 1/4`, `γ = 7/32`,
`η = 1/32`, `L = 1/32`, `R = 1`: bound `2(1/4 + 1/32) + (1/32)(2(1/4)/(7/32)) = 9/16 + 1/14` for
the actual gap `7/32`.
Source: mandate T4(c) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem bound_instance_ref :
    |varyingUtility Dof u p pol 0 - varyingUtility Dof u p pol 1| ≤
      1 * (2 * (1 / 4 + 1 / 32) + (1 / 32) * (2 * (1 / 4) / (7 / 32))) :=
  approxDD_varying_ref Dof u unif4 (by norm_num) (by norm_num) (by norm_num) u_mem lipschitz
    (fun o => by rw [unif4_w]; norm_num) near_ref accurate_ref rfl

/-- The reference-law bound (`≈ 0.634`) is strictly below the trivial range bound `R = 1`.
Source: mandate T4(c) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem bound_ref_lt_range :
    (1 : ℝ) * (2 * (1 / 4 + 1 / 32) + (1 / 32) * (2 * (1 / 4) / (7 / 32))) < 1 := by
  norm_num

end Varying

/-! ### T12(a): a constant predictor factors exactly and is arbitrarily inaccurate -/

namespace ConstPred

/-! Repair round 1 (fidelity B2). The first witness had mechanism type `Fin 1`, over which every
predictor factors and every disagreement bound holds for want of a second mechanism, so `Factors`
was exercised by nothing. Now two mechanisms share the identity policy (`pol 0 = pol 1` is a
conjunct of the headline), and the constant predictor agrees on them — the r1 probe
`Vacuity.lean`'s repair. -/

/-- Two mechanisms, both running the identity policy on `Fin 2`.
Source: mandate T12(a)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pol : Fin 2 → Fin 2 → Fin 2 := fun _ o => o

/-- The constant predictor (constantly `0`, for both mechanisms).
Source: mandate T12(a)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def p : Fin 2 → Fin 2 → Fin 2 := fun _ _ => 0

/-- **Factoring does not give accuracy (T12(a), refutation)**: over two mechanisms with the same
(identity) policy, the constant predictor factors exactly (disagreement mass `0 = 2 · 0`) yet errs
on mass exactly `1/2` under the uniform law (the fourth conjunct, exported since repair round 2) —
so no accuracy bound `δ < 1/2` follows from the `2δ`-disagreement bound, and in particular not the
bound `δ = 0` that exact factoring would suggest (the last conjunct). The conjunct `pol 0 = pol 1`
records that the two distinct mechanisms do share a policy, so `Factors` is exercised on a genuine
pair.
Source: mandate T12(a)
Kind: N+
Fidelity: exact (refutation of the converse of T3)
Hyps: none -/
theorem factoring_not_accuracy : Factors p pol ∧ pol 0 = pol 1 ∧
    (∀ m₁ m₂ : Fin 2, mass unif2.w (disSet p m₁ m₂) ≤ 2 * 0) ∧
    mass unif2.w (errSet p pol 0) = 1 / 2 ∧
    ¬ (∀ m, mass unif2.w (errSet p pol m) ≤ 0) := by
  have he : errSet p pol 0 = {1} := by decide
  have hm : mass unif2.w (errSet p pol 0) = 1 / 2 := by
    rw [he, mass, Finset.sum_singleton, unif2_w.2]
  refine ⟨fun _ _ _ => rfl, rfl, fun m₁ m₂ => ?_, hm, fun h => ?_⟩
  · have : disSet p m₁ m₂ = ∅ := disSet_eq_empty_iff.2 rfl
    rw [this]; simp [mass]
  · have h0 := h 0
    rw [hm] at h0
    norm_num at h0

end ConstPred

end Cleanroom.Udt.UdtCondenseDd
