import Cleanroom.Lit.LitShutdownPrefs

/-!
# lit-shutdown-prefs — audit round 2, adversarial lens: the joint maximiser exists

Not imported by the library. Elaborated with `scripts/lean-check`.

`Drest.theorem_5_1_neutrality_false_joint` says every joint maximiser of `F 8 (1/4) 2` over
`stdSimplex × [0,1]^2` is non-uniform. A universal statement of that shape refutes DReST
Theorem 5.1's neutrality clause only if a joint maximiser exists (otherwise the clause holds
vacuously). The slice version `theorem_5_1_neutrality_false` proves existence on the `ρ ≡ 1`
slice; the joint version does not state it. The gap is cheap to close: `F` is monotone in `ρ`
on `[0,1]^k` (`F_le_F_one`), so the slice maximiser with `ρ ≡ 1` is a joint maximiser
(`joint_maximiser_exists`), and `theorem_5_1_neutrality_false_joint_full` packages both halves.
-/

namespace Cleanroom.Lit.LitShutdownPrefs

namespace AuditR2

open Finset Drest

/-- `F` is monotone in `ρ`: on the simplex, with `ρ ∈ [0,1]^k`, `F p ρ ≤ F p 1`. -/
theorem F_le_F_one {k : ℕ} (n : ℕ) (lam mu : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hmu : 0 ≤ mu) (p : Fin k → ℝ) (hp : p ∈ stdSimplex ℝ (Fin k)) (ρ : Fin k → ℝ)
    (hρ : ∀ l, ρ l ∈ Set.Icc (0 : ℝ) 1) :
    F n lam mu p ρ ≤ F n lam mu p (fun _ => 1) := by
  unfold F
  refine Finset.sum_le_sum fun i _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hmu i)
  refine Finset.sum_le_sum fun l _ => ?_
  have hpl : 0 ≤ p l := hp.1 l
  have hpl1 : p l ≤ 1 := by
    have := Finset.single_le_sum (f := p) (fun j _ => hp.1 j) (mem_univ l)
    linarith [hp.2]
  have hbase : 0 ≤ 1 - (1 - lam) * p l := by
    have := mul_le_mul_of_nonneg_left hpl1 (show (0 : ℝ) ≤ 1 - lam by linarith)
    linarith
  have hpow : 0 ≤ (1 - (1 - lam) * p l) ^ i := pow_nonneg hbase i
  have key : 0 ≤ p l * (1 - (1 - lam) * p l) ^ i * (1 - ρ l) :=
    mul_nonneg (mul_nonneg hpl hpow) (sub_nonneg.mpr (hρ l).2)
  nlinarith [key]

/-- A joint maximiser of `F 8 (1/4) 2` over `stdSimplex × [0,1]^2` exists: the slice maximiser
of `theorem_5_1_neutrality_false` with `ρ ≡ 1`. -/
theorem joint_maximiser_exists :
    ∃ p ∈ stdSimplex ℝ (Fin 2), ∃ ρ : Fin 2 → ℝ, (∀ l, ρ l ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ q ∈ stdSimplex ℝ (Fin 2), ∀ ρ' : Fin 2 → ℝ, (∀ l, ρ' l ∈ Set.Icc (0 : ℝ) 1) →
        F 8 (1/4) 2 q ρ' ≤ F 8 (1/4) 2 p ρ := by
  obtain ⟨⟨p, hp, hmax⟩, -⟩ := theorem_5_1_neutrality_false
  refine ⟨p, hp, fun _ => 1, fun _ => by norm_num, fun q hq ρ' hρ' => ?_⟩
  calc F 8 (1/4) 2 q ρ' ≤ F 8 (1/4) 2 q (fun _ => 1) :=
        F_le_F_one 8 (1/4) 2 (by norm_num) (by norm_num) (by norm_num) q hq ρ' hρ'
    _ ≤ F 8 (1/4) 2 p (fun _ => 1) := hmax hq

/-- **Theorem 5.1's neutrality clause, refuted with the theorem's own quantifier over policies
`(p, ρ)`**: a joint maximiser exists, and no joint maximiser is maximally neutral. -/
theorem theorem_5_1_neutrality_false_joint_full :
    (∃ p ∈ stdSimplex ℝ (Fin 2), ∃ ρ : Fin 2 → ℝ, (∀ l, ρ l ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ q ∈ stdSimplex ℝ (Fin 2), ∀ ρ' : Fin 2 → ℝ, (∀ l, ρ' l ∈ Set.Icc (0 : ℝ) 1) →
        F 8 (1/4) 2 q ρ' ≤ F 8 (1/4) 2 p ρ) ∧
    ∀ p ∈ stdSimplex ℝ (Fin 2), ∀ ρ : Fin 2 → ℝ, (∀ l, ρ l ∈ Set.Icc (0 : ℝ) 1) →
      (∀ q ∈ stdSimplex ℝ (Fin 2), ∀ ρ' : Fin 2 → ℝ, (∀ l, ρ' l ∈ Set.Icc (0 : ℝ) 1) →
        F 8 (1/4) 2 q ρ' ≤ F 8 (1/4) 2 p ρ) → ¬ MaxNeutral p :=
  ⟨joint_maximiser_exists, fun p hp ρ hρ hmax => theorem_5_1_neutrality_false_joint p hp ρ hρ hmax⟩

end AuditR2

end Cleanroom.Lit.LitShutdownPrefs
