import Cleanroom.Decision.DpTwoLesions.Laws

/-!
# T7 — The mean-policy lemma

On any tree querying `d` exactly once on every path, every `ν` is affine in the label
(Proposition 4 at `k = 1`, through `dp-core-tree`'s Bernstein form), so a record pooled over
episodes at labels `p₁, …, p_t` has exactly the statistics of the mean label `p̄`:
`ν_{p̄}(X) = (1/t) ∑ᵢ ν_{pᵢ}(X)`. Hence the cumulative learner's conditionals are the conditionals
at its historical mean policy, and `Δ(p̄_t)` is the exact pooled penalty (Proposition 5's
premise, which the doc asserts). Instantiated on the overwrite tree, and on the bypass tree
through `oneLaw`.
Serves [[dp-two-lesions-mandate]] T7 (dp-core-2-007, 078's affinity clause).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

section general

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- `Bool` has two elements. Source: none: infrastructure. Kind: L -/
theorem card_bool_eq_two : Fintype.card Bool = 2 := by simp

/-- The label is the two-point deviation of any procedure at the (single) point.
Source: none: infrastructure
Kind: L -/
theorem procBoolK_eq_deviate (C : Proc Unit (fun _ => Bool) K) (q : K) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    procBoolK q h0 h1 = C.deviate () (FinDistr.twoPoint true card_bool_eq_two q h0 h1) := by
  funext d
  cases d
  ext b
  simp only [procBoolK_w, Proc.deviate_same, FinDistr.twoPoint_w]
  try (cases b <;> simp)

/-- **Affinity in the label (Proposition 4 at `k = 1`)**: on a tree querying `d` exactly once on
every path, `ν_{procBoolK q}(X) = b₀(1 − q) + b₁ q` with constants `b₀, b₁` not depending on
`q` (the Bernstein coefficients, the forcing conditionals of the two actions).
Source: [[decision-problems-v2]] Proposition 4 (via `dp-core-tree`'s `nu_twoPoint_eq_bernstein`);
[[iv-design-draw-as-instrument]] §5 ("Bernstein coefficients are forcing conditionals")
Kind: C
Fidelity: exact
Hyps: none -/
theorem nu_procBoolK_affine (B : Tree Ω Unit (fun _ => Bool) K) (hB : QueriesExactly B () 1)
    (X : Finset Ω) :
    ∃ b₀ b₁ : K, ∀ (q : K) (h0 : 0 ≤ q) (h1 : q ≤ 1),
      nu (procBoolK q h0 h1) B X = b₀ * (1 - q) + b₁ * q := by
  let C0 : Proc Unit (fun _ => Bool) K := procBoolK 0 le_rfl zero_le_one
  refine ⟨bernCoeff C0 () true B X 1 0, bernCoeff C0 () true B X 1 1, fun q h0 h1 => ?_⟩
  rw [procBoolK_eq_deviate C0 q h0 h1,
    nu_twoPoint_eq_bernstein C0 () true card_bool_eq_two B 1 hB X q h0 h1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernstein_eval]
  simp
  try ring

/-- The mean of labels in `[0, 1]` is in `[0, 1]`. Source: none: infrastructure. Kind: L -/
theorem mean_mem_Icc {t : ℕ} (ht : 0 < t) (ps : Fin t → K) (hps : ∀ i, 0 ≤ ps i ∧ ps i ≤ 1) :
    0 ≤ (∑ i, ps i) / t ∧ (∑ i, ps i) / t ≤ 1 := by
  have htK : (0 : K) < t := by exact_mod_cast ht
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => (hps i).1) htK.le
  · rw [div_le_one htK]
    calc ∑ i, ps i ≤ ∑ _i : Fin t, (1 : K) := Finset.sum_le_sum fun i _ => (hps i).2
      _ = t := by simp

/-- **The mean-policy lemma**: on a tree querying `d` exactly once on every path, the statistics
at the mean label are the pooled statistics: `ν_{p̄}(X) = (1/t) ∑ᵢ ν_{pᵢ}(X)`.
Source: [[two-lesions-doc-2026-09-18]] §5 ("a history compounded of episodes at policies
`p₁, …, p_t` has exactly the joint frequencies `P_{p̄}`"); [[iv-design-draw-as-instrument]] §5
("A lemma the doc also states")
Kind: C
Fidelity: exact
Hyps: none -/
theorem meanPolicy (B : Tree Ω Unit (fun _ => Bool) K) (hB : QueriesExactly B () 1)
    (X : Finset Ω) {t : ℕ} (ht : 0 < t) (ps : Fin t → K) (hps : ∀ i, 0 ≤ ps i ∧ ps i ≤ 1) :
    nu (procBoolK ((∑ i, ps i) / t) (mean_mem_Icc ht ps hps).1 (mean_mem_Icc ht ps hps).2) B X =
      (∑ i, nu (procBoolK (ps i) (hps i).1 (hps i).2) B X) / t := by
  obtain ⟨b₀, b₁, haff⟩ := nu_procBoolK_affine B hB X
  rw [haff]
  rw [Finset.sum_congr rfl fun i _ => haff (ps i) (hps i).1 (hps i).2]
  have htK : (t : K) ≠ 0 := by exact_mod_cast ht.ne'
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp
  try ring

end general

namespace DlParams

variable (P : DlParams K)

/-- `overwrite P` queries `d` exactly once on every path. Source: none: infrastructure. Kind: L -/
theorem overwrite_queriesExactly : QueriesExactly P.overwrite () 1 := P.overwrite_count

/-- **The mean-policy lemma on the double lesion** (overwrite tree, hence by `oneLaw` on the
bypass tree): for labels `p₁, …, p_t ∈ [0, 1]`, `ν_{p̄}(X)` under the label is the mean of the
`ν_{pᵢ}(X)` — so `Δ(p̄_t)` is the exact pooled penalty of a history at those labels.
Source: [[two-lesions-doc-2026-09-18]] §5 ("That `Δ(p̄_t)` is the right cumulative penalty is
not an approximation")
Kind: C
Fidelity: exact
Hyps: none -/
theorem meanPolicy_nuP {t : ℕ} (ht : 0 < t) (ps : Fin t → K) (hps : ∀ i, 0 ≤ ps i ∧ ps i ≤ 1)
    (X : Finset DlW) :
    P.nuP ((∑ i, ps i) / t) X = (∑ i, P.nuP (ps i) X) / t := by
  rw [P.nuP_eq (mean_mem_Icc ht ps hps).1 (mean_mem_Icc ht ps hps).2,
    meanPolicy P.overwrite P.overwrite_queriesExactly X ht ps hps]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (P.nuP_eq (hps i).1 (hps i).2 X).symm

/-- The same on the bypass tree, through `oneLaw`.
Source: [[iv-design-draw-as-instrument]] §5 (the lemma "on both trees")
Kind: C
Fidelity: exact
Hyps: none -/
theorem meanPolicy_bypass {t : ℕ} (ht : 0 < t) (ps : Fin t → K) (hps : ∀ i, 0 ≤ ps i ∧ ps i ≤ 1)
    (X : Finset DlW) :
    nu (procBoolK ((∑ i, ps i) / t) (mean_mem_Icc ht ps hps).1 (mean_mem_Icc ht ps hps).2)
        P.bypass X =
      (∑ i, nu (procBoolK (ps i) (hps i).1 (hps i).2) P.bypass X) / t := by
  rw [P.oneLaw, ← P.nuP_eq, P.meanPolicy_nuP ht ps hps X]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [P.oneLaw, P.nuP_eq (hps i).1 (hps i).2]

end DlParams

end Cleanroom.Decision.DpTwoLesions
