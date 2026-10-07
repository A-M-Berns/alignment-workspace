import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# corr-value-change — the three-term decomposition, abstractly (T2 core)

Source: [[value-change-as-epistemic-update]] §1.4. The decomposition
`Val(C) − Val(K) = (A) + (B) + (C)` is an identity about a *table of values*: the outcome
weights `p_j > 0` summing to one, the keep-values `v_K(a)`, and the outcome-values `v_j(a)`. This
file proves it at that level, exactly as §1.4 derives it (outcome by outcome, then the telescoping
split), so that the evidential two-step model (`TwoStep.lean`) and the causal Savage model
(`Savage.lean`) both inherit it by instantiation, and the auditor can match the steps.
The chosen acts `aK`, `a^j` (installed), `â^j` (the unchanged agent's best act in `C_j`) are
hypothesis-bearing variables: `hK : ∀ a, v_K a ≤ v_K aK`, `hhat : ∀ j a, v_j a ≤ v_j (â^j)`;
nothing is chosen by `Classical.choice`.
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

/-- A **value table**: outcome weights `p_j = P(C_j ∣ C) > 0` summing to one, the keep-values
`v_K(a) = E[U ∣ a ∧ K]` and the outcome-values `v_j(a) = E[U ∣ a ∧ C_j]` of the two-step decision
of §1.3, abstracted from how they are computed. Positivity of the `p_j` is the model's standing
convention (every outcome has positive probability).
Source: [[value-change-as-epistemic-update]] §1.3 (the notation list)
Kind: D
Fidelity: exact (the numbers §1.4 manipulates, with the model's positivity) -/
structure ValueTable (A J : Type) [Fintype A] [Fintype J] where
  /-- `p_j = P(C_j ∣ C)` -/
  p : J → ℝ
  /-- every outcome has positive probability -/
  p_pos : ∀ j, 0 < p j
  /-- the outcome weights sum to one -/
  p_sum : ∑ j, p j = 1
  /-- `v_K(a)`, the value of act `a` in the keep situation -/
  vK : A → ℝ
  /-- `v_j(a)`, the value of act `a` in outcome `C_j`, by the present `U` -/
  v : J → A → ℝ

variable {A J : Type} [Fintype A] [Fintype J]

namespace ValueTable

variable (T : ValueTable A J)

/-- `Val(K) = v_K(a^K)`.
Source: [[value-change-as-epistemic-update]] §1.3
Kind: D
Fidelity: exact -/
def ValK (aK : A) : ℝ := T.vK aK

/-- `Val(C) = ∑_j p_j v_j(a^j)`, with `a^j` the act the changed agent takes in `C_j`.
Source: [[value-change-as-epistemic-update]] §1.3
Kind: D
Fidelity: exact -/
def ValC (aj : J → A) : ℝ := ∑ j, T.p j * T.v j (aj j)

/-- Term **(A) choice**: `∑_j p_j [v_j(a^j) − v_j(â^j)]`.
Source: [[value-change-as-epistemic-update]] §1.4
Kind: D
Fidelity: exact -/
def termA (aj ahat : J → A) : ℝ := ∑ j, T.p j * (T.v j (aj j) - T.v j (ahat j))

/-- Term **(B) adaptation**: `∑_j p_j [v_j(â^j) − v_j(a^K)]`.
Source: [[value-change-as-epistemic-update]] §1.4
Kind: D
Fidelity: exact -/
def termB (ahat : J → A) (aK : A) : ℝ := ∑ j, T.p j * (T.v j (ahat j) - T.v j aK)

/-- Term **(C) level**: `∑_j p_j [v_j(a^K) − v_K(a^K)]`.
Source: [[value-change-as-epistemic-update]] §1.4
Kind: D
Fidelity: exact -/
def termC (aK : A) : ℝ := ∑ j, T.p j * (T.v j aK - T.vK aK)

/-- Step 1 of §1.4: since the `p_j` sum to one, `Val(C) − Val(K) = ∑_j p_j [v_j(a^j) − v_K(a^K)]`,
outcome by outcome.
Source: [[value-change-as-epistemic-update]] §1.4 (first display)
Kind: L
Fidelity: exact -/
theorem ValC_sub_ValK (aj : J → A) (aK : A) :
    T.ValC aj - T.ValK aK = ∑ j, T.p j * (T.v j (aj j) - T.vK aK) := by
  unfold ValC ValK
  have h : T.vK aK = ∑ j, T.p j * T.vK aK := by rw [← sum_mul, T.p_sum, one_mul]
  conv_lhs => rw [h]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- Step 2 of §1.4: each bracket splits through the two intermediate quantities,
`v_j(a^j) − v_K(a^K) = [v_j(a^j) − v_j(â^j)] + [v_j(â^j) − v_j(a^K)] + [v_j(a^K) − v_K(a^K)]`,
an identity since the intermediate terms cancel.
Source: [[value-change-as-epistemic-update]] §1.4 (second display)
Kind: L
Fidelity: exact -/
theorem bracket_split (aj ahat : J → A) (aK : A) (j : J) :
    T.v j (aj j) - T.vK aK =
      (T.v j (aj j) - T.v j (ahat j)) + (T.v j (ahat j) - T.v j aK) + (T.v j aK - T.vK aK) := by
  ring

/-- **The decomposition** (§1.4): `Val(C) − Val(K) = (A) + (B) + (C)`, an identity with no
hypothesis beyond the table's (`∑ p_j = 1`); in particular it holds for *any* acts `a^j`, `â^j`,
`a^K` — the signs of (A) and (B) are where the maximizations enter (`termA_nonpos`,
`termB_nonneg`).
Source: [[value-change-as-epistemic-update]] §1.4 (third display)
Kind: P
Fidelity: exact
Hyps: (a) none beyond the table -/
theorem decomposition (aj ahat : J → A) (aK : A) :
    T.ValC aj - T.ValK aK = T.termA aj ahat + T.termB ahat aK + T.termC aK := by
  rw [ValC_sub_ValK]
  unfold termA termB termC
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [T.bracket_split aj ahat aK j]
  ring

/-- **(A) ≤ 0**, from the defining property of `â^j` (it maximizes `v_j`) and nothing else.
Source: [[value-change-as-epistemic-update]] §1.4 ("Term (A) is never positive")
Kind: P
Fidelity: exact
Hyps: (a) `hhat : ∀ j a, v_j a ≤ v_j (â^j)` -/
theorem termA_nonpos (aj ahat : J → A) (hhat : ∀ j a, T.v j a ≤ T.v j (ahat j)) :
    T.termA aj ahat ≤ 0 := by
  unfold termA
  apply sum_nonpos
  intro j _
  have := hhat j (aj j)
  have := T.p_pos j
  nlinarith

/-- **(B) ≥ 0**, from the defining property of `â^j` and nothing else.
Source: [[value-change-as-epistemic-update]] §1.4 ("Term (B) is never negative")
Kind: P
Fidelity: exact
Hyps: (a) `hhat` -/
theorem termB_nonneg (ahat : J → A) (aK : A) (hhat : ∀ j a, T.v j a ≤ T.v j (ahat j)) :
    0 ≤ T.termB ahat aK := by
  unfold termB
  apply sum_nonneg
  intro j _
  have := hhat j aK
  have := T.p_pos j
  nlinarith

/-- **(B) vanishes iff `a^K` maximizes every `v_j`** (the note's iff, checked: both directions hold
because every `p_j > 0`). The parenthetical "in particular whenever every `Δ_{C_j}` ranks acts
as `Δ_K` does" is the ⇐ direction's special case.
Source: [[value-change-as-epistemic-update]] §1.4 ("Term (B) vanishes iff `a^K` maximizes every
`v_j`"); mandate Known issues 1
Kind: P
Fidelity: exact
Hyps: (a) `hhat` -/
theorem termB_eq_zero_iff (ahat : J → A) (aK : A) (hhat : ∀ j a, T.v j a ≤ T.v j (ahat j)) :
    T.termB ahat aK = 0 ↔ ∀ j a, T.v j a ≤ T.v j aK := by
  unfold termB
  have hnn : ∀ j ∈ (univ : Finset J), 0 ≤ T.p j * (T.v j (ahat j) - T.v j aK) := by
    intro j _
    have := hhat j aK
    have := T.p_pos j
    nlinarith
  rw [sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h j a
    have hj := h j (mem_univ j)
    have hp := T.p_pos j
    have : T.v j (ahat j) - T.v j aK = 0 := by
      rcases mul_eq_zero.1 hj with h0 | h0
      · exact absurd h0 hp.ne'
      · exact h0
    linarith [hhat j a]
  · intro h j _
    have h1 := h j (ahat j)
    have h2 := hhat j aK
    have : T.v j (ahat j) - T.v j aK = 0 := by linarith
    rw [this, mul_zero]

/-- (A) vanishes iff every installed act `a^j` maximizes `v_j`.
Source: [[value-change-as-epistemic-update]] §3.4 ("iff the installed values select, in each
outcome, what the old values would select given that outcome")
Kind: P
Fidelity: exact
Hyps: (a) `hhat` -/
theorem termA_eq_zero_iff (aj ahat : J → A) (hhat : ∀ j a, T.v j a ≤ T.v j (ahat j)) :
    T.termA aj ahat = 0 ↔ ∀ j a, T.v j a ≤ T.v j (aj j) := by
  unfold termA
  have hnn : ∀ j ∈ (univ : Finset J), 0 ≤ T.p j * (T.v j (ahat j) - T.v j (aj j)) := by
    intro j _
    have := hhat j (aj j)
    have := T.p_pos j
    nlinarith
  have hneg : ∑ j, T.p j * (T.v j (aj j) - T.v j (ahat j)) =
      -∑ j, T.p j * (T.v j (ahat j) - T.v j (aj j)) := by
    rw [← sum_neg_distrib]; refine sum_congr rfl fun j _ => ?_; ring
  rw [hneg, neg_eq_zero, sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h j a
    have hj := h j (mem_univ j)
    have hp := T.p_pos j
    have : T.v j (ahat j) - T.v j (aj j) = 0 := by
      rcases mul_eq_zero.1 hj with h0 | h0
      · exact absurd h0 hp.ne'
      · exact h0
    linarith [hhat j a]
  · intro h j _
    have h1 := h j (ahat j)
    have h2 := hhat j (aj j)
    have : T.v j (ahat j) - T.v j (aj j) = 0 := by linarith
    rw [this, mul_zero]

/-- **The intrinsic case** (§1.4, first route, pure level shift): if `v_j = v_K + β_j` pointwise
for every `j`, then `Val(C) − Val(K) = β̄ − ℓ` with `β̄ = ∑_j p_j β_j` the expected level shift and
`ℓ = ∑_j p_j [v_K(a^K) − v_K(a^j)] ≥ 0` the expected loss from the acts the changed agent takes.
Source: [[value-change-as-epistemic-update]] §1.4 (first route display)
Kind: P
Fidelity: exact
Hyps: (a) `hβ : ∀ j a, v_j a = v_K a + β_j`; `hK : a^K` maximizes `v_K` (for `ℓ ≥ 0`) -/
theorem intrinsic_case (aj : J → A) (aK : A) (β : J → ℝ) (hβ : ∀ j a, T.v j a = T.vK a + β j)
    (hK : ∀ a, T.vK a ≤ T.vK aK) :
    T.ValC aj - T.ValK aK = (∑ j, T.p j * β j) - ∑ j, T.p j * (T.vK aK - T.vK (aj j)) ∧
      0 ≤ ∑ j, T.p j * (T.vK aK - T.vK (aj j)) := by
  constructor
  · rw [ValC_sub_ValK, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [hβ j (aj j)]; ring
  · apply sum_nonneg
    intro j _
    have := hK (aj j)
    have := T.p_pos j
    nlinarith

/-- In the intrinsic case `â^j = a^K` works and (B) = 0: a level shift leaves relative values
untouched.
Source: [[value-change-as-epistemic-update]] §1.4 ("relative values are untouched, `â^j = a^K`")
Kind: L
Fidelity: exact
Hyps: (a) `hβ`, `hK` -/
theorem intrinsic_termB_zero (aK : A) (β : J → ℝ) (hβ : ∀ j a, T.v j a = T.vK a + β j)
    (hK : ∀ a, T.vK a ≤ T.vK aK) : T.termB (fun _ => aK) aK = 0 := by
  have hhat : ∀ j a, T.v j a ≤ T.v j aK := by
    intro j a; rw [hβ j a, hβ j aK]; linarith [hK a]
  exact (T.termB_eq_zero_iff (fun _ => aK) aK hhat).2 hhat

/-- **Single outcome, no level change**: with `v_C = v_K` pointwise (which with one outcome is the
whole of `v`), (B) = 0. Stated for any index type: if every `v_j = v_K` pointwise then (B) = 0,
because `a^K` then maximizes every `v_j`.
Source: [[value-change-as-epistemic-update]] §1.4 ("Uncertainty is required": one outcome and
`w_C = v_K`); mandate T2(d)
Kind: L (one rewrite into `termB_eq_zero_iff` plus `hK`; audit r2 N5)
Fidelity: stronger: any number of outcomes with `v_j = v_K`
Hyps: (a) `hv : ∀ j a, v_j a = v_K a`, `hhat`, `hK` -/
theorem termB_zero_of_v_eq_vK (ahat : J → A) (aK : A) (hv : ∀ j a, T.v j a = T.vK a)
    (hhat : ∀ j a, T.v j a ≤ T.v j (ahat j)) (hK : ∀ a, T.vK a ≤ T.vK aK) :
    T.termB ahat aK = 0 := by
  rw [T.termB_eq_zero_iff ahat aK hhat]
  intro j a; rw [hv j a, hv j aK]; exact hK a

/-- The net value of changing is (A) plus the *gain* `∑_j p_j v_j(â^j) − v_K(a^K)` = (B) + (C).
Source: [[value-change-as-epistemic-update]] §1.4 (regrouping)
Kind: L
Fidelity: exact -/
theorem ValC_sub_ValK_eq_termA_add (aj ahat : J → A) (aK : A) :
    T.ValC aj - T.ValK aK = T.termA aj ahat + ((∑ j, T.p j * T.v j (ahat j)) - T.vK aK) := by
  rw [T.decomposition aj ahat aK, add_assoc]
  congr 1
  unfold termB termC
  rw [← sum_add_distrib]
  have h : T.vK aK = ∑ j, T.p j * T.vK aK := by rw [← sum_mul, T.p_sum, one_mul]
  conv_rhs => rw [h]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

end ValueTable

end

end Cleanroom.Corrigibility.CorrValueChange
