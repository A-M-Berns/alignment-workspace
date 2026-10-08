import Cleanroom.Corrigibility.CorrValueChange.Product
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# corr-value-change — the §1.4 example and its variants (T4, T3(d))

Source: [[value-change-as-epistemic-update]] §1.4 (Example, "Uncertainty is required", the
act-by-act reward); fixture `decomposition`, `info_payment`. Facts `F = Bool` (`true` = `A`), acts
`Fin 3`, the base utility `U(F, K, ·) = (1, 0, 3/5)` on `A`-worlds and `(0, 1, 3/5)` on `B`-worlds,
`P(K) = P(C) = 1/2`, acts equiprobable. Each variant is a `ProductModel`; the decomposition's
three terms are computed on the fact side through the transfer lemmas, exactly as the fixture
does. Every witness inhabits the full hypothesis package of `TwoStep.decomposition`,
`termA_nonpos`, `termB_nonneg` (the maximizations `hhat`, `hK` are proved, not assumed).

Reading the witnesses: in each of them the installed choices are the informed choices (`â^j = a^j`),
so every clause of the form `termA â â = 0` is the identity `∑_j p_j (v_j(a^j) − v_j(a^j)) = 0`; the
content of those conjunctions is the `hhat`/`hK` clause before it (that `a^j` is the informed
choice) and the `(B)`, `(C)` values. (A) is non-trivially nonzero in `grade_three_separated`
(`Variants.lean`) and `cond_reflection_not_imp_A_zero` (`CondLegit.lean`).
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

/-- The base utility `U(F, K, a)`: `(1, 0, 3/5)` on `A`, `(0, 1, 3/5)` on `B`.
Source: [[value-change-as-epistemic-update]] §1.4 (Example)
Kind: D
Fidelity: exact -/
def baseU (f : Bool) (a : Fin 3) : ℝ := ![if f then 1 else 0, if f then 0 else 1, 3 / 5] a

/-- The teacher (§1.4): outcomes `C_A, C_B` with `P(F = j ∣ C_j) = 9/10`, `U` independent of the
configuration.
Source: [[value-change-as-epistemic-update]] §1.4 (Example); fixture `teacher`
Kind: D
Fidelity: exact -/
def teacherPM : ProductModel Bool Bool (Fin 3) where
  q := fun f c => match c with
    | none => 1 / 4
    | some j => if f = j then 9 / 40 else 1 / 40
  q_nonneg := fun f c => by cases c <;> simp <;> split_ifs <;> norm_num
  q_sum := by norm_num [Fintype.sum_bool, Fintype.sum_option]
  σ := fun _ => 1 / 3
  σ_pos := fun _ => by norm_num
  σ_sum := by norm_num [Fin.sum_univ_three]
  Uf := fun f _ a => baseU f a
  qK_pos := by norm_num [Fintype.sum_bool]
  qC_pos := fun j => by cases j <;> simp [Fintype.sum_bool] <;> norm_num

/-- The coin (§1.4, "Uncertainty is required"): outcomes uncorrelated with the facts.
Source: [[value-change-as-epistemic-update]] §1.4; fixture `coin`
Kind: D
Fidelity: exact -/
def coinPM : ProductModel Bool Bool (Fin 3) where
  q := fun _ c => match c with
    | none => 1 / 4
    | some _ => 1 / 8
  q_nonneg := fun f c => by cases c <;> simp <;> norm_num
  q_sum := by norm_num [Fintype.sum_bool, Fintype.sum_option]
  σ := fun _ => 1 / 3
  σ_pos := fun _ => by norm_num
  σ_sum := by norm_num [Fin.sum_univ_three]
  Uf := fun f _ a => baseU f a
  qK_pos := by norm_num [Fintype.sum_bool]
  qC_pos := fun j => by cases j <;> simp [Fintype.sum_bool] <;> norm_num

/-- The pill with a uniform level shift `β` (`β = 0` is the plain pill): a single outcome, `U` on
the change event raised by `β`.
Source: [[value-change-as-epistemic-update]] §1.4 ("the pill plus a uniform level shift `β`");
fixture `pill`, `paid`, `underpaid`
Kind: D
Fidelity: exact -/
def paidPM (β : ℝ) : ProductModel Bool Unit (Fin 3) where
  q := fun _ _ => 1 / 4
  q_nonneg := fun _ _ => by norm_num
  q_sum := by norm_num [Fintype.sum_bool, Fintype.sum_option]
  σ := fun _ => 1 / 3
  σ_pos := fun _ => by norm_num
  σ_sum := by norm_num [Fin.sum_univ_three]
  Uf := fun f c a => match c with
    | none => baseU f a
    | some _ => baseU f a + β
  qK_pos := by norm_num [Fintype.sum_bool]
  qC_pos := fun _ => by norm_num [Fintype.sum_bool]

/-- The act-by-act reward: a single outcome revealing nothing, a bonus of `3/10` on `a₁` inside
the change event.
Source: [[value-change-as-epistemic-update]] §1.4 ("with a bonus of `0.3` on `a₁` inside the change
event and nothing revealed"); fixture `bonus`
Kind: D
Fidelity: exact -/
def bonusPM : ProductModel Bool Unit (Fin 3) where
  q := fun _ _ => 1 / 4
  q_nonneg := fun _ _ => by norm_num
  q_sum := by norm_num [Fintype.sum_bool, Fintype.sum_option]
  σ := fun _ => 1 / 3
  σ_pos := fun _ => by norm_num
  σ_sum := by norm_num [Fin.sum_univ_three]
  Uf := fun f c a => match c with
    | none => baseU f a
    | some _ => baseU f a + (if a = 0 then 3 / 10 else 0)
  qK_pos := by norm_num [Fintype.sum_bool]
  qC_pos := fun _ => by norm_num [Fintype.sum_bool]

/-- Installed choices for two outcomes: `a₁` in `C_A`, `a₂` in `C_B`.
Source: [[value-change-as-epistemic-update]] §1.4
Kind: D
Fidelity: exact -/
def chooseSignal : Bool → Fin 3 := fun j => if j then 0 else 1

/-! ## The teacher: `(A, B, C) = (0, 3/10, 0)`, `Val(K) = 3/5`, `Val(C) = 9/10` -/

/-- The teacher's values: `v_K = (1/2, 1/2, 3/5)`, `v_A = (9/10, 1/10, 3/5)`, `v_B = (1/10, 9/10, 3/5)`,
`p_j = 1/2`.
Source: [[value-change-as-epistemic-update]] §1.4 (Example)
Kind: L
Fidelity: exact -/
theorem teacherPM_values :
    (∀ a, teacherPM.toTwoStep.vK teacherPM.U a = ![1 / 2, 1 / 2, 3 / 5] a) ∧
    (∀ j a, teacherPM.toTwoStep.v teacherPM.U j a =
      ![if j then 9 / 10 else 1 / 10, if j then 1 / 10 else 9 / 10, 3 / 5] a) ∧
    (∀ j, teacherPM.toTwoStep.p j = 1 / 2) := by
  refine ⟨fun a => ?_, fun j a => ?_, fun j => ?_⟩
  · rw [ProductModel.toTwoStep_vK]; fin_cases a <;>
      simp [ProductModel.vKf, ProductModel.qK, teacherPM, baseU, Fintype.sum_bool] <;> norm_num
  · rw [ProductModel.toTwoStep_v]; cases j <;> fin_cases a <;>
      simp [ProductModel.vf, ProductModel.qC, teacherPM, baseU, Fintype.sum_bool] <;> norm_num
  · rw [ProductModel.toTwoStep_p]; cases j <;>
      simp [ProductModel.qC, ProductModel.qCtot, teacherPM, Fintype.sum_bool] <;> norm_num

/-- **T4, the teacher**: `a^K = a₃` maximizes `v_K`, `â^j = a_j` maximizes `v_j`, the installed
choices are `a_j`; `(A, B, C) = (0, 3/10, 0)`, `Val(K) = 3/5`, `Val(C) = 9/10`.
Source: [[value-change-as-epistemic-update]] §1.4 (Example, computed); fixture `teacher`
Kind: N+
Fidelity: exact -/
theorem teacher_decomposition :
    (∀ a, teacherPM.toTwoStep.vK teacherPM.U a ≤ teacherPM.toTwoStep.vK teacherPM.U 2) ∧
    (∀ j a, teacherPM.toTwoStep.v teacherPM.U j a ≤ teacherPM.toTwoStep.v teacherPM.U j (chooseSignal j)) ∧
    (teacherPM.toTwoStep.table teacherPM.U).termA chooseSignal chooseSignal = 0 ∧
    (teacherPM.toTwoStep.table teacherPM.U).termB chooseSignal 2 = 3 / 10 ∧
    (teacherPM.toTwoStep.table teacherPM.U).termC 2 = 0 ∧
    teacherPM.toTwoStep.ValK teacherPM.U 2 = 3 / 5 ∧
    teacherPM.toTwoStep.ValC teacherPM.U chooseSignal = 9 / 10 := by
  obtain ⟨hK, hv, hp⟩ := teacherPM_values
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; rw [hK, hK]; fin_cases a <;> simp <;> norm_num
  · intro j a; rw [hv, hv]; cases j <;> fin_cases a <;> simp [chooseSignal] <;> norm_num
  · simp only [ValueTable.termA, TwoStep.table, Fintype.sum_bool, hv, hp, chooseSignal]; simp
  · simp only [ValueTable.termB, TwoStep.table, Fintype.sum_bool, hv, hp, chooseSignal]; simp; norm_num
  · simp only [ValueTable.termC, TwoStep.table, Fintype.sum_bool, hv, hp, hK]; simp
  · unfold TwoStep.ValK; rw [hK]; simp
  · unfold TwoStep.ValC; rw [Fintype.sum_bool, hv, hv, hp, hp]; norm_num [chooseSignal]

/-! ## The coin: `(−1/10, 0, 0)` -/

/-- The coin's values: `v_K = v_A = v_B = (1/2, 1/2, 3/5)`, `p_j = 1/2`.
Source: [[value-change-as-epistemic-update]] §1.4
Kind: L
Fidelity: exact -/
theorem coinPM_values :
    (∀ a, coinPM.toTwoStep.vK coinPM.U a = ![1 / 2, 1 / 2, 3 / 5] a) ∧
    (∀ j a, coinPM.toTwoStep.v coinPM.U j a = ![1 / 2, 1 / 2, 3 / 5] a) ∧
    (∀ j, coinPM.toTwoStep.p j = 1 / 2) := by
  refine ⟨fun a => ?_, fun j a => ?_, fun j => ?_⟩
  · rw [ProductModel.toTwoStep_vK]; fin_cases a <;>
      simp [ProductModel.vKf, ProductModel.qK, coinPM, baseU, Fintype.sum_bool] <;> norm_num
  · rw [ProductModel.toTwoStep_v]; cases j <;> fin_cases a <;>
      simp [ProductModel.vf, ProductModel.qC, coinPM, baseU, Fintype.sum_bool] <;> norm_num
  · rw [ProductModel.toTwoStep_p]; cases j <;>
      simp [ProductModel.qC, ProductModel.qCtot, coinPM, Fintype.sum_bool] <;> norm_num

/-- **T4, the coin**: with the installed choices `a_j` and `â^j = a^K = a₃`, `(A, B, C) = (−1/10, 0, 0)`:
strictly worse than keeping.
Source: [[value-change-as-epistemic-update]] §1.4 ("A change whose outcome is random but
uncorrelated with the facts … has (I) = 0 and (A) = −0.1"); fixture `coin`
Kind: N+
Fidelity: exact -/
theorem coin_decomposition :
    (∀ a, coinPM.toTwoStep.vK coinPM.U a ≤ coinPM.toTwoStep.vK coinPM.U 2) ∧
    (∀ j a, coinPM.toTwoStep.v coinPM.U j a ≤ coinPM.toTwoStep.v coinPM.U j 2) ∧
    (coinPM.toTwoStep.table coinPM.U).termA chooseSignal (fun _ => 2) = -1 / 10 ∧
    (coinPM.toTwoStep.table coinPM.U).termB (fun _ => 2) 2 = 0 ∧
    (coinPM.toTwoStep.table coinPM.U).termC 2 = 0 := by
  obtain ⟨hK, hv, hp⟩ := coinPM_values
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a; rw [hK, hK]; fin_cases a <;> simp <;> norm_num
  · intro j a; rw [hv, hv]; fin_cases a <;> simp <;> norm_num
  · simp only [ValueTable.termA, TwoStep.table, Fintype.sum_bool, hv, hp, chooseSignal]; simp; norm_num
  · simp only [ValueTable.termB, TwoStep.table, Fintype.sum_bool, hv, hp]; simp
  · simp only [ValueTable.termC, TwoStep.table, Fintype.sum_bool, hv, hp, hK]; simp

/-! ## The pill with a level shift: `(−1/10, 0, β)`, total `β − 1/10` -/

/-- The paid pill's values: `v_K = (1/2, 1/2, 3/5)`, `v_C = v_K + β`, `p = 1`.
Source: [[value-change-as-epistemic-update]] §1.4
Kind: L
Fidelity: exact -/
theorem paidPM_values (β : ℝ) :
    (∀ a, (paidPM β).toTwoStep.vK (paidPM β).U a = ![1 / 2, 1 / 2, 3 / 5] a) ∧
    (∀ j a, (paidPM β).toTwoStep.v (paidPM β).U j a = ![1 / 2, 1 / 2, 3 / 5] a + β) ∧
    (∀ j, (paidPM β).toTwoStep.p j = 1) := by
  refine ⟨fun a => ?_, fun j a => ?_, fun j => ?_⟩
  · rw [ProductModel.toTwoStep_vK]; fin_cases a <;>
      simp [ProductModel.vKf, ProductModel.qK, paidPM, baseU, Fintype.sum_bool] <;> norm_num
  · rw [ProductModel.toTwoStep_v]; fin_cases a <;>
      simp [ProductModel.vf, ProductModel.qC, paidPM, baseU, Fintype.sum_bool] <;> ring
  · rw [ProductModel.toTwoStep_p]
    norm_num [ProductModel.qC, ProductModel.qCtot, paidPM, Fintype.sum_bool]

/-- **T4, the pill with a uniform level shift `β`** (the plain pill at `β = 0`): installed choice
`a₁`, `â = a^K = a₃`; `(A, B, C) = (−1/10, 0, β)`, so `Val(C) − Val(K) = β − 1/10`: accepted iff
`β > 1/10`. In particular `β = 1/5` gives total `1/10` and `β = 1/20` gives `−1/20`.
Source: [[value-change-as-epistemic-update]] §1.4 ("the pill plus a uniform level shift `β` has
(A) = −0.1 and (Π) = β, so it is accepted iff `β > 0.1`"); fixture `pill`, `paid`, `underpaid`
Kind: N+ (as a theorem in `β`)
Fidelity: exact -/
theorem paid_decomposition (β : ℝ) :
    (∀ a, (paidPM β).toTwoStep.vK (paidPM β).U a ≤ (paidPM β).toTwoStep.vK (paidPM β).U 2) ∧
    (∀ j a, (paidPM β).toTwoStep.v (paidPM β).U j a ≤ (paidPM β).toTwoStep.v (paidPM β).U j 2) ∧
    ((paidPM β).toTwoStep.table (paidPM β).U).termA (fun _ => 0) (fun _ => 2) = -1 / 10 ∧
    ((paidPM β).toTwoStep.table (paidPM β).U).termB (fun _ => 2) 2 = 0 ∧
    ((paidPM β).toTwoStep.table (paidPM β).U).termC 2 = β ∧
    (paidPM β).toTwoStep.ValC (paidPM β).U (fun _ => 0) - (paidPM β).toTwoStep.ValK (paidPM β).U 2
      = β - 1 / 10 := by
  obtain ⟨hK, hv, hp⟩ := paidPM_values β
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; rw [hK, hK]; fin_cases a <;> simp <;> norm_num
  · intro j a; rw [hv, hv]; fin_cases a <;> simp <;> norm_num
  · simp only [ValueTable.termA, TwoStep.table, Fintype.sum_unique, hv, hp]; simp; norm_num
  · simp only [ValueTable.termB, TwoStep.table, Fintype.sum_unique, hv, hp]; simp
  · simp only [ValueTable.termC, TwoStep.table, Fintype.sum_unique, hv, hp, hK]; simp
  · unfold TwoStep.ValC TwoStep.ValK; rw [Fintype.sum_unique, hv, hp, hK]; simp; ring

/-- The two instances the note quotes: `β = 1/5` nets `1/10`, `β = 1/20` nets `−1/20`.
Source: [[value-change-as-epistemic-update]] §1.4; fixture `paid`, `underpaid`
Kind: N+
Fidelity: exact -/
theorem paid_instances :
    (paidPM (1 / 5)).toTwoStep.ValC (paidPM (1 / 5)).U (fun _ => 0) -
        (paidPM (1 / 5)).toTwoStep.ValK (paidPM (1 / 5)).U 2 = 1 / 10 ∧
    (paidPM (1 / 20)).toTwoStep.ValC (paidPM (1 / 20)).U (fun _ => 0) -
        (paidPM (1 / 20)).toTwoStep.ValK (paidPM (1 / 20)).U 2 = -1 / 20 := by
  constructor
  · rw [(paid_decomposition (1 / 5)).2.2.2.2.2]; norm_num
  · rw [(paid_decomposition (1 / 20)).2.2.2.2.2]; norm_num

/-! ## T3(d): the act-by-act reward, `(A, B, C, I, Π) = (0, 1/5, 0, 0, 1/5)` -/

/-- The bonus model's values: `v_K = (1/2, 1/2, 3/5)`, `v_C = (4/5, 1/2, 3/5)`, `w = v_K`, `p = 1`, and
the uninformative-choice assumption holds.
Source: [[value-change-as-epistemic-update]] §1.4
Kind: L
Fidelity: exact -/
theorem bonusPM_values :
    (∀ a, bonusPM.toTwoStep.vK bonusPM.U a = ![1 / 2, 1 / 2, 3 / 5] a) ∧
    (∀ j a, bonusPM.toTwoStep.v bonusPM.U j a = ![4 / 5, 1 / 2, 3 / 5] a) ∧
    (∀ j a, bonusPM.w j a = ![1 / 2, 1 / 2, 3 / 5] a) ∧
    (∀ j, bonusPM.toTwoStep.p j = 1) ∧ bonusPM.Uninformative := by
  refine ⟨fun a => ?_, fun j a => ?_, fun j a => ?_, fun j => ?_, ?_⟩
  · rw [ProductModel.toTwoStep_vK]; fin_cases a <;>
      simp [ProductModel.vKf, ProductModel.qK, bonusPM, baseU, Fintype.sum_bool] <;> norm_num
  · rw [ProductModel.toTwoStep_v]; fin_cases a <;>
      simp [ProductModel.vf, ProductModel.qC, bonusPM, baseU, Fintype.sum_bool] <;> norm_num
  · fin_cases a <;> simp [ProductModel.w, ProductModel.qC, bonusPM, baseU, Fintype.sum_bool] <;> norm_num
  · rw [ProductModel.toTwoStep_p]
    norm_num [ProductModel.qC, ProductModel.qCtot, bonusPM, Fintype.sum_bool]
  · intro f; simp [ProductModel.qK, ProductModel.qCtot, ProductModel.qC, bonusPM, Fintype.sum_bool]

/-- **T3(d), the act-bonus witness**: with installed choice `a₁ = â`, `ã = a^K = a₃`,
`(A, B, C) = (0, 1/5, 0)` and `(I, Π) = (0, 1/5)`: payment, not learning, picked up by (B) with a
single outcome.
Source: [[value-change-as-epistemic-update]] §1.4 ("`(Π) = 0.2`, (I) = 0, (B) = 0.2, (C) = 0");
fixture `bonus`
Kind: N+
Fidelity: exact -/
theorem bonus_decomposition :
    (∀ a, bonusPM.toTwoStep.vK bonusPM.U a ≤ bonusPM.toTwoStep.vK bonusPM.U 2) ∧
    (∀ j a, bonusPM.toTwoStep.v bonusPM.U j a ≤ bonusPM.toTwoStep.v bonusPM.U j 0) ∧
    (∀ j a, bonusPM.w j a ≤ bonusPM.w j 2) ∧
    (bonusPM.toTwoStep.table bonusPM.U).termA (fun _ => 0) (fun _ => 0) = 0 ∧
    (bonusPM.toTwoStep.table bonusPM.U).termB (fun _ => 0) 2 = 1 / 5 ∧
    (bonusPM.toTwoStep.table bonusPM.U).termC 2 = 0 ∧
    bonusPM.termI (fun _ => 2) 2 = 0 ∧
    bonusPM.termPi (fun _ => 0) (fun _ => 2) = 1 / 5 := by
  obtain ⟨hK, hv, hw, hp, _⟩ := bonusPM_values
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; rw [hK, hK]; fin_cases a <;> simp <;> norm_num
  · intro j a; rw [hv, hv]; fin_cases a <;> simp <;> norm_num
  · intro j a; rw [hw, hw]; fin_cases a <;> simp <;> norm_num
  · simp only [ValueTable.termA, TwoStep.table, Fintype.sum_unique, hv, hp]; simp
  · simp only [ValueTable.termB, TwoStep.table, Fintype.sum_unique, hv, hp]; simp; norm_num
  · simp only [ValueTable.termC, TwoStep.table, Fintype.sum_unique, hv, hp, hK]; simp
  · simp only [ProductModel.termI, Fintype.sum_unique, hw, hp]; simp
  · simp only [ProductModel.termPi, Fintype.sum_unique, hv, hw, hp]; simp; norm_num


/-! ## T3: the teacher's information term, `(I) = 3/10 > 0` -/

/-- The teacher's informed keep-values `w_j`: the utility does not depend on the configuration, so
`w_j = v_j`: `(9/10, 1/10, 3/5)` on `A`, `(1/10, 9/10, 3/5)` on `B`.
Source: [[value-change-as-epistemic-update]] §1.4 ("`w_j(a) = E[U(f, K, a) ∣ C_j]`")
Kind: L
Fidelity: exact -/
theorem teacher_w (j : Bool) (a : Fin 3) :
    teacherPM.w j a = ![if j then 9 / 10 else 1 / 10, if j then 1 / 10 else 9 / 10, 3 / 5] a := by
  cases j <;> fin_cases a <;>
    simp [ProductModel.w, ProductModel.qC, teacherPM, baseU, Fintype.sum_bool] <;> norm_num

/-- The teacher satisfies the uninformative-choice assumption (`P(f ∣ C) = P(f ∣ K)`, product form).
Source: [[value-change-as-epistemic-update]] §1.4 (the standing assumption of the example)
Kind: N+
Fidelity: exact -/
theorem teacher_uninformative : teacherPM.Uninformative := by
  intro f
  cases f <;> simp [ProductModel.qK, ProductModel.qCtot, ProductModel.qC, teacherPM, Fintype.sum_bool] <;>
    norm_num

/-- **T3, the teacher's information term**: `ã^j = a_j` maximizes `w_j`, `a^K = a₃`, `(I) = 3/10`
(the note's "(I) = (B) = 0.3"), `(Π) = 0`, so `(I) > 0`, and the right-hand side of `termI_pos_iff`
holds: `a^K` fails to maximize `w_A` (proved from `teacher_w` directly, `9/10 > 3/5`, not through
the iff: audit r4 fidelity N2). The instance the ledger's Witness cells for `termI_nonneg`,
`info_payment_split` and `termI_pos_iff` name (audit r3 fidelity N1; the probe `TeacherInfo.lean`).
Source: [[value-change-as-epistemic-update]] §1.4 ("the whole of (B) is information: (I) = 0.3")
Kind: N+
Fidelity: exact -/
theorem teacher_info :
    teacherPM.Uninformative ∧
    (∀ j a, teacherPM.w j a ≤ teacherPM.w j (chooseSignal j)) ∧
    teacherPM.termI chooseSignal 2 = 3 / 10 ∧
    teacherPM.termPi chooseSignal chooseSignal = 0 ∧
    0 < teacherPM.termI chooseSignal 2 ∧
    ∃ j, ¬ ∀ a, teacherPM.w j a ≤ teacherPM.w j 2 := by
  obtain ⟨_, hv, hp⟩ := teacherPM_values
  have htil : ∀ j a, teacherPM.w j a ≤ teacherPM.w j (chooseSignal j) := by
    intro j a; rw [teacher_w, teacher_w]; cases j <;> fin_cases a <;> simp [chooseSignal] <;> norm_num
  have hI : teacherPM.termI chooseSignal 2 = 3 / 10 := by
    simp only [ProductModel.termI, Fintype.sum_bool, teacher_w, hp, chooseSignal]; simp; norm_num
  refine ⟨teacher_uninformative, htil, hI, ?_, by rw [hI]; norm_num, ?_⟩
  · simp only [ProductModel.termPi, Fintype.sum_bool, teacher_w, hv, hp, chooseSignal]; simp
  · refine ⟨true, fun h => ?_⟩
    have := h 0
    rw [teacher_w, teacher_w] at this
    simp at this <;> norm_num at this


/-! ## F11: `(I) = 0` without `w_j = v_K` — the weak teacher -/

/-- The weak teacher: the same keep side, `σ` and utility as `teacherPM`, but
`P(F = j ∣ C_j) = 11/20`: the signal is informative about `F` yet too weak to move the agent off
the safe act (`11/20 < 3/5`). The §2.5 parametrization at `r = 11/20 < s = 3/5`.
Source: [[value-change-as-epistemic-update]] §1.4 (the first route: "so (I) = 0 and `w_j = v_K`");
findings F11; audit r4 fidelity N3
Kind: D
Fidelity: n/a -/
def weakTeacherPM : ProductModel Bool Bool (Fin 3) where
  q := fun f c => match c with
    | none => 1 / 4
    | some j => if f = j then 11 / 80 else 9 / 80
  q_nonneg := fun f c => by cases c <;> dsimp only <;> (try split_ifs) <;> norm_num
  q_sum := by norm_num [Fintype.sum_bool, Fintype.sum_option]
  σ := fun _ => 1 / 3
  σ_pos := fun _ => by norm_num
  σ_sum := by norm_num [Fin.sum_univ_three]
  Uf := fun f _ a => baseU f a
  qK_pos := by norm_num [Fintype.sum_bool]
  qC_pos := fun j => by cases j <;> simp [Fintype.sum_bool] <;> norm_num

/-- The weak teacher's informed keep-values: `(11/20, 9/20, 3/5)` on `A`, `(9/20, 11/20, 3/5)` on `B`.
Source: [[value-change-as-epistemic-update]] §1.4; findings F11
Kind: L
Fidelity: exact -/
theorem weakTeacher_w (j : Bool) (a : Fin 3) :
    weakTeacherPM.w j a =
      ![if j then 11 / 20 else 9 / 20, if j then 9 / 20 else 11 / 20, 3 / 5] a := by
  cases j <;> fin_cases a <;>
    simp [ProductModel.w, ProductModel.qC, weakTeacherPM, baseU, Fintype.sum_bool] <;> norm_num

/-- The weak teacher's `v_K = (1/2, 1/2, 3/5)` (the same as the teacher's).
Source: [[value-change-as-epistemic-update]] §1.4; findings F11
Kind: L
Fidelity: exact -/
theorem weakTeacher_vKf (a : Fin 3) : weakTeacherPM.vKf a = ![1 / 2, 1 / 2, 3 / 5] a := by
  fin_cases a <;>
    simp [ProductModel.vKf, ProductModel.qK, weakTeacherPM, baseU, Fintype.sum_bool] <;> norm_num

/-- The weak teacher satisfies the uninformative-choice assumption (so it is a product model to
which `info_payment_split` applies).
Source: [[value-change-as-epistemic-update]] §1.4; findings F11
Kind: L
Fidelity: exact -/
theorem weakTeacher_uninformative : weakTeacherPM.Uninformative := by
  intro f
  cases f <;>
    simp [ProductModel.qK, ProductModel.qCtot, ProductModel.qC, weakTeacherPM, Fintype.sum_bool] <;>
    norm_num

/-- **F11's converse counterexample: `(I) = 0` does not mean the outcomes reveal nothing.** For the
weak teacher the safe act `a₃` maximizes every `w_j` and `v_K`, so `(I) = 0` with `ã^j = a^K = a₃`
(the full hypothesis package of `termI_nonneg`/`termI_pos_iff`), yet `w_A ≠ v_K`
(`w_A(a₁) = 11/20 ≠ 1/2`) and the outcomes are informative about the facts
(`q(A, C_A) · P(K) = 11/160 ≠ 10/160 = q(A, K) · P(C_A)`: the hypothesis of
`w_eq_vKf_of_uninformative_outcomes` fails). So "intrinsic" (`w_j = v_K`) is strictly stronger than
`(I) = 0`, as F11 says; the middle case is a change that reveals facts, changes no informed act, and
pays.
Source: [[value-change-as-epistemic-update]] §1.4 (the first route); findings F11; audit r4
fidelity N3
Kind: N+ (refutation of the converse)
Fidelity: exact -/
theorem termI_zero_not_intrinsic :
    weakTeacherPM.Uninformative ∧
    (∀ j a, weakTeacherPM.w j a ≤ weakTeacherPM.w j 2) ∧
    (∀ a, weakTeacherPM.vKf a ≤ weakTeacherPM.vKf 2) ∧
    weakTeacherPM.termI (fun _ => 2) 2 = 0 ∧
    weakTeacherPM.w true ≠ weakTeacherPM.vKf ∧
    ¬ (∀ j f, weakTeacherPM.q f (some j) * weakTeacherPM.qK =
        weakTeacherPM.q f none * weakTeacherPM.qC j) := by
  have htil : ∀ j a, weakTeacherPM.w j a ≤ weakTeacherPM.w j 2 := by
    intro j a; rw [weakTeacher_w, weakTeacher_w]; cases j <;> fin_cases a <;> simp <;> norm_num
  have hK : ∀ a, weakTeacherPM.vKf a ≤ weakTeacherPM.vKf 2 := by
    intro a; rw [weakTeacher_vKf, weakTeacher_vKf]; fin_cases a <;> simp <;> norm_num
  refine ⟨weakTeacher_uninformative, htil, hK, ?_, ?_, ?_⟩
  · simp [ProductModel.termI]
  · intro h
    have := congrFun h 0
    rw [weakTeacher_w, weakTeacher_vKf] at this
    norm_num at this
  · intro h
    have := h true true
    simp [weakTeacherPM, ProductModel.qK, ProductModel.qC, Fintype.sum_bool] at this
    norm_num at this

end

end Cleanroom.Corrigibility.CorrValueChange
