import Cleanroom.Corrigibility.CorrGeneralObject.Bridge

/-!
# corr-general-object — Example A (the shared witness carrier)

Example A of `general-object-final.md` (P12): three worlds `θ₁, θ₂, θ₃`, prior
`P = (1/2, 1/4, 1/4)`, three plans with `V(plan_k, θ_j) = 10` if `k = j` else `−2`, target
`Q = (1/5, 3/5, 1/5)`. Prior expected values `(4, 1, 1)` (`a^P = plan₁`), target expected values
`(2/5, 26/5, 2/5)` (`a^Q = plan₂`). The kernels used across the package:

| name | kernel | role |
|---|---|---|
| `exA_k1` | `(1/6, 1, 1/3)` | endorsing (`postPush = Q`, push mass `5/12`) — S1(a), S4(c) |
| `exA_k2` | `(1/10, 3/5, 1/10)` | comply; `postPush = (2/9, 2/3, 1/9) ≠ Q`; `R = 0`, `VOI = 6/5` |
| `exA_k3` | `(1/2, 3/5, 1/2)` | do not comply; `R = 6/5`, `VOI = 0` |
| `exA_k5` | `(1/10, 1/10, 3/5)` | CE5: `R = 3/10 = 3/2 − 6/5` |
| `exA_k6` | `(0, 1/2, 1)` | `R = 0` without decision-local trust (`VOI = 3`) |
| `exA_k7` | `(0, 1, 0)` | procurement value `3` |

Everything here is a definition or an exact-rational fact (`norm_num`); the theorems that use
them are in the topic files.

Source: [[general-object-final]] P12 (Example A), P2, P8, CE1, CE5, (E).
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

noncomputable section

/-- Example A's prior `P = (1/2, 1/4, 1/4)`. Source: [[general-object-final]] P12. Kind: D. Fidelity: exact -/
def exA_P : Distr (Fin 3) where
  mass := ![1/2, 1/4, 1/4]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_three]; norm_num

/-- Example A's target `Q = (1/5, 3/5, 1/5)`. Source: [[general-object-final]] P12. Kind: D. Fidelity: exact -/
def exA_Q : Distr (Fin 3) where
  mass := ![1/5, 3/5, 1/5]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_three]; norm_num

/-- Example A's payoffs: `plan_k` is worth `10` in `θ_k` and `−2` elsewhere (row = plan).
Source: [[general-object-final]] P12. Kind: D. Fidelity: exact -/
def exA_V : Fin 3 → Fin 3 → ℝ := ![![10, -2, -2], ![-2, 10, -2], ![-2, -2, 10]]

/-- The endorsing kernel `(1/6, 1, 1/3)`. Source: [[general-object-final]] P2. Kind: D. Fidelity: exact -/
def exA_k1 : Fin 3 → ℝ := ![1/6, 1, 1/3]

/-- The complying kernel `(1/10, 3/5, 1/10)`. Source: [[general-object-final]] P12. Kind: D. Fidelity: exact -/
def exA_k2 : Fin 3 → ℝ := ![1/10, 3/5, 1/10]

/-- The non-complying kernel `(1/2, 3/5, 1/2)`. Source: [[general-object-final]] P12. Kind: D. Fidelity: exact -/
def exA_k3 : Fin 3 → ℝ := ![1/2, 3/5, 1/2]

/-- CE5's kernel `(1/10, 1/10, 3/5)`. Source: [[general-object-final]] CE5, P8. Kind: D. Fidelity: exact -/
def exA_k5 : Fin 3 → ℝ := ![1/10, 1/10, 3/5]

/-- The mandate's converse-failure kernel `(0, 1/2, 1)`. Source: mandate T6(c). Kind: D. Fidelity: exact -/
def exA_k6 : Fin 3 → ℝ := ![0, 1/2, 1]

/-- The procurement kernel `(0, 1, 0)` (this package's choice for T18(c)). Source: mandate T18(c). Kind: D. Fidelity: exact -/
def exA_k7 : Fin 3 → ℝ := ![0, 1, 0]

/-- Every Example A kernel is a kernel. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem exA_kernels : IsKernel exA_k1 ∧ IsKernel exA_k2 ∧ IsKernel exA_k3 ∧ IsKernel exA_k5 ∧
    IsKernel exA_k6 ∧ IsKernel exA_k7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro ω <;> fin_cases ω <;>
    norm_num [exA_k1, exA_k2, exA_k3, exA_k5, exA_k6, exA_k7]

/-- Example A's prior plan is `plan₁` (prior values `(4, 1, 1)`) and its target plan is `plan₂`
(target values `(2/5, 26/5, 2/5)`). Source: [[general-object-final]] P12. Kind: N+. Fidelity: exact -/
theorem exA_plans : IsOptimal exA_P exA_V 0 ∧ IsOptimal exA_Q exA_V 1 ∧
    expect exA_P (exA_V 0) = 4 ∧ expect exA_Q (exA_V 1) = 26/5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b; fin_cases b <;> simp [expect, exA_P, exA_V, Fin.sum_univ_three] <;> norm_num
  · intro b; fin_cases b <;> simp [expect, exA_Q, exA_V, Fin.sum_univ_three] <;> norm_num
  · simp [expect, exA_P, exA_V, Fin.sum_univ_three]; norm_num
  · simp [expect, exA_Q, exA_V, Fin.sum_univ_three]; norm_num

/-- The push masses of the Example A kernels. Source: [[general-object-final]] P2, P8, P11. Kind: L. Fidelity: exact -/
theorem exA_pushMass : pushMass exA_P exA_k1 = 5/12 ∧ pushMass exA_P exA_k2 = 9/40 ∧
    pushMass exA_P exA_k3 = 21/40 ∧ pushMass exA_P exA_k5 = 9/40 ∧ pushMass exA_P exA_k6 = 3/8 ∧
    pushMass exA_P exA_k7 = 1/4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [pushMass, exA_P, exA_k1, exA_k2, exA_k3, exA_k5, exA_k6, exA_k7, Fin.sum_univ_three] <;>
    norm_num

/-- **S1(a), the N+ pair for `Endorsed`**: the same target `Q` is endorsed under `k₁ = (1/6, 1, 1/3)`
(`postPush = Q`) and not under `k₂ = (1/10, 3/5, 1/10)`, where the coherent agent lands at
`(2/9, 2/3, 1/9) ≠ Q`.
Source: [[general-object-final]] S1(a), S4(c), P2, script (B)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exA_endorsed_pair :
    Endorsed exA_P exA_k1 exA_Q ∧ ¬ Endorsed exA_P exA_k2 exA_Q ∧
      (postPush exA_P exA_k2 exA_kernels.2.1.nonneg (by rw [exA_pushMass.2.1]; norm_num)).mass =
        ![2/9, 2/3, 1/9] := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω; rw [exA_pushMass.1]; fin_cases ω <;> simp [exA_P, exA_k1, exA_Q] <;> norm_num
  · intro h
    have := h 1
    rw [exA_pushMass.2.1] at this
    simp [exA_P, exA_k2, exA_Q] at this
    norm_num at this
  · funext ω
    rw [postPush_mass, exA_pushMass.2.1]
    fin_cases ω <;> simp [exA_P, exA_k2] <;> norm_num

end

end Cleanroom.Corrigibility.CorrGeneralObject
