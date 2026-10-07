import Cleanroom.Corrigibility.CorrValueChange.Variants
import Mathlib.Tactic.NormNum

/-!
Audit r4 (adversarial) probe for `corr-value-change`, T9(a) `act_value_good`.

`act_value_good` carries `hfac : V(i) = V(j) → a*_i = a*_j` ("the installed choice is a function of
the value vector"; the note's §2.7 says "since `a*` is a function of the vector", the ledger calls it
"the tie convention made a hypothesis"). This probe checks that the hypothesis is load-bearing, i.e.
that the theorem cannot be strengthened by dropping it: on the sharp joint (`P(θ, i) = ½[θ = i]`)
with the constant uniform installation and the betting utility, act-value reflection holds
(the vector is constant, `V_a ≡ 1/2`, so the one cell is all of `I` and reflection on it is
`E_P[U_a] = 1/2`), every act maximizes every installed vector (ties), `a^K = true` is `P`-optimal,
and the anti-choice `a*_i = !i` — a legitimate installed maximizer at each outcome, but not a function
of the (constant) vector — gives `Val(accept) = 0 < 1/2 = Val(decline)`. So without `hfac` the
conclusion is false. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

/-- The anti-choice: after signal `i`, bet on `!i`. -/
def antiStar : Bool → Bool := fun i => !i

theorem hf_Vvec (i a : Bool) : Vvec uniformInstalled uBet i a = 1 / 2 := by
  unfold Vvec EQ uniformInstalled installedOf Uplus uBet
  cases i <;> cases a <;> simp [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool] <;>
    norm_num

theorem hf_Vcell (i : Bool) : Vcell uniformInstalled uBet i = univ := by
  ext j
  simp only [Vcell, mem_filter, mem_univ, true_and, iff_true]
  funext a; rw [hf_Vvec, hf_Vvec]

theorem hf_S (a i : Bool) : S sharpJoint uBet a i = if i = a then 1 / 2 else 0 := by
  unfold S sharpJoint teacherJoint Uplus uBet
  cases i <;> cases a <;> simp [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool] <;>
    norm_num

theorem hf_π (i : Bool) : sharpJoint.π i = 1 / 2 := teacher_π 1 (by norm_num) (by norm_num) i

/-- Act-value reflection holds: the vector is constant, so the cell is `I` and the condition is
`E_P[U_a] = 1/2`. -/
theorem hf_actValueReflection : ActValueReflection sharpJoint uniformInstalled uBet := by
  intro a i
  rw [hf_Vcell, hf_Vvec, Fintype.sum_bool, Fintype.sum_bool, hf_S, hf_S, hf_π, hf_π]
  cases a <;> norm_num

/-- Every act maximizes the (constant) installed vector; in particular the anti-choice does. -/
theorem hf_hstar :
    ∀ i a, Vvec uniformInstalled uBet i a ≤ Vvec uniformInstalled uBet i (antiStar i) := by
  intro i a; rw [hf_Vvec, hf_Vvec]

theorem hf_EU (a : Bool) : EU sharpJoint uBet a = 1 / 2 := by
  unfold EU; rw [Fintype.sum_bool, hf_S, hf_S]; cases a <;> norm_num

theorem hf_hK : ∀ a, EU sharpJoint uBet a ≤ EU sharpJoint uBet true := by
  intro a; rw [hf_EU, hf_EU]

/-- The anti-choice is not a function of the vector: `V(true) = V(false)` but `!true ≠ !false`. -/
theorem hf_not_hfac :
    ¬ ∀ i j, Vvec uniformInstalled uBet i = Vvec uniformInstalled uBet j → antiStar i = antiStar j := by
  intro h
  have := h true false (by funext a; rw [hf_Vvec, hf_Vvec])
  simp [antiStar] at this

theorem hf_values :
    ValAccept sharpJoint uBet antiStar = 0 ∧ ValDecline sharpJoint uBet true = 1 / 2 := by
  constructor
  · unfold ValAccept; rw [Fintype.sum_bool, hf_S, hf_S]; simp [antiStar]
  · unfold ValDecline; exact hf_EU true

/-- **`hfac` is load-bearing**: every other hypothesis of `act_value_good` holds, `hfac` fails, and the
conclusion fails: `Val(accept) = 0 < 1/2 = Val(decline)`. -/
theorem probe_hfac_needed :
    ActValueReflection sharpJoint uniformInstalled uBet ∧
    (∀ i a, Vvec uniformInstalled uBet i a ≤ Vvec uniformInstalled uBet i (antiStar i)) ∧
    (∀ a, EU sharpJoint uBet a ≤ EU sharpJoint uBet true) ∧
    ¬ (∀ i j, Vvec uniformInstalled uBet i = Vvec uniformInstalled uBet j → antiStar i = antiStar j) ∧
    ValAccept sharpJoint uBet antiStar < ValDecline sharpJoint uBet true := by
  refine ⟨hf_actValueReflection, hf_hstar, hf_hK, hf_not_hfac, ?_⟩
  obtain ⟨h1, h2⟩ := hf_values
  rw [h1, h2]; norm_num

end

end Cleanroom.Corrigibility.CorrValueChange
