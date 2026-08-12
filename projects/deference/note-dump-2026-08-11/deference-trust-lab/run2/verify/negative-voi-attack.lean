/-
  negative-voi-attack.lean  —  FAITHFULNESS GATE attack on run2/lean/negative-voi.lean
  (independent skeptic; success = finding fakeness).

  The headline `negative_VoI : Value E1 < Value E2` has NO hypotheses — it is a closed ℚ
  computation over CONCRETE definitions (π, O, E1, E2, recOpt). So the classic
  hypothesis-LAUNDERING pattern (assume the hard object as a hypothesis) is structurally
  IMPOSSIBLE here: there is no hypothesis to delete. The real attack surface is shadow-test
  (a): is `recOpt` honestly the argmax-of-own-posterior, or is it a hand-tuned constant that
  returns the cherry-picked answer? And is the strict gap genuinely caused by E2's
  non-partitionality (not a payoff artifact)?

  This file re-derives the load-bearing facts INDEPENDENTLY of the author's lemmas, and runs:
    (A1) recOpt is genuinely DATA-DRIVEN: an ADVERSARIAL menu (option 1 dominates everywhere)
         makes the SAME recOpt rule return 1 at every world — so recOpt is NOT a constant.
    (A2) recOpt is genuinely MENU-DRIVEN the other way: a menu where option 0 dominates makes
         recOpt return 0 everywhere.
    (A3) The per-world choices the author claims (recOpt E1 = [1,0,1], E2 = [1,0,0], Q=[1,0,1])
         are FORCED by the argmax rule — re-proved here from scratch via `decide` on the
         Bool-level comparison, NOT by trusting the author's `recOpt_E*` lemmas.
    (A4) ADVERSARIAL NEAR-MISS: `Value E1 < Value Q` is FALSE (4/9 < 4/9). So replacing the
         non-partitional E2 by the partitional anchor Q DESTROYS the strict gap — the gap
         genuinely tracks non-partitionality, not the payoffs. (anti shadow-(c))
    (A5) CONCLUSION-TRIVIALITY: try to get `Value E1 < Value E2` to hold when E2 is REFINED to
         a partition (= Q): it does NOT (`¬ (Value E1 < Value Q)`). The inequality is not a
         tautology of the menu.
    (A6) The SPEC preconditions are real and decide-checked: both S4, E2 non-partitional,
         E1 refines E2, AND E1≠E2 (the comparison is non-degenerate / not the same expert).

  Everything is finite ℚ over Fin 3, copied verbatim from the original so the kernel re-checks
  the SAME objects. No LI/martingale/asymptotic object appears.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Finset

namespace NegativeVoIAttack

abbrev W := Fin 3
abbrev Info := W → W → Bool

def π : W → ℚ := fun _ => 1/3

-- The ORIGINAL menu (verbatim).
def O : Fin 2 → W → ℚ
  | 0, 0 => 0   | 0, 1 => 2/3 | 0, 2 => 1/3
  | 1, 0 => 2/3 | 1, 1 => 0   | 1, 2 => 0

def E1 : Info
  | 0, u => decide (u = 0)
  | 1, u => decide (u = 1)
  | 2, u => decide (u = 0 ∨ u = 2)
def E2 : Info
  | 0, u => decide (u = 0)
  | 1, u => decide (u = 1)
  | 2, _ => true
def Q : Info
  | 0, u => decide (u = 0 ∨ u = 2)
  | 1, u => decide (u = 1)
  | 2, u => decide (u = 0 ∨ u = 2)

-- recOpt parameterized by the menu, so we can swap in adversarial menus (the rule is IDENTICAL).
def condNumM (M : Fin 2 → W → ℚ) (E : Info) (j : Fin 2) (w : W) : ℚ :=
  ∑ u : W, (if E w u then π u * M j u else 0)
def recOptM (M : Fin 2 → W → ℚ) (E : Info) (w : W) : Fin 2 :=
  if condNumM M E 1 w > condNumM M E 0 w then 1 else 0
def recPayoffM (M : Fin 2 → W → ℚ) (E : Info) (w : W) : ℚ := M (recOptM M E w) w
def ValueM (M : Fin 2 → W → ℚ) (E : Info) : ℚ := ∑ w : W, π w * recPayoffM M E w

-- Bind the original menu back: these MUST equal the author's Value E1, etc.
abbrev Value (E : Info) : ℚ := ValueM O E
abbrev recOpt (E : Info) (w : W) : Fin 2 := recOptM O E w

theorem condNumM_eval (M : Fin 2 → W → ℚ) (E : Info) (j : Fin 2) (w : W) :
    condNumM M E j w
      = (if E w 0 then π 0 * M j 0 else 0)
      + (if E w 1 then π 1 * M j 1 else 0)
      + (if E w 2 then π 2 * M j 2 else 0) := by
  simp only [condNumM, Fin.sum_univ_three]

/-! ### (A6) SPEC preconditions are real (re-decided here, not trusted). -/

abbrev Reflexive (E : Info) : Prop := ∀ w, E w w = true
abbrev Transitive (E : Info) : Prop := ∀ w v u, E w v = true → E v u = true → E w u = true
abbrev Nested (E : Info) : Prop :=
  ∀ w v, (∀ u, ¬ (E w u = true ∧ E v u = true))
         ∨ (∀ u, E w u = true → E v u = true)
         ∨ (∀ u, E v u = true → E w u = true)
abbrev S4 (E : Info) : Prop := Reflexive E ∧ Transitive E ∧ Nested E
abbrev Euclidean (E : Info) : Prop := ∀ w v u, E w v = true → E w u = true → E v u = true
abbrev Partitional (E : Info) : Prop := S4 E ∧ Euclidean E
abbrev Refines (Ea Eb : Info) : Prop := ∀ w u, Ea w u = true → Eb w u = true

theorem A6_E1_S4 : S4 E1 := by decide
theorem A6_E2_S4 : S4 E2 := by decide
theorem A6_Q_S4  : S4 Q  := by decide
theorem A6_E2_not_partitional : ¬ Partitional E2 := by decide
theorem A6_Q_partitional : Partitional Q := by decide
theorem A6_E1_refines_E2 : Refines E1 E2 := by decide
theorem A6_E1_refines_Q  : Refines E1 Q  := by decide
-- NON-DEGENERATE: E1 and E2 are genuinely different experts (the comparison isn't E vs itself).
theorem A6_E1_ne_E2 : E1 ≠ E2 := by
  intro h; have := congrFun (congrFun h 2) 1; simp [E1, E2] at this

/-! ### (A3) The per-world recommended choices are FORCED by the argmax rule.
     Proved from scratch (unfold recOpt+condNum on the ORIGINAL menu). If the author had
     hand-tuned recOpt to a constant, these would not all be re-derivable. -/

theorem A3_recOpt_E1 : recOpt E1 0 = 1 ∧ recOpt E1 1 = 0 ∧ recOpt E1 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp only [recOpt, recOptM, condNumM_eval]; simp [E1, O, π] <;> norm_num)
theorem A3_recOpt_E2 : recOpt E2 0 = 1 ∧ recOpt E2 1 = 0 ∧ recOpt E2 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp only [recOpt, recOptM, condNumM_eval]; simp [E2, O, π] <;> norm_num)
theorem A3_recOpt_Q : recOpt Q 0 = 1 ∧ recOpt Q 1 = 0 ∧ recOpt Q 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp only [recOpt, recOptM, condNumM_eval]; simp [Q, O, π] <;> norm_num)

/-! ### (A1)/(A2) recOpt is genuinely DATA-DRIVEN, not a constant returning the answer.
     Swap the ORIGINAL menu for adversarial menus; the SAME rule must respond. -/

-- Menu where option 1 strictly dominates option 0 everywhere.  The SAME recOpt rule, fed this
-- adversarial menu, must return 1 at EVERY world for EVERY expert E1/E2/Q — proving recOpt
-- responds to the menu (it is not a constant returning the cherry-picked answer).
def MdomOne : Fin 2 → W → ℚ
  | 0, _ => 0
  | 1, _ => 1
theorem A1_E1_all_one : recOptM MdomOne E1 0 = 1 ∧ recOptM MdomOne E1 1 = 1 ∧ recOptM MdomOne E1 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp only [recOptM, condNumM_eval]; simp [E1, MdomOne, π] <;> norm_num)
theorem A1_E2_all_one : recOptM MdomOne E2 0 = 1 ∧ recOptM MdomOne E2 1 = 1 ∧ recOptM MdomOne E2 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp only [recOptM, condNumM_eval]; simp [E2, MdomOne, π] <;> norm_num)
-- Menu where option 0 strictly dominates: the SAME rule returns 0 everywhere.
def MdomZero : Fin 2 → W → ℚ
  | 0, _ => 1
  | 1, _ => 0
theorem A2_E1_all_zero : recOptM MdomZero E1 0 = 0 ∧ recOptM MdomZero E1 1 = 0 ∧ recOptM MdomZero E1 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp only [recOptM, condNumM_eval]; simp [E1, MdomZero, π] <;> norm_num)
theorem A2_E2_all_zero : recOptM MdomZero E2 0 = 0 ∧ recOptM MdomZero E2 1 = 0 ∧ recOptM MdomZero E2 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp only [recOptM, condNumM_eval]; simp [E2, MdomZero, π] <;> norm_num)

/-! ### Values on the ORIGINAL menu — recomputed via the parameterized rule. -/

theorem A_Value_E1 : Value E1 = 4/9 := by
  simp only [Value, ValueM, recPayoffM, Fin.sum_univ_three,
    show recOptM O E1 0 = 1 from A3_recOpt_E1.1,
    show recOptM O E1 1 = 0 from A3_recOpt_E1.2.1,
    show recOptM O E1 2 = 1 from A3_recOpt_E1.2.2, O, π]
  norm_num
theorem A_Value_E2 : Value E2 = 5/9 := by
  simp only [Value, ValueM, recPayoffM, Fin.sum_univ_three,
    show recOptM O E2 0 = 1 from A3_recOpt_E2.1,
    show recOptM O E2 1 = 0 from A3_recOpt_E2.2.1,
    show recOptM O E2 2 = 0 from A3_recOpt_E2.2.2, O, π]
  norm_num
theorem A_Value_Q : Value Q = 4/9 := by
  simp only [Value, ValueM, recPayoffM, Fin.sum_univ_three,
    show recOptM O Q 0 = 1 from A3_recOpt_Q.1,
    show recOptM O Q 1 = 0 from A3_recOpt_Q.2.1,
    show recOptM O Q 2 = 1 from A3_recOpt_Q.2.2, O, π]
  norm_num

-- The headline reproduced INDEPENDENTLY (same objects, our own parameterized machinery).
theorem A_negative_VoI : Value E1 < Value E2 := by rw [A_Value_E1, A_Value_E2]; norm_num

/-! ### (A4)/(A5) ADVERSARIAL NEAR-MISS / CONCLUSION-TRIVIALITY.
     With E2 replaced by the PARTITIONAL anchor Q, the strict gap is GONE.
     `Value E1 < Value Q` is FALSE — so the inequality is NOT a payoff tautology; it requires
     the coarser expert to be the non-partitional E2. -/

theorem A4_partitional_destroys_gap : ¬ (Value E1 < Value Q) := by
  rw [A_Value_E1, A_Value_Q]; norm_num
-- And the partitional anchor is strictly beaten by the non-partitional E2 on the SAME menu.
theorem A4_nonpartitional_beats_partition : Value Q < Value E2 := by
  rw [A_Value_Q, A_Value_E2]; norm_num

end NegativeVoIAttack

#print axioms NegativeVoIAttack.A6_E1_S4
#print axioms NegativeVoIAttack.A6_E2_not_partitional
#print axioms NegativeVoIAttack.A6_Q_partitional
#print axioms NegativeVoIAttack.A6_E1_refines_E2
#print axioms NegativeVoIAttack.A6_E1_ne_E2
#print axioms NegativeVoIAttack.A3_recOpt_E1
#print axioms NegativeVoIAttack.A3_recOpt_E2
#print axioms NegativeVoIAttack.A3_recOpt_Q
#print axioms NegativeVoIAttack.A1_E1_all_one
#print axioms NegativeVoIAttack.A1_E2_all_one
#print axioms NegativeVoIAttack.A2_E1_all_zero
#print axioms NegativeVoIAttack.A2_E2_all_zero
#print axioms NegativeVoIAttack.A_negative_VoI
#print axioms NegativeVoIAttack.A4_partitional_destroys_gap
#print axioms NegativeVoIAttack.A4_nonpartitional_beats_partition
