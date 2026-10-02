import Cleanroom.Udt.UdtEndorsePolicy.Transitive
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# T6(b): conditional endorsement is not transitive — the eight-point frame

Coordinates `(x, t, y) ∈ {0,1}³` indexed as `ω = 4x + 2t + y ∈ Fin 8`, weights out of `32`:
`(0,0,0) ↦ 9, (0,0,1) ↦ 3, (0,1,0) ↦ 3, (0,1,1) ↦ 1, (1,0,0) ↦ 1, (1,0,1) ↦ 3, (1,1,0) ↦ 3,
(1,1,1) ↦ 9`. Target `X = {x = 1} = {4, 5, 6, 7}`. Reports:

* `Vj = P(X | t)`: `3/4` on `t = 1`, `1/4` on `t = 0`;
* `Vk = x ⊕ y` (`0/1`-valued; independent of `x` given `t` by construction);
* `Vi = P(X | t, y)`: `9/10, 1/2, 1/2, 1/10` on `(t, y) = (1,1), (1,0), (0,1), (0,0)`.

Then `Vi` is endorsed given `Vj` (each `(Vj, Vi)` pair is one `(t, y)` cell), `Vj` is endorsed
given `Vk`, but `Vi` is not endorsed given `Vk`: `P(X | Vk = 0, Vi = 9/10) = 1 ≠ 9/10`. All three
reports are non-constant (scout Q4's non-vacuity certificate), and the same frame has
`Vi ≻ Vj ≻ Vk` with `¬ (Vi ≻ Vk)`. The mandate writer's hand computation is confirmed here
(every positive pair checked, not a sample: the point form quantifies over all eight points).
-/

namespace Cleanroom.Udt.UdtEndorsePolicy

open Cleanroom.Udt.UdtPolicyCalc Finset

noncomputable section

/-- The weights of the eight-point frame (out of `32`).
Source: mandate T6(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def w8 : Fin 8 → ℝ := ![9 / 32, 3 / 32, 3 / 32, 1 / 32, 1 / 32, 3 / 32, 3 / 32, 9 / 32]

/-- The target event `X = {x = 1} = {4, 5, 6, 7}`.
Source: mandate T6(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def X8 : Finset (Fin 8) := {4, 5, 6, 7}

/-- `Vi = P(X | t, y)`.
Source: mandate T6(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Vi8 : Fin 8 → ℝ := ![1 / 10, 1 / 2, 1 / 2, 9 / 10, 1 / 10, 1 / 2, 1 / 2, 9 / 10]

/-- `Vj = P(X | t)`.
Source: mandate T6(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Vj8 : Fin 8 → ℝ := ![1 / 4, 1 / 4, 3 / 4, 3 / 4, 1 / 4, 1 / 4, 3 / 4, 3 / 4]

/-- `Vk = x ⊕ y`.
Source: mandate T6(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Vk8 : Fin 8 → ℝ := ![0, 1, 0, 1, 1, 0, 1, 0]

/-- The three reports as a family indexed by `Fin 3` (`0 = i`, `1 = j`, `2 = k`).
Source: mandate T6(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def V8 : Fin 3 → Fin 8 → ℝ := ![Vi8, Vj8, Vk8]

/-- Supporting lemma `w8_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem w8_pos (ω : Fin 8) : 0 < w8 ω := by
  fin_cases ω <;> norm_num [w8]

/-- Supporting lemma `w8_nonneg`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem w8_nonneg (ω : Fin 8) : 0 ≤ w8 ω := (w8_pos ω).le

/-- **`Vi` is endorsed given `Vj`** (all eight points, i.e. all four positive `(Vj, Vi)` cells).
Source: mandate T6(b)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem condR_i_j : CondR w8 X8 V8 0 1 := by
  show CondBeliefEndorses w8 X8 Vj8 Vi8
  rw [condBeliefEndorses_iff_forall_pt w8_nonneg]
  intro ω _
  rw [mass_inter_event_eq, mass_event_eq, Fin.sum_univ_eight, Fin.sum_univ_eight]
  fin_cases ω <;>
  · simp +decide only [w8, Vi8, Vj8, Matrix.cons_val, Fin.isValue]
    norm_num

/-- **`Vj` is endorsed given `Vk`** (all eight points, i.e. all four positive `(Vk, Vj)` cells:
`x ⊕ y` is independent of `x` given `t`).
Source: mandate T6(b)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem condR_j_k : CondR w8 X8 V8 1 2 := by
  show CondBeliefEndorses w8 X8 Vk8 Vj8
  rw [condBeliefEndorses_iff_forall_pt w8_nonneg]
  intro ω _
  rw [mass_inter_event_eq, mass_event_eq, Fin.sum_univ_eight, Fin.sum_univ_eight]
  fin_cases ω <;>
  · simp +decide only [w8, Vj8, Vk8, Matrix.cons_val, Fin.isValue]
    norm_num

/-- **`Vi` is not endorsed given `Vk`**: `P(X | Vk = 0, Vi = 9/10) = 1 ≠ 9/10` (the cell is the
single point `(1, 1, 1)`).
Source: mandate T6(b)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem not_condR_i_k : ¬ CondR w8 X8 V8 0 2 := by
  intro h
  have h1 := (condBeliefEndorses_iff_forall_pt w8_nonneg _ _ _).1 h 7 (w8_pos 7)
  rw [mass_inter_event_eq, mass_event_eq, Fin.sum_univ_eight, Fin.sum_univ_eight] at h1
  simp +decide only [V8, w8, Vi8, Vk8, Matrix.cons_val, Fin.isValue] at h1
  norm_num at h1

/-- **`Vj` is not endorsed given `Vi`**: `P(X | Vi = 9/10, Vj = 3/4) = 9/10 ≠ 3/4`.
Source: mandate T6(b)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem not_condR_j_i : ¬ CondR w8 X8 V8 1 0 := by
  intro h
  have h1 := (condBeliefEndorses_iff_forall_pt w8_nonneg _ _ _).1 h 7 (w8_pos 7)
  rw [mass_inter_event_eq, mass_event_eq, Fin.sum_univ_eight, Fin.sum_univ_eight] at h1
  simp +decide only [V8, w8, Vi8, Vj8, Matrix.cons_val, Fin.isValue] at h1
  norm_num at h1

/-- **`Vk` is not endorsed given `Vj`**: `P(X | Vj = 3/4, Vk = 0) = 3/4 ≠ 0`.
Source: mandate T6(b)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem not_condR_k_j : ¬ CondR w8 X8 V8 2 1 := by
  intro h
  have h1 := (condBeliefEndorses_iff_forall_pt w8_nonneg _ _ _).1 h 7 (w8_pos 7)
  rw [mass_inter_event_eq, mass_event_eq, Fin.sum_univ_eight, Fin.sum_univ_eight] at h1
  simp +decide only [V8, w8, Vj8, Vk8, Matrix.cons_val, Fin.isValue] at h1
  norm_num at h1

/-- **All three reports are non-constant** (scout Q4's non-vacuity certificate).
Source: scout Q4 | mandate T6(b)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem V8_nonconstant : ∀ i : Fin 3, ∃ ω ω' : Fin 8, V8 i ω ≠ V8 i ω' := by
  intro i
  fin_cases i
  · exact ⟨0, 1, by norm_num [V8, Vi8]⟩
  · exact ⟨0, 2, by norm_num [V8, Vj8, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]⟩
  · exact ⟨0, 1, by norm_num [V8, Vk8]⟩

/-- **T6(b): conditional endorsement is not transitive** (N+, `refuted`): on the eight-point
frame, `Vi` is endorsed given `Vj` and `Vj` is endorsed given `Vk`, but `Vi` is not endorsed
given `Vk`; all three reports are non-constant. (i) The refuted sentence: M&A Q1 "Is it
transitive?" read as the conjecture that endorsed-given is transitive; (ii) reading: belief
form, `CondR i j := P(X | V j = x, V i = y) = y` on positive pairs (ATTRIBUTION-UNVETTED);
(iii) survivors: `condEndorse_acyclic` (no cycles) and `strictOrder_of_closure` (the transitive
closure of strict trust is a strict partial order).
Source: [[meaning-and-agency-reference]] §Conditional Endorsement, Q1 | udt-rep-2-015 | trust-lab-070 / scout Q4
Kind: N+
Fidelity: n/a (every positive pair checked by the point form; three non-constant reports; positive weights)
Hyps: none -/
theorem condEndorse_not_transitive :
    CondR w8 X8 V8 0 1 ∧ CondR w8 X8 V8 1 2 ∧ ¬ CondR w8 X8 V8 0 2 :=
  ⟨condR_i_j, condR_j_k, not_condR_i_k⟩

/-- **`Prec` ("strictly more trusted") is not transitive, hence not a strict partial order**:
`Vi ≻ Vj`, `Vj ≻ Vk`, `¬ (Vi ≻ Vk)` on the eight-point frame.
Source: [[meaning-and-agency-reference]] §Conditional Endorsement ("we can (partially) order different random variables") | udt-rep-2-015
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem prec_not_transitive :
    Prec w8 X8 V8 0 1 ∧ Prec w8 X8 V8 1 2 ∧ ¬ Prec w8 X8 V8 0 2 :=
  ⟨⟨condR_i_j, not_condR_j_i⟩, ⟨condR_j_k, not_condR_k_j⟩, fun h => not_condR_i_k h.1⟩

/-- **T2(d)(iii), converse fails**: unconditional endorsement does not imply conditional
endorsement given an arbitrary `V` — `Vi` is belief-endorsed (from `condR_i_j`) but not endorsed
given `Vk`, which is informative about `X` beyond `Vi`.
Source: [[meaning-and-agency-reference]] §Conditional Endorsement | udt-rep-2-015(c) (mandate T2(d)(iii))
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem beliefEndorses_not_condBeliefEndorses_witness :
    BeliefEndorses w8 X8 Vi8 ∧ ¬ CondBeliefEndorses w8 X8 Vk8 Vi8 :=
  ⟨beliefEndorses_of_condBeliefEndorses w8_nonneg condR_i_j, not_condR_i_k⟩

end

end Cleanroom.Udt.UdtEndorsePolicy
