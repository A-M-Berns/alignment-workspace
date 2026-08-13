/-
# The surgical repair bound

The bridge between an online-learning regret guarantee and a statement about how
often a learner puts mass on one targeted response.

A **surgical** modification rule is the identity except on one source action, so
the regret it accrues is a single sum of per-occasion terms

    q i * d i

where `q i` is the mixed mass on the targeted response at selected occasion `i`
and `d i` is the loss gap the repair buys there.  Nothing cancels, and a uniform
positive margin turns the regret into a bound on the mass.

Blum--Mansour's regret theorem is **not** reproved here.  It enters as the
hypothesis `hR`, which is where an external online-learning result belongs
(`AGENTS.md` standard 4).  Nothing about a replayed comparator trajectory appears:
every quantity is read off the occasions that actually happened.

All names are provisional (`AGENTS.md` standard 6).
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Workspace.Leverage.Contrib.SurgicalRepairBound

open Finset

variable {ι : Type*} {s : Finset ι} {q d : ι → ℚ} {δ B M : ℚ}

/-- The surgical lower bound: regret is at least the margin times the mass.

`q i` is nonnegative mixed mass, `d i` the gap at occasion `i`, and `δ` a uniform
lower bound on the gap over the selected occasions. -/
theorem margin_mul_mass_le_regret
    (hq : ∀ i ∈ s, 0 ≤ q i) (hd : ∀ i ∈ s, δ ≤ d i) :
    δ * ∑ i ∈ s, q i ≤ ∑ i ∈ s, q i * d i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i hi
  calc δ * q i = q i * δ := by ring
    _ ≤ q i * d i := mul_le_mul_of_nonneg_left (hd i hi) (hq i hi)

/-- With a regret upper bound `B`, the mass on the targeted response is at most
`B / δ`.  This is the finite-horizon crown-jewel inequality. -/
theorem mass_le_regret_div_margin
    (hδ : 0 < δ) (hq : ∀ i ∈ s, 0 ≤ q i) (hd : ∀ i ∈ s, δ ≤ d i)
    (hR : ∑ i ∈ s, q i * d i ≤ B) :
    ∑ i ∈ s, q i ≤ B / δ := by
  have h : δ * ∑ i ∈ s, q i ≤ B :=
    le_trans (margin_mul_mass_le_regret hq hd) hR
  rw [le_div_iff₀ hδ]
  linarith

/-- The conditional rate.  Dividing by the number of occasions on which the
reason was due is what makes the statement about *responding to a reason* rather
than about the whole horizon. -/
theorem rate_le_bound_div_margin_mul_exposure
    (hδ : 0 < δ) (hM : 0 < M)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hd : ∀ i ∈ s, δ ≤ d i)
    (hR : ∑ i ∈ s, q i * d i ≤ B) :
    (∑ i ∈ s, q i) / M ≤ B / (δ * M) := by
  have hQ : ∑ i ∈ s, q i ≤ B / δ := mass_le_regret_div_margin hδ hq hd hR
  have hsplit : B / (δ * M) = (B / δ) / M := by
    field_simp
  rw [hsplit]
  gcongr

/-- A nonpositive margin licenses no bound at all: the hypothesis `0 < δ` in the
results above is doing work, and dropping it leaves the conclusion false.

Witness: one occasion, full mass on the targeted response, and a gap of `-1`.
Regret is `-1`, which `B = 0` bounds, while `B / δ = 0` and the mass is `1`. -/
theorem margin_positivity_is_necessary :
    ∃ (q d : Unit → ℚ) (B : ℚ),
      (∀ i ∈ (univ : Finset Unit), 0 ≤ q i) ∧
      (∑ i ∈ (univ : Finset Unit), q i * d i ≤ B) ∧
      ¬ (∑ i ∈ (univ : Finset Unit), q i ≤ B / (-1 : ℚ)) := by
  refine ⟨fun _ => 1, fun _ => -1, 0, ?_, ?_, ?_⟩
  · intro i _; norm_num
  · norm_num
  · norm_num

/-- Inhabitation: the hypotheses of `mass_le_regret_div_margin` are satisfiable,
so the theorem is not empty.  One occasion, mass `1/2`, gap `1/2`, margin `1/2`,
regret bound `1/4`. -/
theorem mass_bound_is_nonvacuous :
    ∃ (q d : Unit → ℚ) (δ B : ℚ),
      0 < δ ∧
      (∀ i ∈ (univ : Finset Unit), 0 ≤ q i) ∧
      (∀ i ∈ (univ : Finset Unit), δ ≤ d i) ∧
      (∑ i ∈ (univ : Finset Unit), q i * d i ≤ B) ∧
      (∑ i ∈ (univ : Finset Unit), q i ≤ B / δ) := by
  refine ⟨fun _ => 1/2, fun _ => 1/2, 1/2, 1/4, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro i _; norm_num
  · intro i _; norm_num
  · norm_num
  · norm_num

end Workspace.Leverage.Contrib.SurgicalRepairBound

#print axioms Workspace.Leverage.Contrib.SurgicalRepairBound.margin_mul_mass_le_regret
#print axioms Workspace.Leverage.Contrib.SurgicalRepairBound.mass_le_regret_div_margin
#print axioms Workspace.Leverage.Contrib.SurgicalRepairBound.rate_le_bound_div_margin_mul_exposure
#print axioms Workspace.Leverage.Contrib.SurgicalRepairBound.margin_positivity_is_necessary
#print axioms Workspace.Leverage.Contrib.SurgicalRepairBound.mass_bound_is_nonvacuous
