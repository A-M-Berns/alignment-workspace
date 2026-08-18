/-
# The enforcement inequality

The algebra under a distinguished trader compiled from a row presentation of an
admissible region.

A region is a finite family of rows `⟪c i, ·⟫ ≥ r i`.  At a displayed price `p`
the row violations are `g i = max 0 (r i - ⟪c i, p⟫)`, and the compiler's
position is the violation-weighted combination of the row normals,

    ζ k = ∑ i, β i * g i * c i k.

Two inequalities carry the round's conformance and safety claims, and the second
contains the first.  For any point `x`,

    ⟪ζ, x - p⟫ ≥ ∑ i, β i * (g i)^2 - ∑ i, β i * g i * d i,

where `d i = max 0 (r i - ⟪c i, x⟫)` is how far row `i` excludes `x`.  When the
region contains `x` every deficit is zero and the second sum drops, which is the
form the conformance results use.  When it does not, the deficits are exactly the
liability, and a date costs the trader something only where a live violation and
an excluded point meet on one row.

Logical Induction is **not** formalized here.  The market maker's contract enters
as a hypothesis — a bound on the aggregate position's value at a region point —
which is where an external result belongs (`AGENTS.md` standard 4).  Whether
Logical Induction's market maker delivers that hypothesis is argued in the
round's `SOURCE_AUDIT.md` and is not a theorem of this file.

All names are provisional (`AGENTS.md` standard 6).
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Workspace.Normativity.Contrib.TraderizedEnforcement

open Finset

variable {ι κ : Type*}
variable {rows : Finset ι} {coords : Finset κ}
variable {c : ι → κ → ℚ} {r β : ι → ℚ} {p x τ : κ → ℚ} {ε M : ℚ}

/-- The pairing a priced fragment carries: a finite sum over the priced
sentences.  A price vector and a world restricted to the fragment are both fed
to it, which is what lets one inequality speak about both. -/
def pair (coords : Finset κ) (u v : κ → ℚ) : ℚ := ∑ k ∈ coords, u k * v k

/-- The row violation at a price: zero exactly when the row holds. -/
def violation (coords : Finset κ) (c : κ → ℚ) (r : ℚ) (p : κ → ℚ) : ℚ :=
  max 0 (r - pair coords c p)

/-- The realised position of the trader compiled from the row family. -/
def position (rows : Finset ι) (coords : Finset κ) (c : ι → κ → ℚ) (r β : ι → ℚ)
    (p : κ → ℚ) : κ → ℚ :=
  fun k => ∑ i ∈ rows, β i * violation coords (c i) (r i) p * c i k

theorem violation_nonneg (coords : Finset κ) (c : κ → ℚ) (r : ℚ) (p : κ → ℚ) :
    0 ≤ violation coords c r p := le_max_left _ _

theorem le_pair_of_violation_eq_zero {coords : Finset κ} {c : κ → ℚ} {r : ℚ}
    {p : κ → ℚ} (h : violation coords c r p = 0) : r ≤ pair coords c p := by
  have := le_max_right 0 (r - pair coords c p)
  rw [← violation, h] at this
  linarith

/-- The violation multiplied by the signed row gap is its own square.  This is
the step that makes the violation's two roles — the scalar in the position, and
the slack a region point clears — the same number. -/
theorem violation_mul_gap (coords : Finset κ) (c : κ → ℚ) (r : ℚ) (p : κ → ℚ) :
    violation coords c r p * (r - pair coords c p) = violation coords c r p ^ 2 := by
  unfold violation
  rcases le_or_gt 0 (r - pair coords c p) with h | h
  · rw [max_eq_right h]; ring
  · rw [max_eq_left h.le]; ring

theorem pair_sub (coords : Finset κ) (u v w : κ → ℚ) :
    pair coords u (fun k => v k - w k) = pair coords u v - pair coords u w := by
  unfold pair
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem pair_add_left (coords : Finset κ) (u v w : κ → ℚ) :
    pair coords (fun k => u k + v k) w = pair coords u w + pair coords v w := by
  unfold pair
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The position's value against a displacement, resolved row by row. -/
theorem pair_position (d : κ → ℚ) :
    pair coords (position rows coords c r β p) d
      = ∑ i ∈ rows, β i * violation coords (c i) (r i) p * pair coords (c i) d := by
  unfold pair position
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **The enforcement inequality.**  Against any point the region contains, the
compiled position is worth at least the intensity-weighted squared violation.

No hypothesis about the market, the ordinary traders, or the funding appears:
this is a fact about the position and the price alone. -/
theorem weighted_square_le_pair
    (hβ : ∀ i ∈ rows, 0 ≤ β i)
    (hx : ∀ i ∈ rows, r i ≤ pair coords (c i) x) :
    ∑ i ∈ rows, β i * violation coords (c i) (r i) p ^ 2
      ≤ pair coords (position rows coords c r β p) (fun k => x k - p k) := by
  rw [pair_position]
  refine Finset.sum_le_sum fun i hi => ?_
  have hgnn := violation_nonneg coords (c i) (r i) p
  have hgap : r i - pair coords (c i) p
      ≤ pair coords (c i) (fun k => x k - p k) := by
    rw [pair_sub]; linarith [hx i hi]
  have hstep : violation coords (c i) (r i) p ^ 2
      ≤ violation coords (c i) (r i) p * pair coords (c i) (fun k => x k - p k) := by
    rw [← violation_mul_gap coords (c i) (r i) p]
    exact mul_le_mul_of_nonneg_left hgap hgnn
  calc β i * violation coords (c i) (r i) p ^ 2
      ≤ β i * (violation coords (c i) (r i) p
              * pair coords (c i) (fun k => x k - p k)) :=
        mul_le_mul_of_nonneg_left hstep (hβ i hi)
    _ = β i * violation coords (c i) (r i) p
          * pair coords (c i) (fun k => x k - p k) := by ring

/-- How far a row's right-hand side excludes a point.  Zero on every row exactly
when the region contains it. -/
def deficit (coords : Finset κ) (c : κ → ℚ) (r : ℚ) (x : κ → ℚ) : ℚ :=
  max 0 (r - pair coords c x)

theorem deficit_nonneg (coords : Finset κ) (c : κ → ℚ) (r : ℚ) (x : κ → ℚ) :
    0 ≤ deficit coords c r x := le_max_left _ _

theorem sub_deficit_le_pair (coords : Finset κ) (c : κ → ℚ) (r : ℚ) (x : κ → ℚ) :
    r - deficit coords c r x ≤ pair coords c x := by
  have := le_max_right 0 (r - pair coords c x)
  rw [← deficit] at this
  linarith

/-- **The liability bound.**  Against a point the region need *not* contain, the
compiled position is worth at least the intensity-weighted squared violation less
the violation-weighted deficits.

Two factors, and a date costs the enforcement trader something only where both
are present on one row: a live violation, and a right-hand side that excludes the
point.  Setting every deficit to zero recovers `pair_nonneg_of_mem`. -/
theorem weighted_square_sub_deficit_le_pair
    (hβ : ∀ i ∈ rows, 0 ≤ β i) :
    (∑ i ∈ rows, β i * violation coords (c i) (r i) p ^ 2)
      - (∑ i ∈ rows, β i * violation coords (c i) (r i) p
            * deficit coords (c i) (r i) x)
      ≤ pair coords (position rows coords c r β p) (fun k => x k - p k) := by
  rw [pair_position, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hgnn := violation_nonneg coords (c i) (r i) p
  have hgap : r i - deficit coords (c i) (r i) x - pair coords (c i) p
      ≤ pair coords (c i) (fun k => x k - p k) := by
    rw [pair_sub]; linarith [sub_deficit_le_pair coords (c i) (r i) x]
  have hstep : violation coords (c i) (r i) p ^ 2
        - violation coords (c i) (r i) p * deficit coords (c i) (r i) x
      ≤ violation coords (c i) (r i) p * pair coords (c i) (fun k => x k - p k) := by
    have := mul_le_mul_of_nonneg_left hgap hgnn
    nlinarith [violation_mul_gap coords (c i) (r i) p]
  have := mul_le_mul_of_nonneg_left hstep (hβ i hi)
  nlinarith [hβ i hi]

/-- **Plausible value is nonnegative.**  In any world the region contains, the
enforcement position is worth at least nothing — the enforcement trader is not
subsidised there, whatever the ordinary traders did. -/
theorem pair_nonneg_of_mem
    (hβ : ∀ i ∈ rows, 0 ≤ β i)
    (hx : ∀ i ∈ rows, r i ≤ pair coords (c i) x) :
    0 ≤ pair coords (position rows coords c r β p) (fun k => x k - p k) := by
  refine le_trans ?_ (weighted_square_le_pair hβ hx)
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (hβ i hi) (sq_nonneg _)

/-- **Enforcement under slack.**  The market maker's contract on the aggregate,
plus a bound on how far the ordinary aggregate can move against a region point,
bounds every row violation at once. -/
theorem weighted_square_le_slack_add_volume
    (hβ : ∀ i ∈ rows, 0 ≤ β i)
    (hx : ∀ i ∈ rows, r i ≤ pair coords (c i) x)
    (hcontract : pair coords
        (fun k => position rows coords c r β p k + τ k) (fun k => x k - p k) ≤ ε)
    (hτ : -M ≤ pair coords τ (fun k => x k - p k)) :
    ∑ i ∈ rows, β i * violation coords (c i) (r i) p ^ 2 ≤ ε + M := by
  rw [pair_add_left] at hcontract
  have := weighted_square_le_pair (p := p) (x := x) hβ hx
  linarith

/-- **Exact enforcement.**  At slack zero with no opposing volume, every row is
satisfied at the displayed price — for every positive intensity, including
arbitrarily small ones.  Intensity buys precision under slack, not exactness. -/
theorem le_pair_of_contract_zero
    (hβ : ∀ i ∈ rows, 0 < β i)
    (hx : ∀ i ∈ rows, r i ≤ pair coords (c i) x)
    (hcontract :
      pair coords (position rows coords c r β p) (fun k => x k - p k) ≤ 0) :
    ∀ i ∈ rows, r i ≤ pair coords (c i) p := by
  have hnn : ∀ j ∈ rows, 0 ≤ β j * violation coords (c j) (r j) p ^ 2 :=
    fun j hj => mul_nonneg (hβ j hj).le (sq_nonneg _)
  have hsum : ∑ i ∈ rows, β i * violation coords (c i) (r i) p ^ 2 ≤ 0 :=
    le_trans (weighted_square_le_pair (fun i hi => (hβ i hi).le) hx) hcontract
  intro i hi
  have hterm : β i * violation coords (c i) (r i) p ^ 2 = 0 := by
    have hle := Finset.single_le_sum hnn hi
    have := hnn i hi
    linarith
  have hgnn := violation_nonneg coords (c i) (r i) p
  have hb := hβ i hi
  refine le_pair_of_violation_eq_zero (le_antisymm ?_ hgnn)
  rcases mul_eq_zero.mp hterm with h | h
  · exact absurd h hb.ne'
  · nlinarith [hgnn, h]

/-- Inhabitation: one row, one priced sentence, a violated price, and a region
point.  The inequality holds with equality here, so the bound is attained and
the hypothesis package is satisfiable rather than empty. -/
theorem enforcement_inequality_is_nonvacuous :
    ∃ (rows coords : Finset ℕ) (c : ℕ → ℕ → ℚ) (r β p x : ℕ → ℚ),
      (∀ i ∈ rows, 0 ≤ β i) ∧
      (∀ i ∈ rows, r i ≤ pair coords (c i) x) ∧
      (∑ i ∈ rows, β i * violation coords (c i) (r i) p ^ 2 = 1 / 16) ∧
      pair coords (position rows coords c r β p) (fun k => x k - p k) = 1 / 16 ∧
      ¬ (r 0 ≤ pair coords (c 0) p) := by
  refine ⟨{0}, {0}, fun _ _ => 1, fun _ => 1 / 2, fun _ => 1, fun _ => 1 / 4,
          fun _ => 1 / 2, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [pair, position, violation] <;> norm_num

/-- Inhabitation for the liability bound at a **nonzero** deficit, so it is not
witnessed only in the case where it reduces to the previous theorem.  One row,
one priced sentence, a violated price and an excluded point; the bound is an
equality and its value is negative, which is what a liability is. -/
theorem liability_bound_is_nonvacuous :
    ∃ (rows coords : Finset ℕ) (c : ℕ → ℕ → ℚ) (r β p x : ℕ → ℚ),
      (∀ i ∈ rows, 0 ≤ β i) ∧
      (∑ i ∈ rows, β i * violation coords (c i) (r i) p ^ 2 = 1 / 16) ∧
      (∑ i ∈ rows, β i * violation coords (c i) (r i) p
          * deficit coords (c i) (r i) x = 1 / 8) ∧
      pair coords (position rows coords c r β p) (fun k => x k - p k) = -(1 / 16) ∧
      ¬ (r 0 ≤ pair coords (c 0) x) := by
  refine ⟨{0}, {0}, fun _ _ => 1, fun _ => 1 / 2, fun _ => 1, fun _ => 1 / 4,
          fun _ => 0, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [pair, position, violation, deficit] <;> norm_num

end Workspace.Normativity.Contrib.TraderizedEnforcement

#print axioms Workspace.Normativity.Contrib.TraderizedEnforcement.weighted_square_le_pair
#print axioms Workspace.Normativity.Contrib.TraderizedEnforcement.pair_nonneg_of_mem
#print axioms Workspace.Normativity.Contrib.TraderizedEnforcement.weighted_square_sub_deficit_le_pair
#print axioms Workspace.Normativity.Contrib.TraderizedEnforcement.weighted_square_le_slack_add_volume
#print axioms Workspace.Normativity.Contrib.TraderizedEnforcement.le_pair_of_contract_zero
#print axioms Workspace.Normativity.Contrib.TraderizedEnforcement.enforcement_inequality_is_nonvacuous
#print axioms Workspace.Normativity.Contrib.TraderizedEnforcement.liability_bound_is_nonvacuous
