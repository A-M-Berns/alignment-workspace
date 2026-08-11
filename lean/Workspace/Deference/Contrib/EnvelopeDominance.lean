/-
# The later-measurable envelope dominates, and what that does and does not show

Source: `projects/deference/notes/FUD_COMPARATOR_SPEC.md` v1 and
`prompts/2026-08-11-stage-iii-fud/REPORT.md`, over `FINITE_MODEL_SKELETON.md` v2.

Two cell-measurable selections at one decision index, over a partition `cell : Ω → C`
standing for the later information. `φ` maximises the conditional value on each cell;
`δ` is arbitrary. `envelopeGap` is the difference in the current agent's valuation.

Finite, exact-rational, order-and-arithmetic only. No Logical Induction fact appears,
and nothing is asserted as an `axiom`.

**What this file is not.** It was written for a fully-updated-deference comparison and
does **not** deliver one. `φ` is built from the evaluating agent's own credence and own
objective, so it is computable at the earlier time: it is the optimal later-measurable
plan — the *envelope* — and not a distinct future agent. The round's report records this
as the round's central defect. Accordingly:

- `envelope_dominates` is `∑ maxima ≥ ∑ anything`. It carries **no** fairness
  hypothesis, and its content is exhausted by `φ` being a per-cell maximiser. It is
  **not** evidence that transferring authority is safe or attractive.
- `envelopeGap_eq_regret` is distributivity of subtraction over a finite sum. No weight
  may be placed on which terms are absent from it: the model carries no execution layer,
  no null effect and no authorization relation, so their absence from the identity is a
  property of the signature rather than a finding.
- `agreement_gap_zero` is one directional. Its converse is **false**; the report carries
  an exact counterexample in which the two selections disagree, the principal is
  strictly decisive, and the gap is nonetheless zero.

Provisional names (`AGENTS.md` §6): `cellValue`, `cellMass`, `envelopeGap`,
`IsCellMaximiser`, `envelope_dominates`, `envelopeGap_eq_regret`, `agreement_gap_zero`,
`cell_regret_le_of_calibrated`, `gap_le_of_gated_calibration`.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Workspace.Deference.Contrib.EnvelopeDominance

open Finset

variable {Ω C P : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype C] [DecidableEq C]
  [DecidableEq P]

/-- `W(c, π)`, the mass-weighted conditional value of `π` on cell `c`. Carried
unnormalised: it has the same maximisers as the conditional expectation whenever the
cell has positive mass, and it keeps the whole development division-free. -/
def cellValue (p : Ω → ℚ) (X : Ω → P → ℚ) (cell : Ω → C) (c : C) (π : P) : ℚ :=
  ∑ ω, if cell ω = c then p ω * X ω π else 0

/-- The credence mass of a cell. -/
def cellMass (p : Ω → ℚ) (cell : Ω → C) (c : C) : ℚ :=
  ∑ ω, if cell ω = c then p ω else 0

theorem cellMass_nonneg {p : Ω → ℚ} {cell : Ω → C} (hp : ∀ ω, 0 ≤ p ω) (c : C) :
    0 ≤ cellMass p cell c := by
  refine Finset.sum_nonneg fun ω _ => ?_
  by_cases h : cell ω = c <;> simp [h, hp ω]

/-- The current agent's valuation of a cell-measurable selection. -/
def valuation (p : Ω → ℚ) (X : Ω → P → ℚ) (cell : Ω → C) (sel : C → P) : ℚ :=
  ∑ c, cellValue p X cell c (sel c)

/-- `φ` maximises conditional value on every cell. Note this is a property of `φ`
relative to the *evaluator's* own `p` and `X`, which is why `φ` is computable before the
information arrives. -/
def IsCellMaximiser (p : Ω → ℚ) (X : Ω → P → ℚ) (cell : Ω → C) (φ : C → P) : Prop :=
  ∀ c π, cellValue p X cell c π ≤ cellValue p X cell c (φ c)

/-- The gap between the envelope and an arbitrary cell-measurable selection. -/
def envelopeGap (p : Ω → ℚ) (X : Ω → P → ℚ) (cell : Ω → C) (φ δ : C → P) : ℚ :=
  valuation p X cell φ - valuation p X cell δ

/-! ## The state-level and cell-level valuations agree -/

/-- Evaluating a cell-measurable selection state by state is the same as evaluating it
cell by cell. This is what licenses working in the cell register throughout. -/
theorem valuation_eq_sum_states (p : Ω → ℚ) (X : Ω → P → ℚ) (cell : Ω → C)
    (sel : C → P) :
    valuation p X cell sel = ∑ ω, p ω * X ω (sel (cell ω)) := by
  classical
  simp only [valuation, cellValue]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp [Finset.sum_ite_eq]

/-! ## Dominance and the regret identity -/

/-- **The envelope dominates.** A per-cell maximiser is weakly better than any
cell-measurable selection, in the valuation whose conditional maxima define it.

The single hypothesis is `hφ`. There is no fairness condition here and none is needed:
the statement is `∑ maxima ≥ ∑ anything`. Read as a claim about authority it would be
vacuous, and the file header says why. -/
theorem envelope_dominates {p : Ω → ℚ} {X : Ω → P → ℚ} {cell : Ω → C} {φ δ : C → P}
    (hφ : IsCellMaximiser p X cell φ) :
    0 ≤ envelopeGap p X cell φ δ := by
  have : ∀ c ∈ (univ : Finset C),
      cellValue p X cell c (δ c) ≤ cellValue p X cell c (φ c) := fun c _ => hφ c (δ c)
  have h := Finset.sum_le_sum this
  simp only [envelopeGap, valuation]
  linarith

/-- **The regret decomposition.** Distributivity of subtraction over a finite sum. -/
theorem envelopeGap_eq_regret (p : Ω → ℚ) (X : Ω → P → ℚ) (cell : Ω → C) (φ δ : C → P) :
    envelopeGap p X cell φ δ
      = ∑ c, (cellValue p X cell c (φ c) - cellValue p X cell c (δ c)) := by
  simp [envelopeGap, valuation, Finset.sum_sub_distrib]

/-- **Agreement gives a zero gap.** One direction only; the converse is false. -/
theorem agreement_gap_zero (p : Ω → ℚ) (X : Ω → P → ℚ) (cell : Ω → C) (φ δ : C → P)
    (h : ∀ c, δ c = φ c) :
    envelopeGap p X cell φ δ = 0 := by
  rw [envelopeGap_eq_regret]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [h c, sub_self]

/-! ## The competence bound, and where its leakage enters -/

/-- On a cell where the selector's grades are calibrated to the conditional value
within `η` — in mass-weighted form, so no division occurs — and where `δ` maximises
those grades, the per-cell regret is at most `2η` times the cell mass.

The calibration hypothesis compares grades to a **conditional expectation**, so the
evaluator's credence occurs in it. Under `FINITE_MODEL_SKELETON.md` v2 §2a it is a
*joint competence–credence* hypothesis, not a competence hypothesis. -/
theorem cell_regret_le_of_calibrated {p : Ω → ℚ} {X : Ω → P → ℚ} {cell : Ω → C}
    {v : C → P → ℚ} {φ δ : C → P} {η : ℚ} {c : C}
    (hp : ∀ ω, 0 ≤ p ω)
    (hcal : ∀ π, |v c π * cellMass p cell c - cellValue p X cell c π|
              ≤ η * cellMass p cell c)
    (hδ : ∀ π, v c π ≤ v c (δ c)) :
    cellValue p X cell c (φ c) - cellValue p X cell c (δ c)
      ≤ 2 * η * cellMass p cell c := by
  have h1 := (abs_le.mp (hcal (φ c))).1
  have h2 := (abs_le.mp (hcal (δ c))).2
  have h4 : v c (φ c) * cellMass p cell c ≤ v c (δ c) * cellMass p cell c :=
    mul_le_mul_of_nonneg_right (hδ (φ c)) (cellMass_nonneg hp c)
  linarith

/-- Off the gate the regret is bounded by the quantity bound: `2B` times the cell mass. -/
theorem cell_regret_le_of_bounded {p : Ω → ℚ} {X : Ω → P → ℚ} {cell : Ω → C}
    {φ δ : C → P} {B : ℚ} {c : C}
    (hp : ∀ ω, 0 ≤ p ω) (hX : ∀ ω π, |X ω π| ≤ B) :
    cellValue p X cell c (φ c) - cellValue p X cell c (δ c)
      ≤ 2 * B * cellMass p cell c := by
  have key : ∀ π, cellValue p X cell c π ≤ B * cellMass p cell c := by
    intro π
    rw [cellValue, cellMass, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω _ => ?_
    by_cases h : cell ω = c
    · rw [if_pos h, if_pos h]
      nlinarith [mul_le_mul_of_nonneg_left (abs_le.mp (hX ω π)).2 (hp ω)]
    · simp [h]
  have key' : ∀ π, -(B * cellMass p cell c) ≤ cellValue p X cell c π := by
    intro π
    rw [cellValue, cellMass, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun ω _ => ?_
    by_cases h : cell ω = c
    · rw [if_pos h, if_pos h]
      nlinarith [mul_le_mul_of_nonneg_left (abs_le.mp (hX ω π)).1 (hp ω)]
    · simp [h]
  linarith [key (φ c), key' (δ c)]

/-- **The gated bound.** Splitting the cells by a gate, the gap is at most `2η` on the
gated mass plus `2B` on the rest.

The second summand is the leakage, and nothing here bounds it: with the gate nowhere
open the bound degrades to `2B`, which every gap satisfies unconditionally. The round's
harness reports how often the bound is informative at all. -/
theorem gap_le_of_gated_calibration
    {p : Ω → ℚ} {X : Ω → P → ℚ} {cell : Ω → C} {v : C → P → ℚ} {φ δ : C → P}
    {η B : ℚ} (gate : C → Prop) [DecidablePred gate]
    (hp : ∀ ω, 0 ≤ p ω) (hX : ∀ ω π, |X ω π| ≤ B)
    (hcal : ∀ c, gate c → ∀ π,
      |v c π * cellMass p cell c - cellValue p X cell c π| ≤ η * cellMass p cell c)
    (hδ : ∀ c π, v c π ≤ v c (δ c)) :
    envelopeGap p X cell φ δ
      ≤ 2 * η * (∑ c ∈ univ.filter gate, cellMass p cell c)
        + 2 * B * (∑ c ∈ univ.filter (fun c => ¬ gate c), cellMass p cell c) := by
  classical
  rw [envelopeGap_eq_regret, ← Finset.sum_filter_add_sum_filter_not univ gate]
  have h1 : ∑ c ∈ univ.filter gate,
        (cellValue p X cell c (φ c) - cellValue p X cell c (δ c))
      ≤ ∑ c ∈ univ.filter gate, 2 * η * cellMass p cell c :=
    Finset.sum_le_sum fun c hc =>
      cell_regret_le_of_calibrated hp (hcal c (Finset.mem_filter.mp hc).2) (fun π => hδ c π)
  have h2 : ∑ c ∈ univ.filter (fun c => ¬ gate c),
        (cellValue p X cell c (φ c) - cellValue p X cell c (δ c))
      ≤ ∑ c ∈ univ.filter (fun c => ¬ gate c), 2 * B * cellMass p cell c :=
    Finset.sum_le_sum fun c _ => cell_regret_le_of_bounded hp hX
  rw [Finset.mul_sum, Finset.mul_sum]
  linarith

/-! ## The worked case — inhabitation witnesses

Four states, two interventions, two cells, `B = 1`, uniform credence. The grades `v`
are calibrated at `η = 2` on both cells and are *inverted* on cell `0`, so `δ ≠ φ`
there: the instance inhabits the gated bound's full hypothesis package without
collapsing to the degenerate case `δ = φ`.
-/

namespace WorkedCase

abbrev St := Fin 4
abbrev Act := Fin 2
abbrev Cell := Fin 2

def p : St → ℚ := ![1/4, 1/4, 1/4, 1/4]
def X : St → Act → ℚ := ![![1, -1], ![1, -1], ![-1, 1], ![-1, 1]]
def cell : St → Cell := ![0, 0, 1, 1]
def phi : Cell → Act := ![0, 1]
def v : Cell → Act → ℚ := ![![-1, 1], ![-1, 1]]
def delta : Cell → Act := ![1, 1]

theorem p_nonneg : ∀ ω, 0 ≤ p ω := by
  intro ω; fin_cases ω <;> norm_num [p]

theorem X_bounded : ∀ ω π, |X ω π| ≤ 1 := by
  intro ω π; fin_cases ω <;> fin_cases π <;> norm_num [X, abs_le]

theorem phi_maximiser : IsCellMaximiser p X cell phi := by
  intro c π
  fin_cases c <;> fin_cases π <;>
    norm_num [cellValue, phi, p, X, cell, Fin.sum_univ_succ]

/-- `δ` maximises the grades, as the gated bound requires. -/
theorem delta_grade_maximal : ∀ c π, v c π ≤ v c (delta c) := by
  intro c π; fin_cases c <;> fin_cases π <;> norm_num [v, delta]

/-- The grades are calibrated at `η = 2` on every cell — the gate is everywhere open. -/
theorem calibrated : ∀ c : Cell, True → ∀ π,
    |v c π * cellMass p cell c - cellValue p X cell c π| ≤ 2 * cellMass p cell c := by
  intro c _ π
  fin_cases c <;> fin_cases π <;>
    norm_num [cellValue, cellMass, v, p, X, cell, Fin.sum_univ_succ, abs_le]

/-- The instance is not degenerate: the two selections disagree on cell `0`. -/
theorem selections_disagree : delta 0 ≠ phi 0 := by decide

theorem gap_eq : envelopeGap p X cell phi delta = 1 := by
  norm_num [envelopeGap, valuation, cellValue, phi, delta, p, X, cell,
    Fin.sum_univ_succ]

/-- Nonvacuity for `envelope_dominates`, at a non-degenerate instance. -/
theorem envelope_dominates_nonvacuous : 0 < envelopeGap p X cell phi delta := by
  rw [gap_eq]; norm_num

/-- Nonvacuity for `gap_le_of_gated_calibration`: the full hypothesis package is
inhabited, with `δ ≠ φ`, and the bound is satisfied strictly. -/
theorem gap_le_of_gated_calibration_nonvacuous :
    envelopeGap p X cell phi delta
      ≤ 2 * 2 * (∑ c ∈ univ.filter (fun _ : Cell => True), cellMass p cell c)
        + 2 * 1 * (∑ c ∈ univ.filter (fun _ : Cell => ¬ True), cellMass p cell c) :=
  gap_le_of_gated_calibration (fun _ => True) p_nonneg X_bounded calibrated
    delta_grade_maximal

end WorkedCase

#print axioms valuation_eq_sum_states
#print axioms envelope_dominates
#print axioms envelopeGap_eq_regret
#print axioms agreement_gap_zero
#print axioms cellMass_nonneg
#print axioms cell_regret_le_of_calibrated
#print axioms cell_regret_le_of_bounded
#print axioms gap_le_of_gated_calibration
#print axioms WorkedCase.p_nonneg
#print axioms WorkedCase.X_bounded
#print axioms WorkedCase.phi_maximiser
#print axioms WorkedCase.delta_grade_maximal
#print axioms WorkedCase.calibrated
#print axioms WorkedCase.selections_disagree
#print axioms WorkedCase.gap_eq
#print axioms WorkedCase.envelope_dominates_nonvacuous
#print axioms WorkedCase.gap_le_of_gated_calibration_nonvacuous

end Workspace.Deference.Contrib.EnvelopeDominance
