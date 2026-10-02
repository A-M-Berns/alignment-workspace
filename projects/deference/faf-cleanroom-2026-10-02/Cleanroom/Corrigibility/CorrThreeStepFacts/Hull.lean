import Cleanroom.Corrigibility.CorrThreeStepFacts.CommonPrior

/-!
# The hull condition: question-relative deference beyond screening-off (mm open problem 6)

Repair round 1's push on the natural next question after F-6. mm I9.5 proves that
*screening-off* (`ScreensOff`: within each programmers' cell the question is independent of the
agent's `y`) suffices for question-relative deference, and the `h3` frame (`WitnessesC`) shows
it is not necessary even for a live press. This file states the condition that the geometry of
the problem actually asks for, at the level of the *pressed unions* of cells.

**Setting.** For a question `qOf : W → Q`, each programmers' cell `h₀` has a *question vector*
`qVec h₀ : Q → ℝ`, `q ↦ P(h₀ ∩ q)`, and each joint cell `(h₀, y₀)` has `qVecY h₀ y₀`,
`q ↦ P(h₀ ∩ y₀ ∩ q)`. For a `Q`-measurable payoff `f`, the programmers press `h₀` iff
`⟨qVec h₀, f⟩ < 0` (`cellSumX_eq_qVec_dot`), and the agent's `y₀`-cell press sum is
`⟨∑_{h₀ pressed} qVecY h₀ y₀, f⟩` (`jointCellSum_eq_qVecY_dot` with the `y`-cell decomposition).

**The hull condition** (`HullCondition`): for every payoff `f` and every `y₀`, the pressed-union
vector `∑_{h₀ pressed} qVecY h₀ y₀` is a non-negative combination of the pressed cells'
question vectors *minus* a non-negative combination of the unpressed cells' question vectors.
Then `⟨v, f⟩ = ∑_{pressed} a ⟨qVec, f⟩ − ∑_{unpressed} b ⟨qVec, f⟩ ≤ 0` termwise
(`commonPriorRule_pressExpectOn_nonpos_of_hull`, proved). Screening-off is the special case
`a = P(h₀ ∩ y₀)/P(h₀)`, `b = 0` (`hullCondition_of_screensOff`, proved), and the `h3` frame
satisfies the hull condition without screening off (`WitnessesC.h3_hull`, N+).

**Necessity** (`hullCondition_of_defers`, OPEN): if deference holds for every `Q`-measurable
payoff, the hull condition holds. The argument is standard: fix `f` with pressed set `S`; for
`g` in the weak cone `K_S = {g : ⟨qVec h, g⟩ ≤ 0 (h ∈ S), ≥ 0 (h ∉ S)}` and `ε > 0`, `g + εf`
has pressed set exactly `S`, so deference gives `⟨v, g⟩ ≤ −ε⟨v, f⟩` for every `ε > 0`, hence
`⟨v, g⟩ ≤ 0` on all of `K_S`; Farkas' lemma for the finitely generated cone
`cone{qVec h (h ∈ S), −qVec h (h ∉ S)}` (whose dual is `K_S`) then gives the representation.
Mathlib has Farkas for proper (closed) cones in Hilbert spaces
(`ProperCone.hyperplane_separation'`) and the double dual of an H-cone
(`PointedCone.DualFG.dual_dual_flip`, `Mathlib.Geometry.Convex.Cone.DualFinite`), but not, as far
as this package found, Minkowski–Weyl (a finitely generated cone in `Q → ℝ` is an H-cone, hence
closed); the step is left open rather than proved here.

Together: **deference for every `Q`-measurable payoff ⟺ the hull condition** (⟸ proved, ⟹ open),
which is the "necessary-and-sufficient condition at the level of pressed unions of cells" F-6
asked for; this is presumably the finite-frame content of DDB's Theorem 4.1 hull test, which
this package did not read (ATTRIBUTION-UNVETTED).
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

section Hull

variable {W H Y Q : Type*} [Fintype W] [Fintype H] [DecidableEq H] [Fintype Y] [DecidableEq Y]
  [Fintype Q] [DecidableEq Q]
variable (P : Distr W) (hOf : W → H) (yOf : W → Y) (qOf : W → Q)

/-- The question vector of a programmers' cell: `q ↦ P(h₀ ∩ q)`.
Source: mm.md item 5 (I9.5) (the marginal of `q` on a cell `D`), derived here. Kind: D. Fidelity: exact -/
noncomputable def qVec (h₀ : H) : Q → ℝ :=
  fun q => ∑ w ∈ (cell hOf h₀).filter (qOf · = q), P.mass w

/-- The question vector of a joint cell: `q ↦ P(h₀ ∩ y₀ ∩ q)`.
Source: mm.md item 5 (I9.5) (the marginal of `q` on `C_A ∩ D`), derived here. Kind: D. Fidelity: exact -/
noncomputable def qVecY (h₀ : H) (y₀ : Y) : Q → ℝ :=
  fun q => ∑ w ∈ ((cell yOf y₀).filter (hOf · = h₀)).filter (qOf · = q), P.mass w

omit [Fintype H] in
/-- A `Q`-measurable payoff's cell sum is the inner product of the cell's question vector
with the payoff.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellSumX_eq_qVec_dot (f : Q → ℝ) (h₀ : H) :
    cellSumX P (f ∘ qOf) hOf h₀ = ∑ q, qVec P hOf qOf h₀ q * f q := by
  unfold cellSumX qVec
  rw [← sum_fiberwise_of_maps_to (s := cell hOf h₀) (t := univ) (g := qOf) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun q _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun w hw => ?_
  rw [mem_filter] at hw
  simp only [Function.comp, hw.2]

omit [Fintype H] [Fintype Y] in
/-- A `Q`-measurable payoff's joint cell sum is the inner product of the joint cell's question
vector with the payoff.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma jointCellSum_eq_qVecY_dot (f : Q → ℝ) (h₀ : H) (y₀ : Y) :
    jointCellSum P hOf yOf (f ∘ qOf) h₀ y₀ = ∑ q, qVecY P hOf yOf qOf h₀ y₀ q * f q := by
  unfold jointCellSum qVecY
  rw [← sum_fiberwise_of_maps_to (s := (cell yOf y₀).filter (hOf · = h₀)) (t := univ) (g := qOf)
    (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun q _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun w hw => ?_
  rw [mem_filter] at hw
  simp only [Function.comp, hw.2]

/-- **The hull condition.** For every `Q`-measurable payoff `f` and every agent cell `y₀`, the
pressed-union vector `∑_{h₀ pressed} qVecY h₀ y₀` is a non-negative combination of the pressed
cells' question vectors minus a non-negative combination of the unpressed cells' question
vectors (`h₀` is pressed iff `cellSumX (f ∘ qOf) h₀ < 0`). Screening-off is the case
`a = P(h₀ ∩ y₀)/P(h₀)`, `b = 0`.
Source: mm.md item 5 (I9.5), open problem 6 (l. 292); F-6 ("a condition at the level of the pressed unions of cells"); derived here
Kind: D
Fidelity: n/a (the condition is this package's; ATTRIBUTION-UNVETTED that it is DDB's Theorem 4.1 hull test on a finite frame) -/
def HullCondition : Prop :=
  ∀ (f : Q → ℝ) (y₀ : Y), ∃ a b : H → ℝ, (∀ h₀, 0 ≤ a h₀) ∧ (∀ h₀, 0 ≤ b h₀) ∧
    ∀ q, ∑ h₀ ∈ univ.filter (fun h₀ => cellSumX P (f ∘ qOf) hOf h₀ < 0), qVecY P hOf yOf qOf h₀ y₀ q =
      ∑ h₀ ∈ univ.filter (fun h₀ => cellSumX P (f ∘ qOf) hOf h₀ < 0), a h₀ * qVec P hOf qOf h₀ q -
        ∑ h₀ ∈ univ.filter (fun h₀ => ¬ cellSumX P (f ∘ qOf) hOf h₀ < 0), b h₀ * qVec P hOf qOf h₀ q

/-- **The hull condition suffices for question-relative deference.** Under `HullCondition`, for
every `Q`-measurable payoff `f = f' ∘ qOf` and every `y`-cell, the press-weighted sum under the
programmers' rule is `≤ 0`: it equals `∑_{pressed} a ⟨qVec, f⟩ − ∑_{unpressed} b ⟨qVec, f⟩`, and
each pressed inner product is `< 0`, each unpressed one `≥ 0`.
Source: mm.md item 5 (I9.5) (its proof, generalised from proportional to conic weights); F-6; derived here
Kind: P
Fidelity: stronger than mm I9.5 (screening-off implies the hypothesis, `hullCondition_of_screensOff`; `h3_hull` satisfies it without screening off)
Hyps: (a) only -/
theorem commonPriorRule_pressExpectOn_nonpos_of_hull (hH : HullCondition P hOf yOf qOf)
    (f : Q → ℝ) (y₀ : Y) :
    (commonPriorRule P hOf (f ∘ qOf)).pressExpectOn () (cell yOf y₀) (f ∘ qOf) ≤ 0 := by
  obtain ⟨a, b, ha, hb, hab⟩ := hH f y₀
  unfold commonPriorRule
  rw [pressExpectOn_yCell_decomp]
  have e1 : ∑ h₀, ruleVal P hOf (f ∘ qOf) h₀ * jointCellSum P hOf yOf (f ∘ qOf) h₀ y₀ =
      ∑ h₀ ∈ univ.filter (fun h₀ => cellSumX P (f ∘ qOf) hOf h₀ < 0),
        jointCellSum P hOf yOf (f ∘ qOf) h₀ y₀ := by
    rw [sum_filter]
    refine sum_congr rfl fun h₀ _ => ?_
    unfold ruleVal
    split_ifs <;> simp
  have e2 : ∑ h₀ ∈ univ.filter (fun h₀ => cellSumX P (f ∘ qOf) hOf h₀ < 0),
        jointCellSum P hOf yOf (f ∘ qOf) h₀ y₀ =
      ∑ q, (∑ h₀ ∈ univ.filter (fun h₀ => cellSumX P (f ∘ qOf) hOf h₀ < 0),
        qVecY P hOf yOf qOf h₀ y₀ q) * f q := by
    simp only [jointCellSum_eq_qVecY_dot, sum_mul]
    exact sum_comm
  have e3 : ∀ q, (∑ h₀ ∈ univ.filter (fun h₀ => cellSumX P (f ∘ qOf) hOf h₀ < 0),
        qVecY P hOf yOf qOf h₀ y₀ q) * f q =
      ∑ h₀ ∈ univ.filter (fun h₀ => cellSumX P (f ∘ qOf) hOf h₀ < 0),
          a h₀ * (qVec P hOf qOf h₀ q * f q) -
        ∑ h₀ ∈ univ.filter (fun h₀ => ¬ cellSumX P (f ∘ qOf) hOf h₀ < 0),
          b h₀ * (qVec P hOf qOf h₀ q * f q) := by
    intro q
    rw [hab q, sub_mul, sum_mul, sum_mul]
    congr 1 <;> exact sum_congr rfl fun _ _ => by ring
  have e4 : ∑ q, ∑ h₀ ∈ univ.filter (fun h₀ => cellSumX P (f ∘ qOf) hOf h₀ < 0),
        a h₀ * (qVec P hOf qOf h₀ q * f q) =
      ∑ h₀ ∈ univ.filter (fun h₀ => cellSumX P (f ∘ qOf) hOf h₀ < 0),
        a h₀ * cellSumX P (f ∘ qOf) hOf h₀ := by
    rw [sum_comm]
    refine sum_congr rfl fun h₀ _ => ?_
    rw [cellSumX_eq_qVec_dot, mul_sum]
  have e5 : ∑ q, ∑ h₀ ∈ univ.filter (fun h₀ => ¬ cellSumX P (f ∘ qOf) hOf h₀ < 0),
        b h₀ * (qVec P hOf qOf h₀ q * f q) =
      ∑ h₀ ∈ univ.filter (fun h₀ => ¬ cellSumX P (f ∘ qOf) hOf h₀ < 0),
        b h₀ * cellSumX P (f ∘ qOf) hOf h₀ := by
    rw [sum_comm]
    refine sum_congr rfl fun h₀ _ => ?_
    rw [cellSumX_eq_qVec_dot, mul_sum]
  rw [e1, e2]
  simp only [e3, sum_sub_distrib]
  rw [e4, e5]
  have t1 : ∑ h₀ ∈ univ.filter (fun h₀ => cellSumX P (f ∘ qOf) hOf h₀ < 0),
      a h₀ * cellSumX P (f ∘ qOf) hOf h₀ ≤ 0 :=
    sum_nonpos fun h₀ hh => by
      rw [mem_filter] at hh
      nlinarith [ha h₀, hh.2]
  have t2 : 0 ≤ ∑ h₀ ∈ univ.filter (fun h₀ => ¬ cellSumX P (f ∘ qOf) hOf h₀ < 0),
      b h₀ * cellSumX P (f ∘ qOf) hOf h₀ :=
    sum_nonneg fun h₀ hh => by
      rw [mem_filter] at hh
      exact mul_nonneg (hb h₀) (not_lt.mp hh.2)
  linarith

omit [Fintype Y] [Fintype Q] in
/-- **Screening-off implies the hull condition** with the proportional weights
`a h₀ = P(h₀ ∩ y₀)/P(h₀)` and `b = 0`: mm I9.5 is the special case of
`commonPriorRule_pressExpectOn_nonpos_of_hull` in which every pressed cell contributes in
proportion. (A null `h`-cell has `a = 0/0 = 0` and a null joint cell, so contributes nothing.)
Source: mm.md item 5 (I9.5) (its proof); derived here
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem hullCondition_of_screensOff (hSO : ScreensOff P hOf yOf qOf) :
    HullCondition P hOf yOf qOf := by
  intro f y₀
  refine ⟨fun h₀ => (∑ w ∈ (cell yOf y₀).filter (hOf · = h₀), P.mass w) /
      (∑ w ∈ cell hOf h₀, P.mass w), fun _ => 0, fun h₀ => ?_, fun _ => le_rfl, fun q => ?_⟩
  · exact div_nonneg (sum_nonneg fun w _ => P.nonneg w) (sum_nonneg fun w _ => P.nonneg w)
  · simp only [zero_mul, sum_const_zero, sub_zero]
    refine sum_congr rfl fun h₀ _ => ?_
    have key := hSO q h₀ y₀
    unfold qVecY qVec
    rcases (sum_nonneg fun w _ => P.nonneg w : (0 : ℝ) ≤ ∑ w ∈ cell hOf h₀, P.mass w).lt_or_eq
      with hpos | hzero
    · rw [div_mul_eq_mul_div, eq_div_iff hpos.ne', key]
      ring
    · have hnull : ∀ w ∈ cell hOf h₀, P.mass w = 0 := fun w hw =>
        (sum_eq_zero_iff_of_nonneg fun w _ => P.nonneg w).mp hzero.symm w hw
      rw [← hzero, div_zero, zero_mul]
      refine sum_eq_zero fun w hw => ?_
      rw [mem_filter, mem_filter] at hw
      exact hnull w (by rw [cell, mem_filter]; exact ⟨mem_univ _, hw.1.2⟩)

/-- **OPEN — the hull condition is necessary.** If every `Q`-measurable payoff defers on every
`y`-cell under the programmers' rule, the hull condition holds. Argument (not formalized): fix
`f` with pressed set `S`; for `g` in the weak cone `K_S` and `ε > 0` the payoff `g + εf` has
pressed set `S`, so deference gives `⟨v_S, g⟩ ≤ −ε⟨v_S, f⟩` for all `ε > 0`, hence `⟨v_S, g⟩ ≤ 0`
on `K_S`; Farkas' lemma for the finitely generated cone `cone{qVec h (h ∈ S), −qVec h (h ∉ S)}`
(whose dual cone is `K_S`) then yields `a, b ≥ 0`. Mathlib's `ProperCone.hyperplane_separation'`
is Farkas for *closed* cones and `PointedCone.DualFG.dual_dual_flip` the double dual of an
H-cone; that a finitely generated cone in `Q → ℝ` is an H-cone (Minkowski–Weyl) is the missing
step.
Source: mm.md open problem 6 (l. 292); F-6; derived here
Kind: OPEN
Fidelity: n/a (conjecture of record; with `commonPriorRule_pressExpectOn_nonpos_of_hull` it would make the hull condition necessary and sufficient)
Hyps: (a) only -/
theorem hullCondition_of_defers
    (hD : ∀ (f : Q → ℝ) (y₀ : Y),
      (commonPriorRule P hOf (f ∘ qOf)).pressExpectOn () (cell yOf y₀) (f ∘ qOf) ≤ 0) :
    HullCondition P hOf yOf qOf := by
  sorry

end Hull

end Cleanroom.Corrigibility.CorrThreeStepFacts
