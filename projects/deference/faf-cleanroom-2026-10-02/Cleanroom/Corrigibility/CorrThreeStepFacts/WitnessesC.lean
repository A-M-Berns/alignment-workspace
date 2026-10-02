import Cleanroom.Corrigibility.CorrThreeStepFacts.CommonPrior
import Cleanroom.Corrigibility.CorrThreeStepFacts.Hull
import Cleanroom.Corrigibility.CorrThreeStepFacts.WitnessesB
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Witnesses C: frames for T8, T9, T11, T16

* **T8 (⟸, strict)**: `Fin 4`, `hOf = id`, `yOf = (· < 2)`, uniform prior, `X = (−3, 1, 2, −1)`:
  the rule presses worlds `0` and `3`; both `y`-cells have strictly negative press sums
  (`w8_strict_true`, `w8_strict_false`), the full hypothesis package of
  `commonPriorRule_pressExpectOn_neg` discharged (`w8_refines`, positive cell press masses).
* **T8 (⟹)**: roles swapped (`hOf = (· < 2)`, `yOf = id`); the constructed payoff
  `straddleX` at `w₁ = 0`, `K = 8` has the cell `{0, 1}` pressed (`−7/4`) and the agent's
  `y`-cell `{0}` sum `1/4 > 0` (`w8c_pressed`, `w8c_violation`).
* **mm I9.5, necessity refuted**: `Fin 4` with `h`-cells `{0, 1}`, `{2, 3}`, `y`-cells
  `{0, 2}`, `{1, 3}` and question cells `{0, 3}`, `{1, 2}`: screening-off fails
  (`w95_not_screensOff`) yet every `Q`-measurable payoff defers on every `y`-cell
  (`w95_defers`), because both `h`-cells have the same `Q`-marginal and press together — which
  makes the rule *constant* for every `Q`-measurable payoff (`w95_rule_constant`): an inert
  channel, N− (audit r1). The live-channel refutation refines `h` to `{0, 1} | {2} | {3}`
  (`h3`): screening-off still fails (`h3_not_screensOff`), every `Q`-measurable payoff still
  defers (`h3_defers`), and the rule presses world `2` but not world `0` for `f = (1, −1)`
  (`h3_press_nonconst`), N+.
* **mm I9.5, sufficiency inhabited**: an eight-world frame (`so8`) where the programmers'
  cells straddle the agent's (not refining, `so8_not_refines`) but screen the agent's
  information off from the question (`so8_screensOff`); the rule is live (`so8_press_live`) and
  the sufficiency theorem's conclusion holds with its full package (`so8_defers`).
* **T11**: Prop. 14.2's per-cell "iff" fails in the ⟹ direction on `Fin 3`
  (`basin_cells_not_necessary`); the radius theorem is inhabited on the T8 frame with a prior
  perturbed by `1/100 < 1/48` (`w11_basin`).
* **T16**: strict gain on `Fin 3` with `X = (2, −1, −2)` and the partition `{0} | {1, 2}`
  (`w16_strict`); a partition changing no argmax has zero gain (`w16_degenerate`, N−).
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

/-- The uniform prior on `Fin 4`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def unif4 : Distr (Fin 4) where
  mass _ := 1/4
  nonneg _ := by norm_num
  sum_eq_one := by rw [Fin.sum_univ_four]; norm_num

/-- The agent's two-cell partition of `Fin 4`: `{0, 1}` and `{2, 3}`.
Source: mandate T8 (`yOf = (· / 2)`). Kind: D. Fidelity: n/a -/
def lowHalf : Fin 4 → Bool := fun i => decide (i.val < 2)

/-- The T8 payoff `(−3, 1, 2, −1)`. Source: mandate T8. Kind: D. Fidelity: n/a -/
noncomputable def x8 : Fin 4 → ℝ := ![-3, 1, 2, -1]

/-! ## T8 (⟸), strict -/

/-- `hOf = id` refines everything. Source: mandate T8. Kind: N+. Fidelity: exact -/
theorem w8_refines : RefinesModNull unif4 (id : Fin 4 → Fin 4) lowHalf :=
  fun w w' h _ _ => by simp only [id] at h; rw [h]

/-- The rule presses worlds `0` and `3` (cell sums `−3/4`, `1/4`, `1/2`, `−1/4`).
Source: mandate T8. Kind: N+. Fidelity: exact -/
theorem w8_pressed :
    rulePress unif4 id x8 0 = 1 ∧ rulePress unif4 id x8 1 = 0 ∧ rulePress unif4 id x8 2 = 0 ∧
      rulePress unif4 id x8 3 = 1 := by
  simp +decide [rulePress, ruleVal, cellSumX, cell, sum_filter, Fin.sum_univ_four, unif4, x8] <;> norm_num

/-- Both `y`-cells have positive press mass (`1/4` each). Source: mandate T8. Kind: N+. Fidelity: exact -/
theorem w8_pressMassOn :
    (commonPriorRule unif4 id x8).pressMassOn () (cell lowHalf true) = 1/4 ∧
      (commonPriorRule unif4 id x8).pressMassOn () (cell lowHalf false) = 1/4 := by
  simp +decide [commonPriorRule, ruleInstance, pressMassOn, cell, sum_filter, Fin.sum_univ_four,
    lowHalf, rulePress, ruleVal, cellSumX, unif4, x8] <;> norm_num

/-- **T8 (⟸) witness, strict.** On the agent's cell `{0, 1}` the press sum is `−3/4 < 0`; on
`{2, 3}` it is `−1/4 < 0` — Prop. 4.3 strict, with the full package of
`commonPriorRule_pressExpectOn_neg` in force.
Source: [[corr-wf13-inventory]] 008 / miri.md Prop. 4.3
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w8_strict :
    (commonPriorRule unif4 id x8).pressExpectOn () (cell lowHalf true) x8 = -3/4 ∧
      (commonPriorRule unif4 id x8).pressExpectOn () (cell lowHalf false) x8 = -1/4 ∧
      (commonPriorRule unif4 id x8).pressExpectOn () (cell lowHalf true) x8 < 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp +decide [commonPriorRule, ruleInstance, pressExpectOn, cell, sum_filter, Fin.sum_univ_four,
      lowHalf, rulePress, ruleVal, cellSumX, unif4, x8] <;> norm_num
  · simp +decide [commonPriorRule, ruleInstance, pressExpectOn, cell, sum_filter, Fin.sum_univ_four,
      lowHalf, rulePress, ruleVal, cellSumX, unif4, x8] <;> norm_num
  · exact commonPriorRule_pressExpectOn_neg w8_refines true (by rw [w8_pressMassOn.1]; norm_num)

/-! ## T8 (⟹): the straddle -/

/-- **T8 (⟹) witness.** With `hOf = lowHalf`, `yOf = id`, the payoff `straddleX` at `w₁ = 0`,
`K = 8` is `(1, −8, 0, 0)`: the cell `{0, 1}` sums to `−7/4` (pressed) while the agent's cell
`{0}` has press sum `1/4 > 0` — the straddling cell breaks deference.
Source: [[corr-wf13-inventory]] 008 / miri.md Prop. 4.3 (numerics); mm.md Lemma I9.2 (only if)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w8c_violation :
    cellSumX unif4 (straddleX lowHalf id 0 8) lowHalf true = -7/4 ∧
      (commonPriorRule unif4 lowHalf (straddleX lowHalf id 0 8)).pressExpectOn () (cell (id : Fin 4 → Fin 4) 0)
        (straddleX lowHalf id 0 8) = 1/4 := by
  constructor
  · simp +decide [cellSumX, cell, sum_filter, Fin.sum_univ_four, lowHalf, unif4, straddleX] <;> norm_num
  · simp +decide [commonPriorRule, ruleInstance, pressExpectOn, cell, sum_filter, Fin.sum_univ_four,
      lowHalf, rulePress, ruleVal, cellSumX, unif4, straddleX] <;> norm_num

/-- The straddle hypotheses of `exists_X_of_straddle` are inhabited: worlds `0` and `1` share
the `h`-cell, differ in `y`, and have positive mass.
Source: mm.md Lemma I9.2. Kind: N+. Fidelity: exact -/
theorem w8c_straddle :
    lowHalf 0 = lowHalf 1 ∧ (id : Fin 4 → Fin 4) 0 ≠ id 1 ∧ 0 < unif4.mass 0 ∧ 0 < unif4.mass 1 :=
  ⟨by decide, by decide, by norm_num [unif4], by norm_num [unif4]⟩

/-! ## mm I9.5: screening-off is not necessary -/

/-- The agent's partition `{0, 2} | {1, 3}` (parity). Source: derived here. Kind: D. Fidelity: n/a -/
def evenOf : Fin 4 → Bool := fun i => decide (i.val % 2 = 0)

/-- The question `{0, 3} | {1, 2}`. Source: derived here. Kind: D. Fidelity: n/a -/
def q95 : Fin 4 → Bool := fun i => decide (i.val = 0 ∨ i.val = 3)

/-- **Screening-off fails** on this frame: at `q = true`, `h₀ = true`, `y₀ = true`,
`P(q ∩ y₀ ∩ h₀) · P(h₀) = 1/8 ≠ 1/16 = P(q ∩ h₀) · P(y₀ ∩ h₀)`.
Source: mm.md item 5 (I9.5), open problem 6 (necessity)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w95_not_screensOff : ¬ ScreensOff unif4 lowHalf evenOf q95 := by
  intro h
  have := h true true true
  simp only [cell, sum_filter, Fin.sum_univ_four] at this
  simp +decide [lowHalf, evenOf, q95, unif4] at this

/-- **Necessity refuted (inert channel, N−).** Every `Q`-measurable payoff defers on every
`y`-cell of this frame: both `h`-cells carry the same question marginal `(1/4, 1/4)`, so they
press together and each `y`-cell's press sum is `(f(true) + f(false))/4`, negative exactly when
pressed. Hence question-relative deference holds without screening-off. *But* (audit r1) the
rule is then constant on `Ω` for every `Q`-measurable payoff (`w95_rule_constant`): deference
here is T2's inert case, not a fact about information orderings. The live-channel refutation is
`h3_defers` below.
Source: mm.md item 5 (I9.5) ("Necessity is not claimed"), open problem 6 (l. 292); mandate "Extension of record"
Kind: N−
Fidelity: exact (a refutation of necessity as stated; degenerate: the press carries no information)
Hyps: (a) only -/
theorem w95_defers (f : Bool → ℝ) (y₀ : Bool) :
    (commonPriorRule unif4 lowHalf (f ∘ q95)).pressExpectOn () (cell evenOf y₀) (f ∘ q95) ≤ 0 := by
  cases y₀ <;>
    (simp +decide [commonPriorRule, ruleInstance, pressExpectOn, cell, sum_filter, Fin.sum_univ_four,
      lowHalf, evenOf, q95, rulePress, ruleVal, cellSumX, unif4, Function.comp]
     split_ifs <;> linarith)

/-- On the `w95` frame the rule is constant for every `Q`-measurable payoff: the two `h`-cells
have the same question marginal, so they are pressed or unpressed together (the inert channel).
Source: audit r1 (fidelity) probe; mm.md item 5. Kind: N−. Fidelity: exact -/
theorem w95_rule_constant (f : Bool → ℝ) (w : Fin 4) :
    rulePress unif4 lowHalf (f ∘ q95) w = rulePress unif4 lowHalf (f ∘ q95) 0 := by
  fin_cases w <;>
    simp +decide [rulePress, ruleVal, cellSumX, cell, sum_filter, Fin.sum_univ_four, lowHalf, q95,
      unif4, Function.comp] <;>
    (try split_ifs) <;> first | rfl | (exfalso; linarith)

/-- The programmers' three-cell partition `{0, 1} | {2} | {3}` of the same four worlds.
Source: audit r1 (fidelity) probe. Kind: D. Fidelity: n/a -/
def h3 : Fin 4 → Fin 3 := ![0, 0, 1, 2]

/-- **Screening-off fails** on the `h3` frame at `(q, h₀, y₀) = (true, 0, true)`: `1/8 ≠ 1/16`.
Source: mm.md item 5 (I9.5), open problem 6. Kind: N+. Fidelity: exact -/
theorem h3_not_screensOff : ¬ ScreensOff unif4 h3 evenOf q95 := by
  intro h
  have := h true 0 true
  simp only [cell, sum_filter, Fin.sum_univ_four] at this
  simp +decide [unif4] at this

/-- **Necessity refuted (live channel, N+).** Every `Q`-measurable payoff defers on every
`y`-cell under the three-cell rule `h3`, although screening-off fails and the rule is not
constant (`h3_press_nonconst`). Mechanism: the straddling cell `{0, 1}` can be pressed with a
positive `y₀`-part only when `f(true) + f(false) < 0` with `f(true) > 0`, which forces
`f(false) < 0`, so the cell `{2} ⊆ y₀` is pressed too and its contribution `f(false)/4` outweighs
the straddle's `f(true)/4`. mm's open problem 6 has a negative answer for a live press.
Source: mm.md item 5 (I9.5) ("Necessity is not claimed"), open problem 6 (l. 292); mandate "Extension of record"
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem h3_defers (f : Bool → ℝ) (y₀ : Bool) :
    (commonPriorRule unif4 h3 (f ∘ q95)).pressExpectOn () (cell evenOf y₀) (f ∘ q95) ≤ 0 := by
  cases y₀ <;>
    (simp +decide [commonPriorRule, ruleInstance, pressExpectOn, cell, sum_filter, Fin.sum_univ_four,
      h3, evenOf, q95, rulePress, ruleVal, cellSumX, unif4, Function.comp]
     split_ifs <;> linarith)

/-- For `f = (1, −1)` the three-cell rule presses world `2` (cell `{2}`, sum `−1/4`) and not
world `0` (cell `{0, 1}`, sum `0`): the channel is live.
Source: audit r1 (fidelity) probe; mm.md item 5. Kind: N+. Fidelity: exact -/
theorem h3_press_nonconst :
    rulePress unif4 h3 ((fun b => if b then (1 : ℝ) else -1) ∘ q95) 2 = 1 ∧
      rulePress unif4 h3 ((fun b => if b then (1 : ℝ) else -1) ∘ q95) 0 = 0 := by
  constructor <;>
    simp +decide [rulePress, ruleVal, cellSumX, cell, sum_filter, Fin.sum_univ_four, h3, q95, unif4,
      Function.comp]

/-- The three cell sums of the `h3` rule for a `Q`-measurable payoff `f`: `(f(true) + f(false))/4`,
`f(false)/4`, `f(true)/4`. Source: none: witness. Kind: L. Fidelity: n/a -/
lemma h3_cellSumX (f : Bool → ℝ) :
    cellSumX unif4 (f ∘ q95) h3 0 = (f true + f false) / 4 ∧
      cellSumX unif4 (f ∘ q95) h3 1 = f false / 4 ∧ cellSumX unif4 (f ∘ q95) h3 2 = f true / 4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp +decide [cellSumX, cell, sum_filter, Fin.sum_univ_four, h3, q95, unif4, Function.comp]
     ring)

/-- **The `h3` frame satisfies the hull condition without screening off (N+).** The question
vectors are `m_A = (1/4, 1/4)`, `m_B = (0, 1/4)`, `m_C = (1/4, 0)` and the joint vectors
`m_{A,even} = (1/4, 0)`, `m_{B,even} = (0, 1/4)`, `m_{C,even} = 0`, `m_{A,odd} = (0, 1/4)`,
`m_{B,odd} = 0`, `m_{C,odd} = (1/4, 0)`; for each realizable pressed set the pressed-union
vector is a non-negative combination of the pressed `m`'s minus one of the unpressed `m`'s
(e.g. `S = {A, B}`, odd: `m_{A,odd} + m_{B,odd} = (0, 1/4) = m_A − m_C`). With
`commonPriorRule_pressExpectOn_nonpos_of_hull` this re-derives `h3_defers` from the general
theorem, on a frame where `hullCondition_of_screensOff` does not apply (`h3_not_screensOff`).
Source: mm.md open problem 6 (l. 292); F-6; audit r1
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem h3_hull : HullCondition unif4 h3 evenOf q95 := by
  intro f y₀
  obtain ⟨e0, e1, e2⟩ := h3_cellSumX f
  refine ⟨![if cellSumX unif4 (f ∘ q95) h3 0 < 0 then 1 else 0,
      if ¬ cellSumX unif4 (f ∘ q95) h3 0 < 0 ∧ cellSumX unif4 (f ∘ q95) h3 1 < 0 ∧ y₀ = true
        then 1 else 0,
      if ¬ cellSumX unif4 (f ∘ q95) h3 0 < 0 ∧ cellSumX unif4 (f ∘ q95) h3 2 < 0 ∧ y₀ = false
        then 1 else 0],
    ![0,
      if cellSumX unif4 (f ∘ q95) h3 0 < 0 ∧ ¬ cellSumX unif4 (f ∘ q95) h3 1 < 0 ∧ y₀ = true
        then 1 else 0,
      if cellSumX unif4 (f ∘ q95) h3 0 < 0 ∧ ¬ cellSumX unif4 (f ∘ q95) h3 2 < 0 ∧ y₀ = false
        then 1 else 0], ?_, ?_, ?_⟩
  · intro h₀; fin_cases h₀ <;> split_ifs <;> norm_num
  · intro h₀; fin_cases h₀ <;> split_ifs <;> norm_num
  · intro q
    by_cases hA : cellSumX unif4 (f ∘ q95) h3 0 < 0 <;>
    by_cases hB : cellSumX unif4 (f ∘ q95) h3 1 < 0 <;>
    by_cases hC : cellSumX unif4 (f ∘ q95) h3 2 < 0 <;>
    cases y₀ <;> cases q <;>
    first
    | (exfalso; rw [e0] at hA; rw [e1] at hB; rw [e2] at hC; linarith)
    | ((simp only [sum_filter, Fin.sum_univ_three]
        -- resolve the `if`s on the pressed conditions *before* unfolding the frame, so that
        -- they still match `hA`, `hB`, `hC` syntactically
        simp [hA, hB, hC]) <;>
       -- expand the `Fin 4` sums before evaluating the (constant) masses, so that
       -- `Finset.sum_const` cannot turn them into cardinalities of set-builder filters
       (simp only [qVec, qVecY, cell, sum_filter, Fin.sum_univ_four]
        simp +decide [unif4]) <;> norm_num)

/-! ## mm I9.5: a screening-off frame that does not refine (sufficiency inhabited) -/

/-- The eight-world prior: worlds `i = 4h + 2y + q` with `P(h) = P(y | h) = 1/2` and
`P(q = 1 | h = 0) = 3/4`, `P(q = 1 | h = 1) = 1/4`; masses `1/16` and `3/16`.
Source: audit r1 (fidelity) N2 (a screening-off, non-refining frame). Kind: D. Fidelity: n/a -/
noncomputable def so8 : Distr (Fin 8) where
  mass := ![1/16, 3/16, 1/16, 3/16, 3/16, 1/16, 3/16, 1/16]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_eight]; norm_num

/-- The programmers' cells `{0..3} | {4..7}` (`h = i / 4`). Source: derived here. Kind: D. Fidelity: n/a -/
def hOf8 : Fin 8 → Bool := fun i => decide (4 ≤ i.val)

/-- The agent's cells (`y = (i / 2) % 2`). Source: derived here. Kind: D. Fidelity: n/a -/
def yOf8 : Fin 8 → Bool := fun i => decide (i.val / 2 % 2 = 1)

/-- The question (`q = i % 2`). Source: derived here. Kind: D. Fidelity: n/a -/
def qOf8 : Fin 8 → Bool := fun i => decide (i.val % 2 = 1)

/-- The programmers' information does **not** refine the agent's on `so8`: worlds `0` and `2`
share the `h`-cell, differ in `y`, and have positive mass (so T8's refinement theorem does not
apply; `commonPriorRule_pressExpectOn_nonpos_of_screensOff` has content here).
Source: audit r1 (fidelity) N2. Kind: N+. Fidelity: exact -/
theorem so8_not_refines : ¬ RefinesModNull so8 hOf8 yOf8 := by
  intro h
  have := h 0 2 (by decide) (by simp +decide [so8] <;> norm_num) (by simp +decide [so8] <;> norm_num)
  simp [yOf8] at this

/-- **Screening-off holds** on `so8`: within each `h`-cell the question is independent of `y`
(the conditional law of `q` given `h` does not depend on `y`).
Source: mm.md item 5 (I9.5) (the condition `μ(q ∣ C_A ∩ D) = μ(q ∣ D)`). Kind: N+. Fidelity: exact -/
theorem so8_screensOff : ScreensOff so8 hOf8 yOf8 qOf8 := by
  intro q h₀ y₀
  cases q <;> cases h₀ <;> cases y₀ <;>
    (simp only [cell, sum_filter, Fin.sum_univ_eight]
     simp +decide [so8]
     try norm_num)

/-- The rule is **live** on `so8` for `f = (1, −1)`: the cell `h = 1` (sum `−1/4`) is pressed
and the cell `h = 0` (sum `1/4`) is not.
Source: audit r1 (fidelity) N2. Kind: N+. Fidelity: exact -/
theorem so8_press_live :
    rulePress so8 hOf8 ((fun b => if b then (1 : ℝ) else -1) ∘ qOf8) 4 = 1 ∧
      rulePress so8 hOf8 ((fun b => if b then (1 : ℝ) else -1) ∘ qOf8) 0 = 0 := by
  constructor <;>
    (simp only [rulePress, ruleVal, cellSumX, cell, sum_filter, Fin.sum_univ_eight]
     simp +decide [so8, Function.comp]
     try norm_num)

/-- **mm I9.5 sufficiency, inhabited (N+).** On `so8` every `Q`-measurable payoff defers on every
`y`-cell, by the sufficiency theorem with its full package (`so8_screensOff`) — on a frame where
refinement fails and the press is live.
Source: mm.md item 5 (I9.5); audit r1 (fidelity) N2
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem so8_defers (f : Bool → ℝ) (y₀ : Bool) :
    (commonPriorRule so8 hOf8 (f ∘ qOf8)).pressExpectOn () (cell yOf8 y₀) (f ∘ qOf8) ≤ 0 :=
  commonPriorRule_pressExpectOn_nonpos_of_screensOff so8_screensOff f y₀

/-- `so8` satisfies the hull condition too, through screening-off (`hullCondition_of_screensOff`).
Source: mm.md item 5; audit r1. Kind: N+. Fidelity: exact -/
theorem so8_hull : HullCondition so8 hOf8 yOf8 qOf8 :=
  hullCondition_of_screensOff so8 hOf8 yOf8 qOf8 so8_screensOff

/-! ## T11: the per-cell family is not necessary; the basin radius inhabited -/

/-- A three-point prior from a vector. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def distr3 (v : Fin 3 → ℝ) (h0 : ∀ i, 0 ≤ v i) (h1 : ∑ i, v i = 1) : Distr (Fin 3) where
  mass := v
  nonneg := h0
  sum_eq_one := h1

/-- The programmers' prior `(1/3, 1/9, 5/9)`. Source: derived here. Kind: D. Fidelity: n/a -/
noncomputable def μP11 : Distr (Fin 3) :=
  distr3 ![1/3, 1/9, 5/9] (fun i => by fin_cases i <;> norm_num) (by simp [Fin.sum_univ_succ] <;> norm_num)

/-- The agent's prior `(1/3, 1/2, 1/6)`. Source: derived here. Kind: D. Fidelity: n/a -/
noncomputable def μA11 : Distr (Fin 3) :=
  distr3 ![1/3, 1/2, 1/6] (fun i => by fin_cases i <;> norm_num) (by simp [Fin.sum_univ_succ] <;> norm_num)

/-- The programmers' cells `{0} | {1, 2}`. Source: derived here. Kind: D. Fidelity: n/a -/
def firstOf : Fin 3 → Bool := fun i => decide (i.val = 0)

/-- **T11, the per-cell condition is not necessary.** With `X = (−5, 3, −1)` both programmers'
cells are pressed under `μP` (`−5/3`, `−2/9`); under `μA` the cell `{1, 2}` has joint sum
`4/3 > 0` (Prop. 14.2's per-cell inequality fails) yet D1 on the agent's single `y`-cell holds
(`−5/3 + 4/3 = −1/3 ≤ 0`). Prop. 14.2's "iff" holds only as "if".
Source: [[corr-wf13-inventory]] 009 / miri.md Prop. 14.2 (finding)
Kind: N+
Fidelity: exact (refutation of the ⟹ direction)
Hyps: (a) only -/
theorem basin_cells_not_necessary :
    cellSumX μP11 ![-5, 3, -1] firstOf true < 0 ∧ cellSumX μP11 ![-5, 3, -1] firstOf false < 0 ∧
      0 < jointCellSum μA11 firstOf (fun _ => ()) ![-5, 3, -1] false () ∧
      (ruleInstance μA11 μP11 firstOf ![-5, 3, -1]).pressExpectOn () (cell (fun _ : Fin 3 => ()) ())
        ![-5, 3, -1] ≤ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp +decide [cellSumX, cell, sum_filter, Fin.sum_univ_three, firstOf, μP11, distr3] <;> norm_num
  · simp +decide [cellSumX, cell, sum_filter, Fin.sum_univ_three, firstOf, μP11, distr3] <;> norm_num
  · simp +decide [jointCellSum, cell, sum_filter, Fin.sum_univ_three, firstOf, μA11, distr3] <;> norm_num
  · simp +decide [ruleInstance, pressExpectOn, cell, sum_filter, Fin.sum_univ_three, firstOf,
      rulePress, ruleVal, cellSumX, μA11, μP11, distr3] <;> norm_num

/-- The perturbed agent prior `(1/4 + 1/100, 1/4 − 1/100, 1/4, 1/4)`.
Source: mandate T11 ("a perturbed `Distr`"). Kind: D. Fidelity: n/a -/
noncomputable def μA8 : Distr (Fin 4) where
  mass := ![1/4 + 1/100, 1/4 - 1/100, 1/4, 1/4]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_succ] <;> norm_num

/-- **T11, the basin radius inhabited.** On the T8 frame (margin `m = 1/4`, `|X| ≤ 3`,
radius `1/48`) the perturbed prior `μA8` (within `1/100`) satisfies D1 on both `y`-cells, via
`basin_neighbourhood` with every hypothesis discharged.
Source: [[corr-wf13-inventory]] 009 / miri.md Prop. 14.2
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w11_basin (y₀ : Bool) :
    (ruleInstance μA8 unif4 id x8).pressExpectOn () (cell lowHalf y₀) x8 ≤ 0 := by
  refine basin_neighbourhood μA8 unif4 id lowHalf x8 (fun w w' h => by simp only [id] at h; rw [h])
    (m := 1/4) (M := 3) (by norm_num) (by norm_num) (fun w => by fin_cases w <;> norm_num [x8])
    (fun h₀ => ?_) (fun w => ?_) y₀
  · fin_cases h₀ <;>
      (simp +decide [cellSumX, cell, sum_filter, Fin.sum_univ_four, unif4, x8] <;> norm_num)
  · fin_cases w <;> norm_num [μA8, unif4, Fintype.card_fin]

/-! ## T16: strict gain and a degenerate partition -/

/-- **T16 witness, strict.** `Fin 3`, uniform prior, `X = (2, −1, −2)` (prior `E[X] = −1/3`, so
`stop` is the unique prior-optimal act), partition `{0} | {1, 2}`: the cell `{0}` strictly
prefers `cont` (`2/3 > 0`); `priorBest = 0 < 2/3 = partValue`.
Source: [[corr-core-inventory]] 007 (Good's theorem, strict)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w16_strict :
    priorBest unif3 (twoOptionV ![(2 : ℝ), -1, -2]) = 0 ∧
      partValue2 unif3 ![(2 : ℝ), -1, -2] firstOf = 2/3 ∧
      priorBest unif3 (twoOptionV ![(2 : ℝ), -1, -2]) <
        partValue unif3 (twoOptionV ![(2 : ℝ), -1, -2]) firstOf := by
  refine ⟨?_, ?_, ?_⟩
  · unfold priorBest
    rw [sup'_twoAct]
    simp [expect, Fin.sum_univ_three, unif3, twoOptionV] <;> norm_num
  · rw [partValue2_eq, Fintype.sum_bool]
    simp +decide [cellSumX, cell, sum_filter, Fin.sum_univ_three, firstOf, unif3] <;> norm_num
  · refine priorBest_lt_partValue _ _ _ ⟨true, fun b₀ hb₀ => ?_⟩
    have hstop : b₀ = TwoAct.stop := by
      cases b₀
      · exfalso
        have := hb₀ .stop
        simp [expect, Fin.sum_univ_three, unif3, twoOptionV] at this
        norm_num at this
      · rfl
    subst hstop
    refine ⟨TwoAct.cont, ?_⟩
    simp +decide [cellSum, cell, sum_filter, Fin.sum_univ_three, firstOf, unif3, twoOptionV] <;> norm_num

/-- **T16, N−.** The partition `{1} | {0, 2}` on `X = (−1, −2, 1)` changes no argmax (`stop`
stays weakly optimal on both cells): the gain is zero, `partValue2 = 0 = priorBest`.
Source: [[corr-core-inventory]] 007 (a partition changing no argmax)
Kind: N−
Fidelity: exact (a disclosed degenerate case)
Hyps: (a) only -/
theorem w16_degenerate :
    partValue2 unif3 ![(-1 : ℝ), -2, 1] (fun i => decide (i.val = 1)) = 0 ∧
      priorBest unif3 (twoOptionV ![(-1 : ℝ), -2, 1]) = 0 := by
  constructor
  · rw [partValue2_eq, Fintype.sum_bool]
    simp +decide [cellSumX, cell, sum_filter, Fin.sum_univ_three, unif3] <;> norm_num
  · unfold priorBest
    rw [sup'_twoAct]
    simp [expect, Fin.sum_univ_three, unif3, twoOptionV] <;> norm_num

end Cleanroom.Corrigibility.CorrThreeStepFacts
