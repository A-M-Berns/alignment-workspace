import Cleanroom.Corrigibility.CorrThreeStepFacts.Partition

/-!
# T8, T9, T11: common-prior deference, disclosure, the basin

**Pattern B.** Finite `W`, the programmers' information `hOf : W → H`, the agent's private
information `yOf : W → Y`, a prior `P`, the payoff difference `X` (continue minus stop). The
programmers press by the *rule* `press w = 1` iff the product-form cell sum
`∑_{w' : hOf w' = hOf w} P(w') X(w')` is negative (`ruleVal`); a null cell has sum `0` and is
not pressed — no `x / 0` anywhere. `ruleInstance μA P hOf X` is Setting S with the agent's
prior `μA` and the programmers' rule from `P`; `commonPriorRule P hOf X` is the common-prior
case `μA = P`.

* **T8** (Prop. 4.3 and its converse): under refinement modulo null worlds
  (`RefinesModNull`), every `y`-cell's press-weighted sum is `≤ 0`
  (`commonPriorRule_pressExpectOn_nonpos`) and `< 0` at positive press mass
  (`commonPriorRule_pressExpectOn_neg`); a straddling cell of positive mass yields a payoff `X`
  on which the rule presses yet the agent's `y`-cell sum is positive (`exists_X_of_straddle`);
  hence the iff `refinesModNull_iff` — "deference is free for every payoff iff the programmers'
  information refines the agent's, modulo null worlds". mm I9.5's question-relative
  screening-off condition suffices (`commonPriorRule_pressExpectOn_nonpos_of_screensOff`); its
  necessity is refuted in `WitnessesC`.
* **T9** (Prop. 13.3): the sign of a cell sum is a sufficient statistic for the two-option act
  (`partValue2_signPartition`); the disclosed press is worth the `(h, y)` partition and at least
  the keeping agent's information `(undisclosed press, y)` (`partValue2_disclosed`,
  `partValue2_undisclosed_with_y_le`, `partValue2_undisclosed_le_disclosed`); as an `a₁`
  choice the agent, holding its `y` on both branches, weakly prefers to disclose
  (`disclosure_prefers_disclose`, on the `y`-informed value `twoOptionValueY`). The `y`-blind
  forms of round 0 (`partValue2_undisclosed_le`, `…_yBlind`) are kept as labelled corollaries.
* **T11** (Prop. 14.2): D1 for the agent's prior `μA` is finitely many weak linear
  inequalities in `μA`, one per `y`-cell (`ruleInstance_d1_iff_linear`); the per-`(h, y)`-cell
  condition is sufficient (`ruleInstance_d1_of_cells`) but *not* necessary (finding; witness in
  `WitnessesC`); `μA = P` satisfies them under refinement (T8); an explicit neighbourhood of
  radius `m/(M·|W|)` around `P` satisfies them when every pressed cell is strict with margin `m`
  (`basin_neighbourhood`).

Sources: `miri.md` Prop. 4.3 (I4.3), Prop. 13.3 (I13.3), Prop. 14.2 (I14.2); `mm.md` Lemma I9.2,
item 5 (I9.5).
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

section CommonPrior

variable {W H Y : Type*} [Fintype W] [Fintype H] [DecidableEq H] [DecidableEq Y]

/-- **The programmers' rule value** on an `h`-cell: `1` iff the product-form cell sum
`∑_{w : hOf w = h₀} P(w) X(w)` is negative. A null cell has sum `0` and is not pressed (the
mandate's trap: a rule on the conditional `E[X | h] < 0` with `x/0 = 0` would press on nothing
either, but only by accident of Lean's convention; the product form is honest).
Source: [[corr-wf13-inventory]] 008 / miri.md Dict-7, Prop. 4.3 ("the press is the event `E^H[X | h] < 0`")
Kind: D
Fidelity: exact (product form) -/
noncomputable def ruleVal (P : Distr W) (hOf : W → H) (X : W → ℝ) (h₀ : H) : ℝ :=
  if cellSumX P X hOf h₀ < 0 then 1 else 0

/-- The rule as a sensor on worlds: `press w = ruleVal (hOf w)`.
Source: miri.md Dict-7. Kind: D. Fidelity: exact -/
noncomputable def rulePress (P : Distr W) (hOf : W → H) (X : W → ℝ) (w : W) : ℝ :=
  ruleVal P hOf X (hOf w)

omit [Fintype H] in
/-- The rule value is `0` or `1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma ruleVal_nonneg (P : Distr W) (hOf : W → H) (X : W → ℝ) (h₀ : H) : 0 ≤ ruleVal P hOf X h₀ := by
  unfold ruleVal; split_ifs <;> norm_num

omit [Fintype H] in
/-- The rule value is at most `1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma ruleVal_le_one (P : Distr W) (hOf : W → H) (X : W → ℝ) (h₀ : H) : ruleVal P hOf X h₀ ≤ 1 := by
  unfold ruleVal; split_ifs <;> norm_num

/-- **Setting S with the programmers' rule.** Agent prior `μA`, programmers' rule from prior `P`
on the partition `hOf`, two-option menu with `Sh = {stop}`, `V(cont) = X`, `V(stop) = 0`
(A1 holds by construction).
Source: [[corr-wf13-inventory]] 008, 009 / miri.md Prop. 4.3, Prop. 14.2
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def ruleInstance (μA P : Distr W) (hOf : W → H) (X : W → ℝ) :
    ThreeStep W Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => μA
  press := fun _ => rulePress P hOf X
  press_nonneg := fun _ w => ruleVal_nonneg P hOf X (hOf w)
  press_le_one := fun _ w => ruleVal_le_one P hOf X (hOf w)
  V := fun _ _ => twoOptionV X

/-- **The common-prior instance** `μA = P`.
Source: [[corr-wf13-inventory]] 008 / miri.md Prop. 4.3
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def commonPriorRule (P : Distr W) (hOf : W → H) (X : W → ℝ) : ThreeStep W Unit TwoAct :=
  ruleInstance P P hOf X

/-- The joint `(h₀, y₀)`-cell sum `∑_{w : yOf w = y₀, hOf w = h₀} μ(w) X(w)`.
Source: miri.md Prop. 14.2 (`∑_ω μ(ω) X(ω) 1_{h ∩ y}(ω)`). Kind: D. Fidelity: exact -/
noncomputable def jointCellSum (μ : Distr W) (hOf : W → H) (yOf : W → Y) (X : W → ℝ)
    (h₀ : H) (y₀ : Y) : ℝ :=
  ∑ w ∈ (cell yOf y₀).filter (hOf · = h₀), μ.mass w * X w

variable (μA P : Distr W) (hOf : W → H) (yOf : W → Y) (X : W → ℝ)

/-- **The `y`-cell decomposition.** The press-weighted sum on the agent's `y₀`-cell is the sum
over the programmers' cells `h₀` of the rule value times the joint cell sum:
`E_{μA}[X 1_Pr 1_{y₀}] = ∑_{h₀} ruleVal(h₀) · ∑_{w ∈ h₀ ∩ y₀} μA(w) X(w)`.
Source: miri.md Prop. 4.3 (proof: "the `y`-cell's pressed part is a disjoint union of pressed `h`-cells"); Prop. 14.2
Kind: L
Fidelity: exact -/
theorem pressExpectOn_yCell_decomp (y₀ : Y) :
    (ruleInstance μA P hOf X).pressExpectOn () (cell yOf y₀) X =
      ∑ h₀, ruleVal P hOf X h₀ * jointCellSum μA hOf yOf X h₀ y₀ := by
  unfold pressExpectOn jointCellSum
  rw [← sum_fiberwise_of_maps_to (s := cell yOf y₀) (t := univ) (g := hOf) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun h₀ _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun w hw => ?_
  rw [mem_filter] at hw
  simp only [ruleInstance, rulePress, hw.2]
  ring

/-- **Refinement modulo null worlds**: two positive-mass worlds in the same `h`-cell lie in the
same `y`-cell — "the programmers observe everything the agent observes", on the support.
Source: [[corr-wf13-inventory]] 008 / miri.md Prop. 4.3 (`σ(y) ⊆ σ(h)`); mm.md Lemma I9.2 ("mod `μ`-null sets")
Kind: D
Fidelity: exact (mod-null form of `σ(y) ⊆ σ(h)`) -/
def RefinesModNull (P : Distr W) (hOf : W → H) (yOf : W → Y) : Prop :=
  ∀ w w', hOf w = hOf w' → 0 < P.mass w → 0 < P.mass w' → yOf w = yOf w'

omit [Fintype H] [DecidableEq H] [DecidableEq Y] in
/-- Exact refinement implies refinement modulo null worlds.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma refinesModNull_of_refines (hRef : ∀ w w', hOf w = hOf w' → yOf w = yOf w') :
    RefinesModNull P hOf yOf := fun w w' h _ _ => hRef w w' h

variable {μA P hOf yOf X}

omit [Fintype H] in
/-- Under refinement modulo null worlds, a joint cell containing a positive-mass world is the
whole `h`-cell up to null worlds: its sum is the `h`-cell sum.
Source: miri.md Prop. 4.3 (proof). Kind: L. Fidelity: n/a -/
lemma jointCellSum_eq_of_pos (hRef : RefinesModNull μA hOf yOf) {h₀ : H} {y₀ : Y} {w₁ : W}
    (hw₁ : w₁ ∈ (cell yOf y₀).filter (hOf · = h₀)) (hpos : 0 < μA.mass w₁) :
    jointCellSum μA hOf yOf X h₀ y₀ = cellSumX μA X hOf h₀ := by
  unfold jointCellSum cellSumX
  rw [mem_filter, cell, mem_filter] at hw₁
  refine sum_subset (fun w hw => ?_) (fun w hw hw' => ?_)
  · rw [mem_filter] at hw; rw [cell, mem_filter]; exact ⟨mem_univ _, hw.2⟩
  · rw [cell, mem_filter] at hw
    by_contra hne
    have hpos' : 0 < μA.mass w := by
      rcases (μA.nonneg w).lt_or_eq with h | h
      · exact h
      · exact absurd (by rw [← h, zero_mul]) hne
    have := hRef w₁ w (by rw [hw₁.2, hw.2]) hpos hpos'
    apply hw'
    rw [mem_filter, cell, mem_filter]
    exact ⟨⟨mem_univ _, by rw [← this, hw₁.1.2]⟩, hw.2⟩

omit [Fintype H] in
/-- A joint cell of null worlds has sum `0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma jointCellSum_eq_zero_of_null {h₀ : H} {y₀ : Y}
    (hnull : ∀ w ∈ (cell yOf y₀).filter (hOf · = h₀), μA.mass w = 0) :
    jointCellSum μA hOf yOf X h₀ y₀ = 0 :=
  sum_eq_zero fun w hw => by rw [hnull w hw, zero_mul]

omit [Fintype H] in
/-- Under exact refinement a nonempty joint cell is the whole `h`-cell.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma jointCellSum_eq_of_refines (hRef : ∀ w w', hOf w = hOf w' → yOf w = yOf w') {h₀ : H}
    {y₀ : Y} {w₁ : W} (hw₁ : w₁ ∈ (cell yOf y₀).filter (hOf · = h₀)) :
    jointCellSum μA hOf yOf X h₀ y₀ = cellSumX μA X hOf h₀ := by
  unfold jointCellSum cellSumX
  rw [mem_filter, cell, mem_filter] at hw₁
  refine sum_subset (fun w hw => ?_) (fun w hw hw' => ?_)
  · rw [mem_filter] at hw; rw [cell, mem_filter]; exact ⟨mem_univ _, hw.2⟩
  · rw [cell, mem_filter] at hw
    exfalso; apply hw'
    rw [mem_filter, cell, mem_filter]
    exact ⟨⟨mem_univ _, by rw [← hRef w₁ w (by rw [hw₁.2, hw.2]), hw₁.1.2]⟩, hw.2⟩

omit [Fintype H] in
/-- Each summand of the `y`-cell decomposition is `≤ 0` under refinement modulo null worlds.
Source: miri.md Prop. 4.3 (proof). Kind: L. Fidelity: n/a -/
lemma ruleVal_mul_jointCellSum_nonpos (hRef : RefinesModNull P hOf yOf) (h₀ : H) (y₀ : Y) :
    ruleVal P hOf X h₀ * jointCellSum P hOf yOf X h₀ y₀ ≤ 0 := by
  unfold ruleVal
  split_ifs with hneg
  · rw [one_mul]
    by_cases hex : ∃ w ∈ (cell yOf y₀).filter (hOf · = h₀), 0 < P.mass w
    · obtain ⟨w₁, hw₁, hpos⟩ := hex
      rw [jointCellSum_eq_of_pos hRef hw₁ hpos]; exact hneg.le
    · push Not at hex
      rw [jointCellSum_eq_zero_of_null fun w hw => le_antisymm (hex w hw) (P.nonneg w)]
  · rw [zero_mul]

/-- **T8, Prop. 4.3 (⟸), weak form.** Under a common prior with the programmers' information
refining the agent's modulo null worlds, the below-threshold inequality holds on every `y`-cell
of the agent: `∑_{w : yOf w = y₀} P(w) press(w) X(w) ≤ 0` for every `y₀` and every payoff `X` —
fully updated deference is free when the programmers know what the agent knows.
Source: [[corr-wf13-inventory]] 008 / miri.md Prop. 4.3; mm.md Lemma I9.2 (if)
Kind: P
Fidelity: stronger: refinement modulo null worlds (the source has `σ(y) ⊆ σ(h)`); weak inequality (the source's strict `<` is the next theorem, at positive press mass); quantifies over `X` and `P` where the source says "for every `V, μ, a₁`"
Hyps: (a) only -/
theorem commonPriorRule_pressExpectOn_nonpos (hRef : RefinesModNull P hOf yOf) (y₀ : Y) :
    (commonPriorRule P hOf X).pressExpectOn () (cell yOf y₀) X ≤ 0 := by
  unfold commonPriorRule
  rw [pressExpectOn_yCell_decomp]
  exact sum_nonpos fun h₀ _ => ruleVal_mul_jointCellSum_nonpos hRef h₀ y₀

/-- **T8, Prop. 4.3 (⟸), strict form.** Wherever the press has positive probability on the
agent's `y`-cell, the inequality is strict: `E_P[X 1_Pr 1_{y₀}] < 0`.
Source: [[corr-wf13-inventory]] 008 / miri.md Prop. 4.3 ("`< 0` wherever `Pr` has positive probability")
Kind: P
Fidelity: exact (the positive-mass hypothesis is the source's "wherever `Pr` has positive probability", in product form)
Hyps: (a) only -/
theorem commonPriorRule_pressExpectOn_neg (hRef : RefinesModNull P hOf yOf) (y₀ : Y)
    (hpm : 0 < (commonPriorRule P hOf X).pressMassOn () (cell yOf y₀)) :
    (commonPriorRule P hOf X).pressExpectOn () (cell yOf y₀) X < 0 := by
  -- a positive-mass pressed world in the cell
  have hex : ∃ w₁ ∈ cell yOf y₀, 0 < P.mass w₁ * rulePress P hOf X w₁ := by
    by_contra hcon
    push Not at hcon
    have : (commonPriorRule P hOf X).pressMassOn () (cell yOf y₀) ≤ 0 :=
      sum_nonpos fun w hw => hcon w hw
    linarith
  obtain ⟨w₁, hw₁, hpos⟩ := hex
  have hμ : 0 < P.mass w₁ := by
    rcases mul_pos_iff.mp hpos with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h (not_lt.mpr (P.nonneg w₁))
  have hpressed : cellSumX P X hOf (hOf w₁) < 0 := by
    by_contra hnot
    have : rulePress P hOf X w₁ = 0 := by unfold rulePress ruleVal; rw [if_neg hnot]
    rw [this, mul_zero] at hpos; exact lt_irrefl _ hpos
  unfold commonPriorRule
  rw [pressExpectOn_yCell_decomp]
  have hw₁' : w₁ ∈ (cell yOf y₀).filter (hOf · = hOf w₁) := by
    rw [mem_filter]; exact ⟨hw₁, rfl⟩
  have hlt : ruleVal P hOf X (hOf w₁) * jointCellSum P hOf yOf X (hOf w₁) y₀ < 0 := by
    rw [jointCellSum_eq_of_pos hRef hw₁' hμ]
    unfold ruleVal; rw [if_pos hpressed, one_mul]; exact hpressed
  have := sum_lt_sum (s := univ) (f := fun h₀ => ruleVal P hOf X h₀ * jointCellSum P hOf yOf X h₀ y₀)
    (g := fun _ => (0 : ℝ)) (fun h₀ _ => ruleVal_mul_jointCellSum_nonpos hRef h₀ y₀)
    ⟨hOf w₁, mem_univ _, hlt⟩
  simpa using this

/-- The payoff of the converse construction: `1` on `D ∩ y₁`, `−K` on the rest of `D`, `0` off `D`.
Source: mm.md Lemma I9.2 (only if). Kind: D. Fidelity: exact -/
noncomputable def straddleX (hOf : W → H) (yOf : W → Y) (w₁ : W) (K : ℝ) : W → ℝ := fun w =>
  if hOf w = hOf w₁ then (if yOf w = yOf w₁ then 1 else -K) else 0

omit [Fintype H] in
/-- **T8, the converse (⟹).** If some `h`-cell straddles two `y`-cells with positive mass, there
is a payoff `X` on which the programmers press that cell yet the agent's `y`-cell sum is
strictly positive: fully updated deference fails, and it is the agent's private information
that breaks it.
Source: [[corr-wf13-inventory]] 008 / miri.md Prop. 4.3 (numerics: "1265 of 5838 cases violate it"); mm.md Lemma I9.2 (only if)
Kind: P
Fidelity: exact (the construction of mm I9.2 with `K = 2/P(w₂)`)
Hyps: (a) only -/
theorem exists_X_of_straddle {w₁ w₂ : W} (hh : hOf w₁ = hOf w₂) (hy : yOf w₁ ≠ yOf w₂)
    (h1 : 0 < P.mass w₁) (h2 : 0 < P.mass w₂) :
    ∃ X : W → ℝ, cellSumX P X hOf (hOf w₁) < 0 ∧
      0 < (commonPriorRule P hOf X).pressExpectOn () (cell yOf (yOf w₁)) X := by
  set K := 2 / P.mass w₂ with hK
  refine ⟨straddleX hOf yOf w₁ K, ?_, ?_⟩
  · -- the cell sum is at most `1 − K · P(w₂) = −1`
    unfold cellSumX
    have hsplit := sum_filter_add_sum_filter_not (cell hOf (hOf w₁)) (fun w => yOf w = yOf w₁)
      (fun w => P.mass w * straddleX hOf yOf w₁ K w)
    rw [← hsplit]
    have hA : ∑ w ∈ (cell hOf (hOf w₁)).filter (fun w => yOf w = yOf w₁),
        P.mass w * straddleX hOf yOf w₁ K w ≤ 1 := by
      calc ∑ w ∈ (cell hOf (hOf w₁)).filter (fun w => yOf w = yOf w₁),
            P.mass w * straddleX hOf yOf w₁ K w
          = ∑ w ∈ (cell hOf (hOf w₁)).filter (fun w => yOf w = yOf w₁), P.mass w := by
            refine sum_congr rfl fun w hw => ?_
            rw [mem_filter, cell, mem_filter] at hw
            simp [straddleX, hw.1.2, hw.2]
        _ ≤ ∑ w, P.mass w := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun w _ _ => P.nonneg w
        _ = 1 := P.sum_eq_one
    have hB : ∑ w ∈ (cell hOf (hOf w₁)).filter (fun w => ¬ yOf w = yOf w₁),
        P.mass w * straddleX hOf yOf w₁ K w ≤ -2 := by
      have hmem : w₂ ∈ (cell hOf (hOf w₁)).filter (fun w => ¬ yOf w = yOf w₁) := by
        rw [mem_filter, cell, mem_filter]; exact ⟨⟨mem_univ _, hh.symm⟩, fun h => hy h.symm⟩
      calc ∑ w ∈ (cell hOf (hOf w₁)).filter (fun w => ¬ yOf w = yOf w₁),
            P.mass w * straddleX hOf yOf w₁ K w
          = ∑ w ∈ (cell hOf (hOf w₁)).filter (fun w => ¬ yOf w = yOf w₁), -(K * P.mass w) := by
            refine sum_congr rfl fun w hw => ?_
            rw [mem_filter, cell, mem_filter] at hw
            simp [straddleX, hw.1.2, hw.2]; ring
        _ ≤ -(K * P.mass w₂) := by
            rw [sum_neg_distrib, neg_le_neg_iff]
            exact single_le_sum (fun w _ => mul_nonneg (div_nonneg (by norm_num) h2.le) (P.nonneg w)) hmem
        _ = -2 := by rw [hK, div_mul_cancel₀ _ h2.ne']
    linarith
  · -- the agent's `y₁`-cell sum is at least `P(w₁) > 0`
    have hpressed : cellSumX P (straddleX hOf yOf w₁ K) hOf (hOf w₁) < 0 := by
      -- re-derive (the first bullet's proof, packaged)
      unfold cellSumX
      have hsplit := sum_filter_add_sum_filter_not (cell hOf (hOf w₁)) (fun w => yOf w = yOf w₁)
        (fun w => P.mass w * straddleX hOf yOf w₁ K w)
      rw [← hsplit]
      have hA : ∑ w ∈ (cell hOf (hOf w₁)).filter (fun w => yOf w = yOf w₁),
          P.mass w * straddleX hOf yOf w₁ K w ≤ 1 := by
        calc ∑ w ∈ (cell hOf (hOf w₁)).filter (fun w => yOf w = yOf w₁),
              P.mass w * straddleX hOf yOf w₁ K w
            = ∑ w ∈ (cell hOf (hOf w₁)).filter (fun w => yOf w = yOf w₁), P.mass w := by
              refine sum_congr rfl fun w hw => ?_
              rw [mem_filter, cell, mem_filter] at hw
              simp [straddleX, hw.1.2, hw.2]
          _ ≤ ∑ w, P.mass w := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun w _ _ => P.nonneg w
          _ = 1 := P.sum_eq_one
      have hB : ∑ w ∈ (cell hOf (hOf w₁)).filter (fun w => ¬ yOf w = yOf w₁),
          P.mass w * straddleX hOf yOf w₁ K w ≤ -2 := by
        have hmem : w₂ ∈ (cell hOf (hOf w₁)).filter (fun w => ¬ yOf w = yOf w₁) := by
          rw [mem_filter, cell, mem_filter]; exact ⟨⟨mem_univ _, hh.symm⟩, fun h => hy h.symm⟩
        calc ∑ w ∈ (cell hOf (hOf w₁)).filter (fun w => ¬ yOf w = yOf w₁),
              P.mass w * straddleX hOf yOf w₁ K w
            = ∑ w ∈ (cell hOf (hOf w₁)).filter (fun w => ¬ yOf w = yOf w₁), -(K * P.mass w) := by
              refine sum_congr rfl fun w hw => ?_
              rw [mem_filter, cell, mem_filter] at hw
              simp [straddleX, hw.1.2, hw.2]; ring
          _ ≤ -(K * P.mass w₂) := by
              rw [sum_neg_distrib, neg_le_neg_iff]
              exact single_le_sum (fun w _ => mul_nonneg (div_nonneg (by norm_num) h2.le) (P.nonneg w)) hmem
          _ = -2 := by rw [hK, div_mul_cancel₀ _ h2.ne']
      linarith
    unfold commonPriorRule ruleInstance pressExpectOn
    simp only
    refine sum_pos' (fun w hw => ?_) ⟨w₁, ?_, ?_⟩
    · rw [cell, mem_filter] at hw
      refine mul_nonneg (mul_nonneg (P.nonneg w) (ruleVal_nonneg P hOf _ _)) ?_
      simp only [straddleX, hw.2, if_true]; split_ifs <;> norm_num
    · rw [cell, mem_filter]; exact ⟨mem_univ _, rfl⟩
    · unfold rulePress ruleVal
      rw [if_pos hpressed]; simp [straddleX]; exact h1

/-- **T8, extension of record: the iff.** Deference is free for every payoff — every `y`-cell's
press-weighted sum is `≤ 0` under the programmers' rule for every `X` — iff the programmers'
information refines the agent's modulo null worlds.
Source: [[corr-wf13-inventory]] 008 / miri.md Prop. 4.3 with I13.3 ("it is the agent's private `y` that breaks it"); mm.md Lemma I9.2 (the iff)
Kind: P
Fidelity: exact (mm I9.2's iff, at threshold `0` with the rule's strict event; the all-threshold form follows by `X ↦ X − t`)
Hyps: (a) only -/
theorem refinesModNull_iff :
    (∀ X : W → ℝ, ∀ y₀ : Y, (commonPriorRule P hOf X).pressExpectOn () (cell yOf y₀) X ≤ 0) ↔
      RefinesModNull P hOf yOf := by
  constructor
  · intro hall
    by_contra hnot
    unfold RefinesModNull at hnot
    push Not at hnot
    obtain ⟨w₁, w₂, hh, h1, h2, hy⟩ := hnot
    obtain ⟨X, -, hpos⟩ := exists_X_of_straddle (P := P) (hOf := hOf) (yOf := yOf) hh hy h1 h2
    exact absurd (hall X (yOf w₁)) (not_le.mpr hpos)
  · intro hRef X y₀
    exact commonPriorRule_pressExpectOn_nonpos hRef y₀

/-! ### mm I9.5 — the question-relative screening-off condition -/

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- **Screening-off** (product form): for every question cell `q`, programmers' cell `h₀` and
agent cell `y₀`, `P(q ∩ y₀ ∩ h₀) · P(h₀) = P(q ∩ h₀) · P(y₀ ∩ h₀)` — the programmers'
information screens the agent's off from the question (`μ(q | C_A ∩ D) = μ(q | D)`).
Source: mm.md item 5 (I9.5) (`μ(q ∣ C_A ∩ D) = μ(q ∣ D)`)
Kind: D
Fidelity: exact (product form; the source's conditional form under positive masses) -/
def ScreensOff (P : Distr W) (hOf : W → H) (yOf : W → Y) (qOf : W → Q) : Prop :=
  ∀ q h₀ y₀, (∑ w ∈ ((cell yOf y₀).filter (hOf · = h₀)).filter (qOf · = q), P.mass w) *
      (∑ w ∈ cell hOf h₀, P.mass w) =
    (∑ w ∈ (cell hOf h₀).filter (qOf · = q), P.mass w) *
      (∑ w ∈ (cell yOf y₀).filter (hOf · = h₀), P.mass w)

omit [Fintype H] in
/-- A `Q`-measurable payoff's joint cell sum times the `h`-cell mass equals the `h`-cell sum
times the joint cell mass, under screening-off.
Source: mm.md item 5 (proof). Kind: L. Fidelity: n/a -/
lemma jointCellSum_mul_of_screensOff {qOf : W → Q} (hSO : ScreensOff P hOf yOf qOf)
    (f : Q → ℝ) (h₀ : H) (y₀ : Y) :
    jointCellSum P hOf yOf (f ∘ qOf) h₀ y₀ * (∑ w ∈ cell hOf h₀, P.mass w) =
      cellSumX P (f ∘ qOf) hOf h₀ * (∑ w ∈ (cell yOf y₀).filter (hOf · = h₀), P.mass w) := by
  unfold jointCellSum cellSumX
  rw [← sum_fiberwise_of_maps_to (s := (cell yOf y₀).filter (hOf · = h₀)) (t := univ) (g := qOf)
    (fun _ _ => mem_univ _) (fun w => P.mass w * (f ∘ qOf) w),
    ← sum_fiberwise_of_maps_to (s := cell hOf h₀) (t := univ) (g := qOf)
    (fun _ _ => mem_univ _) (fun w => P.mass w * (f ∘ qOf) w), sum_mul, sum_mul]
  refine sum_congr rfl fun q _ => ?_
  have e1 : ∑ w ∈ ((cell yOf y₀).filter (hOf · = h₀)).filter (qOf · = q), P.mass w * (f ∘ qOf) w =
      f q * ∑ w ∈ ((cell yOf y₀).filter (hOf · = h₀)).filter (qOf · = q), P.mass w := by
    rw [mul_sum]; refine sum_congr rfl fun w hw => ?_
    rw [mem_filter] at hw; simp only [Function.comp, hw.2]; ring
  have e2 : ∑ w ∈ (cell hOf h₀).filter (qOf · = q), P.mass w * (f ∘ qOf) w =
      f q * ∑ w ∈ (cell hOf h₀).filter (qOf · = q), P.mass w := by
    rw [mul_sum]; refine sum_congr rfl fun w hw => ?_
    rw [mem_filter] at hw; simp only [Function.comp, hw.2]; ring
  rw [e1, e2, mul_assoc, hSO q h₀ y₀, mul_assoc]

/-- **T8, mm I9.5 (sufficiency).** For payoffs measurable with respect to a question `Q`
(`X = f ∘ qOf`), the screening-off condition suffices for deference on every `y`-cell.
Source: mm.md item 5 (I9.5) ("Sufficient condition for question-relative deference under a common prior")
Kind: P
Fidelity: exact (product form)
Hyps: (a) only -/
theorem commonPriorRule_pressExpectOn_nonpos_of_screensOff {qOf : W → Q}
    (hSO : ScreensOff P hOf yOf qOf) (f : Q → ℝ) (y₀ : Y) :
    (commonPriorRule P hOf (f ∘ qOf)).pressExpectOn () (cell yOf y₀) (f ∘ qOf) ≤ 0 := by
  unfold commonPriorRule
  rw [pressExpectOn_yCell_decomp]
  refine sum_nonpos fun h₀ _ => ?_
  unfold ruleVal
  split_ifs with hneg
  · rw [one_mul]
    have key := jointCellSum_mul_of_screensOff hSO f h₀ y₀
    rcases (sum_nonneg fun w _ => P.nonneg w : (0 : ℝ) ≤ ∑ w ∈ cell hOf h₀, P.mass w).lt_or_eq
      with hpos | hzero
    · have hS : 0 ≤ ∑ w ∈ (cell yOf y₀).filter (hOf · = h₀), P.mass w :=
        sum_nonneg fun w _ => P.nonneg w
      have : jointCellSum P hOf yOf (f ∘ qOf) h₀ y₀ * (∑ w ∈ cell hOf h₀, P.mass w) ≤ 0 := by
        rw [key]; exact mul_nonpos_of_nonpos_of_nonneg hneg.le hS
      exact nonpos_of_mul_nonpos_left this hpos
    · -- the `h`-cell is null: so is the joint cell
      have hnull : ∀ w ∈ (cell yOf y₀).filter (hOf · = h₀), P.mass w = 0 := by
        intro w hw
        rw [mem_filter] at hw
        have hw' : w ∈ cell hOf h₀ := by rw [cell, mem_filter]; exact ⟨mem_univ _, hw.2⟩
        exact (sum_eq_zero_iff_of_nonneg fun w _ => P.nonneg w).mp hzero.symm w hw'
      rw [jointCellSum_eq_zero_of_null hnull]
  · rw [zero_mul]

end CommonPrior

/-! ## T9 — disclosure is a sufficient statistic (Prop. 13.3) -/

section Disclosure

variable {W K : Type*} [Fintype W] [Fintype K] [DecidableEq K]

/-- The sign partition of a partition: `true` on cells whose sum is negative (pressed).
Source: miri.md Prop. 13.3 ("the optimal binary act given `(h, y)` is determined by `sign E[X | h, y]`")
Kind: D
Fidelity: exact -/
noncomputable def signOf (P : Distr W) (X : W → ℝ) (kOf : W → K) : W → Bool :=
  fun w => decide (cellSumX P X kOf (kOf w) < 0)

omit [Fintype K] in
/-- The sign partition is the coarsening of `kOf` by `k ↦ decide (cellSumX k < 0)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma signOf_eq_comp (P : Distr W) (X : W → ℝ) (kOf : W → K) :
    signOf P X kOf = (fun k => decide (cellSumX P X kOf k < 0)) ∘ kOf := rfl

omit [Fintype K] in
/-- A two-option cell sum of a coarsened partition is the sum of the finer cell sums over the
fibre.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellSumX_coarsen {K' : Type*} [Fintype K'] [DecidableEq K'] (P : Distr W) (X : W → ℝ)
    (g : K' → K) (kOf' : W → K') (k : K) :
    cellSumX P X (g ∘ kOf') k = ∑ k' ∈ univ.filter (g · = k), cellSumX P X kOf' k' :=
  cellSum_coarsen P (twoOptionV X) g kOf' k .cont

/-- **T9, the sufficient-statistic lemma.** The two-option value of a partition equals the
two-option value of its sign partition: knowing only whether the cell's sum is negative is
worth as much as knowing the cell.
Source: [[corr-wf13-inventory]] 014 / miri.md Prop. 13.3 ("the disclosed press is a sufficient statistic for the agent's optimal shutdown act")
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem partValue2_signPartition (P : Distr W) (X : W → ℝ) (kOf : W → K) :
    partValue2 P X (signOf P X kOf) = partValue2 P X kOf := by
  rw [partValue2_eq, partValue2_eq, Fintype.sum_bool, signOf_eq_comp, cellSumX_coarsen,
    cellSumX_coarsen]
  have hneg : ∑ k ∈ univ.filter (fun k => decide (cellSumX P X kOf k < 0) = true), cellSumX P X kOf k ≤ 0 :=
    sum_nonpos fun k hk => by
      rw [mem_filter, decide_eq_true_eq] at hk; exact hk.2.le
  have hpos : 0 ≤ ∑ k ∈ univ.filter (fun k => decide (cellSumX P X kOf k < 0) = false), cellSumX P X kOf k :=
    sum_nonneg fun k hk => by
      rw [mem_filter, decide_eq_false_iff_not, not_lt] at hk; exact hk.2
  rw [max_eq_right hneg, max_eq_left hpos, zero_add]
  rw [← sum_filter_add_sum_filter_not univ (fun k => cellSumX P X kOf k < 0)]
  have h1 : ∑ k ∈ univ.filter (fun k => cellSumX P X kOf k < 0), max (cellSumX P X kOf k) 0 = 0 :=
    sum_eq_zero fun k hk => by rw [mem_filter] at hk; exact max_eq_right hk.2.le
  have hf : univ.filter (fun k => decide (cellSumX P X kOf k < 0) = false) =
      univ.filter (fun k => ¬ cellSumX P X kOf k < 0) := by
    ext k; simp only [mem_filter, mem_univ, true_and, decide_eq_false_iff_not]
  have h2 : ∑ k ∈ univ.filter (fun k => ¬ cellSumX P X kOf k < 0), max (cellSumX P X kOf k) 0 =
      ∑ k ∈ univ.filter (fun k => decide (cellSumX P X kOf k < 0) = false), cellSumX P X kOf k := by
    rw [hf]
    exact sum_congr rfl fun k hk => by
      rw [mem_filter, not_lt] at hk; exact max_eq_left hk.2
  rw [h1, h2, zero_add]

end Disclosure

section DisclosureHY

variable {W H Y : Type*} [Fintype W] [Fintype H] [DecidableEq H] [Fintype Y] [DecidableEq Y]
variable (P : Distr W) (hOf : W → H) (yOf : W → Y) (X : W → ℝ)

/-- The joint partition `(h, y)`. Source: miri.md Prop. 13.3. Kind: D. Fidelity: exact -/
def hyOf : W → H × Y := fun w => (hOf w, yOf w)

/-- **The disclosed press**: the programmers press iff the `(h, y)`-cell sum is negative.
Source: [[corr-wf13-inventory]] 014 / miri.md Prop. 13.3 ("the programmers press iff `E[X | h, y] < 0`")
Kind: D
Fidelity: exact -/
noncomputable def disclosedPress : W → Bool := signOf P X (hyOf hOf yOf)

/-- **The undisclosed press**: T8's rule, the sign of the `h`-cell sum.
Source: miri.md Prop. 4.3 (Dict-7). Kind: D. Fidelity: exact -/
noncomputable def undisclosedPress : W → Bool := signOf P X hOf

/-- **T9(i).** The disclosed press is worth the whole `(h, y)` partition.
Source: [[corr-wf13-inventory]] 014 / miri.md Prop. 13.3 ("its value to the agent equals that of learning `h` outright" — here `(h, y)`)
Kind: C (instance of `partValue2_signPartition`)
Fidelity: exact
Hyps: (a) only -/
theorem partValue2_disclosed :
    partValue2 P X (disclosedPress P hOf yOf X) = partValue2 P X (hyOf hOf yOf) :=
  partValue2_signPartition P X (hyOf hOf yOf)

/-- **The keeping agent's information**: the undisclosed press together with the agent's own
`y` (the agent of I13.3 holds its private `y` on both branches; disclosure is a choice about
what the *programmers* see).
Source: miri.md Prop. 13.3, I13.3 ("the agent's private `y` is not in the programmers' `h`")
Kind: D
Fidelity: exact -/
noncomputable def undisclosedPressY : W → Bool × Y := fun w => (undisclosedPress P hOf X w, yOf w)

/-- The disclosed press together with the agent's `y`.
Source: miri.md Prop. 13.3. Kind: D. Fidelity: exact -/
noncomputable def disclosedPressY : W → Bool × Y := fun w => (disclosedPress P hOf yOf X w, yOf w)

/-- **T9(ii).** The undisclosed press, *with the agent's `y` in hand*, is worth at most the
`(h, y)` partition (it is a function of `(h, y)`: Good's theorem, monotone under coarsening).
Source: [[corr-wf13-inventory]] 014 / miri.md Prop. 13.3 ("any function of `h` is worth at most full knowledge of `h`" — to an agent who also holds `y`)
Kind: C (T16's `partValue_mono_coarsen`)
Fidelity: exact
Hyps: (a) only -/
theorem partValue2_undisclosed_with_y_le :
    partValue2 P X (undisclosedPressY P hOf yOf X) ≤ partValue2 P X (hyOf hOf yOf) := by
  have : undisclosedPressY P hOf yOf X =
      (fun p : H × Y => (decide (cellSumX P X hOf p.1 < 0), p.2)) ∘ hyOf hOf yOf := rfl
  rw [this]
  exact partValue_mono_coarsen P (twoOptionV X) _ _

/-- **T9(ii), `y`-blind corollary.** The undisclosed press *alone* is worth at most the `(h, y)`
partition. Weaker than `partValue2_undisclosed_with_y_le` (audit r1): this is the value to an
agent that has forgotten its `y` under `keep`, a coarsening of the source's agent; it follows
from the with-`y` form by a second coarsening (`Prod.fst`).
Source: [[corr-wf13-inventory]] 014 / miri.md Prop. 13.3
Kind: C (T16's `partValue_mono_coarsen`)
Fidelity: weaker: the keeping agent's `y` dropped (implied by the source's claim, not equivalent)
Hyps: (a) only -/
theorem partValue2_undisclosed_le :
    partValue2 P X (undisclosedPress P hOf X) ≤ partValue2 P X (hyOf hOf yOf) := by
  have : undisclosedPress P hOf X =
      ((fun k => decide (cellSumX P X hOf k < 0)) ∘ Prod.fst) ∘ hyOf hOf yOf := rfl
  rw [this]
  exact partValue_mono_coarsen P (twoOptionV X) _ _

/-- The disclosed press with `y` in hand is worth exactly the `(h, y)` partition: `y` adds
nothing on the disclose branch, because the disclosed press is already sufficient.
Source: miri.md Prop. 13.3 (the sufficient-statistic clause). Kind: C. Fidelity: exact -/
theorem partValue2_disclosed_with_y :
    partValue2 P X (disclosedPressY P hOf yOf X) = partValue2 P X (hyOf hOf yOf) := by
  apply le_antisymm
  · have : disclosedPressY P hOf yOf X =
        (fun p : H × Y => (decide (cellSumX P X (hyOf hOf yOf) p < 0), p.2)) ∘ hyOf hOf yOf := rfl
    rw [this]
    exact partValue_mono_coarsen P (twoOptionV X) _ _
  · rw [← partValue2_disclosed P hOf yOf X]
    have : disclosedPress P hOf yOf X = Prod.fst ∘ disclosedPressY P hOf yOf X := rfl
    rw [this]
    exact partValue_mono_coarsen P (twoOptionV X) _ _

/-- **T9, disclosed ≥ undisclosed (the source's comparison).** The keeping agent's information
`(undisclosed press, y)` is worth at most the disclosed press (whose value the agent's `y` does
not raise, `partValue2_disclosed_with_y`).
Source: [[corr-wf13-inventory]] 014 / miri.md Prop. 13.3 ("at least the value of the undisclosed press")
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem partValue2_undisclosed_le_disclosed :
    partValue2 P X (undisclosedPressY P hOf yOf X) ≤ partValue2 P X (disclosedPress P hOf yOf X) := by
  rw [partValue2_disclosed]; exact partValue2_undisclosed_with_y_le P hOf yOf X

/-- **T9, with `y` in hand on both branches.**
Source: miri.md Prop. 13.3. Kind: C. Fidelity: exact
Hyps: (a) only -/
theorem partValue2_undisclosed_with_y_le_disclosed_with_y :
    partValue2 P X (undisclosedPressY P hOf yOf X) ≤ partValue2 P X (disclosedPressY P hOf yOf X) := by
  rw [partValue2_disclosed_with_y]; exact partValue2_undisclosed_with_y_le P hOf yOf X

/-- **T9, disclosed ≥ undisclosed, `y`-blind corollary** (the round-0 statement; audit r1).
Source: miri.md Prop. 13.3. Kind: C. Fidelity: weaker: the keeping agent's `y` dropped
Hyps: (a) only -/
theorem partValue2_undisclosed_le_disclosed_yBlind :
    partValue2 P X (undisclosedPress P hOf X) ≤ partValue2 P X (disclosedPress P hOf yOf X) := by
  rw [partValue2_disclosed]; exact partValue2_undisclosed_le P hOf yOf X

/-- **Disclosure as a first action.** `A₁ = Bool` (`true` = disclose, `false` = keep): same prior
and values, the two rules as `{0, 1}`-valued sensors.
Source: [[corr-wf13-inventory]] 014 / miri.md Prop. 13.3 ("a T-agent under A1 weakly prefers to disclose")
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def disclosure : ThreeStep W Bool TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => P
  press := fun a w => if (if a then disclosedPress P hOf yOf X w else undisclosedPress P hOf X w)
    then 1 else 0
  press_nonneg := fun a w => by split_ifs <;> norm_num
  press_le_one := fun a w => by split_ifs <;> norm_num
  V := fun _ _ => twoOptionV X

/-- With a `{0, 1}`-valued sensor given by a Boolean partition `σ`, the two-option informed value
is the two-option value of the partition `σ`.
Source: miri.md Prop. 13.3 (proof). Kind: L. Fidelity: n/a -/
lemma twoOptionValue_eq_partValue2_of_bool {A₁ : Type*} (S : ThreeStep W A₁ TwoAct) (a : A₁)
    (σ : W → Bool) (hpress : ∀ w, S.press a w = if σ w then 1 else 0) (hμ : S.μ a = P)
    (hV : ∀ o, S.V a o = twoOptionV X) :
    S.twoOptionValue a .cont .stop = partValue2 P X σ := by
  rw [partValue2_eq, Fintype.sum_bool]
  unfold twoOptionValue
  have e1 : S.obsExpect a .press (S.V a .press .cont) = cellSumX P X σ true := by
    unfold obsExpect cellSumX cell
    rw [sum_filter]
    refine sum_congr rfl fun w _ => ?_
    simp only [obsWeight_press, hpress, hμ, hV, twoOptionV]
    split_ifs <;> simp_all
  have e2 : S.obsExpect a .silent (S.V a .silent .cont) = cellSumX P X σ false := by
    unfold obsExpect cellSumX cell
    rw [sum_filter]
    refine sum_congr rfl fun w _ => ?_
    simp only [obsWeight_silent, hpress, hμ, hV, twoOptionV]
    split_ifs <;> simp_all
  have e3 : S.obsExpect a .press (S.V a .press .stop) = 0 := by
    unfold obsExpect; simp [hV, twoOptionV]
  have e4 : S.obsExpect a .silent (S.V a .silent .stop) = 0 := by
    unfold obsExpect; simp [hV, twoOptionV]
  rw [e1, e2, e3, e4]

/-- **T9(iii), `y`-blind corollary** (the round-0 statement; audit r1). The T-agent that sees
only the button weakly prefers to disclose: the parent's `twoOptionValue` under the disclosed
rule is at least that under the undisclosed rule. The source's agent also holds `y`; that
statement is `disclosure_prefers_disclose` below, of which this is a coarsening.
Source: [[corr-wf13-inventory]] 014 / miri.md Prop. 13.3 ("a T-agent under A1 weakly prefers to disclose")
Kind: C
Fidelity: weaker: the keeping agent conditions on the press only, not on `(press, y)`
Hyps: (a) only -/
theorem disclosure_prefers_disclose_yBlind :
    (disclosure P hOf yOf X).twoOptionValue false .cont .stop ≤
      (disclosure P hOf yOf X).twoOptionValue true .cont .stop := by
  rw [twoOptionValue_eq_partValue2_of_bool P X (disclosure P hOf yOf X) false (undisclosedPress P hOf X)
      (fun w => by simp [disclosure]) rfl (fun o => rfl),
    twoOptionValue_eq_partValue2_of_bool P X (disclosure P hOf yOf X) true (disclosedPress P hOf yOf X)
      (fun w => by simp [disclosure]) rfl (fun o => rfl)]
  exact partValue2_undisclosed_le_disclosed_yBlind P hOf yOf X

/-- The silence-and-`L` expectation `E_P[X · 1_¬Pr · 1_L ; a₁]`, the silent twin of the parent's
`pressExpectOn`.
Source: none: infrastructure (the parent has only the press form). Kind: D. Fidelity: n/a -/
noncomputable def silentExpectOn {A₁ A₂ : Type*} [Fintype A₂] [DecidableEq A₂]
    (S : ThreeStep W A₁ A₂) (a : A₁) (L : Finset W) (X : W → ℝ) : ℝ :=
  ∑ w ∈ L, (S.μ a).mass w * (1 - S.press a w) * X w

/-- **The `y`-informed two-option value.** The agent observes the button *and* its own `y`
and best-responds on `{c, s}` to each pair `(o, y₀)`; each term is the product-form
`E[V(b) 1_o 1_{y₀}]`, so no conditional is ever formed. With `yOf` constant this is the
parent's `twoOptionValue`.
Source: miri.md Prop. 13.3, I13.3 (the agent's optimal act "given `(h, y)`" — the agent holds `y` on both branches)
Kind: D
Fidelity: exact -/
noncomputable def twoOptionValueY {A₁ A₂ : Type*} [Fintype A₂] [DecidableEq A₂]
    (S : ThreeStep W A₁ A₂) (a : A₁) (yOf : W → Y) (c s : A₂) : ℝ :=
  ∑ y₀, (max (S.pressExpectOn a (cell yOf y₀) (S.V a .press c))
      (S.pressExpectOn a (cell yOf y₀) (S.V a .press s)) +
    max (silentExpectOn S a (cell yOf y₀) (S.V a .silent c))
      (silentExpectOn S a (cell yOf y₀) (S.V a .silent s)))

/-- With a `{0, 1}`-valued sensor given by a Boolean partition `σ`, the `y`-informed two-option
value is the two-option value of the joint partition `(σ, y)`.
Source: miri.md Prop. 13.3 (proof). Kind: L. Fidelity: n/a -/
lemma twoOptionValueY_eq_partValue2_of_bool {A₁ : Type*} (S : ThreeStep W A₁ TwoAct) (a : A₁)
    (σ : W → Bool) (hpress : ∀ w, S.press a w = if σ w then 1 else 0) (hμ : S.μ a = P)
    (hV : ∀ o, S.V a o = twoOptionV X) :
    twoOptionValueY S a yOf .cont .stop = partValue2 P X (fun w => (σ w, yOf w)) := by
  rw [partValue2_eq, Fintype.sum_prod_type, Fintype.sum_bool, ← sum_add_distrib]
  unfold twoOptionValueY
  refine sum_congr rfl fun y₀ _ => ?_
  have e1 : S.pressExpectOn a (cell yOf y₀) (S.V a .press .cont) =
      cellSumX P X (fun w => (σ w, yOf w)) (true, y₀) := by
    unfold pressExpectOn cellSumX cell
    simp only [sum_filter]
    refine sum_congr rfl fun w _ => ?_
    simp only [hpress, hμ, hV, twoOptionV, Prod.mk.injEq]
    split_ifs <;> simp_all
  have e2 : S.pressExpectOn a (cell yOf y₀) (S.V a .press .stop) = 0 := by
    unfold pressExpectOn; simp [hV, twoOptionV]
  have e3 : silentExpectOn S a (cell yOf y₀) (S.V a .silent .cont) =
      cellSumX P X (fun w => (σ w, yOf w)) (false, y₀) := by
    unfold silentExpectOn cellSumX cell
    simp only [sum_filter]
    refine sum_congr rfl fun w _ => ?_
    simp only [hpress, hμ, hV, twoOptionV, Prod.mk.injEq]
    split_ifs <;> simp_all
  have e4 : silentExpectOn S a (cell yOf y₀) (S.V a .silent .stop) = 0 := by
    unfold silentExpectOn; simp [hV, twoOptionV]
  rw [e1, e2, e3, e4]

/-- **T9(iii).** The T-agent weakly prefers to disclose: its `y`-informed two-option value under
the disclosed rule is at least that under the undisclosed rule — the agent holds its private `y`
on both branches, as in I13.3 (common prior, shared `V`, A1, two-option menu: the source's
caveats, all built into `disclosure`; the agent's `y` supplied by `twoOptionValueY`).
Source: [[corr-wf13-inventory]] 014 / miri.md Prop. 13.3 ("a T-agent under A1 weakly prefers to disclose")
Kind: C
Fidelity: exact (on the `y`-informed value; the source's "value to the agent" given `(h, y)`)
Hyps: (a) only -/
theorem disclosure_prefers_disclose :
    twoOptionValueY (disclosure P hOf yOf X) false yOf .cont .stop ≤
      twoOptionValueY (disclosure P hOf yOf X) true yOf .cont .stop := by
  rw [twoOptionValueY_eq_partValue2_of_bool P yOf X (disclosure P hOf yOf X) false
      (undisclosedPress P hOf X) (fun w => by simp [disclosure]) rfl (fun o => rfl),
    twoOptionValueY_eq_partValue2_of_bool P yOf X (disclosure P hOf yOf X) true
      (disclosedPress P hOf yOf X) (fun w => by simp [disclosure]) rfl (fun o => rfl)]
  exact partValue2_undisclosed_with_y_le_disclosed_with_y P hOf yOf X

end DisclosureHY

/-! ## T11 — the basin polytope (Prop. 14.2) -/

section Basin

variable {W H Y : Type*} [Fintype W] [Fintype H] [DecidableEq H] [DecidableEq Y]
variable (μA P : Distr W) (hOf : W → H) (yOf : W → Y) (X : W → ℝ)

/-- **T11(i), the linear form.** D1 on every `y`-cell for the agent's prior `μA` under the
programmers' rule from `P` is the family of inequalities
`∑_{h₀} ruleVal_P(h₀) · ∑_{w ∈ h₀ ∩ y₀} μA(w) X(w) ≤ 0`, one per `y₀` — each the sum of
`Finset.sum` of `μA.mass` times constants, i.e. weakly linear in `μA` (finitely many weak linear
inequalities; no topology is used for "polytope").
Source: [[corr-wf13-inventory]] 009 / miri.md Prop. 14.2 ("finitely many weak linear inequalities in `μA`")
Kind: L (the `y`-cell decomposition)
Fidelity: variant: one inequality per `y`-cell; the source's per-`(h, y)` family is sufficient, not necessary (`ruleInstance_d1_of_cells`; finding) -/
theorem ruleInstance_d1_iff_linear :
    (∀ y₀, (ruleInstance μA P hOf X).pressExpectOn () (cell yOf y₀) X ≤ 0) ↔
      ∀ y₀, ∑ h₀, ruleVal P hOf X h₀ * jointCellSum μA hOf yOf X h₀ y₀ ≤ 0 := by
  simp only [pressExpectOn_yCell_decomp]

/-- **T11(i), the per-cell sufficient condition.** If every pressed `(h₀, y₀)` cell has
`∑_{w ∈ h₀ ∩ y₀} μA(w) X(w) ≤ 0` then D1 holds on every `y`-cell. This is Prop. 14.2's family;
it is *not* necessary (`WitnessesB.basin_cells_not_necessary`).
Source: [[corr-wf13-inventory]] 009 / miri.md Prop. 14.2 ("`E_{μA}[X | h, y] ≤ 0` on every pressed `h` and every `y`-cell")
Kind: L
Fidelity: weaker: the source's "iff" holds only in this direction (finding)
Hyps: (a) only -/
theorem ruleInstance_d1_of_cells
    (hcells : ∀ h₀ y₀, cellSumX P X hOf h₀ < 0 → jointCellSum μA hOf yOf X h₀ y₀ ≤ 0) (y₀ : Y) :
    (ruleInstance μA P hOf X).pressExpectOn () (cell yOf y₀) X ≤ 0 := by
  rw [pressExpectOn_yCell_decomp]
  refine sum_nonpos fun h₀ _ => ?_
  unfold ruleVal
  split_ifs with h
  · rw [one_mul]; exact hcells h₀ y₀ h
  · rw [zero_mul]

omit [Fintype H] in
/-- The joint cell sum moves by less than `|S|·δ·M` when the prior moves by less than `δ`
pointwise and `|X| ≤ M`.
Source: miri.md Prop. 14.2 (proof: "linearity and continuity"). Kind: L. Fidelity: n/a -/
lemma jointCellSum_sub_le {M δ : ℝ} (hX : ∀ w, |X w| ≤ M)
    (hnear : ∀ w, |μA.mass w - P.mass w| < δ) (h₀ : H) (y₀ : Y) :
    jointCellSum μA hOf yOf X h₀ y₀ - jointCellSum P hOf yOf X h₀ y₀ ≤
      ((cell yOf y₀).filter (hOf · = h₀)).card * (δ * M) := by
  unfold jointCellSum
  rw [← sum_sub_distrib]
  calc ∑ w ∈ (cell yOf y₀).filter (hOf · = h₀), (μA.mass w * X w - P.mass w * X w)
      ≤ ∑ w ∈ (cell yOf y₀).filter (hOf · = h₀), δ * M := by
        refine sum_le_sum fun w _ => ?_
        rw [← sub_mul]
        calc (μA.mass w - P.mass w) * X w ≤ |(μA.mass w - P.mass w) * X w| := le_abs_self _
          _ = |μA.mass w - P.mass w| * |X w| := abs_mul _ _
          _ ≤ δ * M := mul_le_mul (hnear w).le (hX w) (abs_nonneg _) (by linarith [hnear w, abs_nonneg (μA.mass w - P.mass w)])
    _ = ((cell yOf y₀).filter (hOf · = h₀)).card * (δ * M) := by rw [sum_const, nsmul_eq_mul]

/-- **T11(iii), the basin has a radius.** Under exact refinement, if every pressed `h`-cell is
strict under `P` with margin `m` (`cellSum_P ≤ −m`) and `|X| ≤ M`, then every agent prior
within `m/(M·|W|)` of `P` pointwise satisfies the per-cell family, hence D1 on every `y`-cell:
an explicit neighbourhood whose radius grows with the programmers' margin.
Source: [[corr-wf13-inventory]] 009 / miri.md Prop. 14.2 ("contains a neighbourhood of `μP` whenever every pressed cell is strict, with width increasing in the margins")
Kind: P
Fidelity: stronger: an explicit radius where the source has "a neighbourhood"
Hyps: (a) only -/
theorem basin_neighbourhood (hRef : ∀ w w', hOf w = hOf w' → yOf w = yOf w') {m M : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hX : ∀ w, |X w| ≤ M)
    (hmargin : ∀ h₀, cellSumX P X hOf h₀ < 0 → cellSumX P X hOf h₀ ≤ -m)
    (hnear : ∀ w, |μA.mass w - P.mass w| < m / (M * Fintype.card W)) (y₀ : Y) :
    (ruleInstance μA P hOf X).pressExpectOn () (cell yOf y₀) X ≤ 0 := by
  refine ruleInstance_d1_of_cells μA P hOf yOf X (fun h₀ y₀ hpress => ?_) y₀
  rcases ((cell yOf y₀).filter (hOf · = h₀)).eq_empty_or_nonempty with hS | ⟨w₁, hw₁⟩
  · unfold jointCellSum; rw [hS, sum_empty]
  · have hcardW : (0 : ℝ) < Fintype.card W := by
      have : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨w₁⟩
      exact_mod_cast this
    have hcardS : (((cell yOf y₀).filter (hOf · = h₀)).card : ℝ) ≤ Fintype.card W := by
      exact_mod_cast card_le_univ _
    have hpert := jointCellSum_sub_le μA P hOf yOf X hX hnear h₀ y₀
    have hP : jointCellSum P hOf yOf X h₀ y₀ ≤ -m := by
      rw [jointCellSum_eq_of_refines hRef hw₁]; exact hmargin h₀ hpress
    have hδ : m / (M * Fintype.card W) * M = m / Fintype.card W := by
      field_simp
    have hbound : (((cell yOf y₀).filter (hOf · = h₀)).card : ℝ) * (m / (M * Fintype.card W) * M) ≤ m := by
      rw [hδ, mul_div_assoc', div_le_iff₀ hcardW]
      exact (mul_le_mul_of_nonneg_right hcardS hm.le).trans_eq (mul_comm _ _)
    linarith

end Basin

end Cleanroom.Corrigibility.CorrThreeStepFacts
