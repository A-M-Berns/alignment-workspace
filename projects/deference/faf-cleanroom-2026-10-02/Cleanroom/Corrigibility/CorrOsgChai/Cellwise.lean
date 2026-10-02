import Cleanroom.Corrigibility.CorrOsgChai.FileDeletion
import Cleanroom.Found.CorrThreeStep.TwoState

/-!
# The cellwise three-step model: K1–K5 per observation, refinement, and the File Deletion cells
(D5, T11, T7(e), T12's counter-model)

Package `corr-osg-chai`. **D5**: a `ThreeStep` whose world is a product `Ω₀ × ΩA` with the agent
observing the second coordinate. The cellwise product-form quantities `cellExpect a oA o X =
∑_{ω.2 = oA} μ ω · P(o | ω) · X ω` — never a conditional distribution with a `/` — give the
per-cell predicates `CellBelow`, `CellAbove`, and `CellwiseBelow`/`CellwiseAbove` (K5).

* **T11(a)** `belowThresholdIneq_of_cellwise`, `aboveThresholdIneq_of_cellwise`: the aggregate
  inequality is the sum of the cells, so cellwise ⇒ aggregate.
* **T11(b)** the converse fails — **Taylor's brain-state instance** `taylor`: `P(g) = 4/5`,
  `X = ±1`, three brain states with `P(H | b) = (1/10, 4/5, 1/10)`, `P(H | g) = (9/10, 1/50, 2/25)`,
  press iff `H ∈ {h₂, h₃}`: the aggregate `E[X 1_Pr] = −1/10 ≤ 0` holds but the `h₃` cell has
  `E[X 1_{h₃} 1_Pr] = 11/250 > 0`. The refinement's value: coarse two-option value `7/10`, refined
  `93/125`, difference `11/250` — Good's theorem paying the agent to refine and then continue on
  `h₃` (`refinedValue` and the general `twoOptionValue_le_refinedValue`).
* **T7(e)** the File Deletion Game as a product `ThreeStep` (`fileDeletionTS`): on cell `L` both
  clauses fail (`3/4`, `−1/4`), on cell `M` both hold (`−5/4`, `5/4`), while the *aggregate*
  clauses hold (`−1/2 ≤ 0 ≤ 1`) — a second converse failure, and K5's per-cell form failing on
  `L`. Standalone, cell `L` is `twoState (1/2) 1 0 3 1` (the inverted sensor `α_L = 1, β_L = 0`):
  `¬ belowThresholdIneq` (`3/2`), `¬ aboveThresholdIneq` (`−1/2`), the dictionary optimum
  continues on a press (`twoOptionValue = 3/2`, `voiButton2 = 1/2`), and **`¬ D1At`** — the
  counter-model of T12's refutation row: the agent's model is the true kernel by construction,
  the press reveals the version (`posteriorPress wrong = 0`, `posteriorPress right = 1` at press
  mass `1/2`: accuracy-increasing), and continuing is press-posterior-optimal. Cell `M` is
  `twoState (1/2) 0 1 5 5` with both clauses holding and `D1At`. The identification of the
  product model's cells with the standalone cells is a lemma (`fileDeletionTS_cells_eq_half`:
  each cell expectation is half the standalone one), and its press is the OPP's human policy
  (`fileDeletionTS_press_eq_opp`). The whole game, as theorems about `fileDeletionTS`
  (`fileDeletionTS_values`): the cell-aware two-option agent (`refinedValue`) is worth `2`, the
  cell-blind one `1`, the prior `1/2` — VOI `3/2` and `1/2` respectively.
* **K3** as a theorem is `corr-three-step`'s `twoState_alpha_le_beta_of_both` (cited, no new row).

Sources: `workflow-2026-09-14/followup/detection.md` R1, R7 (K5); `workflow-2026-09-13/critique/
taylor.md` §2.2 (`taylor-scratch/refine_check.py`); `critique/chai.md` §2.4.
-/

namespace Cleanroom.Corrigibility.CorrOsgChai

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

/-! ## D5: the cellwise model -/

section Cell

variable {Ω₀ ΩA A₁ A₂ : Type*} [Fintype Ω₀] [Fintype ΩA] [DecidableEq ΩA] [Fintype A₂]
  [DecidableEq A₂]
variable (S : Cleanroom.Found.CorrThreeStep.ThreeStep (Ω₀ × ΩA) A₁ A₂)

/-- **The cellwise product-form expectation** `E_P[X · 1_o · 1_{oA} ; a₁] = ∑_{ω.2 = oA} μ(ω) P(o | ω) X(ω)`:
the restriction of the joint to the agent's observation cell, no conditional distribution, no
division.
Source: [[corr-wf14-inventory]] 015 / detection.md R7 K5 ("conditional on the agent's
observation, for each `oA` of positive probability")
Kind: D
Fidelity: exact (product form) -/
noncomputable def cellExpect (a : A₁) (oA : ΩA) (o : Obs) (X : Ω₀ × ΩA → ℝ) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω : Ω₀ × ΩA => ω.2 = oA), (S.μ a).mass ω * S.obsWeight a o ω * X ω

/-- **The below-threshold inequality on cell `oA`**: `E_P[X 1_Pr 1_{oA}] ≤ 0` (K1 on the cell).
Source: detection.md R7 K5
Kind: D
Fidelity: exact -/
def CellBelow (a : A₁) (oA : ΩA) (X : Ω₀ × ΩA → ℝ) : Prop := cellExpect S a oA .press X ≤ 0

/-- **The above-threshold inequality on cell `oA`**: `0 ≤ E_P[X 1_¬Pr 1_{oA}]` (K2 on the cell).
Source: detection.md R7 K5
Kind: D
Fidelity: exact -/
def CellAbove (a : A₁) (oA : ΩA) (X : Ω₀ × ΩA → ℝ) : Prop := 0 ≤ cellExpect S a oA .silent X

/-- **K5, below half**: the below-threshold inequality holds on every cell.
Source: detection.md R7 K5
Kind: D
Fidelity: exact -/
def CellwiseBelow (a : A₁) (X : Ω₀ × ΩA → ℝ) : Prop := ∀ oA, CellBelow S a oA X

/-- **K5, above half**: the above-threshold inequality holds on every cell.
Source: detection.md R7 K5
Kind: D
Fidelity: exact -/
def CellwiseAbove (a : A₁) (X : Ω₀ × ΩA → ℝ) : Prop := ∀ oA, CellAbove S a oA X

/-- The aggregate product-form expectation is the sum of the cells.
Source: none: infrastructure (fibrewise sum). Kind: L. Fidelity: n/a -/
lemma obsExpect_eq_sum_cellExpect (a : A₁) (o : Obs) (X : Ω₀ × ΩA → ℝ) :
    S.obsExpect a o X = ∑ oA, cellExpect S a oA o X := by
  unfold obsExpect cellExpect
  rw [sum_fiberwise univ (fun ω : Ω₀ × ΩA => ω.2)]

/-- **T11(a), below**: cellwise K1 implies the aggregate below-threshold inequality.
Source: [[corr-wf14-inventory]] 015 / detection.md R7 K5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem belowThresholdIneq_of_cellwise (a : A₁) (X : Ω₀ × ΩA → ℝ) (h : CellwiseBelow S a X) :
    S.belowThresholdIneq a X := by
  unfold belowThresholdIneq
  rw [obsExpect_eq_sum_cellExpect]
  exact sum_nonpos fun oA _ => h oA

/-- **T11(a), above**: cellwise K2 implies the aggregate above-threshold inequality.
Source: [[corr-wf14-inventory]] 015 / detection.md R7 K5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem aboveThresholdIneq_of_cellwise (a : A₁) (X : Ω₀ × ΩA → ℝ) (h : CellwiseAbove S a X) :
    S.aboveThresholdIneq a X := by
  unfold aboveThresholdIneq
  rw [obsExpect_eq_sum_cellExpect]
  exact sum_nonneg fun oA _ => h oA

/-- **The refined two-option value**: the agent sees the press *and* its cell, and best-responds
on each `(cell, observation)` pair.
Source: taylor.md §2.2 (the brain-state refinement); filler.md F4 (two-option menu)
Kind: D
Fidelity: exact -/
noncomputable def refinedValue (a : A₁) (c s : A₂) : ℝ :=
  ∑ oA, (max (cellExpect S a oA .press (S.V a .press c)) (cellExpect S a oA .press (S.V a .press s)) +
    max (cellExpect S a oA .silent (S.V a .silent c)) (cellExpect S a oA .silent (S.V a .silent s)))

/-- **Good's theorem for the cell refinement**: the refined value is at least the coarse
two-option value (a maximum of sums is at most the sum of maxima).
Source: taylor.md §2.2 ("Good's theorem … pays the agent to refine")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem twoOptionValue_le_refinedValue (a : A₁) (c s : A₂) :
    S.twoOptionValue a c s ≤ refinedValue S a c s := by
  unfold twoOptionValue refinedValue
  rw [sum_add_distrib]
  refine add_le_add ?_ ?_
  · rw [obsExpect_eq_sum_cellExpect, obsExpect_eq_sum_cellExpect]
    exact max_le (sum_le_sum fun oA _ => le_max_left _ _) (sum_le_sum fun oA _ => le_max_right _ _)
  · rw [obsExpect_eq_sum_cellExpect, obsExpect_eq_sum_cellExpect]
    exact max_le (sum_le_sum fun oA _ => le_max_left _ _) (sum_le_sum fun oA _ => le_max_right _ _)

end Cell

/-! ## T11(b): Taylor's brain-state instance -/

/-- The joint mass of Taylor's instance: `P(g) = 4/5`, `P(H | g) = (9/10, 1/50, 2/25)`,
`P(H | b) = (1/10, 4/5, 1/10)`; world `(0 = g | 1 = b, brain state)`.
Source: taylor.md §2.2 (`refine_check.py`)
Kind: D
Fidelity: exact -/
noncomputable def taylorMass : Fin 2 → Fin 3 → ℝ := ![![18 / 25, 2 / 125, 8 / 125], ![1 / 50, 4 / 25, 1 / 50]]

/-- Taylor's prior as a FAF `Distr` on `Fin 2 × Fin 3`.
Source: taylor.md §2.2
Kind: D
Fidelity: exact -/
noncomputable def taylorPrior : Distr (Fin 2 × Fin 3) where
  mass ω := taylorMass ω.1 ω.2
  nonneg ω := by
    obtain ⟨i, j⟩ := ω
    fin_cases i <;> fin_cases j <;> simp [taylorMass] <;> norm_num
  sum_eq_one := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_three]
    simp [taylorMass]
    norm_num

/-- **Taylor's instance** as a product `ThreeStep`: the press is the thresholded report
(press iff the brain state is `h₂` or `h₃`), `X = +1` on `g`, `−1` on `b`, stop worth `0`.
Source: taylor.md §2.2
Kind: D
Fidelity: exact -/
noncomputable def taylor : Cleanroom.Found.CorrThreeStep.ThreeStep (Fin 2 × Fin 3) Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => taylorPrior
  press := fun _ ω => if ω.2 = 0 then 0 else 1
  press_nonneg := fun _ ω => by split_ifs <;> norm_num
  press_le_one := fun _ ω => by split_ifs <;> norm_num
  V := fun _ _ b ω => if b = .cont then (if ω.1 = 0 then 1 else -1) else 0

/-- Taylor's `X = V(cont) − V(stop)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma taylor_Xo (o : Obs) (ω : Fin 2 × Fin 3) :
    taylor.Xo () o .cont .stop ω = if ω.1 = 0 then 1 else -1 := by
  simp [Xo, taylor]

/-- **T11(b): the aggregate below-threshold inequality holds** (`E[X 1_Pr] = −1/10`).
Source: taylor.md §2.2 (`E[X | Pr] = −5/13`)
Kind: N+
Fidelity: exact -/
theorem taylor_below : taylor.belowThresholdIneq () (taylor.Xo () .press .cont .stop) := by
  unfold belowThresholdIneq obsExpect
  simp only [taylor_Xo]
  simp only [obsWeight_press, taylor, taylorPrior, taylorMass, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three]
  simp
  norm_num

/-- **T11(b): the `h₃` cell fails** (`E[X 1_{h₃} 1_Pr] = 11/250 > 0`): the converse of T11(a) is
false — the aggregate inequality does not survive refinement.
Source: taylor.md §2.2 (`E[X | h₃] = 11/21 > 0`)
Kind: N+
Fidelity: exact -/
theorem taylor_cell_h3_fails : ¬ CellBelow taylor () 2 (taylor.Xo () .press .cont .stop) := by
  unfold CellBelow cellExpect
  simp only [taylor_Xo]
  simp only [sum_filter, obsWeight_press, taylor, taylorPrior, taylorMass, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three]
  simp
  norm_num

/-- **T11(b): the value of the refinement is `11/250`**: coarse two-option value `7/10`, refined
`93/125`.
Source: taylor.md §2.2 (refined `93/125` vs coarse `7/10`)
Kind: N+ (the P row is `twoOptionValue_le_refinedValue`, instantiated here with a strict gap)
Fidelity: exact -/
theorem taylor_refinement_value :
    taylor.twoOptionValue () .cont .stop = 7 / 10 ∧ refinedValue taylor () .cont .stop = 93 / 125 := by
  constructor
  · unfold twoOptionValue obsExpect
    simp only [obsWeight_press, obsWeight_silent, taylor, taylorPrior, taylorMass,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
    simp
    norm_num [max_def]
  · unfold refinedValue cellExpect
    simp only [sum_filter, obsWeight_press, obsWeight_silent, taylor, taylorPrior, taylorMass,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
    simp
    norm_num [max_def]

/-! ## T7(e): the File Deletion cells -/

/-- **The File Deletion Game as a product `ThreeStep`**: world `(version, code)` uniform, the
agent observes the code (second coordinate), the human presses iff the version is `1.0`
(the thresholded report: `E_H[X | 1.0] = −1 < 0 < 2 = E_H[X | 2.0]`), `V(cont) = ua`,
`V(stop) = 0`.
Source: detection.md R1 items 3–4; chai.md §2.4
Kind: D
Fidelity: exact -/
noncomputable def fileDeletionTS : Cleanroom.Found.CorrThreeStep.ThreeStep (Fin 2 × Fin 2) Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => Distr.uniform
  press := fun _ ω => if ω.1 = 0 then 1 else 0
  press_nonneg := fun _ ω => by split_ifs <;> norm_num
  press_le_one := fun _ ω => by split_ifs <;> norm_num
  V := fun _ _ b ω => if b = .cont then fdUa ω.1 ω.2 else 0

/-- `X = ua` on the product model. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma fileDeletionTS_Xo (o : Obs) (ω : Fin 2 × Fin 2) :
    fileDeletionTS.Xo () o .cont .stop ω = fdUa ω.1 ω.2 := by
  simp [Xo, fileDeletionTS]

/-- **On cell `L` both clauses fail** (`E[X 1_Pr 1_L] = 3/4 > 0`, `E[X 1_¬Pr 1_L] = −1/4 < 0`):
K5 fails on `L`.
Source: detection.md R1 item 3 (A2: "both clauses fail on `L`")
Kind: N+
Fidelity: exact -/
theorem fileDeletionTS_cellL_fails :
    ¬ CellBelow fileDeletionTS () 0 (fileDeletionTS.Xo () .press .cont .stop) ∧
      ¬ CellAbove fileDeletionTS () 0 (fileDeletionTS.Xo () .silent .cont .stop) := by
  unfold CellBelow CellAbove cellExpect
  simp only [fileDeletionTS_Xo]
  simp only [sum_filter, obsWeight_press, obsWeight_silent, fileDeletionTS, uniform_mass_fin2_fin2,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [fdUa]

/-- **On cell `M` both clauses hold** (`−5/4 ≤ 0 ≤ 5/4`): K5 holds on `M`.
Source: detection.md R1 item 3 (A2: "both hold on `M`")
Kind: N+
Fidelity: exact -/
theorem fileDeletionTS_cellM_holds :
    CellBelow fileDeletionTS () 1 (fileDeletionTS.Xo () .press .cont .stop) ∧
      CellAbove fileDeletionTS () 1 (fileDeletionTS.Xo () .silent .cont .stop) := by
  unfold CellBelow CellAbove cellExpect
  simp only [fileDeletionTS_Xo]
  simp only [sum_filter, obsWeight_press, obsWeight_silent, fileDeletionTS, uniform_mass_fin2_fin2,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [fdUa]

/-- **The aggregate clauses hold** (`E[X 1_Pr] = −1/2 ≤ 0 ≤ 1 = E[X 1_¬Pr]`): an agent that could
not condition on the code would satisfy both Total Trust clauses — a second instance of the
converse of T11(a) failing (with `fileDeletionTS_cellL_fails`).
Source: detection.md R1 (the cellwise failure is invisible in the aggregate)
Kind: N+
Fidelity: exact -/
theorem fileDeletionTS_aggregate_holds :
    fileDeletionTS.belowThresholdIneq () (fileDeletionTS.Xo () .press .cont .stop) ∧
      fileDeletionTS.aboveThresholdIneq () (fileDeletionTS.Xo () .silent .cont .stop) := by
  unfold belowThresholdIneq aboveThresholdIneq obsExpect
  simp only [fileDeletionTS_Xo]
  simp only [obsWeight_press, obsWeight_silent, fileDeletionTS, uniform_mass_fin2_fin2,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [fdUa]
  norm_num

/-! ## The standalone cells: `twoState (1/2) 1 0 3 1` (L) and `twoState (1/2) 0 1 5 5` (M) -/

/-- `1/2 ∈ [0,1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_half' : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩

/-- `0 ∈ [0,1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_zero' : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩

/-- `1 ∈ [0,1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_one' : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩

/-- **The cell-`L` game standalone**: `wrong = version 2.0` with mass `1/2`, `X = +3` right,
`−1` wrong, the human presses iff version `1.0` — the *inverted* sensor `α_L = 1, β_L = 0`.
Source: detection.md R1 item 3 (A3)
Kind: D
Fidelity: exact -/
noncomputable abbrev cellL := twoState (1 / 2) 1 0 3 1 mem_Icc_half' mem_Icc_one' mem_Icc_zero'

/-- **The cell-`M` game standalone**: `wrong = version 1.0`, `X = +5` right, `−5` wrong, press iff
wrong — the perfect right-sign sensor `α_M = 0, β_M = 1`.
Source: detection.md R1 item 3 (A3)
Kind: D
Fidelity: exact -/
noncomputable abbrev cellM := twoState (1 / 2) 0 1 5 5 mem_Icc_half' mem_Icc_zero' mem_Icc_one'

/-- **On cell `L` both Total Trust clauses fail**: `E[X 1_Pr] = 3/2`, `E[X 1_¬Pr] = −1/2`.
Source: detection.md R1 item 3
Kind: N+
Fidelity: exact -/
theorem cellL_both_fail :
    ¬ cellL.belowThresholdIneq () (cellL.Xo () .press .cont .stop) ∧
      ¬ cellL.aboveThresholdIneq () (cellL.Xo () .silent .cont .stop) := by
  unfold belowThresholdIneq aboveThresholdIneq
  have h1 : cellL.obsExpect () .press (cellL.Xo () .press .cont .stop) = 3 / 2 := by
    have := twoState_deltaMinus (1 / 2) 1 0 3 1 mem_Icc_half' mem_Icc_one' mem_Icc_zero'
    unfold deltaMinus at this
    linarith
  have h2 : cellL.obsExpect () .silent (cellL.Xo () .silent .cont .stop) = -(1 / 2) := by
    have := twoState_deltaPlus (1 / 2) 1 0 3 1 mem_Icc_half' mem_Icc_one' mem_Icc_zero'
    unfold deltaPlus at this
    linarith
  rw [h1, h2]
  norm_num

/-- **On cell `M` both clauses hold**: `E[X 1_Pr] = −5/2`, `E[X 1_¬Pr] = 5/2`.
Source: detection.md R1 item 3
Kind: N+
Fidelity: exact -/
theorem cellM_both_hold :
    cellM.belowThresholdIneq () (cellM.Xo () .press .cont .stop) ∧
      cellM.aboveThresholdIneq () (cellM.Xo () .silent .cont .stop) := by
  unfold belowThresholdIneq aboveThresholdIneq
  have h1 : cellM.obsExpect () .press (cellM.Xo () .press .cont .stop) = -(5 / 2) := by
    have := twoState_deltaMinus (1 / 2) 0 1 5 5 mem_Icc_half' mem_Icc_zero' mem_Icc_one'
    unfold deltaMinus at this
    linarith
  have h2 : cellM.obsExpect () .silent (cellM.Xo () .silent .cont .stop) = 5 / 2 := by
    have := twoState_deltaPlus (1 / 2) 0 1 5 5 mem_Icc_half' mem_Icc_zero' mem_Icc_one'
    unfold deltaPlus at this
    linarith
  rw [h1, h2]
  norm_num

/-- **T12's counter-model: desideratum 1 fails on cell `L`** — continuing is press-posterior-
optimal (`E[V(cont) 1_Pr] = 3/2 > 0 = E[V(stop) 1_Pr]`), with the agent's model of the press
the true kernel by construction and the press revealing the version
(`cellL_press_reveals_version`). No misspecification, no manipulation, a rational overseer.
Source: chai.md §2.4 reading (b); detection.md R1 item 4
Kind: N+ (the refutation instance of T12)
Fidelity: exact -/
theorem cellL_not_d1At : ¬ cellL.D1At () := by
  rintro ⟨b, hb, hpo⟩
  simp only [twoState, mem_singleton] at hb
  subst hb
  have := hpo .cont
  simp only [obsExpect, obsWeight_press, World.sum_eq, twoState, twoPoint_right, twoPoint_wrong,
    twoPress, twoValue] at this
  norm_num at this

/-- **The press on cell `L` reveals the version** (accuracy-increasing): the press has mass `1/2`
(a genuine event, so the posterior is not the `pressMass = 0` junk value: audit r1 N6), and the
posterior after a press is `δ_{right}` — mass `0` on `wrong` (= version `2.0`), `1` on `right`.
Source: detection.md R1 item 5 ("the update on the press is accuracy-increasing about the world")
Kind: L
Fidelity: exact -/
theorem cellL_press_reveals_version :
    cellL.pressMass () = 1 / 2 ∧ cellL.posteriorPress () .wrong = 0 ∧
      cellL.posteriorPress () .right = 1 := by
  have hm : cellL.pressMass () = 1 / 2 := by rw [twoState_pressMass]; norm_num
  refine ⟨hm, ?_, ?_⟩
  · simp [posteriorPress, twoState, twoPress]
  · rw [posteriorPress, hm]
    simp [twoState, twoPoint_right, twoPress]
    norm_num

/-- **Cell `M` satisfies desideratum 1**: stopping is press-posterior-optimal there.
Source: detection.md R1 item 3
Kind: N+
Fidelity: exact -/
theorem cellM_d1At : cellM.D1At () := by
  refine ⟨.stop, by simp [twoState], fun b' => ?_⟩
  cases b' <;>
    simp only [obsExpect, obsWeight_press, World.sum_eq, twoState, twoPoint_right, twoPoint_wrong,
      twoPress, twoValue] <;> norm_num

/-- **The dictionary optimum's values, per cell**: on `L` the informed agent is worth `3/2`
(continue on a press, stop on silence) with `VOI = 1/2`; on `M` it is worth `5/2` with
`VOI = 5/2`. The whole-game numbers are theorems about `fileDeletionTS` below
(`fileDeletionTS_values`; audit r1 B2 — they were bare arithmetic conjuncts here).
Source: detection.md R1 item 4 (A4, A5)
Kind: N+
Fidelity: exact (per cell) -/
theorem cell_values :
    cellL.twoOptionValue () .cont .stop = 3 / 2 ∧ cellL.voiButton2 () .press .cont .stop = 1 / 2 ∧
      cellM.twoOptionValue () .cont .stop = 5 / 2 ∧ cellM.voiButton2 () .press .cont .stop = 5 / 2 := by
  have hL : cellL.twoOptionValue () .cont .stop = 3 / 2 := by
    simp only [twoOptionValue, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, twoState,
      twoPoint_right, twoPoint_wrong, twoPress, twoValue]
    norm_num [max_def]
  have hM : cellM.twoOptionValue () .cont .stop = 5 / 2 := by
    simp only [twoOptionValue, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, twoState,
      twoPoint_right, twoPoint_wrong, twoPress, twoValue]
    norm_num [max_def]
  refine ⟨hL, ?_, hM, ?_⟩
  · unfold voiButton2
    rw [hL, twoState_twoOptionPriorValue]
    norm_num [max_def]
  · unfold voiButton2
    rw [hM, twoState_twoOptionPriorValue]
    norm_num [max_def]

/-- **The whole game's values, as theorems about `fileDeletionTS`** (audit r1 B2): the cell-aware
two-option agent (`refinedValue`, D5) is worth `2` — detection.md R1 item 4's "paying 2" — the
cell-blind two-option agent is worth `1` (the always-defer payoff of F-16), and the prior value
is `1/2`; so the button's VOI is `2 − 1/2 = 3/2` to the cell-aware agent and `1 − 1/2 = 1/2` to
the cell-blind one. (The three-step agent may override a press, which is why `2` exceeds the
PO-OSG's `7/4`.)
Source: detection.md R1 item 4 (A4, A5: "paying 2", "3/2")
Kind: N+
Fidelity: exact -/
theorem fileDeletionTS_values :
    refinedValue fileDeletionTS () .cont .stop = 2 ∧
      fileDeletionTS.twoOptionValue () .cont .stop = 1 ∧
      fileDeletionTS.twoOptionPriorValue () .press .cont .stop = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold refinedValue cellExpect
    simp only [sum_filter, obsWeight_press, obsWeight_silent, fileDeletionTS,
      uniform_mass_fin2_fin2, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [fdUa]
    norm_num [max_def]
  · unfold twoOptionValue obsExpect
    simp only [obsWeight_press, obsWeight_silent, fileDeletionTS, uniform_mass_fin2_fin2,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [fdUa]
    norm_num [max_def]
  · unfold twoOptionPriorValue priorValue expect
    simp only [fileDeletionTS, uniform_mass_fin2_fin2, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [fdUa]
    norm_num [max_def]

/-- **The product model's press is the OPP's human policy**: `press ω = 1` iff
`![off, on] ω.1 = off` — the thresholded report of the `πH` in `fileDeletion_unique`, not a
separate modelling choice (audit r1 N8).
Source: detection.md R1 item 3; Garber Ex. 4.1 (the OPP's H policy)
Kind: L
Fidelity: exact -/
lemma fileDeletionTS_press_eq_opp (ω : Fin 2 × Fin 2) :
    fileDeletionTS.press () ω =
      if (![HAct.off, .on] : Fin 2 → HAct) ω.1 = .off then 1 else 0 := by
  obtain ⟨r, c⟩ := ω
  fin_cases r <;> simp [fileDeletionTS]

/-- **The product model's cells are the standalone cells at mass `1/2`**: for both observations
the product-form cell expectation of `X` on cell `L` (resp. `M`) is half `cellL`'s (resp.
`cellM`'s) `obsExpect` — so `cellL = twoState (1/2) 1 0 3 1` is a lemma about `fileDeletion`, not
a definition (audit r1 N8).
Source: detection.md R1 item 3 (A3)
Kind: L
Fidelity: exact -/
lemma fileDeletionTS_cells_eq_half (o : Obs) :
    cellExpect fileDeletionTS () 0 o (fileDeletionTS.Xo () o .cont .stop) =
        (1 / 2 : ℝ) * cellL.obsExpect () o (cellL.Xo () o .cont .stop) ∧
      cellExpect fileDeletionTS () 1 o (fileDeletionTS.Xo () o .cont .stop) =
        (1 / 2 : ℝ) * cellM.obsExpect () o (cellM.Xo () o .cont .stop) := by
  cases o
  all_goals
    unfold cellExpect
    simp only [fileDeletionTS_Xo]
    simp only [sum_filter, obsWeight_press, obsWeight_silent, fileDeletionTS,
      uniform_mass_fin2_fin2, Fintype.sum_prod_type, Fin.sum_univ_two, obsExpect, World.sum_eq,
      twoState, twoPoint_right, twoPoint_wrong, twoPress, twoValue, Xo]
    simp [fdUa]
    norm_num

end Cleanroom.Corrigibility.CorrOsgChai
