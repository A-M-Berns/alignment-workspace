import Cleanroom.Corrigibility.CorrJointProcess.Round

/-!
# T2, T3, T8 — cellwise (i): blind failure, inclusion, the refining successor

* **T2 (Prop. 1).** On a blind round the cell `i` *is* the parent's `twoState (ε_i) α β c h`
  (`blind_cellPressSum_eq_twoState`: `Z_i = −P(y = i) · Δ₋(ε_i)`), so cellwise (i) is the
  parent's `Δ₋ ≥ 0` in the cell and its odds / threshold forms follow
  (`blind_cellwise_iff_*`). Averaged does not imply cellwise: the E3 mixture
  (`e3_averaged`, `e3_cellA_overrides`, `e3_cellB_complies`).
* **T3 (Prop. 1′).** Pattern B: overseers who see a refinement `f` of the agent's cell and press
  iff their cell sum is negative (`inclusionRound`). Every cell's press sum is a sum of negative
  sub-cell sums (`inclusion_cellPressSum`), so cellwise (i) holds in every cell
  (`inclusion_cellwise`), strictly where the press has mass (`inclusion_cellPressSum_neg`), and
  a cell with no negative sub-cell has press mass `0` (`inclusion_pressless`: vacuous, not
  violated). Witness `incl_*` (script (E)).
* **T8 (Prop. D4−).** The builder is the mixture over cells; the refined successor's best
  response per cell weakly beats the coarse one (`coarse_le_refined`), strictly when the
  refinement changes a press decision (`coarse_lt_refined_of_split`); on E3 `27/40 > 13/20`
  and the refined successor overrides in cell A.
* **The mixture lemma** (`mixture_cellPressSum`, `mixture_cellwise_iff`) is also Lemma B's
  function-form identity (T13(d)) and Cor. B′'s transport clause (T9(d)): the builder's
  conditional on "successor = `i`" *is* `ρ_i`, so the cell inequality *is* `ρ_i`'s. Kind `L`.

Sources: joint-final.md Props. 1, 1′, D4−, P.1′, P.D4−; joint.md P.7 (E3); adv (E).
-/

namespace Cleanroom.Corrigibility.CorrJointProcess

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

/-- `isWrong : World → Bool`, the two-state `wrong` predicate.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def isWrong : World → Bool
  | .wrong => true
  | .right => false

/-! ## The mixture of cells (Pattern D) -/

section Mixture

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-- **A mixture over cells**: `P(θ, i) = w_i · ρ_i(θ)` for weights `w ≥ 0` summing to `1`. The
builder's belief `P_t = ∑_i w_i ρ_i` of `joint.md` P.7 (E3) and P.D4−; conditioning on the cell
`i` gives `ρ_i` (the successor's belief) by construction.
Source: [[corr-wf14-inventory]] 063 / joint.md P.7 (E3: `P_1 = ½ρ_A + ½ρ_B`)
Kind: D
Fidelity: exact -/
noncomputable def mixture {Θ : Type} [Fintype Θ] (w : Y → ℝ) (ρ : Y → Distr Θ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) : Distr (Θ × Y) where
  mass ω := w ω.2 * (ρ ω.2).mass ω.1
  nonneg ω := mul_nonneg (hw ω.2) ((ρ ω.2).nonneg ω.1)
  sum_eq_one := by
    rw [Fintype.sum_prod_type_right]
    simp only [← mul_sum, Distr.sum_eq_one, mul_one, hw1]

/-- **The blind mixture round**: cells `i` with error rates `ε i`, one blind sensor `(α, β)`,
stakes `(c, h)` — a family of the parent's two-state instances glued by the weights `w`.
Source: [[corr-wf14-inventory]] 054, 063 / joint.md P.7; mandate Pattern D
Kind: D
Fidelity: exact -/
noncomputable def mixtureRound (w : Y → ℝ) (ε : Y → ℝ) (α β c h : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hε : ∀ i, ε i ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) : JointRound World Y :=
  JointRound.blind (mixture w (fun i => twoPoint (ε i) (hε i)) hw hw1) isWrong c h α β hα hβ

variable (w : Y → ℝ) (ε : Y → ℝ) (α β c h : ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
  (hε : ∀ i, ε i ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- Sums over a cell of the mixture reduce to sums over `World`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mixture_sum_cell (i : Y) (F : World × Y → ℝ) :
    ∑ ω ∈ (mixtureRound w ε α β c h hw hw1 hε hα hβ).cell i, F ω = F (.right, i) + F (.wrong, i) := by
  rw [JointRound.cell, sum_filter, Fintype.sum_prod_type_right, sum_eq_single i]
  · rw [World.sum_eq]; simp
  · intro j _ hj; exact sum_eq_zero fun θ _ => by simp [hj]
  · intro hi; exact absurd (mem_univ i) hi

/-- The cell mass of the mixture is its weight. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mixture_cellMass (i : Y) : (mixtureRound w ε α β c h hw hw1 hε hα hβ).cellMass i = w i := by
  unfold JointRound.cellMass; rw [mixture_sum_cell]
  simp [mixtureRound, JointRound.blind, mixture]; ring

/-- The cell error mass of the mixture is `w_i · ε_i`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mixture_cellErrMass (i : Y) :
    (mixtureRound w ε α β c h hw hw1 hε hα hβ).cellErrMass i = w i * ε i := by
  unfold JointRound.cellErrMass; rw [mixture_sum_cell]
  simp [mixtureRound, JointRound.blind, mixture, isWrong]

/-- The cell right mass of the mixture is `w_i · (1 − ε_i)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mixture_cellRightMass (i : Y) :
    (mixtureRound w ε α β c h hw hw1 hε hα hβ).cellRightMass i = w i * (1 - ε i) := by
  unfold JointRound.cellRightMass; rw [mixture_sum_cell]
  simp [mixtureRound, JointRound.blind, mixture, isWrong]

/-- **The mixture's cell sum is minus the weight times the component's `Δ₋`**:
`Z_i = −w_i · Δ₋(twoState (ε_i) α β c h)`. This is Lemma B's function-form transport as the
identity the source says it is (`joint-final` Lemma B: "under function form … the statement is
an identity"): the builder's conditional on cell `i` is `ρ_i`, so the builder's cell inequality
is `ρ_i`'s inequality.
Source: [[corr-wf14-inventory]] 054, 063, 065 / joint-final.md Prop. 1, Lemma B ("downgraded … an identity"), Cor. B′ (transport clause)
Kind: L (the source's own verdict: "Kind S"; recorded as the identity)
Fidelity: exact
Hyps: (a) only -/
theorem mixture_cellPressSum (i : Y) :
    (mixtureRound w ε α β c h hw hw1 hε hα hβ).cellPressSum i =
      -(w i * (twoState (ε i) α β c h (hε i) hα hβ).deltaMinus () .cont .stop) := by
  rw [mixtureRound, JointRound.blind_cellPressSum, twoState_deltaMinus, ← mixtureRound,
    mixture_cellRightMass, mixture_cellErrMass]
  ring

/-- The mixture's cell press mass is `w_i · ((1 − ε_i)α + ε_i β)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mixture_cellPressMass (i : Y) :
    (mixtureRound w ε α β c h hw hw1 hε hα hβ).cellPressMass i = w i * ((1 - ε i) * α + ε i * β) := by
  unfold JointRound.cellPressMass pressMassOn; rw [mixture_sum_cell]
  simp [mixtureRound, JointRound.blind, JointRound.toThreeStep, mixture, isWrong]; ring

/-- **Cellwise (i) on the mixture is `Δ₋ ≥ 0` for the component** (positive weight). With the
parent's `twoState_deltaMinus_nonneg_iff_{odds,threshold,posterior}` this is Prop. 1's three
equivalent forms in the cell.
Source: [[corr-wf14-inventory]] 054 / joint-final.md Prop. 1; joint.md P.1
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem mixture_cellwise_iff (i : Y) (hwi : 0 < w i) :
    (mixtureRound w ε α β c h hw hw1 hε hα hβ).cellwiseBelowThreshold i ↔
      0 ≤ (twoState (ε i) α β c h (hε i) hα hβ).deltaMinus () .cont .stop := by
  unfold JointRound.cellwiseBelowThreshold
  rw [mixture_cellPressSum, neg_nonpos]
  exact ⟨fun H => nonneg_of_mul_nonneg_right H hwi, fun H => mul_nonneg hwi.le H⟩

end Mixture

/-! ## T2 — Prop. 1 on a general blind round -/

section T2

variable {Θ Y : Type} [Fintype Θ] [Fintype Y] [DecidableEq Y]
variable (P : Distr (Θ × Y)) (wrong : Θ → Bool) (c h α β : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- The cell error rate `ε_i = P(W = 1 ∣ y = i)` (derived; junk on a null cell — every theorem
using it carries `0 < cellMass i`).
Source: [[corr-wf14-inventory]] 053 / joint.md S.3 (`ε_{t,i}`)
Kind: D
Fidelity: exact under `0 < cellMass i` -/
noncomputable def JointRound.cellEps (R : JointRound Θ Y) (i : Y) : ℝ := R.cellErrMass i / R.cellMass i

/-- `ε_i ∈ [0, 1]` on a positive-mass cell. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma JointRound.cellEps_mem_Icc (R : JointRound Θ Y) (i : Y) (hm : 0 < R.cellMass i) :
    R.cellEps i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨div_nonneg (R.cellErrMass_nonneg i) hm.le, (div_le_one hm).2 (R.cellErrMass_le_cellMass i)⟩

/-- `P(y = i) · ε_i = P(y = i, W = 1)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma JointRound.cellMass_mul_cellEps (R : JointRound Θ Y) (i : Y) (hm : 0 < R.cellMass i) :
    R.cellMass i * R.cellEps i = R.cellErrMass i := by
  unfold JointRound.cellEps; rw [mul_div_cancel₀ _ hm.ne']

/-- **T2, the identification (Prop. 1).** On a blind round the cell `i` of positive mass is the
parent's `twoState (ε_i) α β c h`: `Z_i = −P(y = i) · Δ₋(ε_i)`.
Source: [[corr-wf14-inventory]] 054 / joint-final.md Prop. 1; joint.md P.1
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem blind_cellPressSum_eq_twoState (i : Y)
    (hm : 0 < (JointRound.blind P wrong c h α β hα hβ).cellMass i) :
    (JointRound.blind P wrong c h α β hα hβ).cellPressSum i =
      -((JointRound.blind P wrong c h α β hα hβ).cellMass i *
        (twoState ((JointRound.blind P wrong c h α β hα hβ).cellEps i) α β c h
          ((JointRound.blind P wrong c h α β hα hβ).cellEps_mem_Icc i hm) hα hβ).deltaMinus
            () .cont .stop) := by
  rw [JointRound.blind_cellPressSum, twoState_deltaMinus]
  have h1 := JointRound.cellMass_mul_cellEps (JointRound.blind P wrong c h α β hα hβ) i hm
  have h2 := JointRound.cellMass_eq_add (JointRound.blind P wrong c h α β hα hβ) i
  linear_combination (α * c + β * h) * h1 - α * c * h2

/-- **T2 (Prop. 1), `Δ₋` form.** In a positive-mass cell of a blind round, cellwise (i) holds iff
`Δ₋(ε_i) ≥ 0` on the cell's two-state instance.
Source: [[corr-wf14-inventory]] 054 / joint-final.md Prop. 1
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem blind_cellwise_iff_deltaMinus (i : Y)
    (hm : 0 < (JointRound.blind P wrong c h α β hα hβ).cellMass i) :
    (JointRound.blind P wrong c h α β hα hβ).cellwiseBelowThreshold i ↔
      0 ≤ (twoState ((JointRound.blind P wrong c h α β hα hβ).cellEps i) α β c h
        ((JointRound.blind P wrong c h α β hα hβ).cellEps_mem_Icc i hm) hα hβ).deltaMinus
          () .cont .stop := by
  unfold JointRound.cellwiseBelowThreshold
  rw [blind_cellPressSum_eq_twoState P wrong c h α β hα hβ i hm, neg_nonpos]
  exact ⟨fun H => nonneg_of_mul_nonneg_right H hm, fun H => mul_nonneg hm.le H⟩

/-- **T2 (Prop. 1), odds form.** `cellwise (i) ⟺ α/β ≤ (ε_i/(1 − ε_i)) · (h/c)` (`ε_i < 1`,
`0 < β`, `0 < c`).
Source: [[corr-wf14-inventory]] 054 / joint-final.md Prop. 1 (third form); joint.md C(i-R)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem blind_cellwise_iff_odds (i : Y)
    (hm : 0 < (JointRound.blind P wrong c h α β hα hβ).cellMass i)
    (hε1 : (JointRound.blind P wrong c h α β hα hβ).cellEps i < 1) (hβ0 : 0 < β) (hc : 0 < c) :
    (JointRound.blind P wrong c h α β hα hβ).cellwiseBelowThreshold i ↔
      α / β ≤ (JointRound.blind P wrong c h α β hα hβ).cellEps i /
        (1 - (JointRound.blind P wrong c h α β hα hβ).cellEps i) * (h / c) := by
  rw [blind_cellwise_iff_deltaMinus P wrong c h α β hα hβ i hm,
    twoState_deltaMinus_nonneg_iff_odds _ _ _ _ _ _ _ _ hε1 hβ0 hc]

/-- **T2 (Prop. 1), threshold form.** `cellwise (i) ⟺ c/(c + h) ≤ P(W ∣ Pr, y = i)`, the
posterior being the parent's `posteriorPress` on the cell's instance.
Source: [[corr-wf14-inventory]] 054 / joint-final.md Prop. 1 (second form)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem blind_cellwise_iff_threshold (i : Y)
    (hm : 0 < (JointRound.blind P wrong c h α β hα hβ).cellMass i)
    (hpm : 0 < (1 - (JointRound.blind P wrong c h α β hα hβ).cellEps i) * α +
      (JointRound.blind P wrong c h α β hα hβ).cellEps i * β) (hch : 0 < c + h) :
    (JointRound.blind P wrong c h α β hα hβ).cellwiseBelowThreshold i ↔
      complianceThreshold c h ≤
        (twoState ((JointRound.blind P wrong c h α β hα hβ).cellEps i) α β c h
          ((JointRound.blind P wrong c h α β hα hβ).cellEps_mem_Icc i hm) hα hβ).posteriorPress
            () .wrong := by
  rw [blind_cellwise_iff_deltaMinus P wrong c h α β hα hβ i hm,
    twoState_deltaMinus_nonneg_iff_threshold _ _ _ _ _ _ _ _ hpm hch]

end T2

/-! ## E3 — averaged (i) without cellwise (i) (witness for T2, T8, T13(d)) -/

section E3

/-- The E3 weights `(½, ½)` are nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma e3_w_nonneg : ∀ i : Bool, (0 : ℝ) ≤ (fun _ : Bool => (1 / 2 : ℝ)) i := fun _ => by norm_num

/-- The E3 weights sum to one. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma e3_w_sum : ∑ i : Bool, (fun _ : Bool => (1 / 2 : ℝ)) i = 1 := by norm_num [Fintype.sum_bool]

/-- The E3 error rates: `1/50` in cell `true` (A), `9/50` in cell `false` (B).
Source: [[corr-wf14-inventory]] 063 / joint.md P.7 (E3)
Kind: D
Fidelity: exact -/
noncomputable def e3Eps : Bool → ℝ := fun b => if b then 1 / 50 else 9 / 50

/-- The E3 rates lie in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma e3Eps_mem : ∀ i, e3Eps i ∈ Set.Icc (0 : ℝ) 1 := fun i => by
  cases i <;> simp [e3Eps] <;> norm_num

/-- `1/10 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_10 : (1 / 10 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `3/5 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_3_5 : (3 / 5 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `1/50 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_50 : (1 / 50 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `1/100 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_100 : (1 / 100 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `1/2 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_half : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- **E3, the round**: two equiprobable cells with `ε = 1/50` and `9/50` (average `1/10`), blind
sensor `(1/10, 3/5)`, `c = 1`, `h = 4`.
Source: [[corr-wf14-inventory]] 063 / joint.md P.7 (E3); script (e)
Kind: D
Fidelity: exact -/
noncomputable def e3 : JointRound World Bool :=
  mixtureRound (fun _ => 1 / 2) e3Eps (1 / 10) (3 / 5) 1 4 e3_w_nonneg e3_w_sum e3Eps_mem
    mem_Icc_1_10 mem_Icc_3_5

/-- **E3: cell A overrides** — `Z_A = 1/40 > 0` (in the cell's own normalisation `1/20`).
Source: [[corr-wf14-inventory]] 054, 063 / joint.md P.7 (E3: "`ρ_A` has `E[Z] = 1/20 > 0`")
Kind: N+
Fidelity: exact (product form: the cell mass `1/2` times the source's `1/20`)
Hyps: (a) only -/
theorem e3_cellA_overrides : e3.cellPressSum true = 1 / 40 := by
  unfold e3; rw [mixture_cellPressSum, twoState_deltaMinus]; simp [e3Eps]; norm_num

/-- **E3: cell B complies** — `Z_B = −7/40` (the source's `−7/20` times the cell mass).
Source: [[corr-wf14-inventory]] 054, 063 / joint.md P.7 (E3)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem e3_cellB_complies : e3.cellPressSum false = -(7 / 40) := by
  unfold e3; rw [mixture_cellPressSum, twoState_deltaMinus]; simp [e3Eps]; norm_num

/-- **E3: averaged (i) holds** — `E[X 1_Pr] = −3/20 ≤ 0` — while cellwise (i) fails in cell A:
Prop. 1's "averaged does not imply cellwise", witnessed.
Source: [[corr-wf14-inventory]] 054 / joint-final.md Prop. 1; joint.md P.7 (E3: `E_{P_1}[Z] = −3/20`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem e3_averaged : e3.averagedBelowThreshold ∧ ¬ e3.cellwiseBelowThreshold true := by
  refine ⟨?_, ?_⟩
  · unfold JointRound.averagedBelowThreshold belowThresholdIneq
    rw [← JointRound.sum_cellPressSum, Fintype.sum_bool, e3_cellA_overrides, e3_cellB_complies]
    norm_num
  · unfold JointRound.cellwiseBelowThreshold; rw [e3_cellA_overrides]; norm_num

/-- **E3, the press-cell sum equals `−3/20`** (the source's number).
Source: joint.md P.7 (E3)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem e3_press_sum : e3.toThreeStep.obsExpect () .press e3.Xω = -(3 / 20) := by
  rw [← JointRound.sum_cellPressSum, Fintype.sum_bool, e3_cellA_overrides, e3_cellB_complies]
  norm_num

/-- **E3, cell A's posterior `6/55 < 1/5`** — the parent's `posteriorPress` on the cell's instance.
Source: joint-final.md Prop. 1′ ("the overseers' posterior after bad news is `6/55 < 1/5`"; the
agent-side number of E3)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem e3_cellA_posterior :
    (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 (e3Eps_mem true) mem_Icc_1_10 mem_Icc_3_5).posteriorPress
      () .wrong = 6 / 55 ∧ (6 / 55 : ℝ) < complianceThreshold 1 4 := by
  rw [twoState_posteriorPress_wrong]; unfold complianceThreshold; norm_num

end E3

/-! ## T3 — Prop. 1′: information inclusion (Pattern B) -/

section T3

variable {Θ Y K : Type} [Fintype Θ] [Fintype Y] [DecidableEq Y] [Fintype K] [DecidableEq K]
variable (P : Distr (Θ × Y)) (wrong : Θ → Bool) (c h : ℝ) (f : Θ × Y → K)

/-- The overseers' cell sum `m_k = ∑_{f ω = k} P(ω) X(θ)` over the worlds they cannot
distinguish (product form of `E[X ∣ f = k] · P(f = k)`).
Source: [[corr-wf14-inventory]] 055 / joint-final.md P.1′ (`m := E[X_t ∣ h_t, y_t]`)
Kind: D
Fidelity: exact (product form) -/
noncomputable def ruleSum (k : K) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => f ω = k), P.mass ω * (if wrong ω.1 then -h else c)

/-- **The inclusion round** (Pattern B): overseers observing `f ω` (their signal and the agent's
cell) who share the prior and press iff their cell sum is negative — a `{0,1}`-valued sensor
derived from the rule, a genuine Setting S instance.
Source: [[corr-wf14-inventory]] 055, 2-009 / joint-final.md Prop. 1′; adv A.0.2
Kind: D
Fidelity: exact -/
noncomputable def inclusionRound : JointRound Θ Y where
  P := P
  wrong := wrong
  c := c
  h := h
  press := fun ω => if ruleSum P wrong c h f (f ω) < 0 then 1 else 0
  press_nonneg := fun ω => by
    show 0 ≤ (if ruleSum P wrong c h f (f ω) < 0 then (1 : ℝ) else 0)
    split_ifs <;> norm_num
  press_le_one := fun ω => by
    show (if ruleSum P wrong c h f (f ω) < 0 then (1 : ℝ) else 0) ≤ 1
    split_ifs <;> norm_num

variable (g : K → Y) (hg : ∀ ω, g (f ω) = ω.2)
include hg

/-- **The cell sum under inclusion is the sum of the negative sub-cell sums.** With the
overseers' partition `f` refining the agent's cells (`g ∘ f = y`),
`Z_i = ∑_{k : g k = i, m_k < 0} m_k` — the tower step of P.1′ in product form.
Source: [[corr-wf14-inventory]] 055 / joint-final.md P.1′
Kind: L
Fidelity: exact
Hyps: (a) `hg`: the overseers see the agent's cell -/
theorem inclusion_cellPressSum (i : Y) :
    (inclusionRound P wrong c h f).cellPressSum i =
      ∑ k, (if g k = i ∧ ruleSum P wrong c h f k < 0 then ruleSum P wrong c h f k else 0) := by
  have h1 : (inclusionRound P wrong c h f).cellPressSum i =
      ∑ ω, (if g (f ω) = i ∧ ruleSum P wrong c h f (f ω) < 0 then
        P.mass ω * (if wrong ω.1 then -h else c) else 0) := by
    rw [JointRound.cellPressSum_eq, JointRound.cell, sum_filter]
    refine sum_congr rfl fun ω _ => ?_
    simp only [inclusionRound, JointRound.X, hg ω]
    by_cases hi : ω.2 = i <;> by_cases hr : ruleSum P wrong c h f (f ω) < 0 <;>
      simp [hi, hr]
  rw [h1, ← sum_fiberwise univ f]
  refine sum_congr rfl fun k _ => ?_
  by_cases hk : g k = i ∧ ruleSum P wrong c h f k < 0
  · rw [if_pos hk, ruleSum]
    refine sum_congr rfl fun ω hω => ?_
    rw [mem_filter] at hω
    rw [hω.2, if_pos hk]
  · rw [if_neg hk]
    refine sum_eq_zero fun ω hω => ?_
    rw [mem_filter] at hω
    rw [hω.2, if_neg hk]

/-- **T3 (Prop. 1′): cellwise (i) is automatic under inclusion.** Every cell's press sum is a
sum of negative terms, hence `≤ 0` — for every cell, every `ε`, no rate condition.
Source: [[corr-wf14-inventory]] 055, 2-009 / joint-final.md Prop. 1′; adv A.0.2
Kind: P (small: the tower step and the sign of the pressed sub-cells)
Fidelity: exact
Hyps: (a) `hg`: the overseers observe the agent's cell (Pattern B); common prior by construction -/
theorem inclusion_cellwise (i : Y) : (inclusionRound P wrong c h f).cellwiseBelowThreshold i := by
  unfold JointRound.cellwiseBelowThreshold
  rw [inclusion_cellPressSum P wrong c h f g hg]
  exact sum_nonpos fun k _ => by split_ifs with hk; exacts [hk.2.le, le_rfl]

/-- **T3, strict**: where the press has positive mass in cell `i`, `Z_i < 0`.
Source: [[corr-wf14-inventory]] 055 / joint-final.md Prop. 1′ ("for every cell `i` with a positive press probability")
Kind: P
Fidelity: exact
Hyps: (a) `hg`; `hpm` names where the strict claim lives -/
theorem inclusion_cellPressSum_neg (i : Y)
    (hpm : 0 < (inclusionRound P wrong c h f).cellPressMass i) :
    (inclusionRound P wrong c h f).cellPressSum i < 0 := by
  rw [inclusion_cellPressSum P wrong c h f g hg]
  -- some world of the cell has positive press mass, so its sub-cell is pressed, i.e. negative
  rw [JointRound.cellPressMass_eq] at hpm
  have hpm' : ∑ ω ∈ (inclusionRound P wrong c h f).cell i, (0 : ℝ) <
      ∑ ω ∈ (inclusionRound P wrong c h f).cell i,
        (inclusionRound P wrong c h f).P.mass ω * (inclusionRound P wrong c h f).press ω := by
    simpa using hpm
  obtain ⟨ω, hω, hpos⟩ := exists_lt_of_sum_lt hpm'
  rw [JointRound.cell, mem_filter] at hω
  have hpress : ruleSum P wrong c h f (f ω) < 0 := by
    by_contra hcon
    have : (inclusionRound P wrong c h f).press ω = 0 := by
      simp only [inclusionRound]; rw [if_neg hcon]
    rw [this, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have hle : ∀ k ∈ (univ : Finset K),
      (if g k = i ∧ ruleSum P wrong c h f k < 0 then ruleSum P wrong c h f k else 0) ≤ 0 :=
    fun k _ => by split_ifs with hk; exacts [hk.2.le, le_rfl]
  have hlt : ∃ k ∈ (univ : Finset K),
      (if g k = i ∧ ruleSum P wrong c h f k < 0 then ruleSum P wrong c h f k else 0) < 0 :=
    ⟨f ω, mem_univ _, by rw [if_pos ⟨by rw [hg ω, hω.2], hpress⟩]; exact hpress⟩
  have := sum_lt_sum hle hlt
  simpa using this

/-- **T3, the vacuous face (N−)**: a cell none of whose sub-cells is negative has press mass
`0` — both derived rates vanish, and cellwise (i) there is vacuous, not violated.
Source: [[corr-wf14-inventory]] 055 / joint-final.md P.1′ ("in a cell so confident that `m ≥ 0` for every `h_t` both are `0`")
Kind: L
Fidelity: exact
Hyps: (a) `hg` -/
theorem inclusion_pressless (i : Y) (hno : ∀ k, g k = i → 0 ≤ ruleSum P wrong c h f k) :
    (inclusionRound P wrong c h f).cellPressMass i = 0 := by
  rw [JointRound.cellPressMass_eq]
  refine sum_eq_zero fun ω hω => ?_
  rw [JointRound.cell, mem_filter] at hω
  have : (inclusionRound P wrong c h f).press ω = 0 := by
    simp only [inclusionRound]
    rw [if_neg (not_lt.2 (hno (f ω) (by rw [hg ω, hω.2])))]
  rw [this, mul_zero]

end T3

/-! ## T8 — Prop. D4−: the refining successor -/

section T8

variable {Θ Y : Type} [Fintype Θ] [Fintype Y] [DecidableEq Y] (R : JointRound Θ Y)

/-- The press-branch value of action `a` in cell `i`: `∑_{y = i} P · press · V(a)`.
Source: [[corr-wf14-inventory]] 064 / joint-final.md P.D4− ("Bayes-optimal policy on a finer partition")
Kind: D
Fidelity: exact -/
noncomputable def JointRound.cellPressValue (i : Y) (a : TwoAct) : ℝ :=
  ∑ ω ∈ R.cell i, R.P.mass ω * R.press ω * R.V a ω

/-- The silence-branch value of action `a` in cell `i`. Source: joint-final.md P.D4−. Kind: D. Fidelity: exact -/
noncomputable def JointRound.cellSilentValue (i : Y) (a : TwoAct) : ℝ :=
  ∑ ω ∈ R.cell i, R.P.mass ω * (1 - R.press ω) * R.V a ω

/-- **The refined successor's value**: the best response per cell on each branch (one decision
per cell), valued by the builder's prior — which is the successor's own value by the mixture
identity.
Source: [[corr-wf14-inventory]] 064 / joint-final.md Prop. D4−, P.D4−
Kind: D
Fidelity: exact -/
noncomputable def JointRound.refinedValue : ℝ :=
  ∑ i, max (R.cellPressValue i .cont) (R.cellPressValue i .stop) +
    ∑ i, max (R.cellSilentValue i .cont) (R.cellSilentValue i .stop)

/-- **The coarse successor's value**: one decision per branch on the average.
Source: [[corr-wf14-inventory]] 064 / joint-final.md Prop. D4−
Kind: D
Fidelity: exact -/
noncomputable def JointRound.coarseValue : ℝ :=
  max (∑ i, R.cellPressValue i .cont) (∑ i, R.cellPressValue i .stop) +
    max (∑ i, R.cellSilentValue i .cont) (∑ i, R.cellSilentValue i .stop)

/-- The coarse value is the parent's two-option informed value `V^free` on the round.
Source: none: infrastructure (bridge). Kind: L. Fidelity: n/a -/
lemma JointRound.coarseValue_eq_twoOptionValue :
    R.coarseValue = R.toThreeStep.twoOptionValue () .cont .stop := by
  unfold JointRound.coarseValue twoOptionValue
  have hp : ∀ a, ∑ i, R.cellPressValue i a = R.toThreeStep.obsExpect () .press (R.toThreeStep.V () .press a) := by
    intro a
    simp only [JointRound.cellPressValue, JointRound.cell, obsExpect, obsWeight_press]
    exact sum_fiberwise (univ : Finset (Θ × Y)) (fun ω => ω.2) _
  have hs : ∀ a, ∑ i, R.cellSilentValue i a = R.toThreeStep.obsExpect () .silent (R.toThreeStep.V () .silent a) := by
    intro a
    simp only [JointRound.cellSilentValue, JointRound.cell, obsExpect, obsWeight_silent]
    exact sum_fiberwise (univ : Finset (Θ × Y)) (fun ω => ω.2) _
  rw [hp, hp, hs, hs]

/-- `max (∑ f) (∑ g) ≤ ∑ max f g`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma max_sum_le_sum_max {ι : Type} (s : Finset ι) (f g : ι → ℝ) :
    max (∑ i ∈ s, f i) (∑ i ∈ s, g i) ≤ ∑ i ∈ s, max (f i) (g i) :=
  max_le (sum_le_sum fun _ _ => le_max_left _ _) (sum_le_sum fun _ _ => le_max_right _ _)

/-- **T8 (Prop. D4−): the builder weakly prefers the refining successor.** A finer partition
admits every coarser policy: `coarseValue ≤ refinedValue`.
Source: [[corr-wf14-inventory]] 064 / joint-final.md Prop. D4−, P.D4−
Kind: C (the partition inequality on each branch; the general form is Blackwell's refinement
monotonicity, `Refines.blackwellLE` in `lit-ddb-frames`, not needed here)
Fidelity: exact
Hyps: (a) only; the builder's conditional on a cell *is* the successor's belief by
`mixture` (function-form reflection by construction — no reflection predicate is defined here) -/
theorem JointRound.coarse_le_refined : R.coarseValue ≤ R.refinedValue :=
  add_le_add (max_sum_le_sum_max _ _ _) (max_sum_le_sum_max _ _ _)

/-- **T8, strict**: if some cell strictly prefers continuing on a press and another strictly
prefers stopping, the refinement changes a decision and the preference is strict.
Source: [[corr-wf14-inventory]] 064 / joint-final.md P.D4− ("strictly when the refinement changes a decision")
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem JointRound.coarse_lt_refined_of_split (i j : Y)
    (hi : R.cellPressValue i .stop < R.cellPressValue i .cont)
    (hj : R.cellPressValue j .cont < R.cellPressValue j .stop) :
    R.coarseValue < R.refinedValue := by
  unfold JointRound.coarseValue JointRound.refinedValue
  have h1 : ∑ k, R.cellPressValue k .cont < ∑ k, max (R.cellPressValue k .cont) (R.cellPressValue k .stop) :=
    sum_lt_sum (fun k _ => le_max_left _ _) ⟨j, mem_univ _, lt_of_lt_of_le hj (le_max_right _ _)⟩
  have h2 : ∑ k, R.cellPressValue k .stop < ∑ k, max (R.cellPressValue k .cont) (R.cellPressValue k .stop) :=
    sum_lt_sum (fun k _ => le_max_right _ _) ⟨i, mem_univ _, lt_of_lt_of_le hi (le_max_left _ _)⟩
  have h3 := max_sum_le_sum_max (univ : Finset Y) (fun k => R.cellSilentValue k .cont)
    (fun k => R.cellSilentValue k .stop)
  have h4 : max (∑ k, R.cellPressValue k .cont) (∑ k, R.cellPressValue k .stop) <
      ∑ k, max (R.cellPressValue k .cont) (R.cellPressValue k .stop) := max_lt h1 h2
  linarith

end T8

/-! ### T8 on E3: `27/40 > 13/20`, and the refined successor overrides in cell A -/

section E3T8

/-- E3's per-cell press values. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma e3_cellPressValue (i : Bool) (a : TwoAct) :
    e3.cellPressValue i a = if a = .cont then e3.cellPressSum i else 0 := by
  unfold JointRound.cellPressValue
  cases a <;> simp [JointRound.cellPressSum_eq, JointRound.V]

/-- E3's per-cell silence values, cell A. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma e3_cellSilentValue_A : e3.cellSilentValue true .cont = 17 / 40 ∧ e3.cellSilentValue true .stop = 0 := by
  unfold JointRound.cellSilentValue e3
  rw [mixture_sum_cell, mixture_sum_cell]
  simp [mixtureRound, JointRound.blind, mixture, JointRound.V, JointRound.X, isWrong, e3Eps]
  norm_num

/-- E3's per-cell silence values, cell B. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma e3_cellSilentValue_B : e3.cellSilentValue false .cont = 9 / 40 ∧ e3.cellSilentValue false .stop = 0 := by
  unfold JointRound.cellSilentValue e3
  rw [mixture_sum_cell, mixture_sum_cell]
  simp [mixtureRound, JointRound.blind, mixture, JointRound.V, JointRound.X, isWrong, e3Eps]
  norm_num

/-- **T8 on E3**: refined `27/40`, coarse `13/20`, strict — and the refined successor continues
on a press in cell A (overrides) where the coarse one stops.
Source: [[corr-wf14-inventory]] 064 / mandate T8 (the numbers recomputed from E3)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem e3_refined_gt_coarse :
    e3.refinedValue = 27 / 40 ∧ e3.coarseValue = 13 / 20 ∧ e3.coarseValue < e3.refinedValue := by
  have hA := e3_cellSilentValue_A
  have hB := e3_cellSilentValue_B
  have hr : e3.refinedValue = 27 / 40 := by
    unfold JointRound.refinedValue
    rw [Fintype.sum_bool, Fintype.sum_bool, e3_cellPressValue, e3_cellPressValue,
      e3_cellPressValue, e3_cellPressValue, hA.1, hA.2, hB.1, hB.2, e3_cellA_overrides,
      e3_cellB_complies]
    simp; norm_num
  have hc : e3.coarseValue = 13 / 20 := by
    unfold JointRound.coarseValue
    rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, e3_cellPressValue,
      e3_cellPressValue, e3_cellPressValue, e3_cellPressValue, hA.1, hA.2, hB.1, hB.2,
      e3_cellA_overrides, e3_cellB_complies]
    simp; norm_num
  exact ⟨hr, hc, by rw [hr, hc]; norm_num⟩

end E3T8

end Cleanroom.Corrigibility.CorrJointProcess
