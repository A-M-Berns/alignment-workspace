import Cleanroom.Found.CorrThreeStep.Setting
import Cleanroom.Found.CorrThreeStep.Thresholds
import Cleanroom.Found.CorrThreeStep.TwoState
import Cleanroom.Found.CorrThreeStep.Identities
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.LinearCombination

/-!
# T1 — the joint round as a definition of record

Package `corr-joint-process` (area `corrigibility`). One round of `joint-final.md` S.1–S.2, S.6
over the parent's Setting S (Pattern A of the mandate: enlarge the latent, keep the structure).

* `JointRound Θ Y`: a prior `P : Distr (Θ × Y)` on value hypotheses × the agent's information
  cells, two-point stakes `c, h` through `wrong : Θ → Bool`, and the overseers' sensor
  `press : Θ × Y → ℝ` in `[0, 1]`. The round *is* a `ThreeStep (Θ × Y) Unit TwoAct`
  (`toThreeStep`, `Sh = {stop}`, `V cont = X`, `V stop = 0`).
* Cells `cell i = {ω | ω.2 = i}`; the derived product-form cell quantities `cellMass`,
  `cellErrMass`, `cellRightMass`, `cellPressMass`, `cellPressSum`; **cellwise (i)**
  `cellwiseBelowThreshold i := cellPressSum i ≤ 0` and averaged (i) as the parent's
  `belowThresholdIneq` on the whole space. Cell rates are never ratios: `blind_cellPressSum`
  states the cell sum as `m_R·α·c − m_W·β·h`.
* `cellwise_imp_averaged` (sum of nonpositives) and `cellwise_unit_iff` (on the trivial
  partition cellwise (i) is the parent's predicate) — `L`.
* Blind oversight `blind` (press through `wrong` only, two rates `α, β`); inclusion is
  `Cellwise.lean`'s Pattern B.
* Coverage at S.6's three grades, and **the sealed target** `SealedTarget` (A0 on the value
  marginal across first actions) — the source's own adopted assumption, named, never built in.

What is *not* defined here (mandate T1 traps): legitimacy `L_{t,t+1}` (S.8 "pending"; T9 takes
legitimacy events as given `Finset`s), the C(i)–C(iv) menu of `joint.md` l. 80–108 beyond what a
theorem uses, (i⁺)/(iii)/(iv-*) on the deep algebra (findings).

Sources: `workflow-2026-09-14/dynamics/joint-final.md` S.0–S.8; `dynamics/joint.md` S.3–S.5.
-/

namespace Cleanroom.Corrigibility.CorrJointProcess

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

/-- **The joint round** (`joint-final` S.1–S.2): a prior `P` on `Θ × Y` (value hypothesis ×
the agent's information cell), the two-point stakes `c` (gain when right) and `h` (harm when
wrong) through `wrong : Θ → Bool` (`W = 1[wrong]`), and the overseers' sensor `press ω ∈ [0,1]`.
Blind oversight is `press` depending on `θ` only through `wrong` (`blind`); inclusion lets it
depend on `y` and an overseer signal (`Cellwise.lean`). Positivity of `c, h` and the sign
condition `α ≤ β` are hypotheses of the theorems that need them.
Source: [[corr-wf14-inventory]] 053 / joint-final.md S.1–S.2
Kind: D
Fidelity: exact (one round; `wrong` as a `Bool`-valued predicate on a finite `Θ`)
Hyps: n/a (definition) -/
structure JointRound (Θ Y : Type) [Fintype Θ] [Fintype Y] where
  /-- the prior on (value hypothesis, information cell) -/
  P : Distr (Θ × Y)
  /-- the agent's plan is wrong under `θ` -/
  wrong : Θ → Bool
  /-- gain when right -/
  c : ℝ
  /-- harm when wrong -/
  h : ℝ
  /-- the overseers' press rate `P(Pr | θ, y)` -/
  press : Θ × Y → ℝ
  press_nonneg : ∀ ω, 0 ≤ press ω
  press_le_one : ∀ ω, press ω ≤ 1

namespace JointRound

variable {Θ Y : Type} [Fintype Θ] [Fintype Y] [DecidableEq Y] (R : JointRound Θ Y)

/-- The two-point decision variable `X(θ) = c` when right, `−h` when wrong.
Source: [[corr-wf14-inventory]] 053 / joint-final.md S.1 ("two-point stakes")
Kind: D
Fidelity: exact -/
def X (θ : Θ) : ℝ := if R.wrong θ then -R.h else R.c

/-- `X` read on the joint world (a function of `θ` alone).
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def Xω (ω : Θ × Y) : ℝ := R.X ω.1

/-- The round's value: continuing pays `X`, stopping pays `0`.
Source: [[corr-wf14-inventory]] 053 / joint-final.md S.2 (`X_t := V(a, cont) − V(a, sh)`)
Kind: D
Fidelity: exact -/
def V : TwoAct → Θ × Y → ℝ
  | .cont, ω => R.X ω.1
  | .stop, _ => 0

/-- **The round is a Setting S instance**: `Ω = Θ × Y`, one first action, `Sh = {stop}`, the
parent's `press` and `V`.
Source: [[corr-wf14-inventory]] 053 / joint-final.md S.2; mandate Pattern A
Kind: D
Fidelity: exact -/
noncomputable def toThreeStep : ThreeStep (Θ × Y) Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => R.P
  press := fun _ => R.press
  press_nonneg := fun _ => R.press_nonneg
  press_le_one := fun _ => R.press_le_one
  V := fun _ _ => R.V

/-- A1 holds on the round by construction. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toThreeStep_A1 : R.toThreeStep.A1 := fun _ _ _ _ _ => rfl

/-- The parent's two-option variable on the round is `X`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Xo_eq (o : Obs) : R.toThreeStep.Xo () o .cont .stop = R.Xω := by
  funext ω; simp [ThreeStep.Xo, toThreeStep, V, Xω]

/-- The information cell `i`: the worlds with `y = i`.
Source: [[corr-wf14-inventory]] 053 / joint.md S.3 ("the partition by `y_t`")
Kind: D
Fidelity: exact -/
def cell (_R : JointRound Θ Y) (i : Y) : Finset (Θ × Y) := univ.filter (fun ω => ω.2 = i)

/-- The mass of cell `i`. Source: joint.md S.3. Kind: D. Fidelity: exact -/
noncomputable def cellMass (i : Y) : ℝ := ∑ ω ∈ R.cell i, R.P.mass ω

/-- The error mass of cell `i`: `P(y = i, W = 1)` (product form of `ε_{t,i} · P(y = i)`).
Source: [[corr-wf14-inventory]] 053 / joint.md S.3 (`ε_{t,i}`)
Kind: D
Fidelity: exact (mass, not ratio) -/
noncomputable def cellErrMass (i : Y) : ℝ :=
  ∑ ω ∈ R.cell i, if R.wrong ω.1 then R.P.mass ω else 0

/-- The right mass of cell `i`: `P(y = i, W = 0)`. Source: joint.md S.3. Kind: D. Fidelity: exact -/
noncomputable def cellRightMass (i : Y) : ℝ :=
  ∑ ω ∈ R.cell i, if R.wrong ω.1 then 0 else R.P.mass ω

/-- The press mass of cell `i`: `P(Pr, y = i)` (the parent's `pressMassOn`).
Source: [[corr-wf14-inventory]] 054 / joint.md C(i-R) ("cells with `P(Pr | i) > 0`")
Kind: D
Fidelity: exact -/
noncomputable def cellPressMass (i : Y) : ℝ := R.toThreeStep.pressMassOn () (R.cell i)

/-- The press-weighted cell sum `Z_i = E[X · 1_Pr · 1_{y = i}]` (the parent's `pressExpectOn`);
the corpus's `Z_{t,a,i}`.
Source: [[corr-wf14-inventory]] 054 / joint.md P.7 (`Z_{t+1,a,i}`)
Kind: D
Fidelity: exact -/
noncomputable def cellPressSum (i : Y) : ℝ := R.toThreeStep.pressExpectOn () (R.cell i) R.Xω

/-- **Cellwise (i)** in cell `i`: `E[X · 1_Pr · 1_{y = i}] ≤ 0` (product form; vacuous on a
null-press cell, content at `0 < cellPressMass i`). The corpus's (i-R) at the universal grade.
Source: [[corr-wf14-inventory]] 054 / joint.md C(i-R); joint-final.md Prop. 1
Kind: D
Fidelity: exact (denominator-free)
Hyps: n/a (definition) -/
def cellwiseBelowThreshold (i : Y) : Prop := R.cellPressSum i ≤ 0

/-- **Averaged (i)**: the parent's below-threshold inequality on the whole space.
Source: [[corr-wf14-inventory]] 054 / joint.md C(i-R) ("averaged grade")
Kind: D
Fidelity: exact -/
def averagedBelowThreshold : Prop := R.toThreeStep.belowThresholdIneq () R.Xω

/-- The cell sum unfolded. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellPressSum_eq (i : Y) :
    R.cellPressSum i = ∑ ω ∈ R.cell i, R.P.mass ω * R.press ω * R.X ω.1 := rfl

/-- The cell press mass unfolded. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellPressMass_eq (i : Y) : R.cellPressMass i = ∑ ω ∈ R.cell i, R.P.mass ω * R.press ω := rfl

/-- Cell masses are nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellMass_nonneg (i : Y) : 0 ≤ R.cellMass i := sum_nonneg fun ω _ => R.P.nonneg ω

/-- Cell error masses are nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellErrMass_nonneg (i : Y) : 0 ≤ R.cellErrMass i :=
  sum_nonneg fun ω _ => by split_ifs <;> simp [R.P.nonneg ω]

/-- Cell right masses are nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellRightMass_nonneg (i : Y) : 0 ≤ R.cellRightMass i :=
  sum_nonneg fun ω _ => by split_ifs <;> simp [R.P.nonneg ω]

/-- A cell's mass splits into its error and right masses. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellMass_eq_add (i : Y) : R.cellMass i = R.cellErrMass i + R.cellRightMass i := by
  unfold cellMass cellErrMass cellRightMass
  rw [← sum_add_distrib]
  exact sum_congr rfl fun ω _ => by split_ifs <;> ring

/-- The error mass is at most the cell mass. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellErrMass_le_cellMass (i : Y) : R.cellErrMass i ≤ R.cellMass i := by
  rw [cellMass_eq_add]; linarith [R.cellRightMass_nonneg i]

/-- **The cells partition the press expectation**: `∑_i Z_i = E[X · 1_Pr]`.
Source: [[corr-wf14-inventory]] 054 / joint-final.md Prop. 1 ("averaged" is the sum of the cells)
Kind: L
Fidelity: exact -/
lemma sum_cellPressSum : ∑ i, R.cellPressSum i = R.toThreeStep.obsExpect () .press R.Xω := by
  simp only [cellPressSum, pressExpectOn, cell, obsExpect, obsWeight_press]
  exact sum_fiberwise (univ : Finset (Θ × Y)) (fun ω => ω.2)
    (fun ω => R.P.mass ω * R.press ω * R.X ω.1)

/-- **Cellwise (i) implies averaged (i)** (the easy direction of Prop. 1's "averaged does not
imply cellwise": a sum of nonpositives is nonpositive). The converse fails: `Cellwise.e3_*`.
Source: [[corr-wf14-inventory]] 054 / joint-final.md Prop. 1
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem cellwise_imp_averaged (hcell : ∀ i, R.cellwiseBelowThreshold i) :
    R.averagedBelowThreshold := by
  unfold averagedBelowThreshold belowThresholdIneq
  rw [← sum_cellPressSum]
  exact sum_nonpos fun i _ => hcell i

/-- **On the trivial partition cellwise (i) is the parent's predicate.**
Source: [[corr-wf14-inventory]] 053 / mandate T1
Kind: L
Fidelity: exact -/
theorem cellwise_unit_iff (R : JointRound Θ Unit) :
    R.cellwiseBelowThreshold () ↔ R.averagedBelowThreshold := by
  unfold cellwiseBelowThreshold averagedBelowThreshold belowThresholdIneq
  rw [← sum_cellPressSum, Fintype.sum_unique]

/-- **Averaged (i) is `Δ₋ ≥ 0` on the round**, hence D1 for the part-best pair (parent).
Source: [[corr-wf14-inventory]] 054 / filler.md F2(iv) on the round
Kind: L
Fidelity: exact -/
theorem averaged_iff_deltaMinus_nonneg :
    R.averagedBelowThreshold ↔ 0 ≤ R.toThreeStep.deltaMinus () .cont .stop := by
  unfold averagedBelowThreshold belowThresholdIneq deltaMinus
  rw [R.Xo_eq]
  constructor <;> intro H <;> linarith

/-! ## Blind oversight: two rates -/

/-- **Blind oversight**: the overseers press at rate `α` when the agent is right and `β` when
wrong, whatever the agent's cell — `joint.md`'s cell-independent `(α_t, β_t)`.
Source: [[corr-wf14-inventory]] 053 / joint-final.md S.1 ("overseers blind to the agent's cell")
Kind: D
Fidelity: exact -/
noncomputable def blind (P : Distr (Θ × Y)) (wrong : Θ → Bool) (c h α β : ℝ)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) : JointRound Θ Y where
  P := P
  wrong := wrong
  c := c
  h := h
  press := fun ω => if wrong ω.1 then β else α
  press_nonneg := fun ω => by
    show 0 ≤ (if wrong ω.1 then β else α)
    split_ifs; exacts [hβ.1, hα.1]
  press_le_one := fun ω => by
    show (if wrong ω.1 then β else α) ≤ 1
    split_ifs; exacts [hβ.2, hα.2]

/-- **The cell sum of a blind round in product form**: `Z_i = m_R(i)·α·c − m_W(i)·β·h` — the
cell rates `α_i = α`, `β_i = β` never appear as ratios.
Source: [[corr-wf14-inventory]] 054 / joint.md P.1 (`E[X 1_Pr]` per cell)
Kind: L
Fidelity: exact -/
lemma blind_cellPressSum (P : Distr (Θ × Y)) (wrong : Θ → Bool) (c h α β : ℝ) (hα hβ) (i : Y) :
    (blind P wrong c h α β hα hβ).cellPressSum i =
      (blind P wrong c h α β hα hβ).cellRightMass i * α * c -
        (blind P wrong c h α β hα hβ).cellErrMass i * β * h := by
  simp only [cellPressSum_eq, cellRightMass, cellErrMass, blind, X, sum_mul, ← sum_sub_distrib]
  exact sum_congr rfl fun ω _ => by split_ifs <;> ring

/-! ## Coverage at S.6's three grades -/

/-- **Representational coverage** of `θ`: the value marginal gives `θ` positive mass.
Source: [[corr-wf14-inventory]] 053 / joint-final.md S.6 ("`H_s ∈ supp P_t` on the value marginal")
Kind: D
Fidelity: weaker: the "`V_θ` correctly represented on every outcome" clause has no finite-model
counterpart (the round has one `V`) -/
def RepresentationalCoverage (θ : Θ) : Prop := 0 < ∑ y, R.P.mass (θ, y)

/-- The estimated gain `G = (1 − ε)c − εh` of a two-point plan action against a benign default
worth `0`.
Source: [[corr-wf14-inventory]] 060 / joint-final.md P.5″
Kind: D
Fidelity: exact -/
noncomputable def planGain (ε c h : ℝ) : ℝ := (1 - ε) * c - ε * h

/-- **Knowledge coverage at tolerance `δ`**: `|G − G°| ≤ δ`, `G°` the true gain.
Source: [[corr-wf14-inventory]] 053 / joint-final.md S.6
Kind: D
Fidelity: exact -/
def KnowledgeCoverage (δ G Gtrue : ℝ) : Prop := |G - Gtrue| ≤ δ

/-- **Harm coverage at tolerance `δ`** of an information action: `|η̂ − η| ≤ δ`.
Source: [[corr-wf14-inventory]] 053 / joint-final.md S.6
Kind: D
Fidelity: exact -/
def HarmCoverage (δ ηhat η : ℝ) : Prop := |ηhat - η| ≤ δ

end JointRound

/-! ## The sealed target, disclosed -/

/-- **The sealed target** (`joint-final` S.1: the humans' values `H_t` are not moved by the
agent — "adopted, not derived", leaky in three named ways). In a round with several first
actions this is A0 restricted to the value marginal: the `Θ`-marginal of the prior does not
depend on the first action. A named hypothesis of every theorem that uses it, never a field.
Source: [[corr-wf14-inventory]] 053 / joint-final.md S.1 ("Human values as a moving target, sealed")
Kind: D
Fidelity: exact (the seal's finite-model shadow; the three leaks are findings)
Hyps: n/a (definition) -/
def SealedTarget {Θ Y A₁ A₂ : Type} [Fintype Θ] [Fintype Y] [Fintype A₂] [DecidableEq A₂]
    (S : ThreeStep (Θ × Y) A₁ A₂) : Prop :=
  ∀ a a' : A₁, ∀ θ : Θ, ∑ y, (S.μ a).mass (θ, y) = ∑ y, (S.μ a').mass (θ, y)

/-- A0 (the whole prior independent of the first action) implies the sealed target.
Source: [[corr-wf14-inventory]] 053 / joint-final.md S.1; filler.md F4 (A0)
Kind: L
Fidelity: exact -/
theorem sealedTarget_of_A0 {Θ Y A₁ A₂ : Type} [Fintype Θ] [Fintype Y] [Fintype A₂] [DecidableEq A₂]
    (S : ThreeStep (Θ × Y) A₁ A₂) (h : S.A0) : SealedTarget S := fun a a' θ => by
  rw [h a a']

end Cleanroom.Corrigibility.CorrJointProcess
