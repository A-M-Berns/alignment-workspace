import Cleanroom.Found.CorrThreeStep.TwoState
import Cleanroom.Corrigibility.CorrPowerChannel.Evpi

/-!
# `corr-power-channel` — T9: the grip's value to a trusting agent; the accuracy-only anchor

One-shot options `{act, ∅}`, `X : Ω → ℝ` the value of acting over `∅` (stopping normalised to
`0`), an intent kernel `κ : Ω → ℝ` (`P(int | ω)`, `corr-three-step`'s press rate), landing
probability `Γ ∈ [0, 1]`. All quantities in **product form** (no division):
`intGain = ∑ P κ X`, `noIntGain = ∑ P (1 − κ) X`.

* **(a)** `gripValue vFree vForced Γ = (1 − Γ) vFree + Γ vForced` is affine (`gripValue_affine`),
  with `vForced = (noIntGain)⁺` and two models of the free arm: *informed*
  (`vFreeInformed = (intGain)⁺ + (noIntGain)⁺`) and *blind* (`vFreeBlind = (E X)⁺`). The informed
  slope is `−(intGain)⁺ ≤ 0`, zero iff the below-threshold inequality `intGain ≤ 0` holds
  (`informedSlope_eq_zero_iff`; on the two-state instance this *is* `corr-three-step`'s
  `belowThresholdIneq`, `informedSlope_eq_zero_iff_belowThreshold`). The blind slope is
  `−intGain` where the agent would act on its prior (`blindSlope_eq`), positive iff the
  below-threshold inequality holds strictly (`blindSlope_pos_iff`). Corollary
  `repair_incentive_iff`: a positive repair incentive exists (in the blind model) iff Total Trust
  holds strictly — and the informed slope is then `0`: the incentive exists only where the grip is
  the agent's sole route to the information. Witness R1 (`r1_slopes`): `c = 1, h = 4`; informed
  slope `0` at `ε = 1/10`, `−1/20` at `1/50`, `−9/20` uninformative; blind `+3/20` at `1/10`.
* **(b)** `keep_beats_erode_iff` (R5): with the press independent of `ω`, keeping beats eroding
  iff `E[X] < 0` iff `ε_true > c/(c + h)`; cells `(−3/5, −3/2)` at `ε_true = 1/2`, `(1/5, 1/2)` at
  `1/10`. The nine-cell grid of S11 (`s11_grid`): world kernel × model kernel, the agent erodes
  iff Total Trust fails under its *model*; realized values as a table. The "legitimate erosion"
  label on the `(other, other)` cells is the source's under the accuracy-only anchor (withdrawn as
  a definition in S11); here it is a value comparison, nothing more.

Sources: channel-final.md S7 (l. 77), S9 (l. 81), S11 (l. 85), P7 (l. 103);
`channel-scratch/repair_checks.py` R1, R1′, R5, F2; corr-wf14b-030, 032.
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect expect_const

noncomputable section

set_option linter.unusedSectionVars false

section Slopes

variable {Ω : Type} [Fintype Ω]

/-- The intent mass `P(int) = ∑ ω, P ω κ ω`. Source: channel-final.md P7 (l. 103). Kind: D.
Fidelity: exact (product form) -/
def intMass (P : Distr Ω) (κ : Ω → ℝ) : ℝ := ∑ ω, P.mass ω * κ ω

/-- The intent-branch gain `∑ ω, P ω κ ω X ω` (`P(int)·E[X | int]` in product form).
Source: channel-final.md P7 (l. 103). Kind: D. Fidelity: exact -/
def intGain (P : Distr Ω) (κ X : Ω → ℝ) : ℝ := ∑ ω, P.mass ω * κ ω * X ω

/-- The no-intent-branch gain `∑ ω, P ω (1 − κ ω) X ω`.
Source: channel-final.md P7 (l. 103). Kind: D. Fidelity: exact -/
def noIntGain (P : Distr Ω) (κ X : Ω → ℝ) : ℝ := ∑ ω, P.mass ω * (1 - κ ω) * X ω

/-- The two branches sum to the prior expectation. Source: none: infrastructure. Kind: L.
Fidelity: n/a -/
theorem intGain_add_noIntGain (P : Distr Ω) (κ X : Ω → ℝ) :
    intGain P κ X + noIntGain P κ X = expect P X := by
  unfold intGain noIntGain expect
  rw [← sum_add_distrib]
  exact sum_congr rfl fun ω _ => by ring

/-- **The forced arm**: the landing replaces the agent by `∅` on the intent branch; off it the
agent acts on its prior restricted to that branch — value `(noIntGain)⁺`.
Source: channel-final.md P7 (l. 103, "with probability `Γ` the continuation on the intend branch
is the humans'"); `repair_checks.py` R1 (`V_forced`)
Kind: D
Fidelity: exact -/
def vForced (P : Distr Ω) (κ X : Ω → ℝ) : ℝ := max (noIntGain P κ X) 0

/-- **The informed free arm**: the agent observes the intent signal even when the modification
does not land and acts on each branch's posterior — `(intGain)⁺ + (noIntGain)⁺`.
Source: channel-final.md S9 (l. 81, "Informed"); `repair_checks.py` R1 (`V_free_inf`)
Kind: D
Fidelity: exact -/
def vFreeInformed (P : Distr Ω) (κ X : Ω → ℝ) : ℝ := max (intGain P κ X) 0 + max (noIntGain P κ X) 0

/-- **The blind free arm**: the landing is the agent's only access to the humans' information; the
free arm acts on the prior — `(E X)⁺`.
Source: channel-final.md S9 (l. 81, "Blind"); `repair_checks.py` R1 (`V_free_blind`)
Kind: D
Fidelity: exact -/
def vFreeBlind (P : Distr Ω) (X : Ω → ℝ) : ℝ := max (expect P X) 0

/-- **The grip's value** `V(Γ) = (1 − Γ) V_free + Γ V_forced`.
Source: channel-final.md S9 (l. 81, "`V(Γ) = (1 − Γ)V^free + Γ V^forced`, affine")
Kind: D
Fidelity: exact -/
def gripValue (vFree vForced Γ : ℝ) : ℝ := (1 - Γ) * vFree + Γ * vForced

/-- **`V(Γ)` is affine in `Γ`** with slope `V_forced − V_free`.
Source: channel-final.md S9 (l. 81); corr-wf14b-030
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem gripValue_affine (vFree vForced Γ : ℝ) :
    gripValue vFree vForced Γ = vFree + Γ * (vForced - vFree) := by
  unfold gripValue; ring

/-- The informed slope `V_forced − V_free_inf`. Source: channel-final.md S9 (l. 81). Kind: D.
Fidelity: exact -/
def informedSlope (P : Distr Ω) (κ X : Ω → ℝ) : ℝ := vForced P κ X - vFreeInformed P κ X

/-- The blind slope `V_forced − V_free_blind`. Source: channel-final.md S9 (l. 81). Kind: D.
Fidelity: exact -/
def blindSlope (P : Distr Ω) (κ X : Ω → ℝ) : ℝ := vForced P κ X - vFreeBlind P X

/-- **The informed slope is `−(intGain)⁺`** (`−P(int)(E[X | int])⁺` in product form).
Source: channel-final.md S9 (l. 81, the informed display); `repair_checks.py` R1
Kind: L
Fidelity: exact -/
theorem informedSlope_eq (P : Distr Ω) (κ X : Ω → ℝ) :
    informedSlope P κ X = -(max (intGain P κ X) 0) := by
  unfold informedSlope vForced vFreeInformed; ring

/-- **The informed slope is `≤ 0`**: in the informed model the grip is never worth repairing.
Source: channel-final.md S9 (l. 81, "`≤ 0`"); run 2 `joint` Prop. 2 (reported there)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem informedSlope_nonpos (P : Distr Ω) (κ X : Ω → ℝ) : informedSlope P κ X ≤ 0 := by
  rw [informedSlope_eq]
  linarith [le_max_right (intGain P κ X) 0]

/-- **The informed slope is `0` iff the below-threshold inequality holds** (`intGain ≤ 0`, i.e.
`E[X · 1_int] ≤ 0`): the grip is free to leave exactly on the trusted class.
Source: channel-final.md S9 (l. 81, "zero where below-threshold Total Trust holds")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem informedSlope_eq_zero_iff (P : Distr Ω) (κ X : Ω → ℝ) :
    informedSlope P κ X = 0 ↔ intGain P κ X ≤ 0 := by
  rw [informedSlope_eq, neg_eq_zero]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [max_eq_left hc.le] at h
    exact absurd h hc.ne'
  · intro h
    exact max_eq_right h

/-- **The blind slope is `−intGain`** where the agent would act on its prior on both arms
(`0 ≤ E X` and `0 ≤ noIntGain`).
Source: channel-final.md S9 (l. 81, "`∂V/∂Γ = −P(int) E[X | int]`"); `repair_checks.py` R1
Kind: L
Fidelity: exact
Hyps: (a) the two act-on-the-prior conditions, named -/
theorem blindSlope_eq (P : Distr Ω) (κ X : Ω → ℝ) (h1 : 0 ≤ expect P X) (h2 : 0 ≤ noIntGain P κ X) :
    blindSlope P κ X = -(intGain P κ X) := by
  unfold blindSlope vForced vFreeBlind
  rw [max_eq_left h2, max_eq_left h1, ← intGain_add_noIntGain]
  ring

/-- **The blind slope is positive iff the below-threshold inequality holds strictly**
(`intGain < 0`) — a repair incentive exists in the blind model exactly on the strictly trusted
class; it is `≤ 0` iff `0 ≤ intGain` (the inequality's negation, weakly).
Source: channel-final.md S9 (l. 81, "positive under Total Trust"); P7 (l. 103)
Kind: L
Fidelity: exact
Hyps: (a) the act-on-the-prior conditions -/
theorem blindSlope_pos_iff (P : Distr Ω) (κ X : Ω → ℝ) (h1 : 0 ≤ expect P X)
    (h2 : 0 ≤ noIntGain P κ X) : (0 < blindSlope P κ X ↔ intGain P κ X < 0) ∧
      (blindSlope P κ X ≤ 0 ↔ 0 ≤ intGain P κ X) := by
  rw [blindSlope_eq P κ X h1 h2]
  constructor <;> constructor <;> intro h <;> linarith

/-- **The corollary, as the conjunction of the two slope lemmas**: a positive repair incentive
exists in the blind model iff the below-threshold inequality holds strictly, in which case the
informed slope is `0`. "Iff" is over the two models of the free arm, not a quantification over
all models. **Kind L** (repair round 1): the right-hand conjunct `informedSlope = 0` is implied by
the left one (`informedSlope = −(intGain)⁺`), so this is `blindSlope_pos_iff` restated — which
*is* the "iff over the two models": in the blind model the incentive exists exactly where the
informed model makes the grip free. The source's sentence is rendered by the pair
`informedSlope_nonpos` (never positive with another route) and `blindSlope_pos_iff`.
Source: channel-final.md S9 (l. 81, "a positive repair incentive for a physical channel exists
iff the grip is the agent's only route to the information … and Total Trust holds")
Kind: L
Fidelity: exact (over the two models)
Hyps: (a) the act-on-the-prior conditions -/
theorem repair_incentive_iff (P : Distr Ω) (κ X : Ω → ℝ) (h1 : 0 ≤ expect P X)
    (h2 : 0 ≤ noIntGain P κ X) :
    0 < blindSlope P κ X ↔ intGain P κ X < 0 ∧ informedSlope P κ X = 0 := by
  rw [(blindSlope_pos_iff P κ X h1 h2).1, informedSlope_eq_zero_iff]
  constructor
  · intro h; exact ⟨h, h.le⟩
  · intro h; exact h.1

end Slopes

/-! ## The two-state bridge and witness R1 -/

section TwoStateBridge

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- The two-state stakes `X = c` when right, `−h` when wrong (`twoValue c h .cont`).
Source: corr-three-step `twoValue`. Kind: D. Fidelity: exact -/
def twoX (c h : ℝ) : World → ℝ := twoValue c h .cont

/-- **On the two-state instance, `intGain` is `corr-three-step`'s press-branch expectation**:
`intGain (twoPoint ε) (twoPress α β) X = (twoState ε α β c h).obsExpect () .press X`.
Source: none: infrastructure (the bridge the mandate asks for)
Kind: L
Fidelity: exact -/
theorem intGain_eq_obsExpect_press (X : World → ℝ) :
    intGain (twoPoint ε hε) (twoPress α β) X =
      (twoState ε α β c h hε hα hβ).obsExpect () .press X := rfl

/-- **The informed slope vanishes iff `corr-three-step`'s `belowThresholdIneq`** on the two-state
instance.
Source: channel-final.md S9 (l. 81); [[corr-power-channel-mandate]] T9(a) ("cite
`corr-three-step`'s predicate")
Kind: L
Fidelity: exact -/
theorem informedSlope_eq_zero_iff_belowThreshold (X : World → ℝ) :
    informedSlope (twoPoint ε hε) (twoPress α β) X = 0 ↔
      (twoState ε α β c h hε hα hβ).belowThresholdIneq () X := by
  rw [informedSlope_eq_zero_iff]
  rfl

/-- Sums over `World` for the slopes. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem intGain_two (X : World → ℝ) :
    intGain (twoPoint ε hε) (twoPress α β) X = (1 - ε) * α * X .right + ε * β * X .wrong := by
  unfold intGain
  rw [World.sum_eq]
  simp [twoPress]

/-- Sums over `World` for the slopes. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem noIntGain_two (X : World → ℝ) :
    noIntGain (twoPoint ε hε) (twoPress α β) X =
      (1 - ε) * (1 - α) * X .right + ε * (1 - β) * X .wrong := by
  unfold noIntGain
  rw [World.sum_eq]
  simp [twoPress]

/-- Sums over `World` for the slopes. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem expect_two (X : World → ℝ) :
    expect (twoPoint ε hε) X = (1 - ε) * X .right + ε * X .wrong := by
  unfold expect
  rw [World.sum_eq]
  simp

/-- **R1 (N+): the slopes on three kernels at `c = 1`, `h = 4`.** Informed slope `0` at
`(ε, α, β) = (1/10, 1/10, 3/5)` (Total Trust holds), `−1/20` at `(1/50, 1/10, 3/5)` (fails),
`−9/20` at the uninformative `(1/10, 9/10, 9/10)`; the blind slope is `+3/20` at
`(1/10, 1/10, 3/5)` (the develop file's number), where both act-on-the-prior conditions hold.
Source: channel-final.md S9 (l. 81, "`0` at `ε = 1/10` … `−1/20` at `1/50`; `−9/20`
uninformative … `+3/20`"); `repair_checks.py` R1
Kind: N+
Fidelity: exact
Hyps: none -/
theorem r1_slopes :
    informedSlope (twoPoint (1 / 10) (by norm_num)) (twoPress (1 / 10) (3 / 5)) (twoX 1 4) = 0 ∧
      informedSlope (twoPoint (1 / 50) (by norm_num)) (twoPress (1 / 10) (3 / 5)) (twoX 1 4)
        = -(1 / 20) ∧
      informedSlope (twoPoint (1 / 10) (by norm_num)) (twoPress (9 / 10) (9 / 10)) (twoX 1 4)
        = -(9 / 20) ∧
      blindSlope (twoPoint (1 / 10) (by norm_num)) (twoPress (1 / 10) (3 / 5)) (twoX 1 4)
        = 3 / 20 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [informedSlope_eq, intGain_two]; simp [twoX, twoValue]; norm_num
  · rw [informedSlope_eq, intGain_two]; simp [twoX, twoValue]; norm_num
  · rw [informedSlope_eq, intGain_two]; simp [twoX, twoValue]; norm_num
  · rw [blindSlope_eq, intGain_two]
    · simp [twoX, twoValue]; norm_num
    · rw [expect_two]; simp [twoX, twoValue]; norm_num
    · rw [noIntGain_two]; simp [twoX, twoValue]; norm_num

end TwoStateBridge

/-! ## (b) Keeping versus eroding under an `ω`-independent press; the S11 grid -/

/-- The value of keeping the grip when the press is independent of `ω` with rate `a` and the
landing forces `∅` on the press: `(1 − a) · E[X]` (the agent acts on its prior otherwise).
Source: channel-final.md S11 (l. 85, "with the press independent of `ω`"); `repair_checks.py` R5
Kind: D
Fidelity: exact -/
def vKeep (a EX : ℝ) : ℝ := (1 - a) * EX

/-- The value of eroding: the agent acts on its prior, `E[X]`.
Source: `repair_checks.py` R5. Kind: D. Fidelity: exact -/
def vErode (EX : ℝ) : ℝ := EX

/-- **R5/F2′: keeping beats eroding iff `E[X] < 0`** (for a press of positive rate) — a fact
about the agent's reliability coordinate, not a legitimacy criterion.
Source: channel-final.md S11 (l. 85, "keeping beats eroding iff `ε_true > c/(c+h)`")
Kind: L
Fidelity: exact
Hyps: (a) `0 < a` -/
theorem keep_beats_erode_iff {a : ℝ} (ha : 0 < a) (EX : ℝ) : vErode EX < vKeep a EX ↔ EX < 0 := by
  unfold vErode vKeep
  constructor <;> intro h <;> nlinarith

/-- **`E[X] < 0 ⟺ ε_true > c/(c+h)`** for `X = c` on right, `−h` on wrong (`0 < c + h`).
Source: channel-final.md S11 (l. 85, "`ε_true > c/(c+h) = 1/5`")
Kind: L
Fidelity: exact
Hyps: (a) `0 < c + h` -/
theorem ex_neg_iff_threshold {ε c h : ℝ} (hch : 0 < c + h) :
    (1 - ε) * c - ε * h < 0 ↔ c / (c + h) < ε := by
  rw [div_lt_iff₀ hch]
  constructor <;> intro H <;> nlinarith

/-- **R5's cells**: at `c = 1`, `h = 4`, press rate `3/5`: `ε_true = 1/2` gives keep `−3/5`
against erode `−3/2` (keep wins); `ε_true = 1/10` gives keep `1/5` against erode `1/2` (erode wins).
Source: channel-final.md S11 (l. 85, "`−3/5` against `−3/2` at `ε_true = 1/2`; `1/5` against
`1/2` at `1/10`"); `repair_checks.py` R5
Kind: N+
Fidelity: exact
Hyps: none -/
theorem r5_cells :
    vKeep (3 / 5) ((1 - 1 / 2) * 1 - 1 / 2 * 4) = -(3 / 5) ∧
      vErode ((1 - 1 / 2) * 1 - 1 / 2 * 4) = -(3 / 2) ∧
      vKeep (3 / 5) ((1 - 1 / 10) * 1 - 1 / 10 * 4) = 1 / 5 ∧
      vErode ((1 - 1 / 10) * 1 - 1 / 10 * 4) = 1 / 2 := by
  norm_num [vKeep, vErode]

/-- The three kernels of the S11 grid: trusted `(1/10, 3/5)`, compromised `(3/5, 3/5)`, inverted
`(3/5, 1/10)`.
Source: channel-final.md S11 (l. 85). Kind: D. Fidelity: exact -/
def gridKernel : Fin 3 → ℝ × ℝ := ![(1 / 10, 3 / 5), (3 / 5, 3 / 5), (3 / 5, 1 / 10)]

/-- Total Trust under the agent's model kernel `m` (`intGain ≤ 0` at `ε = 1/10`, `c = 1`, `h = 4`).
Source: channel-final.md S11 (l. 85, "the agent erodes iff Total Trust fails under its model")
Kind: D
Fidelity: exact -/
def ttUnderModel (m : Fin 3) : Prop :=
  intGain (twoPoint (1 / 10) (by norm_num)) (twoPress (gridKernel m).1 (gridKernel m).2) (twoX 1 4) ≤ 0

/-- Total Trust holds under the trusted model only. Source: `repair_checks.py` F2. Kind: L.
Fidelity: n/a -/
theorem ttUnderModel_iff (m : Fin 3) : ttUnderModel m ↔ m = 0 := by
  unfold ttUnderModel
  fin_cases m <;> rw [intGain_two] <;> simp [gridKernel, twoX, twoValue] <;> norm_num

open Classical in
/-- **The realized value of the agent's policy** in world kernel `w` under model kernel `m`: keep
(forced value under the world kernel) iff Total Trust holds under the model, else erode (the prior
expectation `1/2`).
Source: channel-final.md S11 (l. 85)
Kind: D
Fidelity: exact -/
def gridValue (w m : Fin 3) : ℝ :=
  if ttUnderModel m then
    vForced (twoPoint (1 / 10) (by norm_num)) (twoPress (gridKernel w).1 (gridKernel w).2) (twoX 1 4)
  else vFreeBlind (twoPoint (1 / 10) (by norm_num)) (twoX 1 4)

/-- The S11 table (rows: world kernel; columns: model kernel).
Source: channel-final.md S11 (l. 85). Kind: D. Fidelity: n/a -/
def gridTable : Fin 3 → Fin 3 → ℝ :=
  ![![13 / 20, 1 / 2, 1 / 2], ![1 / 5, 1 / 2, 1 / 2], ![0, 1 / 2, 1 / 2]]

/-- **S11's nine cells (N+)**: `(trusted, trusted)` keeps and realizes `13/20`; `(trusted, other)`
erodes and realizes `1/2 < 13/20` (the source's "illegitimate erosion"); `(other, other)` erodes
and realizes `1/2` against `1/5` or `0` (the source's "legitimate erosion" under the accuracy-only
anchor); `(other, trusted)` keeps and realizes `1/5` or `0 < 1/2` (over-compliance). The four
verdicts are value comparisons in the table; the labels are the source's.
Source: channel-final.md S11 (l. 85); `repair_checks.py` F2, R5
Kind: N+
Fidelity: exact (the labels are the source's under its withdrawn anchor; see findings)
Hyps: none -/
theorem s11_grid : (∀ w m, gridValue w m = gridTable w m) ∧
    gridTable 0 0 = 13 / 20 ∧ gridTable 0 1 < gridTable 0 0 ∧ gridTable 0 2 < gridTable 0 0 ∧
    gridTable 1 0 < gridTable 1 1 ∧ gridTable 2 0 < gridTable 2 2 ∧
    gridTable 1 0 < gridTable 0 1 ∧ gridTable 2 0 < gridTable 0 1 := by
  have h0 : ttUnderModel 0 := (ttUnderModel_iff 0).2 rfl
  have h1 : ¬ ttUnderModel 1 := by rw [ttUnderModel_iff]; decide
  have h2 : ¬ ttUnderModel 2 := by rw [ttUnderModel_iff]; decide
  have t00 : gridTable 0 0 = 13 / 20 := rfl
  have t01 : gridTable 0 1 = 1 / 2 := rfl
  have t02 : gridTable 0 2 = 1 / 2 := rfl
  have t10 : gridTable 1 0 = 1 / 5 := rfl
  have t11 : gridTable 1 1 = 1 / 2 := rfl
  have t20 : gridTable 2 0 = 0 := rfl
  have t22 : gridTable 2 2 = 1 / 2 := rfl
  refine ⟨?_, t00, by rw [t01, t00]; norm_num, by rw [t02, t00]; norm_num,
    by rw [t10, t11]; norm_num, by rw [t20, t22]; norm_num, by rw [t10, t01]; norm_num,
    by rw [t20, t01]; norm_num⟩
  intro w m
  fin_cases m
  · change gridValue w 0 = gridTable w 0
    simp only [gridValue, if_pos h0, vForced]
    fin_cases w <;> rw [noIntGain_two] <;> simp [gridKernel, gridTable, twoX, twoValue] <;> norm_num
  · change gridValue w 1 = gridTable w 1
    simp only [gridValue, if_neg h1, vFreeBlind]
    fin_cases w <;> rw [expect_two] <;> simp [gridTable, twoX, twoValue] <;> norm_num
  · change gridValue w 2 = gridTable w 2
    simp only [gridValue, if_neg h2, vFreeBlind]
    fin_cases w <;> rw [expect_two] <;> simp [gridTable, twoX, twoValue] <;> norm_num

end

end Cleanroom.Corrigibility.CorrPowerChannel
