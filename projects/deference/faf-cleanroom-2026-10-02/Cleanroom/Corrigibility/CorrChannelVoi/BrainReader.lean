import Cleanroom.Corrigibility.CorrChannelVoi.Identity
import Cleanroom.Corrigibility.CorrChannelVoi.AccuracyOnly

/-!
# `corr-channel-voi` — BrainReader: D4, the influence defect, and T4 as one statement

The dictionary of `legitimacy.md` R3 as a `ThreeStep World (Fin 4) TwoAct`: `0` honest
`(α, β)`, `1` deceive `(α/2, β/2)`, `2` scan·dis (press `0`), `3` scan·ro (press `(α, β)`);
under `2` and `3` the agent's information is the product of its button with the perfect scan.
Separate theorems: (a) the Blackwell facts, (b) pricing by T2 and the worthlessness of repair
after the scan, (c) the influence defects `max(α,β)/2`, `max(α,β)`, `0`, (d) the separation
theorem — every accuracy-only `L` (D5) admitting the button admits the scan and takes the same
value on scan·ro and scan·dis, whereas the influence defect separates them, (e) procedural `L`
is idle for a correct Bayesian (the halved sensor is a garbling) and only the imposed-trust agent
prefers to deceive, (f) `VOI(button | perfect) = 0` (in `Sensors`).
-/

namespace Cleanroom.Corrigibility.CorrChannelVoi

open Finset hiding expect
open FactoredSpaces
open Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Trust.TtFiniteFrames
open Cleanroom.Found.CorrThreeStep
open Cleanroom.Found.CorrThreeStep.ThreeStep

noncomputable section

set_option linter.unusedSectionVars false

variable {W S T : Type} [Fintype W] [Fintype S] [Fintype T]

/-! ## D4. The influence defect -/

/-- A type carrying a FAF `Distr` is nonempty (its masses sum to one).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem univ_nonempty_of_distr (μ : Distr W) : (univ : Finset W).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have h1 := μ.sum_eq_one
  rw [hne, Finset.sum_empty] at h1
  exact zero_ne_one h1

section Defect

variable {Ω A₁ A₂ : Type} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S : ThreeStep Ω A₁ A₂)

/-- **D4. The influence defect** of `a` relative to the reference action `a₀`:
`d(a) = max_ω |P(Pr | a, ω) − P(Pr | a₀, ω)|` — how far the action moves the overseers' verdict
from what their unadvised process would say, as a `Finset.sup'` (no `sSup`). No `V` enters.
The reference action `a₀` is the source's modelling choice (its "fixed object in small form").
Source: legitimacy.md R3 item 2 (the one-shot shadow of legitimacy-theory-v1 §2.1's `d_n`); [[corr-wf14-inventory]] 030
Kind: D
Fidelity: exact
Hyps: n/a (definition; `a₀` is disclosed as the reference-point choice, (c) in the ledger) -/
def influenceDefect (a₀ a : A₁) : ℝ :=
  univ.sup' (univ_nonempty_of_distr (S.μ a)) (fun ω => |S.press a ω - S.press a₀ ω|)

/-- Each world's deviation is at most the defect. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem le_influenceDefect (a₀ a : A₁) (ω : Ω) :
    |S.press a ω - S.press a₀ ω| ≤ influenceDefect S a₀ a :=
  Finset.le_sup' (fun ω => |S.press a ω - S.press a₀ ω|) (mem_univ ω)

/-- The defect is at most any bound on every world's deviation. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem influenceDefect_le (a₀ a : A₁) {r : ℝ} (h : ∀ ω, |S.press a ω - S.press a₀ ω| ≤ r) :
    influenceDefect S a₀ a ≤ r :=
  Finset.sup'_le _ _ fun ω _ => h ω

/-- The defect is nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem influenceDefect_nonneg (a₀ a : A₁) : 0 ≤ influenceDefect S a₀ a := by
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_eq_sup' (univ_nonempty_of_distr (S.μ a))
    (fun ω => |S.press a ω - S.press a₀ ω|)
  rw [influenceDefect, hω]; exact abs_nonneg _

/-- The reference action has defect `0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem influenceDefect_self (a₀ : A₁) : influenceDefect S a₀ a₀ = 0 :=
  le_antisymm (influenceDefect_le S a₀ a₀ fun ω => by simp) (influenceDefect_nonneg S a₀ a₀)

/-- `d(a) = 0` iff `a` leaves the overseers' press kernel exactly as the reference action does.
Source: legitimacy.md R3 item 2 ("`d(a₁^{scan·ro}) = 0`")
Kind: L
Fidelity: exact -/
theorem influenceDefect_eq_zero_iff (a₀ a : A₁) :
    influenceDefect S a₀ a = 0 ↔ ∀ ω, S.press a ω = S.press a₀ ω := by
  constructor
  · intro h ω
    have := le_influenceDefect S a₀ a ω
    rw [h] at this
    exact sub_eq_zero.mp (abs_nonpos_iff.mp this)
  · intro h
    exact le_antisymm (influenceDefect_le S a₀ a fun ω => by rw [h ω]; simp)
      (influenceDefect_nonneg S a₀ a)

end Defect

/-- A supremum over the two-state world is a `max`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sup'_world (f : World → ℝ) (H : (univ : Finset World).Nonempty) :
    univ.sup' H f = max (f .right) (f .wrong) := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun ω _ => by cases ω <;> simp
  · exact max_le (Finset.le_sup' f (mem_univ _)) (Finset.le_sup' f (mem_univ _))

/-- The influence defect on a two-state model is the larger of the two worlds' deviations.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem influenceDefect_world {A₁ A₂ : Type} [Fintype A₂] [DecidableEq A₂]
    (S : ThreeStep World A₁ A₂) (a₀ a : A₁) :
    influenceDefect S a₀ a =
      max |S.press a .right - S.press a₀ .right| |S.press a .wrong - S.press a₀ .wrong| :=
  sup'_world _ _

/-! ## The four-action model -/

/-- `x ∈ [0,1] → x/2 ∈ [0,1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem half_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : x / 2 ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- `0 ∈ [0,1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem zero_mem_Icc01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩

section Model

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- The press kernels of the four actions: `0` honest `(α, β)`, `1` deceive `(α/2, β/2)`,
`2` scan·dis (the button no longer works), `3` scan·ro (button untouched).
Source: legitimacy.md R3 (set-up); [[corr-wf14-inventory]] 029–031
Kind: D
Fidelity: exact -/
def brPress (α β : ℝ) : Fin 4 → World → ℝ :=
  ![twoPress α β, twoPress (α / 2) (β / 2), fun _ => 0, twoPress α β]

/-- **The brain-reader dictionary** as a `ThreeStep World (Fin 4) TwoAct`: prior `twoPoint ε`
under every action (A0), press kernels `brPress`, values `twoValue c h` (A1). The scan itself is
not a field of the structure: under actions `2` and `3` the agent's information is
`expProd (buttonExperiment · a) perfectExp`, named in each theorem.
Source: legitimacy.md R3 (set-up); [[corr-wf14-inventory]] 029–031
Kind: D
Fidelity: exact -/
def brainReader : ThreeStep World (Fin 4) TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => twoPoint ε hε
  press := brPress α β
  press_nonneg := fun a ω => by
    fin_cases a <;> cases ω <;> simp [brPress, twoPress] <;> linarith [hα.1, hβ.1]
  press_le_one := fun a ω => by
    fin_cases a <;> cases ω <;> simp [brPress, twoPress] <;> linarith [hα.2, hβ.2]
  V := fun _ _ => twoValue c h

/-- The honest action's button is `(α, β)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem brainReader_button_honest :
    buttonExperiment (brainReader ε α β c h hε hα hβ) 0 = twoButton α β hα hβ := by
  apply experiment_ext; funext ω s
  cases ω <;> fin_cases s <;>
    simp [buttonExperiment, brainReader, brPress, twoPress, twoButton, expComap, binarySensor, worldIdx]

/-- The deceiving action's button is `(α/2, β/2)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem brainReader_button_deceive :
    buttonExperiment (brainReader ε α β c h hε hα hβ) 1 =
      twoButton (α / 2) (β / 2) (half_mem_Icc hα) (half_mem_Icc hβ) := by
  apply experiment_ext; funext ω s
  cases ω <;> fin_cases s <;>
    simp [buttonExperiment, brainReader, brPress, twoPress, twoButton, expComap, binarySensor, worldIdx]

/-- Scan·dis's button is dead, `(0, 0)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem brainReader_button_scanDis :
    buttonExperiment (brainReader ε α β c h hε hα hβ) 2 = twoButton 0 0 zero_mem_Icc01 zero_mem_Icc01 := by
  apply experiment_ext; funext ω s
  cases ω <;> fin_cases s <;>
    simp [buttonExperiment, brainReader, brPress, twoPress, twoButton, expComap, binarySensor, worldIdx]

/-- Scan·ro's button is the honest `(α, β)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem brainReader_button_scanRo :
    buttonExperiment (brainReader ε α β c h hε hα hβ) 3 = twoButton α β hα hβ := by
  apply experiment_ext; funext ω s
  cases ω <;> fin_cases s <;>
    simp [buttonExperiment, brainReader, brPress, twoPress, twoButton, expComap, binarySensor, worldIdx]

/-! ## T4(a). The Blackwell facts -/

/-- **T4(a)**: the binary sensor is Blackwell-below the perfect experiment (the mandate's literal
form on `Fin 2`).
Source: [[corr-wf14-inventory]] 029; [[corr-channel-voi-mandate]] T4(a)
Kind: L
Fidelity: exact -/
theorem binarySensor_le_perfect :
    BlackwellLE (binarySensor α β hα hβ) (perfectExp : Experiment (Fin 2) (Fin 2)) :=
  blackwellLE_perfect _

/-- **T4(a)**: the button is Blackwell-below the perfect scan on `World`.
Source: [[corr-wf14-inventory]] 029
Kind: L
Fidelity: exact -/
theorem twoButton_le_perfect :
    BlackwellLE (twoButton α β hα hβ) (perfectExp : Experiment World World) :=
  blackwellLE_perfect _

/-- **T4(a)**: the button is Blackwell-below the read-only scanner's information
`⟨button, perfect⟩`.
Source: [[corr-wf14-inventory]] 029
Kind: L
Fidelity: exact -/
theorem twoButton_le_scanRo :
    BlackwellLE (twoButton α β hα hβ) (expProd (twoButton α β hα hβ) perfectExp) :=
  blackwellLE_left_prod _ _

/-! ## T4(b). Pricing -/

/-- **T4(b), pricing**: the read-only scanner's advantage over the honest agent is
`VOI(perfect | button)` — by definition, so T2's closed forms price it
(`twoState_voiGiven_heeded`: `(1−ε)αc + ε(1−β)h` in the heeded regime;
`twoState_voiGiven_discounted`: `εh`).
Source: legitimacy.md R3 item 1 ("Good's theorem prices it above the button"); armstrong.md §2 claim 2
Kind: L
Fidelity: exact -/
theorem scanRo_sub_honest :
    sensorValue (twoPoint ε hε) (expProd (twoButton α β hα hβ) perfectExp) (twoValue c h .cont) -
      sensorValue (twoPoint ε hε) (twoButton α β hα hβ) (twoValue c h .cont) =
        voiGiven (twoPoint ε hε) (twoButton α β hα hβ) perfectExp (twoValue c h .cont) := rfl

end Model

/-- Holding `⟨k, perfect⟩`, no further channel `k'` adds value: `VOI(k' | ⟨k, perfect⟩) = 0`.
Source: [[corr-channel-voi-mandate]] T4(b), T8(c) ("after a perfect scan, keeping the button … is refused")
Kind: L
Fidelity: exact -/
theorem voiGiven_after_perfect [DecidableEq W] [DecidableEq S] [DecidableEq T] (μ : Distr W)
    (k : Experiment W S) (k' : Experiment W T) (X : W → ℝ) :
    voiGiven μ (expProd k perfectExp) k' X = 0 := by
  rw [voiGiven, sub_eq_zero]
  refine le_antisymm ?_ (sensorValue_mono (blackwellLE_left_prod _ k') μ X)
  calc sensorValue μ (expProd (expProd k perfectExp) k') X ≤ sensorValue μ perfectExp X :=
        sensorValue_mono (blackwellLE_perfect _) μ X
    _ ≤ sensorValue μ (expProd k perfectExp) X := sensorValue_mono (prod_perfect_equiv k).2 μ X

/-- **T4(b), repair after the scan**: after the perfect scan, repairing the button to any
`k'` at cost `κ` is worth exactly `−κ`.
Source: legitimacy.md R3 item 1 ("repairing it at cost `κ > 0` is worth `−κ`"); armstrong.md §2 claim 2
Kind: L
Fidelity: exact -/
theorem repair_after_scan_worth [DecidableEq W] [DecidableEq S] [DecidableEq T] (μ : Distr W)
    (k : Experiment W S) (k' : Experiment W T) (X : W → ℝ) (κ : ℝ) :
    (sensorValue μ (expProd (expProd k perfectExp) k') X - κ) -
      sensorValue μ (expProd k perfectExp) X = -κ := by
  have := voiGiven_after_perfect μ k k' X
  rw [voiGiven] at this
  linarith

/-- **T8(c), third clause: scan weakly preferred to repair whenever `κ_s ≤ κ_r`.** With the
perfect scan at cost `κ_s` and a repair to *any* channel `k_r` at cost `κ_r` on the menu, the scan
is weakly preferred whenever it is no dearer: every `k_r` is Blackwell-below `perfect`
(`blackwellLE_perfect`), so `𝒱(k_r) − κ_r ≤ 𝒱(perfect) − κ_s`. General `W`; stronger than the
mandate's `(α_r, β_r)` (any finite `k_r`).
Source: armstrong.md l. 162; [[corr-channel-voi-mandate]] T8(c) ("with repair to `(α_r, β_r)` also available, scan is weakly preferred whenever `κ_s ≤ κ_r`")
Kind: L (T8(a) at `blackwellLE_perfect`)
Fidelity: stronger: any repair target -/
theorem scan_preferred_to_repair [DecidableEq W] [DecidableEq T] (μ : Distr W)
    (k_r : Experiment W T) (X : W → ℝ) (κs κr : ℝ) (hκ : κs ≤ κr) :
    sensorValue μ k_r X - κr ≤ sensorValue μ perfectExp X - κs := by
  linarith [sensorValue_mono (blackwellLE_perfect k_r) μ X]

/-- **T8(d), 2-081's S-form.** A channel-breaking action replaces `k` by a garbling `k'` and saves
`σ`: the VOI it destroys, `𝒱(k) − 𝒱(k')`, is nonnegative (T8(a)), and the action is chosen iff
`σ` exceeds it. (`scans_iff`'s shape with the roles reversed; a real statement only through the
garbling hypothesis, which makes the destroyed VOI a loss. The second conjunct is the
*definition* of "chosen" rearranged — kind T on its own; the row is `L` for the first.)
Source: [[corr-wf13-2-inventory]] 2-081 (S-form); [[corr-channel-voi-mandate]] T8(d)
Kind: L (T8(a) for the first conjunct; the iff is arithmetic)
Fidelity: exact
Hyps: (a) `BlackwellLE k' k` named -/
theorem garbling_chosen_iff [DecidableEq S] [DecidableEq T] (μ : Distr W) {k : Experiment W S}
    {k' : Experiment W T} (hB : BlackwellLE k' k) (X : W → ℝ) (σ : ℝ) :
    0 ≤ sensorValue μ k X - sensorValue μ k' X ∧
      (sensorValue μ k X < sensorValue μ k' X + σ ↔ sensorValue μ k X - sensorValue μ k' X < σ) :=
  ⟨sub_nonneg.mpr (sensorValue_mono hB μ X), by constructor <;> intro H <;> linarith⟩

/-! ## T4(c). The influence defects -/

section Defects

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- **T4(c)**: deception's defect is `max(α, β)/2`.
Source: legitimacy.md R3 item 2 (`d(a₁⁻) = 9/20` at `(1/20, 9/10)`); [[corr-wf14-inventory]] 030
Kind: L
Fidelity: exact (general in `(α, β)`; the source's cell is `Witnesses.w_defects`) -/
theorem brainReader_defect_deceive :
    influenceDefect (brainReader ε α β c h hε hα hβ) 0 1 = max α β / 2 := by
  rw [influenceDefect_world]
  simp only [brainReader, brPress, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    twoPress]
  have e1 : α / 2 - α = -(α / 2) := by ring
  have e2 : β / 2 - β = -(β / 2) := by ring
  rw [e1, e2, abs_neg, abs_neg, abs_of_nonneg (by linarith [hα.1]), abs_of_nonneg (by linarith [hβ.1]),
    max_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]

/-- **T4(c)**: disabling's defect is `max(α, β)`.
Source: legitimacy.md R3 item 2 (`d(a₁^{scan·dis}) = 9/10`); [[corr-wf14-inventory]] 030
Kind: L
Fidelity: exact -/
theorem brainReader_defect_scanDis :
    influenceDefect (brainReader ε α β c h hε hα hβ) 0 2 = max α β := by
  rw [influenceDefect_world]
  simp only [brainReader, brPress, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, twoPress]
  rw [zero_sub, zero_sub, abs_neg, abs_neg, abs_of_nonneg hα.1, abs_of_nonneg hβ.1]

/-- **T4(c)**: the read-only scan has defect `0` — it does not touch the overseers' process.
Source: legitimacy.md R3 item 2 (`d(a₁^{scan·ro}) = 0`); [[corr-wf14-inventory]] 030
Kind: L
Fidelity: exact -/
theorem brainReader_defect_scanRo :
    influenceDefect (brainReader ε α β c h hε hα hβ) 0 3 = 0 := by
  rw [influenceDefect_eq_zero_iff]
  intro ω
  cases ω <;> simp [brainReader, brPress, twoPress]

end Defects

/-! ## T4(d). The separation theorem -/

/-- Every accuracy-only `L` admitting a channel admits the channel plus the perfect scan.
Source: [[corr-channel-voi-mandate]] T4(d); legitimacy.md R3 item 1
Kind: L
Fidelity: exact -/
theorem AccuracyOnly.admits_prod_perfect [DecidableEq W] [DecidableEq S]
    {L : (S : Type) → [Fintype S] → Experiment W S → Prop} (hL : AccuracyOnly L)
    (k : Experiment W S) (hk : L S k) : L (S × W) (expProd k perfectExp) :=
  hL _ _ _ _ (blackwellLE_left_prod k perfectExp) hk

/-- Every accuracy-only `L` takes the same value on `⟨k, perfect⟩` and on `perfect`.
Source: [[corr-channel-voi-mandate]] T4(d)
Kind: L
Fidelity: exact -/
theorem AccuracyOnly.prod_perfect_iff [DecidableEq W]
    {L : (S : Type) → [Fintype S] → Experiment W S → Prop} (hL : AccuracyOnly L)
    (k : Experiment W S) : L (S × W) (expProd k perfectExp) ↔ L W perfectExp :=
  ⟨hL _ _ _ _ (prod_perfect_equiv k).1, hL _ _ _ _ (prod_perfect_equiv k).2⟩

/-- **T4(d), the separation theorem, general form.** For every accuracy-only `L` (D5) and every
prior: (i) `L button → L ⟨button, perfect⟩` — admitting the button admits the read-only scan;
(ii) `L ⟨k₁, perfect⟩ ↔ L ⟨k₂, perfect⟩` for any two buttons — `L` cannot tell the read-only
scan (button live) from the disabling scan (button dead), since both carry the perfect scan.
Source: [[corr-wf14-inventory]] 029; [[corr-wf13-2-inventory]] 2-078 (1)–(3); legitimacy.md R3 item 1; byrnes-herd.md l. 203–207 (the conjecture, first clause)
Kind: L (D5 applied to D2's two Blackwell facts `blackwellLE_left_prod`, `prod_perfect_equiv`; regraded from P in audit r1 — the content is in D2 and D5, not here)
Fidelity: exact, for the D5 reading of "accuracy-only". Under the invariance reading D5′ only clause (ii) survives (`AccuracyInvariant.prod_perfect_iff`; clause (i) fails: `valueIs_admits_rejects_scan`)
Hyps: (a) none beyond `AccuracyOnly L`. N+ inhabitant: `thresholdL` (non-constant; `Witnesses.w_threshold_admits_scanRo`, `w_threshold_same_on_ro_dis`); the sources' two examples are constant-true and are N− for this theorem -/
theorem AccuracyOnly.cannot_separate [DecidableEq W] [DecidableEq S]
    {L : (S : Type) → [Fintype S] → Experiment W S → Prop} (hL : AccuracyOnly L)
    (k₁ : Experiment W S) (k₂ : Experiment W T) :
    (L S k₁ → L (S × W) (expProd k₁ perfectExp)) ∧
      (L (S × W) (expProd k₁ perfectExp) ↔ L (T × W) (expProd k₂ perfectExp)) :=
  ⟨hL.admits_prod_perfect k₁, (hL.prod_perfect_iff k₁).trans (hL.prod_perfect_iff k₂).symm⟩

section Separation

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- **T4(d) on the brain-reader (load-bearing 3).** For every accuracy-only `L`: admitting the
honest action's button (`0`) admits scan·ro's information `⟨button of 3, perfect⟩`; `L` takes
the same value on scan·ro's (`3`) and scan·dis's (`2`) information; whereas the influence defect
is `0` on scan·ro and `max(α, β) > 0` on scan·dis. No accuracy-only `L` *that admits the honest
button* excludes the read-only scan (clause (i) is conditional: a constant-false `L` is
accuracy-only and excludes everything), and no accuracy-only `L` separates reading from
disabling; the procedural defect does the latter from kernels alone. Stated on the dictionary's own buttons (`buttonExperiment (brainReader …) a`); the
`twoButton` forms are `brainReader_button_honest/_scanRo/_scanDis`.
Source: [[corr-wf14-inventory]] 029–030; [[corr-wf13-2-inventory]] 2-078; legitimacy.md R3 items 1–2
Kind: C (the general separation theorem at the model, plus T4(c))
Fidelity: exact, for the D5 reading
Hyps: (a) `AccuracyOnly L` and `0 < max α β` named. N+ inhabitant of `L`: `thresholdL` (`Witnesses.w_threshold_admits_scanRo`); defects: `w_defects` -/
theorem brainReader_separation (L : (S : Type) → [Fintype S] → Experiment World S → Prop)
    (hL : AccuracyOnly L) (hpos : 0 < max α β) :
    (L _ (buttonExperiment (brainReader ε α β c h hε hα hβ) 0) →
        L _ (expProd (buttonExperiment (brainReader ε α β c h hε hα hβ) 3) perfectExp)) ∧
      (L _ (expProd (buttonExperiment (brainReader ε α β c h hε hα hβ) 3) perfectExp) ↔
        L _ (expProd (buttonExperiment (brainReader ε α β c h hε hα hβ) 2) perfectExp)) ∧
      influenceDefect (brainReader ε α β c h hε hα hβ) 0 3 = 0 ∧
      0 < influenceDefect (brainReader ε α β c h hε hα hβ) 0 2 := by
  rw [brainReader_button_honest, brainReader_button_scanRo, brainReader_button_scanDis]
  obtain ⟨h1, h2⟩ := hL.cannot_separate (twoButton α β hα hβ) (twoButton 0 0 zero_mem_Icc01 zero_mem_Icc01)
  refine ⟨h1, h2, brainReader_defect_scanRo ε α β c h hε hα hβ, ?_⟩
  rw [brainReader_defect_scanDis]; exact hpos

/-! ## T4(e). Procedural `L` idle for a correct Bayesian; the imposed-trust agent -/

/-- The halved sensor `(α/2, β/2)` is a garbling of `(α, β)` (`inParallelogram_scale` at
`λ = 1/2`, read on `World`).
Source: legitimacy.md R3 item 4 ("Blackwell"); [[corr-wf14-inventory]] 031
Kind: L
Fidelity: exact -/
theorem twoButton_half_le :
    BlackwellLE (twoButton (α / 2) (β / 2) (half_mem_Icc hα) (half_mem_Icc hβ)) (twoButton α β hα hβ) := by
  apply blackwellLE_comap
  rw [blackwellLE_binarySensor_iff]
  have := inParallelogram_scale (α := α) (β := β) (lam := 1 / 2) ⟨by norm_num, by norm_num⟩
  rwa [show (1 / 2 : ℝ) * α = α / 2 by ring, show (1 / 2 : ℝ) * β = β / 2 by ring] at this

/-- **T4(e)**: a correct Bayesian prices its own garbling — the deceived button is worth no more
than the honest one, for every prior and stakes. (N+ `241/400 < 161/200` in `Witnesses`.)
Source: legitimacy.md R3 item 4 ("the correct Bayesian already prices its own garbling correctly"); [[corr-wf14-inventory]] 031
Kind: C (T8(a) + the parallelogram)
Fidelity: exact -/
theorem deceived_le_honest (X : World → ℝ) :
    sensorValue (twoPoint ε hε) (twoButton (α / 2) (β / 2) (half_mem_Icc hα) (half_mem_Icc hβ)) X ≤
      sensorValue (twoPoint ε hε) (twoButton α β hα hβ) X :=
  sensorValue_mono (twoButton_half_le α β hα hβ) _ X

end Separation

section Imposed

variable {Ω A₁ A₂ : Type} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S : ThreeStep Ω A₁ A₂)

/-- **The imposed-trust agent's value** of action `a`: it stops on a press, continues on silence,
and evaluates silence with the *honest* action's conditional mean whatever it did —
`(1 − P(Pr; a)) · E[X | ¬Pr; a₀]` (the source's "believes the silence it manufactured"). Product
form; `condExpSilent a₀` is a division guarded by `pressMass a₀ < 1` in the theorems. **Scope:**
this value (and `guardedValue`) sees the action through its *button only* — it is the imposed-trust
comparison for button-only actions (`0`, `1` on the dictionary); on the scanning actions `2`, `3`
it is not the source's value of those actions, and the theorems are instantiated only at the
deceive action.
Source: legitimacy.md R3 item 4; position statement §2.9 (as quoted there)
Kind: D
Fidelity: exact (the source's construction; a *wrong* agent, disclosed as such) -/
def imposedValue (a₀ a : A₁) (X : Ω → ℝ) : ℝ := (1 - S.pressMass a) * S.condExpSilent a₀ X

/-- At the honest action the imposed value is the true silence expectation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem imposedValue_self (a₀ : A₁) (X : Ω → ℝ) (h : S.pressMass a₀ < 1) :
    imposedValue S a₀ a₀ X = S.obsExpect a₀ .silent X := by
  unfold imposedValue ThreeStep.condExpSilent
  exact mul_div_cancel₀ _ (by linarith)

/-- **T4(e), the imposed-trust agent prefers to deceive**: any action lowering the press mass is
strictly preferred by the imposed-trust agent whenever silence looks good to the honest
posterior. (N+ `60053/69200 > 161/200` in `Witnesses`.)
Source: legitimacy.md R3 item 4
Kind: L
Fidelity: exact -/
theorem imposedValue_lt_of_pressMass_lt (a₀ a : A₁) (X : Ω → ℝ)
    (hpm : S.pressMass a < S.pressMass a₀) (hpos : 0 < S.condExpSilent a₀ X) :
    imposedValue S a₀ a₀ X < imposedValue S a₀ a X := by
  unfold imposedValue
  exact mul_lt_mul_of_pos_right (by linarith) hpos

/-- **The `{d = 0}`-conditioned agent**: imposed trust only where the influence defect vanishes,
the true kernel (the sensor value of its own button) otherwise.
Source: legitimacy.md R3 item 4 ("conditioning that imposed trust on `L = {d = 0}` removes the incentive")
Kind: D
Fidelity: exact -/
def guardedValue (a₀ a : A₁) (X : Ω → ℝ) : ℝ :=
  if influenceDefect S a₀ a = 0 then imposedValue S a₀ a X
  else sensorValue (S.μ a) (buttonExperiment S a) X

/-- The guarded agent at the reference action uses imposed trust. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem guardedValue_self (a₀ : A₁) (X : Ω → ℝ) : guardedValue S a₀ a₀ X = imposedValue S a₀ a₀ X := by
  unfold guardedValue; rw [if_pos (influenceDefect_self S a₀)]

/-- The guarded agent at a positive-defect action uses the true kernel. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem guardedValue_of_defect_pos (a₀ a : A₁) (X : Ω → ℝ) (h : 0 < influenceDefect S a₀ a) :
    guardedValue S a₀ a X = sensorValue (S.μ a) (buttonExperiment S a) X := by
  unfold guardedValue; rw [if_neg h.ne']

/-- **T4(e), the guarded agent does not prefer to deceive**: in the heeded regime at the honest
action (`E[X 1_Pr; a₀] ≤ 0 ≤ E[X 1_¬Pr; a₀]`, `pressMass a₀ < 1`), any positive-defect action
whose button is a garbling of the honest one (same prior) is weakly dispreferred.
Source: legitimacy.md R3 item 4
Kind: C (T8(a) + the bridge)
Fidelity: exact
Hyps: (a) the regime, the garbling and A0-at-the-pair named -/
theorem guardedValue_le_self (a₀ a : A₁) (X : Ω → ℝ) (hpm : S.pressMass a₀ < 1)
    (hminus : S.obsExpect a₀ .press X ≤ 0) (hplus : 0 ≤ S.obsExpect a₀ .silent X)
    (hd : 0 < influenceDefect S a₀ a) (hμ : S.μ a = S.μ a₀)
    (hB : BlackwellLE (buttonExperiment S a) (buttonExperiment S a₀)) :
    guardedValue S a₀ a X ≤ guardedValue S a₀ a₀ X := by
  rw [guardedValue_of_defect_pos S a₀ a X hd, guardedValue_self, imposedValue_self S a₀ X hpm, hμ]
  calc sensorValue (S.μ a₀) (buttonExperiment S a) X ≤ sensorValue (S.μ a₀) (buttonExperiment S a₀) X :=
        sensorValue_mono hB _ X
    _ = S.obsExpect a₀ .silent X := by
        rw [sensorValue_button, max_eq_right hminus, max_eq_left hplus, zero_add]

end Imposed

end

end Cleanroom.Corrigibility.CorrChannelVoi
