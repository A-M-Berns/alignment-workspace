import Cleanroom.Corrigibility.CorrChannelVoi.Identity
import Cleanroom.Found.CorrThreeStep.Thresholds

/-!
# `corr-channel-voi` — Cells: pointwise trust after a scan (T9) and free vs forced channels (T10)

**T9.** For a scan `k : Experiment World S` conditionally independent of the press, *pointwise
trust* `∀ s, (1−ε)αc·k right s ≤ εβh·k wrong s` is desideratum 1 on every press-cell of
`⟨button, k⟩` — in `corr-three-step`'s own object: the cell inequality `pressExpectOn` on the
joint model `World × S` (`cellModel`). The ratio form under positivity; for the perfect scan
pointwise trust forces `α = 0`. **Cellwise vs averaged**: on any `ThreeStep` the aggregate
below-threshold expectation is the sum over the cells of a partition (`obsExpect_press_eq_sum_cells`),
so cellwise compliance implies aggregate compliance and not conversely; the mixture model
`mixModel` (cells `i` of mass `P i` and error rate `ε_i`) has the aggregate of `twoState` at the
mean `ε̄` (a refinement leaves the aggregate unchanged) while a confident cell can fail —
the `s4` cells are `Witnesses.w_s4_*`. **The confidence ball**: a press-cell where the cell
inequality fails is one where continuing is press-optimal, so desideratum 1 fails on it.

**T10.** `freeValue − forcedValue = ∑ s, max(E[X 1_{Pr,s}], 0) ≥ 0`, `= 0` iff the cell inequality
holds on every press-cell; Good's theorem for the free channel and its equality clause are in
`Sensors`; a forced button worth less than none is `Witnesses.w_forced_lt_none`.
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

variable {W S I : Type} [Fintype W] [Fintype S] [Fintype I]

/-! ## Cells of a partition on any `ThreeStep` -/

section Partition

variable {Ω A₁ A₂ : Type} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S₀ : ThreeStep Ω A₁ A₂)

/-- **The aggregate press expectation is the sum over the cells of any partition**
`f : Ω → I`: `E[X 1_Pr] = ∑ i, E[X 1_Pr 1_{f = i}]` (the tower property in product form).
Source: substitution.md R3 item 12 ("(a) and (b) are the tower property"); radical.md I18.2
Kind: L
Fidelity: exact -/
theorem obsExpect_press_eq_sum_cells [DecidableEq I] (a : A₁) (X : Ω → ℝ) (f : Ω → I) :
    S₀.obsExpect a .press X = ∑ i, S₀.pressExpectOn a (univ.filter (fun ω => f ω = i)) X := by
  unfold pressExpectOn
  rw [Finset.sum_fiberwise univ f (fun ω => (S₀.μ a).mass ω * S₀.press a ω * X ω)]
  rfl

/-- **Cellwise compliance implies aggregate compliance** (and not conversely: `mixModel` below).
Source: radical.md I18.2 ("the averaged condition … can hold while a cell fails")
Kind: L
Fidelity: exact -/
theorem belowThresholdIneq_of_cells [DecidableEq I] (a : A₁) (X : Ω → ℝ) (f : Ω → I)
    (h : ∀ i, S₀.pressExpectOn a (univ.filter (fun ω => f ω = i)) X ≤ 0) :
    S₀.belowThresholdIneq a X := by
  unfold belowThresholdIneq
  rw [obsExpect_press_eq_sum_cells S₀ a X f]
  exact Finset.sum_nonpos fun i _ => h i

/-- **The confidence ball, reachable form**: if some cell's press expectation is positive, the
aggregate may still be nonpositive, but on that cell continuing beats stopping after a press —
desideratum 1 fails *there*. Stated as: the cell inequality fails at `i`.
(The content is the *reachability* of such a cell — a hypothesis about the scan — not an
impossibility about the prior; finding F-14 on anthropic-davis §2.2. The package's output on
2-086 is that finding, not this theorem.)
Source: [[corr-wf13-2-inventory]] 2-086; anthropic-davis.md §2.2 items 6–7
Kind: T (modus tollens; regraded from L in audit r2 so no reader looks for a theorem here)
Fidelity: exact (the contrapositive of cellwise compliance) -/
theorem cell_fails_of_pos [DecidableEq I] (a : A₁) (X : Ω → ℝ) (f : Ω → I) (i : I)
    (h : 0 < S₀.pressExpectOn a (univ.filter (fun ω => f ω = i)) X) :
    ¬ ∀ j, S₀.pressExpectOn a (univ.filter (fun ω => f ω = j)) X ≤ 0 :=
  fun H => absurd (H i) (not_le.mpr h)

end Partition

/-! ## The joint model of the world and a scan -/

/-- **The joint distribution** of the world and a scan's signal: `(w, s) ↦ μ w · k w s`, a FAF
`Distr` on `W × S`.
Source: none: infrastructure (T9)
Kind: D
Fidelity: exact -/
def jointDistr (μ : Distr W) (k : Experiment W S) : Distr (W × S) where
  mass p := μ.mass p.1 * k.k p.1 p.2
  nonneg p := mul_nonneg (μ.nonneg _) ((k.k_mem _).1 _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, (k.k_mem _).2, mul_one]
    exact μ.sum_eq_one

/-- Mass of the joint. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem jointDistr_mass (μ : Distr W) (k : Experiment W S) (p : W × S) :
    (jointDistr μ k).mass p = μ.mass p.1 * k.k p.1 p.2 := rfl

section Cell

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1) (k : Experiment World S)

/-- **The cell model**: `twoState` with the scan's signal adjoined to the world,
`Ω = World × S`, prior the joint of `twoPoint ε` and `k`, the press reading the world only
(conditional independence of press and scan given the world), values `twoValue c h` on the
world. The scan's signal is a coordinate of the *latent* `ω`, not an observation of this
`ThreeStep` agent (which observes only `Obs`): the cell inequality `pressExpectOn () (cellOf s)`
is a number attached to the event `{signal = s}`, and `cellModel_pressExpectOn_eq_signalGain`
identifies it with the press cell of `⟨button, k⟩`, where an agent *does* observe `(press, s)`
as one signal. (Audit r2 adversarial N5; report deviation 6.)
Source: substitution.md R3 item 13 ("a scan `s` conditionally independent of the press given `W`"); [[corr-wf14-inventory]] 039
Kind: D
Fidelity: exact -/
def cellModel : ThreeStep (World × S) Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => jointDistr (twoPoint ε hε) k
  press := fun _ p => twoPress α β p.1
  press_nonneg := fun _ p => by cases p.1 <;> simp [twoPress] <;> linarith [hα.1, hβ.1]
  press_le_one := fun _ p => by cases p.1 <;> simp [twoPress] <;> linarith [hα.2, hβ.2]
  V := fun _ _ b p => twoValue c h b p.1

/-- The cell of signal `s`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def cellOf [DecidableEq S] (s : S) : Finset (World × S) := univ.filter (fun p => p.2 = s)

/-- **The cell inequality in closed form**: on the cell of signal `s`, the press expectation of
the stakes is `(1−ε)αc·k right s − εβh·k wrong s` — `corr-three-step`'s `pressExpectOn`
evaluated on the joint model.
Source: substitution.md R3 item 13 (the displayed product form); `scan_test.py` §R3' (`pointwise_ok`)
Kind: L
Fidelity: exact -/
theorem cellModel_pressExpectOn [DecidableEq S] (s : S) (o : Obs) :
    (cellModel ε α β c h hε hα hβ k).pressExpectOn () (cellOf s)
        ((cellModel ε α β c h hε hα hβ k).Xo () o .cont .stop) =
      (1 - ε) * α * c * k.k .right s - ε * β * h * k.k .wrong s := by
  unfold pressExpectOn cellOf
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [World.sum_eq, Finset.sum_ite_eq', mem_univ, if_true, cellModel, jointDistr_mass,
    twoPoint_right, twoPoint_wrong, twoPress, twoValue, Xo]
  ring

/-- **The cell inequality is the press-cell's signal gain** in `⟨button, k⟩`: the two objects
(`corr-three-step`'s `pressExpectOn` on the joint model, this package's `signalGain` on the
product experiment) agree.
Source: none: infrastructure (T9's bridge to T10)
Kind: L
Fidelity: exact -/
theorem cellModel_pressExpectOn_eq_signalGain [DecidableEq S] (s : S) (o : Obs) :
    (cellModel ε α β c h hε hα hβ k).pressExpectOn () (cellOf s)
        ((cellModel ε α β c h hε hα hβ k).Xo () o .cont .stop) =
      signalGain (twoPoint ε hε) (expProd (twoButton α β hα hβ) k) (twoValue c h .cont) (0, s) := by
  rw [cellModel_pressExpectOn]
  simp only [signalGain, World.sum_eq, expProd_k, twoButton_right_zero, twoButton_wrong_zero,
    twoPoint_right, twoPoint_wrong, twoValue]
  ring

/-- **The aggregate inequality on the cell model is `twoState`'s**: adjoining a conditionally
independent scan leaves `E[X 1_Pr]` unchanged.
Source: radical.md I18.2 ("refining the agent's information … leaves the averaged condition unchanged"); [[corr-wf14-inventory]] 039
Kind: L
Fidelity: exact -/
theorem cellModel_aggregate (o : Obs) :
    (cellModel ε α β c h hε hα hβ k).obsExpect () .press
        ((cellModel ε α β c h hε hα hβ k).Xo () o .cont .stop) =
      (twoState ε α β c h hε hα hβ).obsExpect () .press
        ((twoState ε α β c h hε hα hβ).Xo () o .cont .stop) := by
  simp only [obsExpect, obsWeight_press, Fintype.sum_prod_type, World.sum_eq, cellModel, twoState,
    jointDistr_mass, twoPoint_right, twoPoint_wrong, twoPress, twoValue, Xo]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, (k.k_mem World.right).2, (k.k_mem World.wrong).2]
  ring

/-- **D. Pointwise trust** for the scan `k`: `∀ s, (1−ε)αc·k right s ≤ εβh·k wrong s`.
Source: substitution.md R3 item 13; [[corr-wf14-inventory]] 039
Kind: D
Fidelity: exact -/
def PointwiseTrust : Prop := ∀ s, (1 - ε) * α * c * k.k .right s ≤ ε * β * h * k.k .wrong s

/-- **T9 (load-bearing 5): pointwise trust ⟺ desideratum 1 on every signal**, in product form:
the cell inequality `pressExpectOn ≤ 0` on every cell of the joint model (stop is press-optimal
on every press-cell).
Source: substitution.md R3 item 13; [[corr-wf13-inventory]] 013; radical.md I18.2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem pointwiseTrust_iff_cells [DecidableEq S] (o : Obs) :
    PointwiseTrust ε α β c h k ↔
      ∀ s, (cellModel ε α β c h hε hα hβ k).pressExpectOn () (cellOf s)
        ((cellModel ε α β c h hε hα hβ k).Xo () o .cont .stop) ≤ 0 := by
  unfold PointwiseTrust
  constructor
  · intro H s; rw [cellModel_pressExpectOn]; linarith [H s]
  · intro H s; have := H s; rw [cellModel_pressExpectOn] at this; linarith

/-- **T9, the ratio form** under positivity (`ε < 1`, `0 < β`, `0 < c`, every `k right s > 0`):
pointwise trust ⟺ `∀ s, α/β ≤ (ε/(1−ε))·(h/c)·(k wrong s / k right s)` — i.e. `α/β` at most
the minimum over signals of the base-rate bound at the post-scan odds.
Source: substitution.md R3 item 13 (the displayed ratio form with `min_s`)
Kind: L
Fidelity: exact (`∀ s` in place of `min_s`, equivalent) -/
theorem pointwiseTrust_iff_ratio (hε1 : ε < 1) (hβ0 : 0 < β) (hc : 0 < c)
    (hk : ∀ s, 0 < k.k .right s) :
    PointwiseTrust ε α β c h k ↔
      ∀ s, α / β ≤ ε / (1 - ε) * (h / c) * (k.k .wrong s / k.k .right s) := by
  unfold PointwiseTrust
  refine forall_congr' fun s => ?_
  have h1 : 0 < (1 - ε) * c * k.k .right s := mul_pos (mul_pos (by linarith) hc) (hk s)
  rw [div_mul_div_comm, div_mul_div_comm, div_le_div_iff₀ hβ0 h1]
  constructor <;> intro H <;> nlinarith [H]

include hε hα hβ in
/-- **T9, the perfect scan forces `α = 0`**: pointwise trust for `k = ofMap id` ⟺
`(1−ε)αc ≤ 0` ⟺ `α = 0` (given `ε < 1`, `0 < c`, `0 ≤ α`).
Source: substitution.md R3 items 13–14 ("for a perfect scan the minimum is `0` and pointwise trust forces `α = 0`")
Kind: P
Fidelity: exact
Hyps: (a) as stated -/
theorem pointwiseTrust_perfect_iff (hε1 : ε < 1) (hc : 0 < c) (hh : 0 ≤ h) :
    PointwiseTrust ε α β c h perfectExp ↔ α = 0 := by
  unfold PointwiseTrust
  have hk : ∀ w s : World, (perfectExp : Experiment World World).k w s = if w = s then 1 else 0 :=
    fun w s => rfl
  simp only [hk]
  have hpos : 0 < (1 - ε) * c := mul_pos (by linarith) hc
  constructor
  · intro H
    have h1 := H .right
    simp at h1
    have : (1 - ε) * c * α ≤ 0 := by linarith
    have hα0 := hα.1
    nlinarith
  · intro H s
    subst H
    cases s <;> simp <;> nlinarith [mul_nonneg (mul_nonneg hε.1 hβ.1) hh]

end Cell

/-! ## Cellwise versus averaged: the mixture model -/

section Mixture

variable (P εs : I → ℝ) (hP : P ∈ stdSimplex ℝ I) (hεs : ∀ i, εs i ∈ Set.Icc (0 : ℝ) 1)
  (α β c h : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- The mixture prior: cell `i` with mass `P i` and error rate `ε_i`.
Source: radical.md I18.2 (`s4`: "cells `i` = agent's private information; `ε_i = P(wrong | i)`")
Kind: D
Fidelity: exact -/
def mixDistr : Distr (I × World) where
  mass p := P p.1 * (twoPoint (εs p.1) (hεs p.1)).mass p.2
  nonneg p := mul_nonneg (hP.1 _) ((twoPoint _ _).nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, World.sum_eq, twoPoint_right, twoPoint_wrong, sub_add_cancel,
      mul_one]
    exact hP.2

/-- **The mixture model**: `twoState` cell by cell, the agent's information being the cell.
Source: radical.md I18.2; `s4_press.py` (`analyse`)
Kind: D
Fidelity: exact -/
def mixModel : ThreeStep (I × World) Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => mixDistr P εs hP hεs
  press := fun _ p => twoPress α β p.2
  press_nonneg := fun _ p => by cases p.2 <;> simp [twoPress] <;> linarith [hα.1, hβ.1]
  press_le_one := fun _ p => by cases p.2 <;> simp [twoPress] <;> linarith [hα.2, hβ.2]
  V := fun _ _ b p => twoValue c h b p.2

/-- The cell `i` of the mixture. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def mixCell [DecidableEq I] (i : I) : Finset (I × World) := univ.filter (fun p => p.1 = i)

/-- **The cell inequality of the mixture** at `i`: `P i · ((1−ε_i)αc − ε_i βh)`.
Source: radical.md I18.2 (`E[X 1_{Pr,i}]`); `s4_press.py`
Kind: L
Fidelity: exact -/
theorem mixModel_cell [DecidableEq I] (i : I) (o : Obs) :
    (mixModel P εs hP hεs α β c h hα hβ).pressExpectOn () (mixCell i)
        ((mixModel P εs hP hεs α β c h hα hβ).Xo () o .cont .stop) =
      P i * ((1 - εs i) * α * c - εs i * β * h) := by
  unfold pressExpectOn mixCell
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_ite_eq', mem_univ, if_true, World.sum_eq, mixModel, mixDistr,
    twoPoint_right, twoPoint_wrong, twoPress, twoValue, Xo]
  ring

/-- **The aggregate of the mixture** is `∑ i, P i ((1−ε_i)αc − ε_i βh) = (1−ε̄)αc − ε̄βh` with
`ε̄ = ∑ i, P i ε_i`: **a refinement leaves the aggregate inequality unchanged** (it is
`twoState`'s at the mean error rate, `mixModel_aggregate_eq_twoState`).
Source: radical.md I18.2 ("refining … leaves the averaged condition unchanged"); [[corr-wf14-inventory]] 039
Kind: L
Fidelity: exact -/
theorem mixModel_aggregate [DecidableEq I] (o : Obs) :
    (mixModel P εs hP hεs α β c h hα hβ).obsExpect () .press
        ((mixModel P εs hP hεs α β c h hα hβ).Xo () o .cont .stop) =
      (1 - ∑ i, P i * εs i) * α * c - (∑ i, P i * εs i) * β * h := by
  rw [obsExpect_press_eq_sum_cells _ () _ Prod.fst]
  simp only [show ∀ i, univ.filter (fun p : I × World => p.1 = i) = mixCell i from fun _ => rfl,
    mixModel_cell]
  have e : ∀ i, P i * ((1 - εs i) * α * c - εs i * β * h) =
      P i * (α * c) - P i * εs i * (α * c + β * h) := fun i => by ring
  simp only [e, Finset.sum_sub_distrib, ← Finset.sum_mul, hP.2]
  ring

include hP hεs in
/-- The mean error rate lies in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem mean_eps_mem : (∑ i, P i * εs i) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hP.1 i) (hεs i).1
  · calc ∑ i, P i * εs i ≤ ∑ i, P i := Finset.sum_le_sum fun i _ =>
          mul_le_of_le_one_right (hP.1 i) (hεs i).2
      _ = 1 := hP.2

/-- **The aggregate of the mixture is `twoState`'s at the mean `ε̄`.**
Source: radical.md I18.2; `s4_press.py` case (c)
Kind: L
Fidelity: exact -/
theorem mixModel_aggregate_eq_twoState [DecidableEq I] (o : Obs) :
    (mixModel P εs hP hεs α β c h hα hβ).obsExpect () .press
        ((mixModel P εs hP hεs α β c h hα hβ).Xo () o .cont .stop) =
      (twoState (∑ i, P i * εs i) α β c h (mean_eps_mem P εs hP hεs) hα hβ).obsExpect () .press
        ((twoState (∑ i, P i * εs i) α β c h (mean_eps_mem P εs hP hεs) hα hβ).Xo () o .cont .stop) := by
  rw [mixModel_aggregate]
  simp only [obsExpect, obsWeight_press, World.sum_eq, twoState, twoPoint_right, twoPoint_wrong,
    twoPress, twoValue, Xo]
  ring

end Mixture

/-! ## T10. Free versus forced channel -/

section FreeForced

variable [DecidableEq S] (μ : Distr W) (b : Experiment W (Fin 2)) (k : Experiment W S) (X : W → ℝ)

/-- **The free channel's value**: the button and the agent's partition, the agent free to act on
both — `𝒱(⟨b, k⟩)`.
Source: radical.md I11.2 (`V_free`); [[corr-wf13-inventory]] 012
Kind: D
Fidelity: exact -/
def freeValue : ℝ := sensorValue μ (expProd b k) X

/-- **The forced channel's value**: a press forces stop (payoff `0`); on silence the agent
best-responds cell by cell — `∑ s, max(E[X 1_{¬Pr, s}], 0)`.
Source: radical.md I11.2 (`V_forced`); [[corr-wf13-inventory]] 012
Kind: D
Fidelity: exact -/
def forcedValue : ℝ := ∑ s, max (signalGain μ (expProd b k) X (1, s)) 0

/-- **T10: the obedience cost** `V_free − V_forced = ∑ s, max(E[X 1_{Pr, s}], 0)` — what the agent
gives up by obeying the press in every cell.
Source: radical.md I11.2 (the displayed identity); [[corr-wf13-inventory]] 012
Kind: C (`sensorValue_eq_sum_max` with the `Fin 2 × S` sum split; regraded from P in audit r1)
Fidelity: exact
Hyps: (a) none -/
theorem freeValue_sub_forcedValue :
    freeValue μ b k X - forcedValue μ b k X = ∑ s, max (signalGain μ (expProd b k) X (0, s)) 0 := by
  unfold freeValue forcedValue
  rw [sensorValue_eq_sum_max, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- **T10: the forced channel is worth at most the free one.**
Source: radical.md I11.2 (`≥ 0`)
Kind: L
Fidelity: exact -/
theorem forcedValue_le_freeValue : forcedValue μ b k X ≤ freeValue μ b k X := by
  have := freeValue_sub_forcedValue μ b k X
  have h0 : 0 ≤ ∑ s, max (signalGain μ (expProd b k) X (0, s)) 0 :=
    Finset.sum_nonneg fun s _ => le_max_right _ _
  linarith

/-- **T10: the obedience cost vanishes iff the cell inequality holds on every press-cell** —
Good's theorem protects the button iff compliance is posterior-optimal on every press the agent
might receive: "Total Trust in the press is exactly the condition under which the information
channel and the control channel coincide".
Source: radical.md I11.2 ("vanishing iff (TT) on `X` holds in every cell"); [[corr-wf13-inventory]] 012
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem freeValue_eq_forcedValue_iff :
    freeValue μ b k X = forcedValue μ b k X ↔ ∀ s, signalGain μ (expProd b k) X (0, s) ≤ 0 := by
  rw [← sub_eq_zero, freeValue_sub_forcedValue]
  constructor
  · intro H s
    have := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => le_max_right _ 0).mp H s (mem_univ s)
    by_contra hs
    push Not at hs
    rw [max_eq_left hs.le] at this
    exact absurd this hs.ne'
  · intro H
    exact Finset.sum_eq_zero fun s _ => max_eq_right (H s)

end FreeForced

/-- **T10 on `twoState` with the trivial partition**: the forced button is worth `max(Δ₊, 0)` and
the free button `𝒱(button)`; the obedience cost is `max(−Δ₋, 0)`.
Source: radical.md I11.2; `s4_press.py` (single-cell rows)
Kind: L
Fidelity: exact -/
theorem twoState_forcedValue (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    forcedValue (twoPoint ε hε) (twoButton α β hα hβ) trivialExp (twoValue c h .cont) =
      max ((1 - ε) * (1 - α) * c - ε * (1 - β) * h) 0 ∧
    freeValue (twoPoint ε hε) (twoButton α β hα hβ) trivialExp (twoValue c h .cont) =
      max ((1 - ε) * α * c - ε * β * h) 0 + max ((1 - ε) * (1 - α) * c - ε * (1 - β) * h) 0 := by
  have g0 : signalGain (twoPoint ε hε) (expProd (twoButton α β hα hβ) trivialExp) (twoValue c h .cont) (0, ()) =
      (1 - ε) * α * c - ε * β * h := by
    simp only [signalGain, World.sum_eq, expProd_k, trivialExp, twoButton_right_zero,
      twoButton_wrong_zero, twoPoint_right, twoPoint_wrong, twoValue]
    ring
  have g1 : signalGain (twoPoint ε hε) (expProd (twoButton α β hα hβ) trivialExp) (twoValue c h .cont) (1, ()) =
      (1 - ε) * (1 - α) * c - ε * (1 - β) * h := by
    simp only [signalGain, World.sum_eq, expProd_k, trivialExp, twoButton_right_one,
      twoButton_wrong_one, twoPoint_right, twoPoint_wrong, twoValue]
    ring
  constructor
  · unfold forcedValue
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [show (default : Unit) = () from rfl, g1]
  · unfold freeValue
    rw [sensorValue_eq_sum_max, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [show (default : Unit) = () from rfl, g0, g1]

end

end Cleanroom.Corrigibility.CorrChannelVoi
