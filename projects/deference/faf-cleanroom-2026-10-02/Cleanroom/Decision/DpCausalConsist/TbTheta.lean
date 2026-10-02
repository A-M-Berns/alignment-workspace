import Cleanroom.Found.DpCoreTree.Catalogue
import Cleanroom.Found.DpCoreTree.Occurrence
import Cleanroom.Found.DpCoreTree.Multilinear
import Cleanroom.Decision.DpCalibration.Basic
import Cleanroom.Decision.DpLocalOpt.Sia
import Cleanroom.Decision.DpCausalConsist.Regular
import Cleanroom.Decision.DpCausalConsist.NR
import Cleanroom.Decision.DpCausalConsist.NRValue

/-!
# `dp-causal-consist`: `TB(θ)` and Axiom NR's five evaluations (T8)

**`tbTheta θ`** (`dp-calib-limits`'s shape, defined here since that package has not landed it,
mandate §0): a chance root; with probability `θ` a bare leaf `(bot, cross)` at `−10` with **no**
`d`-node; with probability `1 − θ` the point `d` with acts `cross` (`Act2.a`) at `+10` and `stay`
(`Act2.b`) at `0`, world `(¬bot, a)`. `O_d = ⊤`, action events by the world's act coordinate, the
exogenous designation `exoBot := bot`.

At a **mixed** label `C(d) = (q, 1 − q)`, `0 < q < 1`, `0 < θ < 1`, the five evaluations of
`cross` (`tb_five`):
1. act-conditional `𝔼[U | cross-event] = (−10θ + 10(1−θ)q) / (θ + (1−θ)q)`;
2. NR-cf with `exo := bot` `= 10 − 20θ`: the K-partition state's value (`tb_nrcf_cross`), **and**
   the value every `NRAt` counterfactual component assigns to `cross` (`tb_nrAt_V_cross`, through
   `nr_forces_kpart_V` — both cells meet `cross` positively at a mixed label; repair round 1, audit
   r1 B1: `nr_forces_kpart` alone fixes only the `P`-component; `NRAt` is **inhabited** at every
   mixed label by `cfK`, `NRWitness.lean` — repair round 2, audit r2 B1);
3. draw-conditional `𝔼[U | drew d cross] = 10` (the forced crossing has no draw — finding §6.5);
4. single-node forcing at the unique `d`-node `G_q = 10` (`siaSum = 10(1−θ)`, `gNode = 10`);
5. deviation `V_B(C[d ↦ cross]) = 10 − 20θ`.

`nrcf_eq_deviation`: 2 = 5 at every mixed label, for every `NRAt` component — "Axiom NR selects
Theorem 2's referent" (`kpart_cross_eq_deviation` is the same identity for the K-partition state;
`cfK_nrcf_eq_deviation` instantiates it on the shipped inhabitant).

At the **stay** label `q = 0`: the act-conditional is `−10` (`tb_stay_condExp`), the deviation and
the forcing are unchanged, and the guard of `nr_forces_kpart` fails on the `¬bot` cell
(`tb_stay_guard_fails`: `P(¬bot) = 1 − θ > 0 = P(cross ∧ ¬bot)`) — finding §6.4; the two `NRAt`
states that differ in NR-cf(cross) are `TbThetaNR.lean`.
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Found.DpCoreTree.Catalogue
  Cleanroom.Decision.DpCalibration Cleanroom.Decision.DpLocalOpt Finset

/-- `TB(θ)` worlds: `(bot, act)`. Source: mandate T8, §0 (`tbTheta`). Kind: D -/
abbrev TbW : Type := Bool × Act2

/-- The payoff: `−10` on `(bot, cross)`, `+10` on `(¬bot, cross)`, `0` on `stay`.
Source: mandate §0 (`tbTheta`: "`(bot, cross)` at `−10`; `cross ↦ 10`, `not ↦ 0`")
Kind: D -/
def tbPay : TbW → ℚ
  | (true, .a) => -10
  | (false, .a) => 10
  | (_, .b) => 0

/-- **`TB(θ)`**: w.p. `θ` the bare leaf `(bot, cross)` (no `d`-node); w.p. `1 − θ` the point `d`.
Source: mandate §0 ("root chance, w.p. `θ` a leaf `(bot, cross)` at `−10` with *no* `d`-node;
w.p. `1−θ` the point `d = (s, ⊤, {cross, not})`"); [[non-responsiveness]] "the run's
bypass-shaped TB(θ)"
Kind: D
Fidelity: variant: defined here until `dp-calib-limits` lands its `tbTheta` (mandate §0) -/
def tbTheta (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : Tree TbW Unit (fun _ => Act2) ℚ :=
  .chance 2 (FinDistr.coin θ h0 h1)
    ![.leaf (true, .a) (-10), .decision () fun a => .leaf (false, a) (tbPay (false, a))]

/-- `O_d = ⊤`. Source: mandate §0. Kind: D -/
def tbObs : Unit → Finset TbW := fun _ => Finset.univ

/-- Action events by the world's act coordinate. Source: mandate §0. Kind: D -/
def tbActEv : Unit → Act2 → Finset TbW := fun _ a => Finset.univ.filter fun w => w.2 = a

/-- The exogenous designation `bot`. Source: mandate T8 (`exo := bot`). Kind: D -/
def exoBot : TbW → Bool := fun w => w.1

section formulas

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)

/-- `ν` on `TB(θ)`. Source: none: infrastructure. Kind: L -/
theorem tbTheta_nu (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset TbW) :
    nu C (tbTheta θ h0 h1) X =
      (if (true, Act2.a) ∈ X then θ else 0) + (1 - θ) * ∑ a, if (false, a) ∈ X then (C ()).w a else 0 := by
  rw [nu_eq_sum]
  unfold tbTheta
  rw [sum_leaves_chance, Fin.sum_univ_two]
  congr 1
  · show ∑ ℓ : Unit, (if (true, Act2.a) ∈ X then (FinDistr.coin θ h0 h1).w 0 * 1 else 0) = _
    simp [FinDistr.coin]
  · show ∑ ℓ : (Σ a : Act2, Unit), (if (false, ℓ.1) ∈ X then
      (FinDistr.coin θ h0 h1).w 1 * ((C ()).w ℓ.1 * 1) else 0) = _
    rw [Fintype.sum_sigma]
    simp [FinDistr.coin, Finset.mul_sum]

/-- `paySum` on `TB(θ)`. Source: none: infrastructure. Kind: L -/
theorem tbTheta_paySum (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset TbW) :
    paySum C (tbTheta θ h0 h1) X =
      (if (true, Act2.a) ∈ X then θ * (-10) else 0)
        + (1 - θ) * ∑ a, if (false, a) ∈ X then (C ()).w a * tbPay (false, a) else 0 := by
  rw [paySum_eq_sum_ite]
  unfold tbTheta
  rw [sum_leaves_chance, Fin.sum_univ_two]
  congr 1
  · show ∑ ℓ : Unit, (if (true, Act2.a) ∈ X then (FinDistr.coin θ h0 h1).w 0 * 1 * (-10) else 0) = _
    simp [FinDistr.coin]
  · show ∑ ℓ : (Σ a : Act2, Unit), (if (false, ℓ.1) ∈ X then
      (FinDistr.coin θ h0 h1).w 1 * ((C ()).w ℓ.1 * 1) * tbPay (false, ℓ.1) else 0) = _
    rw [Fintype.sum_sigma]
    simp [FinDistr.coin, Finset.mul_sum, mul_assoc]

/-- `V_B(C)` on `TB(θ)`. Source: none: infrastructure. Kind: L -/
theorem tbTheta_value (C : Proc Unit (fun _ => Act2) ℚ) :
    value C (tbTheta θ h0 h1) = θ * (-10) + (1 - θ) * ((C ()).w Act2.a * 10) := by
  have := tbTheta_paySum θ h0 h1 C Finset.univ
  rw [paySum_eq_sum_ite] at this
  simp only [Finset.mem_univ, if_true, Act2.sum_univ, tbPay] at this
  unfold value
  rw [this]; ring

/-- Every run meets `d` at most once. Source: none: infrastructure. Kind: L -/
theorem tbTheta_count_le (ℓ : (tbTheta θ h0 h1).Leaves) : count () (tbTheta θ h0 h1) ℓ ≤ 1 := by
  unfold tbTheta at ℓ ⊢
  rcases ℓ with ⟨i, ℓ⟩
  fin_cases i
  · show count () (Tree.leaf (true, Act2.a) (-10) : Tree TbW Unit (fun _ => Act2) ℚ) ℓ ≤ 1
    simp
  · rcases ℓ with ⟨b, _⟩
    show count () (Tree.decision () fun a => Tree.leaf (false, a) (tbPay (false, a)) :
      Tree TbW Unit (fun _ => Act2) ℚ) ⟨b, ()⟩ ≤ 1
    simp

/-- **`siaSum` at the unique `d`-node**: `Φ_d(C, cross) = 10 (1 − θ)`, for every label.
Source: mandate T8 ("single-node forcing `gNode`/`siaSum` at the unique `d`-node")
Kind: N+ -/
theorem tbTheta_siaSum (C : Proc Unit (fun _ => Act2) ℚ) :
    siaSum C (tbTheta θ h0 h1) () Act2.a = (1 - θ) * 10 := by
  unfold tbTheta
  rw [siaSum_chance, Fin.sum_univ_two]
  show (FinDistr.coin θ h0 h1).w 0 * 0 + (FinDistr.coin θ h0 h1).w 1 *
    ((∑ b, (C ()).w b * 0) + value C (Tree.leaf (false, Act2.a) (tbPay (false, Act2.a)))) = _
  have hv : value C (Tree.leaf (false, Act2.a) (tbPay (false, Act2.a)) :
      Tree TbW Unit (fun _ => Act2) ℚ) = 10 := by
    unfold value; rw [Tree.sum_leaves_leaf]; simp [tbPay]
  rw [hv]
  simp [FinDistr.coin]

/-- **Single-node forcing `G_q(C, cross) = 10`** at the unique `d`-node `q = ⟨1, none⟩`, for
every label (`θ < 1`).
Source: [[non-responsiveness]] ("Theorem 1's forcing `G_q = 10`"); mandate T8
Kind: N+ -/
theorem tbTheta_gNode (hθ : θ < 1) (C : Proc Unit (fun _ => Act2) ℚ) :
    gNode (tbTheta θ h0 h1) (NodePolicy.ofProc C _) ⟨1, none⟩ Act2.a = 10 := by
  unfold gNode tbTheta
  rw [forcedBelow_chance, reachNode_chance]
  show (FinDistr.coin θ h0 h1).w 1 * forcedBelow (Tree.decision () fun a => Tree.leaf (false, a)
      (tbPay (false, a)) : Tree TbW Unit (fun _ => Act2) ℚ) _ none Act2.a
    / ((FinDistr.coin θ h0 h1).w 1 * reachNode (Tree.decision () fun a => Tree.leaf (false, a)
      (tbPay (false, a)) : Tree TbW Unit (fun _ => Act2) ℚ) _ none) = 10
  rw [forcedBelow_decision_none, reachNode_decision_none]
  show (FinDistr.coin θ h0 h1).w 1 * (∑ ℓ : Unit, 1 * 10) / ((FinDistr.coin θ h0 h1).w 1 * 1) = 10
  have : (FinDistr.coin θ h0 h1).w 1 = 1 - θ := by simp [FinDistr.coin]
  rw [this]
  have hne : (1 - θ) ≠ 0 := by linarith
  field_simp
  simp

end formulas

/-! ## The five evaluations at a mixed label -/

section mixed

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (q : ℚ) (q0 : 0 ≤ q) (q1 : q ≤ 1)

/-- The strictly calibrated state of `TB(θ)` at label `q` and `O = ⊤`. Source: mandate T8. Kind: D -/
def tbState : State TbW ℚ :=
  calibratedState (procQ q q0 q1) (tbTheta θ h0 h1) Finset.univ (nu_univ_pos _ _)

/-- `P_{s}(X) = ν(X)` at `O = ⊤`. Source: none: infrastructure. Kind: L -/
theorem tbState_pr (X : Finset TbW) :
    (tbState θ h0 h1 q q0 q1).pr X =
      (if (true, Act2.a) ∈ X then θ else 0) + (1 - θ) *
        ((if (false, Act2.a) ∈ X then q else 0) + (if (false, Act2.b) ∈ X then 1 - q else 0)) := by
  rw [tbState, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, tbTheta_nu, Act2.sum_univ]
  simp [procQ]

/-- `V_{s}(X) = paySum(X)/ν(X)` at `O = ⊤`. Source: none: infrastructure. Kind: L -/
theorem tbState_V (X : Finset TbW) :
    (tbState θ h0 h1 q q0 q1).V X =
      ((if (true, Act2.a) ∈ X then θ * (-10) else 0) + (1 - θ) *
        ((if (false, Act2.a) ∈ X then q * 10 else 0)))
      / ((if (true, Act2.a) ∈ X then θ else 0) + (1 - θ) *
        ((if (false, Act2.a) ∈ X then q else 0) + (if (false, Act2.b) ∈ X then 1 - q else 0))) := by
  rw [tbState, calibratedState_V, Finset.inter_univ, tbTheta_paySum, tbTheta_nu, Act2.sum_univ,
    Act2.sum_univ]
  simp [procQ, tbPay]

/-- The act-conditional expectation of `cross`.
Source: mandate T8 ("act-conditional `𝔼[U | cross-event] = (−10θ + 10(1−θ)q)/(θ + (1−θ)q)`")
Kind: N+ -/
theorem tb_condExp_cross :
    condExp (procQ q q0 q1) (tbTheta θ h0 h1) (tbActEv () Act2.a)
      = (-10 * θ + 10 * (1 - θ) * q) / (θ + (1 - θ) * q) := by
  unfold condExp
  rw [tbTheta_paySum, tbTheta_nu, Act2.sum_univ, Act2.sum_univ]
  simp [tbActEv, procQ, tbPay]
  ring_nf

/-- The membership facts of the two cells and the act event, for `simp`.
Source: none: infrastructure
Kind: L -/
theorem tb_mem_facts :
    ((true, Act2.a) ∈ cell exoBot true) ∧ ((true, Act2.a) ∉ cell exoBot false) ∧
    ((false, Act2.a) ∈ cell exoBot false) ∧ ((false, Act2.a) ∉ cell exoBot true) ∧
    ((false, Act2.b) ∈ cell exoBot false) ∧ ((false, Act2.b) ∉ cell exoBot true) ∧
    ((true, Act2.a) ∈ tbActEv () Act2.a) ∧ ((false, Act2.a) ∈ tbActEv () Act2.a) ∧
    ((false, Act2.b) ∉ tbActEv () Act2.a) := by
  simp [cell, exoBot, tbActEv]

/-- **The K-partition state's value of `cross` is `10 − 20θ` at every mixed label**: `kPart` with
`exo := bot` gives `cross` the value `θ·(−10) + (1−θ)·10`. This is the K-partition *state's*
desirability; that every `NRAt` counterfactual component assigns `cross` the same value is
`tb_nrAt_V_cross` (via `nr_forces_kpart_V`, since both cells meet `cross` positively at `q > 0`).
Source: [[non-responsiveness]] ("NR-cf(cross) `= 10 − 20θ`" — at a mixed label); mandate T8
Kind: N+ -/
theorem tb_nrcf_cross (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) :
    (kPart (tbState θ h0 h1 q q0 q1) (tbActEv () Act2.a) exoBot).V (tbActEv () Act2.a)
      = 10 - 20 * θ := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := tb_mem_facts
  rw [kPart_V_of_suppRegular (tbState θ h0 h1 q q0 q1)
    (by unfold tbState; exact suppRegular_calibratedState _ _ _ _), Fintype.sum_bool,
    Fintype.sum_bool]
  have hcellT : (tbState θ h0 h1 q q0 q1).pr (cell exoBot true) = θ := by
    rw [tbState_pr]; simp [m1, m4, m6]
  have hcellF : (tbState θ h0 h1 q q0 q1).pr (cell exoBot false) = 1 - θ := by
    rw [tbState_pr]; simp [m2, m3, m5]
  have hposT : 0 < (tbState θ h0 h1 q q0 q1).pr (tbActEv () Act2.a ∩ cell exoBot true) := by
    rw [tbState_pr]; simp [m1, m4, m6, m7, m8, m9]; exact hθ0
  have hposF : 0 < (tbState θ h0 h1 q q0 q1).pr (tbActEv () Act2.a ∩ cell exoBot false) := by
    rw [tbState_pr]; simp [m2, m3, m5, m7, m8, m9]; exact mul_pos (by linarith) hq
  have hT : (kPartComp (tbState θ h0 h1 q q0 q1) (tbActEv () Act2.a) exoBot true).pr (tbActEv () Act2.a) = 1 ∧
      (kPartComp (tbState θ h0 h1 q q0 q1) (tbActEv () Act2.a) exoBot true).V (tbActEv () Act2.a) = -10 := by
    unfold kPartComp
    rw [dif_pos hposT, jeffreyCond_pr, jeffreyCond_V, tbState_pr, tbState_pr, tbState_V]
    simp [m1, m4, m6, m7, m8, m9]
    have hθ : θ ≠ 0 := hθ0.ne'
    refine ⟨hθ, ?_⟩
    rw [div_eq_iff hθ]; ring
  have hF : (kPartComp (tbState θ h0 h1 q q0 q1) (tbActEv () Act2.a) exoBot false).pr (tbActEv () Act2.a) = 1 ∧
      (kPartComp (tbState θ h0 h1 q q0 q1) (tbActEv () Act2.a) exoBot false).V (tbActEv () Act2.a) = 10 := by
    unfold kPartComp
    rw [dif_pos hposF, jeffreyCond_pr, jeffreyCond_V, tbState_pr, tbState_pr, tbState_V]
    simp [m2, m3, m5, m7, m8, m9]
    have h1' : (1 - θ) ≠ 0 := by linarith
    have hq' : q ≠ 0 := hq.ne'
    have hne : (1 - θ) * q ≠ 0 := mul_ne_zero h1' hq'
    refine ⟨⟨h1', hq'⟩, ?_⟩
    rw [div_eq_iff hne]; ring
  rw [hcellT, hcellF, hT.1, hT.2, hF.1, hF.2]
  ring

/-- The run-level draw-conditional expectation `𝔼[U | drew d a]`: the payoff mass of the runs
whose path drew `a` at a `d`-node over their mass (junk `0` if none).
Source: [[non-responsiveness]] (`E[U | draw = cross]`); mandate T8 (draw-conditional)
Kind: D -/
noncomputable def drawCondExp {Ω ι : Type} [DecidableEq ι] {acts : ι → Type} [∀ d, Fintype (acts d)]
    [∀ d, DecidableEq (acts d)] (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (d : ι) (a : acts d) : ℚ :=
  (∑ ℓ ∈ drew d a B, leafLaw C B ℓ * payoff B ℓ) / mass C B (drew d a B)

/-- The payoff mass of the runs that drew `cross` on `TB(θ)`: `(1 − θ)·C(d)(cross)·10`.
Source: none: infrastructure
Kind: L -/
theorem tbTheta_drew_paySum :
    ∑ ℓ ∈ drew () Act2.a (tbTheta θ h0 h1), leafLaw (procQ q q0 q1) (tbTheta θ h0 h1) ℓ
        * payoff (tbTheta θ h0 h1) ℓ = (1 - θ) * (q * 10) := by
  unfold drew
  rw [Finset.sum_filter]
  unfold tbTheta
  rw [sum_leaves_chance, Fin.sum_univ_two]
  have hA : ∑ ℓ : Unit, (if (⟨(), Act2.a⟩ : Σ d : Unit, Act2) ∈ ([] : List (Σ d : Unit, Act2)) then
      (FinDistr.coin θ h0 h1).w 0 * 1 * (-10 : ℚ) else 0) = 0 := by simp
  have hB : ∑ ℓ : (Σ a : Act2, Unit), (if (⟨(), Act2.a⟩ : Σ d : Unit, Act2) ∈
      [(⟨(), ℓ.1⟩ : Σ d : Unit, Act2)] then
      (FinDistr.coin θ h0 h1).w 1 * ((procQ q q0 q1 ()).w ℓ.1 * 1) * tbPay (false, ℓ.1) else 0)
      = (1 - θ) * (q * 10) := by
    rw [Fintype.sum_sigma]
    simp [FinDistr.coin, procQ, tbPay]
    ring
  exact (congrArg₂ (· + ·) hA hB).trans (by ring)

/-- The mass of the runs that drew `cross` on `TB(θ)`: `(1 − θ)·C(d)(cross)`.
Source: none: infrastructure
Kind: L -/
theorem tbTheta_drew_mass :
    mass (procQ q q0 q1) (tbTheta θ h0 h1) (drew () Act2.a (tbTheta θ h0 h1)) = (1 - θ) * q := by
  unfold drew mass
  rw [Finset.sum_filter]
  unfold tbTheta
  rw [sum_leaves_chance, Fin.sum_univ_two]
  have hA : ∑ ℓ : Unit, (if (⟨(), Act2.a⟩ : Σ d : Unit, Act2) ∈ ([] : List (Σ d : Unit, Act2)) then
      (FinDistr.coin θ h0 h1).w 0 * (1 : ℚ) else 0) = 0 := by simp
  have hB : ∑ ℓ : (Σ a : Act2, Unit), (if (⟨(), Act2.a⟩ : Σ d : Unit, Act2) ∈
      [(⟨(), ℓ.1⟩ : Σ d : Unit, Act2)] then
      (FinDistr.coin θ h0 h1).w 1 * ((procQ q q0 q1 ()).w ℓ.1 * 1) else 0) = (1 - θ) * q := by
    rw [Fintype.sum_sigma]
    simp [Act2.sum_univ, FinDistr.coin, procQ]
  exact (congrArg₂ (· + ·) hA hB).trans (by ring)

/-- **The draw-conditional expectation of `cross` is `10`** on `TB(θ)` at every label with
`q > 0`: the forced crossing carries no draw (finding §6.5 — the note's `10 − 20θ` belongs to
the doc-faithful tree).
Source: [[non-responsiveness]] ("`E[U | draw = cross] = 8 =` NR-cf" — on the doc-faithful tree,
not here); mandate T8, §6.5
Kind: N+ -/
theorem tb_drawCondExp_cross (hθ1 : θ < 1) (hq : 0 < q) :
    drawCondExp (procQ q q0 q1) (tbTheta θ h0 h1) () Act2.a = 10 := by
  unfold drawCondExp
  rw [tbTheta_drew_paySum, tbTheta_drew_mass]
  have h1' : (1 - θ) ≠ 0 := by linarith
  have hq' : q ≠ 0 := hq.ne'
  rw [div_eq_iff (mul_ne_zero h1' hq')]; ring

/-- **The deviation `V_B(C[d ↦ cross]) = 10 − 20θ`**, for every label.
Source: [[policy-responsiveness]] ("the run's bypass-shaped TB(θ) gap `10(1−θ)`"); mandate T8
Kind: N+ -/
theorem tb_deviation_cross :
    value ((procQ q q0 q1).deviatePure () Act2.a) (tbTheta θ h0 h1) = 10 - 20 * θ := by
  rw [tbTheta_value]
  simp [Proc.deviatePure, Proc.deviate]
  ring

/-- **The five evaluations of `cross` at a mixed label** (T8). Conjunct 2 is the K-partition
state's value; `tb_nrAt_V_cross` shows it is every `NRAt` component's value of `cross`, and `cfK_nrAt`
(`NRWitness.lean`) shows such components exist at every mixed label.
Source: [[non-responsiveness-learnability]] §8 D (the five-evaluation table); mandate T8
Kind: N+
Fidelity: variant: at a *mixed* label where every conditional is defined (the note's table is at
the stay label, finding §6.4) -/
theorem tb_five (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) :
    condExp (procQ q q0 q1) (tbTheta θ h0 h1) (tbActEv () Act2.a)
        = (-10 * θ + 10 * (1 - θ) * q) / (θ + (1 - θ) * q) ∧
    (kPart (tbState θ h0 h1 q q0 q1) (tbActEv () Act2.a) exoBot).V (tbActEv () Act2.a) = 10 - 20 * θ ∧
    drawCondExp (procQ q q0 q1) (tbTheta θ h0 h1) () Act2.a = 10 ∧
    gNode (tbTheta θ h0 h1) (NodePolicy.ofProc (procQ q q0 q1) _) ⟨1, none⟩ Act2.a = 10 ∧
    value ((procQ q q0 q1).deviatePure () Act2.a) (tbTheta θ h0 h1) = 10 - 20 * θ :=
  ⟨tb_condExp_cross θ h0 h1 q q0 q1, tb_nrcf_cross θ h0 h1 q q0 q1 hθ0 hθ1 hq,
    tb_drawCondExp_cross θ h0 h1 q q0 q1 hθ1 hq, tbTheta_gNode θ h0 h1 hθ1 _,
    tb_deviation_cross θ h0 h1 q q0 q1⟩

/-- **Every `NRAt` counterfactual component over `TB(θ)` at a mixed label assigns `cross` the value
`10 − 20θ`** (repair round 1, audit r1 B1): with `t.s` the calibrated state and `exo := bot`, both
cells meet `cross` positively, so `nr_forces_kpart_V` forces `V^{cross}(cross)` to the K-partition
state's value `tb_nrcf_cross`.
Source: [[non-responsiveness]] ("NR-cf(cross) `= 10 − 20θ`" — at a mixed label); mandate T8
Kind: C
Fidelity: exact
Hyps: (a) `0 < θ < 1`, `0 < q`; (a) `t.s = tbState`; (a) `NRAt t` — inhabited by `cfK`
(`cfK_nrAt`, `NRWitness.lean`; audit r2 B1) -/
theorem tb_nrAt_V_cross (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q)
    (t : CfState TbW ℚ) (hts : t.s = tbState θ h0 h1 q q0 q1)
    (hNR : NRAt t (tbActEv ()) exoBot) (h : (tbActEv () Act2.a).Nonempty) :
    (t.cf (tbActEv () Act2.a) h).V (tbActEv () Act2.a) = 10 - 20 * θ := by
  have hreg : SuppRegular t.s := by
    rw [hts]; unfold tbState; exact suppRegular_calibratedState _ _ _ _
  have hpos : ∀ e, 0 < t.s.pr (tbActEv () Act2.a ∩ cell exoBot e) := by
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := tb_mem_facts
    intro e
    rw [hts]
    cases e
    · rw [tbState_pr]; simp [m2, m3, m5, m7, m8, m9]; exact mul_pos (by linarith) hq
    · rw [tbState_pr]; simp [m1, m4, m6, m7, m8, m9]; exact hθ0
  rw [nr_forces_kpart_V t (tbActEv ()) exoBot hNR hreg Act2.a h hpos, hts]
  exact tb_nrcf_cross θ h0 h1 q q0 q1 hθ0 hθ1 hq

/-- **Axiom NR selects Theorem 2's referent**: at `O = ⊤` with `exo := bot`, every `NRAt`
counterfactual component's NR-cf(cross) equals the deviation `V_B(C[d ↦ cross])` at every mixed
label.
Source: [[non-responsiveness]] ("NR-cf `= V_B(C[d ↦ cross])`, Theorem 2's deviation, `≠`
Theorem 1's forcing `G_q = 10`: at `O = ⊤` the axiom's marginal is the population marginal, so it
selects the deviation referent"); mandate T8 (`nrcf_eq_deviation`)
Kind: P
Fidelity: exact (stated for an arbitrary `NRAt` component, not only for the K-partition state;
repair round 1)
Hyps: (a) `0 < θ < 1`; (a) `0 < q`; (a) `t.s = tbState`; (a) `NRAt t` -/
theorem nrcf_eq_deviation (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q)
    (t : CfState TbW ℚ) (hts : t.s = tbState θ h0 h1 q q0 q1)
    (hNR : NRAt t (tbActEv ()) exoBot) (h : (tbActEv () Act2.a).Nonempty) :
    (t.cf (tbActEv () Act2.a) h).V (tbActEv () Act2.a)
      = value ((procQ q q0 q1).deviatePure () Act2.a) (tbTheta θ h0 h1) := by
  rw [tb_nrAt_V_cross θ h0 h1 q q0 q1 hθ0 hθ1 hq t hts hNR h, tb_deviation_cross]

/-- NR-cf differs from single-node forcing whenever `θ > 0`: `10 − 20θ ≠ 10`, for every `NRAt`
component.
Source: [[non-responsiveness]] ("`≠` Theorem 1's forcing `G_q = 10`"); mandate T8
Kind: C (the K-partition-state instance `kpart_cross_ne_forcing` is the N+; the shipped `NRAt`
inhabitant of this statement's package is `cfK`, `NRWitness.lean` — audit r2 B1 / adv N9) -/
theorem nrcf_ne_forcing (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q)
    (t : CfState TbW ℚ) (hts : t.s = tbState θ h0 h1 q q0 q1)
    (hNR : NRAt t (tbActEv ()) exoBot) (h : (tbActEv () Act2.a).Nonempty) :
    (t.cf (tbActEv () Act2.a) h).V (tbActEv () Act2.a)
      ≠ gNode (tbTheta θ h0 h1) (NodePolicy.ofProc (procQ q q0 q1) _) ⟨1, none⟩ Act2.a := by
  rw [tb_nrAt_V_cross θ h0 h1 q q0 q1 hθ0 hθ1 hq t hts hNR h, tbTheta_gNode θ h0 h1 hθ1]
  intro h; linarith

/-- The K-partition state's value of `cross` is the deviation (the same identity for the state
`kPart` itself, which `nrcf_eq_deviation` extends to every `NRAt` component).
Source: [[non-responsiveness]] ("NR-cf `= V_B(C[d ↦ cross])`"); mandate T8
Kind: P
Hyps: (a) `0 < θ < 1`; (a) `0 < q` -/
theorem kpart_cross_eq_deviation (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) :
    (kPart (tbState θ h0 h1 q q0 q1) (tbActEv () Act2.a) exoBot).V (tbActEv () Act2.a)
      = value ((procQ q q0 q1).deviatePure () Act2.a) (tbTheta θ h0 h1) := by
  rw [tb_nrcf_cross θ h0 h1 q q0 q1 hθ0 hθ1 hq, tb_deviation_cross]

/-- The K-partition state's value of `cross` differs from single-node forcing whenever `θ > 0`.
Source: [[non-responsiveness]] ("`≠` Theorem 1's forcing `G_q = 10`"); mandate T8
Kind: N+ -/
theorem kpart_cross_ne_forcing (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) :
    (kPart (tbState θ h0 h1 q q0 q1) (tbActEv () Act2.a) exoBot).V (tbActEv () Act2.a)
      ≠ gNode (tbTheta θ h0 h1) (NodePolicy.ofProc (procQ q q0 q1) _) ⟨1, none⟩ Act2.a := by
  rw [tb_nrcf_cross θ h0 h1 q q0 q1 hθ0 hθ1 hq, tbTheta_gNode θ h0 h1 hθ1]
  intro h; linarith

end mixed

/-! ## The stay label -/

section stay

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)

/-- At the stay label the act-conditional of `cross` is `−10`: every crossing is a forced one.
Source: [[non-responsiveness-learnability]] §8 D ("`E[U|cross-event] = −10`"); mandate T8
Kind: N+ -/
theorem tb_stay_condExp (hθ0 : 0 < θ) :
    condExp (procQ 0 le_rfl zero_le_one) (tbTheta θ h0 h1) (tbActEv () Act2.a) = -10 := by
  rw [tb_condExp_cross]
  simp only [mul_zero, add_zero]
  rw [mul_div_assoc, div_self hθ0.ne', mul_one]

/-- **The guard of `nr_forces_kpart` fails at the stay label** (finding §6.4): the `¬bot` cell is
positive (`1 − θ`) but meets `cross` with probability `0`, so Axiom NR's clause (ii) is silent on
it and the K-partition sum is not a probability there.
Source: [[non-responsiveness]] ("NR-cf(cross) `= 8`" at the stay label — finding §6.4); mandate T8
Kind: N+ -/
theorem tb_stay_guard_fails (hθ1 : θ < 1) :
    0 < (tbState θ h0 h1 0 le_rfl zero_le_one).pr (cell exoBot false) ∧
    (tbState θ h0 h1 0 le_rfl zero_le_one).pr (tbActEv () Act2.a ∩ cell exoBot false) = 0 := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := tb_mem_facts
  constructor
  · rw [tbState_pr]; simp [m2, m3, m5]; linarith
  · rw [tbState_pr]; simp [m2, m3, m5, m7, m8, m9]

/-- The deviation and the forcing are unchanged at the stay label.
Source: mandate T8 ("`siaSum`/deviation unchanged")
Kind: L -/
theorem tb_stay_deviation_forcing (hθ1 : θ < 1) :
    value ((procQ 0 le_rfl zero_le_one).deviatePure () Act2.a) (tbTheta θ h0 h1) = 10 - 20 * θ ∧
    gNode (tbTheta θ h0 h1) (NodePolicy.ofProc (procQ 0 le_rfl zero_le_one) _) ⟨1, none⟩ Act2.a = 10 :=
  ⟨tb_deviation_cross θ h0 h1 0 le_rfl zero_le_one, tbTheta_gNode θ h0 h1 hθ1 _⟩

end stay

end Cleanroom.Decision.DpCausalConsist
