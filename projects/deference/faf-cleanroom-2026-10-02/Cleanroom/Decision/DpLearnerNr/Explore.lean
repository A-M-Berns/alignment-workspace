import Cleanroom.Decision.DpLearnerNr.TbThetaDoc

/-!
# `dp-learner-nr` target 3(d): the exploring-agent troll as a tree, `tbThetaExplore`

`tbThetaExplore θ ε`: root chance `bot` (weight `θ`); below it a chance `explore` (weight `ε`);
on `explore` a uniform coin picks `cross`/`stay` *without consulting the point* and the troll
fires on every explored crossing (`−10` regardless of `bot`; `0` on explored stay); on `¬explore`
the point `d` is consulted as in `tbThetaDoc`. Worlds `ExW := Bool × Bool × Act2` (`bot`,
`explored`, act): the exploration coin is a *world coordinate read by the payoff* — hypothesis H's
(h1) of [[dp-referents-cdt]]'s P04-A′ fails on purpose; that is what the exploring-agent troll is.

* `tbThetaExplore_value`: `V(q) = −5ε + (1−ε)·10q(1−2θ)`; `tbThetaExplore_gap`:
  `V(procQ 1) − V(procQ 0) = 10(1−ε)(1−2θ)` — the deliberate label's gap is the `(1−ε)`-scaled
  Proposition 10 rule;
* `tbThetaExplore_licdt`: LICDT, the run-conditional `𝔼[U ∣ explored ∧ cross]` (a `condExp` on the
  world event, which is `dp-referents-cdt`'s `runCondExp` on `worldEv`), is `−10` at every label
  (`ε > 0`);
* `tbThetaExplore_bot_nonResponsive`: `bot` is non-responsive here too;
* N+: `θ = 1/20, ε = 1/10 ↦ 81/10`.
-/

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Found.DpCoreTree.Catalogue
  Cleanroom.Decision.DpCalibration Cleanroom.Decision.DpCausalConsist Finset

/-- Worlds of the exploring-agent troll: `(bot, explored, act)`.
Source: [[dp-learner-nr-mandate]] D3 (`tbThetaExplore`)
Kind: D -/
abbrev ExW : Type := Bool × Bool × Act2

/-- The exploring-agent troll's payoff: `−10` on every explored crossing (whatever `bot`), `0` on
explored stay, `tbPay` on a deliberate act.
Source: `posts/11-troll-bridge-5.md` l. 147 (the exploring-agent variant: the troll fires on
exploration or inconsistency); [[clean-source-and-policy-responsiveness]] §9 C;
[[dp-learner-nr-mandate]] D3
Kind: D -/
def exPay : ExW → ℚ
  | (_, true, .a) => -10
  | (_, true, .b) => 0
  | (b, false, a) => tbPay (b, a)

/-- The coin's act: index `0` is `cross`. Source: none: infrastructure. Kind: D -/
def coinAct' (k : Fin 2) : Act2 := if k = 0 then .a else .b

/-- **The exploring-agent troll `tbThetaExplore θ ε`**: chance `bot` (`θ` on index `0`), then chance
`explore` (`ε` on index `0`); explored: a fair coin draws the act with no `d`-node; deliberate: the
point `d`. The coin is a world coordinate read by `exPay`.
Source: [[clean-source-and-policy-responsiveness]] §9 C ("Troll Bridge, exploring-agent troll …
`10(1−ε)(1−2θ)`"); [[dp-core-2-inventory]] 017; [[dp-learner-nr-mandate]] D3
Kind: D
Fidelity: exact (of the mandate's description; hypothesis H's (h1) fails on purpose) -/
def tbThetaExplore (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (ε : ℚ) (e0 : 0 ≤ ε) (e1 : ε ≤ 1) :
    Tree ExW Unit (fun _ => Act2) ℚ :=
  .chance 2 (FinDistr.coin θ h0 h1) fun i =>
    .chance 2 (FinDistr.coin ε e0 e1)
      ![.chance 2 FinDistr.fair fun k =>
          .leaf (decide (i = 0), true, coinAct' k) (exPay (decide (i = 0), true, coinAct' k)),
        .decision () fun a =>
          .leaf (decide (i = 0), false, a) (exPay (decide (i = 0), false, a))]

/-- The exogenous designation `bot` on `ExW`. Source: [[dp-learner-nr-mandate]] D3. Kind: D -/
def exoBotEx : ExW → Bool := fun w => w.1

/-- The event "explored and crossed". Source: [[dp-learner-nr-mandate]] target 3(d). Kind: D -/
def exploredCross : Finset ExW := univ.filter fun w => w.2.1 = true ∧ w.2.2 = Act2.a

section formulas

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (ε : ℚ) (e0 : 0 ≤ ε) (e1 : ε ≤ 1)

/-- Sums over the leaves of `tbThetaExplore`: `bot` index, then the explored coin or the
deliberate act.
Source: none: infrastructure
Kind: L -/
theorem tbThetaExplore_sum (f : (tbThetaExplore θ h0 h1 ε e0 e1).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ((∑ k : Fin 2, f ⟨i, ⟨0, ⟨k, ()⟩⟩⟩) + ∑ a : Act2, f ⟨i, ⟨1, ⟨a, ()⟩⟩⟩) := by
  unfold tbThetaExplore
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_chance, Fin.sum_univ_two]
  congr 1

/-- **`V(C) = −5ε + (1−ε)·C(d)(cross)·10(1 − 2θ)`** on the exploring-agent troll.
Source: [[clean-source-and-policy-responsiveness]] §9 C; [[dp-learner-nr-mandate]] target 3(d)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem tbThetaExplore_value (C : Proc Unit (fun _ => Act2) ℚ) :
    value C (tbThetaExplore θ h0 h1 ε e0 e1)
      = -5 * ε + (1 - ε) * ((C ()).w .a * (10 * (1 - 2 * θ))) := by
  unfold value
  rw [tbThetaExplore_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, tbThetaExplore, FinDistr.coin, FinDistr.fair, coinAct',
    exPay, tbPay]
  ring

/-- **The deliberate label's gap is `10(1−ε)(1−2θ)`** — the `(1−ε)`-scaled Proposition 10 rule
(load-bearing 2).
Source: [[clean-source-and-policy-responsiveness]] §9 C ("lower `ε` (§9 C: `10(1−ε)(1−2θ)`)");
[[dp-core-2-inventory]] 017; [[dp-learner-nr-mandate]] target 3(d), load-bearing 2
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem tbThetaExplore_gap :
    value (procQ 1 zero_le_one le_rfl) (tbThetaExplore θ h0 h1 ε e0 e1)
      - value (procQ 0 le_rfl zero_le_one) (tbThetaExplore θ h0 h1 ε e0 e1)
      = 10 * (1 - ε) * (1 - 2 * θ) := by
  rw [tbThetaExplore_value, tbThetaExplore_value]
  simp [procQ]; ring

/-- The all-instance deviation gap at any label is the same `10(1−ε)(1−2θ)`.
Source: [[dp-learner-nr-mandate]] target 3(d)
Kind: L -/
theorem tbThetaExplore_dev_gap (C : Proc Unit (fun _ => Act2) ℚ) :
    value (C.deviatePure () Act2.a) (tbThetaExplore θ h0 h1 ε e0 e1)
      - value (C.deviatePure () Act2.b) (tbThetaExplore θ h0 h1 ε e0 e1)
      = 10 * (1 - ε) * (1 - 2 * θ) := by
  rw [tbThetaExplore_value, tbThetaExplore_value]
  simp [Proc.deviatePure, Proc.deviate]; ring

/-- `ν` of the explored-crossing event is `ε/2`, at every label.
Source: none: infrastructure
Kind: L -/
theorem tbThetaExplore_nu_exploredCross (C : Proc Unit (fun _ => Act2) ℚ) :
    nu C (tbThetaExplore θ h0 h1 ε e0 e1) exploredCross = ε / 2 := by
  rw [nu_eq_sum, tbThetaExplore_sum]
  simp [Fin.sum_univ_two, tbThetaExplore, FinDistr.coin, FinDistr.fair, coinAct',
    exploredCross]
  ring

/-- `paySum` of the explored-crossing event is `−5ε`, at every label.
Source: none: infrastructure
Kind: L -/
theorem tbThetaExplore_paySum_exploredCross (C : Proc Unit (fun _ => Act2) ℚ) :
    paySum C (tbThetaExplore θ h0 h1 ε e0 e1) exploredCross = -5 * ε := by
  rw [paySum_eq_sum_ite, tbThetaExplore_sum]
  simp [Fin.sum_univ_two, tbThetaExplore, FinDistr.coin, FinDistr.fair, coinAct',
    exploredCross, exPay]
  ring

/-- **LICDT `= −10` at every label**: the run-conditional `𝔼[U ∣ explored ∧ cross]` — a
`condExp` on the world event `exploredCross`, i.e. `dp-referents-cdt`'s `runCondExp` on
`worldEv` — is `−10` for every procedure when `ε > 0`.
Source: [[clean-source-and-policy-responsiveness]] §9 C ("LICDT (`−10` on every explored
crossing)"); [[dp-core-2-inventory]] 017; [[dp-learner-nr-mandate]] target 3(d)
Kind: L (holds by construction of `exPay`: every explored crossing pays `−10`, so the conditional
is `−5ε/(ε/2)`; relabelled from P at audit r1)
Fidelity: exact (LICDT rendered as the explored-crossing run-conditional)
Hyps: (a) `0 < ε` (the explored-cross event has positive mass; trap (iv)) -/
theorem tbThetaExplore_licdt (hε : 0 < ε) (C : Proc Unit (fun _ => Act2) ℚ) :
    condExp C (tbThetaExplore θ h0 h1 ε e0 e1) exploredCross = -10 := by
  unfold condExp
  rw [tbThetaExplore_paySum_exploredCross, tbThetaExplore_nu_exploredCross,
    div_eq_iff (by positivity)]
  ring

/-- `ν_{C[d↦a]}(bot) = θ` on the exploring-agent troll. Source: none: infrastructure. Kind: L -/
theorem tbThetaExplore_bot_dev (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    nu (C.deviatePure () a) (tbThetaExplore θ h0 h1 ε e0 e1) (cell exoBotEx true) = θ := by
  rw [nu_eq_sum, tbThetaExplore_sum]
  cases a <;> simp [Fin.sum_univ_two, tbThetaExplore, FinDistr.coin, FinDistr.fair,
    coinAct', cell, exoBotEx, Proc.deviatePure, Proc.deviate] <;> ring

/-- **`bot` is non-responsive on the exploring-agent troll** too.
Source: [[clean-source-and-policy-responsiveness]] §9 C ("`□⊥`: no"); [[dp-learner-nr-mandate]] target 3(d)
Kind: P (a universal statement over every `C`, not a witness; relabelled from N+ at audit r1) -/
theorem tbThetaExplore_bot_nonResponsive (C : Proc Unit (fun _ => Act2) ℚ) :
    ¬ Responsive C (tbThetaExplore θ h0 h1 ε e0 e1) () (cell exoBotEx true) := by
  rw [not_responsive_iff]
  intro a b
  rw [tbThetaExplore_bot_dev, tbThetaExplore_bot_dev]

end formulas

/-- **N+**: `θ = 1/20`, `ε = 1/10` gives the deliberate gap `81/10`, and LICDT `−10`.
Source: [[dp-learner-nr-mandate]] target 3(d) ("N+: `θ = 1/20, ε = 1/10 ↦ 81/10`")
Kind: N+ -/
theorem tbThetaExplore_instance :
    value (procQ 1 zero_le_one le_rfl)
        (tbThetaExplore (1/20) (by norm_num) (by norm_num) (1/10) (by norm_num) (by norm_num))
      - value (procQ 0 le_rfl zero_le_one)
        (tbThetaExplore (1/20) (by norm_num) (by norm_num) (1/10) (by norm_num) (by norm_num))
      = 81 / 10 ∧
    condExp (procQ 1 zero_le_one le_rfl)
        (tbThetaExplore (1/20) (by norm_num) (by norm_num) (1/10) (by norm_num) (by norm_num))
        exploredCross = -10 := by
  refine ⟨?_, tbThetaExplore_licdt _ _ _ _ _ _ (by norm_num) _⟩
  rw [tbThetaExplore_gap]; norm_num

end Cleanroom.Decision.DpLearnerNr
