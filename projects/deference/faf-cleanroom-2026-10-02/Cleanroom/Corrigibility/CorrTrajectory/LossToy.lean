import Cleanroom.Corrigibility.CorrTrajectory.Certificate

/-!
# `corr-trajectory` — `LossToy`: the one-action loss toy of 2-013 as an `AgentView`; A1, A8, A2, C6

The two-round toy of `invariant-adversary-scratch/counterexamples.py` (A1, A2, A8) and
`invariant-scratch/checks.py` (C6): one harmful-if-wrong action per round, stakes `h` (harm if wrong
and executed) and `c` (omission if right and refrained), the agent executes iff its posterior
expected value `ev q = (1 − q) c − q h` is positive (ties refrain, as the script), objective
wrongness `q*` per round, i.i.d. The agent's credence is `q₀` at round `0` (for both rounds) and
*predictably* `q₁` at round `1` — no evidence arrives, so every filtration is trivial.

As an instance of `ShutdownProc`: the overseers press every round and the press is uninformative,
so `executed = ¬κ` is the agent's own decision and `κ_t` is literally S2 step 4's rule
(comply iff `P_t(W ∣ Pr) ĥ ≥ P_t(¬W ∣ Pr) ĉ`, i.e. `ev q ≤ 0`). The `T = 1` instance carries the
three refutations of Statement 8's develop text and C6; the `T = 0` instance is A8.

**Witness grades (audit r1, B1; r2, adversarial N1).** At `T = 0` on the trivial filtration the
hypothesis of `expect_Reg_le` is its conclusion (`horizon_zero_squeeze`), so A8 is N− *for the
theorem*; and no instance of this family *with a non-constant loss* inhabits `ville_Z`, because the
incurred loss is not `𝓕₁`-measurable on a trivial filtration once the agent executes with `h > 0`
(`a8_not_lossesObservable`, at A8). The zero-stakes member (`h = c = 0`, `zeroStakesP`) does inhabit
`ville_Z`'s package, vacuously: `loss ≡ 0`, `Δ ≡ 0`, `E*[Ψ₀] = 0` and an empty hit set
(`zeroStakes_ville`, `zeroStakes_vacuous`) — an N− instance, recorded so that the sentence above is
not read as a universal. The N+ witnesses of the certificate theorems are in `ObsToy` (A8's agent
for two rounds, with `ℓ₀` revealed at time `1`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect

namespace LossToy

/-- The product Bernoulli law on `Bool × Bool`: `P(W₀ = 1) = p₀`, `P(W₁ = 1) = p₁`, independent.
Source: [[corr-wf14-inventory]] 2-013 / counterexamples.py (the toy's laws)
Kind: D
Fidelity: exact -/
noncomputable def bern2 (p₀ p₁ : ℝ) (h₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) (h₁ : p₁ ∈ Set.Icc (0 : ℝ) 1) :
    Distr (Bool × Bool) where
  mass ω := (if ω.1 then p₀ else 1 - p₀) * (if ω.2 then p₁ else 1 - p₁)
  nonneg ω := by
    refine mul_nonneg ?_ ?_ <;> split_ifs <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2]
  sum_eq_one := by
    simp [Fintype.sum_prod_type, Fintype.sum_bool]; ring

/-- `expect_bern2` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_bern2 (p₀ p₁ : ℝ) (h₀ h₁) (f : Bool × Bool → ℝ) :
    expect (bern2 p₀ p₁ h₀ h₁) f =
      p₀ * p₁ * f (true, true) + p₀ * (1 - p₁) * f (true, false) +
        (1 - p₀) * p₁ * f (false, true) + (1 - p₀) * (1 - p₁) * f (false, false) := by
  simp [expect, Fintype.sum_prod_type, Fintype.sum_bool, bern2]; ring

/-- `ev q = (1 − q) c − q h`: the value of executing at wrongness credence `q`.
Source: [[corr-wf14-inventory]] 2-013 / counterexamples.py `ev`
Kind: D
Fidelity: exact -/
def ev (h c q : ℝ) : ℝ := (1 - q) * c - q * h

/-- The posterior-optimal rule: execute iff `0 < ev q` (ties refrain).
Source: [[corr-wf14-inventory]] 2-013 / counterexamples.py (`ev(q) > 0`)
Kind: D
Fidelity: exact -/
noncomputable def exec (h c q : ℝ) : Bool := decide (0 < ev h c q)

/-- `lossExp q e`: the expected one-round loss at wrongness rate `q` under decision `e` — the script's
`loss_exp` (objective `q`) and `own_est` (the agent's `q`), one formula.
Source: [[corr-wf14-inventory]] 2-013 / counterexamples.py `loss_exp`, `own_est`
Kind: D
Fidelity: exact -/
noncomputable def lossExp (h c q : ℝ) (e : Bool) : ℝ := if e then q * h else (1 - q) * c

/-- `exec_of_pos` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma exec_of_pos {h c q : ℝ} (hq : 0 < ev h c q) : exec h c q = true := by
  simp [exec, hq]

/-- `exec_of_nonpos` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma exec_of_nonpos {h c q : ℝ} (hq : ev h c q ≤ 0) : exec h c q = false := by
  simp [exec, not_lt.2 hq]

/-- The toy's parameters. Source: 2-013. Kind: D. Fidelity: exact -/
structure Params where
  /-- objective wrongness per round -/
  qs : ℝ
  /-- the agent's credence at round 0 (both rounds) -/
  q0 : ℝ
  /-- the agent's credence at round 1 (predictable) -/
  q1 : ℝ
  h : ℝ
  c : ℝ
  hqs : qs ∈ Set.Icc (0 : ℝ) 1
  hq0 : q0 ∈ Set.Icc (0 : ℝ) 1
  hq1 : q1 ∈ Set.Icc (0 : ℝ) 1
  hh : 0 ≤ h
  hc : 0 ≤ c

/-- **The two-round loss toy as an `AgentView`** (trivial filtrations; the press always on and
uninformative, so `executed = ¬κ` with `κ` the posterior-optimal rule).
Source: [[corr-wf14-inventory]] 2-013, 2-014–2-016 / counterexamples.py (A1, A2, A8), checks.py (C6)
Kind: D
Fidelity: exact (the script's model, as the `T = 1` / `T = 0` instance of S2) -/
noncomputable def toy (P : Params) : AgentView (Bool × Bool) Unit where
  μ := bern2 P.qs P.qs P.hqs P.hqs
  F := Atoms.trivial
  Fpre := Atoms.trivial
  post_subset_pre _ _ := subset_rfl
  pre_succ_subset_post _ _ := subset_rfl
  wrong t ω := if t = 0 then ω.1 else if t = 1 then ω.2 else false
  mag _ _ := ()
  hOf _ := P.h
  cOf _ := P.c
  hOf_nonneg _ := P.hh
  cOf_nonneg _ := P.hc
  pressed _ _ := true
  pressed_meas _ _ _ _ := rfl
  kappa t _ := !(exec P.h P.c (if t = 0 then P.q0 else P.q1))
  kappa_meas _ _ _ _ := rfl
  irr _ _ := false
  cat _ _ := false
  cat_absorbing _ _ _ h := h
  agentLaw t _ := if t = 0 then bern2 P.q0 P.q0 P.hq0 P.hq0 else bern2 P.q0 P.q1 P.hq0 P.hq1
  agentLaw_meas _ _ _ _ := rfl
  L _ := univ

variable (P : Params)

/-- `toy_μ` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma toy_μ : (toy P).μ = bern2 P.qs P.qs P.hqs P.hqs := rfl
/-- `toy_F` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma toy_F : (toy P).F = Atoms.trivial := rfl
/-- `toy_agentLaw_zero` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma toy_agentLaw_zero (ω : Bool × Bool) : (toy P).agentLaw 0 ω = bern2 P.q0 P.q0 P.hq0 P.hq0 := rfl
/-- `toy_agentLaw_one` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma toy_agentLaw_one (ω : Bool × Bool) : (toy P).agentLaw 1 ω = bern2 P.q0 P.q1 P.hq0 P.hq1 := rfl

/-- `toy_executed` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_executed (t : ℕ) (ω : Bool × Bool) :
    (toy P).executed t ω = exec P.h P.c (if t = 0 then P.q0 else P.q1) := by
  simp [ShutdownProc.executed, toy]

/-- `toy_executed_fun` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_executed_fun (t : ℕ) :
    (toy P).executed t = fun _ => exec P.h P.c (if t = 0 then P.q0 else P.q1) :=
  funext (toy_executed P t)

/-- The round-`0` loss: `W₀ h` if executed, `(1 − W₀) c` if refrained.
Source: 2-013. Kind: L. Fidelity: exact -/
lemma toy_loss_zero (ω : Bool × Bool) :
    (toy P).loss 0 ω = if exec P.h P.c P.q0 then (if ω.1 then P.h else 0) else (if ω.1 then 0 else P.c) := by
  unfold ShutdownProc.loss ShutdownProc.harm ShutdownProc.omission ShutdownProc.H ShutdownProc.C
  rw [toy_executed_fun]
  simp only [if_true]
  cases he : exec P.h P.c P.q0 <;> cases hw : ω.1 <;> simp [toy, indB, hw, he]

/-- The round-`1` loss. Source: 2-013. Kind: L. Fidelity: exact -/
lemma toy_loss_one (ω : Bool × Bool) :
    (toy P).loss 1 ω = if exec P.h P.c P.q1 then (if ω.2 then P.h else 0) else (if ω.2 then 0 else P.c) := by
  unfold ShutdownProc.loss ShutdownProc.harm ShutdownProc.omission ShutdownProc.H ShutdownProc.C
  rw [toy_executed_fun]
  simp only [one_ne_zero, if_false]
  cases he : exec P.h P.c P.q1 <;> cases hw : ω.2 <;> simp [toy, indB, hw, he]

/-- Expectation of the round-`0` loss under a product law with `P(W₀) = p₀`: `lossExp p₀ (exec q₀)`.
Source: 2-013. Kind: L. Fidelity: exact -/
lemma expect_loss_zero (p₀ p₁ : ℝ) (h₀ h₁) :
    expect (bern2 p₀ p₁ h₀ h₁) ((toy P).loss 0) = lossExp P.h P.c p₀ (exec P.h P.c P.q0) := by
  have e : (toy P).loss 0 = fun ω => if exec P.h P.c P.q0 then (if ω.1 then P.h else 0)
      else (if ω.1 then 0 else P.c) := funext (toy_loss_zero P)
  rw [e, expect_bern2]
  cases exec P.h P.c P.q0 <;> simp [lossExp] <;> ring

/-- Expectation of the round-`1` loss under a product law with `P(W₁) = p₁`: `lossExp p₁ (exec q₁)`.
Source: 2-013. Kind: L. Fidelity: exact -/
lemma expect_loss_one (p₀ p₁ : ℝ) (h₀ h₁) :
    expect (bern2 p₀ p₁ h₀ h₁) ((toy P).loss 1) = lossExp P.h P.c p₁ (exec P.h P.c P.q1) := by
  have e : (toy P).loss 1 = fun ω => if exec P.h P.c P.q1 then (if ω.2 then P.h else 0)
      else (if ω.2 then 0 else P.c) := funext (toy_loss_one P)
  rw [e, expect_bern2]
  cases exec P.h P.c P.q1 <;> simp [lossExp] <;> ring

/-- `toy_R_one_one` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_R_one_one (ω : Bool × Bool) : (toy P).R 1 1 ω = (toy P).loss 1 ω := by
  simp [AgentView.R]

/-- `toy_R_one_zero` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_R_one_zero (ω : Bool × Bool) : (toy P).R 1 0 ω = (toy P).loss 0 ω + (toy P).loss 1 ω := by
  rw [(toy P).R_succ 1 0 (by norm_num), toy_R_one_one]

/-- `toy_R_zero_zero` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_R_zero_zero (ω : Bool × Bool) : (toy P).R 0 0 ω = (toy P).loss 0 ω := by
  simp [AgentView.R]

/-- `Ψ₁ = lossExp q₁ (exec q₁)`: the agent's own round-`1` estimate.
Source: counterexamples.py `Psi1 = own_est(q1, ex1)`. Kind: L. Fidelity: exact -/
lemma toy_Psi_one (ω : Bool × Bool) : (toy P).Psi 1 1 ω = lossExp P.h P.c P.q1 (exec P.h P.c P.q1) := by
  unfold AgentView.Psi
  have e : (toy P).R 1 1 = (toy P).loss 1 := funext (toy_R_one_one P)
  rw [e]
  show expect (bern2 P.q0 P.q1 P.hq0 P.hq1) ((toy P).loss 1) = _
  exact expect_loss_one P _ _ _ _

/-- `Ψ₀ = lossExp q₀ (exec q₀) + lossExp q₀ (exec q₁)`: `P₀` foresees the round-`1` decision and
prices it at its own credence.
Source: counterexamples.py `Psi0 = own_est(q0, ex0) + loss_exp(q0, ex1)`. Kind: L. Fidelity: exact -/
lemma toy_Psi_zero (ω : Bool × Bool) :
    (toy P).Psi 1 0 ω = lossExp P.h P.c P.q0 (exec P.h P.c P.q0) + lossExp P.h P.c P.q0 (exec P.h P.c P.q1) := by
  unfold AgentView.Psi
  have e : (toy P).R 1 0 = fun ω => (toy P).loss 0 ω + (toy P).loss 1 ω := funext (toy_R_one_zero P)
  rw [e]
  show expect (bern2 P.q0 P.q0 P.hq0 P.hq0) _ = _
  rw [Found.CorrThreeStep.expect_add, expect_loss_zero, expect_loss_one]

/-- `Ψ₂ = 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_Psi_two (ω : Bool × Bool) : (toy P).Psi 1 2 ω = 0 := (toy P).Psi_top 1 ω

/-- `E*[R₁] = lossExp q* (exec q₁)`. Source: counterexamples.py. Kind: L. Fidelity: exact -/
lemma toy_expect_R_one : expect (toy P).μ ((toy P).R 1 1) = lossExp P.h P.c P.qs (exec P.h P.c P.q1) := by
  have e : (toy P).R 1 1 = (toy P).loss 1 := funext (toy_R_one_one P)
  rw [e, toy_μ]; exact expect_loss_one P _ _ _ _

/-- `E*[R₀] = lossExp q* (exec q₀) + lossExp q* (exec q₁)`. Source: counterexamples.py. Kind: L. Fidelity: exact -/
lemma toy_expect_R_zero :
    expect (toy P).μ ((toy P).R 1 0) =
      lossExp P.h P.c P.qs (exec P.h P.c P.q0) + lossExp P.h P.c P.qs (exec P.h P.c P.q1) := by
  have e : (toy P).R 1 0 = fun ω => (toy P).loss 0 ω + (toy P).loss 1 ω := funext (toy_R_one_zero P)
  rw [e]
  show expect (bern2 P.qs P.qs P.hqs P.hqs) _ = _
  rw [Found.CorrThreeStep.expect_add, expect_loss_zero, expect_loss_one]

/-- `E_{P₀}[Ψ₁] = Ψ₁` (constant). Source: counterexamples.py `E0_Psi1 = Psi1`. Kind: L. Fidelity: exact -/
lemma toy_E0_Psi_one (ω : Bool × Bool) :
    expect ((toy P).agentLaw 0 ω) ((toy P).Psi 1 1) = lossExp P.h P.c P.q1 (exec P.h P.c P.q1) := by
  have e : (toy P).Psi 1 1 = fun _ => lossExp P.h P.c P.q1 (exec P.h P.c P.q1) := funext (toy_Psi_one P)
  rw [e, Found.CorrThreeStep.expect_const]

/-- `E_{P₀}[R₁] = lossExp q₀ (exec q₁)`. Source: counterexamples.py `E0_R1`. Kind: L. Fidelity: exact -/
lemma toy_E0_R_one (ω : Bool × Bool) :
    expect ((toy P).agentLaw 0 ω) ((toy P).R 1 1) = lossExp P.h P.c P.q0 (exec P.h P.c P.q1) := by
  have e : (toy P).R 1 1 = (toy P).loss 1 := funext (toy_R_one_one P)
  rw [e]
  show expect (bern2 P.q0 P.q0 P.hq0 P.hq0) _ = _
  exact expect_loss_one P _ _ _ _

/-- `E_{P₀}[ℓ₀] = lossExp q₀ (exec q₀)`. Source: counterexamples.py `own_est(q0, ex0)`. Kind: L. Fidelity: exact -/
lemma toy_E0_loss_zero (ω : Bool × Bool) :
    expect ((toy P).agentLaw 0 ω) ((toy P).loss 0) = lossExp P.h P.c P.q0 (exec P.h P.c P.q0) := by
  show expect (bern2 P.q0 P.q0 P.hq0 P.hq0) _ = _
  exact expect_loss_zero P _ _ _ _

/-- The round-`0` optimism drift (trivial atoms): `Δ₀ = Ψ₁ + E*[ℓ₀] − Ψ₀`.
Source: counterexamples.py `Delta0`. Kind: L. Fidelity: exact -/
lemma toy_drift_zero (ω : Bool × Bool) :
    (toy P).drift 1 0 ω =
      lossExp P.h P.c P.q1 (exec P.h P.c P.q1) + lossExp P.h P.c P.qs (exec P.h P.c P.q0) -
        (lossExp P.h P.c P.q0 (exec P.h P.c P.q0) + lossExp P.h P.c P.q0 (exec P.h P.c P.q1)) := by
  unfold AgentView.drift
  rw [toy_F, condSum_trivial, condSum_trivial, Found.CorrThreeStep.expect_add]
  have e1 : (toy P).Psi 1 1 = fun _ => lossExp P.h P.c P.q1 (exec P.h P.c P.q1) := funext (toy_Psi_one P)
  have e0 : (toy P).Psi 1 0 = fun _ => lossExp P.h P.c P.q0 (exec P.h P.c P.q0) +
      lossExp P.h P.c P.q0 (exec P.h P.c P.q1) := funext (toy_Psi_zero P)
  rw [e1, e0, Found.CorrThreeStep.expect_const, Found.CorrThreeStep.expect_const, toy_μ, expect_loss_zero]

/-- The round-`1` optimism drift: `Δ₁ = E*[ℓ₁] − Ψ₁`. Source: checks.py C6. Kind: L. Fidelity: exact -/
lemma toy_drift_one (ω : Bool × Bool) :
    (toy P).drift 1 1 ω = lossExp P.h P.c P.qs (exec P.h P.c P.q1) - lossExp P.h P.c P.q1 (exec P.h P.c P.q1) := by
  unfold AgentView.drift
  rw [toy_F, condSum_trivial, condSum_trivial, Found.CorrThreeStep.expect_add]
  have e2 : (toy P).Psi 1 2 = fun _ => 0 := funext (toy_Psi_two P)
  have e1 : (toy P).Psi 1 1 = fun _ => lossExp P.h P.c P.q1 (exec P.h P.c P.q1) := funext (toy_Psi_one P)
  rw [e2, e1, Found.CorrThreeStep.expect_const, Found.CorrThreeStep.expect_const, toy_μ, expect_loss_one]
  ring

/-- One round (`T = 0`): `Ψ₀ = lossExp q₀ (exec q₀)`. Source: counterexamples.py A8. Kind: L. Fidelity: exact -/
lemma toy_Psi_zero_zero (ω : Bool × Bool) : (toy P).Psi 0 0 ω = lossExp P.h P.c P.q0 (exec P.h P.c P.q0) := by
  unfold AgentView.Psi
  have e : (toy P).R 0 0 = (toy P).loss 0 := funext (toy_R_zero_zero P)
  rw [e]
  show expect (bern2 P.q0 P.q0 P.hq0 P.hq0) _ = _
  exact expect_loss_zero P _ _ _ _

/-- One round: `E*[ℓ₀] = lossExp q* (exec q₀)`. Source: counterexamples.py A8. Kind: L. Fidelity: exact -/
lemma toy_expect_loss_zero : expect (toy P).μ ((toy P).loss 0) = lossExp P.h P.c P.qs (exec P.h P.c P.q0) := by
  rw [toy_μ]; exact expect_loss_zero P _ _ _ _

/-- One round: `Δ₀ = E*[ℓ₀] − Ψ₀`. Source: counterexamples.py A8 `Delta0_p`. Kind: L. Fidelity: exact -/
lemma toy_drift_zero_zero (ω : Bool × Bool) :
    (toy P).drift 0 0 ω = lossExp P.h P.c P.qs (exec P.h P.c P.q0) - lossExp P.h P.c P.q0 (exec P.h P.c P.q0) := by
  unfold AgentView.drift
  rw [toy_F, condSum_trivial, condSum_trivial, Found.CorrThreeStep.expect_add]
  have e1 : (toy P).Psi 0 1 = fun _ => 0 := funext ((toy P).Psi_top 0)
  have e0 : (toy P).Psi 0 0 = fun _ => lossExp P.h P.c P.q0 (exec P.h P.c P.q0) := funext (toy_Psi_zero_zero P)
  rw [e1, e0, Found.CorrThreeStep.expect_const, Found.CorrThreeStep.expect_const, toy_expect_loss_zero]
  ring

/-! ### The witnesses: `h = 1`, `c = 3/5`, threshold `3/8` -/

/-- `exec_half` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma exec_half : exec 1 (3 / 5) (1 / 2) = false := exec_of_nonpos (by norm_num [ev])
/-- `exec_three_quarters` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma exec_three_quarters : exec 1 (3 / 5) (3 / 4) = false := exec_of_nonpos (by norm_num [ev])
/-- `exec_three_eighths` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma exec_three_eighths : exec 1 (3 / 5) (3 / 8) = false := exec_of_nonpos (by norm_num [ev])
/-- `exec_quarter` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma exec_quarter : exec 1 (3 / 5) (1 / 4) = true := exec_of_pos (by norm_num [ev])

/-- A1's parameters: `q* = 1/2`, `q₀ = 1/2`, `q₁ = 3/4` (predictably more conservative, no evidence).
Source: counterexamples.py A1. Kind: D. Fidelity: exact -/
noncomputable def a1P : Params :=
  ⟨1 / 2, 1 / 2, 3 / 4, 1, 3 / 5, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

/-- `a1P_qs` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma a1P_qs : a1P.qs = 1 / 2 := rfl
/-- `a1P_q0` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma a1P_q0 : a1P.q0 = 1 / 2 := rfl
/-- `a1P_q1` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma a1P_q1 : a1P.q1 = 3 / 4 := rfl
/-- `a1P_h` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma a1P_h : a1P.h = 1 := rfl
/-- `a1P_c` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma a1P_c : a1P.c = 3 / 5 := rfl

/-- **A1 — refutes Statement 8's first "iff" ("is a potential iff reflection holds").** At `A1`:
the `P₀`-chain inequality holds strictly (`E_{P₀}[Ψ₁] = 3/20 ≤ Ψ₀ − E_{P₀}[ℓ₀] = 3/10`), the
unconditional Mart identity fails (`3/20 ≠ E_{P₀}[R₁] = 3/10`), and the round-`1` certificate is
false under `P*` (`E*[R₁] = 3/10 > Ψ₁ = 3/20`). So the chain is neither equivalent to reflection
nor sufficient for anything under `P*`. Surviving neighbour: 8(a) as the one-way `chain_of_uncondMart`.
Source: [[corr-wf14-inventory]] 2-014 / invariant.md Statement 8 title l. 81 ("is a potential **iff** reflection holds"); counterexamples.py A1
Kind: N+ (refutation)
Fidelity: exact (the script's three checks, on the `AgentView` instance)
Hyps: (a) only -/
theorem a1 :
    expect ((toy a1P).agentLaw 0 (true, true)) ((toy a1P).Psi 1 1) = 3 / 20 ∧
      (toy a1P).Psi 1 0 (true, true) - expect ((toy a1P).agentLaw 0 (true, true)) ((toy a1P).loss 0) = 3 / 10 ∧
      ¬ (toy a1P).uncondMart 1 0 (true, true) ∧
      expect ((toy a1P).agentLaw 0 (true, true)) ((toy a1P).R 1 1) = 3 / 10 ∧
      expect (toy a1P).μ ((toy a1P).R 1 1) = 3 / 10 ∧ (toy a1P).Psi 1 1 (true, true) = 3 / 20 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [toy_E0_Psi_one]; simp only [a1P_h, a1P_c, a1P_q1, exec_three_quarters]; norm_num [lossExp]
  · rw [toy_Psi_zero, toy_E0_loss_zero]
    simp only [a1P_h, a1P_c, a1P_q0, a1P_q1, exec_half, exec_three_quarters]; norm_num [lossExp]
  · unfold AgentView.uncondMart
    rw [toy_E0_Psi_one, toy_E0_R_one]
    simp only [a1P_h, a1P_c, a1P_q0, a1P_q1, exec_three_quarters]; norm_num [lossExp]
  · rw [toy_E0_R_one]; simp only [a1P_h, a1P_c, a1P_q0, a1P_q1, exec_three_quarters]; norm_num [lossExp]
  · rw [toy_expect_R_one]; simp only [a1P_h, a1P_c, a1P_qs, a1P_q1, exec_three_quarters]; norm_num [lossExp]
  · rw [toy_Psi_one]; simp only [a1P_h, a1P_c, a1P_q1, exec_three_quarters]; norm_num [lossExp]

/-- A8's parameters (one round): credence `1/4` (executes), objective `1/8`.
Source: counterexamples.py A8. Kind: D. Fidelity: exact -/
noncomputable def a8P : Params :=
  ⟨1 / 8, 1 / 4, 1 / 4, 1, 3 / 5, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

/-- `a8P_qs` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma a8P_qs : a8P.qs = 1 / 8 := rfl
/-- `a8P_q0` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma a8P_q0 : a8P.q0 = 1 / 4 := rfl
/-- `a8P_q1` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma a8P_q1 : a8P.q1 = 1 / 4 := rfl
/-- `a8P_h` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma a8P_h : a8P.h = 1 := rfl
/-- `a8P_c` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma a8P_c : a8P.c = 3 / 5 := rfl

/-- **A8 — refutes Statement 8's second "iff" ("certifies a finite-time regret bound iff its one-step
forecasts are calibrated").** One round, a *pessimistic* agent: `Ψ₀ = 1/4`, `E*[ℓ₀] = 1/8`,
`Δ₀ = −1/8 ≤ 0`, the bound `E*[Reg₀] = 1/8 ≤ 1/4` holds (through `expect_Reg_le_const`), and the
one-step forecasts disagree (`1/4 ≠ 1/8`). Surviving neighbour: 8(b) with `Δ_t ≤ 0` as the hypothesis.
Source: [[corr-wf14-inventory]] 2-015 / invariant.md Statement 8 title l. 81 ("**iff** its one-step forecasts are calibrated"); counterexamples.py A8
Kind: N+ (refutation)
Fidelity: exact
Hyps: (a) only -/
theorem a8 :
    (toy a8P).executed 0 (true, true) = true ∧
      (toy a8P).Psi 0 0 (true, true) = 1 / 4 ∧ expect (toy a8P).μ ((toy a8P).loss 0) = 1 / 8 ∧
      (toy a8P).drift 0 0 (true, true) = -(1 / 8) ∧
      expect (toy a8P).μ ((toy a8P).Reg 0) ≤ 1 / 4 ∧
      expect (toy a8P).μ ((toy a8P).loss 0) ≠ a8P.q0 * a8P.h := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [toy_executed]; simp only [a8P_h, a8P_c, a8P_q0, if_true, exec_quarter]
  · rw [toy_Psi_zero_zero]; simp only [a8P_h, a8P_c, a8P_q0, exec_quarter]; norm_num [lossExp]
  · rw [toy_expect_loss_zero]; simp only [a8P_h, a8P_c, a8P_qs, a8P_q0, exec_quarter]; norm_num [lossExp]
  · rw [toy_drift_zero_zero]; simp only [a8P_h, a8P_c, a8P_qs, a8P_q0, exec_quarter]; norm_num [lossExp]
  · refine (toy a8P).expect_Reg_le_const 0 (fun t ht ω => ?_) (1 / 4) (fun ω => ?_)
    · have ht0 : t = 0 := Nat.le_zero.1 ht
      subst ht0
      rw [toy_drift_zero_zero]; simp only [a8P_h, a8P_c, a8P_qs, a8P_q0, exec_quarter]; norm_num [lossExp]
    · rw [toy_Psi_zero_zero]; simp only [a8P_h, a8P_c, a8P_q0, exec_quarter]; norm_num [lossExp]
  · rw [toy_expect_loss_zero]; simp only [a8P_h, a8P_c, a8P_qs, a8P_q0, exec_quarter]; norm_num [lossExp]

/-- **At `T = 0` the hypothesis of `expect_Reg_le` is its conclusion** (audit r1, B1): on the trivial
filtration `Δ₀ = E*[Reg₀] − E*[Ψ₀]`, so a one-round instance inhabits the package without exercising
the telescoping or the atom decomposition. `a8` is therefore **N− for the theorem** (it stays N+ as a
refutation of the develop's second "iff"); the N+ witness of `expect_Reg_le` at a horizon with content
is `ObsToy.certificate` (two rounds, non-trivial atoms, strict drift).
Source: invariant-final.md Statement 8(b) (the hypothesis); audit r1 (fidelity B1, adversarial B1)
Kind: L
Fidelity: n/a (a fact about the witness grade, not about the source) -/
theorem horizon_zero_squeeze (P : Params) (ω : Bool × Bool) :
    (toy P).drift 0 0 ω = expect (toy P).μ ((toy P).Reg 0) - expect (toy P).μ ((toy P).Psi 0 0) := by
  unfold AgentView.drift
  rw [toy_F, condSum_trivial, condSum_trivial, Found.CorrThreeStep.expect_add]
  have e1 : (toy P).Psi 0 1 = fun _ => 0 := funext ((toy P).Psi_top 0)
  have eR : (toy P).Reg 0 = (toy P).loss 0 := by funext ω'; simp [ShutdownProc.Reg]
  rw [e1, eR, Found.CorrThreeStep.expect_const]
  ring

/-- **`ville_Z` has no instance at A8 in the `toy` family**: on the trivial filtration `ℓ₀ = W₀ · h`
is not `𝓕₁`-measurable once the agent executes with `h > 0` (A8's agent does), so the named
hypothesis `lossesObservable` fails. This is a fact about A8 (and any member with a non-constant
loss), not about the family: the zero-stakes member inhabits the package vacuously
(`zeroStakes_ville`; audit r2, adversarial N1). The witness of `ville_Z` lives on the observed-loss
filtration (`ObsToy.ville`).
Source: invariant-final.md S2 step 5 (an executed round's outcome settles; the toy's filtration is trivial regardless); audit r1 B1
Kind: L
Fidelity: n/a -/
theorem a8_not_lossesObservable : ¬ (toy a8P).lossesObservable 1 := by
  intro h
  have h1 := h 1 (by norm_num) (true, true) (false, true) (by rw [toy_F]; exact Finset.mem_univ _)
  dsimp only at h1
  simp only [Finset.sum_range_one] at h1
  rw [toy_loss_zero, toy_loss_zero] at h1
  simp only [a8P_h, a8P_c, a8P_q0, exec_quarter, if_true] at h1
  norm_num at h1

/-- A2's parameters: `q₁ = 3/8`, exactly the threshold (refrains; more conservative).
Source: counterexamples.py A2. Kind: D. Fidelity: exact -/
noncomputable def a2P : Params :=
  ⟨1 / 2, 1 / 2, 3 / 8, 1, 3 / 5, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

/-- `a2P_qs` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma a2P_qs : a2P.qs = 1 / 2 := rfl
/-- `a2P_q0` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma a2P_q0 : a2P.q0 = 1 / 2 := rfl
/-- `a2P_q1` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma a2P_q1 : a2P.q1 = 3 / 8 := rfl
/-- `a2P_h` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma a2P_h : a2P.h = 1 := rfl
/-- `a2P_c` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma a2P_c : a2P.c = 3 / 5 := rfl

/-- **A2 — refutes Statement 8(c) "locality" and the converse of `honest_of_drift`.** Honest
certificates at both times (`E*[R₀] = 3/5 ≤ Ψ₀ = 3/5`, `E*[R₁] = 3/10 ≤ Ψ₁ = 3/8`), yet
`Δ₀ = 3/40 > 0`: honesty at every time does not give `Δ_t ≤ 0`, and the hypothesis is the
far-future condition of 8(c), not a local one. Surviving neighbour: 8(c) as stated in the final.
Source: [[corr-wf14-inventory]] 2-016 / invariant.md Statement 8(c) ("Locality. Only one-step forecasts need to be calibrated; nothing about the far future is assumed"); counterexamples.py A2
Kind: N+ (refutation)
Fidelity: exact
Hyps: (a) only -/
theorem a2 :
    expect (toy a2P).μ ((toy a2P).R 1 0) = 3 / 5 ∧ (toy a2P).Psi 1 0 (true, true) = 3 / 5 ∧
      expect (toy a2P).μ ((toy a2P).R 1 1) = 3 / 10 ∧ (toy a2P).Psi 1 1 (true, true) = 3 / 8 ∧
      (∀ ω, (toy a2P).honestAt 1 0 ω) ∧ (∀ ω, (toy a2P).honestAt 1 1 ω) ∧
      (toy a2P).drift 1 0 (true, true) = 3 / 40 := by
  refine ⟨?_, ?_, ?_, ?_, fun ω => ?_, fun ω => ?_, ?_⟩
  · rw [toy_expect_R_zero]; simp only [a2P_h, a2P_c, a2P_qs, a2P_q0, a2P_q1, exec_half, exec_three_eighths]
    norm_num [lossExp]
  · rw [toy_Psi_zero]; simp only [a2P_h, a2P_c, a2P_q0, a2P_q1, exec_half, exec_three_eighths]
    norm_num [lossExp]
  · rw [toy_expect_R_one]; simp only [a2P_h, a2P_c, a2P_qs, a2P_q1, exec_three_eighths]; norm_num [lossExp]
  · rw [toy_Psi_one]; simp only [a2P_h, a2P_c, a2P_q1, exec_three_eighths]; norm_num [lossExp]
  · unfold AgentView.honestAt
    rw [toy_F, condSum_trivial, atomMass_trivial, toy_expect_R_zero, toy_Psi_zero]
    simp only [a2P_h, a2P_c, a2P_qs, a2P_q0, a2P_q1, exec_half, exec_three_eighths]; norm_num [lossExp]
  · unfold AgentView.honestAt
    rw [toy_F, condSum_trivial, atomMass_trivial, toy_expect_R_one, toy_Psi_one]
    simp only [a2P_h, a2P_c, a2P_qs, a2P_q1, exec_three_eighths]; norm_num [lossExp]
  · rw [toy_drift_zero]; simp only [a2P_h, a2P_c, a2P_qs, a2P_q0, a2P_q1, exec_half, exec_three_eighths]
    norm_num [lossExp]

/-- **A2, sharpened (audit r1, adversarial N5)**: in the same instance the one-step forecasts *are*
calibrated — `E_{P₀}[ℓ₀] = E*[ℓ₀] = 3/10` and `E_{P₀}[Ψ₁] = E*[Ψ₁] = 3/8` — and `Δ₀ = 3/40 > 0`
nonetheless (`a2`). So the develop's parenthetical "`Δ_t ≤ 0` … holds whenever `P_t` and `P*` agree on
the one-step forecasts `E[ℓ_t ∣ 𝓕_t]` and `E[Ψ_{t+1} ∣ 𝓕_t]`" is refuted *detached from 8(a)*:
agreement on both one-step forecasts alone does not give `Δ_t ≤ 0`, because `Ψ_t` itself is priced at
the agent's credence. **Scope** (audit r2, fidelity N1): the parenthetical is 8(b) of a statement whose
8(a) is the agent's reflection (the unconditional Mart identity); under 8(a) it is exact —
`drift_eq_zero_of_uncondMart_of_calibrated` gives `Δ_t = 0` — and in A2 the agent is not reflective
(`a2_not_uncondMart`), so the develop's own standing hypothesis fails in this instance.
Source: [[corr-wf14-inventory]] 2-016 / invariant.md Statement 8(b) l. 83 ("which holds whenever `P_t` and `P*` agree on the one-step forecasts"); counterexamples.py A2
Kind: N+ (refutation of the parenthetical detached from 8(a))
Fidelity: exact
Hyps: (a) only -/
theorem a2_calibrated (ω : Bool × Bool) :
    expect ((toy a2P).agentLaw 0 ω) ((toy a2P).loss 0) = expect (toy a2P).μ ((toy a2P).loss 0) ∧
      expect (toy a2P).μ ((toy a2P).loss 0) = 3 / 10 ∧
      expect ((toy a2P).agentLaw 0 ω) ((toy a2P).Psi 1 1) = expect (toy a2P).μ ((toy a2P).Psi 1 1) ∧
      expect (toy a2P).μ ((toy a2P).Psi 1 1) = 3 / 8 := by
  have hpsi : (toy a2P).Psi 1 1 = fun _ => 3 / 8 := by
    funext ω'; rw [toy_Psi_one]; simp only [a2P_h, a2P_c, a2P_q1, exec_three_eighths]; norm_num [lossExp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [toy_E0_loss_zero, toy_expect_loss_zero]
    simp only [a2P_h, a2P_c, a2P_qs, a2P_q0, exec_half]
  · rw [toy_expect_loss_zero]; simp only [a2P_h, a2P_c, a2P_qs, a2P_q0, exec_half]; norm_num [lossExp]
  · rw [toy_E0_Psi_one, hpsi, Found.CorrThreeStep.expect_const]
    simp only [a2P_h, a2P_c, a2P_q1, exec_three_eighths]; norm_num [lossExp]
  · rw [hpsi, Found.CorrThreeStep.expect_const]

/-- **In A2 the agent is not reflective**: `E_{P₀}[Ψ₁] = 3/8 ≠ 3/10 = E_{P₀}[R₁]`, so the develop's
8(a) (the unconditional Mart identity) fails in the instance that `a2_calibrated` uses against 8(b)'s
parenthetical — which, under 8(a), holds with equality (`drift_eq_zero_of_uncondMart_of_calibrated`).
Source: invariant.md Statement 8(a) l. 81; counterexamples.py A2; audit r2 (fidelity N1)
Kind: N+ (the scope of the refutation)
Fidelity: exact
Hyps: (a) only -/
theorem a2_not_uncondMart (ω : Bool × Bool) : ¬ (toy a2P).uncondMart 1 0 ω := by
  unfold AgentView.uncondMart
  rw [toy_E0_Psi_one, toy_E0_R_one]
  simp only [a2P_h, a2P_c, a2P_q0, a2P_q1, exec_three_eighths]
  norm_num [lossExp]

/-- C6's parameters: `q₁ = 1/4` (predictably optimistic, executes).
Source: checks.py C6. Kind: D. Fidelity: exact -/
noncomputable def c6P : Params :=
  ⟨1 / 2, 1 / 2, 1 / 4, 1, 3 / 5, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

/-- `c6P_qs` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma c6P_qs : c6P.qs = 1 / 2 := rfl
/-- `c6P_q0` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma c6P_q0 : c6P.q0 = 1 / 2 := rfl
/-- `c6P_q1` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma c6P_q1 : c6P.q1 = 1 / 4 := rfl
/-- `c6P_h` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma c6P_h : c6P.h = 1 := rfl
/-- `c6P_c` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma c6P_c : c6P.c = 3 / 5 := rfl

/-- **C6, predictable optimism (N+): honesty at `0` does not propagate.** `P₀` calibrated
(`Ψ₀ = 4/5 = E*[R₀]`), `P₁` predictably optimistic with no evidence: `Ψ₁ = 1/4 < 1/2 = E*[R₁]`
and `Δ₁ = 1/4 > 0`. The failure of Armstrong's sequential unbiasedness
(`E_{ρ_i} E_{ρ_j} X = E_{ρ_i} X`, `i < j`), as 8(d) names it.
Source: [[corr-wf14-inventory]] 2-080 (C6) / invariant-final.md Statement 8(d); checks.py C6
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem c6 :
    (toy c6P).executed 0 (true, true) = false ∧ (toy c6P).executed 1 (true, true) = true ∧
      (toy c6P).Psi 1 0 (true, true) = 4 / 5 ∧ expect (toy c6P).μ ((toy c6P).R 1 0) = 4 / 5 ∧
      (toy c6P).Psi 1 1 (true, true) = 1 / 4 ∧ expect (toy c6P).μ ((toy c6P).R 1 1) = 1 / 2 ∧
      (toy c6P).drift 1 1 (true, true) = 1 / 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [toy_executed]; simp only [c6P_h, c6P_c, c6P_q0, if_true, exec_half]
  · rw [toy_executed]; simp only [c6P_h, c6P_c, c6P_q1, one_ne_zero, if_false, exec_quarter]
  · rw [toy_Psi_zero]; simp only [c6P_h, c6P_c, c6P_q0, c6P_q1, exec_half, exec_quarter]; norm_num [lossExp]
  · rw [toy_expect_R_zero]; simp only [c6P_h, c6P_c, c6P_qs, c6P_q0, c6P_q1, exec_half, exec_quarter]
    norm_num [lossExp]
  · rw [toy_Psi_one]; simp only [c6P_h, c6P_c, c6P_q1, exec_quarter]; norm_num [lossExp]
  · rw [toy_expect_R_one]; simp only [c6P_h, c6P_c, c6P_qs, c6P_q1, exec_quarter]; norm_num [lossExp]
  · rw [toy_drift_one]; simp only [c6P_h, c6P_c, c6P_qs, c6P_q1, exec_quarter]; norm_num [lossExp]

/-! ### The zero-stakes member: `ville_Z`'s package has a (vacuous) trivial-filtration inhabitant

Audit r2, adversarial N1. The round-1 docstrings said "no trivial-filtration toy can inhabit
`ville_Z`"; the Lean (`a8_not_lossesObservable`) proves it at A8 only, and the universal is false:
with `h = c = 0` the loss is identically `0`, so `lossesObservable` holds on the trivial filtration
and `Δ ≡ 0` — `ville_Z` applies and says nothing (`E*[Ψ₀] = 0`, empty hit set for `λ > 0`). -/

/-- A8's agent and objective rate with zero stakes (`h = c = 0`).
Source: counterexamples.py A8 (credences and rate); audit r2 (adversarial N1). Kind: D. Fidelity: n/a (a probe instance) -/
noncomputable def zeroStakesP : Params :=
  ⟨1 / 8, 1 / 4, 1 / 4, 0, 0, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, le_rfl, le_rfl⟩

/-- `zeroStakesP_h` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma zeroStakesP_h : zeroStakesP.h = 0 := rfl
/-- `zeroStakesP_c` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma zeroStakesP_c : zeroStakesP.c = 0 := rfl

/-- `zeroStakes_loss` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma zeroStakes_loss (t : ℕ) (ω : Bool × Bool) : (toy zeroStakesP).loss t ω = 0 := by
  unfold ShutdownProc.loss ShutdownProc.harm ShutdownProc.omission ShutdownProc.H ShutdownProc.C
  simp [toy]

/-- `zeroStakes_R` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma zeroStakes_R (T t : ℕ) (ω : Bool × Bool) : (toy zeroStakesP).R T t ω = 0 := by
  simp [AgentView.R, zeroStakes_loss]

/-- `zeroStakes_Psi` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma zeroStakes_Psi (T t : ℕ) (ω : Bool × Bool) : (toy zeroStakesP).Psi T t ω = 0 := by
  unfold AgentView.Psi
  have : (toy zeroStakesP).R T t = fun _ => 0 := funext (zeroStakes_R T t)
  rw [this, Found.CorrThreeStep.expect_const]

/-- `zeroStakes_Z` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma zeroStakes_Z (T t : ℕ) (ω : Bool × Bool) : (toy zeroStakesP).Z T t ω = 0 := by
  unfold AgentView.Z
  simp [zeroStakes_Psi, zeroStakes_loss]

/-- `zeroStakes_drift` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma zeroStakes_drift (T t : ℕ) (ω : Bool × Bool) : (toy zeroStakesP).drift T t ω = 0 := by
  unfold AgentView.drift
  simp [condSum, zeroStakes_Psi, zeroStakes_loss]

/-- The named hypothesis `lossesObservable` holds on the trivial filtration: the loss is constant.
Source: audit r2 (adversarial N1). Kind: L. Fidelity: n/a -/
theorem zeroStakes_lossesObservable (T : ℕ) : (toy zeroStakesP).lossesObservable T := by
  intro t _ ω ω' _
  simp [zeroStakes_loss]

/-- The drift hypothesis holds at every horizon. Source: audit r2 (adversarial N1). Kind: L. Fidelity: n/a -/
theorem zeroStakes_drift_nonpos (T : ℕ) : ∀ t ≤ T, ∀ ω, (toy zeroStakesP).drift T t ω ≤ 0 :=
  fun t _ ω => by rw [zeroStakes_drift]

/-- **`ville_Z`'s full package is inhabited by a trivial-filtration `toy`** (the zero-stakes member), so
"no trivial-filtration toy can inhabit it" is false as a universal; `a8_not_lossesObservable` is
correctly scoped to A8. N−: the instance is vacuous (`zeroStakes_vacuous`).
Source: audit r2 (adversarial N1, probe `ZeroStakesVille`)
Kind: N− (vacuous inhabitant; the N+ witness is `ObsToy.ville`)
Fidelity: n/a
Hyps: (a) only -/
theorem zeroStakes_ville (T : ℕ) (lam : ℝ) (n : ℕ) (hn : n ≤ T + 1) :
    lam * probOf (toy zeroStakesP).μ (hitSet ((toy zeroStakesP).Z T) lam n) ≤
      expect (toy zeroStakesP).μ ((toy zeroStakesP).Psi T 0) :=
  (toy zeroStakesP).ville_Z T (zeroStakes_lossesObservable T) (zeroStakes_drift_nonpos T) lam n hn

/-- … and on it the theorem says nothing: the right-hand side is `0` and the hit set is empty for every
`λ > 0`.
Source: audit r2 (adversarial N1). Kind: L. Fidelity: n/a -/
theorem zeroStakes_vacuous (T : ℕ) {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    expect (toy zeroStakesP).μ ((toy zeroStakesP).Psi T 0) = 0 ∧
      hitSet ((toy zeroStakesP).Z T) lam n = ∅ := by
  constructor
  · have : (toy zeroStakesP).Psi T 0 = fun _ => 0 := funext (zeroStakes_Psi T 0)
    rw [this, Found.CorrThreeStep.expect_const]
  · ext ω
    rw [mem_hitSet]
    constructor
    · rintro ⟨t, _, h⟩
      rw [zeroStakes_Z] at h
      exact absurd h (not_le.2 hlam)
    · intro h
      simp at h

end LossToy

end Cleanroom.Corrigibility.CorrTrajectory
