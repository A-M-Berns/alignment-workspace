import Cleanroom.Corrigibility.CorrTrajectory.Certificate

/-!
# `corr-trajectory` — `LegitToy`: A3, the legitimacy-conditioned certificate (Statement 8(e))

The adversary's A3 model as an `AgentView` on `(W₀, W₁, L) : Bool × Bool × Bool`: two rounds of
the loss toy (`h = 1`, `c = 3/5`), the objective law `W₀, W₁ ~ Bern(1/2)` and the transition `0 → 1`
legitimate with probability `9/10` (`L`), independent. `P₀` is calibrated (the objective law); at
round `1` the agent knows the branch: on `L` it keeps credence `1/2` (refrains, `Ψ₁ = 3/10`), on `¬L`
it is optimistic at `1/4` (executes, `Ψ₁ = 1/4`). Round `0` refrains.

Checked: the legitimacy-conditioned Mart identity holds (`27/100 = 27/100`), the unconditional one
fails (`59/200 ≠ 8/25`), the `P₀`-chain inequality holds (`59/200 ≤ 8/25`), the round-`1`
certificate is dishonest exactly on `¬L` (`E*[R₁ 1_{¬L}] = 1/20 > Ψ₁ P(¬L) = 1/40`), and F2: both
sides of the legitimacy budget are `1/10` — `(H)` holds, the budget is tight.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect

namespace LegitToy

/-- The product law on `(W₀, W₁, L)`. Source: counterexamples.py A3. Kind: D. Fidelity: exact -/
noncomputable def bern3 (p₀ p₁ p₂ : ℝ) (h₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) (h₁ : p₁ ∈ Set.Icc (0 : ℝ) 1)
    (h₂ : p₂ ∈ Set.Icc (0 : ℝ) 1) : Distr (Bool × Bool × Bool) where
  mass ω := (if ω.1 then p₀ else 1 - p₀) * (if ω.2.1 then p₁ else 1 - p₁) * (if ω.2.2 then p₂ else 1 - p₂)
  nonneg ω := by
    refine mul_nonneg (mul_nonneg ?_ ?_) ?_ <;> split_ifs <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]
  sum_eq_one := by
    simp [Fintype.sum_prod_type, Fintype.sum_bool]; ring

/-- `expect_bern3` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_bern3 (p₀ p₁ p₂ : ℝ) (h₀ h₁ h₂) (f : Bool × Bool × Bool → ℝ) :
    expect (bern3 p₀ p₁ p₂ h₀ h₁ h₂) f =
      p₀ * p₁ * p₂ * f (true, true, true) + p₀ * p₁ * (1 - p₂) * f (true, true, false) +
      p₀ * (1 - p₁) * p₂ * f (true, false, true) + p₀ * (1 - p₁) * (1 - p₂) * f (true, false, false) +
      (1 - p₀) * p₁ * p₂ * f (false, true, true) + (1 - p₀) * p₁ * (1 - p₂) * f (false, true, false) +
      (1 - p₀) * (1 - p₁) * p₂ * f (false, false, true) +
      (1 - p₀) * (1 - p₁) * (1 - p₂) * f (false, false, false) := by
  simp [expect, Fintype.sum_prod_type, Fintype.sum_bool, bern3]; ring

/-- The objective law `W₀, W₁ ~ Bern(1/2)`, `L ~ Bern(9/10)` (also `P₀`). Source: A3. Kind: D. Fidelity: exact -/
noncomputable def objLaw : Distr (Bool × Bool × Bool) :=
  bern3 (1 / 2) (1 / 2) (9 / 10) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- `P₁` on the legitimate branch: credence `1/2`, branch known. Source: A3. Kind: D. Fidelity: exact -/
noncomputable def lawL : Distr (Bool × Bool × Bool) :=
  bern3 (1 / 2) (1 / 2) 1 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- `P₁` on the illegitimate branch: optimistic credence `1/4`, branch known. Source: A3. Kind: D. Fidelity: exact -/
noncomputable def lawI : Distr (Bool × Bool × Bool) :=
  bern3 (1 / 2) (1 / 4) 0 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- `expect_objLaw` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_objLaw (f : Bool × Bool × Bool → ℝ) :
    expect objLaw f = 1 / 2 * (1 / 2) * (9 / 10) * f (true, true, true) +
      1 / 2 * (1 / 2) * (1 - 9 / 10) * f (true, true, false) +
      1 / 2 * (1 - 1 / 2) * (9 / 10) * f (true, false, true) +
      1 / 2 * (1 - 1 / 2) * (1 - 9 / 10) * f (true, false, false) +
      (1 - 1 / 2) * (1 / 2) * (9 / 10) * f (false, true, true) +
      (1 - 1 / 2) * (1 / 2) * (1 - 9 / 10) * f (false, true, false) +
      (1 - 1 / 2) * (1 - 1 / 2) * (9 / 10) * f (false, false, true) +
      (1 - 1 / 2) * (1 - 1 / 2) * (1 - 9 / 10) * f (false, false, false) :=
  expect_bern3 _ _ _ _ _ _ f

/-- `expect_lawL` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_lawL (f : Bool × Bool × Bool → ℝ) :
    expect lawL f = 1 / 2 * (1 / 2) * 1 * f (true, true, true) + 1 / 2 * (1 / 2) * (1 - 1) * f (true, true, false) +
      1 / 2 * (1 - 1 / 2) * 1 * f (true, false, true) + 1 / 2 * (1 - 1 / 2) * (1 - 1) * f (true, false, false) +
      (1 - 1 / 2) * (1 / 2) * 1 * f (false, true, true) + (1 - 1 / 2) * (1 / 2) * (1 - 1) * f (false, true, false) +
      (1 - 1 / 2) * (1 - 1 / 2) * 1 * f (false, false, true) +
      (1 - 1 / 2) * (1 - 1 / 2) * (1 - 1) * f (false, false, false) :=
  expect_bern3 _ _ _ _ _ _ f

/-- `expect_lawI` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_lawI (f : Bool × Bool × Bool → ℝ) :
    expect lawI f = 1 / 2 * (1 / 4) * 0 * f (true, true, true) + 1 / 2 * (1 / 4) * (1 - 0) * f (true, true, false) +
      1 / 2 * (1 - 1 / 4) * 0 * f (true, false, true) + 1 / 2 * (1 - 1 / 4) * (1 - 0) * f (true, false, false) +
      (1 - 1 / 2) * (1 / 4) * 0 * f (false, true, true) + (1 - 1 / 2) * (1 / 4) * (1 - 0) * f (false, true, false) +
      (1 - 1 / 2) * (1 - 1 / 4) * 0 * f (false, false, true) +
      (1 - 1 / 2) * (1 - 1 / 4) * (1 - 0) * f (false, false, false) :=
  expect_bern3 _ _ _ _ _ _ f

/-- The filtration: nothing at `0`, the legitimacy flag at `1`, everything from `2`.
Source: counterexamples.py A3 (`P₀` knows `p`; at round `1` the branch is known)
Kind: D
Fidelity: exact -/
def atoms : Atoms (Bool × Bool × Bool) where
  fib t ω := if t = 0 then univ else if t = 1 then univ.filter (fun ω' => ω'.2.2 = ω.2.2) else {ω}
  mem_fib t ω := by
    rcases t with _ | _ | t <;> simp
  fib_eq_of_mem t ω ω' h := by
    rcases t with _ | _ | t
    · rfl
    · simp at h
      simp [h]
    · simp at h
      rw [h]
  fib_succ_subset t ω := by
    rcases t with _ | _ | t
    · simp
    · intro ω' h
      simp at h
      simp [h]
    · simp

/-- **The A3 model as an `AgentView`**.
Source: [[corr-wf14-inventory]] 2-017 / invariant-final.md Statement 8(e); counterexamples.py A3
Kind: D
Fidelity: exact -/
noncomputable def toy : AgentView (Bool × Bool × Bool) Unit where
  μ := objLaw
  F := atoms
  Fpre := atoms
  post_subset_pre _ _ := subset_rfl
  pre_succ_subset_post t ω := atoms.fib_succ_subset t ω
  wrong t ω := if t = 0 then ω.1 else if t = 1 then ω.2.1 else false
  mag _ _ := ()
  hOf _ := 1
  cOf _ := 3 / 5
  hOf_nonneg _ := by norm_num
  cOf_nonneg _ := by norm_num
  pressed _ _ := true
  pressed_meas _ _ _ _ := rfl
  kappa t ω := if t = 1 then ω.2.2 else true
  kappa_meas t ω ω' h := by
    rcases t with _ | _ | t
    · rfl
    · simp [atoms] at h
      simp [indB, h]
    · rfl
  irr _ _ := false
  cat _ _ := false
  cat_absorbing _ _ _ h := h
  agentLaw t ω := if t = 0 then objLaw else if ω.2.2 then lawL else lawI
  agentLaw_meas t ω ω' h := by
    rcases t with _ | _ | t
    · rfl
    · simp [atoms] at h
      simp [h]
    · simp [atoms] at h
      rw [h]
  L t := if t = 0 then univ.filter (fun ω => ω.2.2 = true) else univ

/-- `toy_μ` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma toy_μ : toy.μ = objLaw := rfl
/-- `toy_agentLaw_zero` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma toy_agentLaw_zero (ω : Bool × Bool × Bool) : toy.agentLaw 0 ω = objLaw := rfl
/-- `toy_agentLaw_one_true` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_agentLaw_one_true {ω : Bool × Bool × Bool} (h : ω.2.2 = true) : toy.agentLaw 1 ω = lawL := by
  simp [toy, h]
/-- `toy_agentLaw_one_false` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_agentLaw_one_false {ω : Bool × Bool × Bool} (h : ω.2.2 = false) : toy.agentLaw 1 ω = lawI := by
  simp [toy, h]

/-- `toy_executed_zero` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_executed_zero (ω : Bool × Bool × Bool) : toy.executed 0 ω = false := by
  simp [ShutdownProc.executed, toy]

/-- `toy_executed_one` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_executed_one (ω : Bool × Bool × Bool) : toy.executed 1 ω = !ω.2.2 := by
  simp [ShutdownProc.executed, toy]

/-- Round `0` refrains: `ℓ₀ = (1 − W₀) · 3/5`. Source: A3. Kind: L. Fidelity: exact -/
lemma toy_loss_zero (ω : Bool × Bool × Bool) : toy.loss 0 ω = if ω.1 then 0 else 3 / 5 := by
  unfold ShutdownProc.loss ShutdownProc.harm ShutdownProc.omission ShutdownProc.H ShutdownProc.C
  have e : toy.executed 0 = fun _ => false := funext toy_executed_zero
  rw [e]
  cases hw : ω.1 <;> simp [toy, indB, hw]

/-- Round `1`: on `L` refrain (`ℓ₁ = (1 − W₁) · 3/5`), on `¬L` execute (`ℓ₁ = W₁`).
Source: A3. Kind: L. Fidelity: exact -/
lemma toy_loss_one (ω : Bool × Bool × Bool) :
    toy.loss 1 ω = if ω.2.2 then (if ω.2.1 then 0 else 3 / 5) else (if ω.2.1 then 1 else 0) := by
  unfold ShutdownProc.loss ShutdownProc.harm ShutdownProc.omission ShutdownProc.H ShutdownProc.C
  have e : toy.executed 1 = fun ω => !ω.2.2 := funext toy_executed_one
  rw [e]
  cases hl : ω.2.2 <;> cases hw : ω.2.1 <;> simp [toy, indB, hw, hl]

/-- The closed form of `ℓ₁` as a function. Source: A3. Kind: L. Fidelity: exact -/
lemma toy_loss_one_fun :
    toy.loss 1 = fun ω => if ω.2.2 then (if ω.2.1 then 0 else 3 / 5) else (if ω.2.1 then 1 else 0) :=
  funext toy_loss_one

/-- `toy_loss_zero_fun` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_loss_zero_fun : toy.loss 0 = fun ω => if ω.1 then 0 else 3 / 5 := funext toy_loss_zero

/-- `toy_R_one_one` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_R_one_one : toy.R 1 1 = toy.loss 1 := by funext ω; simp [AgentView.R]

/-- `toy_R_one_zero` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_R_one_zero : toy.R 1 0 = fun ω => toy.loss 0 ω + toy.loss 1 ω := by
  funext ω; rw [toy.R_succ 1 0 (by norm_num), toy_R_one_one]

/-- `Ψ₁ = 3/10` on `L`, `1/4` on `¬L`. Source: A3. Kind: L. Fidelity: exact -/
lemma toy_Psi_one (ω : Bool × Bool × Bool) : toy.Psi 1 1 ω = if ω.2.2 then 3 / 10 else 1 / 4 := by
  unfold AgentView.Psi
  rw [toy_R_one_one, toy_loss_one_fun]
  cases hl : ω.2.2
  · rw [toy_agentLaw_one_false hl, expect_lawI]; norm_num
  · rw [toy_agentLaw_one_true hl, expect_lawL]; norm_num

/-- `toy_Psi_one_fun` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_Psi_one_fun : toy.Psi 1 1 = fun ω => if ω.2.2 then 3 / 10 else 1 / 4 := funext toy_Psi_one

/-- `Ψ₀ = 31/50 = 3/10 + 8/25`. Source: A3 `Psi0c`. Kind: L. Fidelity: exact -/
lemma toy_Psi_zero (ω : Bool × Bool × Bool) : toy.Psi 1 0 ω = 31 / 50 := by
  unfold AgentView.Psi
  rw [toy_R_one_zero, toy_loss_zero_fun, toy_loss_one_fun, toy_agentLaw_zero, expect_objLaw]
  norm_num

/-- **A3, the legitimacy-conditioned Mart identity holds**: `E_{P₀}[Ψ₁ 1_L] = 27/100 = E_{P₀}[R₁ 1_L]`.
Source: [[corr-wf14-inventory]] 2-017 / invariant-final.md Statement 8(e); counterexamples.py A3 ("conditional identity holds")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem a3_condMart (ω : Bool × Bool × Bool) : toy.condMart 1 0 ω := by
  unfold AgentView.condMart
  rw [toy_Psi_one_fun, toy_R_one_one, toy_loss_one_fun, toy_agentLaw_zero, expect_objLaw, expect_objLaw]
  simp [ind, toy]; norm_num

/-- **A3, the unconditional Mart identity fails**: `E_{P₀}[Ψ₁] = 59/200 ≠ 8/25 = E_{P₀}[R₁]` — so the
develop's 8(a) hypothesis is not (iv).
Source: [[corr-wf14-inventory]] 2-017 / invariant-final.md Statement 8(e), S4(iv); counterexamples.py A3
Kind: N+ (refutation of "(iv) gives 8(a)")
Fidelity: exact
Hyps: (a) only -/
theorem a3_not_uncondMart (ω : Bool × Bool × Bool) :
    expect (toy.agentLaw 0 ω) (toy.Psi 1 1) = 59 / 200 ∧ expect (toy.agentLaw 0 ω) (toy.R 1 1) = 8 / 25 ∧
      ¬ toy.uncondMart 1 0 ω := by
  have h1 : expect (toy.agentLaw 0 ω) (toy.Psi 1 1) = 59 / 200 := by
    rw [toy_Psi_one_fun, toy_agentLaw_zero, expect_objLaw]; norm_num
  have h2 : expect (toy.agentLaw 0 ω) (toy.R 1 1) = 8 / 25 := by
    rw [toy_R_one_one, toy_loss_one_fun, toy_agentLaw_zero, expect_objLaw]; norm_num
  refine ⟨h1, h2, ?_⟩
  unfold AgentView.uncondMart
  rw [h1, h2]; norm_num

/-- **A3, the `P₀`-chain inequality still holds**: `E_{P₀}[Ψ₁] = 59/200 ≤ 8/25 = Ψ₀ − E_{P₀}[ℓ₀]`.
Source: counterexamples.py A3 ("P_0-potential inequality still holds"). Kind: N+. Fidelity: exact -/
theorem a3_chain (ω : Bool × Bool × Bool) :
    expect (toy.agentLaw 0 ω) (toy.Psi 1 1) ≤ toy.Psi 1 0 ω - expect (toy.agentLaw 0 ω) (toy.loss 0) := by
  rw [(a3_not_uncondMart ω).1, toy_Psi_zero, toy_loss_zero_fun, toy_agentLaw_zero, expect_objLaw]
  norm_num

/-- The conditional sum at round `1` is the sum over the branch. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma condSum_one (X : Bool × Bool × Bool → ℝ) (ω : Bool × Bool × Bool) :
    condSum toy.μ toy.F 1 X ω = ∑ ω', if ω'.2.2 = ω.2.2 then objLaw.mass ω' * X ω' else 0 := by
  unfold condSum
  show ∑ ω' ∈ univ.filter (fun ω' : Bool × Bool × Bool => ω'.2.2 = ω.2.2), _ = _
  rw [sum_filter]
  rfl

/-- `atomMass_one` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma atomMass_one (ω : Bool × Bool × Bool) : atomMass toy.μ toy.F 1 ω = if ω.2.2 then 9 / 10 else 1 / 10 := by
  unfold atomMass
  show ∑ ω' ∈ univ.filter (fun ω' : Bool × Bool × Bool => ω'.2.2 = ω.2.2), _ = _
  rw [sum_filter]
  cases hl : ω.2.2 <;> simp [Fintype.sum_prod_type, Fintype.sum_bool, toy, objLaw, bern3] <;> norm_num

/-- **A3, the round-`1` certificate is dishonest exactly on the illegitimate branch**: on `¬L`,
`E*[R₁ 1_{¬L}] = 1/20 > 1/40 = Ψ₁ · P*(¬L)` (the source's `E*[R₁ ∣ ¬L] = 1/2 > 1/4`); on `L` it is
honest with equality (`27/100`).
Source: [[corr-wf14-inventory]] 2-017 / invariant-final.md Statement 8(e); counterexamples.py A3
Kind: N+
Fidelity: exact (product form)
Hyps: (a) only -/
theorem a3_honest_one (ω : Bool × Bool × Bool) : toy.honestAt 1 1 ω ↔ ω.2.2 = true := by
  unfold AgentView.honestAt
  rw [condSum_one, atomMass_one, toy_Psi_one, toy_R_one_one, toy_loss_one_fun]
  cases hl : ω.2.2 <;> simp [Fintype.sum_prod_type, Fintype.sum_bool, objLaw, bern3] <;> norm_num

/-- The round-`0` certificate is honest (with equality): `E*[R₀] = 31/50 = Ψ₀`.
Source: A3. Kind: N+. Fidelity: exact -/
theorem a3_honest_zero (ω : Bool × Bool × Bool) : toy.honestAt 1 0 ω := by
  unfold AgentView.honestAt
  have hm : atomMass toy.μ toy.F 0 ω = 1 := by
    unfold atomMass
    show ∑ ω' ∈ univ, toy.μ.mass ω' = 1
    exact toy.μ.sum_eq_one
  have hc : condSum toy.μ toy.F 0 (toy.R 1 0) ω = expect toy.μ (toy.R 1 0) := rfl
  rw [hm, hc, toy_Psi_zero, toy_R_one_zero, toy_loss_zero_fun, toy_loss_one_fun, toy_μ, expect_objLaw]
  norm_num

/-- `(H)` holds on the A3 model: honest on `G_t` for `t ≤ 1`. Source: Statement 8(e). Kind: L. Fidelity: exact -/
theorem a3_honestOnLegit : toy.honestOnLegit 1 := by
  intro t ht ω hG
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ht with rfl | rfl
  · exact a3_honest_zero ω
  · rw [a3_honest_one]
    simp only [AgentView.G, range_one, inf_singleton, toy, if_true, mem_filter, mem_univ, true_and] at hG
    exact hG

/-- **F2: the legitimacy budget is tight on A3** — `P*(some certificate dishonest by 1) = 1/10 =
∑_{t<1} P*(¬L_{t,t+1})`, through `legitimacy_budget` for `≤` and the `¬L` branch for `≥`.
Source: [[corr-wf14-inventory]] 2-080 (F2) / invariant-final.md Statement 8(e) ("F2: equality in the two-round A3 model")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem f2 :
    probOf toy.μ (toy.dishonestBy 1) = 1 / 10 ∧ ∑ t ∈ range 1, probOf toy.μ (toy.L t)ᶜ = 1 / 10 := by
  have hbud := toy.legitimacy_budget 1 a3_honestOnLegit
  have hL : ∑ t ∈ range 1, probOf toy.μ (toy.L t)ᶜ = 1 / 10 := by
    rw [sum_range_one]
    show probOf toy.μ (univ.filter (fun ω : Bool × Bool × Bool => ω.2.2 = true))ᶜ = _
    rw [probOf_compl]
    unfold probOf
    rw [sum_filter]
    simp [Fintype.sum_prod_type, Fintype.sum_bool, objLaw, bern3]; norm_num
  refine ⟨le_antisymm (hbud.1.trans (hbud.2.trans hL.le)) ?_, hL⟩
  have hsub : univ.filter (fun ω : Bool × Bool × Bool => ω.2.2 = false) ⊆ toy.dishonestBy 1 := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    simp only [AgentView.dishonestBy, mem_biUnion, mem_range, mem_filter, mem_univ, true_and]
    exact ⟨1, by norm_num, by rw [a3_honest_one]; simp [hω]⟩
  refine le_trans (le_of_eq ?_) (probOf_mono hsub)
  unfold probOf
  rw [sum_filter]
  simp [Fintype.sum_prod_type, Fintype.sum_bool, objLaw, bern3]; norm_num

end LegitToy

end Cleanroom.Corrigibility.CorrTrajectory
