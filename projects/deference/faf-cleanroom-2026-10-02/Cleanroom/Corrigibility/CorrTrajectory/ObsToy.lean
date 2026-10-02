import Cleanroom.Corrigibility.CorrTrajectory.LossToy

/-!
# `corr-trajectory` — `ObsToy`: the loss toy with the round-0 loss observed; the T7 witnesses

Repair of audit round 1, B1 (both lenses). The only instance of `expect_Reg_le`'s hypothesis
package was `LossToy.a8` at horizon `T = 0`, where on the trivial filtration
`Δ₀ = E*[Reg₀] − E*[Ψ₀]`: the hypothesis is the conclusion (`LossToy.horizon_zero_squeeze`), so the
telescoping and the atom decomposition were never exercised; `ville_Z` had no instance at all,
because on a trivial filtration the incurred loss is not `𝓕₁`-measurable once the agent executes
(`LossToy.a8_not_lossesObservable`).

This file ships the witness. `toyObs P` is the two-round toy of 2-013 on the filtration that
reveals `W₀` — hence `ℓ₀` — at time `1` and everything at time `2` (the observable history of a
process whose round-0 action executes, S2 step 5). At A8's parameters run for both rounds
(`q* = 1/8`, credence `1/4` at both rounds, executes; `h = 1`, `c = 3/5`):

* `Δ₀ = −1/8` on the trivial atom and `Δ₁ · atomMass = −(1/8) · P*(W₀ = b)` on each of the two round-1
  atoms (`drift_zero`, `drift_one`): the package of `expect_Reg_le 1` is inhabited with strict drift
  at both rounds and non-trivial atoms at round `1` (`drift_nonpos`);
* `expect_Reg_le_const 1` gives `E*[Reg₁] ≤ Ψ₀ = 1/2` *through the theorem*, and `E*[Reg₁] = 1/4`
  (`certificate`): two rounds, telescoping exercised, bound strict;
* `honest_of_drift 1` gives honesty at every `t ≤ 2` through the backward induction across the
  non-trivial level (`honest`), strict on both round-1 atoms;
* `lossesObservable 1` is discharged (`lossesObservable`), so `ville_Z` applies: at `λ = 1`,
  `n = 2`, `P*(∃ t ≤ 2, Z_t ≥ 1) = P*(W₀ ∨ W₁) = 15/64 ≤ Ψ₀ = 1/2` (`ville`), the hit set computed
  exactly (`hitSet_eq`).

Grade: N+ for `expect_Reg_le`, `expect_Reg_le_const`, `honest_of_drift`, `ville_Z`, `ville_Z_ratio`.
The objective law is i.i.d. Bernoulli and the agent's law is constant in `ω`, so `agentLaw_meas`,
`kappa_meas`, `pressed_meas` are `rfl`; the content is in the atoms at round `1` (masses `1/8`, `7/8`).
**The agent's law is left unconditioned on the revealed `W₀`** (at time `1` it still prices `W₀` at
`1/4`), which `R₁ = ℓ₁` does not involve; so `Ψ₁` is the same number on both round-1 atoms (audit r2,
fidelity N6 / adversarial N2). The section `Updating` ships the sharper witness at the same cost: the
same process with an agent that updates on the revealed `W₀` (credence `3/10` for `W₁` after a wrong
round, `1/4` after a right one), on which `Ψ₁` **depends on the atom** and the full package of the
three theorems is still inhabited, with `Δ₀ = −19/160` and `Δ₁ · mass ∈ {−7/320, −7/64}`.
Layer M (`Martingale`) remains unwitnessed — T15 did not land; the ledger says so.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect
open LossToy

namespace ObsToy

/-- The filtration that reveals `W₀` at time `1` and everything from `2`: `𝓕₀` trivial,
`𝓕₁ = σ(W₀)` (so `ℓ₀` is `𝓕₁`-measurable), `𝓕₂` discrete.
Source: invariant-final.md S1 (`𝓕_t` the observable history), S2 step 5 (an executed round's outcome settles)
Kind: D
Fidelity: exact (the observable history of a process that executes at round `0`) -/
def atoms : Atoms (Bool × Bool) where
  fib t ω := if t = 0 then univ else if t = 1 then univ.filter (fun ω' => ω'.1 = ω.1) else {ω}
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

/-- **The two-round loss toy with the round-0 loss observed, as an `AgentView`** — the fields of
`LossToy.toy` on the filtration `atoms` (both `𝓕` and `𝓕^-`; the press is uninformative).
Source: [[corr-wf14-inventory]] 2-013, 2-015 / counterexamples.py A8 run for two rounds; invariant-final.md S1–S2
Kind: D
Fidelity: exact (the script's model with the observable history as the filtration) -/
noncomputable def toyObs (P : Params) : AgentView (Bool × Bool) Unit where
  μ := bern2 P.qs P.qs P.hqs P.hqs
  F := atoms
  Fpre := atoms
  post_subset_pre _ _ := subset_rfl
  pre_succ_subset_post t ω := atoms.fib_succ_subset t ω
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

/-- `toyObs_μ` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma toyObs_μ : (toyObs P).μ = bern2 P.qs P.qs P.hqs P.hqs := rfl
/-- `toyObs_F` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma toyObs_F : (toyObs P).F = atoms := rfl
/-- The losses coincide with `LossToy.toy`'s: the filtration does not enter them.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toyObs_loss (t : ℕ) (ω : Bool × Bool) : (toyObs P).loss t ω = (toy P).loss t ω := rfl
/-- `toyObs_R` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toyObs_R (T t : ℕ) (ω : Bool × Bool) : (toyObs P).R T t ω = (toy P).R T t ω := rfl
/-- `toyObs_Psi` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toyObs_Psi (T t : ℕ) (ω : Bool × Bool) : (toyObs P).Psi T t ω = (toy P).Psi T t ω := rfl

/-- The conditional sum at time `0` is the expectation. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma condSum_zero (X : Bool × Bool → ℝ) (ω : Bool × Bool) :
    condSum (toyObs P).μ (toyObs P).F 0 X ω = expect (toyObs P).μ X := rfl

/-- The conditional sum at time `1` is the sum over the `W₀`-atom. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma condSum_one (X : Bool × Bool → ℝ) (ω : Bool × Bool) :
    condSum (toyObs P).μ (toyObs P).F 1 X ω =
      ∑ ω', if ω'.1 = ω.1 then (toyObs P).μ.mass ω' * X ω' else 0 := by
  unfold condSum
  show ∑ ω' ∈ univ.filter (fun ω' : Bool × Bool => ω'.1 = ω.1), _ = _
  rw [sum_filter]

/-! ### A8's pessimistic agent at both rounds: `q* = 1/8`, `q₀ = q₁ = 1/4`, `h = 1`, `c = 3/5` -/

/-- `ℓ₀ = W₀` (the agent executes at credence `1/4`, `h = 1`). Source: A8. Kind: L. Fidelity: exact -/
lemma loss_zero_fun : (toyObs a8P).loss 0 = fun ω => if ω.1 then 1 else 0 := by
  funext ω
  rw [toyObs_loss, toy_loss_zero]
  simp only [a8P_h, a8P_c, a8P_q0, exec_quarter, if_true]

/-- `ℓ₁ = W₁`. Source: A8. Kind: L. Fidelity: exact -/
lemma loss_one_fun : (toyObs a8P).loss 1 = fun ω => if ω.2 then 1 else 0 := by
  funext ω
  rw [toyObs_loss, toy_loss_one]
  simp only [a8P_h, a8P_c, a8P_q1, exec_quarter, if_true]

/-- `Ψ₁ = 1/4` (the agent's own number, constant). Source: A8. Kind: L. Fidelity: exact -/
lemma Psi_one_fun : (toyObs a8P).Psi 1 1 = fun _ => 1 / 4 := by
  funext ω
  rw [toyObs_Psi, toy_Psi_one]
  simp only [a8P_h, a8P_c, a8P_q1, exec_quarter]; norm_num [lossExp]

/-- `Ψ₀ = 1/2`. Source: A8. Kind: L. Fidelity: exact -/
lemma Psi_zero_fun : (toyObs a8P).Psi 1 0 = fun _ => 1 / 2 := by
  funext ω
  rw [toyObs_Psi, toy_Psi_zero]
  simp only [a8P_h, a8P_c, a8P_q0, a8P_q1, exec_quarter]; norm_num [lossExp]

/-- `Ψ₂ = 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Psi_two_fun : (toyObs a8P).Psi 1 2 = fun _ => 0 := funext ((toyObs a8P).Psi_top 1)

/-- The atom masses at time `1`: `P*(W₀ = b)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma atomMass_one (ω : Bool × Bool) :
    atomMass (toyObs a8P).μ (toyObs a8P).F 1 ω = if ω.1 then 1 / 8 else 7 / 8 := by
  unfold atomMass
  show ∑ ω' ∈ univ.filter (fun ω' : Bool × Bool => ω'.1 = ω.1), _ = _
  rw [sum_filter]
  cases hl : ω.1 <;> simp [Fintype.sum_prod_type, bern2] <;> norm_num

/-- `Δ₀ = −1/8` (the trivial atom). Source: A8 run for two rounds. Kind: L. Fidelity: exact -/
theorem drift_zero (ω : Bool × Bool) : (toyObs a8P).drift 1 0 ω = -(1 / 8) := by
  unfold AgentView.drift
  rw [condSum_zero, condSum_zero, Found.CorrThreeStep.expect_add, Psi_one_fun, Psi_zero_fun,
    loss_zero_fun, Found.CorrThreeStep.expect_const, Found.CorrThreeStep.expect_const, toyObs_μ,
    expect_bern2]
  simp only [a8P_qs]; norm_num

/-- `Δ₁ · atomMass = −(1/8) · P*(W₀ = b)` on the round-1 atom of `b`: strictly negative on both atoms.
Source: A8 run for two rounds. Kind: L. Fidelity: exact (product form) -/
theorem drift_one (ω : Bool × Bool) :
    (toyObs a8P).drift 1 1 ω = -(1 / 8) * (if ω.1 then 1 / 8 else 7 / 8) := by
  unfold AgentView.drift
  rw [Psi_two_fun, loss_one_fun, Psi_one_fun, condSum_one, condSum_one]
  cases hl : ω.1 <;> simp [Fintype.sum_prod_type, bern2] <;> norm_num

/-- **The hypothesis package of `expect_Reg_le 1`, `honest_of_drift 1` and `ville_Z 1`, inhabited with
strict drift**: `Δ_t ≤ 0` at both rounds on every atom, the round-1 atoms non-trivial.
Source: invariant-final.md Statement 8(b) (the hypothesis); counterexamples.py A8 run for two rounds
Kind: N+ (the full package at horizon `1`)
Fidelity: exact
Hyps: (a) only -/
theorem drift_nonpos : ∀ t ≤ 1, ∀ ω, (toyObs a8P).drift 1 t ω ≤ 0 := by
  intro t ht ω
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ht with rfl | rfl
  · rw [drift_zero]; norm_num
  · rw [drift_one]; split_ifs <;> norm_num

/-- **Observable losses**: `∑_{s<t} ℓ_s` is `𝓕_t`-measurable for `t ≤ 2` — `ℓ₀ = W₀` is revealed at
time `1` (the agent executed), and `𝓕₂` is discrete. This is the hypothesis `ville_Z` adds (F-1).
Source: invariant-final.md Statement 8(b) (implicit), S2 step 5; counterexamples.py A8 run for two rounds
Kind: N+ (the named hypothesis discharged on a non-trivial filtration)
Fidelity: exact
Hyps: (a) only -/
theorem lossesObservable : (toyObs a8P).lossesObservable 1 := by
  intro t ht ω ω' h
  rcases t with _ | _ | _ | t
  · simp
  · simp [toyObs, atoms] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [loss_zero_fun]
    simp [h]
  · simp [toyObs, atoms] at h
    subst h
    rfl
  · omega

/-- **`expect_Reg_le` at horizon `1`, exercised**: `E*[Reg₁] ≤ Ψ₀` *through the theorem* (both rounds'
drifts enter the telescoping; the round-1 atoms are non-trivial), with the two sides `1/4` and `1/2`:
the bound is strict, as the strict drift predicts.
Source: [[corr-wf14-inventory]] 078 / invariant-final.md Statement 8(b) (first display), (f); counterexamples.py A8 run for two rounds
Kind: N+ (witness of `expect_Reg_le`, `expect_Reg_le_const`)
Fidelity: exact
Hyps: (a) only -/
theorem certificate :
    expect (toyObs a8P).μ ((toyObs a8P).Reg 1) ≤ 1 / 2 ∧
      expect (toyObs a8P).μ ((toyObs a8P).Reg 1) = 1 / 4 ∧
      (∀ ω, (toyObs a8P).Psi 1 0 ω = 1 / 2) := by
  have hpsi : ∀ ω, (toyObs a8P).Psi 1 0 ω = 1 / 2 := fun ω => by simp [Psi_zero_fun]
  refine ⟨(toyObs a8P).expect_Reg_le_const 1 drift_nonpos (1 / 2) hpsi, ?_, hpsi⟩
  have e : (toyObs a8P).Reg 1 = fun ω => (if ω.1 then 1 else 0) + (if ω.2 then 1 else 0) := by
    funext ω
    unfold ShutdownProc.Reg
    rw [sum_range_succ, sum_range_one, loss_zero_fun, loss_one_fun]
  rw [e, toyObs_μ, expect_bern2]
  simp only [a8P_qs]; norm_num

/-- **`honest_of_drift` at horizon `1`, exercised**: honesty `E*[R_t ∣ 𝓕_t] ≤ Ψ_t` at every `t ≤ 2` on
every atom, through the backward induction (the tower step crosses the non-trivial level at `t = 1`);
and at `t = 1` the inequality is strict on both atoms:
`E*[R₁ 1_{W₀ = b}] = (1/8) · P*(W₀ = b) < (1/4) · P*(W₀ = b) = Ψ₁ · P*(W₀ = b)`.
Source: [[corr-wf14-inventory]] 078 / invariant-final.md Statement 8(c); counterexamples.py A8 run for two rounds
Kind: N+ (witness of `honest_of_drift`)
Fidelity: exact
Hyps: (a) only -/
theorem honest :
    (∀ t ≤ 2, ∀ ω, (toyObs a8P).honestAt 1 t ω) ∧
      ∀ ω, condSum (toyObs a8P).μ (toyObs a8P).F 1 ((toyObs a8P).R 1 1) ω =
        1 / 8 * atomMass (toyObs a8P).μ (toyObs a8P).F 1 ω := by
  refine ⟨(toyObs a8P).honest_of_drift 1 drift_nonpos, fun ω => ?_⟩
  have e : (toyObs a8P).R 1 1 = (toyObs a8P).loss 1 := by
    funext ω'; rw [toyObs_R, toy_R_one_one, toyObs_loss]
  rw [e, loss_one_fun, condSum_one, atomMass_one]
  cases hl : ω.1 <;> simp [Fintype.sum_prod_type, bern2] <;> norm_num

/-- `Z₀ = 1/2`. Source: Statement 8(b); A8 run for two rounds. Kind: L. Fidelity: exact -/
lemma Z_zero_fun : (toyObs a8P).Z 1 0 = fun _ => 1 / 2 := by
  funext ω; rw [(toyObs a8P).Z_zero]; simp [Psi_zero_fun]

/-- `Z₁ = 1/4 + W₀`. Source: Statement 8(b); A8 run for two rounds. Kind: L. Fidelity: exact -/
lemma Z_one_fun : (toyObs a8P).Z 1 1 = fun ω => 1 / 4 + if ω.1 then 1 else 0 := by
  funext ω; unfold AgentView.Z; rw [sum_range_one, Psi_one_fun, loss_zero_fun]

/-- `Z₂ = W₀ + W₁ = Reg₁`. Source: Statement 8(b); A8 run for two rounds. Kind: L. Fidelity: exact -/
lemma Z_two_fun : (toyObs a8P).Z 1 2 = fun ω => (if ω.1 then 1 else 0) + if ω.2 then 1 else 0 := by
  funext ω; unfold AgentView.Z
  rw [sum_range_succ, sum_range_one, Psi_two_fun, loss_zero_fun, loss_one_fun]; simp

/-- The hit set at `λ = 1`, `n = 2` is `{W₀ ∨ W₁}`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma hitSet_eq :
    hitSet ((toyObs a8P).Z 1) 1 2 = univ.filter (fun ω : Bool × Bool => ω.1 = true ∨ ω.2 = true) := by
  ext ⟨b₀, b₁⟩
  rw [mem_hitSet, mem_filter]
  simp only [mem_univ, true_and]
  cases b₀ <;> cases b₁
  · constructor
    · rintro ⟨t, ht, hZ⟩
      exfalso
      rcases t with _ | _ | _ | t
      · norm_num [Z_zero_fun] at hZ
      · norm_num [Z_one_fun] at hZ
      · norm_num [Z_two_fun] at hZ
      · omega
    · intro h; simp at h
  · constructor
    · intro _; simp
    · intro _; exact ⟨2, le_rfl, by rw [Z_two_fun]; norm_num⟩
  · constructor
    · intro _; simp
    · intro _; exact ⟨1, by norm_num, by rw [Z_one_fun]; norm_num⟩
  · constructor
    · intro _; simp
    · intro _; exact ⟨1, by norm_num, by rw [Z_one_fun]; norm_num⟩

/-- **`ville_Z` at horizon `1`, exercised** (Statement 8(b)(ii), Layer F): with observable losses and
strict drift at both rounds, Ville at `λ = 1`, `n = 2` reads `P*(∃ t ≤ 2, Z_t ≥ 1) ≤ E*[Ψ₀]` through the
theorem; the two sides are `P*(W₀ ∨ W₁) = 15/64` and `1/2`; the ratio form gives `≤ (1/2)/1`.
Source: [[corr-wf14-inventory]] 078 / invariant-final.md Statement 8(b) (second display); counterexamples.py A8 run for two rounds
Kind: N+ (witness of `ville_Z`, `ville_Z_ratio`: non-trivial atoms, `lossesObservable` discharged)
Fidelity: exact
Hyps: (a) only -/
theorem ville :
    1 * probOf (toyObs a8P).μ (hitSet ((toyObs a8P).Z 1) 1 2) ≤
        expect (toyObs a8P).μ ((toyObs a8P).Psi 1 0) ∧
      probOf (toyObs a8P).μ (hitSet ((toyObs a8P).Z 1) 1 2) = 15 / 64 ∧
      expect (toyObs a8P).μ ((toyObs a8P).Psi 1 0) = 1 / 2 ∧
      probOf (toyObs a8P).μ (hitSet ((toyObs a8P).Z 1) 1 2) ≤ (1 / 2) / 1 := by
  refine ⟨(toyObs a8P).ville_Z 1 lossesObservable drift_nonpos 1 2 le_rfl, ?_, ?_, ?_⟩
  · rw [hitSet_eq]
    unfold probOf
    rw [sum_filter]
    simp [Fintype.sum_prod_type, bern2]; norm_num
  · rw [Psi_zero_fun, Found.CorrThreeStep.expect_const]
  · exact (toyObs a8P).ville_Z_ratio 1 lossesObservable drift_nonpos (1 / 2)
      (fun ω => by simp [Psi_zero_fun]) one_pos 2 le_rfl

/-! ### `Updating`: the same process with an agent that updates on the revealed `W₀`

Audit r2 (adversarial N2, probe `AtomPsi`). On `toyObs a8P` the agent's law is constant in `ω`, so
`Ψ₁` takes the same value on both round-1 atoms; this section shows the N+ grade does not rest on
that: the agent below conditions on `W₀` (credence `3/10` for `W₁` after a wrong round, `1/4` after
a right one — both execute under S2 step 4's rule, `rule_consistent`), so `Ψ₁ = 3/10` on one atom
and `1/4` on the other, and the full package of `expect_Reg_le 1`, `honest_of_drift 1`, `ville_Z 1`
is still inhabited with the theorems applied. -/

namespace Updating

/-- Both post-update credences execute under the rule (`ev q > 0`), so `κ₁ = false` on both atoms is
S2 step 4's rule at both credences.
Source: invariant-final.md S2 step 4; counterexamples.py (the rule). Kind: L. Fidelity: exact -/
lemma rule_consistent : exec 1 (3 / 5) (3 / 10) = true ∧ exec 1 (3 / 5) (1 / 4) = true :=
  ⟨exec_of_pos (by norm_num [ev]), exec_of_pos (by norm_num [ev])⟩

/-- **The two-round toy on `ObsToy.atoms` with an agent that updates on the revealed `W₀`**: A8's
objective law and stakes, credence `1/4` at round `0` for both rounds, and at round `1` credence
`3/10` for `W₁` after a wrong round (`W₀` known to be `1`) and `1/4` after a right one.
Source: counterexamples.py A8 run for two rounds, with the round-1 credence conditioned on `W₀`; invariant-final.md S1–S2; audit r2 (adversarial N2)
Kind: D
Fidelity: exact (the observable history as the filtration; the agent's law `𝓕₁`-measurable by branch) -/
noncomputable def view : AgentView (Bool × Bool) Unit where
  μ := bern2 (1 / 8) (1 / 8) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
  F := atoms
  Fpre := atoms
  post_subset_pre _ _ := subset_rfl
  pre_succ_subset_post t ω := atoms.fib_succ_subset t ω
  wrong t ω := if t = 0 then ω.1 else if t = 1 then ω.2 else false
  mag _ _ := ()
  hOf _ := 1
  cOf _ := 3 / 5
  hOf_nonneg _ := by norm_num
  cOf_nonneg _ := by norm_num
  pressed _ _ := true
  pressed_meas _ _ _ _ := rfl
  kappa _ _ := false
  kappa_meas _ _ _ _ := rfl
  irr _ _ := false
  cat _ _ := false
  cat_absorbing _ _ _ h := h
  agentLaw t ω :=
    if t = 0 then bern2 (1 / 4) (1 / 4) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    else if ω.1 then bern2 1 (3 / 10) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    else bern2 0 (1 / 4) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
  agentLaw_meas t ω ω' h := by
    rcases t with _ | _ | t
    · rfl
    · simp [atoms] at h
      simp [h]
    · simp [atoms] at h
      rw [h]
  L _ := univ

/-- `view_loss_zero` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma view_loss_zero : view.loss 0 = fun ω => if ω.1 then 1 else 0 := by
  funext ω
  unfold ShutdownProc.loss ShutdownProc.harm ShutdownProc.omission ShutdownProc.H ShutdownProc.C
  cases hw : ω.1 <;> simp [view, indB, hw, ShutdownProc.executed]

/-- `view_loss_one` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma view_loss_one : view.loss 1 = fun ω => if ω.2 then 1 else 0 := by
  funext ω
  unfold ShutdownProc.loss ShutdownProc.harm ShutdownProc.omission ShutdownProc.H ShutdownProc.C
  cases hw : ω.2 <;> simp [view, indB, hw, ShutdownProc.executed]

/-- `view_R_one_one` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma view_R_one_one : view.R 1 1 = view.loss 1 := by
  funext ω; simp [AgentView.R]

/-- `view_R_one_zero` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma view_R_one_zero : view.R 1 0 = fun ω => view.loss 0 ω + view.loss 1 ω := by
  funext ω; rw [view.R_succ 1 0 (by norm_num)]; simp [AgentView.R]

/-- `view_agentLaw_zero` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma view_agentLaw_zero (ω : Bool × Bool) :
    view.agentLaw 0 ω = bern2 (1 / 4) (1 / 4) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ := rfl

/-- `view_agentLaw_one_true` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma view_agentLaw_one_true {ω : Bool × Bool} (h : ω.1 = true) :
    view.agentLaw 1 ω = bern2 1 (3 / 10) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ := by
  simp [view, h]

/-- `view_agentLaw_one_false` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma view_agentLaw_one_false {ω : Bool × Bool} (h : ω.1 = false) :
    view.agentLaw 1 ω = bern2 0 (1 / 4) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ := by
  simp [view, h]

/-- **`Ψ₁` depends on the atom**: `3/10` after a wrong round, `1/4` after a right one.
Source: counterexamples.py A8 (the round-1 estimate, conditioned on `W₀`); audit r2 (adversarial N2). Kind: L. Fidelity: exact -/
lemma view_Psi_one : view.Psi 1 1 = fun ω => if ω.1 then 3 / 10 else 1 / 4 := by
  funext ω
  unfold AgentView.Psi
  rw [view_R_one_one, view_loss_one]
  cases hl : ω.1
  · rw [view_agentLaw_one_false hl, expect_bern2]; norm_num
  · rw [view_agentLaw_one_true hl, expect_bern2]; norm_num

/-- `view_Psi_zero` (supporting lemma): `Ψ₀ = 1/2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma view_Psi_zero : view.Psi 1 0 = fun _ => 1 / 2 := by
  funext ω
  unfold AgentView.Psi
  rw [view_R_one_zero, view_loss_zero, view_loss_one, view_agentLaw_zero, expect_bern2]
  norm_num

/-- `view_Psi_two` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma view_Psi_two : view.Psi 1 2 = fun _ => 0 := funext (view.Psi_top 1)

/-- `view_condSum_zero` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma view_condSum_zero (X : Bool × Bool → ℝ) (ω : Bool × Bool) :
    condSum view.μ view.F 0 X ω = expect view.μ X := rfl

/-- `view_condSum_one` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma view_condSum_one (X : Bool × Bool → ℝ) (ω : Bool × Bool) :
    condSum view.μ view.F 1 X ω = ∑ ω', if ω'.1 = ω.1 then view.μ.mass ω' * X ω' else 0 := by
  unfold condSum
  show ∑ ω' ∈ univ.filter (fun ω' : Bool × Bool => ω'.1 = ω.1), _ = _
  rw [sum_filter]

/-- `view_μ` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma view_μ : view.μ = bern2 (1 / 8) (1 / 8) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ := rfl

/-- `Δ₀ = −19/160` (strict).
Source: counterexamples.py A8 run for two rounds (the agent conditioned on `W₀`); audit r2 (adversarial N2). Kind: L. Fidelity: exact -/
theorem view_drift_zero (ω : Bool × Bool) : view.drift 1 0 ω = -(19 / 160) := by
  unfold AgentView.drift
  rw [view_condSum_zero, view_condSum_zero, Found.CorrThreeStep.expect_add, view_Psi_one, view_Psi_zero,
    view_loss_zero, Found.CorrThreeStep.expect_const, view_μ, expect_bern2, expect_bern2]
  norm_num

/-- `Δ₁ · atomMass = −7/320` on the wrong-round atom and `−7/64` on the right-round atom: the drift
differs across the atoms.
Source: counterexamples.py A8 run for two rounds (the agent conditioned on `W₀`); audit r2 (adversarial N2). Kind: L. Fidelity: exact -/
theorem view_drift_one (ω : Bool × Bool) :
    view.drift 1 1 ω = if ω.1 then -(7 / 320) else -(7 / 64) := by
  unfold AgentView.drift
  rw [view_Psi_two, view_loss_one, view_Psi_one, view_condSum_one, view_condSum_one]
  cases hl : ω.1 <;> simp [Fintype.sum_prod_type, view, bern2] <;> norm_num

/-- The full drift package at horizon `1`. Source: audit r2 (adversarial N2). Kind: L. Fidelity: n/a -/
theorem view_drift_nonpos : ∀ t ≤ 1, ∀ ω, view.drift 1 t ω ≤ 0 := by
  intro t ht ω
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ht with rfl | rfl
  · rw [view_drift_zero]; norm_num
  · rw [view_drift_one]; split_ifs <;> norm_num

/-- `lossesObservable 1` on the updating witness. Source: audit r2 (adversarial N2). Kind: L. Fidelity: n/a -/
theorem view_lossesObservable : view.lossesObservable 1 := by
  intro t ht ω ω' h
  rcases t with _ | _ | _ | t
  · simp
  · simp [view, atoms] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [view_loss_zero]
    simp [h]
  · simp [view, atoms] at h
    subst h
    rfl
  · omega

/-- **The certificate theorems applied on a witness with an atom-dependent `Ψ₁`**: `expect_Reg_le 1`,
`honest_of_drift 1` and `ville_Z 1` all apply, with `E*[Reg₁] = 1/4 ≤ Ψ₀ = 1/2` through the theorem
and `Ψ₁ (true, ·) ≠ Ψ₁ (false, ·)`. So the N+ grade of `ObsToy.certificate`/`honest`/`ville` does not
rest on `toyObs`'s constant agent law.
Source: [[corr-wf14-inventory]] 078 / invariant-final.md Statement 8(b)–(c); counterexamples.py A8 run for two rounds; audit r2 (adversarial N2, probe `AtomPsi`)
Kind: N+ (witness of `expect_Reg_le`, `honest_of_drift`, `ville_Z` with `Ψ₁` varying across the atoms)
Fidelity: exact
Hyps: (a) only -/
theorem witness :
    expect view.μ (view.Reg 1) ≤ 1 / 2 ∧ expect view.μ (view.Reg 1) = 1 / 4 ∧
      (∀ t ≤ 2, ∀ ω, view.honestAt 1 t ω) ∧
      (∀ n ≤ 2, ∀ lam : ℝ, lam * probOf view.μ (hitSet (view.Z 1) lam n) ≤ expect view.μ (view.Psi 1 0)) ∧
      view.Psi 1 1 (true, true) ≠ view.Psi 1 1 (false, true) := by
  have hpsi : ∀ ω, view.Psi 1 0 ω = 1 / 2 := fun ω => by simp [view_Psi_zero]
  refine ⟨view.expect_Reg_le_const 1 view_drift_nonpos (1 / 2) hpsi, ?_,
    view.honest_of_drift 1 view_drift_nonpos,
    fun n hn lam => view.ville_Z 1 view_lossesObservable view_drift_nonpos lam n hn, ?_⟩
  · have e : view.Reg 1 = fun ω => (if ω.1 then 1 else 0) + (if ω.2 then 1 else 0) := by
      funext ω
      unfold ShutdownProc.Reg
      rw [sum_range_succ, sum_range_one, view_loss_zero, view_loss_one]
    rw [e, view_μ, expect_bern2]
    norm_num
  · rw [view_Psi_one]; norm_num

end Updating

end ObsToy

end Cleanroom.Corrigibility.CorrTrajectory
