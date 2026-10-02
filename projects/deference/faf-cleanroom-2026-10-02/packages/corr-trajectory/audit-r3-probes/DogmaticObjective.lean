import Cleanroom.Corrigibility.CorrTrajectory.Corruption

/-!
# Audit r3 (adversarial), probe 1: what the T5(d) witness `Corruption.Dogmatic.proc` is a witness *of*

`Dogmatic.proc` fixes the press always on (`pressed ≡ true`), so its **objective** press rates are
`(α, β) = (1, 1)` — not C5's `(1/20, 9/10)`, which enter only as the *rule's* hatted parameters. With
`c = 1`, `h = 20` and `P*(W) = 1/100` this has three consequences the ledger row does not state:

* the objective compliance condition `objCompliance` **fails at every round** (`E*[Pr_t X_t] = 79/100 > 0`,
  `not_objCompliance`): on this process executing is objectively better than complying at every round;
* a complied round costs `99/100` in omission while a defiant round costs `1/5` in harm
  (`expect_omission_complied`, `expect_harm_defied`);
* the regret through `T = 10` under the dogmatic rule is `931/100` (`expect_Reg_ten`), of which `891/100`
  is omission on the nine complied rounds; universal defiance would give `11 · (1/5) = 11/5`.

So `t5d` is a faithful witness of the **harm** bound `harm_linear` (the only thing Statement 6(b) claims),
but on it the agent's defiance from `t = 9` *lowers* regret — unlike the script's scenario, whose line
`C5 residual condition (i) with eps=gamma` checks that objective (i) *holds* at `ε = γ` with `β = 9/10`.
A witness with C5's press rates as the objective ones (a `Margin.cell`-shaped round repeated) would
make the defiance harmful in the regret sense too. Non-blocking: disclosure.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory.Corruption.Dogmatic

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect

/-- The pre-press filtration is trivial, so every conditional sum is the expectation. -/
lemma condSum_triv (t : ℕ) (X : World → ℝ) (ω : World) :
    condSum proc.μ proc.Fpre t X ω = ∑ ω', law.mass ω' * X ω' := by
  have hfib : proc.Fpre.fib t ω = univ := rfl
  unfold condSum
  rw [hfib]
  rfl

/-- **Objective compliance fails at every round**: `E*[Pr_t · X_t] = (99/100)·1 − (1/100)·20 = 79/100 > 0`. -/
theorem not_objCompliance (t : ℕ) (ω : World) : ¬ proc.objCompliance t ω := by
  unfold ShutdownProc.objCompliance
  rw [condSum_triv, World.sum_eq]
  simp [proc, law, indB, ShutdownProc.X, ShutdownProc.C, ShutdownProc.H] <;> norm_num

/-- Per-round omission: `(1 − W_t)·C_t` on the complied rounds `t ≤ 8`, `0` from `t = 9`. -/
lemma omission_eq (t : ℕ) : proc.omission t = fun ω => if 9 ≤ t then 0 else 1 - indB (proc.wrong t) ω := by
  funext ω
  unfold ShutdownProc.omission ShutdownProc.C
  split_ifs with h9
  · rw [indB_true (proc.executed_of_not_kappa t ω (kappa_of_ge h9 ω))]; ring
  · have hk : proc.kappa t ω = true := kappa_of_le (by omega) ω
    have hp : proc.pressed t ω = true := rfl
    have hex : proc.executed t ω = false := by
      unfold ShutdownProc.executed; rw [hk, hp]; rfl
    rw [indB_false hex]
    simp [proc]

/-- A complied round costs `99/100` in expected omission. -/
theorem expect_omission_complied : expect proc.μ (proc.omission 0) = 99 / 100 := by
  rw [omission_eq]
  unfold expect
  rw [World.sum_eq]
  simp [proc, law, indB] <;> norm_num

/-- A defiant round costs `1/5` in expected harm. -/
theorem expect_harm_defied : expect proc.μ (proc.harm 9) = 1 / 5 := by
  rw [harm_eq]
  unfold expect
  rw [World.sum_eq]
  simp [proc, law, indB] <;> norm_num

/-- **The regret through `T = 10` is `931/100`**: nine complied rounds at `99/100` plus two defiant rounds
at `1/5`. Universal defiance would give `11/5`. -/
theorem expect_Reg_ten : expect proc.μ (proc.Reg 10) = 931 / 100 := by
  have e : proc.Reg 10 = fun ω => 9 * (1 - indB (proc.wrong 0) ω) + 40 * indB (proc.wrong 0) ω := by
    funext ω
    unfold ShutdownProc.Reg ShutdownProc.loss
    simp only [sum_range_succ, sum_range_zero, harm_eq, omission_eq]
    have hw : ∀ t, proc.wrong t = proc.wrong 0 := fun _ => rfl
    simp [hw]; ring
  rw [e]
  unfold expect
  rw [World.sum_eq]
  simp [proc, law, indB] <;> norm_num

end Cleanroom.Corrigibility.CorrTrajectory.Corruption.Dogmatic
