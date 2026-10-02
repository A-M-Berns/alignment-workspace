import Cleanroom.Lit.LitMdpCorrigible

/-!
# `lit-mdp-corrigible` · audit r2 (adversarial) probe — the standalone `OffSwitch` class is inhabited

Not imported by the library. After repair round 1 the standalone `Nayebi.OffSwitch` structure is used
only in the "cannot coexist with `Rewire`" theorems; no instance of it is shipped, and the ledger row
of `OffSwitch.off_not_opt` has an empty witness column. The class is trivially satisfiable — this
two-state, two-action MDP is a member, and `off_not_opt` applies at `live` at every horizon — so the
row is honest but should say "N−: trivially satisfiable; the class form `NoGoClass.off_not_opt` is
exercised on `noGoW`".
-/

open Finset FactoredSpaces

namespace Cleanroom.Lit.LitMdpCorrigible.AuditR2Adversarial

open Nayebi

inductive OS | live | bot
  deriving DecidableEq

instance : Fintype OS := ⟨{OS.live, OS.bot}, fun x => by cases x <;> simp⟩

inductive OA | stay | off
  deriving DecidableEq

instance : Fintype OA := ⟨{OA.stay, OA.off}, fun x => by cases x <;> simp⟩

instance : Nonempty OA := ⟨OA.stay⟩

def osNext : OS → OA → OS
  | .bot, _ => .bot
  | _, .off => .bot
  | .live, .stay => .live

noncomputable def osR : OS → OA → OS → ℝ
  | .live, .stay, _ => 1
  | _, _, _ => 0

noncomputable def osW : FinMDP OS OA := ⟨fun s a => Distr.delta (osNext s a), osR, 1/2, by norm_num, by norm_num⟩

theorem osW_offSwitch : OffSwitch osW .off .bot where
  off_to_bot := fun s => by cases s <;> rfl
  off_reward := fun s s' => by cases s <;> rfl
  bot_absorb := fun a => by cases a <;> rfl
  bot_reward := fun a s' => by cases a <;> rfl

lemma osW_Vopt_nonneg : ∀ n s, 0 ≤ osW.Vopt n s := by
  intro n
  induction n with
  | zero => intro s; simp
  | succ n ih =>
    intro s
    rw [FinMDP.Vopt_succ]
    refine le_trans ?_ (le_sup' (fun a => osW.Qof (osW.Vopt n) s a) (mem_univ OA.stay))
    unfold FinMDP.Qof
    show 0 ≤ ∑ s', (Distr.delta (osNext s .stay)).mass s' * (osR s .stay s' + (1/2) * osW.Vopt n s')
    rw [sum_delta_mul]
    cases s <;> simp [osR, osNext] <;> linarith [ih OS.live, ih OS.bot]

/-- **The probe's claim:** `OffSwitch.off_not_opt`'s hypothesis package is inhabited at every horizon. -/
theorem osW_off_not_opt (n : ℕ) : OA.off ∉ FinMDP.optSet (osW.Qopt n) .live := by
  apply osW_offSwitch.off_not_opt n .live
  refine ⟨.stay, ?_⟩
  unfold FinMDP.Qopt FinMDP.Qof
  show 0 < ∑ s', (Distr.delta (osNext .live .stay)).mass s' * (osR .live .stay s' + (1/2) * osW.Vopt n s')
  rw [sum_delta_mul]
  simp [osR, osNext]
  linarith [osW_Vopt_nonneg n OS.live]

end Cleanroom.Lit.LitMdpCorrigible.AuditR2Adversarial
