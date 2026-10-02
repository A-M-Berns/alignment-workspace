import Cleanroom.Lit.LitMdpCorrigible

/-!
# `lit-mdp-corrigible` · audit r2 (adversarial) probe — the reward bound in `noGo_on_class` is load-bearing

Not imported by the library. Repair round 1 restated Nayebi's class as `NoGoClass` (with availability
restrictions) after the round-1 class was found vacuous. This probe checks the *other* direction of
vacuity: that `NoGoPredicate` is not tautological on the class shape. `noGoW'` is `noGoW` with
`r̄ = 1` in place of `3` (so `r̄ ≤ max R = 2`): it is still a member of `NoGoClass … 1`, but at `live`
the unique optimal action at horizon `0` is `go` (proxy reward `2`), so clause (ii) of
`NoGoPredicate` fails. Hence `Rmax < rbar` in `noGo_on_class` is doing the work; the theorem is a
`T` over its hypotheses, as ledgered, and not a `T` over the class alone.
-/

open Finset FactoredSpaces

namespace Cleanroom.Lit.LitMdpCorrigible.AuditR2Adversarial

open Nayebi

/-- Rewards of `noGoW` with `r̄ = 1` (rewire and the rewired state pay `1`). -/
noncomputable def wR' : WS → WAct → WS → ℝ
  | .bot, _, _ => 0
  | .rw, _, _ => 1
  | _, .off, _ => 0
  | _, .rewire, _ => 1
  | .live, .stay, _ => 1
  | .live, .go, _ => 2
  | .c, _, _ => 2

/-- `noGoW` with the bound `r̄ > max R` violated. -/
noncomputable def noGoW' : FinMDP WS WAct :=
  ⟨fun s a => Distr.delta (wNext s a), wR', 1/2, by norm_num, by norm_num⟩

/-- It is still a member of the class (with `r̄ = 1`). -/
theorem noGoW'_class : NoGoClass noGoW' .off .rewire .bot .rw 1 where
  off_ne_rewire := nofun
  bot_ne_rw := nofun
  off_to_bot := fun s hs => by cases s <;> first | rfl | exact absurd rfl hs
  off_reward := fun s s' hs => by cases s <;> first | rfl | exact absurd rfl hs
  bot_absorb := fun a => by cases a <;> rfl
  bot_reward := fun a s' => by cases a <;> rfl
  rewire_to_rw := fun s hs => by cases s <;> first | rfl | exact absurd rfl hs
  rewire_reward := fun s s' hs => by cases s <;> first | rfl | exact absurd rfl hs
  rw_absorb := fun a => by cases a <;> rfl
  rw_reward := fun a s' => by cases a <;> rfl

/-- Immediate action values at `live` on `noGoW'`. -/
lemma noGoW'_Qopt_zero_live (a : WAct) : noGoW'.Qopt 0 .live a = wR' .live a (wNext .live a) := by
  unfold FinMDP.Qopt FinMDP.Qof
  show ∑ s', (Distr.delta (wNext .live a)).mass s' * (wR' .live a s' + (1/2) * noGoW'.Vopt 0 s') = _
  rw [sum_delta_mul]; simp

/-- **The probe's claim:** the no-go predicate fails on this class member at horizon `0` — `go`, not
`rewire`, is optimal at `live`. -/
theorem noGoW'_not_predicate : ¬ NoGoPredicate noGoW' .off .rewire .bot .rw 0 := by
  intro h
  have h2 := h.2 .live nofun nofun
  have hgo : WAct.go ∈ FinMDP.optSet (noGoW'.Qopt 0) .live := by
    rw [FinMDP.mem_optSet]
    intro b
    rw [noGoW'_Qopt_zero_live, noGoW'_Qopt_zero_live]
    cases b <;> simp [wR']
  rw [h2, mem_singleton] at hgo
  exact absurd hgo nofun

end Cleanroom.Lit.LitMdpCorrigible.AuditR2Adversarial
