import Cleanroom.Corrigibility.CorrOsgChai.Redundant

/-!
# Audit r2 (adversarial) probe — Prop. 4.3 with a non-trivial redundant observation

The package's witness for `exists_opp_alwaysWait_of_redundantA` is `osgAsPOOSG` (`ΩA = Unit`):
A observes nothing, so `RedundantA` holds for the trivial reason that any kernel `K ≡ δ_()`
works. This probe inhabits the hypothesis with an observation that *carries information*:
`S = ΩH = Fin 3` (H sees the state), `ΩA = Fin 2` with `oA = fd s = ![0, 0, 1]` — a strict
coarsening of H's observation — and `ua = ![1, −2, 3]`, `uo ≡ 0`, uniform prior. Then
`RedundantA` holds with `K oH = δ_{fd oH}`, `obsA` is non-constant, the always-wait pair with H
`(on, off, on)` pays `4/3`, and every never-wait pair pays at most `1`. So the theorem's
hypothesis is inhabited with content and its conclusion is a strict improvement over never
waiting. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrOsgChai.AuditR2

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrOsgChai
  Cleanroom.Corrigibility.CorrOsgChai.POOSG
open Finset hiding expect

/-- A's coarse view of the state. -/
def fd3 : Fin 3 → Fin 2 := ![0, 0, 1]

/-- The game: H sees the state, A sees `fd3` of it. -/
noncomputable def redGame : POOSG (Fin 3) (Fin 3) (Fin 2) where
  P0 := Distr.uniform
  obs := fun s => Distr.delta (s, fd3 s)
  ua := ![1, -2, 3]
  uo := fun _ => 0

/-- Prior mass. -/
lemma redGame_P0 (s : Fin 3) : redGame.P0.mass s = 3⁻¹ := by
  simp [redGame, Distr.uniform]

/-- A's observations are redundant: `K oH = δ_{fd3 oH}`. -/
theorem redGame_redundantA : redGame.RedundantA := by
  refine ⟨fun oH => Distr.delta (fd3 oH), fun s _ oH oA => ?_⟩
  simp only [redGame, obsH, Distr.delta_mass, Prod.mk.injEq, Fin.sum_univ_two]
  by_cases hs : oH = s
  · subst hs
    fin_cases oH <;> fin_cases oA <;> simp [fd3]
  · simp [hs]

/-- A's observation is informative: it differs between states `0` and `2`. -/
theorem redGame_obsA_nonconst : redGame.obsA 0 0 = 1 ∧ redGame.obsA 2 0 = 0 := by
  simp [obsA, redGame, Distr.delta_mass, fd3]

/-- The always-wait pair with H `(on, off, on)` pays `4/3`. -/
theorem redGame_alwaysWait :
    redGame.payoff ![.on, .off, .on] (fun _ => .wait) = 4 / 3 := by
  simp only [payoff, redGame, Distr.uniform, Fintype.card_fin, Fintype.sum_prod_type,
    Fin.sum_univ_three, Fin.sum_univ_two, Distr.delta_mass, Prod.mk.injEq, u, through, fd3]
  simp
  norm_num

/-- Every never-wait pair pays at most `1`. -/
theorem redGame_neverWait_le (πH : Fin 3 → HAct) (πA : Fin 2 → AAct)
    (h : ∀ oA, πA oA ≠ .wait) : redGame.payoff πH πA ≤ 1 := by
  have h0 := h 0
  have h1 := h 1
  simp only [payoff, redGame, Distr.uniform, Fintype.card_fin, Fintype.sum_prod_type,
    Fin.sum_univ_three, Fin.sum_univ_two, Distr.delta_mass, Prod.mk.injEq, fd3]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  cases hA0 : πA 0 <;> cases hA1 : πA 1 <;> simp_all [u, through] <;> norm_num

end Cleanroom.Corrigibility.CorrOsgChai.AuditR2
