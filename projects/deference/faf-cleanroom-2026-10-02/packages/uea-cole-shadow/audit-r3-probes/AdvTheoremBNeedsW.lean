import Cleanroom.Uea.UeaColeShadow.Instances

/-!
# `uea-cole-shadow` audit round 3 (adversarial lens): `0 < w_h` in Theorem B is load-bearing, machine-checked

The mandate (target 4, trap (ii)) and the docstrings say that `0 < w_h` in Theorems B and C is load-bearing because
`O_h = (1 - w_h)/w_h` is Lean's junk `0` at `w_h = 0`, "at `w_h = 0` the statement is false". No instance in the
library exhibits a `w_h = 0` trust-bound decision node of a plain fixed point with positive loss, so that claim rested
on prose. This file supplies one from Instance B's own lemmas: at the plain fixed point `(0, 0, swim)` the node `n₁` has
`w_{n₁} = 0` (the self never plays `go`; the residual does), `TB_{n₁}` holds (it holds for every policy), the loss is
`gap(n₁) = 1 - 17/20 = 3/20 > 0`, and Lean's `O_{n₁} = 0`. So `theoremB_odds` with `0 < w_h` dropped is false
(`probe_theoremB_odds_needs_w`). For Theorem C the same junk arises at `w_h = 0` nodes of floored fixed points, but
none of the library's instances has such a node with positive loss (a `T = 3` model with a misleading residual below a
self-null node is needed; hand-derived, not machine-checked here). Not imported by the library.
-/

namespace Cleanroom.Uea.UeaColeShadow.InstB

open Model Finset

/-- The plain fixed point `(0, 0, swim)` of Instance B: action `0` (stay / stay / swim) surely, everywhere. -/
noncomputable def stayPol : Policy (Fin 2) Unit := fun _ _ a => if a = 0 then 1 else 0

theorem stayPol_isPolicy : model.IsPolicy stayPol := by
  intro n h _
  refine ⟨fun a => ?_, ?_⟩
  · unfold stayPol; split_ifs <;> norm_num
  · simp [stayPol]

theorem stayPol_isPlainFP : model.IsPlainFP stayPol :=
  (isPlainFP_iff _).2 ⟨stayPol_isPolicy, by simp [stayPol], by simp [stayPol], by simp [stayPol]⟩

/-- `w_{n₁} = 0` under `(0, 0, swim)`: the self never reaches `n₁`, the residual does. -/
theorem stayPol_wS_n1 : model.wS stayPol 1 n1 = 0 := by
  rw [wS_n1 _ stayPol_isPolicy]
  simp [stayPol]

/-- The loss at `n₁` is `3/20 > 0`: `V^*(n₁) = 1`, `V^π(n₁) = 17/20`. -/
theorem stayPol_gap_n1 : model.gap stayPol 1 n1 = 3 / 20 := by
  unfold Model.gap
  rw [Vstar_n1, model.Vpi_eq nt_n1, Fin.sum_univ_two, Qpi_n1_0]
  simp [stayPol]
  norm_num

/-- Lean's `O_{n₁} = (1 - 0)/0 = 0`. -/
theorem stayPol_odds_n1 : model.odds stayPol 1 n1 = 0 := by
  unfold Model.odds
  rw [stayPol_wS_n1]
  simp

/-- **At `w_h = 0`, Theorem B's package minus `0 < w_h` is inhabited with `gap > O_h`**: `(0,0,swim)` is a plain fixed
point, `n₁` is a decision node, `w_{n₁} = 0`, `TB_{n₁}` holds, and `O_{n₁} = 0 < 3/20 = gap(n₁)`. -/
theorem probe_w_zero_node :
    model.IsPlainFP stayPol ∧ model.nonterminal 1 n1 ∧ model.wS stayPol 1 n1 = 0 ∧ model.TB stayPol 1 n1 ∧
      model.odds stayPol 1 n1 < model.gap stayPol 1 n1 :=
  ⟨stayPol_isPlainFP, nt_n1, stayPol_wS_n1, TB_n1 _ stayPol_isPolicy,
    by rw [stayPol_odds_n1, stayPol_gap_n1]; norm_num⟩

end Cleanroom.Uea.UeaColeShadow.InstB

namespace Cleanroom.Uea.UeaColeShadow

/-- **`theoremB_odds` without `0 < w_h` is false**: it is not the case that every plain fixed point of every model
(already at `Model (Fin 2) Unit Unit`) has `gap ≤ O_h` at every trust-bound decision node. -/
theorem probe_theoremB_odds_needs_w :
    ¬ ∀ (M : Model (Fin 2) Unit Unit) (π : Policy (Fin 2) Unit) (n : ℕ) (h : Hist (Fin 2) Unit n),
      M.IsPlainFP π → M.nonterminal n h → M.TB π n h → M.gap π n h ≤ M.odds π n h := by
  intro H
  obtain ⟨hfp, hnt, _, htb, hlt⟩ := InstB.probe_w_zero_node
  exact absurd (H _ _ _ _ hfp hnt htb) (not_le.2 hlt)

end Cleanroom.Uea.UeaColeShadow

#print axioms Cleanroom.Uea.UeaColeShadow.probe_theoremB_odds_needs_w
