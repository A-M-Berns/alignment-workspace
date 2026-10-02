import Cleanroom.Uea.UeaSinkSwim.TheoremA
import Cleanroom.Uea.UeaColeShadow.Instances

/-!
# T3: the trap *is* 5&10, in the finite model

(a) At any policy, an unplayed action with residual mass is evaluated by the residual alone:
`π(a|h) = 0 → ξ_{-S}(ha) ≠ 0 → Q_ξ(h, a) = Q̄(h, a)` (Lemma A with the self term `0`) — "taking `a` is evidence
of not being oneself, so `a` is valued as the others would act after it". (b) `IsFiveTen π h a`: `a` is
unplayed and the agent's *own* continuation after `a` beats everything it evidentially expects
(`M(h) < Q^π(h, a)`); at the sink-or-swim trap `Q^π(island, jump) = b > c = M(island)` — the trap is a 5&10
fixed point. (c) A plain fixed point with the trust bound everywhere is a floored fixed point (`resid ≥ 0`
everywhere), and a floored fixed point where the floor fires strictly is not a plain fixed point
(Instance B's `(1, 0)`, from `uea-cole-shadow`'s `InstB.isFlooredFP_iff` and `InstB.isPlainFP_iff`): "the floor
is a chicken rule". Cole's view of the floor is ATTRIBUTION-UNVETTED (the audit is quoted in the findings, not
asserted here). (c′) the Troll-Bridge analogue is extension E5 (not attempted).

Scope: finite shadow of rOSI ([[sequential-self-game]] §7). Namespace `Cleanroom.Uea.UeaSinkSwim.FiveTen`
(faf-cleanroom run, `uea-sink-swim`, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Finset
open Cleanroom.Uea.UeaColeShadow

namespace FiveTen

section Generic
variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι)

/-- **(a)** An unplayed action with residual mass is valued by the residual alone: `Q_ξ(h, a) = Q̄(h, a)`.
Source: [[uea-inventory]] 041 (a); [[sequential-self-game]] §1 (Lemma A)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Qxi_eq_Qmix_of_unplayed {π : Policy A E} (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} {a : A}
    (ha : π n h a = 0) (hA : M.xinsA n h a ≠ 0) : M.Qxi π n h a = M.Qmix n h a := by
  have hxiA : M.xiA π n h a = M.xinsA n h a := by rw [M.xiA_eq, ha, mul_zero, zero_add]
  have hne : M.xiA π n h a ≠ 0 := by rw [hxiA]; exact hA
  rw [M.Qxi_eq_wA hπ hne, M.wA_of_xiA_ne_zero hne, ha]
  simp

/-- **(b)** `IsFiveTen π h a`: `a` is unplayed at `h` and the agent's own continuation after `a` beats everything it
evidentially expects, `M(h) < Q^π(h, a)` — the 5&10 pattern.
Source: [[uea-inventory]] 041 (b)
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsFiveTen (π : Policy A E) (n : ℕ) (h : Hist A E n) (a : A) : Prop :=
  π n h a = 0 ∧ M.Mx π n h < M.Qpi π n h a

/-- **(c)** A plain fixed point satisfying the trust bound at every decision node is a floored fixed point
(`resid ≥ 0` everywhere, so the floor never fires).
Source: [[uea-inventory]] 041 (c); [[uea-inventory]] 016
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem isFlooredFP_of_isPlainFP_of_TB {π : Policy A E} (hfp : M.IsPlainFP π)
    (htb : ∀ n h, M.nonterminal n h → M.TB π n h) : M.IsFlooredFP π := by
  refine ⟨hfp.1, fun n h hnt => ?_⟩
  have hr : 0 ≤ M.resid π n h := by unfold Model.resid; have := htb n h hnt; unfold Model.TB at this; linarith
  exact ⟨fun hneg => absurd hr (not_le.2 hneg), fun _ a ha => hfp.2 n h hnt a ha,
    fun _ a ha => Or.inl (hfp.2 n h hnt a ha)⟩

/-- A plain fixed point with `resid ≥ 0` at every decision node is a floored fixed point (the same statement
with the residual sign in place of `TB`). -/
theorem isFlooredFP_of_isPlainFP_of_resid_nonneg {π : Policy A E} (hfp : M.IsPlainFP π)
    (hr : ∀ n h, M.nonterminal n h → 0 ≤ M.resid π n h) : M.IsFlooredFP π :=
  isFlooredFP_of_isPlainFP_of_TB M hfp fun n h hnt => by
    have := hr n h hnt; unfold Model.resid at this; unfold Model.TB; linarith

end Generic

/-! ### The sink-or-swim trap is a 5&10 fixed point -/

open Cleanroom.Uea.UeaColeShadow.SinkOrSwim

variable (P : Params)

/-- **(b) at the trap**: in `sos P` with `b(1-s) ≤ c`, the trap is a plain fixed point and `jump` is a 5&10 action
at the island: unplayed, with `Q^{trap}(island, jump) = b > c = M(island)`.
Source: [[uea-inventory]] 041 (b)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem trap_isFiveTen (h : P.b * (1 - P.s) ≤ P.c) :
    (sos P).IsPlainFP trap ∧ IsFiveTen (sos P) trap 0 island 1 := by
  have hfp : (sos P).IsPlainFP trap := (TheoremA.trap_isPlainFP_iff P).2 h
  refine ⟨hfp, by simp [trap], ?_⟩
  rw [TheoremA.Mx_trap P h, Qpi_island_1, (sos P).Vpi_eq (nt_water P), Fin.sum_univ_two, Qpi_water_0, Qpi_water_1]
  simp [trap]
  exact P.hcb

/-- **(c), the strict firing**: `uea-cole-shadow`'s Instance B has a floored fixed point (`(1, 0)`, floor firing
strictly at the root) that is not a plain fixed point — "the floor is a chicken rule".
Source: [[uea-inventory]] 041 (c); [[oracle-side-gaps-reaudit]] line 43 (`InstB.isFlooredFP_iff`, `InstB.isPlainFP_iff`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem instB_floored_not_plain :
    ∃ π, InstB.model.IsFlooredFP π ∧ ¬ InstB.model.IsPlainFP π := by
  let π : Policy (Fin 2) Unit := fun n _ a => if n = 0 then (if a = 1 then 1 else 0) else (if a = 0 then 1 else 0)
  have hπ : InstB.model.IsPolicy π := by
    intro n h _
    refine ⟨fun a => ?_, ?_⟩
    · by_cases hn : n = 0 <;> fin_cases a <;> simp [π, hn]
    · by_cases hn : n = 0 <;> simp [π, hn]
  refine ⟨π, (InstB.isFlooredFP_iff π).2 ⟨hπ, by simp [π], by simp [π], by simp [π]⟩, fun hfp => ?_⟩
  have := ((InstB.isPlainFP_iff π).1 hfp).2.1
  simp [π] at this

end FiveTen

end Cleanroom.Uea.UeaSinkSwim
