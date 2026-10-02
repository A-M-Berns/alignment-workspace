import Cleanroom.Uea.UeaSinkSwim.TheoremA
import Cleanroom.Uea.UeaColeShadow.Gap

/-!
# The `1 - w_t` martingale: the one-step identity, and monotonicity under a pure policy

(a) **One-step identity**: for a policy `π` and a decision node `h`,
`∑_a ∑_e ξ(hae) (1 - w_{hae}) = ξ(h) (1 - w_h)` — both sides are the residual mass `ξ_{-S}` (`(1 - w) ξ = ξ_{-S}`
where `ξ ≠ 0`, and `0 = 0` where `ξ = 0`), so `(1 - w_t) ξ(h_{<t})` is a non-negative `ξ`-martingale in the
finite tree. This is the identity behind [[audit-revised-theorem-1]] §3.3's Ville correction; the maximal
inequality and the composite "for all time w.h.p." clause are `stretch` (S3), not done here.
(d) Under a pure policy the self-posterior is non-decreasing along the played path
(`wS_le_wA_of_eq_one` of `uea-cole-shadow` with F1): the no-ties clause of the 2025 statement survives in that
form. Witness (N+): the mixed sink-or-swim fixed point, where `w_water = 1/3 < 3/4 = w_island` — a real drop,
so the martingale is not constant.

Scope: finite shadow of rOSI ([[sequential-self-game]] §7). Namespace `Cleanroom.Uea.UeaSinkSwim.Martingale`
(faf-cleanroom run, `uea-sink-swim`, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Finset
open Cleanroom.Uea.UeaColeShadow

namespace Martingale

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] (M : Model A E ι)

/-- `ξ(h)(1 - w_h) = ξ_{-S}(h)` at any history with `ξ_S(h) ≥ 0` (both sides `0` when `ξ(h) = 0`). -/
theorem xi_mul_one_sub_wS {π : Policy A E} {n : ℕ} {h : Hist A E n} (hS : 0 ≤ M.xiS π n h) :
    M.xi π n h * (1 - M.wS π n h) = M.xins n h := by
  by_cases hx : M.xi π n h = 0
  · have h0 : M.xins n h = 0 := by
      have := M.xins_nonneg n h
      have h1 : (0:ℝ) ≤ (1 - M.δ) * M.xiS π n h := mul_nonneg (by linarith [M.δ_lt_one]) hS
      unfold Model.xi at hx
      linarith
    rw [hx, h0, zero_mul]
  · rw [Model.wS_of_xi_ne_zero M hx]
    field_simp
    unfold Model.xi
    ring

/-- **(a) The one-step martingale identity**: `∑_a ∑_e ξ(hae)(1 - w_{hae}) = ξ(h)(1 - w_h)` at every decision node.
Source: [[audit-revised-theorem-1]] §3.3 (the Ville correction); [[uea-inventory]] 015
Kind: P
Fidelity: exact (the finite-tree identity; the measure-theoretic martingale statement is not formalized)
Hyps: (a) -/
theorem one_step {π : Policy A E} (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    ∑ a, ∑ e, M.xi π (n + 1) (ext h a e) * (1 - M.wS π (n + 1) (ext h a e)) =
      M.xi π n h * (1 - M.wS π n h) := by
  rw [xi_mul_one_sub_wS M (M.xiS_nonneg hπ n h hnt), ← M.xinsA_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [← M.xins_ext_sum]
  refine sum_congr rfl fun e _ => ?_
  exact xi_mul_one_sub_wS M (M.xiS_ext_nonneg hπ hnt a e)

/-- **(d) Monotone along a pure path**: under a pure policy the self-posterior does not decrease along the played
action with a positive percept: `w_h ≤ w_{hae}` when `π(a|h) = 1` and `ξ(e|ha) ≠ 0`.
Source: [[audit-revised-theorem-1]] §1 (F1, F2); [[lesswrong-post--live-2026-08-22]] line 236 (the no-ties clause)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem wS_le_wS_ext_of_eq_one [Nonempty A] {π : Policy A E} (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n}
    (hnt : M.nonterminal n h) {a : A} (ha : π n h a = 1) {e : E}
    (he : M.xie n h a e ≠ 0) : M.wS π n h ≤ M.wS π (n + 1) (ext h a e) := by
  rw [M.wS_ext_of_xie_ne_zero h a he]
  exact M.wS_le_wA_of_eq_one hπ hnt ha

end Martingale

/-! ### Witness: the mixed sink-or-swim point, where the self-posterior drops -/

namespace Martingale

open Cleanroom.Uea.UeaColeShadow.SinkOrSwim TheoremA

/-- **Witness (N+)**: at the mixed fixed point `j* = 1/6` of `b = 1, c = 1/2, δ = 1/4, s = 3/4`,
`w_island = 3/4` and `w_water = 1/3` — a real drop, so `1 - w` is a non-constant martingale.
Source: mandate target 5 (witness)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem witness :
    (sos witParams).IsPlainFP (mixedPol (1 / 6)) ∧ (sos witParams).wS (mixedPol (1 / 6)) 0 island = 3 / 4 ∧
      (sos witParams).wS (mixedPol (1 / 6)) 1 water = 1 / 3 := by
  obtain ⟨_, _, _, hmix, _⟩ := TheoremA.witness
  refine ⟨hmix, ?_, ?_⟩
  · rw [wS_island]; unfold witParams; norm_num
  · have hx : (sos witParams).xi (mixedPol (1 / 6)) 1 water = 3 / 8 := by
      rw [xi_water]; unfold witParams; simp [mixedPol]; norm_num
    rw [Model.wS_of_xi_ne_zero _ (by rw [hx]; norm_num), hx, xiS_water]
    unfold witParams; simp [mixedPol]; norm_num

end Martingale

end Cleanroom.Uea.UeaSinkSwim
