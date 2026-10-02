import Cleanroom.Uea.UeaColeShadow.TheoremB
import Cleanroom.Uea.UeaColeShadow.InstanceW

/-!
# The `δ = 0` corner as the residual-null subtree

A plain fixed point is optimal on every residual-null subtree, with **no trust-bound hypothesis**: at a
residual-null decision node `Q_ξ = Q^π`, the fixed point is greedy for its own `Q^π`, and by depth induction
on the null subtree (`xins_ext_eq_zero`) a self-greedy policy is optimal for the kernel `ξ(e|·)`.
`uea-cole-shadow`'s `gap_le_zero_of_xins_eq_zero` assumed `TB`; here it is derived. Fidelity `variant`: the
model has `δ_pos`, so "`δ = 0`" is the subtree form (the post's footnote at line 318 and §4.1 Step 0).
Witness: `InstW.model`'s node `N`, which the residual never reaches, under its plain fixed point `polW`.

Scope: finite shadow of rOSI ([[sequential-self-game]] §7). Namespace `Cleanroom.Uea.UeaSinkSwim.Corner`
(faf-cleanroom run, `uea-sink-swim`, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Finset
open Cleanroom.Uea.UeaColeShadow

namespace Corner

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι)

/-- **The `δ = 0` corner**: a plain fixed point has `V^π = V^*` at every residual-null decision node — no `TB`
hypothesis (depth induction on the null subtree; `Q_ξ = Q^π = Q^*` there and the fixed point is greedy).
Source: [[uea-inventory]] 017; [[sequential-self-game]] §4.1 (Step 0); [[lesswrong-post--live-2026-08-22]] footnote (line 318)
Kind: L
Fidelity: variant: the residual-null-subtree form of "`δ = 0`" (the model has `δ_pos`); no `TB` hypothesis, unlike
`gap_le_zero_of_xins_eq_zero`
Hyps: (a) -/
theorem Vpi_eq_Vstar_of_xins_eq_zero_plain {π : Policy A E} (hfp : M.IsPlainFP π) :
    ∀ n h, M.nonterminal n h → M.xins n h = 0 → M.Vpi π n h = M.Vstar n h := by
  have hπ := hfp.1
  refine M.depth_induction (fun n h => M.nonterminal n h → M.xins n h = 0 → M.Vpi π n h = M.Vstar n h) ?_ ?_
  · intro n h hnt hnt' _
    exact absurd hnt' hnt
  · intro n h hnt ih _ hx
    have hchild : ∀ a e, M.Vpi π (n + 1) (ext h a e) = M.Vstar (n + 1) (ext h a e) := by
      intro a e
      by_cases hc : M.nonterminal (n + 1) (ext h a e)
      · exact ih a e hc (M.xins_ext_eq_zero hx a e)
      · rw [M.Vpi_of_not_nonterminal hc, M.Vstar_of_not_nonterminal hc]
    have hQ : ∀ a, M.Qpi π n h a = M.Qstar n h a := by
      intro a
      rw [M.Qpi_eq_sum, M.Qstar_eq_sum]
      exact sum_congr rfl fun e _ => by rw [hchild a e]
    have hQxi : ∀ a, M.Qxi π n h a = M.Qstar n h a := fun a => by
      rw [M.Qxi_eq_Qpi_of_xins_eq_zero hx a, hQ a]
    have hM : M.Mx π n h = M.Vstar n h := by
      rw [M.Vstar_eq hnt]
      unfold Model.Mx
      exact congrArg _ (funext hQxi)
    have hsupp : ∀ a ∈ supp π n h, M.Qpi π n h a = M.Vstar n h := by
      intro a ha
      rw [Model.mem_supp] at ha
      rw [hQ a, ← hQxi a, hfp.2 n h hnt a ha, hM]
    rw [M.Vpi_eq_sum_supp hπ hnt, sum_congr rfl fun a ha => by rw [hsupp a ha], ← sum_mul,
      M.sum_supp_eq_one hπ hnt, one_mul]

/-- The loss of a plain fixed point is `0` at every residual-null decision node (no `TB`). -/
theorem gap_eq_zero_of_xins_eq_zero_plain {π : Policy A E} (hfp : M.IsPlainFP π) {n : ℕ} {h : Hist A E n}
    (hnt : M.nonterminal n h) (hx : M.xins n h = 0) : M.gap π n h = 0 := by
  unfold Model.gap
  rw [Vpi_eq_Vstar_of_xins_eq_zero_plain M hfp n h hnt hx, sub_self]

end Corner

namespace Corner

/-- **Witness (N+)**: `uea-cole-shadow`'s Instance W — its node `N` is a decision node the residual never reaches
(`ξ_{-S}(N) = 0`) and `polW` is a plain fixed point, so `V^{polW}(N) = V^*(N) = 1` by the corner lemma (the
witness exercises a genuine subtree, not a terminal node).
Source: [[uea-inventory]] 017; `uea-cole-shadow` `InstanceW.lean`
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem instW_witness :
    InstW.model.xins 1 InstW.N = 0 ∧ InstW.model.IsPlainFP InstW.polW ∧
      InstW.model.Vpi InstW.polW 1 InstW.N = InstW.model.Vstar 1 InstW.N ∧ InstW.model.Vstar 1 InstW.N = 1 :=
  ⟨InstW.xins_N, InstW.isPlainFP,
    Vpi_eq_Vstar_of_xins_eq_zero_plain InstW.model InstW.isPlainFP 1 InstW.N InstW.nt_N InstW.xins_N, InstW.Vstar_N⟩

end Corner

end Cleanroom.Uea.UeaSinkSwim
