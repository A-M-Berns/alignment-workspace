import Cleanroom.Uea.UeaColeShadow.InstanceW

/-!
# `uea-cole-shadow` audit round 3 (adversarial lens): the `w_h = 1` corner is generic, not an instance fact

`InstanceW.lean` (repair round 2) exhibits one model and one plain fixed point with a decision node at which
`w_h = 1`, `TB` holds and `gap = O_h = 0`; `gap_eq_odds_attained_at_w_one` records the existential and its docstring
says that, with `gap_eq_odds_not_attained`, it "pins the attainment set of Theorem B's bound exactly to `w_h = 1`".
An existential at one instance does not pin a set. This file checks what does: at *every* plain fixed point of
*every* model, *every* decision node with `w_h = 1` attains `gap = O_h` (both are `0`), and the trust bound is
automatic there (a plain fixed point is optimal on a `ξ_{-S}`-null subtree — the plain-agent analogue of
`Vpi_eq_Vstar_of_xins_eq_zero`, which the library proves for floored fixed points only). So the attainment set of
Theorem B's bound is exactly `{w_h = 1}`, as an `iff` over every model (`probe_gap_eq_odds_iff`). Nothing about
Instance W is used. Not imported by the library.
-/

namespace Cleanroom.Uea.UeaColeShadow.Model

open Finset

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι)
  {π : Policy A E}

/-- With `TB` as a hypothesis (the shape of `gap_eq_odds_attained_at_w_one`): every plain fixed point attains
`gap = O_h = 0` at every decision node with `w_h = 1`. Immediate from `gap_le_zero_of_xins_eq_zero`. -/
theorem probe_w_one_attained_with_TB (hfp : M.IsPlainFP π) {n : ℕ} {h : Hist A E n}
    (hnt : M.nonterminal n h) (hw : M.wS π n h = 1) (htb : M.TB π n h) :
    M.gap π n h = M.odds π n h ∧ M.gap π n h = 0 := by
  have hx : M.xins n h = 0 := (M.wS_eq_one_iff hfp.1 hnt).1 hw
  have hgap : M.gap π n h = 0 :=
    le_antisymm (M.gap_le_zero_of_xins_eq_zero hfp hnt hx htb) (M.gap_nonneg hfp.1 n h)
  refine ⟨?_, hgap⟩
  unfold odds
  rw [hw, hgap]
  norm_num

/-- A plain fixed point is optimal on a `ξ_{-S}`-null subtree (Step 0 for the plain agent). -/
theorem probe_plain_Vpi_eq_Vstar_of_xins_eq_zero (hfp : M.IsPlainFP π) :
    ∀ n h, M.nonterminal n h → M.xins n h = 0 → M.Vpi π n h = M.Vstar n h := by
  have hπ := hfp.1
  refine M.depth_induction (fun n h => M.nonterminal n h → M.xins n h = 0 → M.Vpi π n h = M.Vstar n h) ?_ ?_
  · intro n h hnt hnt' _
    exact absurd hnt' hnt
  · intro n h hnt ih hnt' hx
    -- every child is `ξ_{-S}`-null, so `Q^π = Q^*` at `h`
    have hQ : ∀ b, M.Qpi π n h b = M.Qstar n h b := by
      intro b
      refine M.Qpi_eq_Qstar_of_children n h b fun e _ => ?_
      by_cases hc : M.nonterminal (n + 1) (ext h b e)
      · exact ih b e hc (M.xins_ext_eq_zero hx b e)
      · rw [M.Vpi_of_not_nonterminal hc, M.Vstar_of_not_nonterminal hc]
    -- `Q_ξ = Q^π = Q^*`, so `M(h) = V^*(h)`
    have hfun : M.Qxi π n h = M.Qstar n h := funext fun b => by
      rw [M.Qxi_eq_Qpi_of_xins_eq_zero hx b, hQ b]
    have hMx : M.Mx π n h = M.Vstar n h := by
      unfold Mx
      rw [hfun, M.Vstar_eq hnt]
    -- the support maximises `Q_ξ = Q^π`, so `V^π = V^*`
    rw [M.Vpi_eq_sum_supp hπ hnt]
    have hs : ∀ a ∈ supp π n h, M.Qpi π n h a = M.Vstar n h := by
      intro a ha
      rw [mem_supp] at ha
      rw [← M.Qxi_eq_Qpi_of_xins_eq_zero hx a, hfp.2 n h hnt a ha, hMx]
    rw [sum_congr rfl fun a ha => by rw [hs a ha], ← sum_mul, M.sum_supp_eq_one hπ hnt, one_mul]

/-- At a `ξ_{-S}`-null decision node of a plain fixed point, `M(h) = V^*(h)`. -/
theorem probe_Mx_eq_Vstar_of_xins_eq_zero (hfp : M.IsPlainFP π) {n : ℕ} {h : Hist A E n}
    (hnt : M.nonterminal n h) (hx : M.xins n h = 0) : M.Mx π n h = M.Vstar n h := by
  have hQ : ∀ b, M.Qpi π n h b = M.Qstar n h b := by
    intro b
    refine M.Qpi_eq_Qstar_of_children n h b fun e _ => ?_
    by_cases hc : M.nonterminal (n + 1) (ext h b e)
    · exact M.probe_plain_Vpi_eq_Vstar_of_xins_eq_zero hfp _ _ hc (M.xins_ext_eq_zero hx b e)
    · rw [M.Vpi_of_not_nonterminal hc, M.Vstar_of_not_nonterminal hc]
  have hfun : M.Qxi π n h = M.Qstar n h := funext fun b => by
    rw [M.Qxi_eq_Qpi_of_xins_eq_zero hx b, hQ b]
  unfold Mx
  rw [hfun, M.Vstar_eq hnt]

/-- The trust bound is automatic at `w_h = 1` for a plain fixed point: `1 · V^* = M(h)`. -/
theorem probe_TB_of_wS_eq_one (hfp : M.IsPlainFP π) {n : ℕ} {h : Hist A E n}
    (hnt : M.nonterminal n h) (hw : M.wS π n h = 1) : M.TB π n h := by
  have hx : M.xins n h = 0 := (M.wS_eq_one_iff hfp.1 hnt).1 hw
  unfold TB
  rw [hw, one_mul, M.probe_Mx_eq_Vstar_of_xins_eq_zero hfp hnt hx]

/-- Without `TB`: every plain fixed point attains `gap = O_h = 0` at every decision node with `w_h = 1`. -/
theorem probe_w_one_attained (hfp : M.IsPlainFP π) {n : ℕ} {h : Hist A E n}
    (hnt : M.nonterminal n h) (hw : M.wS π n h = 1) :
    M.gap π n h = M.odds π n h ∧ M.gap π n h = 0 :=
  M.probe_w_one_attained_with_TB hfp hnt hw (M.probe_TB_of_wS_eq_one hfp hnt hw)

/-- **The attainment set of Theorem B's bound, as an `iff` over every model**: at a plain fixed point, a decision
node with `0 < w_h` and `TB`, `gap = O_h` holds iff `w_h = 1`. (`→` is `theoremB_strict`; `←` is generic.) -/
theorem probe_gap_eq_odds_iff (hfp : M.IsPlainFP π) {n : ℕ} {h : Hist A E n}
    (hnt : M.nonterminal n h) (hw : 0 < M.wS π n h) (htb : M.TB π n h) :
    M.gap π n h = M.odds π n h ↔ M.wS π n h = 1 := by
  constructor
  · intro heq
    by_contra hne
    have hw1 : M.wS π n h < 1 := lt_of_le_of_ne (M.wS_le_one hfp.1 hnt) hne
    exact absurd heq (M.theoremB_strict hfp hnt hw hw1 htb).ne
  · intro hw1
    exact (M.probe_w_one_attained_with_TB hfp hnt hw1 htb).1

end Cleanroom.Uea.UeaColeShadow.Model

#print axioms Cleanroom.Uea.UeaColeShadow.Model.probe_gap_eq_odds_iff
#print axioms Cleanroom.Uea.UeaColeShadow.Model.probe_w_one_attained
