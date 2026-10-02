import Cleanroom.Uea.UeaColeShadow.TheoremB

/-!
# Theorem B is strict: `gap < O_h` whenever `0 < w_h < 1`

Mandate target 10 asked for the tightness class of Theorem B (necessary conditions for `gap = O_h`, and
whether the bound is attained). The answer proved here: **it is never attained**. At every plain fixed
point and every trust-bound decision node with `0 < w_h < 1`, `V^*_ξ(h) - V^π_ξ(h) < O_h`. The tight trap
(`SinkOrSwim.tight_trap`, `gap/O_h = 1 - δ`) shows the supremum `1` of `gap/O_h` is approached; this
module shows it is not reached.

Route (the round-1 auditors' derivation, machine-checked here). If `gap = O_h` then both inequalities of
`theoremB` are tight. Tightness of the second forces `p̄_h = 1` (`V^*_ξ(h) ≤ 1 < 1/w_h`); tightness of the
first forces the per-action inequality to be tight at every supported action, and `p̄_h = 1` supplies a
supported `a` with `π̄(a|h) > 0`. A tight per-action inequality at such an `a` forces `Q̄(h,a) = 1`
(`Qmix_eq_one_of_per_action_eq`), so the non-self mixture plays optimally below `(h,a)`; a depth induction
(`Vpi_eq_Vstar_of_Vbar_eq_Vstar`) shows every plain fixed point then also plays optimally below `(h,a)` at
nodes both the self and the non-self reach, so `Q^π_ξ(h,a) = Q^*_ξ(h,a) = V^*_ξ(h)` — but the tight
per-action inequality also says `π(a|h)(V^*_ξ(h) - Q^π_ξ(h,a)) > 0`. Contradiction.

Source: [[uea-cole-shadow-mandate]] target 10; [[sequential-self-game]] §3 (Theorem B). Scope: finite
shadow of rOSI ([[sequential-self-game]] §7).
-/

namespace Cleanroom.Uea.UeaColeShadow

open Finset

namespace Model

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι)
  {π : Policy A E}

/-- If the non-self mixture's action value `Q^{π̄}_ξ(h,b)` is optimal (`= Q^*_ξ(h,b)`), then `V^{π̄}_ξ = V^*_ξ` at
every child `hbe` of positive percept probability (termwise equality in `Q^{π̄} ≤ Q^*`).
Source: none: infrastructure (target 10)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Vbar_eq_Vstar_of_Qbar_eq (n : ℕ) (h : Hist A E n) (b : A)
    (hQ : M.Qbar n h b = M.Qstar n h b) {e : E} (he : M.xie n h b e ≠ 0) :
    M.Vbar (n + 1) (ext h b e) = M.Vstar (n + 1) (ext h b e) := by
  rw [Qbar_eq_sum, Qstar_eq_sum] at hQ
  have hle : ∀ e ∈ (univ : Finset E),
      M.xie n h b e * (M.γ ^ n * M.r n (ext h b e) + M.Vbar (n + 1) (ext h b e)) ≤
        M.xie n h b e * (M.γ ^ n * M.r n (ext h b e) + M.Vstar (n + 1) (ext h b e)) := fun e _ =>
    mul_le_mul_of_nonneg_left (by linarith [M.Vbar_le_Vstar (n + 1) (ext h b e)]) (M.xie_nonneg n h b e)
  have h1 := (Finset.sum_eq_sum_iff_of_le hle).1 hQ e (mem_univ e)
  have h2 := mul_left_cancel₀ he h1
  linarith

/-- If `V^π_ξ = V^*_ξ` at every child `hbe` of positive percept probability, then `Q^π_ξ(h,b) = Q^*_ξ(h,b)`.
Source: none: infrastructure (target 10)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Qpi_eq_Qstar_of_children (n : ℕ) (h : Hist A E n) (b : A)
    (hc : ∀ e, M.xie n h b e ≠ 0 → M.Vpi π (n + 1) (ext h b e) = M.Vstar (n + 1) (ext h b e)) :
    M.Qpi π n h b = M.Qstar n h b := by
  rw [Qpi_eq_sum, Qstar_eq_sum]
  refine sum_congr rfl fun e _ => ?_
  by_cases he : M.xie n h b e = 0
  · rw [he, zero_mul, zero_mul]
  · rw [hc e he]

/-- **Both-reachable optimality propagates to the self.** At a decision node `h` reached by the self
(`ξ_S(h) > 0`) and by the non-self mixture (`ξ_{-S}(h) > 0`) at which the non-self mixture plays optimally
(`V^{π̄}_ξ(h) = V^*_ξ(h)`), every plain fixed point also plays optimally: `V^π_ξ(h) = V^*_ξ(h)`. Proof by depth
induction: a residual-supported action `b` is optimal for `π̄`; if the self never plays it, `w_{hb} = 0` and
`Q_ξ(h,b) = Q̄(h,b) = V^*`; otherwise the children `hbe` satisfy the hypotheses and the induction gives
`Q^π(h,b) = Q^*(h,b) = V^*`, so again `Q_ξ(h,b) = V^*`. Hence `M(h) = V^*`, so every self-supported `c` has
`Q_ξ(h,c) = V^*` with `w_{hc} > 0`, forcing `Q^π(h,c) = V^*`.
Source: [[uea-cole-shadow-mandate]] target 10 (the round-1 audits' derivation)
Kind: P
Fidelity: n/a
Hyps: (a) -/
theorem Vpi_eq_Vstar_of_Vbar_eq_Vstar (hfp : M.IsPlainFP π) :
    ∀ n h, M.nonterminal n h → 0 < M.xiS π n h → M.xins n h ≠ 0 → M.Vbar n h = M.Vstar n h →
      M.Vpi π n h = M.Vstar n h := by
  have hπ := hfp.1
  have hδ : (0:ℝ) < 1 - M.δ := by linarith [M.δ_lt_one]
  refine M.depth_induction (fun n h => M.nonterminal n h → 0 < M.xiS π n h → M.xins n h ≠ 0 →
    M.Vbar n h = M.Vstar n h → M.Vpi π n h = M.Vstar n h) ?_ ?_
  · intro n h hnt hnt' _ _ _
    exact absurd hnt' hnt
  · intro n h hnt ih _ hS hxins hVbar
    -- residual-supported actions are optimal for `π̄`
    have hopt : ∀ b, M.pibar n h b ≠ 0 → M.Qbar n h b = M.Vstar n h := by
      intro b hb
      have hle : ∀ b ∈ (univ : Finset A), M.pibar n h b * M.Qbar n h b ≤ M.pibar n h b * M.Vstar n h :=
        fun b _ => mul_le_mul_of_nonneg_left (M.Qbar_le_Vstar hnt b) (M.pibar_nonneg n h b)
      have hsum : ∑ b, M.pibar n h b * M.Qbar n h b = ∑ b, M.pibar n h b * M.Vstar n h := by
        rw [← M.Vbar_eq hnt, ← sum_mul, M.pibar_sum_eq_one hxins, one_mul, hVbar]
      have h1 := (Finset.sum_eq_sum_iff_of_le hle).1 hsum b (mem_univ b)
      exact mul_left_cancel₀ hb h1
    -- some residual-supported action exists
    have hsum1 : ∑ b, M.pibar n h b ≠ 0 := by rw [M.pibar_sum_eq_one hxins]; exact one_ne_zero
    obtain ⟨b, _, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum1
    have hxA : M.xinsA n h b ≠ 0 := fun h0 => hb (by simp [pibar, h0])
    have hxApos : 0 < M.xinsA n h b := lt_of_le_of_ne (M.xinsA_nonneg n h b) (Ne.symm hxA)
    have hQbar : M.Qbar n h b = M.Vstar n h := hopt b hb
    have hQstar : M.Qstar n h b = M.Vstar n h :=
      le_antisymm (M.Qstar_le_Vstar hnt b) (hQbar ▸ M.Qbar_le_Qstar n h b)
    have hxiA : M.xiA π n h b ≠ 0 := by
      rw [xiA_eq]
      have h1 : 0 ≤ (1 - M.δ) * M.xiS π n h * π n h b :=
        mul_nonneg (mul_nonneg hδ.le hS.le) (hπ.nonneg hnt b)
      linarith
    -- `Q_ξ(h,b) = V^*`
    have hQxi : M.Qxi π n h b = M.Vstar n h := by
      rw [M.Qxi_eq_wA hπ hxiA, M.Qmix_eq_Qbar hxA, hQbar]
      by_cases hpb : π n h b = 0
      · rw [M.wA_of_xiA_ne_zero hxiA, hpb]
        ring
      · have hpb' : 0 < π n h b := lt_of_le_of_ne (hπ.nonneg hnt b) (Ne.symm hpb)
        have hchild : ∀ e, M.xie n h b e ≠ 0 →
            M.Vpi π (n + 1) (ext h b e) = M.Vstar (n + 1) (ext h b e) := by
          intro e he
          by_cases hc : M.nonterminal (n + 1) (ext h b e)
          · have hepos : 0 < M.xie n h b e := lt_of_le_of_ne (M.xie_nonneg n h b e) (Ne.symm he)
            refine ih b e hc ?_ ?_ ?_
            · rw [xiS_ext]
              positivity
            · rw [xins_ext]
              exact mul_ne_zero hxA he
            · exact M.Vbar_eq_Vstar_of_Qbar_eq n h b (hQbar.trans hQstar.symm) he
          · rw [M.Vpi_of_not_nonterminal hc, M.Vstar_of_not_nonterminal hc]
        rw [M.Qpi_eq_Qstar_of_children n h b hchild, hQstar]
        ring
    have hM : M.Mx π n h = M.Vstar n h :=
      le_antisymm (M.Mx_le_Vstar hπ hnt) (hQxi ▸ M.Qxi_le_Mx n h b)
    -- every self-supported action has `Q^π = V^*`
    have hsupp : ∀ c ∈ supp π n h, M.Qpi π n h c = M.Vstar n h := by
      intro c hc
      rw [mem_supp] at hc
      have hQc : M.Qxi π n h c = M.Vstar n h := by rw [hfp.2 n h hnt c hc, hM]
      have hxiAc : 0 < M.xiA π n h c := by
        rw [xiA_eq]
        have := M.xinsA_nonneg n h c
        positivity
      have hwA : 0 < M.wA π n h c := by
        rw [M.wA_of_xiA_ne_zero hxiAc.ne']
        positivity
      have hwA1 := M.wA_le_one hπ hnt c
      have hmix := M.Qmix_le_Vstar hnt c
      have hQpi_le : M.Qpi π n h c ≤ M.Vstar n h :=
        le_trans (M.Qpi_le_Qstar hπ n h c) (M.Qstar_le_Vstar hnt c)
      have e := M.Qxi_eq_wA hπ hxiAc.ne'
      rw [hQc] at e
      have hge : M.Vstar n h ≤ M.Qpi π n h c := by
        by_contra hlt
        have h1 := mul_pos hwA (sub_pos.2 (not_le.1 hlt))
        have h2 := mul_nonneg (sub_nonneg.2 hwA1) (sub_nonneg.2 hmix)
        nlinarith
      exact le_antisymm hQpi_le hge
    rw [M.Vpi_eq_sum_supp hπ hnt, sum_congr rfl fun c hc => by rw [hsupp c hc], ← sum_mul,
      M.sum_supp_eq_one hπ hnt, one_mul]

/-- **Tightness of the per-action inequality forces `Q̄(h,a) = 1`.** At a decision node with `ξ(h) ≠ 0` and
`0 < w_h < 1`, at an action `a` with `π̄(a|h) > 0` clearing the trust threshold, equality in
`per_action_bound` (with `c = 1`) gives `Q̄(h,a) = 1` (and `Q_ξ(h,a) = w_h V^*_ξ(h)`, not needed).
Source: [[uea-cole-shadow-mandate]] target 10 (necessary conditions)
Kind: P
Fidelity: n/a
Hyps: (a) -/
theorem Qmix_eq_one_of_per_action_eq (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hx : M.xi π n h ≠ 0) (hw : 0 < M.wS π n h) (hw1 : M.wS π n h < 1) {a : A}
    (hq : 0 < M.pibar n h a) (hQ : M.wS π n h * M.Vstar n h ≤ M.Qxi π n h a)
    (heq : π n h a * (M.Vstar n h - M.Qpi π n h a) =
      (1 - M.wS π n h) * (π n h a * M.Vstar n h + M.pibar n h a * (1 / M.wS π n h - M.Vstar n h))) :
    M.Qmix n h a = 1 := by
  have e := M.xia_mul_Qxi hπ hnt hx a
  have f := M.xia_eq_wS hπ hnt hx a
  rw [f] at e
  have hxia : 0 ≤ M.xia π n h a := M.xia_nonneg hπ hnt a
  rw [f] at hxia
  have hm1 := M.Qmix_le_one hnt.1 h a
  have hwu : M.wS π n h * (1 / M.wS π n h) = 1 := mul_one_div_cancel hw.ne'
  have h1w : 0 < 1 - M.wS π n h := by linarith
  have key : (M.wS π n h * π n h a + (1 - M.wS π n h) * M.pibar n h a) *
      (M.Qxi π n h a - M.wS π n h * M.Vstar n h) =
      (1 - M.wS π n h) * M.pibar n h a * (M.Qmix n h a - 1) := by
    linear_combination e - M.wS π n h * heq - (1 - M.wS π n h) * M.pibar n h a * hwu
  have hL : 0 ≤ (M.wS π n h * π n h a + (1 - M.wS π n h) * M.pibar n h a) *
      (M.Qxi π n h a - M.wS π n h * M.Vstar n h) := mul_nonneg hxia (by linarith)
  have hR : (1 - M.wS π n h) * M.pibar n h a * (M.Qmix n h a - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_pos h1w hq).le (by linarith)
  have hzero : (1 - M.wS π n h) * M.pibar n h a * (M.Qmix n h a - 1) = 0 :=
    le_antisymm hR (key ▸ hL)
  rcases mul_eq_zero.1 hzero with h0 | h0
  · exact absurd h0 (mul_pos h1w hq).ne'
  · linarith

/-- **Theorem B is strict.** Every model, every plain fixed point `π`, every decision node `h` with
`0 < w_h < 1` at which `(TB_h)` holds: `V^*_ξ(h) - V^π_ξ(h) < O_h`. The bound of `theoremB_odds` is never
attained; its supremum `1` of `gap/O_h` (approached by `SinkOrSwim.tight_trap`) is not a maximum. At `w_h = 1`
the bound is `gap ≤ 0`, attained. Scope: finite shadow of rOSI ([[sequential-self-game]] §7).
Source: [[uea-cole-shadow-mandate]] target 10 (attainment); [[sequential-self-game]] §3 (Theorem B)
Kind: P
Fidelity: stronger (strict inequality; the note states `≤`)
Hyps: (a) -/
theorem theoremB_strict (hfp : M.IsPlainFP π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hw : 0 < M.wS π n h) (hw1 : M.wS π n h < 1) (htb : M.TB π n h) :
    M.gap π n h < M.odds π n h := by
  have hπ := hfp.1
  have hB := M.theoremB hfp hnt hw htb
  refine lt_of_le_of_ne (le_trans hB.1 hB.2) fun heq => ?_
  have hxins : M.xins n h ≠ 0 := fun h0 => by
    have := (M.wS_eq_one_iff hπ hnt).2 h0
    linarith
  have hx : M.xi π n h ≠ 0 := fun h0 => hxins (M.xins_eq_zero_of_xi_eq_zero hπ hnt h0)
  have hS : 0 < M.xiS π n h := M.xiS_pos_of_wS_pos hπ hnt hx hw
  have hV1 := M.Vstar_le_one n h
  have hV0 := M.Vstar_nonneg n h
  have h1w : 0 < 1 - M.wS π n h := by linarith
  have hwu : M.wS π n h * (1 / M.wS π n h) = 1 := mul_one_div_cancel hw.ne'
  -- the second inequality is tight
  have hX : (1 - M.wS π n h) * ((1 - M.pbar π n h) * M.Vstar n h + M.pbar π n h / M.wS π n h) =
      M.odds π n h := le_antisymm hB.2 (by rw [← heq]; exact hB.1)
  -- hence `p̄_h = 1`
  have hpb : M.pbar π n h = 1 := by
    unfold odds at hX
    have key : (1 - M.wS π n h) * (1 - M.pbar π n h) * (M.wS π n h * M.Vstar n h - 1) = 0 := by
      linear_combination M.wS π n h * hX + (1 - M.wS π n h) * (1 - M.pbar π n h) * hwu
    rcases mul_eq_zero.1 key with h0 | h0
    · rcases mul_eq_zero.1 h0 with h1 | h1
      · exact absurd h1 h1w.ne'
      · linarith
    · have : M.wS π n h * M.Vstar n h ≤ M.wS π n h := mul_le_of_le_one_right hw.le hV1
      linarith
  -- the first inequality is tight, termwise
  have hper : ∀ a ∈ supp π n h, π n h a * (M.Vstar n h - M.Qpi π n h a) ≤
      (1 - M.wS π n h) * (π n h a * M.Vstar n h + M.pibar n h a * (1 / M.wS π n h - M.Vstar n h)) := by
    intro a ha
    rw [mem_supp] at ha
    have hQ : M.wS π n h * M.Vstar n h ≤ M.Qxi π n h a := by
      rw [hfp.2 n h hnt a ha]
      exact htb
    exact M.per_action_bound hπ hnt hx hw (by simpa using M.sum_nu_Qnu_le_xinsA hnt.1 h a) hQ
  have hsum : M.gap π n h = ∑ a ∈ supp π n h, π n h a * (M.Vstar n h - M.Qpi π n h a) := by
    unfold gap
    rw [M.Vpi_eq_sum_supp hπ hnt]
    simp_rw [mul_sub]
    rw [sum_sub_distrib, ← sum_mul, M.sum_supp_eq_one hπ hnt, one_mul]
  have hsumR : ∑ a ∈ supp π n h, (1 - M.wS π n h) *
      (π n h a * M.Vstar n h + M.pibar n h a * (1 / M.wS π n h - M.Vstar n h)) =
      (1 - M.wS π n h) * ((1 - M.pbar π n h) * M.Vstar n h + M.pbar π n h / M.wS π n h) := by
    rw [← mul_sum, sum_add_distrib, ← sum_mul, ← sum_mul, M.sum_supp_eq_one hπ hnt]
    unfold pbar
    ring
  have hteq : ∑ a ∈ supp π n h, π n h a * (M.Vstar n h - M.Qpi π n h a) =
      ∑ a ∈ supp π n h, (1 - M.wS π n h) *
        (π n h a * M.Vstar n h + M.pibar n h a * (1 / M.wS π n h - M.Vstar n h)) := by
    rw [← hsum, hsumR, hX, heq]
  have htight := (Finset.sum_eq_sum_iff_of_le hper).1 hteq
  -- a supported action with `π̄(a|h) > 0`
  have hpb' : ∑ a ∈ supp π n h, M.pibar n h a ≠ 0 := by
    unfold pbar at hpb
    rw [hpb]
    exact one_ne_zero
  obtain ⟨a, ha, hqa⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpb'
  have hpa : 0 < π n h a := mem_supp.1 ha
  have hq : 0 < M.pibar n h a := lt_of_le_of_ne (M.pibar_nonneg n h a) (Ne.symm hqa)
  have hQ : M.wS π n h * M.Vstar n h ≤ M.Qxi π n h a := by
    rw [hfp.2 n h hnt a hpa]
    exact htb
  -- `Q̄(h,a) = 1`, hence `Q^*(h,a) = 1 = V^*(h)` and the non-self mixture is optimal below `(h,a)`
  have hm : M.Qmix n h a = 1 := M.Qmix_eq_one_of_per_action_eq hπ hnt hx hw hw1 hq hQ (htight a ha)
  have hxA : M.xinsA n h a ≠ 0 := fun h0 => hqa (by simp [pibar, h0])
  have hQbar : M.Qbar n h a = 1 := by rw [← M.Qmix_eq_Qbar hxA]; exact hm
  have hQstar : M.Qstar n h a = 1 :=
    le_antisymm (M.Qstar_le_one hnt.1 h a) (hQbar ▸ M.Qbar_le_Qstar n h a)
  have hVeq : M.Vstar n h = 1 := le_antisymm hV1 (hQstar ▸ M.Qstar_le_Vstar hnt a)
  -- the self is optimal below `(h,a)` too
  have hchild : ∀ e, M.xie n h a e ≠ 0 →
      M.Vpi π (n + 1) (ext h a e) = M.Vstar (n + 1) (ext h a e) := by
    intro e he
    by_cases hc : M.nonterminal (n + 1) (ext h a e)
    · have hepos : 0 < M.xie n h a e := lt_of_le_of_ne (M.xie_nonneg n h a e) (Ne.symm he)
      refine M.Vpi_eq_Vstar_of_Vbar_eq_Vstar hfp (n + 1) (ext h a e) hc ?_ ?_ ?_
      · rw [xiS_ext]
        positivity
      · rw [xins_ext]
        exact mul_ne_zero hxA he
      · exact M.Vbar_eq_Vstar_of_Qbar_eq n h a (hQbar.trans hQstar.symm) he
    · rw [M.Vpi_of_not_nonterminal hc, M.Vstar_of_not_nonterminal hc]
  have hQpi : M.Qpi π n h a = M.Vstar n h := by
    rw [M.Qpi_eq_Qstar_of_children n h a hchild, hQstar, hVeq]
  -- but the tight per-action inequality at `a` has a positive right-hand side
  have ht := htight a ha
  rw [hQpi, sub_self, mul_zero] at ht
  have hinv : 1 < 1 / M.wS π n h := by
    rw [lt_div_iff₀ hw]
    linarith
  have hpos : 0 < (1 - M.wS π n h) *
      (π n h a * M.Vstar n h + M.pibar n h a * (1 / M.wS π n h - M.Vstar n h)) := by
    apply mul_pos h1w
    have h1 : 0 < M.pibar n h a * (1 / M.wS π n h - M.Vstar n h) := mul_pos hq (by linarith)
    have h2 : 0 ≤ π n h a * M.Vstar n h := mul_nonneg hpa.le hV0
    linarith
  linarith

/-- **Theorem B, tightness of the second step**: for a policy at a decision node with `0 < w_h < 1`,
`(1-w_h)[(1-p̄_h)V^*_ξ(h) + p̄_h/w_h] = O_h` iff `p̄_h = 1` (the non-self mixture is carried entirely by the
agent's support). Pure algebra in `p̄_h`, `w_h`, `V^*` (only `V^* ≤ 1` is used): no policy or fixed-point
hypothesis, and `p̄_h = 1` does occur — at `SinkOrSwim.mixed_witness_second_step_tight` the second step is an
equality while the first is strict. So a trust-bound node with `p̄_h < 1` has `gap < O_h` already from the second
step, with room `(1-w_h)(1-p̄_h)(1/w_h - V^*)`; at a node with `p̄_h = 1` the strictness of `theoremB_strict` comes
entirely from the first step. (The repair-round-1 sentence "the only way to approach `O_h` is through `p̄_h → 1`"
was false: the tight trap approaches the supremum with `p̄ = 0`, `SinkOrSwim.sup_approached_with_pbar_zero`.)
Source: [[uea-cole-shadow-mandate]] target 10 (necessary conditions)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem theoremB_second_eq_iff {n : ℕ} {h : Hist A E n} (hw : 0 < M.wS π n h) (hw1 : M.wS π n h < 1) :
    (1 - M.wS π n h) * ((1 - M.pbar π n h) * M.Vstar n h + M.pbar π n h / M.wS π n h) = M.odds π n h ↔
      M.pbar π n h = 1 := by
  have hV1 := M.Vstar_le_one n h
  have h1w : 0 < 1 - M.wS π n h := by linarith
  have hwu : M.wS π n h * (1 / M.wS π n h) = 1 := mul_one_div_cancel hw.ne'
  unfold odds
  constructor
  · intro hX
    have key : (1 - M.wS π n h) * (1 - M.pbar π n h) * (M.wS π n h * M.Vstar n h - 1) = 0 := by
      linear_combination M.wS π n h * hX + (1 - M.wS π n h) * (1 - M.pbar π n h) * hwu
    rcases mul_eq_zero.1 key with h0 | h0
    · rcases mul_eq_zero.1 h0 with h1 | h1
      · exact absurd h1 h1w.ne'
      · linarith
    · have : M.wS π n h * M.Vstar n h ≤ M.wS π n h := mul_le_of_le_one_right hw.le hV1
      linarith
  · intro hpb
    rw [hpb]
    ring

end Model

/-- **Target 10, attainment, resolved**: no model, plain fixed point and trust-bound decision node with
`0 < w_h < 1` attains `gap = O_h`. (The direction the round-1 audits conjectured; proved via
`theoremB_strict`.) Universe: the quantified types are in `Type`; the theorem `theoremB_strict` behind it is
universe-polymorphic.
Source: [[uea-cole-shadow-mandate]] target 10
Kind: C
Fidelity: n/a
Hyps: (a) -/
theorem gap_eq_odds_not_attained :
    ¬ ∃ (A E ι : Type) (_ : Fintype A) (_ : Fintype E) (_ : Fintype ι) (_ : Nonempty A) (M : Model A E ι)
        (π : Policy A E) (n : ℕ) (h : Hist A E n), M.IsPlainFP π ∧ M.nonterminal n h ∧ 0 < M.wS π n h ∧
          M.wS π n h < 1 ∧ M.TB π n h ∧ M.gap π n h = M.odds π n h := by
  rintro ⟨A, E, ι, _, _, _, _, M, π, n, h, hfp, hnt, hw, hw1, htb, heq⟩
  exact absurd heq (M.theoremB_strict hfp hnt hw hw1 htb).ne

end Cleanroom.Uea.UeaColeShadow
