import Cleanroom.Uea.UeaColeShadow.TheoremB

/-!
# Theorem C, horizon form: every fixed point of the floored agent is near-optimal

For every model, every floored fixed point `π` and every decision node `h` with `0 < w_h`:
`ε(h) = V^*_ξ(h) - V^π_ξ(h) ≤ O_h (1 + T)`, with no trust-bound hypothesis, no `|A|` and no tie clause.
The proof is a node-local induction on the remaining depth, proving the stronger
`ε(h) ≤ O_h (1 + T - depth h)`: at a node the loss splits into the argmax part (bounded by `O_h` through
Theorem B's per-action inequality, with the trust bound available because the floor did not fire) and the
`π⋆`-part `π(π⋆(h)|h) ∑_e ξ(e|hπ⋆) ε(hπ⋆e)`, whose children have odds `O_{hπ⋆e} = O_h π̄(π⋆|h)/π(π⋆|h)` (F2, F1),
so the induction hypothesis at the children gives `≤ O_h π̄(π⋆|h) (T - depth h) ≤ O_h (T - depth h)`.
A reset node (`r_h < 0`) has only the `π⋆`-part.

Source: [[sequential-self-game]] §4.1 (Theorem C, horizon form; Steps 0–4 and 7(i)). Scope: finite shadow
of rOSI — finite horizon and hypothesis class, fixed points for oracles, continuous extension at `ξ`-null
nodes ([[sequential-self-game]] §7).
-/

namespace Cleanroom.Uea.UeaColeShadow

open Finset

namespace Model

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι)
  {π : Policy A E}

theorem odds_nonneg (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hw : 0 < M.wS π n h) : 0 ≤ M.odds π n h :=
  div_nonneg (by linarith [M.wS_le_one hπ hnt]) hw.le

/-- A floored fixed point supports only actions that are EDT-optimal or equal to `π⋆(h)`, at every node
where the floor does not fire strictly.
Source: [[sequential-self-game]] §1 (floored agent), §4.1 (Step 1)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem IsFlooredFP.supp_of_nonneg {M : Model A E ι} (hfp : M.IsFlooredFP π) {n : ℕ} {h : Hist A E n}
    (hnt : M.nonterminal n h) (hr : 0 ≤ M.resid π n h) {a : A} (ha : 0 < π n h a) :
    M.Qxi π n h a = M.Mx π n h ∨ a = M.piStar n h := by
  rcases lt_or_eq_of_le hr with hpos | h0
  · exact Or.inl ((hfp.2 n h hnt).2.1 hpos a ha)
  · exact (hfp.2 n h hnt).2.2 h0.symm a ha

/-- **Step 0**: at a `ξ_{-S}`-null decision node of a floored fixed point the loss is `0` (the whole
subtree has `w ≡ 1` and `Q_ξ = Q^π`; every node is an equality node with `π⋆` and the argmax both
optimal).
Source: [[sequential-self-game]] §4.1 (Step 0)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Vpi_eq_Vstar_of_xins_eq_zero (hfp : M.IsFlooredFP π) :
    ∀ n h, M.nonterminal n h → M.xins n h = 0 → M.Vpi π n h = M.Vstar n h := by
  have hπ := hfp.1
  refine M.depth_induction (fun n h => M.nonterminal n h → M.xins n h = 0 → M.Vpi π n h = M.Vstar n h) ?_ ?_
  · intro n h hnt hnt' _
    exact absurd hnt' hnt
  · intro n h hnt ih _ hx
    -- children: `V^π = V^*`
    have hchild : ∀ a e, M.Vpi π (n + 1) (ext h a e) = M.Vstar (n + 1) (ext h a e) := by
      intro a e
      by_cases hc : M.nonterminal (n + 1) (ext h a e)
      · exact ih a e hc (M.xins_ext_eq_zero hx a e)
      · rw [M.Vpi_of_not_nonterminal hc, M.Vstar_of_not_nonterminal hc]
    have hQ : ∀ a, M.Qpi π n h a = M.Qstar n h a := by
      intro a
      rw [Qpi_eq_sum, Qstar_eq_sum]
      exact sum_congr rfl fun e _ => by rw [hchild a e]
    have hQxi : ∀ a, M.Qxi π n h a = M.Qstar n h a := fun a => by
      rw [M.Qxi_eq_Qpi_of_xins_eq_zero hx a, hQ a]
    have hM : M.Mx π n h = M.Vstar n h := by
      rw [M.Vstar_eq hnt]
      unfold Mx
      exact congrArg _ (funext hQxi)
    have hw : M.wS π n h = 1 := (M.wS_eq_one_iff hπ hnt).2 hx
    have hr : 0 ≤ M.resid π n h := by
      unfold resid
      rw [hM, hw, one_mul, sub_self]
    -- every supported action has `Q^π = V^*`
    have hsupp : ∀ a ∈ supp π n h, M.Qpi π n h a = M.Vstar n h := by
      intro a ha
      rw [mem_supp] at ha
      rcases hfp.supp_of_nonneg hnt hr ha with h1 | h1
      · rw [hQ a, ← hQxi a, h1, hM]
      · rw [h1, hQ, ← M.Vstar_eq_Qstar_piStar hnt]
    rw [M.Vpi_eq_sum_supp hπ hnt, sum_congr rfl fun a ha => by rw [hsupp a ha], ← sum_mul,
      M.sum_supp_eq_one hπ hnt, one_mul]

/-- **Node identity, `π⋆`-part**: `V^*_ξ(h) - Q^π_ξ(h, π⋆(h)) = ∑_e ξ(e|hπ⋆) ε(hπ⋆e)` (same percept kernel
and immediate rewards; absolute discounting, so no extra factor).
Source: [[sequential-self-game]] §4.1 (Step 2)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Vstar_sub_Qpi_piStar {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    M.Vstar n h - M.Qpi π n h (M.piStar n h) =
      ∑ e, M.xie n h (M.piStar n h) e * M.gap π (n + 1) (ext h (M.piStar n h) e) := by
  rw [M.Vstar_eq_Qstar_piStar hnt, Qstar_eq_sum, Qpi_eq_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun e _ => ?_
  unfold gap
  ring

/-- **Odds along `π⋆`**: at a decision node with `ξ_S(h) > 0` and `λ := π(π⋆|h) > 0`, every child `hπ⋆e` of
positive percept probability is a decision node or terminal, has `w > 0`, and its odds satisfy
`λ O_{hπ⋆e} = O_h π̄(π⋆|h)` (F2 in odds form and F1).
Source: [[sequential-self-game]] §4.1 (Step 4)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem child_odds (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hS : 0 < M.xiS π n h) {a : A} (ha : 0 < π n h a) {e : E} (he : M.xie n h a e ≠ 0) :
    0 < M.wS π (n + 1) (ext h a e) ∧
      π n h a * M.odds π (n + 1) (ext h a e) = M.odds π n h * M.pibar n h a := by
  have hA : 0 < M.xiA π n h a := by
    rw [xiA_eq]
    have := M.xinsA_nonneg n h a
    have hδ : (0:ℝ) < 1 - M.δ := by linarith [M.δ_lt_one]
    positivity
  have hwA : 0 < M.wA π n h a := by
    rw [M.wA_of_xiA_ne_zero hA.ne']
    have hδ : (0:ℝ) < 1 - M.δ := by linarith [M.δ_lt_one]
    positivity
  refine ⟨by rw [M.wS_ext_of_xie_ne_zero h a he]; exact hwA, ?_⟩
  rw [M.odds_ext_of_xie_ne_zero h a he, M.oddsA_eq hπ hnt hS ha]
  field_simp

/-- **The `π⋆`-part is bounded by `O_h (T - depth h)`**, given the induction hypothesis at the children:
`π(π⋆|h) (V^*_ξ(h) - Q^π_ξ(h, π⋆(h))) ≤ O_h (T - depth h)`.
Source: [[sequential-self-game]] §4.1 (Steps 2, 4)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem piStar_part_le (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hw : 0 < M.wS π n h) (hS : 0 < M.xiS π n h)
    (ih : ∀ a e, M.nonterminal (n + 1) (ext h a e) → 0 < M.wS π (n + 1) (ext h a e) →
      M.gap π (n + 1) (ext h a e) ≤ M.odds π (n + 1) (ext h a e) * (1 + ((M.T : ℝ) - ((n + 1 : ℕ) : ℝ)))) :
    π n h (M.piStar n h) * (M.Vstar n h - M.Qpi π n h (M.piStar n h)) ≤
      M.odds π n h * ((M.T : ℝ) - n) := by
  set a := M.piStar n h with ha_def
  have hTn : (0:ℝ) ≤ (M.T : ℝ) - n := by
    have := hnt.1
    have : (n : ℝ) < M.T := by exact_mod_cast this
    linarith
  have hodds := M.odds_nonneg hπ hnt hw
  rcases (hπ.nonneg hnt a).lt_or_eq with hpos | hzero
  · -- `λ > 0`: use the children's odds
    rw [M.Vstar_sub_Qpi_piStar hnt, mul_sum]
    have hterm : ∀ e, π n h a * (M.xie n h a e * M.gap π (n + 1) (ext h a e)) ≤
        M.xie n h a e * (M.odds π n h * M.pibar n h a * ((M.T : ℝ) - n)) := by
      intro e
      by_cases he : M.xie n h a e = 0
      · rw [he]; simp
      · obtain ⟨hwc, hoc⟩ := M.child_odds hπ hnt hS hpos he
        have hxe : 0 ≤ M.xie n h a e := M.xie_nonneg n h a e
        by_cases hc : M.nonterminal (n + 1) (ext h a e)
        · have hg := ih a e hc hwc
          have hsimp : (1 + ((M.T : ℝ) - ((n + 1 : ℕ) : ℝ))) = (M.T : ℝ) - n := by push_cast; ring
          rw [hsimp] at hg
          calc π n h a * (M.xie n h a e * M.gap π (n + 1) (ext h a e))
              ≤ π n h a * (M.xie n h a e * (M.odds π (n + 1) (ext h a e) * ((M.T : ℝ) - n))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg hxe) hpos.le
            _ = M.xie n h a e * ((π n h a * M.odds π (n + 1) (ext h a e)) * ((M.T : ℝ) - n)) := by ring
            _ = M.xie n h a e * (M.odds π n h * M.pibar n h a * ((M.T : ℝ) - n)) := by rw [hoc]
        · have hg : M.gap π (n + 1) (ext h a e) = 0 := by
            unfold gap
            rw [M.Vstar_of_not_nonterminal hc, M.Vpi_of_not_nonterminal hc, sub_zero]
          rw [hg, mul_zero, mul_zero]
          exact mul_nonneg hxe (mul_nonneg (mul_nonneg hodds (M.pibar_nonneg n h a)) hTn)
    calc ∑ e, π n h a * (M.xie n h a e * M.gap π (n + 1) (ext h a e))
        ≤ ∑ e, M.xie n h a e * (M.odds π n h * M.pibar n h a * ((M.T : ℝ) - n)) := sum_le_sum fun e _ => hterm e
      _ = M.odds π n h * M.pibar n h a * ((M.T : ℝ) - n) := by rw [← sum_mul, M.xie_sum, one_mul]
      _ ≤ M.odds π n h * 1 * ((M.T : ℝ) - n) := by
          gcongr
          exact M.pibar_le_one n h a
      _ = M.odds π n h * ((M.T : ℝ) - n) := by ring
  · rw [← hzero, zero_mul]
    exact mul_nonneg hodds hTn

/-- **Node loss of the argmax part**: at a decision node with `ξ(h) ≠ 0`, `0 < w_h` and the trust bound, the
loss carried by the EDT-optimal supported actions is at most `O_h`
(Theorem B's per-action inequality summed over `𝒜_h ∩ supp π(·|h)`).
Source: [[sequential-self-game]] §4.1 (Step 3), §3
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem argmax_part_le (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hx : M.xi π n h ≠ 0) (hw : 0 < M.wS π n h) (htb : M.TB π n h) :
    ∑ a ∈ (supp π n h).filter (fun a => M.Qxi π n h a = M.Mx π n h),
        π n h a * (M.Vstar n h - M.Qpi π n h a) ≤ M.odds π n h := by
  set S := (supp π n h).filter (fun a => M.Qxi π n h a = M.Mx π n h) with hS_def
  have hw1 := M.wS_le_one hπ hnt
  have hV0 := M.Vstar_nonneg n h
  have hV1 := M.Vstar_le_one n h
  have hper : ∀ a ∈ S, π n h a * (M.Vstar n h - M.Qpi π n h a) ≤
      (1 - M.wS π n h) * (π n h a * M.Vstar n h + M.pibar n h a * (1 / M.wS π n h - M.Vstar n h)) := by
    intro a ha
    rw [hS_def, mem_filter] at ha
    have hQ : M.wS π n h * M.Vstar n h ≤ M.Qxi π n h a := by rw [ha.2]; exact htb
    exact M.per_action_bound hπ hnt hx hw (by simpa using M.sum_nu_Qnu_le_xinsA hnt.1 h a) hQ
  have hp1 : ∑ a ∈ S, π n h a ≤ 1 := by
    rw [← hπ.sum hnt]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun a _ _ => hπ.nonneg hnt a
  have hp0 : 0 ≤ ∑ a ∈ S, π n h a := sum_nonneg fun a _ => hπ.nonneg hnt a
  have hq1 : ∑ a ∈ S, M.pibar n h a ≤ 1 :=
    le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun a _ _ => M.pibar_nonneg n h a)
      (M.pibar_sum_le_one n h)
  have hq0 : 0 ≤ ∑ a ∈ S, M.pibar n h a := sum_nonneg fun a _ => M.pibar_nonneg n h a
  have hinv : 1 ≤ 1 / M.wS π n h := by rw [le_div_iff₀ hw]; linarith
  have hinvV : 0 ≤ 1 / M.wS π n h - M.Vstar n h := by linarith
  calc ∑ a ∈ S, π n h a * (M.Vstar n h - M.Qpi π n h a)
      ≤ ∑ a ∈ S, (1 - M.wS π n h) *
          (π n h a * M.Vstar n h + M.pibar n h a * (1 / M.wS π n h - M.Vstar n h)) := sum_le_sum hper
    _ = (1 - M.wS π n h) * ((∑ a ∈ S, π n h a) * M.Vstar n h +
          (∑ a ∈ S, M.pibar n h a) * (1 / M.wS π n h - M.Vstar n h)) := by
        rw [← mul_sum, sum_add_distrib, sum_mul, sum_mul]
    _ ≤ (1 - M.wS π n h) * (1 * M.Vstar n h + (∑ a ∈ S, M.pibar n h a) * (1 / M.wS π n h - M.Vstar n h)) := by
        gcongr
    _ = (1 - M.wS π n h) * ((1 - ∑ a ∈ S, M.pibar n h a) * M.Vstar n h + (∑ a ∈ S, M.pibar n h a) / M.wS π n h) := by
        ring
    _ ≤ (1 - M.wS π n h) * (1 / M.wS π n h) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        have h1 : (1 - ∑ a ∈ S, M.pibar n h a) * M.Vstar n h ≤ (1 - ∑ a ∈ S, M.pibar n h a) * (1 / M.wS π n h) :=
          mul_le_mul_of_nonneg_left (le_trans hV1 hinv) (by linarith)
        have h2 : (1 - ∑ a ∈ S, M.pibar n h a) * (1 / M.wS π n h) + (∑ a ∈ S, M.pibar n h a) / M.wS π n h =
            1 / M.wS π n h := by field_simp; ring
        linarith
    _ = M.odds π n h := by unfold odds; ring

/-- **Theorem C, depth-refined horizon form.** For every model, every floored fixed point `π`, every decision
node `h` of depth `n` with `0 < w_h`: `ε(h) ≤ O_h (1 + T - n)`. No trust-bound hypothesis, no `|A|`, no tie
clause. Scope: finite shadow of rOSI — finite horizon and hypothesis class, fixed points for oracles,
continuous extension at `ξ`-null nodes ([[sequential-self-game]] §7).
Source: [[sequential-self-game]] §4.1 (Theorem C, horizon form); [[uea-inventory]] 011
Kind: P
Fidelity: stronger: depth-refined (the note's `O_h (1 + T)` is `theoremC`)
Hyps: (a) -/
theorem theoremC_depth (hfp : M.IsFlooredFP π) :
    ∀ n h, M.nonterminal n h → 0 < M.wS π n h → M.gap π n h ≤ M.odds π n h * (1 + ((M.T : ℝ) - n)) := by
  have hπ := hfp.1
  refine M.depth_induction (fun n h => M.nonterminal n h → 0 < M.wS π n h →
    M.gap π n h ≤ M.odds π n h * (1 + ((M.T : ℝ) - n))) ?_ ?_
  · intro n h hnt hnt' _
    exact absurd hnt' hnt
  · intro n h hnt ih hnt' hw
    have hTn : (0:ℝ) ≤ (M.T : ℝ) - n := by
      have : (n : ℝ) < M.T := by exact_mod_cast hnt.1
      linarith
    have hodds := M.odds_nonneg hπ hnt hw
    by_cases hx : M.xins n h = 0
    · -- Step 0
      unfold gap
      rw [M.Vpi_eq_Vstar_of_xins_eq_zero hfp n h hnt hx, sub_self]
      exact mul_nonneg hodds (by linarith)
    · have hxi : M.xi π n h ≠ 0 := by
        intro h0
        exact hx (M.xins_eq_zero_of_xi_eq_zero hπ hnt h0)
      have hS : 0 < M.xiS π n h := M.xiS_pos_of_wS_pos hπ hnt hxi hw
      set a := M.piStar n h with ha_def
      -- the `π⋆`-part
      have hstar := M.piStar_part_le hπ hnt hw hS ih
      -- nonnegativity of the per-action losses
      have hf0 : ∀ b, 0 ≤ π n h b * (M.Vstar n h - M.Qpi π n h b) := fun b =>
        mul_nonneg (hπ.nonneg hnt b) (sub_nonneg.2 (le_trans (M.Qpi_le_Qstar hπ n h b) (M.Qstar_le_Vstar hnt b)))
      have hsum : M.gap π n h = ∑ b ∈ supp π n h, π n h b * (M.Vstar n h - M.Qpi π n h b) := by
        unfold gap
        rw [M.Vpi_eq_sum_supp hπ hnt]
        simp_rw [mul_sub]
        rw [sum_sub_distrib, ← sum_mul, M.sum_supp_eq_one hπ hnt, one_mul]
      rw [hsum]
      by_cases hr : M.resid π n h < 0
      · -- reset node: the support is `{π⋆(h)}`
        have hsub : supp π n h ⊆ {a} := by
          intro b hb
          rw [mem_supp] at hb
          rw [mem_singleton]
          exact (hfp.2 n h hnt).1 hr b hb
        calc ∑ b ∈ supp π n h, π n h b * (M.Vstar n h - M.Qpi π n h b)
            ≤ ∑ b ∈ ({a} : Finset A), π n h b * (M.Vstar n h - M.Qpi π n h b) :=
              sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => hf0 b
          _ = π n h a * (M.Vstar n h - M.Qpi π n h a) := sum_singleton _ _
          _ ≤ M.odds π n h * ((M.T : ℝ) - n) := hstar
          _ ≤ M.odds π n h * (1 + ((M.T : ℝ) - n)) := by
              apply mul_le_mul_of_nonneg_left _ hodds
              linarith
      · -- trust-bound node: split the support into the argmax part and the rest (`⊆ {π⋆(h)}`)
        have hr' : 0 ≤ M.resid π n h := not_lt.1 hr
        have htb : M.TB π n h := by
          unfold TB
          unfold resid at hr'
          linarith
        rw [← sum_filter_add_sum_filter_not (supp π n h) (fun b => M.Qxi π n h b = M.Mx π n h)]
        have hrest : (supp π n h).filter (fun b => ¬ M.Qxi π n h b = M.Mx π n h) ⊆ {a} := by
          intro b hb
          rw [mem_filter, mem_supp] at hb
          rw [mem_singleton]
          rcases hfp.supp_of_nonneg hnt hr' hb.1 with h1 | h1
          · exact absurd h1 hb.2
          · exact h1
        have hrest_le : ∑ b ∈ (supp π n h).filter (fun b => ¬ M.Qxi π n h b = M.Mx π n h),
            π n h b * (M.Vstar n h - M.Qpi π n h b) ≤ M.odds π n h * ((M.T : ℝ) - n) :=
          calc ∑ b ∈ (supp π n h).filter (fun b => ¬ M.Qxi π n h b = M.Mx π n h),
                π n h b * (M.Vstar n h - M.Qpi π n h b)
              ≤ ∑ b ∈ ({a} : Finset A), π n h b * (M.Vstar n h - M.Qpi π n h b) :=
                sum_le_sum_of_subset_of_nonneg hrest fun b _ _ => hf0 b
            _ = π n h a * (M.Vstar n h - M.Qpi π n h a) := sum_singleton _ _
            _ ≤ M.odds π n h * ((M.T : ℝ) - n) := hstar
        have hmain := M.argmax_part_le hπ hnt hxi hw htb
        linarith

/-- **Theorem C (horizon form).** For every model, every floored fixed point `π`, every decision node `h`
with `0 < w_h`: `V^*_ξ(h) - V^π_ξ(h) ≤ O_h (1 + T)`. No trust-bound hypothesis, no `|A|`, no tie clause; the
hypotheses are the model's own predicates. Scope: finite shadow of rOSI ([[sequential-self-game]] §7).
Source: [[sequential-self-game]] §4.1 (Theorem C, horizon form); [[uea-inventory]] 011
Kind: C
Fidelity: exact against §4.1's horizon form; variant: finite shadow relative to Cole's rOSI claim
Hyps: (a) -/
theorem theoremC (hfp : M.IsFlooredFP π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hw : 0 < M.wS π n h) : M.gap π n h ≤ M.odds π n h * (1 + M.T) := by
  have h1 := M.theoremC_depth hfp n h hnt hw
  have hodds := M.odds_nonneg hfp.1 hnt hw
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  calc M.gap π n h ≤ M.odds π n h * (1 + ((M.T : ℝ) - n)) := h1
    _ ≤ M.odds π n h * (1 + M.T) := by
        apply mul_le_mul_of_nonneg_left _ hodds
        linarith

end Model

end Cleanroom.Uea.UeaColeShadow
