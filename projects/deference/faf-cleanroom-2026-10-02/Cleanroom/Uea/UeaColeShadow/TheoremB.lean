import Cleanroom.Uea.UeaColeShadow.Facts

/-!
# Theorem B: the one-line bound at any plain fixed point

At any plain fixed point `π` (pure or mixed) and any decision node `h` with `0 < w_h` at which the trust
bound `(TB_h) : M(h) ≥ w_h V^*_ξ(h)` holds,
`V^*_ξ(h) - V^π_ξ(h) ≤ (1-w_h)[(1-p̄_h) V^*_ξ(h) + p̄_h / w_h] ≤ (1-w_h)/w_h = O_h`,
with no `|A|` factor and no tie clause; the refinement via Lemma A′,
`gap ≤ (1-w_h) V^*_ξ(h) [1 + p̄_h O_h]`; and the corollary `w_h > 1-δ' ⇒ gap < δ'/(1-δ')`.
The per-action inequality is a named lemma (`per_action_bound`) reused by Theorem C.

Source: [[sequential-self-game]] §3. Scope: finite shadow of rOSI — finite horizon and hypothesis
class, fixed points for oracles, continuous extension at `ξ`-null nodes ([[sequential-self-game]] §7).
-/

namespace Cleanroom.Uea.UeaColeShadow

open Finset

namespace Model

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι)
  {π : Policy A E}

/-- `(1 - w_h) π̄(a|h) = ξ_{-S}(ha) / ξ(h)` when `ξ(h) ≠ 0` (both sides vanish when `ξ_{-S}(h) = 0`). -/
theorem one_sub_wS_mul_pibar {n : ℕ} {h : Hist A E n} (hx : M.xi π n h ≠ 0) (a : A) :
    (1 - M.wS π n h) * M.pibar n h a = M.xinsA n h a / M.xi π n h := by
  rw [M.one_sub_wS hx]
  unfold pibar
  by_cases hs : M.xins n h = 0
  · rw [hs, M.xinsA_eq_zero_of_xins_eq_zero hs]
    simp
  · field_simp

/-- **The per-action inequality** behind Theorems B and C. At a decision node with `ξ(h) ≠ 0` and
`0 < w_h`, for any action `a` whose EDT value clears the trust threshold, `Q_ξ(h,a) ≥ w_h V^*_ξ(h)`, and any
bound `c` on the non-self continuation in the unnormalised form `∑_i w_i ν_i(ha) Q^{ν_i}(h,a) ≤ ξ_{-S}(ha) c`:
`π(a|h) (V^*_ξ(h) - Q^π_ξ(h,a)) ≤ (1-w_h) [π(a|h) V^*_ξ(h) + π̄(a|h) (c/w_h - V^*_ξ(h))]`.
With `c = 1` this is the note's per-action inequality; with `c = V^*_ξ(h)` (Lemma A′) the refined one.
Source: [[sequential-self-game]] §3 (proof of Theorem B), §4.1 (Step 3)
Kind: P
Fidelity: exact (stated for any action clearing the threshold, not only supported ones)
Hyps: (a) -/
theorem per_action_bound (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hx : M.xi π n h ≠ 0) (hw : 0 < M.wS π n h) {a : A} {c : ℝ}
    (hc : ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a ≤ M.xinsA n h a * c)
    (hQ : M.wS π n h * M.Vstar n h ≤ M.Qxi π n h a) :
    π n h a * (M.Vstar n h - M.Qpi π n h a) ≤
      (1 - M.wS π n h) * (π n h a * M.Vstar n h + M.pibar n h a * (c / M.wS π n h - M.Vstar n h)) := by
  have hxpos : 0 < M.xi π n h := lt_of_le_of_ne (M.xi_nonneg hπ hnt) (Ne.symm hx)
  have e1 : M.xia π n h a * M.Qxi π n h a = M.wS π n h * π n h a * M.Qpi π n h a +
      (∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a) / M.xi π n h := by
    have hxa : M.xia π n h a * M.Qxi π n h a = (M.xiA π n h a * M.Qxi π n h a) / M.xi π n h := by
      unfold xia
      rw [if_neg hx]
      ring
    rw [hxa, M.xiA_mul_Qxi hπ, wS_of_xi_ne_zero M hx]
    field_simp
  have e2 := M.one_sub_wS_mul_pibar (π := π) hx a
  have e3 := M.xia_eq_wS hπ hnt hx a
  have e4 : (∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a) / M.xi π n h ≤
      (1 - M.wS π n h) * M.pibar n h a * c := by
    rw [e2, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hc hxpos.le
  have e5 : M.xia π n h a * (M.wS π n h * M.Vstar n h) ≤ M.xia π n h a * M.Qxi π n h a :=
    mul_le_mul_of_nonneg_left hQ (M.xia_nonneg hπ hnt a)
  have E : (M.wS π n h * π n h a + (1 - M.wS π n h) * M.pibar n h a) * (M.wS π n h * M.Vstar n h) ≤
      M.wS π n h * π n h a * M.Qpi π n h a + (1 - M.wS π n h) * M.pibar n h a * c := by
    rw [← e3]
    linarith [e1, e4, e5]
  have hc' : M.wS π n h * (c / M.wS π n h) = c := mul_div_cancel₀ c hw.ne'
  refine le_of_mul_le_mul_left ?_ hw
  have hfin : M.wS π n h * ((1 - M.wS π n h) *
      (π n h a * M.Vstar n h + M.pibar n h a * (c / M.wS π n h - M.Vstar n h))) =
      (1 - M.wS π n h) * (M.wS π n h * π n h a * M.Vstar n h +
        M.pibar n h a * (M.wS π n h * (c / M.wS π n h) - M.wS π n h * M.Vstar n h)) := by ring
  rw [hfin, hc']
  nlinarith [E]

/-- At a `ξ_{-S}`-null decision node, a plain fixed point satisfying the trust bound has no loss: the
support maximises `Q^π_ξ(h,·)` and that maximum is `≥ V^*_ξ(h)`.
Source: [[sequential-self-game]] §3 (the case `ξ(h) = 0`)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem gap_le_zero_of_xins_eq_zero (hfp : M.IsPlainFP π) {n : ℕ} {h : Hist A E n}
    (hnt : M.nonterminal n h) (hx : M.xins n h = 0) (htb : M.TB π n h) : M.gap π n h ≤ 0 := by
  have hπ := hfp.1
  have hw : M.wS π n h = 1 := (M.wS_eq_one_iff hπ hnt).2 hx
  unfold TB at htb
  rw [hw, one_mul] at htb
  unfold gap
  rw [M.Vpi_eq_sum_supp hπ hnt]
  have hQ : ∀ a ∈ supp π n h, M.Qpi π n h a = M.Mx π n h := by
    intro a ha
    rw [mem_supp] at ha
    rw [← M.Qxi_eq_Qpi_of_xins_eq_zero hx a]
    exact hfp.2 n h hnt a ha
  rw [sum_congr rfl fun a ha => by rw [hQ a ha], ← sum_mul, M.sum_supp_eq_one hπ hnt, one_mul]
  linarith

/-- **Theorem B** (plain agent, pure or mixed). Every model, every plain fixed point `π`, every decision
node `h` with `0 < w_h` at which `(TB_h)` holds:
`V^*_ξ(h) - V^π_ξ(h) ≤ (1-w_h)[(1-p̄_h) V^*_ξ(h) + p̄_h/w_h] ≤ (1-w_h)/w_h = O_h`.
No `|A|` factor, no tie clause. The only hypotheses are the model's own predicates (`IsPlainFP`, `0 < w_h`,
`TB`); the trust-bound identity is proved, not assumed. `0 < w_h` is load-bearing: at `w_h = 0` the
value `O_h` is junk. Scope: finite shadow of rOSI — finite horizon and hypothesis class, fixed points for
oracles, continuous extension at `ξ`-null nodes ([[sequential-self-game]] §7).
Source: [[sequential-self-game]] §3 (Theorem B); [[uea-inventory]] 005
Kind: P
Fidelity: exact against §3; variant: finite shadow relative to Cole's rOSI Theorem 1
Hyps: (a) -/
theorem theoremB (hfp : M.IsPlainFP π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hw : 0 < M.wS π n h) (htb : M.TB π n h) :
    M.gap π n h ≤ (1 - M.wS π n h) * ((1 - M.pbar π n h) * M.Vstar n h + M.pbar π n h / M.wS π n h) ∧
    (1 - M.wS π n h) * ((1 - M.pbar π n h) * M.Vstar n h + M.pbar π n h / M.wS π n h) ≤ M.odds π n h := by
  have hπ := hfp.1
  have hw1 := M.wS_le_one hπ hnt
  have hpb0 := M.pbar_nonneg (π := π) n h
  have hpb1 := M.pbar_le_one (π := π) n h
  have hV0 := M.Vstar_nonneg n h
  have hV1 := M.Vstar_le_one n h
  -- the second inequality holds regardless of the fixed point
  have second : (1 - M.wS π n h) * ((1 - M.pbar π n h) * M.Vstar n h + M.pbar π n h / M.wS π n h) ≤
      M.odds π n h := by
    unfold odds
    have h1 : (1 - M.pbar π n h) * M.Vstar n h + M.pbar π n h / M.wS π n h ≤ 1 / M.wS π n h := by
      have hinv : 1 ≤ 1 / M.wS π n h := by rw [le_div_iff₀ hw]; linarith
      have : (1 - M.pbar π n h) * M.Vstar n h ≤ (1 - M.pbar π n h) * (1 / M.wS π n h) :=
        mul_le_mul_of_nonneg_left (le_trans hV1 hinv) (by linarith)
      have h2 : (1 - M.pbar π n h) * (1 / M.wS π n h) + M.pbar π n h / M.wS π n h = 1 / M.wS π n h := by
        field_simp
        ring
      linarith
    calc (1 - M.wS π n h) * ((1 - M.pbar π n h) * M.Vstar n h + M.pbar π n h / M.wS π n h)
        ≤ (1 - M.wS π n h) * (1 / M.wS π n h) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = (1 - M.wS π n h) / M.wS π n h := by ring
  refine ⟨?_, second⟩
  by_cases hx : M.xi π n h = 0
  · -- `ξ(h) = 0`: `w_h = 1`, `Q_ξ = Q^π`, the gap is `≤ 0`
    have hxs := M.xins_eq_zero_of_xi_eq_zero hπ hnt hx
    have hgap := M.gap_le_zero_of_xins_eq_zero hfp hnt hxs htb
    have hw1' : M.wS π n h = 1 := (M.wS_eq_one_iff hπ hnt).2 hxs
    rw [hw1']
    simp only [sub_self, zero_mul]
    exact hgap
  · -- `ξ(h) > 0`: sum the per-action inequality over the support
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
    rw [hsum]
    calc ∑ a ∈ supp π n h, π n h a * (M.Vstar n h - M.Qpi π n h a)
        ≤ ∑ a ∈ supp π n h, (1 - M.wS π n h) *
            (π n h a * M.Vstar n h + M.pibar n h a * (1 / M.wS π n h - M.Vstar n h)) :=
          sum_le_sum hper
      _ = (1 - M.wS π n h) * ((∑ a ∈ supp π n h, π n h a) * M.Vstar n h +
            (∑ a ∈ supp π n h, M.pibar n h a) * (1 / M.wS π n h - M.Vstar n h)) := by
          rw [← mul_sum, sum_add_distrib, sum_mul, sum_mul]
      _ = (1 - M.wS π n h) * ((1 - M.pbar π n h) * M.Vstar n h + M.pbar π n h / M.wS π n h) := by
          rw [M.sum_supp_eq_one hπ hnt]
          unfold pbar
          ring

/-- **Theorem B, `O_h` form**: `V^*_ξ(h) - V^π_ξ(h) ≤ O_h` at every trust-bound node with `0 < w_h` of every
plain fixed point.
Source: [[sequential-self-game]] §3 (Theorem B)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem theoremB_odds (hfp : M.IsPlainFP π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hw : 0 < M.wS π n h) (htb : M.TB π n h) : M.gap π n h ≤ M.odds π n h :=
  le_trans (M.theoremB hfp hnt hw htb).1 (M.theoremB hfp hnt hw htb).2

/-- **Theorem B, refinement via Lemma A′**: `gap ≤ (1-w_h) V^*_ξ(h) [1 + p̄_h O_h]` (uses `Q̄ ≤ V^*_ξ(h)`
instead of `Q̄ ≤ 1`).
Source: [[sequential-self-game]] §3 (Remarks, "Refinement via Lemma A′")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem theoremB_refined (hfp : M.IsPlainFP π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hw : 0 < M.wS π n h) (htb : M.TB π n h) :
    M.gap π n h ≤ (1 - M.wS π n h) * M.Vstar n h * (1 + M.pbar π n h * M.odds π n h) := by
  have hπ := hfp.1
  by_cases hx : M.xi π n h = 0
  · have hxs := M.xins_eq_zero_of_xi_eq_zero hπ hnt hx
    have hgap := M.gap_le_zero_of_xins_eq_zero hfp hnt hxs htb
    have hw1' : M.wS π n h = 1 := (M.wS_eq_one_iff hπ hnt).2 hxs
    rw [hw1']
    simp only [sub_self, zero_mul]
    exact hgap
  · have hper : ∀ a ∈ supp π n h, π n h a * (M.Vstar n h - M.Qpi π n h a) ≤
        (1 - M.wS π n h) * (π n h a * M.Vstar n h +
          M.pibar n h a * (M.Vstar n h / M.wS π n h - M.Vstar n h)) := by
      intro a ha
      rw [mem_supp] at ha
      have hQ : M.wS π n h * M.Vstar n h ≤ M.Qxi π n h a := by
        rw [hfp.2 n h hnt a ha]
        exact htb
      exact M.per_action_bound hπ hnt hx hw (M.sum_nu_Qnu_le_xinsA_mul_Vstar hnt a) hQ
    have hsum : M.gap π n h = ∑ a ∈ supp π n h, π n h a * (M.Vstar n h - M.Qpi π n h a) := by
      unfold gap
      rw [M.Vpi_eq_sum_supp hπ hnt]
      simp_rw [mul_sub]
      rw [sum_sub_distrib, ← sum_mul, M.sum_supp_eq_one hπ hnt, one_mul]
    rw [hsum]
    calc ∑ a ∈ supp π n h, π n h a * (M.Vstar n h - M.Qpi π n h a)
        ≤ ∑ a ∈ supp π n h, (1 - M.wS π n h) * (π n h a * M.Vstar n h +
            M.pibar n h a * (M.Vstar n h / M.wS π n h - M.Vstar n h)) := sum_le_sum hper
      _ = (1 - M.wS π n h) * ((∑ a ∈ supp π n h, π n h a) * M.Vstar n h +
            (∑ a ∈ supp π n h, M.pibar n h a) * (M.Vstar n h / M.wS π n h - M.Vstar n h)) := by
          rw [← mul_sum, sum_add_distrib, sum_mul, sum_mul]
      _ = (1 - M.wS π n h) * M.Vstar n h * (1 + M.pbar π n h * M.odds π n h) := by
          rw [M.sum_supp_eq_one hπ hnt]
          unfold pbar odds
          field_simp

/-- **Theorem B, corollary**: `w_h > 1 - δ'` (for `δ' < 1`) implies `V^π_ξ(h) > V^*_ξ(h) - δ'/(1-δ')` — the
sibling's `δ/(1-δ)` with the posterior in place of the prior.
Source: [[sequential-self-game]] §3 ("In particular")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem theoremB_corollary (hfp : M.IsPlainFP π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (htb : M.TB π n h) {δ' : ℝ} (hδ' : δ' < 1) (hw : 1 - δ' < M.wS π n h) :
    M.gap π n h < δ' / (1 - δ') := by
  have hw0 : 0 < M.wS π n h := by linarith
  have hB := M.theoremB_odds hfp hnt hw0 htb
  have hodds : M.odds π n h < δ' / (1 - δ') := by
    unfold odds
    rw [div_lt_iff₀ hw0, div_mul_eq_mul_div, lt_div_iff₀ (by linarith : (0:ℝ) < 1 - δ')]
    nlinarith
  exact lt_of_le_of_lt hB hodds

end Model

end Cleanroom.Uea.UeaColeShadow
