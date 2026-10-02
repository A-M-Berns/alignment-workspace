import Cleanroom.Uea.UeaColeShadow.Instances

/-!
# Pure fixed points at `T = 2`

At horizon `2` the depth-1 decisions are policy-independent and optimal, so under a pure root action `x` (with
`π⋆` at depth 1) every other root action `y` has `Q_ξ(ε,y) = g(y)`, where the **score** `g(y)` is the non-self
continuation `Q^{π̄}_ξ(ε,y)` if some hypothesis plays `y` and the optimal value `Q^*_ξ(ε,y)` otherwise (the
continuous extension; this fallback is the correction of findings F3 to the note's `Q_ξ(ε,y) = Q^{π̄}_ξ(ε,y)`),
while `Q_ξ(ε,x) ≥ g(x)` (Lemma A′). Hence a root action maximising `g` is a pure plain fixed point; and either it or
`π⋆(ε)` is a pure floored fixed point.

Source: [[sequential-self-game]] §4.5 ("Pure fixed points: exist at `T = 2`"); [[uea-inventory]] 013.
-/

namespace Cleanroom.Uea.UeaColeShadow

open Finset

namespace Model

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] [DecidableEq A] (M : Model A E ι)

/-- The root history (all depth-`0` histories are equal). -/
def root0 : Hist A E 0 := fun i => Fin.elim0 i

theorem eq_root0 (h : Hist A E 0) : h = root0 := funext fun i => Fin.elim0 i

/-- The pure policy: `x` at the root, `π⋆` at every deeper node. -/
noncomputable def pure2 (x : A) : Policy A E := fun n h a =>
  if n = 0 then (if a = x then 1 else 0) else (if a = M.piStar n h then 1 else 0)

theorem pure2_isPolicy (x : A) : M.IsPolicy (M.pure2 x) := by
  intro n h _
  refine ⟨fun a => ?_, ?_⟩
  · unfold pure2; split_ifs <;> norm_num
  · unfold pure2; split_ifs <;> simp

theorem pure2_isPure (x : A) : M.IsPure (M.pure2 x) := by
  intro n h _
  by_cases hn : n = 0
  · exact ⟨x, by simp [pure2, hn]⟩
  · exact ⟨M.piStar n h, by simp [pure2, hn]⟩

theorem pure2_root (x : A) (h : Hist A E 0) (a : A) : M.pure2 x 0 h a = if a = x then 1 else 0 := by
  simp [pure2]

theorem pure2_succ (x : A) {n : ℕ} (h : Hist A E (n + 1)) (a : A) :
    M.pure2 x (n + 1) h a = if a = M.piStar (n + 1) h then 1 else 0 := by
  simp [pure2]

/-- The score of a root action: the non-self continuation where some hypothesis plays it, the optimum otherwise. -/
noncomputable def score (a : A) : ℝ := if M.xinsA 0 root0 a = 0 then M.Qstar 0 root0 a else M.Qbar 0 root0 a

theorem xiA_pure2_root (x : A) (b : A) :
    M.xiA (M.pure2 x) 0 root0 b = (1 - M.δ) * (if b = x then 1 else 0) + M.xinsA 0 root0 b := by
  rw [xiA_eq, xiS_zero, mul_one, pure2_root]

/-- The root's self-posterior is the prior `1 - δ` under every policy. -/
theorem wS_root0 (π : Policy A E) : M.wS π 0 root0 = 1 - M.δ := by
  have hxins : M.xins 0 root0 = M.δ := by simp [xins, M.w_sum]
  have hx : M.xi π 0 root0 = 1 := by unfold xi; rw [hxins, xiS_zero]; ring
  rw [wS_of_xi_ne_zero M (by rw [hx]; exact one_ne_zero), hx, xiS_zero]
  ring

theorem xinsA_root0_le (a : A) : M.xinsA 0 root0 a ≤ M.δ := by
  have hxins : M.xins 0 root0 = M.δ := by simp [xins, M.w_sum]
  rw [← hxins]; exact M.xinsA_le_xins 0 root0 a

/-- A maximiser of the score. -/
noncomputable def xmax : A := Classical.choose (Finset.exists_mem_eq_sup' (univ_nonempty (α := A)) M.score)

theorem score_le_xmax (b : A) : M.score b ≤ M.score M.xmax := by
  have := (Classical.choose_spec (Finset.exists_mem_eq_sup' (univ_nonempty (α := A)) M.score)).2
  unfold xmax
  rw [← this]
  exact le_sup' _ (mem_univ b)

theorem pure2_root_cond (x : A) (hx : M.Mx (M.pure2 x) 0 root0 = M.Qxi (M.pure2 x) 0 root0 x) :
    ∀ a, 0 < M.pure2 x 0 root0 a → M.Qxi (M.pure2 x) 0 root0 a = M.Mx (M.pure2 x) 0 root0 := by
  intro a ha
  rw [pure2_root] at ha
  by_cases hax : a = x
  · rw [hax, hx]
  · rw [if_neg hax] at ha; exact absurd ha (lt_irrefl 0)

section T2
variable (hT : M.T = 2)
include hT

theorem not_nt_two (h : Hist A E 2) : ¬ M.nonterminal 2 h := M.not_nonterminal_of_le (by omega) h

theorem not_nt_ge_two {n : ℕ} (hn : 2 ≤ n) (h : Hist A E n) : ¬ M.nonterminal n h :=
  M.not_nonterminal_of_le (by omega) h

/-- At depth `1` the EDT and policy action values are the optimal ones (children are terminal). -/
theorem Qxi_one_eq_Qstar (π : Policy A E) (h : Hist A E 1) (a : A) : M.Qxi π 1 h a = M.Qstar 1 h a := by
  rw [M.Qxi_eq_of_children_terminal h a (fun e => M.not_nt_two hT _),
    M.Qstar_eq_of_children_terminal h a (fun e => M.not_nt_two hT _)]

theorem Qpi_one_eq_Qstar (π : Policy A E) (h : Hist A E 1) (a : A) : M.Qpi π 1 h a = M.Qstar 1 h a := by
  rw [M.Qpi_eq_of_children_terminal h a (fun e => M.not_nt_two hT _),
    M.Qstar_eq_of_children_terminal h a (fun e => M.not_nt_two hT _)]

theorem Mx_one (π : Policy A E) {h : Hist A E 1} (hnt : M.nonterminal 1 h) : M.Mx π 1 h = M.Vstar 1 h := by
  rw [M.Vstar_eq hnt]
  unfold Mx
  exact congrArg _ (funext (M.Qxi_one_eq_Qstar hT π h))

/-- The depth-`1` value of the pure policy is optimal. -/
theorem Vpi_pure2_one (x : A) (h : Hist A E 1) : M.Vpi (M.pure2 x) 1 h = M.Vstar 1 h := by
  by_cases hnt : M.nonterminal 1 h
  · rw [M.Vpi_eq hnt, M.Vstar_eq_Qstar_piStar hnt]
    rw [Finset.sum_eq_single (M.piStar 1 h) (fun a _ ha => by rw [pure2_succ, if_neg ha, zero_mul])
      (fun h' => absurd (Finset.mem_univ _) h'), pure2_succ, if_pos rfl, one_mul, M.Qpi_one_eq_Qstar hT]
  · rw [M.Vpi_of_not_nonterminal hnt, M.Vstar_of_not_nonterminal hnt]

/-- Under the pure policy the root policy values are the optimal ones. -/
theorem Qpi_pure2_root (x : A) (b : A) : M.Qpi (M.pure2 x) 0 root0 b = M.Qstar 0 root0 b := by
  rw [Qpi_eq_sum, Qstar_eq_sum]
  exact sum_congr rfl fun e _ => by rw [M.Vpi_pure2_one hT x]

/-- The depth-`1` fixed-point conditions (plain and floored) hold for the pure policy. -/
theorem pure2_depth_one (x : A) {h : Hist A E 1} (hnt : M.nonterminal 1 h) :
    (∀ a, 0 < M.pure2 x 1 h a → M.Qxi (M.pure2 x) 1 h a = M.Mx (M.pure2 x) 1 h) ∧
    (M.resid (M.pure2 x) 1 h < 0 → ∀ a, 0 < M.pure2 x 1 h a → a = M.piStar 1 h) ∧
    (0 < M.resid (M.pure2 x) 1 h → ∀ a, 0 < M.pure2 x 1 h a → M.Qxi (M.pure2 x) 1 h a = M.Mx (M.pure2 x) 1 h) ∧
    (M.resid (M.pure2 x) 1 h = 0 → ∀ a, 0 < M.pure2 x 1 h a →
      M.Qxi (M.pure2 x) 1 h a = M.Mx (M.pure2 x) 1 h ∨ a = M.piStar 1 h) := by
  have hsupp : ∀ a, 0 < M.pure2 x 1 h a → a = M.piStar 1 h := by
    intro a ha
    rw [pure2_succ] at ha
    by_contra hne
    rw [if_neg hne] at ha
    exact lt_irrefl _ ha
  have hQ : M.Qxi (M.pure2 x) 1 h (M.piStar 1 h) = M.Mx (M.pure2 x) 1 h := by
    rw [M.Mx_one hT _ hnt, M.Qxi_one_eq_Qstar hT, M.Vstar_eq_Qstar_piStar hnt]
  refine ⟨fun a ha => by rw [hsupp a ha]; exact hQ, fun _ a ha => hsupp a ha, fun _ a ha => by rw [hsupp a ha]; exact hQ,
    fun _ a ha => Or.inr (hsupp a ha)⟩

/-- **Off the root action**: `Q_ξ(ε, b) = g(b)` for `b ≠ x` under the pure policy `x`.
Source: [[sequential-self-game]] §4.5 (corrected, findings F3)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Qxi_pure2_root_ne (x : A) {b : A} (hb : b ≠ x) : M.Qxi (M.pure2 x) 0 root0 b = M.score b := by
  have hπ := M.pure2_isPolicy x
  have hA : M.xiA (M.pure2 x) 0 root0 b = M.xinsA 0 root0 b := by
    rw [xiA_pure2_root, if_neg hb]; ring
  unfold score
  split_ifs with h0
  · -- every child is `ξ_{-S}`-null: `Q_ξ = Q^π = Q^*`
    rw [← M.Qpi_pure2_root hT x b, Qxi_eq_sum, Qpi_eq_sum]
    refine sum_congr rfl fun e _ => ?_
    rw [M.Vxi_eq_Vpi_of_xins_eq_zero _ _ (by rw [xins_ext, h0, zero_mul])]
  · have hA' : M.xiA (M.pure2 x) 0 root0 b ≠ 0 := by rw [hA]; exact h0
    rw [M.Qxi_eq_wA hπ hA', M.wA_of_xiA_ne_zero hA', M.Qmix_eq_Qbar h0, xiS_zero, pure2_root, if_neg hb]
    simp

/-- **On the root action**: `Q_ξ(ε, x) ≥ g(x)` (Lemma A′).
Source: [[sequential-self-game]] §4.5
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem score_le_Qxi_pure2_root (x : A) : M.score x ≤ M.Qxi (M.pure2 x) 0 root0 x := by
  have hπ := M.pure2_isPolicy x
  have hδ : (0:ℝ) < 1 - M.δ := by linarith [M.δ_lt_one]
  have hA : M.xiA (M.pure2 x) 0 root0 x = (1 - M.δ) + M.xinsA 0 root0 x := by
    rw [xiA_pure2_root, if_pos rfl, mul_one]
  have hA' : M.xiA (M.pure2 x) 0 root0 x ≠ 0 := by
    rw [hA]; have := M.xinsA_nonneg 0 root0 x; positivity
  rw [M.Qxi_eq_wA hπ hA', M.Qpi_pure2_root hT]
  unfold score
  split_ifs with h0
  · have hw : M.wA (M.pure2 x) 0 root0 x = 1 := by
      rw [M.wA_of_xiA_ne_zero hA', hA, xiS_zero, pure2_root, if_pos rfl, h0, add_zero]
      field_simp
    rw [hw]; simp
  · rw [M.Qmix_eq_Qbar h0]
    have hxA0 := M.xinsA_nonneg 0 root0 x
    have hw : M.wA (M.pure2 x) 0 root0 x = (1 - M.δ) / ((1 - M.δ) + M.xinsA 0 root0 x) := by
      rw [M.wA_of_xiA_ne_zero hA', hA, xiS_zero, pure2_root, if_pos rfl]; ring
    have hw0 : 0 ≤ M.wA (M.pure2 x) 0 root0 x := by rw [hw]; positivity
    have hw1 : M.wA (M.pure2 x) 0 root0 x ≤ 1 := by rw [hw, div_le_one (by positivity)]; linarith
    have hQ := M.Qbar_le_Qstar 0 root0 x
    nlinarith

theorem Qxi_le_Qxi_xmax (b : A) : M.Qxi (M.pure2 M.xmax) 0 root0 b ≤ M.Qxi (M.pure2 M.xmax) 0 root0 M.xmax := by
  by_cases hb : b = M.xmax
  · rw [hb]
  · rw [M.Qxi_pure2_root_ne hT _ hb]
    exact le_trans (M.score_le_xmax b) (M.score_le_Qxi_pure2_root hT _)

theorem Mx_pure2_xmax : M.Mx (M.pure2 M.xmax) 0 root0 = M.Qxi (M.pure2 M.xmax) 0 root0 M.xmax :=
  le_antisymm (M.Mx_le_iff.2 (M.Qxi_le_Qxi_xmax hT)) (M.Qxi_le_Mx _ _ _)

theorem isPlainFP_pure2 (x : A) (hx : M.Mx (M.pure2 x) 0 root0 = M.Qxi (M.pure2 x) 0 root0 x) :
    M.IsPlainFP (M.pure2 x) := by
  refine ⟨M.pure2_isPolicy x, fun n h hnt => ?_⟩
  match n with
  | 0 => rw [eq_root0 h]; exact M.pure2_root_cond x hx
  | 1 => exact (M.pure2_depth_one hT x hnt).1
  | n + 2 => exact absurd hnt (M.not_nt_ge_two hT (by omega) h)

theorem isFlooredFP_pure2 (x : A) (hx : M.Mx (M.pure2 x) 0 root0 = M.Qxi (M.pure2 x) 0 root0 x)
    (hres : 0 ≤ M.resid (M.pure2 x) 0 root0) : M.IsFlooredFP (M.pure2 x) := by
  refine ⟨M.pure2_isPolicy x, fun n h hnt => ?_⟩
  match n with
  | 0 =>
    rw [eq_root0 h]
    exact ⟨fun hneg => absurd hres (not_le.2 hneg), fun _ => M.pure2_root_cond x hx,
      fun _ a ha => Or.inl (M.pure2_root_cond x hx a ha)⟩
  | 1 => exact (M.pure2_depth_one hT x hnt).2
  | n + 2 => exact absurd hnt (M.not_nt_ge_two hT (by omega) h)

/-- **Pure plain fixed points exist at `T = 2`**: the root action maximising the score `g` (with `π⋆` at depth
`1`) is a pure plain fixed point.
Source: [[sequential-self-game]] §4.5 ("Pure fixed points: exist at `T = 2`"); [[uea-inventory]] 013
Kind: P
Fidelity: exact (with the corrected score at residual-null root actions, findings F3)
Hyps: (a) -/
theorem exists_pure_isPlainFP : ∃ π, M.IsPure π ∧ M.IsPlainFP π :=
  ⟨M.pure2 M.xmax, M.pure2_isPure _, M.isPlainFP_pure2 hT _ (M.Mx_pure2_xmax hT)⟩

/-- **Pure floored fixed points exist at `T = 2`**: either the score maximiser or `π⋆(ε)` at the root (when the
former violates the trust bound, every score is below `(1-δ) V^*` and `π⋆(ε)` clears it: `w_{επ⋆} ≥ 1 - δ`).
Source: [[sequential-self-game]] §4.5
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem exists_pure_isFlooredFP : ∃ π, M.IsPure π ∧ M.IsFlooredFP π := by
  by_cases hres : 0 ≤ M.resid (M.pure2 M.xmax) 0 root0
  · exact ⟨M.pure2 M.xmax, M.pure2_isPure _, M.isFlooredFP_pure2 hT _ (M.Mx_pure2_xmax hT) hres⟩
  push_neg at hres
  by_cases hnt : M.nonterminal 0 root0
  · set a := M.piStar 0 root0 with ha_def
    have hδ : (0:ℝ) < 1 - M.δ := by linarith [M.δ_lt_one]
    have hV0 := M.Vstar_nonneg 0 root0
    -- every score is below `(1-δ) V^*`
    have hscore : ∀ b, M.score b < (1 - M.δ) * M.Vstar 0 root0 := by
      intro b
      unfold resid at hres
      rw [M.wS_root0] at hres
      linarith [M.score_le_xmax b, M.score_le_Qxi_pure2_root hT M.xmax, M.Qxi_le_Mx (π := M.pure2 M.xmax) 0 root0 M.xmax]
    -- under `π⋆` at the root the reset action clears the threshold
    have hπ := M.pure2_isPolicy a
    have hA : M.xiA (M.pure2 a) 0 root0 a = (1 - M.δ) + M.xinsA 0 root0 a := by
      rw [xiA_pure2_root, if_pos rfl, mul_one]
    have hxA0 := M.xinsA_nonneg 0 root0 a
    have hA' : M.xiA (M.pure2 a) 0 root0 a ≠ 0 := by rw [hA]; positivity
    have hw : M.wA (M.pure2 a) 0 root0 a = (1 - M.δ) / ((1 - M.δ) + M.xinsA 0 root0 a) := by
      rw [M.wA_of_xiA_ne_zero hA', hA, xiS_zero, pure2_root, if_pos rfl]; ring
    have hw1 : M.wA (M.pure2 a) 0 root0 a ≤ 1 := by rw [hw, div_le_one (by positivity)]; linarith
    have hwge : 1 - M.δ ≤ M.wA (M.pure2 a) 0 root0 a := by
      rw [hw]
      have hD : (1 - M.δ) + M.xinsA 0 root0 a ≤ 1 := by linarith [M.xinsA_root0_le a]
      calc 1 - M.δ = (1 - M.δ) / 1 := (div_one _).symm
        _ ≤ (1 - M.δ) / ((1 - M.δ) + M.xinsA 0 root0 a) :=
          div_le_div_of_nonneg_left hδ.le (by positivity) hD
    have hQa : (1 - M.δ) * M.Vstar 0 root0 ≤ M.Qxi (M.pure2 a) 0 root0 a := by
      rw [M.Qxi_eq_wA hπ hA', M.Qpi_pure2_root hT, ← M.Vstar_eq_Qstar_piStar hnt]
      have hQm := M.Qmix_nonneg 0 root0 a
      nlinarith
    have hlt : ∀ b, b ≠ a → M.Qxi (M.pure2 a) 0 root0 b < M.Qxi (M.pure2 a) 0 root0 a := by
      intro b hb
      rw [M.Qxi_pure2_root_ne hT a hb]
      exact lt_of_lt_of_le (hscore b) hQa
    have hMx : M.Mx (M.pure2 a) 0 root0 = M.Qxi (M.pure2 a) 0 root0 a := by
      refine le_antisymm (M.Mx_le_iff.2 fun b => ?_) (M.Qxi_le_Mx _ _ _)
      by_cases hb : b = a
      · rw [hb]
      · exact (hlt b hb).le
    refine ⟨M.pure2 a, M.pure2_isPure _, M.isFlooredFP_pure2 hT a hMx ?_⟩
    unfold resid
    rw [hMx, M.wS_root0]
    linarith
  · -- a dead root: there are no decision nodes at all
    refine ⟨M.pure2 M.xmax, M.pure2_isPure _, M.pure2_isPolicy _, fun n h hnt' => ?_⟩
    exfalso
    match n with
    | 0 => exact hnt (by rw [← eq_root0 h]; exact hnt')
    | 1 => exact hnt (by rw [← eq_root0 (Fin.init h)]; exact M.nonterminal_init hnt')
    | n + 2 => exact M.not_nt_ge_two hT (by omega) h hnt'

/-- **Pure fixed points at `T = 2`** (target 9d): plain and floored.
Source: [[sequential-self-game]] §4.5; [[uea-inventory]] 013
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem pure_T2 : (∃ π, M.IsPure π ∧ M.IsPlainFP π) ∧ (∃ π, M.IsPure π ∧ M.IsFlooredFP π) :=
  ⟨M.exists_pure_isPlainFP hT, M.exists_pure_isFlooredFP hT⟩

end T2

end Model

end Cleanroom.Uea.UeaColeShadow
