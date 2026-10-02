import Cleanroom.Uea.UeaColeShadow.Instances
import Cleanroom.Uea.UeaColeShadow.Strict

/-!
# Instance W: the `w_h = 1` corner of Theorem B is inhabited

A two-step model with a decision node the non-self mixture never reaches. Root actions `0` (a leaf, reward `0`)
and `1` (to the node `N`); at `N`, action `0` pays `1` and action `1` pays `0`; one residual hypothesis of weight
`δ = 1/10` that plays `0` surely at every node — so it never reaches `N`. Under the policy `polW` (`1` at the
root, `0` at `N`): `ξ_{-S}(N) = 0`, hence `w_N = 1` and `O_N = 0`; `polW` is a plain fixed point; `TB` holds at
`N` with equality (`1 · V^* = 1 = M`); and `gap(N) = 0 = O_N`. So Theorem B's bound `gap ≤ O_h` is attained with
equality at `w_h = 1`, and the hypothesis `w_h < 1` of `theoremB_strict` / `gap_eq_odds_not_attained` is
necessary rather than an artefact (`gap_eq_odds_attained_at_w_one`). The root has `0 < w_root = 9/10 < 1`, so the
model is not the degenerate "no residual anywhere" case. Asked for by the round-2 adversarial audit (item 6).

Source: [[uea-cole-shadow-mandate]] target 10; round-2 adversarial audit, item 6.
-/

namespace Cleanroom.Uea.UeaColeShadow

open Finset

namespace InstW

/-- Alive nodes: the root; `N` (after root action `1`). -/
def alive : (n : ℕ) → Hist (Fin 2) Unit n → Bool
  | 0, _ => true
  | 1, h => decide ((h 0).1 = 1)
  | _, _ => false

/-- Rewards on arrival at depth 2: `1` after `1, 0`; `0` otherwise. -/
noncomputable def r : (n : ℕ) → Hist (Fin 2) Unit (n + 1) → ℝ
  | 0, _ => 0
  | 1, h => if (h 0).1 = 1 ∧ (h 1).1 = 0 then 1 else 0
  | _, _ => 0

/-- The residual: action `0` surely, everywhere (so it never enters `N`). -/
noncomputable def νa : Unit → (n : ℕ) → Hist (Fin 2) Unit n → Fin 2 → ℝ
  | _, _, _, a => if a = 0 then 1 else 0

theorem νa_mem (i : Unit) (n : ℕ) (h : Hist (Fin 2) Unit n) : νa i n h ∈ stdSimplex ℝ (Fin 2) := by
  refine ⟨fun a => ?_, ?_⟩
  · simp only [νa]; split_ifs <;> norm_num
  · simp [νa]

theorem r_nonneg (n : ℕ) (h : Hist (Fin 2) Unit (n + 1)) : 0 ≤ r n h := by
  match n with
  | 0 => simp [r]
  | 1 => simp only [r]; split_ifs <;> norm_num
  | n + 2 => simp [r]

theorem alive_init (n : ℕ) (h : Hist (Fin 2) Unit (n + 1)) (hh : alive (n + 1) h = true) :
    alive n (Fin.init h) = true := by
  match n with
  | 0 => rfl
  | n + 1 => simp [alive] at hh

theorem norm (n : ℕ) (hn : n ≤ 2) (h : Hist (Fin 2) Unit n) : pathReturnOf 1 r n h ≤ 1 := by
  match n with
  | 0 => simp
  | 1 => simp [pathReturnOf, r]
  | 2 =>
    simp only [pathReturnOf, r]
    split_ifs <;> norm_num
  | n + 3 => omega

/-- **Instance W** as a `Model`: `T = 2`, `γ = 1`, `δ = 1/10`; the residual never enters `N`.
Source: round-2 adversarial audit, item 6 (the `w_h = 1` corner)
Kind: D
Fidelity: n/a (a witness instance, not a source object)
Hyps: n/a -/
noncomputable def model : Model (Fin 2) Unit Unit where
  T := 2
  alive := alive
  alive_init := alive_init
  r := r
  r_nonneg := r_nonneg
  γ := 1
  γ_pos := one_pos
  γ_le_one := le_rfl
  norm := norm
  νa := νa
  νe := fun _ _ _ _ _ => 1
  νa_mem := νa_mem
  νe_mem := fun _ _ _ _ => ⟨fun _ => zero_le_one, by simp⟩
  w := fun _ => 1 / 10
  w_nonneg := fun _ => by norm_num
  δ := 1 / 10
  w_sum := by simp
  δ_pos := by norm_num
  δ_lt_one := by norm_num

def root : Hist (Fin 2) Unit 0 := Fin.elim0
/-- The node after root action `1`: the one the residual never reaches. -/
def N : Hist (Fin 2) Unit 1 := ext root 1 ()

@[simp] theorem model_T : model.T = 2 := rfl
@[simp] theorem model_alive : model.alive = alive := rfl
@[simp] theorem model_r : model.r = r := rfl
@[simp] theorem model_γ : model.γ = 1 := rfl
@[simp] theorem model_νa : model.νa = νa := rfl
@[simp] theorem model_νe (i : Unit) (n : ℕ) (h : Hist (Fin 2) Unit n) (a : Fin 2) (e : Unit) :
    model.νe i n h a e = 1 := rfl
@[simp] theorem model_w (i : Unit) : model.w i = 1 / 10 := rfl
@[simp] theorem model_δ : model.δ = 1 / 10 := rfl

theorem nt_root : model.nonterminal 0 root := ⟨by simp, rfl⟩
theorem nt_N : model.nonterminal 1 N := ⟨by simp, by simp [alive, N]⟩
theorem not_nt_leaf : ¬ model.nonterminal 1 (ext root 0 ()) := fun h => by
  have := h.2; simp [alive] at this
theorem not_nt_two (h : Hist (Fin 2) Unit 2) : ¬ model.nonterminal 2 h := fun h' => by
  have := h'.1; simp at this
theorem not_nt_ge_two (n : ℕ) (hn : 2 ≤ n) (h : Hist (Fin 2) Unit n) : ¬ model.nonterminal n h :=
  model.not_nonterminal_of_le (by simpa using hn) h

theorem eq_root (h : Hist (Fin 2) Unit 0) : h = root := funext fun i => Fin.elim0 i
theorem eq_N_of_nonterminal (h : Hist (Fin 2) Unit 1) (hnt : model.nonterminal 1 h) : h = N := by
  have h0 : (h 0).1 = 1 := by have := hnt.2; simpa [alive] using this
  funext i
  fin_cases i
  exact Prod.ext h0 (Subsingleton.elim _ _)

theorem xie_eq_one (n : ℕ) (h : Hist (Fin 2) Unit n) (a : Fin 2) (e : Unit) : model.xie n h a e = 1 :=
  model.xie_eq_one_of_unique n h a e

/-- The policy: `1` at the root, `0` at `N` (and at every depth-1 node), `0` below. -/
noncomputable def polW : Policy (Fin 2) Unit := fun n _ a =>
  if n = 0 then (if a = 1 then 1 else 0) else if n = 1 then (if a = 0 then 1 else 0) else 0

theorem polW_isPolicy : model.IsPolicy polW := by
  intro n h hnt
  have hn : n < 2 := hnt.1
  refine ⟨fun a => ?_, ?_⟩
  · unfold polW; split_ifs <;> norm_num
  · unfold polW
    match n with
    | 0 => simp
    | 1 => simp
    | n + 2 => omega

section Values

theorem xins_N : model.xins 1 N = 0 := by simp [Model.xins, N, νa]
theorem xinsA_N_0 : model.xinsA 1 N 0 = 0 := by simp [Model.xinsA, N, νa]
theorem xiS_N : model.xiS polW 1 N = 1 := by simp [N, xie_eq_one, polW]
theorem xi_N : model.xi polW 1 N = 9 / 10 := by
  unfold Model.xi; rw [xins_N, xiS_N, model_δ]; ring
theorem xiA_N_0 : model.xiA polW 1 N 0 = 9 / 10 := by
  rw [Model.xiA_eq, xiS_N, xinsA_N_0, model_δ]; norm_num [polW]
theorem xi_root : model.xi polW 0 root = 1 := by
  unfold Model.xi; simp [Model.xins, model_δ]
theorem wS_root : model.wS polW 0 root = 9 / 10 := by
  rw [Model.wS_of_xi_ne_zero _ (by rw [xi_root]; exact one_ne_zero), xi_root, Model.xiS_zero, model_δ]; norm_num

/-- `w_N = 1`: the non-self mixture never reaches `N`. -/
theorem wS_N : model.wS polW 1 N = 1 := (model.wS_eq_one_iff polW_isPolicy nt_N).2 xins_N

theorem Qxi_N_0 : model.Qxi polW 1 N 0 = 1 := by
  rw [model.Qxi_eq_of_children_terminal N 0 (fun e => not_nt_two _)]; simp [xie_eq_one, r, N]
theorem Qxi_N_1 : model.Qxi polW 1 N 1 = 0 := by
  rw [model.Qxi_eq_of_children_terminal N 1 (fun e => not_nt_two _)]; simp [xie_eq_one, r, N]
theorem Qstar_N_0 : model.Qstar 1 N 0 = 1 := by
  rw [model.Qstar_eq_of_children_terminal N 0 (fun e => not_nt_two _)]; simp [xie_eq_one, r, N]
theorem Qstar_N_1 : model.Qstar 1 N 1 = 0 := by
  rw [model.Qstar_eq_of_children_terminal N 1 (fun e => not_nt_two _)]; simp [xie_eq_one, r, N]
theorem Vstar_N : model.Vstar 1 N = 1 := by
  rw [model.Vstar_fin_two nt_N, Qstar_N_0, Qstar_N_1]; norm_num
theorem Mx_N : model.Mx polW 1 N = 1 := by
  rw [model.Mx_fin_two, Qxi_N_0, Qxi_N_1]; norm_num

theorem Qxi_root_0 : model.Qxi polW 0 root 0 = 0 := by
  rw [model.Qxi_eq_of_children_terminal root 0 (fun e => by cases e; exact not_nt_leaf)]; simp [xie_eq_one, r]
theorem Qxi_root_1 : model.Qxi polW 0 root 1 = 1 := by
  have hx : model.xi polW 1 N ≠ 0 := by rw [xi_N]; norm_num
  rw [Model.Qxi_eq_sum, Fintype.sum_unique, xie_eq_one]
  simp only [r, model_r, model_γ, pow_zero, one_mul, zero_add]
  show model.Vxi polW 1 N = _
  rw [model.Vxi_eq nt_N, Fin.sum_univ_two, Qxi_N_0, Qxi_N_1]
  simp only [Model.xia, hx, if_false, mul_zero, add_zero, mul_one]
  rw [xiA_N_0, xi_N]
  norm_num

end Values

/-- `polW` is a plain fixed point of Instance W: at the root the supported action `1` has `Q_ξ = 1 = M`; at `N`
the supported action `0` has `Q_ξ = 1 = M`. -/
theorem isPlainFP : model.IsPlainFP polW := by
  refine ⟨polW_isPolicy, fun n h hnt => ?_⟩
  match n with
  | 0 =>
    rw [eq_root h]
    refine Fin.forall_fin_two.2 ⟨fun ha => ?_, fun _ => ?_⟩
    · simp [polW] at ha
    · rw [model.Mx_fin_two, Qxi_root_0, Qxi_root_1]; norm_num
  | 1 =>
    rw [eq_N_of_nonterminal h hnt]
    refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun ha => ?_⟩
    · rw [Mx_N, Qxi_N_0]
    · simp [polW] at ha
  | n + 2 => exact absurd hnt (not_nt_ge_two _ (by omega) h)

theorem TB_N : model.TB polW 1 N := by
  unfold Model.TB; rw [wS_N, Vstar_N, Mx_N]; norm_num

/-- **The `w_h = 1` corner of Theorem B is inhabited**: `polW` is a plain fixed point of Instance W, `N` is a
decision node with `w_N = 1` (the non-self mixture never reaches it), `TB` holds there, and `gap(N) = 0 = O_N`,
so Theorem B's bound `gap ≤ O_h` is attained with equality. Hence the hypothesis `w_h < 1` of `theoremB_strict` and
of `gap_eq_odds_not_attained` is necessary, not an artefact of the encoding. Grade N+: `N` is a genuine decision
node (two actions, one strictly worse), the root has `0 < w_root = 9/10 < 1` (the residual is present in the
model, it just never enters `N`), and `gap = 0` is obtained from `gap_le_zero_of_xins_eq_zero`, i.e. from
Theorem B's own `ξ_{-S}`-null case, not by a separate computation.
Source: [[uea-cole-shadow-mandate]] target 10; round-2 adversarial audit, item 6
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem w_eq_one_corner :
    model.IsPlainFP polW ∧ model.nonterminal 1 N ∧ model.wS polW 1 N = 1 ∧ model.TB polW 1 N ∧
    model.gap polW 1 N = 0 ∧ model.odds polW 1 N = 0 ∧ model.gap polW 1 N = model.odds polW 1 N ∧
    model.wS polW 0 root = 9 / 10 := by
  have htb : model.TB polW 1 N := TB_N
  have hgap : model.gap polW 1 N = 0 :=
    le_antisymm (model.gap_le_zero_of_xins_eq_zero isPlainFP nt_N xins_N htb)
      (model.gap_nonneg polW_isPolicy 1 N)
  have hodds : model.odds polW 1 N = 0 := by unfold Model.odds; rw [wS_N]; norm_num
  exact ⟨isPlainFP, nt_N, wS_N, htb, hgap, hodds, by rw [hgap, hodds], wS_root⟩

end InstW

/-- **Attainment without `w_h < 1`**: dropping the hypothesis `w_h < 1` from `gap_eq_odds_not_attained` makes the
existential true — at Instance W's node `N` (`w_N = 1`, `gap = O_N = 0`). Composition of `InstW.w_eq_one_corner`;
together with `gap_eq_odds_not_attained` this pins the attainment set of Theorem B's bound exactly to `w_h = 1`.
Source: [[uea-cole-shadow-mandate]] target 10; round-2 adversarial audit, item 6
Kind: C
Fidelity: n/a
Hyps: (a) -/
theorem gap_eq_odds_attained_at_w_one :
    ∃ (M : Model (Fin 2) Unit Unit) (π : Policy (Fin 2) Unit) (n : ℕ) (h : Hist (Fin 2) Unit n),
      M.IsPlainFP π ∧ M.nonterminal n h ∧ 0 < M.wS π n h ∧ M.wS π n h = 1 ∧ M.TB π n h ∧
        M.gap π n h = M.odds π n h := by
  obtain ⟨hfp, hnt, hw, htb, _, _, heq, _⟩ := InstW.w_eq_one_corner
  exact ⟨InstW.model, InstW.polW, 1, InstW.N, hfp, hnt, by rw [hw]; norm_num, hw, htb, heq⟩

end Cleanroom.Uea.UeaColeShadow
