import Cleanroom.Uea.UeaColeShadow.Instances

/-!
# Instance A: a partial-reset fixed point — Gap 1's boundary point

Two steps ([[oracle-side-gaps-reaudit]] lines 20–31): root actions `a₁ = 0`, `a₂ = 1`; after `a₁` the agent
chooses reward `x = 0.93` (action `0`) or `0`; after `a₂` it chooses `1` (`0`, swim) or `0` (`1`, sink).
`δ = 0.1`; the residual takes `a₁`/`a₂` with probability `1/2` each, picks `x` with probability `1/2` after `a₁`,
and always sinks after `a₂`. With `t := π(a₂|root)` and the (forced) optimal depth-1 choices:
`Q_ξ(root,a₁) = 0.93 (0.9(1-t) + 0.025)/(0.9(1-t) + 0.05)`, `Q_ξ(root,a₂) = 0.9 t/(0.9 t + 0.05)`.
At `t⋆ = 7/36`: `Q_ξ(root,a₁) = 9/10 = w_root V^*` exactly (the trust bound holds **with equality**),
`Q_ξ(root,a₂) = 7/9`, so `𝒜_root = {a₁} ≠ {π⋆(root)} = {a₂}` — the boundary configuration of Gap 1, at which the
two branches of the strict-reset map disagree; `t = 0` and `t = 1` are plain fixed points; `t⋆` is not.

Source: [[oracle-side-gaps-reaudit]] Instance A; [[uea-inventory]] 010, 007.
-/

namespace Cleanroom.Uea.UeaColeShadow

open Finset

namespace InstA

def alive : (n : ℕ) → Hist (Fin 2) Unit n → Bool
  | 0, _ => true
  | 1, _ => true
  | _, _ => false

/-- Rewards on arrival at depth 2: `x = 93/100` after `a₁, 0`; `1` after `a₂, 0`. -/
noncomputable def r : (n : ℕ) → Hist (Fin 2) Unit (n + 1) → ℝ
  | 0, _ => 0
  | 1, h => if (h 0).1 = 0 ∧ (h 1).1 = 0 then 93 / 100 else if (h 0).1 = 1 ∧ (h 1).1 = 0 then 1 else 0
  | _, _ => 0

/-- The residual: half/half at the root; `x` with probability `1/2` after `a₁`; sink after `a₂`. -/
noncomputable def νa : Unit → (n : ℕ) → Hist (Fin 2) Unit n → Fin 2 → ℝ
  | _, 0, _, _ => 1 / 2
  | _, 1, h, a => if (h 0).1 = 0 then 1 / 2 else (if a = 1 then 1 else 0)
  | _, _, _, a => if a = 0 then 1 else 0

theorem νa_mem (i : Unit) (n : ℕ) (h : Hist (Fin 2) Unit n) : νa i n h ∈ stdSimplex ℝ (Fin 2) := by
  refine ⟨fun a => ?_, ?_⟩
  · match n with
    | 0 => simp [νa]
    | 1 => simp only [νa]; split_ifs <;> norm_num
    | n + 2 => simp only [νa]; split_ifs <;> norm_num
  · match n with
    | 0 => simp [νa, Fin.sum_univ_two]
    | 1 => simp only [νa]; split_ifs <;> simp [Fin.sum_univ_two] <;> norm_num
    | n + 2 => simp [νa, Fin.sum_univ_two]

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
    simp only [pathReturnOf, r, Fin.init, Fin.castSucc_zero]
    split_ifs <;> norm_num
  | n + 3 => omega

/-- **Instance A** as a `Model`: `T = 2`, `γ = 1`, `δ = 1/10`.
Source: [[oracle-side-gaps-reaudit]] lines 20–23 (Instance A)
Kind: D
Fidelity: exact (terminal rewards rendered as rewards on arrival; `u = 0`)
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
/-- The node after `a₁`. -/
def L : Hist (Fin 2) Unit 1 := ext root 0 ()
/-- The node after `a₂`. -/
def R : Hist (Fin 2) Unit 1 := ext root 1 ()

@[simp] theorem model_T : model.T = 2 := rfl
@[simp] theorem model_r : model.r = r := rfl
@[simp] theorem model_γ : model.γ = 1 := rfl
@[simp] theorem model_νa : model.νa = νa := rfl
@[simp] theorem model_νe (i : Unit) (n : ℕ) (h : Hist (Fin 2) Unit n) (a : Fin 2) (e : Unit) : model.νe i n h a e = 1 := rfl
@[simp] theorem model_w (i : Unit) : model.w i = 1 / 10 := rfl
@[simp] theorem model_δ : model.δ = 1 / 10 := rfl

theorem nt_root : model.nonterminal 0 root := ⟨by simp, rfl⟩
theorem nt_L : model.nonterminal 1 L := ⟨by simp, rfl⟩
theorem nt_R : model.nonterminal 1 R := ⟨by simp, rfl⟩
theorem not_nt_two (h : Hist (Fin 2) Unit 2) : ¬ model.nonterminal 2 h := fun h' => by
  have := h'.1; simp at this
theorem not_nt_ge_two (n : ℕ) (hn : 2 ≤ n) (h : Hist (Fin 2) Unit n) : ¬ model.nonterminal n h :=
  model.not_nonterminal_of_le (by simpa using hn) h

theorem eq_root (h : Hist (Fin 2) Unit 0) : h = root := funext fun i => Fin.elim0 i
theorem eq_L_or_R (h : Hist (Fin 2) Unit 1) : h = L ∨ h = R := by
  rcases Fin.exists_fin_two.1 ⟨(h 0).1, rfl⟩ with h0 | h0
  · left; funext i; fin_cases i; exact Prod.ext h0 (Subsingleton.elim _ _)
  · right; funext i; fin_cases i; exact Prod.ext h0 (Subsingleton.elim _ _)

theorem xie_eq_one (n : ℕ) (h : Hist (Fin 2) Unit n) (a : Fin 2) (e : Unit) : model.xie n h a e = 1 :=
  model.xie_eq_one_of_unique n h a e

/-- The policy family: `t = π(a₂|root)`, optimal choices at depth 1. -/
noncomputable def polA (t : ℝ) : Policy (Fin 2) Unit := fun n _ a =>
  if n = 0 then (if a = 0 then 1 - t else t) else if n = 1 then (if a = 0 then 1 else 0) else 0

theorem polA_isPolicy {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : model.IsPolicy (polA t) := by
  intro n h hnt
  have hn : n < 2 := hnt.1
  refine ⟨fun a => ?_, ?_⟩
  · unfold polA; split_ifs <;> linarith
  · unfold polA
    match n with
    | 0 => simp [Fin.sum_univ_two]
    | 1 => simp [Fin.sum_univ_two]
    | n + 2 => omega

section Values
variable (t : ℝ)

theorem xins_L : model.xins 1 L = 1 / 20 := by simp [Model.xins, L, νa]; norm_num
theorem xins_R : model.xins 1 R = 1 / 20 := by simp [Model.xins, R, νa]; norm_num
theorem xinsA_L_0 : model.xinsA 1 L 0 = 1 / 40 := by simp [Model.xinsA, L, νa]; norm_num
theorem xinsA_R_0 : model.xinsA 1 R 0 = 0 := by simp [Model.xinsA, R, νa]
theorem xiS_L : model.xiS (polA t) 1 L = 1 - t := by simp [L, xie_eq_one, polA]
theorem xiS_R : model.xiS (polA t) 1 R = t := by simp [R, xie_eq_one, polA]
theorem xi_L : model.xi (polA t) 1 L = 9 / 10 * (1 - t) + 1 / 20 := by
  unfold Model.xi; rw [xins_L, xiS_L, model_δ]; ring
theorem xi_R : model.xi (polA t) 1 R = 9 / 10 * t + 1 / 20 := by
  unfold Model.xi; rw [xins_R, xiS_R, model_δ]; ring
theorem xiA_L_0 : model.xiA (polA t) 1 L 0 = 9 / 10 * (1 - t) + 1 / 40 := by
  rw [Model.xiA_eq, xiS_L, xinsA_L_0, model_δ]; norm_num [polA]
theorem xiA_R_0 : model.xiA (polA t) 1 R 0 = 9 / 10 * t := by
  rw [Model.xiA_eq, xiS_R, xinsA_R_0, model_δ]; norm_num [polA]
theorem xi_root : model.xi (polA t) 0 root = 1 := by
  unfold Model.xi; simp [Model.xins, model_δ]
theorem wS_root : model.wS (polA t) 0 root = 9 / 10 := by
  rw [Model.wS_of_xi_ne_zero _ (by rw [xi_root]; exact one_ne_zero), xi_root, Model.xiS_zero, model_δ]; norm_num

theorem Qxi_L_0 : model.Qxi (polA t) 1 L 0 = 93 / 100 := by
  rw [model.Qxi_eq_of_children_terminal L 0 (fun e => not_nt_two _)]; simp [xie_eq_one, r, L]
theorem Qxi_L_1 : model.Qxi (polA t) 1 L 1 = 0 := by
  rw [model.Qxi_eq_of_children_terminal L 1 (fun e => not_nt_two _)]; simp [xie_eq_one, r, L]
theorem Qxi_R_0 : model.Qxi (polA t) 1 R 0 = 1 := by
  rw [model.Qxi_eq_of_children_terminal R 0 (fun e => not_nt_two _)]; simp [xie_eq_one, r, R]
theorem Qxi_R_1 : model.Qxi (polA t) 1 R 1 = 0 := by
  rw [model.Qxi_eq_of_children_terminal R 1 (fun e => not_nt_two _)]; simp [xie_eq_one, r, R]
theorem Qstar_L_0 : model.Qstar 1 L 0 = 93 / 100 := by
  rw [model.Qstar_eq_of_children_terminal L 0 (fun e => not_nt_two _)]; simp [xie_eq_one, r, L]
theorem Qstar_L_1 : model.Qstar 1 L 1 = 0 := by
  rw [model.Qstar_eq_of_children_terminal L 1 (fun e => not_nt_two _)]; simp [xie_eq_one, r, L]
theorem Qstar_R_0 : model.Qstar 1 R 0 = 1 := by
  rw [model.Qstar_eq_of_children_terminal R 0 (fun e => not_nt_two _)]; simp [xie_eq_one, r, R]
theorem Qstar_R_1 : model.Qstar 1 R 1 = 0 := by
  rw [model.Qstar_eq_of_children_terminal R 1 (fun e => not_nt_two _)]; simp [xie_eq_one, r, R]
theorem Vstar_L : model.Vstar 1 L = 93 / 100 := by
  rw [model.Vstar_fin_two nt_L, Qstar_L_0, Qstar_L_1]; norm_num
theorem Vstar_R : model.Vstar 1 R = 1 := by
  rw [model.Vstar_fin_two nt_R, Qstar_R_0, Qstar_R_1]; norm_num
theorem Mx_L : model.Mx (polA t) 1 L = 93 / 100 := by
  rw [model.Mx_fin_two, Qxi_L_0, Qxi_L_1]; norm_num
theorem Mx_R : model.Mx (polA t) 1 R = 1 := by
  rw [model.Mx_fin_two, Qxi_R_0, Qxi_R_1]; norm_num
theorem Qstar_root_0 : model.Qstar 0 root 0 = 93 / 100 := by
  rw [Model.Qstar_eq_sum, Fintype.sum_unique, xie_eq_one]; simp [r]; exact Vstar_L
theorem Qstar_root_1 : model.Qstar 0 root 1 = 1 := by
  rw [Model.Qstar_eq_sum, Fintype.sum_unique, xie_eq_one]; simp [r]; exact Vstar_R
theorem Vstar_root : model.Vstar 0 root = 1 := by
  rw [model.Vstar_fin_two nt_root, Qstar_root_0, Qstar_root_1]; norm_num
theorem piStar_root : model.piStar 0 root = 1 := by
  refine model.piStar_eq_of_unique nt_root (Fin.forall_fin_two.2 ⟨fun ha => ?_, fun _ => rfl⟩)
  rw [Qstar_root_0, Vstar_root] at ha; norm_num at ha

/-- `Q_ξ(root, a₁) = 0.93 (0.9(1-t) + 0.025)/(0.9(1-t) + 0.05)`.
Source: [[oracle-side-gaps-reaudit]] line 25
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Qxi_root_0 (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    model.Qxi (polA t) 0 root 0 = 93 / 100 * ((9 / 10 * (1 - t) + 1 / 40) / (9 / 10 * (1 - t) + 1 / 20)) := by
  have hx : model.xi (polA t) 1 L ≠ 0 := by
    rw [xi_L]
    have h : (0:ℝ) < 9 / 10 * (1 - t) + 1 / 20 := by linarith
    exact h.ne'
  rw [Model.Qxi_eq_sum, Fintype.sum_unique, xie_eq_one]
  simp only [r, model_r, model_γ, pow_zero, one_mul, zero_add]
  show model.Vxi (polA t) 1 L = _
  rw [model.Vxi_eq nt_L, Fin.sum_univ_two, Qxi_L_0, Qxi_L_1]
  simp only [Model.xia, hx, if_false, mul_zero, add_zero]
  rw [xiA_L_0, xi_L]
  ring

/-- `Q_ξ(root, a₂) = 0.9 t / (0.9 t + 0.05)`.
Source: [[oracle-side-gaps-reaudit]] line 25
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Qxi_root_1 (ht0 : 0 ≤ t) :
    model.Qxi (polA t) 0 root 1 = 9 / 10 * t / (9 / 10 * t + 1 / 20) := by
  have hx : model.xi (polA t) 1 R ≠ 0 := by rw [xi_R]; positivity
  rw [Model.Qxi_eq_sum, Fintype.sum_unique, xie_eq_one]
  simp only [r, model_r, model_γ, pow_zero, one_mul, zero_add]
  show model.Vxi (polA t) 1 R = _
  rw [model.Vxi_eq nt_R, Fin.sum_univ_two, Qxi_R_0, Qxi_R_1]
  simp only [Model.xia, hx, if_false, mul_zero, add_zero, mul_one]
  rw [xiA_R_0, xi_R]

end Values

/-- **Instance A at `t⋆ = 7/36`**: `Q_ξ(root,a₁) = 9/10 = w_root V^*_ξ(root)` (the trust bound holds with
**equality**), `Q_ξ(root,a₂) = 7/9 < 9/10`, so the EDT best response is `a₁` while `π⋆(root) = a₂`; `π(a₂|root) = 7/36 > 0`
makes `t⋆` **not** a plain fixed point. This is Gap 1's boundary configuration (the two branches of the reset
map disagree at equality), and it shows `π⋆(h) ∉ 𝒜_h` at equality is generic.
Source: [[oracle-side-gaps-reaudit]] lines 27–29
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem tstar :
    model.Qxi (polA (7 / 36)) 0 root 0 = 9 / 10 ∧ model.Qxi (polA (7 / 36)) 0 root 1 = 7 / 9 ∧
    model.wS (polA (7 / 36)) 0 root * model.Vstar 0 root = model.Mx (polA (7 / 36)) 0 root ∧
    model.argmaxSet (polA (7 / 36)) 0 root = {0} ∧ model.piStar 0 root = 1 ∧
    ¬ model.IsPlainFP (polA (7 / 36)) := by
  have h0 : model.Qxi (polA (7 / 36)) 0 root 0 = 9 / 10 := by
    rw [Qxi_root_0 _ (by norm_num) (by norm_num)]; norm_num
  have h1 : model.Qxi (polA (7 / 36)) 0 root 1 = 7 / 9 := by
    rw [Qxi_root_1 _ (by norm_num)]; norm_num
  have hMx : model.Mx (polA (7 / 36)) 0 root = 9 / 10 := by
    rw [model.Mx_fin_two, h0, h1]; norm_num
  refine ⟨h0, h1, ?_, ?_, piStar_root, ?_⟩
  · rw [wS_root, Vstar_root, hMx]; norm_num
  · ext a
    rw [Model.mem_argmaxSet, hMx, mem_singleton]
    rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with rfl | rfl
    · simp [h0]
    · simp [h1]; norm_num
  · rintro ⟨_, hfp⟩
    have := hfp 0 root nt_root 1 (by simp [polA])
    rw [h1, hMx] at this; norm_num at this

/-- `t = 0` and `t = 1` are plain fixed points of Instance A (the honest fixed points of `π_S`, with strict
trust bounds `3441/3800 > 9/10` and `18/19 > 9/10`).
Source: [[oracle-side-gaps-reaudit]] line 30
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem isPlainFP_zero_one : model.IsPlainFP (polA 0) ∧ model.IsPlainFP (polA 1) ∧
    model.Qxi (polA 0) 0 root 0 = 3441 / 3800 ∧ model.Qxi (polA 1) 0 root 1 = 18 / 19 := by
  have q00 : model.Qxi (polA 0) 0 root 0 = 3441 / 3800 := by rw [Qxi_root_0 _ le_rfl zero_le_one]; norm_num
  have q01 : model.Qxi (polA 0) 0 root 1 = 0 := by rw [Qxi_root_1 _ le_rfl]; norm_num
  have q10 : model.Qxi (polA 1) 0 root 0 = 93 / 200 := by rw [Qxi_root_0 _ zero_le_one le_rfl]; norm_num
  have q11 : model.Qxi (polA 1) 0 root 1 = 18 / 19 := by rw [Qxi_root_1 _ zero_le_one]; norm_num
  have depth1 : ∀ t, ∀ h : Hist (Fin 2) Unit 1, model.nonterminal 1 h →
      ∀ a, 0 < polA t 1 h a → model.Qxi (polA t) 1 h a = model.Mx (polA t) 1 h := by
    intro t h _
    refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun ha => ?_⟩
    · rcases eq_L_or_R h with rfl | rfl
      · rw [Mx_L, Qxi_L_0]
      · rw [Mx_R, Qxi_R_0]
    · simp [polA] at ha
  refine ⟨⟨polA_isPolicy le_rfl zero_le_one, fun n h hnt => ?_⟩, ⟨polA_isPolicy zero_le_one le_rfl, fun n h hnt => ?_⟩,
    q00, q11⟩
  · match n with
    | 0 =>
      rw [eq_root h]
      refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun ha => ?_⟩
      · rw [model.Mx_fin_two, q00, q01]; norm_num
      · simp [polA] at ha
    | 1 => exact depth1 0 h hnt
    | n + 2 => exact absurd hnt (not_nt_ge_two _ (by omega) h)
  · match n with
    | 0 =>
      rw [eq_root h]
      refine Fin.forall_fin_two.2 ⟨fun ha => ?_, fun _ => ?_⟩
      · simp [polA] at ha
      · rw [model.Mx_fin_two, q10, q11]; norm_num
    | 1 => exact depth1 1 h hnt
    | n + 2 => exact absurd hnt (not_nt_ge_two _ (by omega) h)

end InstA

end Cleanroom.Uea.UeaColeShadow
