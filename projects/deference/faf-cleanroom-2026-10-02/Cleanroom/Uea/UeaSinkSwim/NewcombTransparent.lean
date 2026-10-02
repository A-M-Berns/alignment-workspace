import Cleanroom.Uea.UeaSinkSwim.NewcombOpaque

/-!
# Transparent Newcomb in the sequential model

`Transparent.model P : Model (Fin 2) (Fin 2) (Fin 4)`, `T = 2`: at the root the agent `look`s (action `0`;
action `1` leads to a dead node with reward `0` — an encoding artifact of one action type per model, shown
never to be in an argmax) and sees the content `e₀ ∈ {M = 0, empty = 1}`; at `H_M`/`H_0` it one-boxes (`0`)
or two-boxes (`1`) with a dummy percept; the reward `payoff(a₁, e₀)` arrives at depth `2`. Four
hypotheses `T_pol`, `pol = (action on M, action on empty)`: `UDT = (one, two)`, `1box = (one, one)`,
`2box = (two, two)`, `worst = (two, one)`; `T_pol` looks, Omega fills the box w.p. `q` if `pol(M) = one`
else `1 - q`, then `pol` acts; shares `f_pol` of `δ`.

Facts: `ξ(M)` is policy-free; the last-level values are the immediate payoffs, so `π⋆` two-boxes on both
branches and **2box is the unique plain fixed point among all policies** (strict argmax at `H_M`, `H_0` and
the root, for `0 < q < 1`), with `gap = 0` and `TB` at the root, `H_M`, `H_0`; `V^*(root) = ξ(M) + (1-ξ(M)) KILO`;
`trueValue pol := Q^{ν_pol}(root, look)` (the value against the policy's own accurate Omega) is
`UDT = q MEG + (1-q) KILO`, `1box = q MEG`, `2box = (1-q) + q KILO`, `worst = 1 - q`. Headline remark: the fixed
point is Bayes-optimal for `ξ` and, at `q = 9/10`, worst-but-one in the world — "the interleaving artifact
is exactly updatefulness". `V^*`/`Q^*` do not mention the policy (true by their types: `Vstar : Model → ℕ → Hist → ℝ`).

Scope: finite shadow of rOSI ([[sequential-self-game]] §7). Namespace `Cleanroom.Uea.UeaSinkSwim.Transparent`
(faf-cleanroom run, `uea-sink-swim`, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Finset
open Cleanroom.Uea.UeaColeShadow

namespace Transparent

open Newcomb

/-- The four policies, as `(action on M, action on empty)`: `0 = UDT (one, two)`, `1 = 1box (one, one)`,
`2 = 2box (two, two)`, `3 = worst (two, one)`; `pol i e` is the action on percept `e`.
Source: `newcomb_interleaving.py` `POLICIES`; [[uea-2-inventory]] 2-002
Kind: D
Fidelity: exact
Hyps: n/a -/
def pol (i : Fin 4) (e : Fin 2) : Fin 2 :=
  if i = 0 then e else if i = 1 then 0 else if i = 2 then 1 else (if e = 0 then 1 else 0)

/-- Parameters: Omega's accuracy `q ∈ (0,1)`, non-self prior `δ ∈ (0,1)`, shares `f i ≥ 0` summing to `1`.
Source: `newcomb_interleaving.py` `transparent_class`
Kind: D
Fidelity: exact (`q ∈ (0,1)` strict so that both branches have positive `ξ`-mass)
Hyps: n/a -/
structure TP where
  q : ℝ
  δ : ℝ
  f : Fin 4 → ℝ
  hq0 : 0 < q
  hq1 : q < 1
  hδ : 0 < δ
  hδ1 : δ < 1
  hf : ∀ i, 0 ≤ f i
  hfsum : f 0 + f 1 + f 2 + f 3 = 1

variable (P : TP)

/-- Omega's probability of filling the box under `T_i`: `q` if `pol i` one-boxes on `M`, else `1 - q`. -/
noncomputable def pM (i : Fin 4) : ℝ := if pol i 0 = 0 then P.q else 1 - P.q

theorem pM_pos (i : Fin 4) : 0 < pM P i := by
  unfold pM; split_ifs; exact P.hq0; linarith [P.hq1]
theorem pM_lt_one (i : Fin 4) : pM P i < 1 := by
  unfold pM; split_ifs; exact P.hq1; linarith [P.hq0]

def alive : (n : ℕ) → Hist (Fin 2) (Fin 2) n → Bool
  | 0, _ => true
  | 1, h => decide ((h 0).1 = 0)
  | _ + 2, _ => false

/-- Rewards on arrival: `0` at depth `1`; `payoff(a₁, e₀)` at depth `2` after `look`; `0` otherwise. -/
noncomputable def r : (n : ℕ) → Hist (Fin 2) (Fin 2) (n + 1) → ℝ
  | 0, _ => 0
  | 1, h => if (h 0).1 = 0 then payoff (h 1).1 (h 0).2 else 0
  | _ + 2, _ => 0

/-- `T_i` looks at the root and then plays `pol i` on the root percept. -/
noncomputable def νa (i : Fin 4) : (n : ℕ) → Hist (Fin 2) (Fin 2) n → Fin 2 → ℝ
  | 0, _, a => if a = 0 then 1 else 0
  | _ + 1, h, a => if a = pol i (h 0).2 then 1 else 0

/-- `T_i`'s Omega fills the box w.p. `pM i`; the later percept is the dummy `0`. -/
noncomputable def νe (i : Fin 4) : (n : ℕ) → Hist (Fin 2) (Fin 2) n → Fin 2 → Fin 2 → ℝ
  | 0, _, _, e => if e = 0 then pM P i else 1 - pM P i
  | _ + 1, _, _, e => if e = 0 then 1 else 0

theorem νa_mem (i : Fin 4) (n : ℕ) (h : Hist (Fin 2) (Fin 2) n) : νa i n h ∈ stdSimplex ℝ (Fin 2) := by
  refine ⟨fun a => ?_, ?_⟩
  · match n with
    | 0 => simp only [νa]; split_ifs <;> norm_num
    | n + 1 => simp only [νa]; split_ifs <;> norm_num
  · match n with
    | 0 => simp [νa, Fin.sum_univ_two]
    | n + 1 =>
      simp only [νa, Fin.sum_univ_two]
      generalize pol i (h 0).2 = p
      fin_cases p <;> simp

theorem νe_mem (i : Fin 4) (n : ℕ) (h : Hist (Fin 2) (Fin 2) n) (a : Fin 2) :
    νe P i n h a ∈ stdSimplex ℝ (Fin 2) := by
  have h0 := pM_pos P i; have h1 := pM_lt_one P i
  refine ⟨fun e => ?_, ?_⟩
  · match n with
    | 0 => simp only [νe]; split_ifs <;> linarith
    | n + 1 => simp only [νe]; split_ifs <;> norm_num
  · match n with
    | 0 => simp [νe, Fin.sum_univ_two]
    | n + 1 => simp [νe, Fin.sum_univ_two]

theorem r_nonneg (n : ℕ) (h : Hist (Fin 2) (Fin 2) (n + 1)) : 0 ≤ r n h := by
  match n with
  | 0 => exact le_rfl
  | 1 => simp only [r]; split_ifs; exact payoff_nonneg _ _; exact le_rfl
  | n + 2 => exact le_rfl

theorem r_le_one (n : ℕ) (h : Hist (Fin 2) (Fin 2) (n + 1)) : r n h ≤ 1 := by
  match n with
  | 0 => exact zero_le_one
  | 1 => simp only [r]; split_ifs; exact payoff_le_one _ _; exact zero_le_one
  | n + 2 => exact zero_le_one

theorem norm (n : ℕ) (hn : n ≤ 2) (h : Hist (Fin 2) (Fin 2) n) : pathReturnOf 1 r n h ≤ 1 := by
  match n with
  | 0 => simp
  | 1 => simp [pathReturnOf, r]
  | 2 =>
    simp only [pathReturnOf, pow_zero, one_mul, zero_add, pow_one]
    show (0:ℝ) + r 1 h ≤ 1
    rw [zero_add]; exact r_le_one 1 h
  | n + 3 => omega

theorem alive_init (n : ℕ) (h : Hist (Fin 2) (Fin 2) (n + 1)) (hh : alive (n + 1) h = true) :
    alive n (Fin.init h) = true := by
  match n with
  | 0 => rfl
  | n + 1 => simp [alive] at hh

/-- **Transparent Newcomb** `model P`: `T = 2`, `γ = 1`, weights `δ f i`.
Source: `newcomb_interleaving.py` `transparent_tree`, `omega_hyp`, `transparent_class`; [[uea-2-inventory]] 2-002
Kind: D
Fidelity: variant: the root has a second action (`1`, dead node, reward `0`) because the model has one action type;
it is never in an argmax (`Qxi_root_1`, `root_look_of_isPlainFP`) — disclosed
Hyps: n/a -/
noncomputable def model : Model (Fin 2) (Fin 2) (Fin 4) where
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
  νe := νe P
  νa_mem := νa_mem
  νe_mem := νe_mem P
  w := fun i => P.δ * P.f i
  w_nonneg := fun i => mul_nonneg P.hδ.le (P.hf i)
  δ := P.δ
  w_sum := by rw [← mul_sum, Fin.sum_univ_four, P.hfsum, mul_one]
  δ_pos := P.hδ
  δ_lt_one := P.hδ1

/-- The root. -/
def root : Hist (Fin 2) (Fin 2) 0 := Fin.elim0
/-- `H e := (look, e)`: the decision node after seeing `e` (`H 0 = H_M`, `H 1 = H_0`). -/
def H (e : Fin 2) : Hist (Fin 2) (Fin 2) 1 := ext root 0 e
/-- The dead node after action `1` at the root. -/
def dead (e : Fin 2) : Hist (Fin 2) (Fin 2) 1 := ext root 1 e

@[simp] theorem model_T : (model P).T = 2 := rfl
@[simp] theorem model_alive : (model P).alive = alive := rfl
@[simp] theorem model_δ : (model P).δ = P.δ := rfl
@[simp] theorem model_r : (model P).r = r := rfl
@[simp] theorem model_γ : (model P).γ = 1 := rfl
@[simp] theorem model_w (i : Fin 4) : (model P).w i = P.δ * P.f i := rfl
@[simp] theorem model_νa : (model P).νa = νa := rfl
@[simp] theorem model_νe : (model P).νe = νe P := rfl
@[simp] theorem H_zero (e : Fin 2) : H e 0 = (0, e) := rfl

theorem nt_root : (model P).nonterminal 0 root := ⟨by simp, rfl⟩
theorem nt_H (e : Fin 2) : (model P).nonterminal 1 (H e) := ⟨by simp, by simp [alive, H]⟩
theorem not_nt_dead (e : Fin 2) : ¬ (model P).nonterminal 1 (dead e) := fun h => by
  have := h.2; simp [alive, dead] at this
theorem not_nt_two (h : Hist (Fin 2) (Fin 2) 2) : ¬ (model P).nonterminal 2 h := fun h' => by
  have := h'.1; simp at this
theorem not_nt_ge_two (n : ℕ) (hn : 2 ≤ n) (h : Hist (Fin 2) (Fin 2) n) : ¬ (model P).nonterminal n h :=
  (model P).not_nonterminal_of_le (by simpa using hn) h

theorem eq_root (h : Hist (Fin 2) (Fin 2) 0) : h = root := funext fun i => Fin.elim0 i

theorem eq_H_of_nonterminal (h : Hist (Fin 2) (Fin 2) 1) (hnt : (model P).nonterminal 1 h) : h = H (h 0).2 := by
  have h0 : (h 0).1 = 0 := by have := hnt.2; simpa [alive] using this
  funext i
  fin_cases i
  exact Prod.ext h0 rfl

/-! ### Kernels -/

/-- The depth-`1` percept kernel is the dummy `δ_0` under both branches of `xie` (the fallback included). -/
theorem xie_one (h : Hist (Fin 2) (Fin 2) 1) (a : Fin 2) (e : Fin 2) :
    (model P).xie 1 h a e = if e = 0 then 1 else 0 := by
  unfold Model.xie
  split_ifs with hA he he
  · simp [νe, he, Fin.sum_univ_four]
    rw [← mul_add, ← mul_add, ← mul_add, P.hfsum, mul_one, div_self P.hδ.ne']
  · simp [νe, he]
  · rw [div_eq_iff hA]
    simp only [model_νe, νe, he, if_true, mul_one]
    rw [one_mul]
    rfl
  · simp [νe, he]

theorem xinsA_root_0 : (model P).xinsA 0 root 0 = P.δ := by
  simp [Model.xinsA, Fin.sum_univ_four, νa]
  rw [← mul_add, ← mul_add, ← mul_add, P.hfsum, mul_one]

theorem xinsA_root_1 : (model P).xinsA 0 root 1 = 0 := by
  simp [Model.xinsA, νa]

/-- `ξ(M) := ξ(M | look)`. -/
noncomputable def xiM : ℝ := ∑ i, P.f i * pM P i

/-- **`ξ(M)` is policy-free**: `ξ(M|look) = ∑_pol f_pol [pol(M) = one ? q : 1-q]`.
Source: [[uea-2-inventory]] 2-002 (`transparent_report`'s `xiM`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem xie_root_0_0 : (model P).xie 0 root 0 0 = xiM P := by
  have hδ := P.hδ.ne'
  unfold Model.xie
  rw [if_neg (by rw [xinsA_root_0]; exact hδ), xinsA_root_0]
  unfold xiM
  rw [div_eq_iff hδ, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  simp [νa, νe]
  ring

theorem xie_root_0_1 : (model P).xie 0 root 0 1 = 1 - xiM P := by
  have := (model P).xie_sum 0 root 0
  rw [Fin.sum_univ_two, xie_root_0_0] at this
  linarith

theorem f_sum : ∑ i, P.f i = 1 := by rw [Fin.sum_univ_four]; exact P.hfsum

theorem xiM_pos : 0 < xiM P := by
  unfold xiM
  have hsum : ∑ i, P.f i * pM P i ≥ ∑ i, P.f i * (P.q ⊓ (1 - P.q)) := by
    refine sum_le_sum fun i _ => ?_
    unfold pM; split_ifs
    · exact mul_le_mul_of_nonneg_left inf_le_left (P.hf i)
    · exact mul_le_mul_of_nonneg_left inf_le_right (P.hf i)
  rw [← sum_mul, f_sum, one_mul] at hsum
  have : 0 < P.q ⊓ (1 - P.q) := lt_inf_iff.2 ⟨P.hq0, by linarith [P.hq1]⟩
  linarith

theorem xiM_lt_one : xiM P < 1 := by
  unfold xiM
  have hsum : ∑ i, P.f i * pM P i ≤ ∑ i, P.f i * (P.q ⊔ (1 - P.q)) := by
    refine sum_le_sum fun i _ => ?_
    unfold pM; split_ifs
    · exact mul_le_mul_of_nonneg_left le_sup_left (P.hf i)
    · exact mul_le_mul_of_nonneg_left le_sup_right (P.hf i)
  rw [← sum_mul, f_sum, one_mul] at hsum
  have : P.q ⊔ (1 - P.q) < 1 := sup_lt_iff.2 ⟨P.hq1, by linarith [P.hq0]⟩
  linarith

/-! ### Last-level values are the immediate payoffs -/

section Values
variable (π : Policy (Fin 2) (Fin 2))

theorem r_H (e a : Fin 2) (e' : Fin 2) : r 1 (ext (H e) a e') = payoff a e := by
  simp [r, H]

/-- `Q_ξ(H_e, a) = payoff(a, e)`. -/
theorem Qxi_H (e a : Fin 2) : (model P).Qxi π 1 (H e) a = payoff a e := by
  rw [(model P).Qxi_eq_of_children_terminal (H e) a (fun e' => not_nt_two P _), Fin.sum_univ_two, xie_one, xie_one]
  simp [r_H]

theorem Qpi_H (e a : Fin 2) : (model P).Qpi π 1 (H e) a = payoff a e := by
  rw [(model P).Qpi_eq_of_children_terminal (H e) a (fun e' => not_nt_two P _), Fin.sum_univ_two, xie_one, xie_one]
  simp [r_H]

theorem Qstar_H (e a : Fin 2) : (model P).Qstar 1 (H e) a = payoff a e := by
  rw [(model P).Qstar_eq_of_children_terminal (H e) a (fun e' => not_nt_two P _), Fin.sum_univ_two, xie_one, xie_one]
  simp [r_H]

theorem payoff_0_lt_1 : ∀ e : Fin 2, payoff 0 e < payoff 1 e := by
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · rw [payoff_00, payoff_10]; unfold MEG; norm_num
  · rw [payoff_01, payoff_11]; unfold KILO; norm_num

/-- `V^*(H_e) = payoff(two, e)`: two-boxing is optimal on both branches. -/
theorem Vstar_H (e : Fin 2) : (model P).Vstar 1 (H e) = payoff 1 e := by
  rw [(model P).Vstar_fin_two (nt_H P e), Qstar_H, Qstar_H]
  exact max_eq_right (payoff_0_lt_1 e).le

/-- `π⋆` two-boxes on both branches (`1 > MEG`, `KILO > 0`). -/
theorem piStar_H (e : Fin 2) : (model P).piStar 1 (H e) = 1 := by
  apply (model P).piStar_eq_of_unique (nt_H P e)
  refine Fin.forall_fin_two.2 ⟨fun ha => ?_, fun _ => rfl⟩
  rw [Qstar_H, Vstar_H] at ha
  exact absurd ha (payoff_0_lt_1 e).ne

theorem Mx_H (e : Fin 2) : (model P).Mx π 1 (H e) = payoff 1 e := by
  rw [(model P).Mx_fin_two, Qxi_H, Qxi_H]
  exact max_eq_right (payoff_0_lt_1 e).le

/-- `V_ξ(H_e) = ∑_a ξ(a|H_e) payoff(a, e)`. -/
theorem Vxi_H (e : Fin 2) : (model P).Vxi π 1 (H e) = ∑ a, (model P).xia π 1 (H e) a * payoff a e := by
  rw [(model P).Vxi_eq (nt_H P e)]
  exact sum_congr rfl fun a _ => by rw [Qxi_H]

/-- `V_ξ(H_M) ≥ MEG` under every policy. -/
theorem Vxi_H_M_ge (hπ : (model P).IsPolicy π) : MEG ≤ (model P).Vxi π 1 (H 0) := by
  rw [Vxi_H, Fin.sum_univ_two, payoff_00, payoff_10]
  have hs := (model P).xia_sum hπ (nt_H P 0)
  rw [Fin.sum_univ_two] at hs
  have h0 := (model P).xia_nonneg hπ (nt_H P 0) 0
  have h1 := (model P).xia_nonneg hπ (nt_H P 0) 1
  have : MEG ≤ 1 := by unfold MEG; norm_num
  nlinarith

/-- `Q_ξ(root, dead) = 0`: the dead action is worth nothing. -/
theorem Qxi_root_1 : (model P).Qxi π 0 root 1 = 0 := by
  rw [(model P).Qxi_eq_of_children_terminal root 1 (fun e => not_nt_dead P e)]
  simp [r]

theorem Qstar_root_1 : (model P).Qstar 0 root 1 = 0 := by
  rw [(model P).Qstar_eq_of_children_terminal root 1 (fun e => not_nt_dead P e)]
  simp [r]

theorem Qxi_root_0 : (model P).Qxi π 0 root 0 =
    xiM P * (model P).Vxi π 1 (H 0) + (1 - xiM P) * (model P).Vxi π 1 (H 1) := by
  rw [Model.Qxi_eq_sum, Fin.sum_univ_two, xie_root_0_0, xie_root_0_1]
  simp [r, H]

theorem Qpi_root_0 : (model P).Qpi π 0 root 0 =
    xiM P * (model P).Vpi π 1 (H 0) + (1 - xiM P) * (model P).Vpi π 1 (H 1) := by
  rw [Model.Qpi_eq_sum, Fin.sum_univ_two, xie_root_0_0, xie_root_0_1]
  simp [r, H]

/-- `V^*(root) = ξ(M) + (1 - ξ(M)) KILO`. -/
theorem Qstar_root_0 : (model P).Qstar 0 root 0 = xiM P + (1 - xiM P) * KILO := by
  have e0 : (model P).Vstar 1 (ext root 0 0) = payoff 1 0 := Vstar_H P 0
  have e1 : (model P).Vstar 1 (ext root 0 1) = payoff 1 1 := Vstar_H P 1
  rw [Model.Qstar_eq_sum, Fin.sum_univ_two, xie_root_0_0, xie_root_0_1]
  simp only [model_γ, pow_zero, one_mul, model_r, r, zero_add]
  rw [e0, e1, payoff_10, payoff_11]
  ring

theorem Vstar_root : (model P).Vstar 0 root = xiM P + (1 - xiM P) * KILO := by
  rw [(model P).Vstar_fin_two (nt_root P), Qstar_root_0, Qstar_root_1]
  have := xiM_pos P; have := xiM_lt_one P
  have : 0 < KILO := by unfold KILO; norm_num
  exact max_eq_left (by nlinarith)

theorem piStar_root : (model P).piStar 0 root = 0 := by
  apply (model P).piStar_eq_of_unique (nt_root P)
  refine Fin.forall_fin_two.2 ⟨fun _ => rfl, fun ha => ?_⟩
  rw [Qstar_root_1, Vstar_root] at ha
  have := xiM_pos P; have := xiM_lt_one P
  have : 0 < KILO := by unfold KILO; norm_num
  nlinarith

/-- `Q_ξ(root, look) > 0 = Q_ξ(root, dead)` under every policy. -/
theorem Qxi_root_0_pos (hπ : (model P).IsPolicy π) : 0 < (model P).Qxi π 0 root 0 := by
  rw [Qxi_root_0]
  have h1 := Vxi_H_M_ge P π hπ
  have h2 := (model P).Vxi_nonneg hπ 1 (H 1)
  have h3 := xiM_pos P; have h4 := xiM_lt_one P
  have : 0 < MEG := by unfold MEG; norm_num
  nlinarith

end Values

/-! ### The fixed point -/

/-- The two-boxing policy: `look` at the root, `two` at depth `≥ 1`. -/
noncomputable def twoBox : Policy (Fin 2) (Fin 2) := fun n _ a =>
  if n = 0 then (if a = 0 then 1 else 0) else (if a = 1 then 1 else 0)

theorem twoBox_isPolicy : (model P).IsPolicy twoBox := by
  intro n h _
  refine ⟨fun a => ?_, ?_⟩
  · by_cases hn : n = 0 <;> fin_cases a <;> simp [twoBox, hn]
  · by_cases hn : n = 0 <;> simp [twoBox, hn]

theorem twoBox_isPure : (model P).IsPure twoBox := fun n _ _ => by
  by_cases hn : n = 0
  · exact ⟨0, by simp [twoBox, hn]⟩
  · exact ⟨1, by simp [twoBox, hn]⟩

/-- **2box is the unique plain fixed point among all policies**: `π` is a plain fixed point iff it is a policy
that looks at the root and two-boxes at `H_M` and `H_0` (strict argmax at all three nodes).
Source: [[uea-2-inventory]] 2-002 (`transparent_report`: "2box is the unique fixed point"); [[uea-inventory]] 034
Kind: P
Fidelity: exact (both directions, every `q ∈ (0,1)`, `δ`, `f`)
Hyps: (a) -/
theorem isPlainFP_iff (π : Policy (Fin 2) (Fin 2)) : (model P).IsPlainFP π ↔
    (model P).IsPolicy π ∧ π 0 root 0 = 1 ∧ π 1 (H 0) 1 = 1 ∧ π 1 (H 1) 1 = 1 := by
  constructor
  · rintro ⟨hπ, hfp⟩
    have hH : ∀ e, π 1 (H e) 1 = 1 := by
      intro e
      have h0 : π 1 (H e) 0 = 0 := by
        by_contra hne
        have hpos : 0 < π 1 (H e) 0 := lt_of_le_of_ne (hπ.nonneg (nt_H P e) 0) (Ne.symm hne)
        have := hfp 1 (H e) (nt_H P e) 0 hpos
        rw [Qxi_H, Mx_H] at this
        exact absurd this (payoff_0_lt_1 e).ne
      have := hπ.fin_two_zero (nt_H P e); rw [h0] at this; linarith
    refine ⟨hπ, ?_, hH 0, hH 1⟩
    have h1 : π 0 root 1 = 0 := by
      by_contra hne
      have hpos : 0 < π 0 root 1 := lt_of_le_of_ne (hπ.nonneg (nt_root P) 1) (Ne.symm hne)
      have := hfp 0 root (nt_root P) 1 hpos
      rw [Qxi_root_1] at this
      have hle := (model P).Qxi_le_Mx (π := π) 0 root 0
      have := Qxi_root_0_pos P π hπ
      linarith
    rw [hπ.fin_two_zero (nt_root P), h1, sub_zero]
  · rintro ⟨hπ, hlook, hM, h0⟩
    refine ⟨hπ, fun n h hnt => ?_⟩
    match n with
    | 0 =>
      rw [eq_root h]
      have hM' : (model P).Mx π 0 root = (model P).Qxi π 0 root 0 := by
        rw [(model P).Mx_fin_two, Qxi_root_1]
        exact max_eq_left (Qxi_root_0_pos P π hπ).le
      refine Fin.forall_fin_two.2 ⟨fun _ => hM'.symm, fun ha => ?_⟩
      have := hπ.fin_two_zero (nt_root P); rw [hlook] at this; linarith
    | 1 =>
      rw [eq_H_of_nonterminal P h hnt]
      have hH : ∀ e, π 1 (H e) 1 = 1 := Fin.forall_fin_two.2 ⟨hM, h0⟩
      have he : π 1 (H (h 0).2) 1 = 1 := hH (h 0).2
      refine Fin.forall_fin_two.2 ⟨fun ha => ?_, fun _ => by rw [Qxi_H, Mx_H]⟩
      have := hπ.fin_two_zero (nt_H P (h 0).2); rw [he] at this; linarith
    | n + 2 => exact absurd hnt (not_nt_ge_two P (n + 2) (by omega) h)

theorem twoBox_isPlainFP : (model P).IsPlainFP twoBox :=
  (isPlainFP_iff P twoBox).2 ⟨twoBox_isPolicy P, by simp [twoBox], by simp [twoBox], by simp [twoBox]⟩

/-- Every fixed point has `gap = 0` at the root and at `H_M`, `H_0`.
Source: [[uea-2-inventory]] 2-002
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem gap_of_isPlainFP {π : Policy (Fin 2) (Fin 2)} (hfp : (model P).IsPlainFP π) :
    (model P).gap π 0 root = 0 ∧ ∀ e, (model P).gap π 1 (H e) = 0 := by
  obtain ⟨hπ, hlook, hM, h0⟩ := (isPlainFP_iff P π).1 hfp
  have hH : ∀ e, π 1 (H e) 1 = 1 := Fin.forall_fin_two.2 ⟨hM, h0⟩
  have hVH : ∀ e, (model P).Vpi π 1 (H e) = payoff 1 e := by
    intro e
    have he : π 1 (H e) 1 = 1 := hH e
    have he0 : π 1 (H e) 0 = 0 := by
      have := hπ.fin_two_zero (nt_H P e); rw [he] at this; linarith
    rw [(model P).Vpi_eq (nt_H P e), Fin.sum_univ_two, he, he0, Qpi_H, Qpi_H]
    ring
  refine ⟨?_, fun e => ?_⟩
  · unfold Model.gap
    rw [(model P).Vpi_eq (nt_root P), Fin.sum_univ_two, hlook,
      show π 0 root 1 = 0 by have := hπ.fin_two_zero (nt_root P); rw [hlook] at this; linarith,
      Qpi_root_0, hVH, hVH, payoff_10, payoff_11, Vstar_root]
    ring
  · unfold Model.gap
    rw [hVH, Vstar_H, sub_self]

/-- `w_{H_e} = 1 - δ` whenever the agent looks surely (F1: `w_{hae} = w_{ha}`, and `ξ(root, look) = 1`). -/
theorem wS_H {π : Policy (Fin 2) (Fin 2)} (hlook : π 0 root 0 = 1) (e : Fin 2) :
    (model P).wS π 1 (H e) = 1 - P.δ := by
  have hxie' : ∀ e, (model P).xie 0 root 0 e ≠ 0 :=
    Fin.forall_fin_two.2 ⟨by rw [xie_root_0_0]; exact (xiM_pos P).ne', by rw [xie_root_0_1]; linarith [xiM_lt_one P]⟩
  have hxie := hxie' e
  have hA : (model P).xiA π 0 root 0 = 1 := by
    rw [Model.xiA_eq, Model.xiS_zero, hlook, xinsA_root_0, model_δ]; ring
  unfold H
  rw [(model P).wS_ext_of_xie_ne_zero root 0 hxie, (model P).wA_of_xiA_ne_zero (by rw [hA]; exact one_ne_zero), hA,
    Model.xiS_zero, hlook, model_δ]
  ring

/-- `w_root = 1 - δ`. -/
theorem wS_root (π : Policy (Fin 2) (Fin 2)) : (model P).wS π 0 root = 1 - P.δ :=
  T1.wS_root (model P) π root

/-- **The trust bound holds at the root, `H_M` and `H_0` of every fixed point.**
Source: [[uea-2-inventory]] 2-002
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem TB_of_isPlainFP {π : Policy (Fin 2) (Fin 2)} (hfp : (model P).IsPlainFP π) :
    (model P).TB π 0 root ∧ ∀ e, (model P).TB π 1 (H e) := by
  obtain ⟨hπ, hlook, hM, h0⟩ := (isPlainFP_iff P π).1 hfp
  have hδ := P.hδ; have hδ1 := P.hδ1
  -- at `H_e`: `V_ξ(H_e) ≥ w_{H_e} payoff(two, e) = (1 - δ) V^*(H_e)`
  have hH : ∀ e, π 1 (H e) 1 = 1 := Fin.forall_fin_two.2 ⟨hM, h0⟩
  have hVxi : ∀ e, (1 - P.δ) * payoff 1 e ≤ (model P).Vxi π 1 (H e) := by
    intro e
    have he : π 1 (H e) 1 = 1 := hH e
    have he0 : π 1 (H e) 0 = 0 := by
      have := hπ.fin_two_zero (nt_H P e); rw [he] at this; linarith
    have hx : (model P).xi π 1 (H e) ≠ 0 := by
      intro hx
      have := (model P).wS_of_xi_eq_zero (π := π) hx
      rw [wS_H P hlook] at this
      linarith
    rw [Vxi_H, Fin.sum_univ_two, (model P).xia_eq_wS hπ (nt_H P e) hx, (model P).xia_eq_wS hπ (nt_H P e) hx,
      wS_H P hlook, he, he0]
    have hp0 := payoff_nonneg 0 e
    have hp1 := payoff_nonneg 1 e
    have hb0 := (model P).pibar_nonneg 1 (H e) 0
    have hb1 := (model P).pibar_nonneg 1 (H e) 1
    have hm0 := mul_nonneg (mul_nonneg hδ.le hb0) hp0
    have hm1 := mul_nonneg (mul_nonneg hδ.le hb1) hp1
    nlinarith
  refine ⟨?_, fun e => ?_⟩
  · unfold Model.TB
    rw [wS_root, Vstar_root, (model P).Mx_fin_two, Qxi_root_1, max_eq_left (Qxi_root_0_pos P π hπ).le, Qxi_root_0]
    have h0' := hVxi 0; have h1' := hVxi 1
    rw [payoff_10] at h0'; rw [payoff_11] at h1'
    have := xiM_pos P; have := xiM_lt_one P
    nlinarith
  · unfold Model.TB
    rw [wS_H P hlook, Vstar_H, Mx_H]
    have := payoff_nonneg 1 e
    nlinarith

/-! ### The true values -/

/-- `trueValue pol := Q^{ν_pol}(root, look)`: the value of `pol` against the Omega-accurate universe in which
it is the agent.
Source: `newcomb_interleaving.py` `true_value`; [[uea-2-inventory]] 2-002
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def trueValue (i : Fin 4) : ℝ := (model P).Qnu i 0 root 0

theorem Qnu_H (i : Fin 4) (e a : Fin 2) : (model P).Qnu i 1 (H e) a = payoff a e := by
  rw [(model P).Qnu_eq_of_children_terminal i (H e) a (fun e' => not_nt_two P _), Fin.sum_univ_two]
  simp [νe, r_H]

theorem Vnu_H (i : Fin 4) (e : Fin 2) : (model P).Vnu i 1 (H e) = payoff (pol i e) e := by
  rw [(model P).Vnu_eq i (nt_H P e), Fin.sum_univ_two, Qnu_H, Qnu_H]
  have hp : pol i e = 0 ∨ pol i e = 1 := by generalize pol i e = p; fin_cases p <;> simp
  rcases hp with h' | h' <;> simp [νa, h']

theorem trueValue_eq (i : Fin 4) :
    trueValue P i = pM P i * payoff (pol i 0) 0 + (1 - pM P i) * payoff (pol i 1) 1 := by
  have v0 : (model P).Vnu i 1 (ext root 0 0) = payoff (pol i 0) 0 := Vnu_H P i 0
  have v1 : (model P).Vnu i 1 (ext root 0 1) = payoff (pol i 1) 1 := Vnu_H P i 1
  unfold trueValue
  rw [Model.Qnu_eq_sum, Fin.sum_univ_two, v0, v1]
  simp [νe, r]
  try ring

/-- **The four true values**: `UDT = q MEG + (1-q) KILO`, `1box = q MEG`, `2box = (1-q) + q KILO`, `worst = 1 - q`.
Source: [[uea-2-inventory]] 2-002 (`true_value`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem trueValues :
    trueValue P 0 = P.q * MEG + (1 - P.q) * KILO ∧ trueValue P 1 = P.q * MEG ∧
      trueValue P 2 = (1 - P.q) + P.q * KILO ∧ trueValue P 3 = 1 - P.q := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [trueValue_eq] <;> simp [pol, pM, payoff_00, payoff_01, payoff_10, payoff_11]

/-- **The headline remark**: at `q = 9/10` the fixed point (2box) is Bayes-optimal for `ξ` (`gap = 0`) and its true
value `101/1001` is worst-but-one in the world (`UDT = 9001/10010`, `1box = 900/1001`, `worst = 1/10`) — the
interleaving artifact is exactly updatefulness.
Source: [[uea-2-inventory]] 2-002; [[uea-inventory]] 034
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem headline (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (f : Fin 4 → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hfsum : f 0 + f 1 + f 2 + f 3 = 1) :
    let P : TP := ⟨9 / 10, δ, f, by norm_num, by norm_num, hδ, hδ1, hf, hfsum⟩
    (model P).IsPlainFP twoBox ∧ (model P).gap twoBox 0 root = 0 ∧
      trueValue P 0 = 9001 / 10010 ∧ trueValue P 1 = 900 / 1001 ∧ trueValue P 2 = 101 / 1001 ∧
      trueValue P 3 = 1 / 10 ∧ trueValue P 3 < trueValue P 2 ∧ trueValue P 2 < trueValue P 1 ∧
      trueValue P 1 < trueValue P 0 := by
  intro P
  obtain ⟨h0, h1, h2, h3⟩ := trueValues P
  have e0 : trueValue P 0 = 9001 / 10010 := by rw [h0]; unfold MEG KILO; show (9/10 : ℝ) * (1000/1001) + (1 - 9/10) * (1/1001) = _; norm_num
  have e1 : trueValue P 1 = 900 / 1001 := by rw [h1]; unfold MEG; show (9/10 : ℝ) * (1000/1001) = _; norm_num
  have e2 : trueValue P 2 = 101 / 1001 := by rw [h2]; unfold KILO; show (1 - 9/10 : ℝ) + 9/10 * (1/1001) = _; norm_num
  have e3 : trueValue P 3 = 1 / 10 := by rw [h3]; show (1 : ℝ) - 9/10 = _; norm_num
  refine ⟨twoBox_isPlainFP P, (gap_of_isPlainFP P (twoBox_isPlainFP P)).1, e0, e1, e2, e3, ?_, ?_, ?_⟩
  · rw [e3, e2]; norm_num
  · rw [e2, e1]; norm_num
  · rw [e1, e0]; norm_num

end Transparent

end Cleanroom.Uea.UeaSinkSwim
