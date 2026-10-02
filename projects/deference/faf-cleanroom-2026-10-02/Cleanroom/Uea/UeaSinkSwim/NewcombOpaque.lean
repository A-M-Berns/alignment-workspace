import Cleanroom.Uea.UeaColeShadow.Instances

/-!
# Opaque Newcomb in the sequential model, and the `ξ`-null fallback

Payoffs scaled to `[0,1]`: `$1M ↦ MEG = 1000/1001`, `$1K ↦ KILO = 1/1001`, both `↦ 1`, nothing `↦ 0`.
Action `0 = one-box`, `1 = two-box`; percept `0 = M` (the opaque box is full), `1 = 0` (empty).

**`T = 1` models** (section `T1`): at the only decision node `Q_ξ = Q^*` for every policy, so the plain
fixed points are exactly the argmax policies, every fixed point has `gap = 0` and satisfies `TB`, and
`w_root = 1 - δ`.

**Opaque Newcomb** `Opaque.model P` (`T = 1`, hypotheses `T₁`: one-boxes, `M` w.p. `q` regardless of the
action; `T₂`: two-boxes, `M` w.p. `1-q`; `T₃`: uniform action, uniform percept; shares `f₀ f₁ f₂` of `δ`):
the percept kernel `ξ(e|a)` is policy-free (F1 makes the correlation live in `ξ(e|a)`), and with
`f = (1/2, 1/2, 0)` one-box is the unique plain fixed point iff `q > 1001/2000`, two-box iff
`q < 1001/2000`, and at `q = 1001/2000` every policy is a fixed point — three-way, exact.

**2-003**: with the class `{T₁}` alone the action `two` is `ξ_{-S}`-null, so its percept kernel is the
**fallback** `∑ wᵢ νeᵢ/δ = T₁`'s kernel, `ξ(M|two) = q`, and two-box is the unique fixed point for every `q`.
(c) disclosure: the fixed-point set is a function of the `ξ`-null-action convention (the continuous
extension of `uea-cole-shadow` target 1), not only of the instance; "opaque Newcomb one-boxes" is
convention-dependent when the class lacks a two-boxing hypothesis.

Scope: finite shadow of rOSI ([[sequential-self-game]] §7). Namespace
`Cleanroom.Uea.UeaSinkSwim.{Newcomb, T1, Opaque}` (faf-cleanroom run, `uea-sink-swim`, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Finset
open Cleanroom.Uea.UeaColeShadow

namespace Newcomb

/-- `$1M` scaled: `1000/1001`. -/
noncomputable def MEG : ℝ := 1000 / 1001
/-- `$1K` scaled: `1/1001`. -/
noncomputable def KILO : ℝ := 1 / 1001

/-- The terminal payoff of action `a` (`0 = one`, `1 = two`) given the box content `e` (`0 = M`, `1 = empty`):
`one, M ↦ MEG`, `two, M ↦ 1`, `two, 0 ↦ KILO`, `one, 0 ↦ 0`.
Source: `newcomb_interleaving.py` `payoff`; [[uea-2-inventory]] 2-001
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def payoff (a e : Fin 2) : ℝ := (if e = 0 then MEG else 0) + (if a = 1 then KILO else 0)

theorem payoff_00 : payoff 0 0 = MEG := by simp [payoff]
theorem payoff_10 : payoff 1 0 = 1 := by simp [payoff, MEG, KILO]; norm_num
theorem payoff_01 : payoff 0 1 = 0 := by simp [payoff]
theorem payoff_11 : payoff 1 1 = KILO := by simp [payoff]

theorem payoff_nonneg (a e : Fin 2) : 0 ≤ payoff a e := by
  unfold payoff MEG KILO; split_ifs <;> norm_num

theorem payoff_le_one (a e : Fin 2) : payoff a e ≤ 1 := by
  unfold payoff MEG KILO; split_ifs <;> norm_num

end Newcomb

/-! ### `T = 1` models: fixed points are the argmax policies -/

namespace T1

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι) (hT : M.T = 1)
include hT

omit [Nonempty A] in
theorem not_nt_succ (n : ℕ) (h : Hist A E (n + 1)) : ¬ M.nonterminal (n + 1) h := fun h' => by
  have := h'.1; omega

/-- At `T = 1`, `Q_ξ(root, a) = Q^*(root, a)` for every policy. -/
theorem Qxi_eq_Qstar (π : Policy A E) (h : Hist A E 0) (a : A) : M.Qxi π 0 h a = M.Qstar 0 h a := by
  rw [M.Qxi_eq_of_children_terminal h a (fun e => not_nt_succ M hT 0 _),
    M.Qstar_eq_of_children_terminal h a (fun e => not_nt_succ M hT 0 _)]

theorem Qpi_eq_Qstar (π : Policy A E) (h : Hist A E 0) (a : A) : M.Qpi π 0 h a = M.Qstar 0 h a := by
  rw [M.Qpi_eq_of_children_terminal h a (fun e => not_nt_succ M hT 0 _),
    M.Qstar_eq_of_children_terminal h a (fun e => not_nt_succ M hT 0 _)]

theorem Mx_eq_Vstar (π : Policy A E) {h : Hist A E 0} (hnt : M.nonterminal 0 h) : M.Mx π 0 h = M.Vstar 0 h := by
  rw [M.Vstar_eq hnt]
  unfold Model.Mx
  exact congrArg _ (funext (Qxi_eq_Qstar M hT π h))

omit [Nonempty A] hT in
/-- The root's self-posterior is the prior `1 - δ` under every policy. -/
theorem wS_root (π : Policy A E) (h : Hist A E 0) : M.wS π 0 h = 1 - M.δ := by
  have hx : M.xi π 0 h = 1 := by
    unfold Model.xi Model.xins
    simp only [Model.nuJoint_zero, mul_one, Model.xiS_zero, M.w_sum]
    ring
  rw [Model.wS_of_xi_ne_zero _ (by rw [hx]; exact one_ne_zero), hx, Model.xiS_zero]
  ring

/-- **`T = 1` fixed points**: `π` is a plain fixed point iff it is a policy and its support at the root lies in
`argmax Q^*`.
Source: mandate target 10 ("general `L` lemma for `T = 1` models")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem isPlainFP_iff (π : Policy A E) : M.IsPlainFP π ↔
    M.IsPolicy π ∧ ∀ h : Hist A E 0, M.nonterminal 0 h → ∀ a, 0 < π 0 h a → M.Qstar 0 h a = M.Vstar 0 h := by
  constructor
  · rintro ⟨hπ, hfp⟩
    refine ⟨hπ, fun h hnt a ha => ?_⟩
    rw [← Qxi_eq_Qstar M hT π h a, ← Mx_eq_Vstar M hT π hnt]
    exact hfp 0 h hnt a ha
  · rintro ⟨hπ, hfp⟩
    refine ⟨hπ, fun n h hnt => ?_⟩
    match n with
    | 0 =>
      intro a ha
      rw [Qxi_eq_Qstar M hT π h a, Mx_eq_Vstar M hT π hnt]
      exact hfp h hnt a ha
    | n + 1 => exact absurd hnt (not_nt_succ M hT n h)

/-- Every fixed point of a `T = 1` model has `gap = 0` at the root.
Source: mandate target 10
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem gap_eq_zero {π : Policy A E} (hfp : M.IsPlainFP π) {h : Hist A E 0} (hnt : M.nonterminal 0 h) :
    M.gap π 0 h = 0 := by
  have hπ := hfp.1
  obtain ⟨_, hfx⟩ := (isPlainFP_iff M hT π).1 hfp
  unfold Model.gap
  rw [M.Vpi_eq_sum_supp hπ hnt]
  have hQ : ∀ a ∈ supp π 0 h, M.Qpi π 0 h a = M.Vstar 0 h := by
    intro a ha
    rw [Model.mem_supp] at ha
    rw [Qpi_eq_Qstar M hT π h a]
    exact hfx h hnt a ha
  rw [sum_congr rfl fun a ha => by rw [hQ a ha], ← sum_mul, M.sum_supp_eq_one hπ hnt, one_mul, sub_self]

/-- Every fixed point of a `T = 1` model satisfies the trust bound at the root (`M = V^* ≥ w V^*`).
Source: mandate target 10
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem TB_root {π : Policy A E} (hfp : M.IsPlainFP π) {h : Hist A E 0} (hnt : M.nonterminal 0 h) :
    M.TB π 0 h := by
  unfold Model.TB
  rw [Mx_eq_Vstar M hT π hnt]
  have h1 := M.wS_le_one hfp.1 hnt
  have h2 := M.Vstar_nonneg 0 h
  nlinarith

end T1

/-! ### Opaque Newcomb -/

namespace Opaque

open Newcomb

/-- Parameters: Omega's accuracy `q ∈ [0,1]`, non-self prior `δ ∈ (0,1)`, shares `f 0, f 1, f 2 ≥ 0` summing to
`1` of `T₁` (one-boxer), `T₂` (two-boxer), `T₃` (random).
Source: `newcomb_interleaving.py` `opaque_newcomb`; [[uea-2-inventory]] 2-001
Kind: D
Fidelity: exact
Hyps: n/a -/
structure OP where
  q : ℝ
  δ : ℝ
  f : Fin 3 → ℝ
  hq0 : 0 ≤ q
  hq1 : q ≤ 1
  hδ : 0 < δ
  hδ1 : δ < 1
  hf : ∀ i, 0 ≤ f i
  hfsum : f 0 + f 1 + f 2 = 1

variable (P : OP)

def alive : (n : ℕ) → Hist (Fin 2) (Fin 2) n → Bool
  | 0, _ => true
  | _ + 1, _ => false

noncomputable def r : (n : ℕ) → Hist (Fin 2) (Fin 2) (n + 1) → ℝ
  | 0, h => payoff (h 0).1 (h 0).2
  | _ + 1, _ => 0

/-- Action kernels: `T₁` one-boxes, `T₂` two-boxes, `T₃` is uniform. -/
noncomputable def νa : Fin 3 → (n : ℕ) → Hist (Fin 2) (Fin 2) n → Fin 2 → ℝ := fun i _ _ a =>
  if i = 0 then (if a = 0 then 1 else 0) else if i = 1 then (if a = 1 then 1 else 0) else 1 / 2

/-- Percept kernels: `T₁`: `M` w.p. `q`; `T₂`: `M` w.p. `1 - q`; `T₃`: uniform — regardless of the action
(the content is fixed before the choice). -/
noncomputable def νe (q : ℝ) : Fin 3 → (n : ℕ) → Hist (Fin 2) (Fin 2) n → Fin 2 → Fin 2 → ℝ := fun i _ _ _ e =>
  if i = 0 then (if e = 0 then q else 1 - q) else if i = 1 then (if e = 0 then 1 - q else q) else 1 / 2

theorem νa_mem (i : Fin 3) (n : ℕ) (h : Hist (Fin 2) (Fin 2) n) : νa i n h ∈ stdSimplex ℝ (Fin 2) := by
  refine ⟨fun a => ?_, ?_⟩
  · unfold νa; split_ifs <;> norm_num
  · fin_cases i <;> simp [νa, Fin.sum_univ_two]

theorem νe_mem (i : Fin 3) (n : ℕ) (h : Hist (Fin 2) (Fin 2) n) (a : Fin 2) :
    νe P.q i n h a ∈ stdSimplex ℝ (Fin 2) := by
  have := P.hq0; have := P.hq1
  refine ⟨fun e => ?_, ?_⟩
  · unfold νe; split_ifs <;> linarith
  · fin_cases i <;> simp [νe, Fin.sum_univ_two]

theorem r_nonneg (n : ℕ) (h : Hist (Fin 2) (Fin 2) (n + 1)) : 0 ≤ r n h := by
  match n with
  | 0 => exact payoff_nonneg _ _
  | n + 1 => exact le_rfl

theorem norm (n : ℕ) (hn : n ≤ 1) (h : Hist (Fin 2) (Fin 2) n) : pathReturnOf 1 r n h ≤ 1 := by
  match n with
  | 0 => simp
  | 1 =>
    simp only [pathReturnOf, pow_zero, one_mul, zero_add]
    exact payoff_le_one _ _
  | n + 2 => omega

/-- **Opaque Newcomb** `model P`: `T = 1`, `γ = 1`, weights `δ f i`.
Source: `newcomb_interleaving.py` `opaque_newcomb`; [[uea-2-inventory]] 2-001; [[uea-inventory]] 034
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def model : Model (Fin 2) (Fin 2) (Fin 3) where
  T := 1
  alive := alive
  alive_init := fun n h hh => by simp [alive] at hh
  r := r
  r_nonneg := r_nonneg
  γ := 1
  γ_pos := one_pos
  γ_le_one := le_rfl
  norm := norm
  νa := νa
  νe := νe P.q
  νa_mem := νa_mem
  νe_mem := νe_mem P
  w := fun i => P.δ * P.f i
  w_nonneg := fun i => mul_nonneg P.hδ.le (P.hf i)
  δ := P.δ
  w_sum := by rw [← mul_sum, Fin.sum_univ_three, P.hfsum, mul_one]
  δ_pos := P.hδ
  δ_lt_one := P.hδ1

/-- The root. -/
def root : Hist (Fin 2) (Fin 2) 0 := Fin.elim0

@[simp] theorem model_T : (model P).T = 1 := rfl
@[simp] theorem model_δ : (model P).δ = P.δ := rfl
@[simp] theorem model_r : (model P).r = r := rfl
@[simp] theorem model_γ : (model P).γ = 1 := rfl
@[simp] theorem model_w (i : Fin 3) : (model P).w i = P.δ * P.f i := rfl
@[simp] theorem model_νa : (model P).νa = νa := rfl
@[simp] theorem model_νe : (model P).νe = νe P.q := rfl

theorem nt_root : (model P).nonterminal 0 root := ⟨by simp, rfl⟩
theorem eq_root (h : Hist (Fin 2) (Fin 2) 0) : h = root := funext fun i => Fin.elim0 i

theorem xinsA_root_0 : (model P).xinsA 0 root 0 = P.δ * (P.f 0 + P.f 2 / 2) := by
  simp [Model.xinsA, Fin.sum_univ_three, νa]; ring

theorem xinsA_root_1 : (model P).xinsA 0 root 1 = P.δ * (P.f 1 + P.f 2 / 2) := by
  simp [Model.xinsA, Fin.sum_univ_three, νa]; ring

/-- **`ξ(M|one)` is policy-free**: `ξ(M|one) = (f₀ q + f₂/4) / (f₀ + f₂/2)` when the one-boxers have mass
(F1 makes the correlation live in `ξ(e|a)`).
Source: [[uea-2-inventory]] 2-001 (`opaque_report`'s `xiM_one`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem xie_root_0_0 (hf : P.f 0 + P.f 2 / 2 ≠ 0) :
    (model P).xie 0 root 0 0 = (P.f 0 * P.q + P.f 2 / 4) / (P.f 0 + P.f 2 / 2) := by
  have hδ := P.hδ.ne'
  unfold Model.xie
  rw [if_neg (by rw [xinsA_root_0]; exact mul_ne_zero hδ hf), xinsA_root_0]
  simp only [Fin.sum_univ_three, Model.nuJoint_zero]
  show (P.δ * P.f 0 * 1 * νa 0 0 root 0 * νe P.q 0 0 root 0 0 + P.δ * P.f 1 * 1 * νa 1 0 root 0 * νe P.q 1 0 root 0 0 +
    P.δ * P.f 2 * 1 * νa 2 0 root 0 * νe P.q 2 0 root 0 0) / (P.δ * (P.f 0 + P.f 2 / 2)) = _
  simp only [νa, νe]
  simp
  field_simp
  ring

/-- `ξ(M|two) = (f₁ (1-q) + f₂/4) / (f₁ + f₂/2)` when the two-boxers have mass.
Source: [[uea-2-inventory]] 2-001
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem xie_root_1_0 (hf : P.f 1 + P.f 2 / 2 ≠ 0) :
    (model P).xie 0 root 1 0 = (P.f 1 * (1 - P.q) + P.f 2 / 4) / (P.f 1 + P.f 2 / 2) := by
  have hδ := P.hδ.ne'
  unfold Model.xie
  rw [if_neg (by rw [xinsA_root_1]; exact mul_ne_zero hδ hf), xinsA_root_1]
  simp only [Fin.sum_univ_three, Model.nuJoint_zero]
  show (P.δ * P.f 0 * 1 * νa 0 0 root 1 * νe P.q 0 0 root 1 0 + P.δ * P.f 1 * 1 * νa 1 0 root 1 * νe P.q 1 0 root 1 0 +
    P.δ * P.f 2 * 1 * νa 2 0 root 1 * νe P.q 2 0 root 1 0) / (P.δ * (P.f 1 + P.f 2 / 2)) = _
  simp only [νa, νe]
  simp
  field_simp
  ring

/-- `Q^*(root, a) = ∑_e ξ(e|a) payoff(a, e)`. -/
theorem Qstar_root (a : Fin 2) : (model P).Qstar 0 root a = ∑ e, (model P).xie 0 root a e * payoff a e := by
  rw [(model P).Qstar_eq_of_children_terminal root a (fun e => T1.not_nt_succ (model P) rfl 0 _)]
  refine sum_congr rfl fun e _ => ?_
  simp [r]

theorem xie_root_sum (a : Fin 2) : (model P).xie 0 root a 0 + (model P).xie 0 root a 1 = 1 := by
  have := (model P).xie_sum 0 root a
  rwa [Fin.sum_univ_two] at this

theorem Qstar_root_0 : (model P).Qstar 0 root 0 = (model P).xie 0 root 0 0 * MEG := by
  rw [Qstar_root, Fin.sum_univ_two, payoff_00, payoff_01, mul_zero, add_zero]

theorem Qstar_root_1 : (model P).Qstar 0 root 1 = (model P).xie 0 root 1 0 * 1 + (1 - (model P).xie 0 root 1 0) * KILO := by
  rw [Qstar_root, Fin.sum_univ_two, payoff_10, payoff_11]
  have := xie_root_sum P 1
  congr 2
  linarith

/-! ### The symmetric class `f = (1/2, 1/2, 0)`: the three-way threshold -/

/-- The symmetric class: `f = (1/2, 1/2, 0)`. -/
noncomputable def half (q δ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1) : OP :=
  ⟨q, δ, fun i => if i = 2 then 0 else 1 / 2, hq0, hq1, hδ, hδ1, fun i => by split_ifs <;> norm_num,
    by rw [if_neg (by decide), if_neg (by decide), if_pos rfl]; norm_num⟩

section Half
variable (q δ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1)

theorem half_xie_0 : (model (half q δ hq0 hq1 hδ hδ1)).xie 0 root 0 0 = q := by
  rw [xie_root_0_0 _ (by simp [half])]
  simp [half]
  ring

theorem half_xie_1 : (model (half q δ hq0 hq1 hδ hδ1)).xie 0 root 1 0 = 1 - q := by
  rw [xie_root_1_0 _ (by simp [half])]
  simp [half]
  ring

theorem half_Qstar_0 : (model (half q δ hq0 hq1 hδ hδ1)).Qstar 0 root 0 = q * MEG := by
  rw [Qstar_root_0, half_xie_0]

theorem half_Qstar_1 : (model (half q δ hq0 hq1 hδ hδ1)).Qstar 0 root 1 = (1 - q) + q * KILO := by
  rw [Qstar_root_1, half_xie_1]
  ring

/-- `Q^*(one) - Q^*(two) = (2000 q - 1001)/1001`: the sign is the sign of `q - 1001/2000`. -/
theorem half_Qstar_diff :
    (model (half q δ hq0 hq1 hδ hδ1)).Qstar 0 root 0 - (model (half q δ hq0 hq1 hδ hδ1)).Qstar 0 root 1 =
      (2000 * q - 1001) / 1001 := by
  rw [half_Qstar_0, half_Qstar_1]
  unfold MEG KILO
  ring

/-- **Opaque Newcomb, three-way, exact**: with `f = (1/2, 1/2, 0)`, one-box is the unique plain fixed point
iff `q > 1001/2000`, two-box iff `q < 1001/2000`, and at `q = 1001/2000` every policy is a fixed point (tie).
"Unique" is "the fixed points are exactly the policies with that action sure at the root".
Source: [[uea-2-inventory]] 2-001 (`opaque_threshold_check`: "one-box iff q > 1001/2000"); [[uea-inventory]] 034
Kind: P
Fidelity: exact (both directions in each regime; the (c) of the null-action convention does not enter here:
both root actions carry residual mass)
Hyps: (a) -/
theorem half_fixedPoints (π : Policy (Fin 2) (Fin 2)) :
    (1001 / 2000 < q → ((model (half q δ hq0 hq1 hδ hδ1)).IsPlainFP π ↔
        (model (half q δ hq0 hq1 hδ hδ1)).IsPolicy π ∧ π 0 root 0 = 1)) ∧
    (q < 1001 / 2000 → ((model (half q δ hq0 hq1 hδ hδ1)).IsPlainFP π ↔
        (model (half q δ hq0 hq1 hδ hδ1)).IsPolicy π ∧ π 0 root 1 = 1)) ∧
    (q = 1001 / 2000 → ((model (half q δ hq0 hq1 hδ hδ1)).IsPlainFP π ↔
        (model (half q δ hq0 hq1 hδ hδ1)).IsPolicy π)) := by
  set M := model (half q δ hq0 hq1 hδ hδ1) with hM
  have hdiff := half_Qstar_diff q δ hq0 hq1 hδ hδ1
  rw [← hM] at hdiff
  have hV : M.Vstar 0 root = max (M.Qstar 0 root 0) (M.Qstar 0 root 1) := M.Vstar_fin_two (nt_root _)
  rw [T1.isPlainFP_iff M rfl π]
  -- reduce the root quantifier to `root`
  have hred : (∀ h : Hist (Fin 2) (Fin 2) 0, M.nonterminal 0 h → ∀ a, 0 < π 0 h a → M.Qstar 0 h a = M.Vstar 0 h) ↔
      ∀ a, 0 < π 0 root a → M.Qstar 0 root a = M.Vstar 0 root := by
    constructor
    · intro H a ha; exact H root (nt_root _) a ha
    · intro H h _ a ha; rw [eq_root h] at ha ⊢; exact H a ha
  rw [hred]
  refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_⟩
  · have hlt : M.Qstar 0 root 1 < M.Qstar 0 root 0 := by linarith
    have hV' : M.Vstar 0 root = M.Qstar 0 root 0 := by rw [hV]; exact max_eq_left hlt.le
    constructor
    · rintro ⟨hπ, H⟩
      refine ⟨hπ, ?_⟩
      have h1 : π 0 root 1 = 0 := by
        by_contra hne
        have hpos : 0 < π 0 root 1 := lt_of_le_of_ne (hπ.nonneg (nt_root _) 1) (Ne.symm hne)
        have := H 1 hpos
        rw [hV'] at this
        linarith
      rw [hπ.fin_two_zero (nt_root _), h1, sub_zero]
    · rintro ⟨hπ, h0⟩
      refine ⟨hπ, ?_⟩
      refine Fin.forall_fin_two.2 ⟨fun _ => hV'.symm, fun h1 => ?_⟩
      have := hπ.fin_two_zero (nt_root _); rw [h0] at this; linarith
  · have hlt : M.Qstar 0 root 0 < M.Qstar 0 root 1 := by linarith
    have hV' : M.Vstar 0 root = M.Qstar 0 root 1 := by rw [hV]; exact max_eq_right hlt.le
    constructor
    · rintro ⟨hπ, H⟩
      refine ⟨hπ, ?_⟩
      have h0 : π 0 root 0 = 0 := by
        by_contra hne
        have hpos : 0 < π 0 root 0 := lt_of_le_of_ne (hπ.nonneg (nt_root _) 0) (Ne.symm hne)
        have := H 0 hpos
        rw [hV'] at this
        linarith
      have := hπ.fin_two_zero (nt_root _); rw [h0] at this; linarith
    · rintro ⟨hπ, h1⟩
      refine ⟨hπ, ?_⟩
      refine Fin.forall_fin_two.2 ⟨fun h0 => ?_, fun _ => hV'.symm⟩
      have := hπ.fin_two_zero (nt_root _); rw [h1] at this; linarith
  · have heq : M.Qstar 0 root 0 = M.Qstar 0 root 1 := by rw [hq] at hdiff; linarith
    have hV' : M.Vstar 0 root = M.Qstar 0 root 0 := by rw [hV, heq, max_self]
    constructor
    · exact fun h => h.1
    · intro hπ
      refine ⟨hπ, Fin.forall_fin_two.2 ⟨fun _ => hV'.symm, fun _ => by rw [hV', heq]⟩⟩

end Half

/-- **N+ data**: `q = 9/10, δ = 1/10, f = (1/2, 1/2, 0)`: `Q_ξ(one) = 900/1001`, `Q_ξ(two) = 101/1001`, one-box
is the unique fixed point, and every fixed point has `gap = 0` with `TB` and `w_root = 9/10`.
Source: [[uea-2-inventory]] 2-001 (`opaque_report` at `q = 9/10`)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem witness :
    let M := model (half (9 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    M.Qstar 0 root 0 = 900 / 1001 ∧ M.Qstar 0 root 1 = 101 / 1001 ∧
      (∀ π, M.IsPlainFP π ↔ M.IsPolicy π ∧ π 0 root 0 = 1) ∧
      (∀ π, M.IsPlainFP π → M.gap π 0 root = 0 ∧ M.TB π 0 root ∧ M.wS π 0 root = 9 / 10) := by
  intro M
  refine ⟨?_, ?_, fun π => (half_fixedPoints _ _ _ _ _ _ π).1 (by norm_num), fun π hfp => ?_⟩
  · rw [half_Qstar_0]; unfold MEG; norm_num
  · rw [half_Qstar_1]; unfold KILO; norm_num
  · refine ⟨T1.gap_eq_zero M rfl hfp (nt_root _), T1.TB_root M rfl hfp (nt_root _), ?_⟩
    rw [T1.wS_root M π root]
    show (1:ℝ) - 1 / 10 = 9 / 10
    norm_num

/-! ### 2-003: the class `{T₁}` alone — the `ξ`-null fallback decides -/

/-- The one-hypothesis class `f = (1, 0, 0)` (2-003's `modelT1`). -/
noncomputable def onlyT1 (q δ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1) : OP :=
  ⟨q, δ, fun i => if i = 0 then 1 else 0, hq0, hq1, hδ, hδ1, fun i => by split_ifs <;> norm_num,
    by rw [if_pos rfl, if_neg (by decide), if_neg (by decide)]; norm_num⟩

section OnlyT1
variable (q δ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1)

/-- `two` is `ξ_{-S}`-null in the class `{T₁}`. -/
theorem onlyT1_xinsA_1 : (model (onlyT1 q δ hq0 hq1 hδ hδ1)).xinsA 0 root 1 = 0 := by
  rw [xinsA_root_1]; simp [onlyT1]

/-- **The fallback kernel**: `ξ(M|two) = q` — `T₁`'s own percept kernel, by the prior-weighted fallback
`∑ wᵢ νeᵢ/δ` at the `ξ_{-S}`-null action.
Source: [[uea-2-inventory]] 2-003
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem onlyT1_xie_1 : (model (onlyT1 q δ hq0 hq1 hδ hδ1)).xie 0 root 1 0 = q := by
  unfold Model.xie
  rw [if_pos (onlyT1_xinsA_1 q δ hq0 hq1 hδ hδ1)]
  simp only [Fin.sum_univ_three]
  show (δ * 1 * νe q 0 0 root 1 0 + δ * 0 * νe q 1 0 root 1 0 + δ * 0 * νe q 2 0 root 1 0) / δ = q
  simp [νe]
  field_simp

theorem onlyT1_xie_0 : (model (onlyT1 q δ hq0 hq1 hδ hδ1)).xie 0 root 0 0 = q := by
  rw [xie_root_0_0 _ (by simp [onlyT1])]
  simp [onlyT1]

/-- **2-003**: in the class `{T₁}`, `Q_ξ(two) = q + (1-q) KILO > q MEG = Q_ξ(one)` for every `q ∈ [0,1]`
(the difference is `1/1001`), so two-box is the unique plain fixed point. The `ξ`-null-action convention,
not the instance, decides: (c) disclosure — the fixed-point set is a function of the convention.
Source: [[uea-2-inventory]] 2-003; [[uea-inventory]] 034
Kind: P
Fidelity: exact
Hyps: (c) the continuous extension / prior-weighted fallback at `ξ_{-S}`-null actions is the model's
convention (`uea-cole-shadow` target 1, F8); the note's "opaque Newcomb one-boxes" needs a two-boxing hypothesis -/
theorem onlyT1_fixedPoints (π : Policy (Fin 2) (Fin 2)) :
    (model (onlyT1 q δ hq0 hq1 hδ hδ1)).Qstar 0 root 1 - (model (onlyT1 q δ hq0 hq1 hδ hδ1)).Qstar 0 root 0 = 1 / 1001 ∧
    ((model (onlyT1 q δ hq0 hq1 hδ hδ1)).IsPlainFP π ↔
      (model (onlyT1 q δ hq0 hq1 hδ hδ1)).IsPolicy π ∧ π 0 root 1 = 1) := by
  set M := model (onlyT1 q δ hq0 hq1 hδ hδ1) with hM
  have hdiff : M.Qstar 0 root 1 - M.Qstar 0 root 0 = 1 / 1001 := by
    rw [hM, Qstar_root_1, Qstar_root_0, onlyT1_xie_1, onlyT1_xie_0]
    unfold MEG KILO; ring
  refine ⟨hdiff, ?_⟩
  have hlt : M.Qstar 0 root 0 < M.Qstar 0 root 1 := by linarith
  have hV : M.Vstar 0 root = M.Qstar 0 root 1 := by
    rw [M.Vstar_fin_two (nt_root _)]; exact max_eq_right hlt.le
  rw [T1.isPlainFP_iff M rfl π]
  constructor
  · rintro ⟨hπ, H⟩
    refine ⟨hπ, ?_⟩
    have h0 : π 0 root 0 = 0 := by
      by_contra hne
      have hpos : 0 < π 0 root 0 := lt_of_le_of_ne (hπ.nonneg (nt_root _) 0) (Ne.symm hne)
      have := H root (nt_root _) 0 hpos
      rw [hV] at this
      linarith
    have := hπ.fin_two_zero (nt_root _); rw [h0] at this; linarith
  · rintro ⟨hπ, h1⟩
    refine ⟨hπ, fun h _ => ?_⟩
    rw [eq_root h]
    refine Fin.forall_fin_two.2 ⟨fun h0 => ?_, fun _ => hV.symm⟩
    have := hπ.fin_two_zero (nt_root _); rw [h1] at this; linarith

end OnlyT1

end Opaque

end Cleanroom.Uea.UeaSinkSwim
