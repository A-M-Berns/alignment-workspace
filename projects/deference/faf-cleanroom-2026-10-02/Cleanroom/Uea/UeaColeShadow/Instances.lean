import Cleanroom.Uea.UeaColeShadow.TheoremB

/-!
# Instances A and B: exact computations — the refutation of Cole's key lemma in the finite shadow

Both instances are from [[oracle-side-gaps-reaudit]] (lines 18–43): deterministic percepts (`E = Unit`),
`γ = 1`, no uniform randomizer (`u = 0`), rewards on arrival (the reaudit's terminal rewards embed).

**Instance B** (three steps): root `stay` (`0.7`) / `go`; after `go` (node `n₁`) `stay` (`0.85`) / `jump`;
after `jump` (the water) `swim` (`1`) / `sink` (`0`). `δ = 0.2`; one residual hypothesis playing `go`,
`jump`, `sink`. Actions are `Fin 2` with `1` = go / jump / sink (the residual's action everywhere) and
`0` = stay / stay / swim. State `(j, k) = (π(go|root), π(jump|n₁))`, and `s = π(swim|water)`.

Results: `𝒜_{n₁} = {stay}` for all `(j,k)` and `TB_{n₁}` always holds; `Q_ξ(root, go) ≤ 0.8` with equality
iff `(j,k) = (1,1)` (at `s = 1`); the unique plain fixed point is `(0,0)` (with `s = 1`), value `0.7`, where
`TB_root` fails, loss `0.3 = 1.5 δ`; the floored agent's unique fixed point is `(1,0)`, the floor firing
strictly at the root, value `0.85`. Hence the finite shadow of the post's key lemma — some plain fixed point
satisfies the trust bound everywhere — is refuted.

Scope: finite shadow of rOSI — finite horizon and hypothesis class, fixed points for oracles, continuous
extension at `ξ`-null nodes ([[sequential-self-game]] §7).
-/

namespace Cleanroom.Uea.UeaColeShadow

open Finset

namespace Model

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι)
  {π : Policy A E}

/-! ### Generic evaluation helpers -/

/-- At a node all of whose children are terminal, `Q_ξ` is the expected immediate reward. -/
theorem Qxi_eq_of_children_terminal {n : ℕ} (h : Hist A E n) (a : A)
    (hc : ∀ e, ¬ M.nonterminal (n + 1) (ext h a e)) :
    M.Qxi π n h a = ∑ e, M.xie n h a e * (M.γ ^ n * M.r n (ext h a e)) := by
  rw [Qxi_eq_sum]
  exact sum_congr rfl fun e _ => by rw [M.Vxi_of_not_nonterminal (hc e), add_zero]

theorem Qpi_eq_of_children_terminal {n : ℕ} (h : Hist A E n) (a : A)
    (hc : ∀ e, ¬ M.nonterminal (n + 1) (ext h a e)) :
    M.Qpi π n h a = ∑ e, M.xie n h a e * (M.γ ^ n * M.r n (ext h a e)) := by
  rw [Qpi_eq_sum]
  exact sum_congr rfl fun e _ => by rw [M.Vpi_of_not_nonterminal (hc e), add_zero]

theorem Qstar_eq_of_children_terminal {n : ℕ} (h : Hist A E n) (a : A)
    (hc : ∀ e, ¬ M.nonterminal (n + 1) (ext h a e)) :
    M.Qstar n h a = ∑ e, M.xie n h a e * (M.γ ^ n * M.r n (ext h a e)) := by
  rw [Qstar_eq_sum]
  exact sum_congr rfl fun e _ => by rw [M.Vstar_of_not_nonterminal (hc e), add_zero]

theorem Qnu_eq_of_children_terminal (i : ι) {n : ℕ} (h : Hist A E n) (a : A)
    (hc : ∀ e, ¬ M.nonterminal (n + 1) (ext h a e)) :
    M.Qnu i n h a = ∑ e, M.νe i n h a e * (M.γ ^ n * M.r n (ext h a e)) := by
  rw [Qnu_eq_sum]
  exact sum_congr rfl fun e _ => by rw [M.Vnu_of_not_nonterminal i (hc e), add_zero]

/-- With a single percept the percept kernel is identically `1`. -/
theorem xie_eq_one_of_unique [Unique E] (n : ℕ) (h : Hist A E n) (a : A) (e : E) :
    M.xie n h a e = 1 := by
  have := M.xie_sum n h a
  rw [Fintype.sum_unique] at this
  rwa [Subsingleton.elim e default]

/-- `sup'` over `Fin 2` is the `max`. -/
theorem sup'_fin_two (f : Fin 2 → ℝ) : (univ : Finset (Fin 2)).sup' univ_nonempty f = max (f 0) (f 1) := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun b _ => by fin_cases b <;> simp
  · exact max_le (le_sup' f (mem_univ 0)) (le_sup' f (mem_univ 1))

theorem Mx_fin_two {E ι : Type*} [Fintype E] [Fintype ι] (M : Model (Fin 2) E ι) (π : Policy (Fin 2) E)
    (n : ℕ) (h : Hist (Fin 2) E n) : M.Mx π n h = max (M.Qxi π n h 0) (M.Qxi π n h 1) :=
  sup'_fin_two _

theorem Vstar_fin_two {E ι : Type*} [Fintype E] [Fintype ι] (M : Model (Fin 2) E ι) {n : ℕ}
    {h : Hist (Fin 2) E n} (hnt : M.nonterminal n h) :
    M.Vstar n h = max (M.Qstar n h 0) (M.Qstar n h 1) := by
  rw [M.Vstar_eq hnt]
  exact sup'_fin_two _

/-- A policy over `Fin 2` puts `1 - π(1|h)` on action `0` at decision nodes. -/
theorem IsPolicy.fin_two_zero {E ι : Type*} [Fintype E] [Fintype ι] {M : Model (Fin 2) E ι}
    {π : Policy (Fin 2) E} (hπ : M.IsPolicy π) {n : ℕ} {h : Hist (Fin 2) E n} (hnt : M.nonterminal n h) :
    π n h 0 = 1 - π n h 1 := by
  have := hπ.sum hnt
  rw [Fin.sum_univ_two] at this
  linarith

end Model

/-! ### Instance B -/

namespace InstB

/-- Alive nodes: the root; `go`; `go, jump`. -/
def alive : (n : ℕ) → Hist (Fin 2) Unit n → Bool
  | 0, _ => true
  | 1, h => decide ((h 0).1 = 1)
  | 2, h => decide ((h 0).1 = 1 ∧ (h 1).1 = 1)
  | _, _ => false

/-- Rewards on arrival: `stay` at the root `0.7`; `go, stay` `0.85`; `go, jump, swim` `1`. -/
noncomputable def r : (n : ℕ) → Hist (Fin 2) Unit (n + 1) → ℝ
  | 0, h => if (h 0).1 = 0 then 7 / 10 else 0
  | 1, h => if (h 0).1 = 1 ∧ (h 1).1 = 0 then 17 / 20 else 0
  | 2, h => if (h 0).1 = 1 ∧ (h 1).1 = 1 ∧ (h 2).1 = 0 then 1 else 0
  | _, _ => 0

/-- The residual's action kernel: action `1` (go / jump / sink) surely, everywhere. -/
noncomputable def νa : Unit → (n : ℕ) → Hist (Fin 2) Unit n → Fin 2 → ℝ :=
  fun _ _ _ a => if a = 1 then 1 else 0

theorem νa_mem (i : Unit) (n : ℕ) (h : Hist (Fin 2) Unit n) : νa i n h ∈ stdSimplex ℝ (Fin 2) := by
  refine ⟨fun a => ?_, ?_⟩
  · unfold νa; split_ifs <;> norm_num
  · simp [νa, Fin.sum_univ_two]

theorem r_nonneg (n : ℕ) (h : Hist (Fin 2) Unit (n + 1)) : 0 ≤ r n h := by
  match n with
  | 0 => simp only [r]; split_ifs <;> norm_num
  | 1 => simp only [r]; split_ifs <;> norm_num
  | 2 => simp only [r]; split_ifs <;> norm_num
  | n + 3 => simp [r]

theorem alive_init (n : ℕ) (h : Hist (Fin 2) Unit (n + 1)) (hh : alive (n + 1) h = true) :
    alive n (Fin.init h) = true := by
  match n with
  | 0 => rfl
  | 1 =>
    simp only [alive, decide_eq_true_eq] at hh ⊢
    simp [Fin.init, hh.1]
  | n + 2 => simp [alive] at hh

theorem norm (n : ℕ) (hn : n ≤ 3) (h : Hist (Fin 2) Unit n) : pathReturnOf 1 r n h ≤ 1 := by
  match n with
  | 0 => simp
  | 1 =>
    simp only [pathReturnOf, r]
    split_ifs <;> norm_num
  | 2 =>
    simp only [pathReturnOf, r, Fin.init, Fin.castSucc_zero, Fin.castSucc_one]
    split_ifs <;> norm_num <;> simp_all
  | 3 =>
    simp only [pathReturnOf, r, Fin.init, Fin.castSucc_zero, Fin.castSucc_one]
    split_ifs <;> norm_num <;> simp_all
  | n + 4 => omega

/-- **Instance B** as a `Model`: `T = 3`, `γ = 1`, `δ = 1/5`, one residual hypothesis.
Source: [[oracle-side-gaps-reaudit]] lines 33–43 (Instance B)
Kind: D
Fidelity: exact (terminal rewards of the reaudit rendered as rewards on arrival; `u = 0`)
Hyps: n/a -/
noncomputable def model : Model (Fin 2) Unit Unit where
  T := 3
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
  w := fun _ => 1 / 5
  w_nonneg := fun _ => by norm_num
  δ := 1 / 5
  w_sum := by simp
  δ_pos := by norm_num
  δ_lt_one := by norm_num

/-- The root history. -/
def root : Hist (Fin 2) Unit 0 := Fin.elim0
/-- The node `n₁ = (go)`. -/
def n1 : Hist (Fin 2) Unit 1 := ext root 1 ()
/-- The water node `(go, jump)`. -/
def water : Hist (Fin 2) Unit 2 := ext n1 1 ()

@[simp] theorem model_T : model.T = 3 := rfl
@[simp] theorem model_alive : model.alive = alive := rfl
@[simp] theorem model_r : model.r = r := rfl
@[simp] theorem model_γ : model.γ = 1 := rfl
@[simp] theorem model_νa : model.νa = νa := rfl
@[simp] theorem model_νe (i : Unit) (n : ℕ) (h : Hist (Fin 2) Unit n) (a : Fin 2) (e : Unit) :
    model.νe i n h a e = 1 := rfl
@[simp] theorem model_w (i : Unit) : model.w i = 1 / 5 := rfl
@[simp] theorem model_δ : model.δ = 1 / 5 := rfl

theorem nt_root : model.nonterminal 0 root := ⟨by simp, rfl⟩
theorem nt_n1 : model.nonterminal 1 n1 := ⟨by simp, by simp [alive, n1]⟩
theorem nt_water : model.nonterminal 2 water := ⟨by simp, by simp [alive, water, n1]⟩
theorem not_nt_stay : ¬ model.nonterminal 1 (ext root 0 ()) := fun h => by
  have := h.2; simp [alive] at this
theorem not_nt_n1stay : ¬ model.nonterminal 2 (ext n1 0 ()) := fun h => by
  have := h.2; simp [alive, n1] at this
theorem not_nt_three (h : Hist (Fin 2) Unit 3) : ¬ model.nonterminal 3 h := fun h' => by
  have := h'.1; simp at this

theorem xie_eq_one (n : ℕ) (h : Hist (Fin 2) Unit n) (a : Fin 2) (e : Unit) : model.xie n h a e = 1 :=
  model.xie_eq_one_of_unique n h a e

theorem nuJoint_n1 : model.nuJoint () 1 n1 = 1 := by simp [n1, νa]
theorem nuJoint_water : model.nuJoint () 2 water = 1 := by simp [water, n1, νa]
theorem nuJoint_stay : model.nuJoint () 1 (ext root 0 ()) = 0 := by simp [νa]
theorem nuJoint_n1stay : model.nuJoint () 2 (ext n1 0 ()) = 0 := by simp [νa]
theorem nuJoint_swim : model.nuJoint () 3 (ext water 0 ()) = 0 := by simp [νa]
theorem nuJoint_sink : model.nuJoint () 3 (ext water 1 ()) = 1 := by simp [water, n1, νa]

theorem xins_root : model.xins 0 root = 1 / 5 := by simp [Model.xins]
theorem xins_n1 : model.xins 1 n1 = 1 / 5 := by simp [Model.xins, water, n1, νa]
theorem xins_water : model.xins 2 water = 1 / 5 := by simp [Model.xins, water, n1, νa]
theorem xins_stay : model.xins 1 (ext root 0 ()) = 0 := by simp [Model.xins, water, n1, νa]
theorem xins_n1stay : model.xins 2 (ext n1 0 ()) = 0 := by simp [Model.xins, water, n1, νa]
theorem xins_swim : model.xins 3 (ext water 0 ()) = 0 := by simp [Model.xins, water, n1, νa]
theorem xins_sink : model.xins 3 (ext water 1 ()) = 1 / 5 := by simp [Model.xins, water, n1, νa]


/-! #### The decision nodes are exactly `root`, `n₁`, `water` -/

theorem eq_root (h : Hist (Fin 2) Unit 0) : h = root := funext fun i => Fin.elim0 i

theorem eq_n1_of_nonterminal (h : Hist (Fin 2) Unit 1) (hnt : model.nonterminal 1 h) : h = n1 := by
  have h0 : (h 0).1 = 1 := by have := hnt.2; simpa [alive] using this
  funext i
  fin_cases i
  exact Prod.ext h0 (Subsingleton.elim _ _)

theorem eq_water_of_nonterminal (h : Hist (Fin 2) Unit 2) (hnt : model.nonterminal 2 h) : h = water := by
  have h0 : (h 0).1 = 1 ∧ (h 1).1 = 1 := by have := hnt.2; simpa [alive] using this
  funext i
  fin_cases i
  · exact Prod.ext h0.1 (Subsingleton.elim _ _)
  · exact Prod.ext h0.2 (Subsingleton.elim _ _)

theorem not_nonterminal_ge_three (n : ℕ) (hn : 3 ≤ n) (h : Hist (Fin 2) Unit n) : ¬ model.nonterminal n h :=
  model.not_nonterminal_of_le (by simpa using hn) h

theorem div_mul_div_cancel_aux (a b c : ℝ) (ha : a ≠ 0) : a / b * (c / a) = c / b := by
  rw [div_mul_div_comm, mul_comm a c, mul_div_mul_right _ _ ha]

/-! #### Joints along the tree -/

section Values
variable (π : Policy (Fin 2) Unit)

theorem xiS_n1 : model.xiS π 1 n1 = π 0 root 1 := by simp [n1, xie_eq_one]
theorem xiS_water : model.xiS π 2 water = π 0 root 1 * π 1 n1 1 := by simp [water, n1, xie_eq_one]
theorem xiS_swim : model.xiS π 3 (ext water 0 ()) = π 0 root 1 * π 1 n1 1 * π 2 water 0 := by
  simp [water, n1, xie_eq_one]
theorem xiS_sink : model.xiS π 3 (ext water 1 ()) = π 0 root 1 * π 1 n1 1 * π 2 water 1 := by
  simp [water, n1, xie_eq_one]
theorem xiS_stay : model.xiS π 1 (ext root 0 ()) = π 0 root 0 := by simp [xie_eq_one]
theorem xiS_n1stay : model.xiS π 2 (ext n1 0 ()) = π 0 root 1 * π 1 n1 0 := by simp [n1, xie_eq_one]

theorem xi_root : model.xi π 0 root = 1 := by
  unfold Model.xi; rw [xins_root, Model.xiS_zero, model_δ]; norm_num
theorem xi_n1 : model.xi π 1 n1 = 4 / 5 * π 0 root 1 + 1 / 5 := by
  unfold Model.xi; rw [xins_n1, xiS_n1, model_δ]; ring
theorem xi_water : model.xi π 2 water = 4 / 5 * (π 0 root 1 * π 1 n1 1) + 1 / 5 := by
  unfold Model.xi; rw [xins_water, xiS_water, model_δ]; ring
theorem xi_swim : model.xi π 3 (ext water 0 ()) = 4 / 5 * (π 0 root 1 * π 1 n1 1 * π 2 water 0) := by
  unfold Model.xi; rw [xins_swim, xiS_swim, model_δ]; ring
theorem xi_sink : model.xi π 3 (ext water 1 ()) = 4 / 5 * (π 0 root 1 * π 1 n1 1 * π 2 water 1) + 1 / 5 := by
  unfold Model.xi; rw [xins_sink, xiS_sink, model_δ]; ring
theorem xi_stay : model.xi π 1 (ext root 0 ()) = 4 / 5 * π 0 root 0 := by
  unfold Model.xi; rw [xins_stay, xiS_stay, model_δ]; ring
theorem xi_n1stay : model.xi π 2 (ext n1 0 ()) = 4 / 5 * (π 0 root 1 * π 1 n1 0) := by
  unfold Model.xi; rw [xins_n1stay, xiS_n1stay, model_δ]; ring

theorem xiA_root_0 : model.xiA π 0 root 0 = 4 / 5 * π 0 root 0 := by
  show ∑ e : Unit, model.xi π 1 (ext root 0 e) = _
  rw [Fintype.sum_unique]
  exact xi_stay π
theorem xiA_root_1 : model.xiA π 0 root 1 = 4 / 5 * π 0 root 1 + 1 / 5 := by
  show ∑ e : Unit, model.xi π 1 (ext root 1 e) = _
  rw [Fintype.sum_unique]
  exact xi_n1 π
theorem xiA_n1_0 : model.xiA π 1 n1 0 = 4 / 5 * (π 0 root 1 * π 1 n1 0) := by
  show ∑ e : Unit, model.xi π 2 (ext n1 0 e) = _
  rw [Fintype.sum_unique]
  exact xi_n1stay π
theorem xiA_n1_1 : model.xiA π 1 n1 1 = 4 / 5 * (π 0 root 1 * π 1 n1 1) + 1 / 5 := by
  show ∑ e : Unit, model.xi π 2 (ext n1 1 e) = _
  rw [Fintype.sum_unique]
  exact xi_water π
theorem xiA_water_0 : model.xiA π 2 water 0 = 4 / 5 * (π 0 root 1 * π 1 n1 1 * π 2 water 0) := by
  show ∑ e : Unit, model.xi π 3 (ext water 0 e) = _
  rw [Fintype.sum_unique]
  exact xi_swim π
theorem xiA_water_1 : model.xiA π 2 water 1 = 4 / 5 * (π 0 root 1 * π 1 n1 1 * π 2 water 1) + 1 / 5 := by
  show ∑ e : Unit, model.xi π 3 (ext water 1 e) = _
  rw [Fintype.sum_unique]
  exact xi_sink π

/-! #### Values at the water -/

theorem Qxi_water_0 : model.Qxi π 2 water 0 = 1 := by
  rw [model.Qxi_eq_of_children_terminal water 0 (fun e => not_nt_three _)]
  simp [xie_eq_one, r, water, n1]
theorem Qxi_water_1 : model.Qxi π 2 water 1 = 0 := by
  rw [model.Qxi_eq_of_children_terminal water 1 (fun e => not_nt_three _)]
  simp [xie_eq_one, r, water, n1]
theorem Qpi_water_0 : model.Qpi π 2 water 0 = 1 := by
  rw [model.Qpi_eq_of_children_terminal water 0 (fun e => not_nt_three _)]
  simp [xie_eq_one, r, water, n1]
theorem Qpi_water_1 : model.Qpi π 2 water 1 = 0 := by
  rw [model.Qpi_eq_of_children_terminal water 1 (fun e => not_nt_three _)]
  simp [xie_eq_one, r, water, n1]
theorem Qstar_water_0 : model.Qstar 2 water 0 = 1 := by
  rw [model.Qstar_eq_of_children_terminal water 0 (fun e => not_nt_three _)]
  simp [xie_eq_one, r, water, n1]
theorem Qstar_water_1 : model.Qstar 2 water 1 = 0 := by
  rw [model.Qstar_eq_of_children_terminal water 1 (fun e => not_nt_three _)]
  simp [xie_eq_one, r, water, n1]
theorem Vstar_water : model.Vstar 2 water = 1 := by
  rw [model.Vstar_fin_two nt_water, Qstar_water_0, Qstar_water_1]; norm_num
theorem Mx_water : model.Mx π 2 water = 1 := by
  rw [model.Mx_fin_two, Qxi_water_0, Qxi_water_1]; norm_num
theorem piStar_water : model.piStar 2 water = 0 := by
  refine model.piStar_eq_of_unique nt_water (Fin.forall_fin_two.2 ⟨fun _ => rfl, fun ha => ?_⟩)
  rw [Qstar_water_1, Vstar_water] at ha; norm_num at ha

theorem wS_water (hπ : model.IsPolicy π) :
    model.wS π 2 water = 4 / 5 * (π 0 root 1 * π 1 n1 1) / (4 / 5 * (π 0 root 1 * π 1 n1 1) + 1 / 5) := by
  have hx : model.xi π 2 water ≠ 0 := by
    rw [xi_water]
    have := mul_nonneg (hπ.nonneg nt_root 1) (hπ.nonneg nt_n1 1)
    positivity
  rw [Model.wS_of_xi_ne_zero model hx, xi_water, xiS_water]
  norm_num

theorem Vxi_water (hπ : model.IsPolicy π) :
    model.Vxi π 2 water = 4 / 5 * (π 0 root 1 * π 1 n1 1 * π 2 water 0) /
      (4 / 5 * (π 0 root 1 * π 1 n1 1) + 1 / 5) := by
  have hx : model.xi π 2 water ≠ 0 := by
    rw [xi_water]
    have := mul_nonneg (hπ.nonneg nt_root 1) (hπ.nonneg nt_n1 1)
    positivity
  rw [model.Vxi_eq nt_water, Fin.sum_univ_two, Qxi_water_0, Qxi_water_1]
  simp only [Model.xia, hx, if_false, mul_one, mul_zero, add_zero]
  rw [xiA_water_0, xi_water]

/-! #### Values at `n₁` -/

theorem Qxi_n1_0 : model.Qxi π 1 n1 0 = 17 / 20 := by
  rw [model.Qxi_eq_of_children_terminal n1 0 (fun e => by cases e; exact not_nt_n1stay)]
  simp [xie_eq_one, r, n1]
theorem Qxi_n1_1 : model.Qxi π 1 n1 1 = model.Vxi π 2 water := by
  rw [Model.Qxi_eq_sum, Fintype.sum_unique, xie_eq_one]
  simp [r, n1]
  rfl
theorem Qpi_n1_0 : model.Qpi π 1 n1 0 = 17 / 20 := by
  rw [model.Qpi_eq_of_children_terminal n1 0 (fun e => by cases e; exact not_nt_n1stay)]
  simp [xie_eq_one, r, n1]
theorem Qpi_n1_1 : model.Qpi π 1 n1 1 = model.Vpi π 2 water := by
  rw [Model.Qpi_eq_sum, Fintype.sum_unique, xie_eq_one]
  simp [r, n1]
  rfl
theorem Qstar_n1_0 : model.Qstar 1 n1 0 = 17 / 20 := by
  rw [model.Qstar_eq_of_children_terminal n1 0 (fun e => by cases e; exact not_nt_n1stay)]
  simp [xie_eq_one, r, n1]
theorem Qstar_n1_1 : model.Qstar 1 n1 1 = 1 := by
  rw [Model.Qstar_eq_sum, Fintype.sum_unique, xie_eq_one]
  simp [r, n1]
  exact Vstar_water
theorem Vstar_n1 : model.Vstar 1 n1 = 1 := by
  rw [model.Vstar_fin_two nt_n1, Qstar_n1_0, Qstar_n1_1]; norm_num
theorem piStar_n1 : model.piStar 1 n1 = 1 := by
  refine model.piStar_eq_of_unique nt_n1 (Fin.forall_fin_two.2 ⟨fun ha => ?_, fun _ => rfl⟩)
  rw [Qstar_n1_0, Vstar_n1] at ha; norm_num at ha

/-- `Q_ξ(n₁, jump) ≤ 4/5 < 0.85` for every policy: `stay` is the unique EDT best response at `n₁`.
Source: [[oracle-side-gaps-reaudit]] line 37
Kind: P
Fidelity: exact (stated for every `(j, k, s)`, the reaudit fixes `s = 1`)
Hyps: (a) -/
theorem Qxi_n1_1_le (hπ : model.IsPolicy π) : model.Qxi π 1 n1 1 ≤ 4 / 5 := by
  rw [Qxi_n1_1, Vxi_water π hπ]
  have hj0 := hπ.nonneg nt_root 1
  have hj1 := hπ.le_one nt_root 1
  have hk0 := hπ.nonneg nt_n1 1
  have hk1 := hπ.le_one nt_n1 1
  have hs0 := hπ.nonneg nt_water 0
  have hs1 := hπ.le_one nt_water 0
  have hx : (0:ℝ) < 4 / 5 * (π 0 root 1 * π 1 n1 1) + 1 / 5 := by positivity
  rw [div_le_iff₀ hx]
  nlinarith [mul_nonneg hj0 hk0, mul_le_one₀ hj1 hk0 hk1]

theorem Mx_n1 (hπ : model.IsPolicy π) : model.Mx π 1 n1 = 17 / 20 := by
  rw [model.Mx_fin_two, Qxi_n1_0]
  have := Qxi_n1_1_le π hπ
  rw [max_eq_left (by linarith)]

theorem wS_n1 (hπ : model.IsPolicy π) :
    model.wS π 1 n1 = 4 / 5 * π 0 root 1 / (4 / 5 * π 0 root 1 + 1 / 5) := by
  have hx : model.xi π 1 n1 ≠ 0 := by
    rw [xi_n1]
    have := hπ.nonneg nt_root 1
    positivity
  rw [Model.wS_of_xi_ne_zero model hx, xi_n1, xiS_n1]
  norm_num

theorem wS_n1_le (hπ : model.IsPolicy π) : model.wS π 1 n1 ≤ 4 / 5 := by
  rw [wS_n1 π hπ]
  have hj0 := hπ.nonneg nt_root 1
  have hj1 := hπ.le_one nt_root 1
  have hx : (0:ℝ) < 4 / 5 * π 0 root 1 + 1 / 5 := by positivity
  rw [div_le_iff₀ hx]
  nlinarith

/-- The trust bound at `n₁` holds for every policy (the floor never fires there).
Source: [[oracle-side-gaps-reaudit]] line 37
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem TB_n1 (hπ : model.IsPolicy π) : model.TB π 1 n1 := by
  unfold Model.TB
  rw [Mx_n1 π hπ, Vstar_n1, mul_one]
  linarith [wS_n1_le π hπ]

theorem Vxi_n1 (hπ : model.IsPolicy π) :
    model.Vxi π 1 n1 = (4 / 5 * (π 0 root 1 * π 1 n1 0) * (17 / 20) +
      4 / 5 * (π 0 root 1 * π 1 n1 1 * π 2 water 0)) / (4 / 5 * π 0 root 1 + 1 / 5) := by
  have hx : model.xi π 1 n1 ≠ 0 := by
    rw [xi_n1]
    have := hπ.nonneg nt_root 1
    positivity
  have hxw : (0:ℝ) < 4 / 5 * (π 0 root 1 * π 1 n1 1) + 1 / 5 := by
    have := mul_nonneg (hπ.nonneg nt_root 1) (hπ.nonneg nt_n1 1)
    positivity
  have hxw' := hxw.ne'
  have hx' : (4 / 5 * π 0 root 1 + 1 / 5 : ℝ) ≠ 0 := by rw [← xi_n1]; exact hx
  rw [model.Vxi_eq nt_n1, Fin.sum_univ_two, Qxi_n1_0, Qxi_n1_1, Vxi_water π hπ]
  simp only [Model.xia, hx, if_false]
  rw [xiA_n1_0, xiA_n1_1, xi_n1, div_mul_div_cancel_aux _ _ _ hxw', div_mul_eq_mul_div]
  ring

/-! #### Values at the root -/

theorem Qxi_root_0 : model.Qxi π 0 root 0 = 7 / 10 := by
  rw [model.Qxi_eq_of_children_terminal root 0 (fun e => by cases e; exact not_nt_stay)]
  simp [xie_eq_one, r]
theorem Qxi_root_1 : model.Qxi π 0 root 1 = model.Vxi π 1 n1 := by
  rw [Model.Qxi_eq_sum, Fintype.sum_unique, xie_eq_one]
  simp [r]
  rfl
theorem Qpi_root_0 : model.Qpi π 0 root 0 = 7 / 10 := by
  rw [model.Qpi_eq_of_children_terminal root 0 (fun e => by cases e; exact not_nt_stay)]
  simp [xie_eq_one, r]
theorem Qpi_root_1 : model.Qpi π 0 root 1 = model.Vpi π 1 n1 := by
  rw [Model.Qpi_eq_sum, Fintype.sum_unique, xie_eq_one]
  simp [r]
  rfl
theorem Qstar_root_0 : model.Qstar 0 root 0 = 7 / 10 := by
  rw [model.Qstar_eq_of_children_terminal root 0 (fun e => by cases e; exact not_nt_stay)]
  simp [xie_eq_one, r]
theorem Qstar_root_1 : model.Qstar 0 root 1 = 1 := by
  rw [Model.Qstar_eq_sum, Fintype.sum_unique, xie_eq_one]
  simp [r]
  exact Vstar_n1
theorem Vstar_root : model.Vstar 0 root = 1 := by
  rw [model.Vstar_fin_two nt_root, Qstar_root_0, Qstar_root_1]; norm_num
theorem piStar_root : model.piStar 0 root = 1 := by
  refine model.piStar_eq_of_unique nt_root (Fin.forall_fin_two.2 ⟨fun ha => ?_, fun _ => rfl⟩)
  rw [Qstar_root_0, Vstar_root] at ha; norm_num at ha
theorem wS_root : model.wS π 0 root = 4 / 5 := by
  rw [Model.wS_of_xi_ne_zero model (by rw [xi_root]; exact one_ne_zero), xi_root, Model.xiS_zero, model_δ]
  norm_num

/-- The closed form `Q_ξ(root, go) = (4/5) j [(1-k)(17/20) + k s] / ((4/5) j + 1/5)`. -/
theorem Qxi_root_1_eq (hπ : model.IsPolicy π) :
    model.Qxi π 0 root 1 = 4 / 5 * π 0 root 1 * ((1 - π 1 n1 1) * (17 / 20) + π 1 n1 1 * π 2 water 0) /
      (4 / 5 * π 0 root 1 + 1 / 5) := by
  rw [Qxi_root_1, Vxi_n1 π hπ, hπ.fin_two_zero nt_n1]
  ring

/-- `Q_ξ(root, go) ≤ 4/5` for every policy.
Source: [[oracle-side-gaps-reaudit]] line 39
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Qxi_root_1_le (hπ : model.IsPolicy π) : model.Qxi π 0 root 1 ≤ 4 / 5 := by
  rw [Qxi_root_1_eq π hπ]
  have hj0 := hπ.nonneg nt_root 1
  have hj1 := hπ.le_one nt_root 1
  have hk0 := hπ.nonneg nt_n1 1
  have hk1 := hπ.le_one nt_n1 1
  have hs0 := hπ.nonneg nt_water 0
  have hs1 := hπ.le_one nt_water 0
  have hx : (0:ℝ) < 4 / 5 * π 0 root 1 + 1 / 5 := by positivity
  rw [div_le_iff₀ hx]
  have hin : (1 - π 1 n1 1) * (17 / 20) + π 1 n1 1 * π 2 water 0 ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hin hj0]

/-- `Q_ξ(root, go) = 4/5` iff `(j, k, s) = (1, 1, 1)`.
Source: [[oracle-side-gaps-reaudit]] line 39 ("equality iff `(j,k) = (1,1)`")
Kind: P
Fidelity: exact (with `s = π(swim|water)` made explicit)
Hyps: (a) -/
theorem Qxi_root_1_eq_iff (hπ : model.IsPolicy π) :
    model.Qxi π 0 root 1 = 4 / 5 ↔ π 0 root 1 = 1 ∧ π 1 n1 1 = 1 ∧ π 2 water 0 = 1 := by
  rw [Qxi_root_1_eq π hπ]
  have hj0 := hπ.nonneg nt_root 1
  have hj1 := hπ.le_one nt_root 1
  have hk0 := hπ.nonneg nt_n1 1
  have hk1 := hπ.le_one nt_n1 1
  have hs0 := hπ.nonneg nt_water 0
  have hs1 := hπ.le_one nt_water 0
  have hx : (0:ℝ) < 4 / 5 * π 0 root 1 + 1 / 5 := by positivity
  rw [div_eq_iff hx.ne']
  constructor
  · intro heq
    have hin : (1 - π 1 n1 1) * (17 / 20) + π 1 n1 1 * π 2 water 0 ≤ 1 := by nlinarith
    have hj : π 0 root 1 = 1 := by nlinarith [mul_le_mul_of_nonneg_left hin hj0]
    rw [hj] at heq
    have hk : π 1 n1 1 = 1 := by nlinarith
    rw [hk] at heq
    have hs : π 2 water 0 = 1 := by nlinarith
    exact ⟨hj, hk, hs⟩
  · rintro ⟨hj, hk, hs⟩
    rw [hj, hk, hs]
    norm_num

/-! #### Fixed points of the plain agent: unique, `(j,k) = (0,0)`, the trust bound fails at the root -/

/-- **Plain fixed points of Instance B**: `π` is a plain fixed point iff it is a policy with
`π(go|root) = 0`, `π(jump|n₁) = 0`, `π(sink|water) = 0` — the unique honest fixed point `(0,0)`.
Source: [[oracle-side-gaps-reaudit]] line 41 ("Unique honest fixed point `(0,0)`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem isPlainFP_iff : model.IsPlainFP π ↔
    model.IsPolicy π ∧ π 0 root 1 = 0 ∧ π 1 n1 1 = 0 ∧ π 2 water 1 = 0 := by
  constructor
  · rintro ⟨hπ, hfp⟩
    -- water: `sink` is not a best response
    have hs : π 2 water 1 = 0 := by
      by_contra hne
      have hpos : 0 < π 2 water 1 := lt_of_le_of_ne (hπ.nonneg nt_water 1) (Ne.symm hne)
      have := hfp 2 water nt_water 1 hpos
      rw [Qxi_water_1, Mx_water] at this
      norm_num at this
    -- `n₁`: `jump` is not a best response
    have hk : π 1 n1 1 = 0 := by
      by_contra hne
      have hpos : 0 < π 1 n1 1 := lt_of_le_of_ne (hπ.nonneg nt_n1 1) (Ne.symm hne)
      have := hfp 1 n1 nt_n1 1 hpos
      rw [Mx_n1 π hπ] at this
      linarith [Qxi_n1_1_le π hπ]
    -- root: with `k = 0`, `Q_ξ(root, go) ≤ 17/25 < 7/10`
    have hj : π 0 root 1 = 0 := by
      by_contra hne
      have hpos : 0 < π 0 root 1 := lt_of_le_of_ne (hπ.nonneg nt_root 1) (Ne.symm hne)
      have hQ : model.Qxi π 0 root 1 ≤ 17 / 25 := by
        rw [Qxi_root_1_eq π hπ, hk]
        have hj1 := hπ.le_one nt_root 1
        have hx : (0:ℝ) < 4 / 5 * π 0 root 1 + 1 / 5 := by positivity
        rw [div_le_iff₀ hx]
        nlinarith
      have := hfp 0 root nt_root 1 hpos
      rw [model.Mx_fin_two, Qxi_root_0] at this
      have hmax : max (7 / 10 : ℝ) (model.Qxi π 0 root 1) = 7 / 10 := max_eq_left (by linarith)
      rw [hmax] at this
      linarith
    exact ⟨hπ, hj, hk, hs⟩
  · rintro ⟨hπ, hj, hk, hs⟩
    refine ⟨hπ, ?_⟩
    intro n h hnt
    match n with
    | 0 =>
      rw [eq_root h]
      refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun ha => ?_⟩
      · rw [model.Mx_fin_two, Qxi_root_0, Qxi_root_1_eq π hπ, hj]
        norm_num
      · rw [hj] at ha; exact absurd ha (lt_irrefl 0)
    | 1 =>
      rw [eq_n1_of_nonterminal h hnt]
      refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun ha => ?_⟩
      · rw [Mx_n1 π hπ, Qxi_n1_0]
      · rw [hk] at ha; exact absurd ha (lt_irrefl 0)
    | 2 =>
      rw [eq_water_of_nonterminal h hnt]
      refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun ha => ?_⟩
      · rw [Mx_water, Qxi_water_0]
      · rw [hs] at ha; exact absurd ha (lt_irrefl 0)
    | n + 3 => exact absurd hnt (not_nonterminal_ge_three _ (by omega) h)

/-- At the plain fixed point of Instance B the trust bound **fails** at the root: `w_root V^* = 4/5 > 7/10 = M(root)`.
Source: [[oracle-side-gaps-reaudit]] line 41 ("the trust bound fails there")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem not_TB_root_of_isPlainFP (hfp : model.IsPlainFP π) : ¬ model.TB π 0 root := by
  obtain ⟨hπ, hj, hk, hs⟩ := (isPlainFP_iff π).1 hfp
  unfold Model.TB
  rw [wS_root, Vstar_root, model.Mx_fin_two, Qxi_root_0, Qxi_root_1_eq π hπ, hj]
  norm_num

/-- Value and loss at the plain fixed point: `V^π(root) = 7/10`, loss `3/10 = 1.5 δ`.
Source: [[oracle-side-gaps-reaudit]] line 41
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Vpi_root_of_isPlainFP (hfp : model.IsPlainFP π) :
    model.Vpi π 0 root = 7 / 10 ∧ model.gap π 0 root = 3 / 2 * model.δ := by
  obtain ⟨hπ, hj, hk, hs⟩ := (isPlainFP_iff π).1 hfp
  have hV : model.Vpi π 0 root = 7 / 10 := by
    rw [model.Vpi_eq nt_root, Fin.sum_univ_two, Qpi_root_0, hj, hπ.fin_two_zero nt_root, hj]
    norm_num
  refine ⟨hV, ?_⟩
  unfold Model.gap
  rw [hV, Vstar_root, model_δ]
  norm_num

/-! #### Fixed points of the floored agent: unique, `(j,k) = (1,0)`, the floor fires strictly at the root -/

/-- **Floored fixed points of Instance B**: `π` is a floored fixed point iff it is a policy with
`π(go|root) = 1`, `π(jump|n₁) = 0`, `π(sink|water) = 0` — the unique fixed point `(1,0)` of the current-node
floor, at which the floor fires strictly at the root (`resid_root_neg_of_isFlooredFP`).
Source: [[oracle-side-gaps-reaudit]] line 43 ("current-node `π†` has the unique fixed point `(1,0)`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem isFlooredFP_iff : model.IsFlooredFP π ↔
    model.IsPolicy π ∧ π 0 root 1 = 1 ∧ π 1 n1 1 = 0 ∧ π 2 water 1 = 0 := by
  constructor
  · rintro ⟨hπ, hfp⟩
    have hj0 := hπ.nonneg nt_root 1
    have hj1 := hπ.le_one nt_root 1
    have hk0 := hπ.nonneg nt_n1 1
    -- water: `r > 0` (`w_water < 1`), so the support is in the argmax `{swim}`
    have hs : π 2 water 1 = 0 := by
      have hr : 0 < model.resid π 2 water := by
        unfold Model.resid
        rw [Mx_water, Vstar_water, wS_water π hπ, mul_one]
        have hjk := mul_nonneg hj0 hk0
        have hx : (0:ℝ) < 4 / 5 * (π 0 root 1 * π 1 n1 1) + 1 / 5 := by positivity
        rw [sub_pos, div_lt_one hx]
        linarith
      by_contra hne
      have hpos : 0 < π 2 water 1 := lt_of_le_of_ne (hπ.nonneg nt_water 1) (Ne.symm hne)
      have := (hfp 2 water nt_water).2.1 hr 1 hpos
      rw [Qxi_water_1, Mx_water] at this
      norm_num at this
    -- `n₁`: `r ≥ 17/20 - 4/5 > 0`, support in the argmax `{stay}`
    have hk : π 1 n1 1 = 0 := by
      have hr : 0 < model.resid π 1 n1 := by
        unfold Model.resid
        rw [Mx_n1 π hπ, Vstar_n1, mul_one]
        linarith [wS_n1_le π hπ]
      by_contra hne
      have hpos : 0 < π 1 n1 1 := lt_of_le_of_ne (hπ.nonneg nt_n1 1) (Ne.symm hne)
      have := (hfp 1 n1 nt_n1).2.1 hr 1 hpos
      rw [Mx_n1 π hπ] at this
      linarith [Qxi_n1_1_le π hπ]
    -- root: `M = 7/10 < 4/5 = w V^*`, so the support is `{π⋆(root)} = {go}`
    have hj : π 0 root 1 = 1 := by
      have hQ : model.Qxi π 0 root 1 ≤ 17 / 25 := by
        rw [Qxi_root_1_eq π hπ, hk]
        have hx : (0:ℝ) < 4 / 5 * π 0 root 1 + 1 / 5 := by positivity
        rw [div_le_iff₀ hx]
        nlinarith
      have hr : model.resid π 0 root < 0 := by
        unfold Model.resid
        rw [wS_root, Vstar_root, model.Mx_fin_two, Qxi_root_0, max_eq_left (by linarith)]
        norm_num
      by_contra hne
      have h0pos : 0 < π 0 root 0 := by rw [hπ.fin_two_zero nt_root]; exact sub_pos.2 (lt_of_le_of_ne hj1 hne)
      have := (hfp 0 root nt_root).1 hr 0 h0pos
      rw [piStar_root] at this
      exact absurd this (by decide)
    exact ⟨hπ, hj, hk, hs⟩
  · rintro ⟨hπ, hj, hk, hs⟩
    refine ⟨hπ, ?_⟩
    intro n h hnt
    match n with
    | 0 =>
      rw [eq_root h]
      have hr : model.resid π 0 root < 0 := by
        unfold Model.resid
        rw [wS_root, Vstar_root, model.Mx_fin_two, Qxi_root_0, Qxi_root_1_eq π hπ, hj, hk]
        norm_num
      refine ⟨fun _ => Fin.forall_fin_two.2 ⟨fun ha => ?_, fun _ => piStar_root.symm⟩,
        fun hpos => absurd hr (not_lt.2 hpos.le), fun h0 => absurd h0 hr.ne⟩
      rw [hπ.fin_two_zero nt_root, hj] at ha; norm_num at ha
    | 1 =>
      rw [eq_n1_of_nonterminal h hnt]
      have hr : 0 < model.resid π 1 n1 := by
        unfold Model.resid
        rw [Mx_n1 π hπ, Vstar_n1, mul_one]
        linarith [wS_n1_le π hπ]
      refine ⟨fun hneg => absurd hr (not_lt.2 hneg.le),
        fun _ => Fin.forall_fin_two.2 ⟨fun _ => ?_, fun ha => ?_⟩, fun h0 => absurd h0 hr.ne'⟩
      · rw [Mx_n1 π hπ, Qxi_n1_0]
      · rw [hk] at ha; exact absurd ha (lt_irrefl 0)
    | 2 =>
      rw [eq_water_of_nonterminal h hnt]
      have hr : 0 < model.resid π 2 water := by
        unfold Model.resid
        rw [Mx_water, Vstar_water, wS_water π hπ, mul_one, hk]
        norm_num
      refine ⟨fun hneg => absurd hr (not_lt.2 hneg.le),
        fun _ => Fin.forall_fin_two.2 ⟨fun _ => ?_, fun ha => ?_⟩, fun h0 => absurd h0 hr.ne'⟩
      · rw [Mx_water, Qxi_water_0]
      · rw [hs] at ha; exact absurd ha (lt_irrefl 0)
    | n + 3 => exact absurd hnt (not_nonterminal_ge_three _ (by omega) h)

/-- At the floored fixed point the floor fires **strictly** at the root (`r_root = 7/10 - 4/5 < 0`), and
the value is `V^π(root) = 17/20`, loss `3/20 = 0.75 δ`.
Source: [[oracle-side-gaps-reaudit]] line 43 ("the floor fires strictly at the root … value `0.85`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem resid_root_neg_of_isFlooredFP (hfp : model.IsFlooredFP π) :
    model.resid π 0 root < 0 ∧ model.Vpi π 0 root = 17 / 20 ∧ model.gap π 0 root = 3 / 4 * model.δ := by
  obtain ⟨hπ, hj, hk, hs⟩ := (isFlooredFP_iff π).1 hfp
  refine ⟨?_, ?_, ?_⟩
  · unfold Model.resid
    rw [wS_root, Vstar_root, model.Mx_fin_two, Qxi_root_0, Qxi_root_1_eq π hπ, hj, hk]
    norm_num
  · rw [model.Vpi_eq nt_root, Fin.sum_univ_two, Qpi_root_0, Qpi_root_1, hj, hπ.fin_two_zero nt_root, hj,
      model.Vpi_eq nt_n1, Fin.sum_univ_two, Qpi_n1_0, hk, hπ.fin_two_zero nt_n1, hk]
    norm_num
  · have hV : model.Vpi π 0 root = 17 / 20 := by
      rw [model.Vpi_eq nt_root, Fin.sum_univ_two, Qpi_root_0, Qpi_root_1, hj, hπ.fin_two_zero nt_root, hj,
        model.Vpi_eq nt_n1, Fin.sum_univ_two, Qpi_n1_0, hk, hπ.fin_two_zero nt_n1, hk]
      norm_num
    unfold Model.gap
    rw [hV, Vstar_root, model_δ]
    norm_num

end Values

/-! #### The refutation -/

/-- **The key lemma of the post is false in the finite shadow.** In Instance B, *every* plain fixed point
violates the trust bound at some decision node (the root). Quoted claim ([[lesswrong-post--live-2026-08-22]]
lines 218–221): "at a fixed point … the trust bound is not violated … no subtrees are reset" — read (finite
shadow, ATTRIBUTION-UNVETTED as a reading of Cole's construction) as "some plain fixed point satisfies
`(TB_h)` at every node". Surviving neighbours: Theorem B (the conclusion at trust-bound nodes), the floored
agent (Theorem C), and `uea-sink-swim`'s D1.
Source: [[oracle-side-gaps-reaudit]] line 41; [[uea-inventory]] 010, 006
Kind: P
Fidelity: exact (finite shadow)
Hyps: (a) -/
theorem key_lemma_refuted_instB :
    ∀ π, model.IsPlainFP π → ∃ (n : ℕ) (h : Hist (Fin 2) Unit n), model.nonterminal n h ∧ ¬ model.TB π n h :=
  fun π hfp => ⟨0, root, nt_root, not_TB_root_of_isPlainFP π hfp⟩

/-- Instance B does have plain fixed points (the refutation is not vacuous): the policy `(0,0)` with
`swim` at the water.
Source: [[oracle-side-gaps-reaudit]] line 41
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem exists_isPlainFP : ∃ π, model.IsPlainFP π := by
  refine ⟨fun _ _ a => if a = 0 then 1 else 0, (isPlainFP_iff _).2 ⟨?_, by simp, by simp, by simp⟩⟩
  intro n h _
  refine ⟨fun a => ?_, ?_⟩
  · dsimp only; split_ifs <;> norm_num
  · dsimp only; simp [Fin.sum_univ_two]

/-- Instance B does have floored fixed points: the policy `(1,0)` with `swim` at the water (the floor fires
strictly at the root, `resid_root_neg_of_isFlooredFP`).
Source: [[oracle-side-gaps-reaudit]] line 43
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem exists_isFlooredFP : ∃ π, model.IsFlooredFP π := by
  refine ⟨fun n _ a => if n = 0 then (if a = 1 then 1 else 0) else (if a = 0 then 1 else 0),
    (isFlooredFP_iff _).2 ⟨?_, by simp, by simp, by simp⟩⟩
  intro n h _
  refine ⟨fun a => ?_, ?_⟩
  · dsimp only; split_ifs <;> norm_num
  · dsimp only; split_ifs <;> simp [Fin.sum_univ_two]

end InstB

/-- **Cole's key lemma, finite shadow, refuted in general form**: it is not the case that every model has a
plain fixed point satisfying the trust bound at every decision node (Instance B is the witness). Universe: the
quantified types are in `Type` (universe 0), where Instance B lives; a `Type u` version would need the instance
lifted, which nothing here requires. The ξ-positive-node reading (the note's own finite shadow) is refuted as
`key_lemma_refuted_xi_pos`.
Source: [[oracle-side-gaps-reaudit]] line 41; [[uea-inventory]] 010
Kind: P
Fidelity: exact (finite shadow, all-nodes reading); the rOSI statement is not formalized
Hyps: (a) -/
theorem key_lemma_refuted :
    ¬ ∀ (A E ι : Type) [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι),
      ∃ π, M.IsPlainFP π ∧ ∀ n (h : Hist A E n), M.nonterminal n h → M.TB π n h := by
  intro H
  obtain ⟨π, hfp, htb⟩ := H (Fin 2) Unit Unit InstB.model
  exact InstB.not_TB_root_of_isPlainFP π hfp (htb 0 InstB.root InstB.nt_root)

/-- **The key lemma refuted in the ξ-positive-node reading** — the stronger refutation: it is not the case that
every model has a plain fixed point satisfying the trust bound at every decision node of positive
`ξ`-probability ([[sequential-self-game]] §5 and `sequential_self_game.py` line 536 state the finite shadow
with `ξ(h) > 0`; in rOSI every history has positive probability, and `TB` at a `ξ`-null node is a convention).
Instance B's violation is at the root, where `ξ(root) = 1`.
Source: [[oracle-side-gaps-reaudit]] line 41; [[sequential-self-game]] §5; round-1 audit
Kind: P
Fidelity: exact (finite shadow, ξ-positive reading)
Hyps: (a) -/
theorem key_lemma_refuted_xi_pos :
    ¬ ∀ (A E ι : Type) [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι),
      ∃ π, M.IsPlainFP π ∧ ∀ n (h : Hist A E n), M.nonterminal n h → M.xi π n h ≠ 0 → M.TB π n h := by
  intro H
  obtain ⟨π, hfp, htb⟩ := H (Fin 2) Unit Unit InstB.model
  exact InstB.not_TB_root_of_isPlainFP π hfp
    (htb 0 InstB.root InstB.nt_root (by rw [InstB.xi_root]; exact one_ne_zero))

end Cleanroom.Uea.UeaColeShadow
