import Cleanroom.Uea.UeaColeShadow.Instances

/-!
# mupi's Prop 4.29 in finite form, and where its transcription fails

(a) **The dogmatic residual.** For any tree data, true percept kernel `κ`, pure policy `π₀` and a *punishing
percept* `e₀` (every deviation `a ≠ π₀(h)` followed by `e₀` is dead with reward `0`), the model
`Dogmatic.model D` with one residual (`νa := π₀`, `νe(·|ha) := κ` if `a = π₀(h)` else `δ_{e₀}`) has `π₀` as a plain
fixed point for every `δ ∈ (0,1)`, with `w_h = 1 - δ` at every `κ`-reachable node; every deviation has
`Q_ξ = 0` (the fallback kernel at `ξ_{-S}(ha) = 0` is the residual's `δ_{e₀}`). **Yardstick**: the `ξ`-loss is `0`
(`V^* = V^{π₀}`: the equilibrium is *subjective*); the trap is against the true kernel, `val aggMax κ -
val (aggPol π₀) κ` at the root, which the tree makes arbitrary (witness: a one-step tree with `E = Fin 2`
where `π₀ = stay` loses `1/2`). **(c)**: reward-through-percept stands in for mupi's reward-in-percept; the
`ξ`-null fallback is load-bearing (target 10). (b) **Finding + N−**: with tree-fixed rewards and no punishing
percept, the unqualified "any deterministic policy is a fixed point of *some* dogmatic prior" is false — on the
two-node tree where `jump ↦ 1` (terminal) and `stay ↦ 1/2`, `stay` is not a plain fixed point of **any** model,
whatever the residual class (`NoPunish.stay_not_isPlainFP_any_residual`, quantified over `ι`, `νa`, `νe`, `w`,
`δ`), since with one percept `jump` pays its tree-fixed reward whatever the residual expects
(`NoPunish.Qxi_eq_reward_of_unique`); `NoPunish.stay_not_isPlainFP` is the one-model instance. Theorem A's trap is
a *different* mechanism (residual mass on the deviation with a bad continuation) from the dogmatic one (no
residual mass on the deviation, punishing percept): sink-or-swim is the former.

Scope: finite shadow of rOSI ([[sequential-self-game]] §7). Namespace `Cleanroom.Uea.UeaSinkSwim.Dogmatic`
(faf-cleanroom run, `uea-sink-swim`, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Finset
open Cleanroom.Uea.UeaColeShadow

namespace Dogmatic

/-- The data of a dogmatic instance: tree data, the true percept kernel `κ`, the pure policy `π₀`, the punishing
percept `e₀`, and the residual's prior `δ`.
Source: mupi `main.tex` L1306–1312 (Prop 4.29), proof L2996–3018; [[uea-inventory]] 040
Kind: D
Fidelity: variant: reward-through-percept and a punishing percept stand in for mupi's reward-in-percept (disclosed (c))
Hyps: n/a -/
structure DP (A E : Type*) [Fintype A] [Fintype E] where
  T : ℕ
  alive : (n : ℕ) → Hist A E n → Bool
  alive_init : ∀ (n : ℕ) (h : Hist A E (n + 1)), alive (n + 1) h = true → alive n (Fin.init h) = true
  r : (n : ℕ) → Hist A E (n + 1) → ℝ
  r_nonneg : ∀ n h, 0 ≤ r n h
  γ : ℝ
  γ_pos : 0 < γ
  γ_le_one : γ ≤ 1
  norm : ∀ n, n ≤ T → ∀ h : Hist A E n, pathReturnOf γ r n h ≤ 1
  κ : PerKernel A E
  κ_mem : ∀ n h a, κ n h a ∈ stdSimplex ℝ E
  π₀ : (n : ℕ) → Hist A E n → A
  e₀ : E
  punish : ∀ (n : ℕ) (h : Hist A E n) (a : A), a ≠ π₀ n h → alive (n + 1) (ext h a e₀) = false ∧ r n (ext h a e₀) = 0
  δ : ℝ
  hδ : 0 < δ
  hδ1 : δ < 1

variable {A E : Type*} [Fintype A] [Fintype E] [Nonempty A] (D : DP A E)

open Classical in
/-- The residual's action kernel: `π₀` surely. -/
noncomputable def νa : Unit → (n : ℕ) → Hist A E n → A → ℝ := fun _ n h a => if a = D.π₀ n h then 1 else 0

open Classical in
/-- The residual's percept kernel: `κ` after `π₀(h)`, the punishing `δ_{e₀}` after any deviation. -/
noncomputable def νe : Unit → (n : ℕ) → Hist A E n → A → E → ℝ := fun _ n h a e =>
  if a = D.π₀ n h then D.κ n h a e else (if e = D.e₀ then 1 else 0)

open Classical in
theorem νa_mem (i : Unit) (n : ℕ) (h : Hist A E n) : νa D i n h ∈ stdSimplex ℝ A := by
  refine ⟨fun a => ?_, ?_⟩
  · unfold νa; split_ifs <;> norm_num
  · unfold νa; simp

open Classical in
theorem νe_mem (i : Unit) (n : ℕ) (h : Hist A E n) (a : A) : νe D i n h a ∈ stdSimplex ℝ E := by
  unfold νe
  split_ifs with ha
  · exact D.κ_mem n h a
  · refine ⟨fun e => ?_, by simp⟩
    show (0:ℝ) ≤ if e = D.e₀ then 1 else 0
    split_ifs <;> norm_num

/-- **The dogmatic model** `model D : Model A E Unit`.
Source: mupi Prop 4.29 (finite form); [[uea-inventory]] 040
Kind: D
Fidelity: variant (see `DP`)
Hyps: n/a -/
noncomputable def model : Model A E Unit where
  T := D.T
  alive := D.alive
  alive_init := D.alive_init
  r := D.r
  r_nonneg := D.r_nonneg
  γ := D.γ
  γ_pos := D.γ_pos
  γ_le_one := D.γ_le_one
  norm := D.norm
  νa := νa D
  νe := νe D
  νa_mem := νa_mem D
  νe_mem := νe_mem D
  w := fun _ => D.δ
  w_nonneg := fun _ => D.hδ.le
  δ := D.δ
  w_sum := by simp
  δ_pos := D.hδ
  δ_lt_one := D.hδ1

open Classical in
/-- `π₀` as a policy. -/
noncomputable def pol : Policy A E := fun n h a => if a = D.π₀ n h then 1 else 0

theorem pol_self (n : ℕ) (h : Hist A E n) : pol D n h (D.π₀ n h) = 1 := by simp [pol]
theorem pol_ne {n : ℕ} {h : Hist A E n} {a : A} (ha : a ≠ D.π₀ n h) : pol D n h a = 0 := by simp [pol, ha]

theorem pol_isPolicy : (model D).IsPolicy (pol D) := fun n h _ => νa_mem D () n h
theorem pol_isPure : (model D).IsPure (pol D) := fun n h _ => ⟨D.π₀ n h, pol_self D n h⟩

@[simp] theorem model_νa : (model D).νa = νa D := rfl
@[simp] theorem model_νe : (model D).νe = νe D := rfl
@[simp] theorem model_w (i : Unit) : (model D).w i = D.δ := rfl
@[simp] theorem model_δ : (model D).δ = D.δ := rfl
@[simp] theorem model_r : (model D).r = D.r := rfl
@[simp] theorem model_alive : (model D).alive = D.alive := rfl

/-- A deviation carries no residual mass. -/
theorem xinsA_of_ne {n : ℕ} {h : Hist A E n} {a : A} (ha : a ≠ D.π₀ n h) : (model D).xinsA n h a = 0 := by
  simp [Model.xinsA, νa, ha]

open Classical in
/-- **The fallback kernel after a deviation is the punishing `δ_{e₀}`** (the `ξ`-null fallback is load-bearing). -/
theorem xie_of_ne {n : ℕ} {h : Hist A E n} {a : A} (ha : a ≠ D.π₀ n h) (e : E) :
    (model D).xie n h a e = if e = D.e₀ then 1 else 0 := by
  unfold Model.xie
  rw [if_pos (xinsA_of_ne D ha)]
  by_cases he : e = D.e₀ <;> simp [νe, ha, he, D.hδ.ne']

theorem dead_of_ne {n : ℕ} {h : Hist A E n} {a : A} (ha : a ≠ D.π₀ n h) :
    ¬ (model D).nonterminal (n + 1) (ext h a D.e₀) := fun hnt => by
  have := hnt.2
  rw [model_alive, (D.punish n h a ha).1] at this
  exact Bool.false_ne_true this

/-- Any `qval` with the kernel `ξ(e|·)` is `0` on a deviation: the only percept is `e₀`, which is dead with reward `0`. -/
theorem qval_of_ne (agg : Model.Agg A E) {n : ℕ} {h : Hist A E n} {a : A} (ha : a ≠ D.π₀ n h) :
    (model D).qval agg (model D).xie n h a = 0 := by
  unfold Model.qval
  rw [sum_eq_single D.e₀]
  · rw [xie_of_ne D ha, if_pos rfl, one_mul, (model D).val_eq_zero_of_not_nonterminal _ _ (dead_of_ne D ha),
      model_r, (D.punish n h a ha).2]
    ring
  · intro e _ he
    rw [xie_of_ne D ha, if_neg he, zero_mul]
  · intro habs; exact absurd (mem_univ _) habs

/-- **Every deviation has `Q_ξ = 0`** (under every policy), and `Q^* = 0`, `Q^π = 0` there too. -/
theorem Qxi_of_ne (π : Policy A E) {n : ℕ} {h : Hist A E n} {a : A} (ha : a ≠ D.π₀ n h) :
    (model D).Qxi π n h a = 0 := qval_of_ne D _ ha
theorem Qstar_of_ne {n : ℕ} {h : Hist A E n} {a : A} (ha : a ≠ D.π₀ n h) : (model D).Qstar n h a = 0 :=
  qval_of_ne D _ ha
theorem Qpi_of_ne (π : Policy A E) {n : ℕ} {h : Hist A E n} {a : A} (ha : a ≠ D.π₀ n h) :
    (model D).Qpi π n h a = 0 := qval_of_ne D _ ha

/-- **(a) `π₀` is a plain fixed point of the dogmatic model** for every `δ ∈ (0,1)`: every deviation is worth `0`
and `π₀(h)` is worth `≥ 0`. Explicitly: every deviation `a ≠ π₀(h)` is `ξ_{-S}`-null (the residual plays `π₀`),
so its percept kernel is the fallback — the residual's `δ_{e₀}` — and the deviation lands on a dead child of
reward `0` *regardless of `δ` and of anything else the residual does*; the "dogmatic prior" is entirely the
`ξ`-null fallback convention plus the punishing percept, which is the disclosed (c).
Source: mupi Prop 4.29 (finite form); [[uea-inventory]] 040
Kind: P
Fidelity: variant (see `DP`)
Hyps: (c) reward-through-percept and the punishing percept in place of mupi's reward-in-percept; the `ξ`-null fallback
convention at deviations -/
theorem pol_isPlainFP : (model D).IsPure (pol D) ∧ (model D).IsPlainFP (pol D) := by
  refine ⟨pol_isPure D, pol_isPolicy D, fun n h hnt a ha => ?_⟩
  have ha' : a = D.π₀ n h := by
    by_contra hne; rw [pol_ne D hne] at ha; exact lt_irrefl _ ha
  subst ha'
  apply le_antisymm ((model D).Qxi_le_Mx _ _ _)
  rw [(model D).Mx_le_iff]
  intro b
  by_cases hb : b = D.π₀ n h
  · rw [hb]
  · rw [Qxi_of_ne D _ hb]
    exact (model D).Qxi_nonneg (pol_isPolicy D) n h _

/-- The self-hypothesis's joint equals the residual's: `ξ_S(h) = ν(h)` under `π₀` (same actions, and the same percept
kernel `κ` along `π₀`). -/
theorem xiS_eq_nuJoint : ∀ (n : ℕ) (h : Hist A E n), (model D).xiS (pol D) n h = (model D).nuJoint () n h := by
  intro n
  induction n with
  | zero => intro h; simp
  | succ n ih =>
    intro h
    have hx := (model D).xiS_ext (pol D) (Fin.init h) (h (Fin.last n)).1 (h (Fin.last n)).2
    have hν := (model D).nuJoint_ext () (Fin.init h) (h (Fin.last n)).1 (h (Fin.last n)).2
    rw [ext_init_last] at hx hν
    rw [hx, hν, ih]
    by_cases ha : (h (Fin.last n)).1 = D.π₀ n (Fin.init h)
    · have hps : pol D n (Fin.init h) (h (Fin.last n)).1 = 1 := by rw [ha]; exact pol_self D n _
      rw [hps, ha]
      simp only [model_νa, νa, eq_self_iff_true, if_true, mul_one]
      by_cases hν0 : (model D).nuJoint () n (Fin.init h) = 0
      · rw [hν0]; ring
      · congr 1
        unfold Model.xie
        have hA : (model D).xinsA n (Fin.init h) (D.π₀ n (Fin.init h)) = D.δ * (model D).nuJoint () n (Fin.init h) := by
          simp [Model.xinsA, νa]
        rw [if_neg (by rw [hA]; exact mul_ne_zero D.hδ.ne' hν0), hA]
        simp [νa, νe]
        exact mul_div_cancel_left₀ _ (mul_ne_zero D.hδ.ne' hν0)
    · rw [pol_ne D ha]
      simp [νa, ha]

/-- **`w_h = 1 - δ` at every `κ`-reachable node** (`ν(h) > 0`): `ξ(h) = (1-δ)ν(h) + δν(h) = ν(h)`.
Source: mupi Prop 4.29 (finite form)
Kind: P
Fidelity: variant (see `DP`)
Hyps: (c) as above -/
theorem wS_eq {n : ℕ} {h : Hist A E n} (hν : 0 < (model D).nuJoint () n h) :
    (model D).wS (pol D) n h = 1 - D.δ := by
  have hxins : (model D).xins n h = D.δ * (model D).nuJoint () n h := by simp [Model.xins]
  have hxi : (model D).xi (pol D) n h = (model D).nuJoint () n h := by
    unfold Model.xi; rw [xiS_eq_nuJoint, hxins, model_δ]; ring
  rw [Model.wS_of_xi_ne_zero _ (by rw [hxi]; exact hν.ne'), hxi, xiS_eq_nuJoint, model_δ]
  field_simp

/-- **The `ξ`-yardstick sees no loss**: `V^* = V^{π₀}` at every history (the deviations are worth `0` to `ξ` and
`π₀(h)` is the only action with value) — the equilibrium is subjective.
Source: mupi Prop 4.29 (finite form); mandate target 17 ("Yardstick")
Kind: P
Fidelity: variant (see `DP`)
Hyps: (c) as above -/
theorem Vstar_eq_Vpi : ∀ n h, (model D).Vstar n h = (model D).Vpi (pol D) n h := by
  refine (model D).depth_induction (fun n h => (model D).Vstar n h = (model D).Vpi (pol D) n h) ?_ ?_
  · intro n h hnt
    rw [(model D).Vstar_of_not_nonterminal hnt, (model D).Vpi_of_not_nonterminal hnt]
  · intro n h hnt ih
    have hQ : (model D).Qstar n h (D.π₀ n h) = (model D).Qpi (pol D) n h (D.π₀ n h) := by
      rw [Model.Qstar_eq_sum, Model.Qpi_eq_sum]
      exact sum_congr rfl fun e _ => by rw [ih _ e]
    have hV : (model D).Vpi (pol D) n h = (model D).Qpi (pol D) n h (D.π₀ n h) := by
      rw [(model D).Vpi_eq hnt, sum_eq_single (D.π₀ n h)]
      · rw [pol_self, one_mul]
      · intro b _ hb; rw [pol_ne D hb, zero_mul]
      · intro habs; exact absurd (mem_univ _) habs
    rw [hV, (model D).Vstar_eq hnt]
    apply le_antisymm
    · rw [Finset.sup'_le_iff]
      intro b _
      by_cases hb : b = D.π₀ n h
      · rw [hb, hQ]
      · rw [Qstar_of_ne D hb]; exact (model D).Qpi_nonneg (pol_isPolicy D) n h _
    · rw [← hQ]; exact le_sup' _ (mem_univ _)

theorem gap_eq_zero (n : ℕ) (h : Hist A E n) : (model D).gap (pol D) n h = 0 := by
  unfold Model.gap; rw [Vstar_eq_Vpi, sub_self]

/-- **The trap against the true kernel**: the loss of `π₀` measured with the true percept kernel `κ`. -/
noncomputable def trueLoss : ℝ :=
  (model D).val Model.aggMax D.κ 0 (fun i => Fin.elim0 i) -
    (model D).val (Model.aggPol (pol D)) D.κ 0 (fun i => Fin.elim0 i)

end Dogmatic

/-! ### Witness: a one-step tree where the subjective equilibrium loses `1/2` against the truth -/

namespace Dogmatic

/-- The witness data: `A = E = Fin 2`, `T = 1`, `π₀ = stay (0)`, true kernel always `0`, `e₀ = 1`; `jump` with
percept `0` pays `1/2`, everything else `0`. -/
noncomputable def W : DP (Fin 2) (Fin 2) where
  T := 1
  alive := fun n _ => decide (n = 0)
  alive_init := fun n h hh => by cases n <;> simp at hh ⊢
  r := fun n h => match n with
    | 0 => if (h 0).1 = 1 ∧ (h 0).2 = 0 then 1 / 2 else 0
    | _ + 1 => 0
  r_nonneg := fun n h => by
    cases n
    · dsimp only; split_ifs <;> norm_num
    · exact le_rfl
  γ := 1
  γ_pos := one_pos
  γ_le_one := le_rfl
  norm := fun n hn h => by
    match n with
    | 0 => simp
    | 1 => simp only [pathReturnOf, pow_zero, one_mul, zero_add]; split_ifs <;> norm_num
    | n + 2 => omega
  κ := fun _ _ _ e => if e = 0 then 1 else 0
  κ_mem := fun _ _ _ => ⟨fun e => by show (0:ℝ) ≤ if e = 0 then 1 else 0; split_ifs <;> norm_num, by simp⟩
  π₀ := fun _ _ => 0
  e₀ := 1
  punish := fun n h a ha => ⟨by simp, by cases n <;> simp⟩
  δ := 1 / 2
  hδ := by norm_num
  hδ1 := by norm_num

/-- **Witness (N+)**: in `W`, `π₀ = stay` is a plain fixed point with `ξ`-loss `0`, but its loss against the true
kernel is `1/2` (`jump` then percept `0` pays `1/2`, which the dogmatic residual never sees).
Source: mandate target 17 ("the tree makes [the true loss] arbitrary")
Kind: N+
Fidelity: exact (a one-step tree suffices; the mandate's two-step tree is not needed)
Hyps: (a) -/
theorem witness : (model W).IsPlainFP (pol W) ∧ (model W).gap (pol W) 0 (fun i => Fin.elim0 i) = 0 ∧
    trueLoss W = 1 / 2 := by
  refine ⟨(pol_isPlainFP W).2, gap_eq_zero W 0 _, ?_⟩
  have hnt : (model W).nonterminal 0 (fun i => Fin.elim0 i) := ⟨by show 0 < 1; norm_num, rfl⟩
  have hterm : ∀ (h : Hist (Fin 2) (Fin 2) 1), ¬ (model W).nonterminal 1 h := fun h hn => by
    have := hn.1; exact absurd this (by show ¬ (1 < 1); norm_num)
  have hq : ∀ (agg : Model.Agg (Fin 2) (Fin 2)) (a : Fin 2), (model W).qval agg W.κ 0 (fun i => Fin.elim0 i) a =
      if a = 1 then 1 / 2 else 0 := by
    intro agg a
    unfold Model.qval
    rw [Fin.sum_univ_two, (model W).val_eq_zero_of_not_nonterminal _ _ (hterm _),
      (model W).val_eq_zero_of_not_nonterminal _ _ (hterm _)]
    fin_cases a <;> simp [W]
  unfold trueLoss
  rw [(model W).val_eq_of_nonterminal _ _ hnt, (model W).val_eq_of_nonterminal _ _ hnt]
  simp only [Model.aggMax, Model.aggPol, hq]
  rw [Fin.sum_univ_two, Model.sup'_fin_two]
  simp [pol, W]

end Dogmatic

/-! ### (b) Without a punishing percept, "any deterministic policy" is false -/

namespace NoPunish

/-- The two-node instance: `T = 1`, `E = Unit`, `jump (1) ↦ 1`, `stay (0) ↦ 1/2`, the residual plays `stay`. -/
noncomputable def model : Model (Fin 2) Unit Unit where
  T := 1
  alive := fun n _ => decide (n = 0)
  alive_init := fun n h hh => by cases n <;> simp at hh ⊢
  r := fun n h => match n with
    | 0 => if (h 0).1 = 1 then 1 else 1 / 2
    | _ + 1 => 0
  r_nonneg := fun n h => by
    cases n
    · dsimp only; split_ifs <;> norm_num
    · exact le_rfl
  γ := 1
  γ_pos := one_pos
  γ_le_one := le_rfl
  norm := fun n hn h => by
    match n with
    | 0 => simp
    | 1 => simp only [pathReturnOf, pow_zero, one_mul, zero_add]; split_ifs <;> norm_num
    | n + 2 => omega
  νa := fun _ _ _ a => if a = 0 then 1 else 0
  νe := fun _ _ _ _ _ => 1
  νa_mem := fun _ _ _ => ⟨fun a => by show (0:ℝ) ≤ if a = 0 then 1 else 0; split_ifs <;> norm_num, by simp⟩
  νe_mem := fun _ _ _ _ => ⟨fun _ => zero_le_one, by simp⟩
  w := fun _ => 1 / 2
  w_nonneg := fun _ => by norm_num
  δ := 1 / 2
  w_sum := by simp
  δ_pos := by norm_num
  δ_lt_one := by norm_num

/-- The pure `stay` policy. -/
noncomputable def stay : Policy (Fin 2) Unit := fun _ _ a => if a = 0 then 1 else 0

/-- The root history of a two-action, `Unit`-percept tree.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def root : Hist (Fin 2) Unit 0 := fun i => Fin.elim0 i

/-- **The general lemma behind (b)** (mandate target 17 (b): "an action whose every continuation pays more than the
alternatives' maximum is in every argmax"): on a one-step tree with a unique percept, `Q_ξ(root, a)` is the tree
reward of `a` for **every** policy and **every** residual class (`ι`, `νa`, `νe`, `w`, `δ`) — the residual cannot
move it, because with one percept the kernel is forced and the children are terminal.
Source: mandate target 17 (b); [[uea-inventory]] 040
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Qxi_eq_reward_of_unique {ι : Type} [Fintype ι] (M : Model (Fin 2) Unit ι) (hT : M.T = 1)
    (π : Policy (Fin 2) Unit) (a : Fin 2) :
    M.Qxi π 0 root a = M.r 0 (ext root a ()) := by
  have hterm : ∀ (h : Hist (Fin 2) Unit 1), ¬ M.nonterminal 1 h := fun h hn => by
    have := hn.1; rw [hT] at this; exact absurd this (lt_irrefl 1)
  rw [M.Qxi_eq_of_children_terminal _ a (fun e => hterm _)]
  rw [Fintype.sum_unique, M.xie_eq_one_of_unique]
  simp

/-- **(b) Finding — the refutation of the unqualified transcription, quantified over every residual class**: on the
two-node tree with tree-fixed rewards `jump ↦ 1`, `stay ↦ 1/2` and no punishing percept (`E = Unit`), the
deterministic policy `stay` is **not** a plain fixed point of **any** model on that tree — whatever the index type
`ι`, the residual kernels `νa`, `νe`, the weights `w` and the prior `δ`. So "any deterministic policy is a plain
fixed point of *some* dogmatic prior" is false with tree-fixed rewards: no residual class rescues `stay`, because
`jump` pays its tree-fixed `1 > 1/2` whatever the residual expects (`Qxi_eq_reward_of_unique`). mupi's statement
needs the reward to come through the percept (the punishing `e₀` of `Dogmatic.model`).
Source: mupi Prop 4.29 ("any deterministic policy"); [[uea-inventory]] 040; mandate target 17 (b)
Kind: P
Fidelity: exact (a refutation of the existential-over-priors transcription in the finite model; the tree is the smallest
one on which the question arises)
Hyps: (a) -/
theorem stay_not_isPlainFP_any_residual {ι : Type} [Fintype ι] (M : Model (Fin 2) Unit ι)
    (hT : M.T = 1) (halive : M.alive 0 root = true)
    (hr : ∀ h : Hist (Fin 2) Unit 1, M.r 0 h = if (h 0).1 = 1 then 1 else 1 / 2) :
    ¬ M.IsPlainFP stay := by
  rintro ⟨_, hfp⟩
  have hnt : M.nonterminal 0 root := ⟨by rw [hT]; norm_num, halive⟩
  have hQ : ∀ a, M.Qxi stay 0 root a = if a = 1 then 1 else 1 / 2 := by
    intro a
    rw [Qxi_eq_reward_of_unique M hT stay a, hr]
    simp [Cleanroom.Uea.UeaColeShadow.ext, Fin.snoc]
  have := hfp 0 root hnt 0 (by simp [stay])
  rw [hQ 0, M.Mx_fin_two, hQ 0, hQ 1] at this
  norm_num at this

/-- **(b) The instance (N−)**: the one fixed model `NoPunish.model` (the residual that plays `stay`) is a case of
`stay_not_isPlainFP_any_residual`. Degenerate by design: the smallest tree; the quantified theorem above is the
refutation, this is its inhabitant.
Source: mupi Prop 4.29 ("any deterministic policy"); [[uea-inventory]] 040; mandate target 17 (b)
Kind: N-
Fidelity: exact (one residual class; see `stay_not_isPlainFP_any_residual` for all of them)
Hyps: (a) -/
theorem stay_not_isPlainFP : ¬ model.IsPlainFP stay :=
  stay_not_isPlainFP_any_residual model rfl rfl (fun _ => rfl)

end NoPunish

end Cleanroom.Uea.UeaSinkSwim
