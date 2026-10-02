import Cleanroom.Uea.UeaSinkSwim.FiveTen

/-!
# The three-parameter twin `(δ, s, ρ)`: the twin kills the good point and makes the floor inert

`sos3 Q j₀ : Model (Fin 2) Unit (Fin 3)`: sink-or-swim with a third hypothesis `H_twin` of weight `(1-δ)ρ` that
jumps with probability `j₀` and then sinks; the model's non-self prior is `δ + (1-δ)ρ`, so the honest self has
prior `(1-δ)(1-ρ)`. The twin is "the same as `π` on the path" only when `j₀ = π(jump|island)`:
`IsTwinFP Q π := π(jump|island) = j₀ ∧ (sos3 Q j₀).IsPlainFP π` — **(c)**: a fixed kernel plus a
self-consistency clause stands in for a policy-dependent hypothesis (for pure `j₀` it is the note's object
exactly). Results: (i) the trap is a fixed point iff `s ≥ 1 - c/b`, `ρ`-free; (ii) the good point iff
`(1-δ)(1-ρ) + δ(1-s) ≥ c/b`; (iii) **the twin kills the good point**: for every `b, c, δ` there are `ρ, s` with
the trap a plain fixed point, the good point not, `w_self(island) = (1-δ)(1-ρ) < c/b` so `TB` holds at the trap,
and the trap a floored fixed point too — the floor is inert (mupi's Theorem 5.33 in finite form, Q5);
(iv) Cole's premise at the honest self: `(1-δ)(1-ρ) > 1 - δ'` iff `ρ < 1 - (1-δ')/(1-δ)`. `wS` in `sos3` is the
*honest* self's posterior (the twin is non-self by construction) — that is the point.

Scope: finite shadow of rOSI ([[sequential-self-game]] §7). Namespace `Cleanroom.Uea.UeaSinkSwim.Twin`
(faf-cleanroom run, `uea-sink-swim`, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Finset
open Cleanroom.Uea.UeaColeShadow
open Cleanroom.Uea.UeaColeShadow.SinkOrSwim

namespace Twin

/-- Twin parameters: a sink-or-swim `P` and the twin's share `ρ ∈ [0, 1)` of the self prior. -/
structure TwinP where
  P : Params
  ρ : ℝ
  hρ0 : 0 ≤ ρ
  hρ1 : ρ < 1

variable (Q : TwinP)

/-- Action kernels: `0 = H_swim`, `1 = H_sink` (jump, then swim / sink), `2 = H_twin` (jump w.p. `j₀`, then sink). -/
noncomputable def νa3 (j₀ : ℝ) : Fin 3 → (n : ℕ) → Hist (Fin 2) Unit n → Fin 2 → ℝ := fun i n _ a =>
  if n = 0 then (if i = 2 then (if a = 1 then j₀ else 1 - j₀) else (if a = 1 then 1 else 0))
  else (if i = 0 then (if a = 0 then 1 else 0) else (if a = 1 then 1 else 0))

theorem νa3_mem {j₀ : ℝ} (hj0 : 0 ≤ j₀) (hj1 : j₀ ≤ 1) (i : Fin 3) (n : ℕ) (h : Hist (Fin 2) Unit n) :
    νa3 j₀ i n h ∈ stdSimplex ℝ (Fin 2) := by
  refine ⟨fun a => ?_, ?_⟩
  · unfold νa3; split_ifs <;> linarith
  · unfold νa3; split_ifs <;> simp [Fin.sum_univ_two]

/-- **The three-parameter twin** `sos3 Q j₀`: `T = 2`, `γ = 1`, weights `δ(1-s), δ s, (1-δ)ρ`; non-self prior
`δ + (1-δ)ρ`, honest self prior `(1-δ)(1-ρ)`.
Source: [[02-mupi-c18-read]] Q4–Q5; [[uea-inventory]] 038, 037
Kind: D
Fidelity: exact (the twin's "same as `π` on the path" is the clause `j₀ = π(jump|island)` of `IsTwinFP`)
Hyps: n/a -/
noncomputable def sos3 (j₀ : ℝ) (hj0 : 0 ≤ j₀) (hj1 : j₀ ≤ 1) : Model (Fin 2) Unit (Fin 3) where
  T := 2
  alive := alive
  alive_init := alive_init
  r := r Q.P.b Q.P.c
  r_nonneg := r_nonneg Q.P
  γ := 1
  γ_pos := one_pos
  γ_le_one := le_rfl
  norm := norm Q.P
  νa := νa3 j₀
  νe := fun _ _ _ _ _ => 1
  νa_mem := νa3_mem hj0 hj1
  νe_mem := fun _ _ _ _ => ⟨fun _ => zero_le_one, by simp⟩
  w := fun i => if i = 0 then Q.P.δ * (1 - Q.P.s) else if i = 1 then Q.P.δ * Q.P.s else (1 - Q.P.δ) * Q.ρ
  w_nonneg := fun i => by
    have := Q.P.hδ; have := Q.P.hs0; have := Q.P.hs1; have := Q.P.hδ1; have := Q.hρ0
    split_ifs <;> nlinarith
  δ := Q.P.δ + (1 - Q.P.δ) * Q.ρ
  w_sum := by
    rw [Fin.sum_univ_three]
    show Q.P.δ * (1 - Q.P.s) + Q.P.δ * Q.P.s + (1 - Q.P.δ) * Q.ρ = _
    ring
  δ_pos := by have := Q.P.hδ; have := Q.P.hδ1; have := Q.hρ0; nlinarith
  δ_lt_one := by have := Q.P.hδ; have := Q.P.hδ1; have := Q.hρ1; nlinarith

/-- **The twin fixed point** (disclosed (c)): `π(jump|island) = j₀` and `π` is a plain fixed point of `sos3 Q j₀`.
Source: [[02-mupi-c18-read]] Q4–Q5; mandate target 3
Kind: D
Fidelity: variant: a fixed kernel plus a self-consistency clause in place of a policy-dependent hypothesis (disclosed (c))
Hyps: n/a -/
def IsTwinFP (π : Policy (Fin 2) Unit) : Prop :=
  ∃ hj : 0 ≤ π 0 island 1 ∧ π 0 island 1 ≤ 1, (sos3 Q (π 0 island 1) hj.1 hj.2).IsPlainFP π

section Values
variable (j₀ : ℝ) (hj0 : 0 ≤ j₀) (hj1 : j₀ ≤ 1)

local notation "M₃" => sos3 Q j₀ hj0 hj1

@[simp] theorem sos3_T : (M₃).T = 2 := rfl
@[simp] theorem sos3_alive : (M₃).alive = alive := rfl
@[simp] theorem sos3_δ : (M₃).δ = Q.P.δ + (1 - Q.P.δ) * Q.ρ := rfl
@[simp] theorem sos3_νa : (M₃).νa = νa3 j₀ := rfl
@[simp] theorem sos3_νe (i : Fin 3) (n : ℕ) (h : Hist (Fin 2) Unit n) (a : Fin 2) (e : Unit) : (M₃).νe i n h a e = 1 := rfl
@[simp] theorem sos3_w (i : Fin 3) :
    (M₃).w i = if i = 0 then Q.P.δ * (1 - Q.P.s) else if i = 1 then Q.P.δ * Q.P.s else (1 - Q.P.δ) * Q.ρ := rfl
@[simp] theorem sos3_r : (M₃).r = r Q.P.b Q.P.c := rfl
@[simp] theorem sos3_γ : (M₃).γ = 1 := rfl

theorem nt_island3 : (M₃).nonterminal 0 island := ⟨by simp, rfl⟩
theorem nt_water3 : (M₃).nonterminal 1 water := ⟨by simp, by simp [alive, water]⟩
theorem not_nt_stay3 : ¬ (M₃).nonterminal 1 (ext island 0 ()) := fun h => by
  have := h.2; simp [alive] at this
theorem not_nt_two3 (h : Hist (Fin 2) Unit 2) : ¬ (M₃).nonterminal 2 h := fun h' => by
  have := h'.1; simp at this
theorem not_nt_ge_two3 (n : ℕ) (hn : 2 ≤ n) (h : Hist (Fin 2) Unit n) : ¬ (M₃).nonterminal n h :=
  (M₃).not_nonterminal_of_le (by simpa using hn) h
theorem eq_water_of_nonterminal3 (h : Hist (Fin 2) Unit 1) (hnt : (M₃).nonterminal 1 h) : h = water := by
  have h0 : (h 0).1 = 1 := by have := hnt.2; simpa [alive] using this
  funext i
  fin_cases i
  exact Prod.ext h0 (Subsingleton.elim _ _)

theorem xie3_eq_one (n : ℕ) (h : Hist (Fin 2) Unit n) (a : Fin 2) (e : Unit) : (M₃).xie n h a e = 1 :=
  (M₃).xie_eq_one_of_unique n h a e

theorem xins3_water : (M₃).xins 1 water = Q.P.δ + (1 - Q.P.δ) * Q.ρ * j₀ := by
  simp [Model.xins, Fin.sum_univ_three, water, νa3] <;> ring

theorem xinsA3_water_swim : (M₃).xinsA 1 water 0 = Q.P.δ * (1 - Q.P.s) := by
  simp [Model.xinsA, Fin.sum_univ_three, water, νa3]

theorem xinsA3_water_sink : (M₃).xinsA 1 water 1 = Q.P.δ * Q.P.s + (1 - Q.P.δ) * Q.ρ * j₀ := by
  simp [Model.xinsA, Fin.sum_univ_three, water, νa3] <;> ring

variable (π : Policy (Fin 2) Unit)

theorem xiS3_water : (M₃).xiS π 1 water = π 0 island 1 := by simp [water, xie3_eq_one]

theorem xi3_island : (M₃).xi π 0 island = 1 := by
  unfold Model.xi Model.xins
  simp [Fin.sum_univ_three]
  ring

theorem xi3_water : (M₃).xi π 1 water = (1 - Q.P.δ) * (1 - Q.ρ) * π 0 island 1 + (Q.P.δ + (1 - Q.P.δ) * Q.ρ * j₀) := by
  unfold Model.xi
  rw [xins3_water, xiS3_water, sos3_δ]
  ring

theorem xiA3_water_swim : (M₃).xiA π 1 water 0 = (1 - Q.P.δ) * (1 - Q.ρ) * π 0 island 1 * π 1 water 0 + Q.P.δ * (1 - Q.P.s) := by
  rw [Model.xiA_eq, xiS3_water, xinsA3_water_swim, sos3_δ]
  ring

/-- `w_island = (1-δ)(1-ρ)`: the **honest** self's posterior at the root (the twin is non-self). -/
theorem wS3_island : (M₃).wS π 0 island = (1 - Q.P.δ) * (1 - Q.ρ) := by
  rw [Model.wS_of_xi_ne_zero _ (by rw [xi3_island]; exact one_ne_zero), xi3_island, Model.xiS_zero, sos3_δ]
  ring

theorem Qxi3_water_0 : (M₃).Qxi π 1 water 0 = Q.P.b := by
  rw [(M₃).Qxi_eq_of_children_terminal water 0 (fun e => not_nt_two3 Q j₀ hj0 hj1 _)]
  simp [xie3_eq_one, r, water]
theorem Qxi3_water_1 : (M₃).Qxi π 1 water 1 = 0 := by
  rw [(M₃).Qxi_eq_of_children_terminal water 1 (fun e => not_nt_two3 Q j₀ hj0 hj1 _)]
  simp [xie3_eq_one, r, water]
theorem Qstar3_water_0 : (M₃).Qstar 1 water 0 = Q.P.b := by
  rw [(M₃).Qstar_eq_of_children_terminal water 0 (fun e => not_nt_two3 Q j₀ hj0 hj1 _)]
  simp [xie3_eq_one, r, water]
theorem Qstar3_water_1 : (M₃).Qstar 1 water 1 = 0 := by
  rw [(M₃).Qstar_eq_of_children_terminal water 1 (fun e => not_nt_two3 Q j₀ hj0 hj1 _)]
  simp [xie3_eq_one, r, water]
theorem Mx3_water : (M₃).Mx π 1 water = Q.P.b := by
  rw [(M₃).Mx_fin_two, Qxi3_water_0, Qxi3_water_1]
  exact max_eq_left (by linarith [Q.P.hc, Q.P.hcb])
theorem Vstar3_water : (M₃).Vstar 1 water = Q.P.b := by
  rw [(M₃).Vstar_fin_two (nt_water3 Q j₀ hj0 hj1), Qstar3_water_0, Qstar3_water_1]
  exact max_eq_left (by linarith [Q.P.hc, Q.P.hcb])
theorem Qxi3_island_0 : (M₃).Qxi π 0 island 0 = Q.P.c := by
  rw [(M₃).Qxi_eq_of_children_terminal island 0 (fun e => by cases e; exact not_nt_stay3 Q j₀ hj0 hj1)]
  simp [xie3_eq_one, r]
theorem Qstar3_island_0 : (M₃).Qstar 0 island 0 = Q.P.c := by
  rw [(M₃).Qstar_eq_of_children_terminal island 0 (fun e => by cases e; exact not_nt_stay3 Q j₀ hj0 hj1)]
  simp [xie3_eq_one, r]
theorem Qstar3_island_1 : (M₃).Qstar 0 island 1 = Q.P.b := by
  rw [Model.Qstar_eq_sum, Fintype.sum_unique, xie3_eq_one]
  simp [r]
  exact Vstar3_water Q j₀ hj0 hj1
theorem Vstar3_island : (M₃).Vstar 0 island = Q.P.b := by
  rw [(M₃).Vstar_fin_two (nt_island3 Q j₀ hj0 hj1), Qstar3_island_0, Qstar3_island_1]
  exact max_eq_right Q.P.hcb.le

/-- The closed form `Q_ξ(island, jump) = b((1-δ)(1-ρ) j σ + δ(1-s)) / ((1-δ)(1-ρ) j + δ + (1-δ)ρ j₀)`. -/
theorem Qxi3_island_1 (hπ : (M₃).IsPolicy π) : (M₃).Qxi π 0 island 1 =
    Q.P.b * ((1 - Q.P.δ) * (1 - Q.ρ) * π 0 island 1 * π 1 water 0 + Q.P.δ * (1 - Q.P.s)) /
      ((1 - Q.P.δ) * (1 - Q.ρ) * π 0 island 1 + (Q.P.δ + (1 - Q.P.δ) * Q.ρ * j₀)) := by
  have hδ := Q.P.hδ; have hδ1 := Q.P.hδ1; have hρ0 := Q.hρ0; have hρ1 := Q.hρ1
  have hx : (M₃).xi π 1 water ≠ 0 := by
    rw [xi3_water]
    have := hπ.nonneg (nt_island3 Q j₀ hj0 hj1) 1
    have h1 : (0:ℝ) ≤ (1 - Q.P.δ) * (1 - Q.ρ) * π 0 island 1 := by
      have : (0:ℝ) < 1 - Q.P.δ := by linarith
      have : (0:ℝ) < 1 - Q.ρ := by linarith
      positivity
    have h2 : (0:ℝ) ≤ (1 - Q.P.δ) * Q.ρ * j₀ := by
      have : (0:ℝ) < 1 - Q.P.δ := by linarith
      positivity
    linarith
  rw [Model.Qxi_eq_sum, Fintype.sum_unique, xie3_eq_one]
  simp only [r, sos3_r, sos3_γ, pow_zero, one_mul, ext_zero_zero, Fin.isValue]
  rw [if_neg (by decide), zero_add]
  show (M₃).Vxi π 1 water = _
  rw [(M₃).Vxi_eq (nt_water3 Q j₀ hj0 hj1), Fin.sum_univ_two, Qxi3_water_0, Qxi3_water_1]
  simp only [Model.xia, hx, if_false, mul_zero, add_zero]
  rw [xiA3_water_swim, xi3_water]
  ring

/-- Every plain fixed point of `sos3` swims. -/
theorem swim_of_isPlainFP3 (hfp : (M₃).IsPlainFP π) : π 1 water 0 = 1 := by
  have hπ := hfp.1
  have h1 : π 1 water 1 = 0 := by
    by_contra hne
    have hpos : 0 < π 1 water 1 := lt_of_le_of_ne (hπ.nonneg (nt_water3 Q j₀ hj0 hj1) 1) (Ne.symm hne)
    have := hfp.2 1 water (nt_water3 Q j₀ hj0 hj1) 1 hpos
    rw [Qxi3_water_1, Mx3_water] at this
    linarith [Q.P.hc, Q.P.hcb]
  rw [hπ.fin_two_zero (nt_water3 Q j₀ hj0 hj1), h1, sub_zero]

/-- The plain fixed points of `sos3` in raw form (as for `sos`: swim, and the island conditions). -/
theorem isPlainFP3_iff (hπ : (M₃).IsPolicy π) :
    (M₃).IsPlainFP π ↔ π 1 water 0 = 1 ∧
      (π 0 island 1 < 1 → (M₃).Qxi π 0 island 1 ≤ Q.P.c) ∧
      (0 < π 0 island 1 → Q.P.c ≤ (M₃).Qxi π 0 island 1) := by
  constructor
  · intro hfp
    refine ⟨swim_of_isPlainFP3 Q j₀ hj0 hj1 π hfp, fun hj => ?_, fun hj => ?_⟩
    · have h0 : 0 < π 0 island 0 := by rw [hπ.fin_two_zero (nt_island3 Q j₀ hj0 hj1)]; linarith
      have := hfp.2 0 island (nt_island3 Q j₀ hj0 hj1) 0 h0
      rw [Qxi3_island_0, (M₃).Mx_fin_two, Qxi3_island_0] at this
      exact max_eq_left_iff.1 this.symm
    · have := hfp.2 0 island (nt_island3 Q j₀ hj0 hj1) 1 hj
      rw [(M₃).Mx_fin_two, Qxi3_island_0] at this
      exact max_eq_right_iff.1 this.symm
  · rintro ⟨hσ, h1, h2⟩
    refine ⟨hπ, fun n h hnt => ?_⟩
    match n with
    | 0 =>
      rw [eq_island h]
      refine Fin.forall_fin_two.2 ⟨fun h0 => ?_, fun hj => ?_⟩
      · rw [hπ.fin_two_zero (nt_island3 Q j₀ hj0 hj1)] at h0
        rw [(M₃).Mx_fin_two, Qxi3_island_0, max_eq_left (h1 (by linarith))]
      · rw [(M₃).Mx_fin_two, Qxi3_island_0, max_eq_right (h2 hj)]
    | 1 =>
      rw [eq_water_of_nonterminal3 Q j₀ hj0 hj1 h hnt]
      refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun ha => ?_⟩
      · rw [Mx3_water, Qxi3_water_0]
      · have h0 := hπ.fin_two_zero (nt_water3 Q j₀ hj0 hj1)
        rw [hσ] at h0
        linarith
    | n + 2 => exact absurd hnt (not_nt_ge_two3 Q j₀ hj0 hj1 (n + 2) (by omega) h)

end Values

/-! ### (i) the trap, `ρ`-free; (ii) the good point -/

theorem trap_isPolicy3 (j₀ : ℝ) (hj0 : 0 ≤ j₀) (hj1 : j₀ ≤ 1) : (sos3 Q j₀ hj0 hj1).IsPolicy trap := by
  intro n h _
  refine ⟨fun a => ?_, ?_⟩
  · unfold trap; split_ifs <;> norm_num
  · simp [trap]

theorem good_isPolicy3 (j₀ : ℝ) (hj0 : 0 ≤ j₀) (hj1 : j₀ ≤ 1) : (sos3 Q j₀ hj0 hj1).IsPolicy TheoremA.good := by
  intro n h _
  refine ⟨fun a => ?_, ?_⟩
  · by_cases hn : n = 0 <;> fin_cases a <;> simp [TheoremA.good, hn]
  · by_cases hn : n = 0 <;> simp [TheoremA.good, hn]

/-- **(i) the trap**: `Q_ξ(island, jump) = b(1-s)` and the trap is a twin fixed point iff `b(1-s) ≤ c` — `ρ`-free.
Source: [[02-mupi-c18-read]] Q4; mandate target 3 (i)
Kind: P
Fidelity: exact
Hyps: (c) the twin clause `j₀ = π(jump|island) = 0` (`IsTwinFP`) -/
theorem trap_twinFP_iff :
    (sos3 Q 0 le_rfl zero_le_one).Qxi trap 0 island 1 = Q.P.b * (1 - Q.P.s) ∧
    (IsTwinFP Q trap ↔ Q.P.b * (1 - Q.P.s) ≤ Q.P.c) := by
  have hδ := Q.P.hδ.ne'
  have hQ : (sos3 Q 0 le_rfl zero_le_one).Qxi trap 0 island 1 = Q.P.b * (1 - Q.P.s) := by
    have hj0 : trap 0 island 1 = 0 := by simp [trap]
    have hσ : trap 1 water 0 = 1 := by simp [trap]
    rw [Qxi3_island_1 Q 0 le_rfl zero_le_one trap (trap_isPolicy3 Q 0 le_rfl zero_le_one), hj0, hσ,
      show (1 - Q.P.δ) * (1 - Q.ρ) * 0 * 1 + Q.P.δ * (1 - Q.P.s) = Q.P.δ * (1 - Q.P.s) by ring,
      show (1 - Q.P.δ) * (1 - Q.ρ) * 0 + (Q.P.δ + (1 - Q.P.δ) * Q.ρ * 0) = Q.P.δ by ring,
      mul_div_assoc, mul_div_cancel_left₀ _ hδ]
  refine ⟨hQ, ?_⟩
  have hj : trap 0 island 1 = 0 := by simp [trap]
  constructor
  · rintro ⟨hj', hfp⟩
    have hfp' : (sos3 Q 0 le_rfl zero_le_one).IsPlainFP trap := by
      convert hfp using 2 <;> simp [trap]
    have := ((isPlainFP3_iff Q 0 le_rfl zero_le_one trap (trap_isPolicy3 Q 0 le_rfl zero_le_one)).1 hfp').2.1
      (by rw [hj]; norm_num)
    rwa [hQ] at this
  · intro h
    refine ⟨⟨by rw [hj], by rw [hj]; norm_num⟩, ?_⟩
    have : (sos3 Q 0 le_rfl zero_le_one).IsPlainFP trap :=
      (isPlainFP3_iff Q 0 le_rfl zero_le_one trap (trap_isPolicy3 Q 0 le_rfl zero_le_one)).2
        ⟨by simp [trap], fun _ => by rw [hQ]; exact h, fun h0 => by rw [hj] at h0; exact absurd h0 (lt_irrefl 0)⟩
    convert this using 2 <;> simp [trap]

/-- **(ii) the good point**: `Q_ξ(island, jump) = b[(1-δ)(1-ρ) + δ(1-s)]` (denominator `1`) and the good point is a
twin fixed point iff `(1-δ)(1-ρ) + δ(1-s) ≥ c/b`.
Source: [[02-mupi-c18-read]] Q4; mandate target 3 (ii)
Kind: P
Fidelity: exact
Hyps: (c) the twin clause `j₀ = π(jump|island) = 1` -/
theorem good_twinFP_iff :
    (sos3 Q 1 zero_le_one le_rfl).Qxi TheoremA.good 0 island 1 =
      Q.P.b * ((1 - Q.P.δ) * (1 - Q.ρ) + Q.P.δ * (1 - Q.P.s)) ∧
    (IsTwinFP Q TheoremA.good ↔ Q.P.c ≤ Q.P.b * ((1 - Q.P.δ) * (1 - Q.ρ) + Q.P.δ * (1 - Q.P.s))) := by
  have hQ : (sos3 Q 1 zero_le_one le_rfl).Qxi TheoremA.good 0 island 1 =
      Q.P.b * ((1 - Q.P.δ) * (1 - Q.ρ) + Q.P.δ * (1 - Q.P.s)) := by
    have hj1 : TheoremA.good 0 island 1 = 1 := by simp [TheoremA.good]
    have hσ : TheoremA.good 1 water 0 = 1 := by simp [TheoremA.good]
    rw [Qxi3_island_1 Q 1 zero_le_one le_rfl _ (good_isPolicy3 Q 1 zero_le_one le_rfl), hj1, hσ]
    have hden : (1 - Q.P.δ) * (1 - Q.ρ) * 1 + (Q.P.δ + (1 - Q.P.δ) * Q.ρ * 1) = 1 := by ring
    rw [hden, div_one]
    ring
  refine ⟨hQ, ?_⟩
  have hj : TheoremA.good 0 island 1 = 1 := by simp [TheoremA.good]
  constructor
  · rintro ⟨hj', hfp⟩
    have hfp' : (sos3 Q 1 zero_le_one le_rfl).IsPlainFP TheoremA.good := by
      convert hfp using 2 <;> simp [TheoremA.good]
    have := ((isPlainFP3_iff Q 1 zero_le_one le_rfl _ (good_isPolicy3 Q 1 zero_le_one le_rfl)).1 hfp').2.2
      (by rw [hj]; norm_num)
    rwa [hQ] at this
  · intro h
    refine ⟨⟨by rw [hj]; norm_num, by rw [hj]⟩, ?_⟩
    have : (sos3 Q 1 zero_le_one le_rfl).IsPlainFP TheoremA.good :=
      (isPlainFP3_iff Q 1 zero_le_one le_rfl _ (good_isPolicy3 Q 1 zero_le_one le_rfl)).2
        ⟨by simp [TheoremA.good], fun h1 => by rw [hj] at h1; exact absurd h1 (lt_irrefl 1), fun _ => by rw [hQ]; exact h⟩
    convert this using 2 <;> simp [TheoremA.good]

/-! ### (iii) the twin kills the good point; the floor is inert -/

/-- **(iii)** For every `b, c, δ` there are `ρ ∈ [0,1)` and `s` (here `s = 1`) such that the trap is a twin fixed point,
the good point is not, the honest self's posterior at the root is `(1-δ)(1-ρ) < c/b` so `TB` holds at the trap, and
the trap is a **floored** fixed point as well — the floor is inert (mupi's Theorem 5.33 in finite form).
Source: [[02-mupi-c18-read]] Q5; [[uea-inventory]] 038, 037; mandate target 3 (iii)
Kind: P
Fidelity: exact
Hyps: (c) the twin clause of `IsTwinFP` (the trap at `j₀ = 0`, the good point at `j₀ = 1`) -/
theorem twin_kills_good (P : Params) :
    ∃ (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1),
      let Q : TwinP := ⟨⟨P.b, P.c, P.δ, 1, P.hc, P.hcb, P.hb, P.hδ, P.hδ1, zero_le_one, le_rfl⟩, ρ, hρ0, hρ1⟩
      IsTwinFP Q trap ∧ ¬ IsTwinFP Q TheoremA.good ∧
        (sos3 Q 0 le_rfl zero_le_one).wS trap 0 island = (1 - P.δ) * (1 - ρ) ∧
        (1 - P.δ) * (1 - ρ) < P.c / P.b ∧ (sos3 Q 0 le_rfl zero_le_one).TB trap 0 island ∧
        (sos3 Q 0 le_rfl zero_le_one).IsFlooredFP trap := by
  have hb := TheoremA.b_pos P
  have hc := P.hc; have hcb := P.hcb; have hδ := P.hδ; have hδ1 := P.hδ1
  have h1δ : 0 < 1 - P.δ := by linarith
  -- the choice of `ρ`
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ (1 - P.δ) * (1 - ρ) < P.c / P.b := by
    by_cases hcase : P.c ≤ 2 * P.b * (1 - P.δ)
    · refine ⟨1 - P.c / (2 * P.b * (1 - P.δ)), ?_, ?_, ?_⟩
      · have : P.c / (2 * P.b * (1 - P.δ)) ≤ 1 := (div_le_one (by positivity)).2 hcase
        linarith
      · have : 0 < P.c / (2 * P.b * (1 - P.δ)) := by positivity
        linarith
      · have hpos : 0 < 2 * P.b * (1 - P.δ) := by positivity
        rw [show (1 - P.δ) * (1 - (1 - P.c / (2 * P.b * (1 - P.δ)))) = P.c / (2 * P.b) by field_simp; ring]
        rw [div_lt_div_iff₀ (by positivity) hb]
        nlinarith
    · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
      have hcase' := not_le.1 hcase
      rw [sub_zero, mul_one, lt_div_iff₀ hb]
      nlinarith
  refine ⟨ρ, hρ0, hρ1, ?_⟩
  intro Q
  have hs : Q.P.s = 1 := rfl
  have htrap : IsTwinFP Q trap := (trap_twinFP_iff Q).2.2 (by rw [hs]; simp; exact hc.le)
  have hgood : ¬ IsTwinFP Q TheoremA.good := by
    rw [(good_twinFP_iff Q).2]
    rw [hs]
    have : (1 - P.δ) * (1 - ρ) * P.b < P.c := (lt_div_iff₀ hb).1 hρ
    show ¬ P.c ≤ P.b * ((1 - P.δ) * (1 - ρ) + P.δ * (1 - 1))
    intro h
    nlinarith
  have hw : (sos3 Q 0 le_rfl zero_le_one).wS trap 0 island = (1 - P.δ) * (1 - ρ) := wS3_island Q 0 le_rfl zero_le_one trap
  have hM : (sos3 Q 0 le_rfl zero_le_one).Mx trap 0 island = P.c := by
    rw [(sos3 Q 0 le_rfl zero_le_one).Mx_fin_two, Qxi3_island_0, (trap_twinFP_iff Q).1]
    show max P.c (P.b * (1 - 1)) = P.c
    simp; exact hc.le
  have hTB : (sos3 Q 0 le_rfl zero_le_one).TB trap 0 island := by
    unfold Model.TB
    rw [hw, Vstar3_island, hM]
    have := (lt_div_iff₀ hb).1 hρ
    show (1 - P.δ) * (1 - ρ) * P.b ≤ P.c
    exact this.le
  refine ⟨htrap, hgood, hw, hρ, hTB, ?_⟩
  -- floored: a plain fixed point with `resid ≥ 0` at both decision nodes
  obtain ⟨_, hfp⟩ := htrap
  have hfp' : (sos3 Q 0 le_rfl zero_le_one).IsPlainFP trap := by
    convert hfp using 2 <;> simp [trap]
  refine FiveTen.isFlooredFP_of_isPlainFP_of_resid_nonneg _ hfp' fun n h hnt => ?_
  match n with
  | 0 =>
    rw [eq_island h]
    unfold Model.resid
    unfold Model.TB at hTB
    linarith
  | 1 =>
    rw [eq_water_of_nonterminal3 Q 0 le_rfl zero_le_one h hnt]
    unfold Model.resid
    rw [Mx3_water, Vstar3_water]
    have hw1 := (sos3 Q 0 le_rfl zero_le_one).wS_le_one (trap_isPolicy3 Q 0 le_rfl zero_le_one) (nt_water3 Q 0 le_rfl zero_le_one)
    nlinarith
  | n + 2 => exact absurd hnt (not_nt_ge_two3 Q 0 le_rfl zero_le_one (n + 2) (by omega) h)

/-- **(iv) Cole's premise at the honest self**: `(1-δ)(1-ρ) > 1 - δ'` iff `ρ < 1 - (1-δ')/(1-δ)`.
Source: [[02-mupi-c18-read]] Q4; mandate target 3 (iv)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem premise_iff (δ δ' ρ : ℝ) (hδ1 : δ < 1) :
    1 - δ' < (1 - δ) * (1 - ρ) ↔ ρ < 1 - (1 - δ') / (1 - δ) := by
  have h : 0 < 1 - δ := by linarith
  constructor
  · intro hlt
    have : (1 - δ') / (1 - δ) < 1 - ρ := by rw [div_lt_iff₀ h]; linarith
    linarith
  · intro hlt
    have : (1 - δ') / (1 - δ) < 1 - ρ := by linarith
    rw [div_lt_iff₀ h] at this
    linarith

/-- **Witness (N+)**: `b = 1, c = 1/2, δ = 1/10, s = 1, ρ = 9/10`: the trap is a twin fixed point, the good point is
not (`(1-δ)(1-ρ) = 9/100 < 1/2`), `w_island = 9/100`, `TB` holds at the trap.
Source: mandate target 3 (witness)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem witness :
    let Q : TwinP := ⟨⟨1, 1 / 2, 1 / 10, 1, by norm_num, by norm_num, le_rfl, by norm_num, by norm_num, zero_le_one, le_rfl⟩,
      9 / 10, by norm_num, by norm_num⟩
    IsTwinFP Q trap ∧ ¬ IsTwinFP Q TheoremA.good ∧
      (sos3 Q 0 le_rfl zero_le_one).wS trap 0 island = 9 / 100 ∧ (sos3 Q 0 le_rfl zero_le_one).TB trap 0 island := by
  intro Q
  refine ⟨(trap_twinFP_iff Q).2.2 (by norm_num), ?_, ?_, ?_⟩
  · rw [(good_twinFP_iff Q).2]; norm_num
  · rw [wS3_island]; norm_num
  · unfold Model.TB
    rw [wS3_island, Vstar3_island, (sos3 Q 0 le_rfl zero_le_one).Mx_fin_two, Qxi3_island_0, (trap_twinFP_iff Q).1]
    norm_num

end Twin

end Cleanroom.Uea.UeaSinkSwim
