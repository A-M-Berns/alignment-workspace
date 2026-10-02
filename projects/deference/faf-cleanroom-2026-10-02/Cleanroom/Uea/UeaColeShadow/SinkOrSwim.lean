import Cleanroom.Uea.UeaColeShadow.TheoremB
import Cleanroom.Uea.UeaColeShadow.Instances
import Cleanroom.Uea.UeaColeShadow.Strict

/-!
# Sink-or-swim: the tightness witnesses for Theorem B

The two-step self-game of [[sequential-self-game]] §2 as a `Model` family `sos b c δ s`: island `stay`
(reward `c`, terminal) or `jump`; water `swim` (reward `b`) or `sink` (`0`); `0 < c < b ≤ 1`; deterministic
percepts, `γ = 1`; non-self hypotheses `H_sink` (jump, then sink) of weight `δ s` and `H_swim` (jump, then swim)
of weight `δ (1 - s)`. Actions are `Fin 2`: island `0 = stay`, `1 = jump`; water `0 = swim`, `1 = sink`;
hypothesis index `0 = H_swim`, `1 = H_sink`.
`j := π(jump|island)`, `σ := π(swim|water)`.

Here: the general closed form `Q_ξ(island, jump) = b ((1-δ) j σ + δ (1-s)) / ((1-δ) j + δ)`, and the two
witnesses Theorem B needs — the **tight trap** (`b = 1`, `c = 1 - δ`, `s = 1`: `j = 0` is a plain fixed point,
`(TB)` holds with equality, `gap / O_h = 1 - δ`, for every `δ ∈ (0,1)`) and a **genuinely mixed** trust-bound
fixed point (`b = 1`, `c = 1/2`, `δ = 1/2`, `s = 3/4`, `j = 1/2`: `(TB)` holds, `gap = 1/4 ≤ O_h = 1`). Theorem A
(the full characterization) is `uea-sink-swim`'s; `uea-sink-swim` reuses `sos`.

Source: [[sequential-self-game]] §2, §3 (Remarks, "Tightness"; "Where the mixed point sits").
-/

namespace Cleanroom.Uea.UeaColeShadow

open Finset

namespace SinkOrSwim

/-- Alive nodes: the island; the water (after `jump`). -/
def alive : (n : ℕ) → Hist (Fin 2) Unit n → Bool
  | 0, _ => true
  | 1, h => decide ((h 0).1 = 1)
  | _, _ => false

/-- Rewards on arrival: `stay` pays `c`; `jump, swim` pays `b`. -/
noncomputable def r (b c : ℝ) : (n : ℕ) → Hist (Fin 2) Unit (n + 1) → ℝ
  | 0, h => if (h 0).1 = 0 then c else 0
  | 1, h => if (h 0).1 = 1 ∧ (h 1).1 = 0 then b else 0
  | _, _ => 0

/-- Non-self action kernels: both hypotheses `jump` at the island; in the water hypothesis `i` plays action `i`:
`H_swim` is index `0` (weight `δ (1 - s)`), `H_sink` is index `1` (weight `δ s`). -/
noncomputable def νa : Fin 2 → (n : ℕ) → Hist (Fin 2) Unit n → Fin 2 → ℝ
  | _, 0, _, a => if a = 1 then 1 else 0
  | i, _, _, a => if a = i then 1 else 0

theorem νa_mem (i : Fin 2) (n : ℕ) (h : Hist (Fin 2) Unit n) : νa i n h ∈ stdSimplex ℝ (Fin 2) := by
  refine ⟨fun a => ?_, ?_⟩
  · match n with
    | 0 => simp only [νa]; split_ifs <;> norm_num
    | n + 1 => simp only [νa]; split_ifs <;> norm_num
  · match n with
    | 0 => simp [νa, Fin.sum_univ_two]
    | n + 1 => fin_cases i <;> simp [νa, Fin.sum_univ_two]

theorem alive_init (n : ℕ) (h : Hist (Fin 2) Unit (n + 1)) (hh : alive (n + 1) h = true) :
    alive n (Fin.init h) = true := by
  match n with
  | 0 => rfl
  | n + 1 => simp [alive] at hh

/-- The parameters of a sink-or-swim instance: `0 < c < b ≤ 1`, `0 < δ < 1`, `s ∈ [0,1]`.
Source: [[sequential-self-game]] §2
Kind: D
Fidelity: exact
Hyps: n/a -/
structure Params where
  b : ℝ
  c : ℝ
  δ : ℝ
  s : ℝ
  hc : 0 < c
  hcb : c < b
  hb : b ≤ 1
  hδ : 0 < δ
  hδ1 : δ < 1
  hs0 : 0 ≤ s
  hs1 : s ≤ 1

variable (P : Params)

theorem r_nonneg (n : ℕ) (h : Hist (Fin 2) Unit (n + 1)) : 0 ≤ r P.b P.c n h := by
  have := P.hc; have := P.hcb
  match n with
  | 0 => simp only [r]; split_ifs <;> linarith
  | 1 => simp only [r]; split_ifs <;> linarith
  | n + 2 => simp [r]

theorem norm (n : ℕ) (hn : n ≤ 2) (h : Hist (Fin 2) Unit n) : pathReturnOf 1 (r P.b P.c) n h ≤ 1 := by
  have := P.hc; have := P.hcb; have := P.hb
  match n with
  | 0 => simp
  | 1 =>
    simp only [pathReturnOf, r]
    split_ifs <;> linarith
  | 2 =>
    simp only [pathReturnOf, r, Fin.init, Fin.castSucc_zero]
    split_ifs <;> first | linarith | simp_all
  | n + 3 => omega

/-- **The sink-or-swim model** `sos P`: `T = 2`, `γ = 1`, weights `δ (1-s)` (swim, index `0`) and `δ s` (sink,
index `1`).
Source: [[sequential-self-game]] §2 ("Instance"); [[00-founding-sketches]] §1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def sos : Model (Fin 2) Unit (Fin 2) where
  T := 2
  alive := alive
  alive_init := alive_init
  r := r P.b P.c
  r_nonneg := r_nonneg P
  γ := 1
  γ_pos := one_pos
  γ_le_one := le_rfl
  norm := norm P
  νa := νa
  νe := fun _ _ _ _ _ => 1
  νa_mem := νa_mem
  νe_mem := fun _ _ _ _ => ⟨fun _ => zero_le_one, by simp⟩
  w := fun i => if i = 0 then P.δ * (1 - P.s) else P.δ * P.s
  w_nonneg := fun i => by have := P.hδ; have := P.hs0; have := P.hs1; split_ifs <;> nlinarith
  δ := P.δ
  w_sum := by simp [Fin.sum_univ_two]; ring
  δ_pos := P.hδ
  δ_lt_one := P.hδ1

/-- The island. -/
def island : Hist (Fin 2) Unit 0 := Fin.elim0
/-- The water `(jump)`. -/
def water : Hist (Fin 2) Unit 1 := ext island 1 ()

@[simp] theorem sos_T : (sos P).T = 2 := rfl
@[simp] theorem sos_alive : (sos P).alive = alive := rfl
@[simp] theorem sos_r : (sos P).r = r P.b P.c := rfl
@[simp] theorem sos_γ : (sos P).γ = 1 := rfl
@[simp] theorem sos_νa : (sos P).νa = νa := rfl
@[simp] theorem sos_νe (i : Fin 2) (n : ℕ) (h : Hist (Fin 2) Unit n) (a : Fin 2) (e : Unit) : (sos P).νe i n h a e = 1 := rfl
@[simp] theorem sos_w (i : Fin 2) : (sos P).w i = if i = 0 then P.δ * (1 - P.s) else P.δ * P.s := rfl
@[simp] theorem sos_δ : (sos P).δ = P.δ := rfl

theorem nt_island : (sos P).nonterminal 0 island := ⟨by simp, rfl⟩
theorem nt_water : (sos P).nonterminal 1 water := ⟨by simp, by simp [alive, water]⟩
theorem not_nt_stay : ¬ (sos P).nonterminal 1 (ext island 0 ()) := fun h => by
  have := h.2; simp [alive] at this
theorem not_nt_two (h : Hist (Fin 2) Unit 2) : ¬ (sos P).nonterminal 2 h := fun h' => by
  have := h'.1; simp at this
theorem not_nt_ge_two (n : ℕ) (hn : 2 ≤ n) (h : Hist (Fin 2) Unit n) : ¬ (sos P).nonterminal n h :=
  (sos P).not_nonterminal_of_le (by simpa using hn) h

theorem eq_island (h : Hist (Fin 2) Unit 0) : h = island := funext fun i => Fin.elim0 i
theorem eq_water_of_nonterminal (h : Hist (Fin 2) Unit 1) (hnt : (sos P).nonterminal 1 h) : h = water := by
  have h0 : (h 0).1 = 1 := by have := hnt.2; simpa [alive] using this
  funext i
  fin_cases i
  exact Prod.ext h0 (Subsingleton.elim _ _)

theorem xie_eq_one (n : ℕ) (h : Hist (Fin 2) Unit n) (a : Fin 2) (e : Unit) : (sos P).xie n h a e = 1 :=
  (sos P).xie_eq_one_of_unique n h a e

theorem xins_island : (sos P).xins 0 island = P.δ := by simp [Model.xins, Fin.sum_univ_two]; ring
theorem xins_water : (sos P).xins 1 water = P.δ := by simp [Model.xins, Fin.sum_univ_two, water, νa]; ring
theorem xinsA_water_swim : (sos P).xinsA 1 water 0 = P.δ * (1 - P.s) := by
  simp [Model.xinsA, Fin.sum_univ_two, water, νa]
theorem xinsA_water_sink : (sos P).xinsA 1 water 1 = P.δ * P.s := by
  simp [Model.xinsA, Fin.sum_univ_two, water, νa]

section Values
variable (π : Policy (Fin 2) Unit)

theorem xiS_water : (sos P).xiS π 1 water = π 0 island 1 := by simp [water, xie_eq_one]
theorem xiS_stay : (sos P).xiS π 1 (ext island 0 ()) = π 0 island 0 := by simp [xie_eq_one]

theorem xi_island : (sos P).xi π 0 island = 1 := by
  unfold Model.xi; rw [xins_island, Model.xiS_zero, sos_δ]; ring
theorem xi_water : (sos P).xi π 1 water = (1 - P.δ) * π 0 island 1 + P.δ := by
  unfold Model.xi; rw [xins_water, xiS_water, sos_δ]
theorem xiA_water_swim : (sos P).xiA π 1 water 0 = (1 - P.δ) * π 0 island 1 * π 1 water 0 + P.δ * (1 - P.s) := by
  rw [Model.xiA_eq, xiS_water, xinsA_water_swim, sos_δ]

theorem wS_island : (sos P).wS π 0 island = 1 - P.δ := by
  rw [Model.wS_of_xi_ne_zero _ (by rw [xi_island]; exact one_ne_zero), xi_island, Model.xiS_zero, sos_δ]
  ring

theorem Vstar_water : (sos P).Vstar 1 water = P.b := by
  have := P.hc; have := P.hcb
  rw [(sos P).Vstar_fin_two (nt_water P), (sos P).Qstar_eq_of_children_terminal water 0 (fun e => not_nt_two P _),
    (sos P).Qstar_eq_of_children_terminal water 1 (fun e => not_nt_two P _)]
  simp [xie_eq_one, r, water]
  linarith

theorem Qstar_island_0 : (sos P).Qstar 0 island 0 = P.c := by
  rw [(sos P).Qstar_eq_of_children_terminal island 0 (fun e => by cases e; exact not_nt_stay P)]
  simp [xie_eq_one, r]

theorem Qstar_island_1 : (sos P).Qstar 0 island 1 = P.b := by
  rw [Model.Qstar_eq_sum, Fintype.sum_unique, xie_eq_one]
  simp [r]
  exact Vstar_water P

theorem Vstar_island : (sos P).Vstar 0 island = P.b := by
  have := P.hcb
  rw [(sos P).Vstar_fin_two (nt_island P), Qstar_island_0, Qstar_island_1]
  exact max_eq_right (by linarith)

theorem Qxi_water_0 : (sos P).Qxi π 1 water 0 = P.b := by
  rw [(sos P).Qxi_eq_of_children_terminal water 0 (fun e => not_nt_two P _)]
  simp [xie_eq_one, r, water]
theorem Qxi_water_1 : (sos P).Qxi π 1 water 1 = 0 := by
  rw [(sos P).Qxi_eq_of_children_terminal water 1 (fun e => not_nt_two P _)]
  simp [xie_eq_one, r, water]
theorem Qpi_water_0 : (sos P).Qpi π 1 water 0 = P.b := by
  rw [(sos P).Qpi_eq_of_children_terminal water 0 (fun e => not_nt_two P _)]
  simp [xie_eq_one, r, water]
theorem Qpi_water_1 : (sos P).Qpi π 1 water 1 = 0 := by
  rw [(sos P).Qpi_eq_of_children_terminal water 1 (fun e => not_nt_two P _)]
  simp [xie_eq_one, r, water]
theorem Mx_water : (sos P).Mx π 1 water = P.b := by
  have := P.hc; have := P.hcb
  rw [(sos P).Mx_fin_two, Qxi_water_0, Qxi_water_1]
  exact max_eq_left (by linarith)

theorem Qxi_island_0 : (sos P).Qxi π 0 island 0 = P.c := by
  rw [(sos P).Qxi_eq_of_children_terminal island 0 (fun e => by cases e; exact not_nt_stay P)]
  simp [xie_eq_one, r]
theorem Qpi_island_0 : (sos P).Qpi π 0 island 0 = P.c := by
  rw [(sos P).Qpi_eq_of_children_terminal island 0 (fun e => by cases e; exact not_nt_stay P)]
  simp [xie_eq_one, r]
theorem Qpi_island_1 : (sos P).Qpi π 0 island 1 = (sos P).Vpi π 1 water := by
  rw [Model.Qpi_eq_sum, Fintype.sum_unique, xie_eq_one]
  simp [r]
  rfl

/-- **Theorem A's closed form**: `Q_ξ(island, jump) = b ((1-δ) j σ + δ (1-s)) / ((1-δ) j + δ)`.
Source: [[sequential-self-game]] §2 (Theorem A, with `σ = π(swim|water)` explicit; at `σ = 1` it is the note's)
Kind: P
Fidelity: exact (with `σ` explicit)
Hyps: (a) -/
theorem Qxi_island_1 (hπ : (sos P).IsPolicy π) : (sos P).Qxi π 0 island 1 =
    P.b * ((1 - P.δ) * π 0 island 1 * π 1 water 0 + P.δ * (1 - P.s)) / ((1 - P.δ) * π 0 island 1 + P.δ) := by
  have hδ := P.hδ; have hδ1 := P.hδ1
  have hx : (sos P).xi π 1 water ≠ 0 := by
    rw [xi_water]
    have := hπ.nonneg (nt_island P) 1
    have : (0:ℝ) < 1 - P.δ := by linarith
    positivity
  rw [Model.Qxi_eq_sum, Fintype.sum_unique, xie_eq_one]
  simp only [r, sos_r, sos_γ, pow_zero, one_mul, ext_zero_zero, Fin.isValue]
  rw [if_neg (by decide), zero_add]
  show (sos P).Vxi π 1 water = _
  rw [(sos P).Vxi_eq (nt_water P), Fin.sum_univ_two, Qxi_water_0, Qxi_water_1]
  simp only [Model.xia, hx, if_false, mul_zero, add_zero]
  rw [xiA_water_swim, xi_water]
  ring

theorem Vpi_island (hπ : (sos P).IsPolicy π) :
    (sos P).Vpi π 0 island = (1 - π 0 island 1) * P.c + π 0 island 1 * (π 1 water 0 * P.b) := by
  rw [(sos P).Vpi_eq (nt_island P), Fin.sum_univ_two, Qpi_island_0, Qpi_island_1, (sos P).Vpi_eq (nt_water P),
    Fin.sum_univ_two, Qpi_water_0, Qpi_water_1, hπ.fin_two_zero (nt_island P)]
  ring

end Values

/-! ### The tight trap: `b = 1`, `c = 1 - δ`, `s = 1`, `j = 0` -/

/-- The trapped policy: `stay` at the island, `swim` in the water. -/
noncomputable def trap : Policy (Fin 2) Unit := fun _ _ a => if a = 0 then 1 else 0

theorem trap_isPolicy : (sos P).IsPolicy trap := by
  intro n h _
  refine ⟨fun a => ?_, ?_⟩
  · unfold trap; split_ifs <;> norm_num
  · simp [trap, Fin.sum_univ_two]

/-- The tight-trap parameters `b = 1`, `c = 1 - δ`, `s = 1`. -/
noncomputable def tightParams (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) : Params :=
  ⟨1, 1 - δ, δ, 1, by linarith, by linarith, le_rfl, hδ, hδ1, zero_le_one, le_rfl⟩

/-- **Tightness of Theorem B (N+, every `δ ∈ (0,1)`)**: in sink-or-swim with `b = 1`, `c = 1 - δ`, `s = 1`, the
trap `j = 0` is a plain fixed point, satisfies `(TB_island)` with **equality**, has `0 < w_island = 1 - δ < 1`
and a residual of positive mass (`δ`), and `gap / O_island = 1 - δ`. Hence `sup gap/O_h ≥ 1 - δ` for every `δ`,
so the constant `1` in Theorem B cannot be improved (the general-`δ` family).
Source: [[sequential-self-game]] §3 (Remarks, "Tightness")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem tight_trap (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (sos (tightParams δ hδ hδ1)).IsPlainFP trap ∧
    (sos (tightParams δ hδ hδ1)).wS trap 0 island * (sos (tightParams δ hδ hδ1)).Vstar 0 island =
      (sos (tightParams δ hδ hδ1)).Mx trap 0 island ∧
    (sos (tightParams δ hδ hδ1)).wS trap 0 island = 1 - δ ∧
    (sos (tightParams δ hδ hδ1)).gap trap 0 island / (sos (tightParams δ hδ hδ1)).odds trap 0 island = 1 - δ := by
  set P := tightParams δ hδ hδ1 with hP
  have hπ : (sos P).IsPolicy trap := trap_isPolicy P
  have hQ1 : (sos P).Qxi trap 0 island 1 = 0 := by
    rw [Qxi_island_1 P trap hπ]
    simp [trap, P, tightParams]
  have hMx : (sos P).Mx trap 0 island = 1 - δ := by
    rw [(sos P).Mx_fin_two, Qxi_island_0, hQ1]
    exact max_eq_left (by simp [P, tightParams]; linarith)
  have hw : (sos P).wS trap 0 island = 1 - δ := wS_island P trap
  have hV : (sos P).Vstar 0 island = 1 := Vstar_island P
  refine ⟨⟨hπ, ?_⟩, ?_, hw, ?_⟩
  · intro n h hnt
    match n with
    | 0 =>
      rw [eq_island h]
      refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun ha => ?_⟩
      · rw [hMx, Qxi_island_0]; rfl
      · simp [trap] at ha
    | 1 =>
      rw [eq_water_of_nonterminal P h hnt]
      refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun ha => ?_⟩
      · rw [Mx_water, Qxi_water_0]
      · simp [trap] at ha
    | n + 2 => exact absurd hnt (not_nt_ge_two P (n + 2) (by omega) h)
  · rw [hMx, hw, hV, mul_one]
  · have hVpi : (sos P).Vpi trap 0 island = 1 - δ := by
      rw [Vpi_island P trap hπ]
      simp [trap, P, tightParams]
    have hδ' : (1:ℝ) - (1 - δ) ≠ 0 := by linarith
    unfold Model.gap Model.odds
    rw [hVpi, hV, hw, div_div_eq_mul_div, mul_div_right_comm, div_self hδ', one_mul]

/-! ### A genuinely mixed trust-bound fixed point: `b = 1`, `c = 1/2`, `δ = 1/2`, `s = 3/4`, `j = 1/2` -/

/-- The mixed policy: `jump` with probability `1/2` at the island, `swim` in the water. -/
noncomputable def mixed : Policy (Fin 2) Unit := fun n _ a => if n = 0 then 1 / 2 else (if a = 0 then 1 else 0)

/-- The mixed-witness parameters `b = 1`, `c = 1/2`, `δ = 1/2`, `s = 3/4`. -/
noncomputable def mixedParams : Params :=
  ⟨1, 1 / 2, 1 / 2, 3 / 4, by norm_num, by norm_num, le_rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The note's mixed trust-bound fixed point (N−)**: `b = 1`, `c = 1/2`, `δ = 1/2`, `s = 3/4`: the policy
`j = 1/2` (swim in the water) is a plain fixed point with both island actions in the argmax, `(TB_island)` holds,
`w_island = 1/2`, `O_island = 1`, and `gap = 1/4 ≤ O_island`. It inhabits Theorem B's full hypothesis package
and is genuinely mixed, but `O_island = 1` there, so the inequality `gap ≤ O_h` is implied by `gap ≤ 1` and the
bound is not exercised (round-1 audit); graded N− for the bound, kept because it is the note's own point. The
informative mixed witness is `mixed_witness_informative` below.
Source: [[sequential-self-game]] §2 ("Where the mixed point sits")
Kind: N-
Fidelity: exact
Hyps: (a) -/
theorem mixed_witness :
    (sos mixedParams).IsPlainFP mixed ∧ (sos mixedParams).TB mixed 0 island ∧
      (sos mixedParams).wS mixed 0 island = 1 / 2 ∧ (sos mixedParams).odds mixed 0 island = 1 ∧
      (sos mixedParams).gap mixed 0 island = 1 / 4 ∧ (sos mixedParams).Qxi mixed 0 island 1 = 1 / 2 := by
  have hπ : (sos mixedParams).IsPolicy mixed := by
    intro n h _
    refine ⟨fun a => ?_, ?_⟩
    · unfold mixed; split_ifs <;> norm_num
    · unfold mixed; split_ifs <;> simp [Fin.sum_univ_two]
  have hQ1 : (sos mixedParams).Qxi mixed 0 island 1 = 1 / 2 := by
    rw [Qxi_island_1 mixedParams mixed hπ]
    norm_num [mixed, mixedParams]
  have hQ0 : (sos mixedParams).Qxi mixed 0 island 0 = 1 / 2 := Qxi_island_0 mixedParams mixed
  have hMx : (sos mixedParams).Mx mixed 0 island = 1 / 2 := by
    rw [(sos mixedParams).Mx_fin_two, hQ0, hQ1, max_self]
  have hw : (sos mixedParams).wS mixed 0 island = 1 / 2 := by
    rw [wS_island mixedParams mixed]; norm_num [mixedParams]
  have hV : (sos mixedParams).Vstar 0 island = 1 := Vstar_island mixedParams
  refine ⟨⟨hπ, ?_⟩, ?_, hw, ?_, ?_, hQ1⟩
  · intro n h hnt
    match n with
    | 0 =>
      rw [eq_island h]
      refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun _ => ?_⟩
      · rw [hMx, hQ0]
      · rw [hMx, hQ1]
    | 1 =>
      rw [eq_water_of_nonterminal mixedParams h hnt]
      refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun ha => ?_⟩
      · rw [Mx_water, Qxi_water_0]
      · simp [mixed] at ha
    | n + 2 => exact absurd hnt (not_nt_ge_two mixedParams (n + 2) (by omega) h)
  · unfold Model.TB
    rw [hMx, hw, hV]; norm_num
  · unfold Model.odds
    rw [hw]; norm_num
  · unfold Model.gap
    rw [hV, Vpi_island mixedParams mixed hπ]
    norm_num [mixed, mixedParams]

/-! ### A mixed trust-bound fixed point at which Theorem B's bound is informative: `b = 1`, `c = 4/5`, `δ = 1/4`, `s = 3/4`, `j = 11/12` -/

/-- The parameters `b = 1`, `c = 4/5`, `δ = 1/4`, `s = 3/4` (round-1 adversarial audit's probe). -/
noncomputable def mixedParams2 : Params :=
  ⟨1, 4 / 5, 1 / 4, 3 / 4, by norm_num, by norm_num, le_rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `jump` with probability `11/12` at the island, `swim` in the water. -/
noncomputable def mixed2 : Policy (Fin 2) Unit :=
  fun n _ a => if n = 0 then (if a = 0 then 1 / 12 else 11 / 12) else (if a = 0 then 1 else 0)

/-- **A genuinely mixed trust-bound fixed point with an informative bound (N+)**: `b = 1`, `c = 4/5`, `δ = 1/4`,
`s = 3/4`, `j = 11/12` (swim in the water) is a plain fixed point with both island actions in the argmax
(`Q_ξ = 4/5` each), `(TB_island)` holds **strictly** (`3/4 < 4/5`), `0 < w_island = 3/4 < 1`, `O_island = 1/3 < 1`
and `gap = 1/60`: Theorem B's inequality is exercised, not implied by `gap ≤ 1`. Supplied by the round-1
adversarial audit; replaces `mixed_witness` as Theorem B's mixed N+ witness.
Source: [[sequential-self-game]] §2 (the mixed point); round-1 audit
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem mixed_witness_informative :
    (sos mixedParams2).IsPlainFP mixed2 ∧ (sos mixedParams2).TB mixed2 0 island ∧
      (sos mixedParams2).wS mixed2 0 island = 3 / 4 ∧ (sos mixedParams2).odds mixed2 0 island = 1 / 3 ∧
      (sos mixedParams2).gap mixed2 0 island = 1 / 60 ∧ (sos mixedParams2).odds mixed2 0 island < 1 ∧
      (sos mixedParams2).Qxi mixed2 0 island 1 = 4 / 5 ∧
      (sos mixedParams2).wS mixed2 0 island * (sos mixedParams2).Vstar 0 island <
        (sos mixedParams2).Mx mixed2 0 island := by
  have hπ : (sos mixedParams2).IsPolicy mixed2 := by
    intro n h _
    refine ⟨fun a => ?_, ?_⟩
    · unfold mixed2; split_ifs <;> norm_num
    · unfold mixed2; split_ifs <;> simp [Fin.sum_univ_two] <;> norm_num
  have hQ1 : (sos mixedParams2).Qxi mixed2 0 island 1 = 4 / 5 := by
    rw [Qxi_island_1 mixedParams2 mixed2 hπ]
    norm_num [mixed2, mixedParams2]
  have hQ0 : (sos mixedParams2).Qxi mixed2 0 island 0 = 4 / 5 := Qxi_island_0 mixedParams2 mixed2
  have hMx : (sos mixedParams2).Mx mixed2 0 island = 4 / 5 := by
    rw [(sos mixedParams2).Mx_fin_two, hQ0, hQ1, max_self]
  have hw : (sos mixedParams2).wS mixed2 0 island = 3 / 4 := by
    rw [wS_island mixedParams2 mixed2]; norm_num [mixedParams2]
  have hV : (sos mixedParams2).Vstar 0 island = 1 := Vstar_island mixedParams2
  have hodds : (sos mixedParams2).odds mixed2 0 island = 1 / 3 := by
    unfold Model.odds
    rw [hw]; norm_num
  refine ⟨⟨hπ, ?_⟩, ?_, hw, hodds, ?_, by rw [hodds]; norm_num, hQ1, ?_⟩
  · intro n h hnt
    match n with
    | 0 =>
      rw [eq_island h]
      refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun _ => ?_⟩
      · rw [hMx, hQ0]
      · rw [hMx, hQ1]
    | 1 =>
      rw [eq_water_of_nonterminal mixedParams2 h hnt]
      refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun ha => ?_⟩
      · rw [Mx_water, Qxi_water_0]
      · simp [mixed2] at ha
    | n + 2 => exact absurd hnt (not_nt_ge_two mixedParams2 (n + 2) (by omega) h)
  · unfold Model.TB
    rw [hMx, hw, hV]; norm_num
  · unfold Model.gap
    rw [hV, Vpi_island mixedParams2 mixed2 hπ]
    norm_num [mixed2, mixedParams2]
  · rw [hMx, hw, hV]; norm_num

/-- **The tight trap attains Theorem B's first inequality**, with `p̄_island = 0` (the residual never plays
`stay`): `gap = (1 - w) V^* = δ`, while the second inequality is strict (`δ < O_h = δ/(1-δ)`). Each step of
Theorem B's two-step bound is attained separately — the first here (`p̄ = 0`), the second exactly when `p̄_h = 1`
(`theoremB_second_eq_iff`; e.g. `mixed_witness_second_step_tight`) — and never both (`theoremB_strict`,
`Strict.lean`). (The repair-round-1 sentence "tight in its first step and never in its second" was false; round-2
fidelity audit B1.)
Source: [[sequential-self-game]] §3 (tightness); round-1 audit
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem tight_trap_pbar (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (sos (tightParams δ hδ hδ1)).pbar trap 0 island = 0 ∧
    (sos (tightParams δ hδ hδ1)).gap trap 0 island =
      (1 - (sos (tightParams δ hδ hδ1)).wS trap 0 island) * (sos (tightParams δ hδ hδ1)).Vstar 0 island ∧
    (sos (tightParams δ hδ hδ1)).gap trap 0 island < (sos (tightParams δ hδ hδ1)).odds trap 0 island := by
  set P := tightParams δ hδ hδ1 with hP
  have hπ : (sos P).IsPolicy trap := trap_isPolicy P
  have hxinsA0 : (sos P).xinsA 0 island 0 = 0 := by
    simp [Model.xinsA, νa]
  have hpbar : (sos P).pbar trap 0 island = 0 := by
    unfold Model.pbar
    apply Finset.sum_eq_zero
    intro a ha
    simp only [supp, Finset.mem_filter] at ha
    have ha0 : a = 0 := by
      rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with h | h
      · exact h
      · exfalso; simp [trap, h] at ha
    rw [ha0]
    unfold Model.pibar
    rw [hxinsA0, zero_div]
  have hw : (sos P).wS trap 0 island = 1 - δ := by
    rw [wS_island P trap]; simp [P, tightParams]
  have hV : (sos P).Vstar 0 island = 1 := Vstar_island P
  have hgap : (sos P).gap trap 0 island = δ := by
    unfold Model.gap
    rw [hV, Vpi_island P trap hπ]
    simp [trap, P, tightParams]
  refine ⟨hpbar, ?_, ?_⟩
  · rw [hgap, hw, hV]; ring
  · unfold Model.odds
    rw [hgap, hw]
    rw [lt_div_iff₀ (by linarith)]
    nlinarith

/-- At the informative mixed witness the non-self mixture's mass on the agent's support is `1` (`p̄ = 1`): both
sink-or-swim hypotheses jump at the island and `mixed2` supports both island actions. (Round-2 fidelity audit's
probe `probe_pbar_mixed2`, moved into the library.)
Source: round-2 fidelity audit B1; [[sequential-self-game]] §3
Kind: P
Fidelity: n/a
Hyps: (a) -/
theorem mixed2_pbar : (sos mixedParams2).pbar mixed2 0 island = 1 := by
  unfold Model.pbar
  have hsupp : supp mixed2 0 island = univ := by
    ext a
    simp only [supp, mem_filter, mem_univ, true_and]
    fin_cases a <;> simp [mixed2]
  rw [hsupp]
  exact (sos mixedParams2).pibar_sum_eq_one (by rw [xins_island]; norm_num [mixedParams2])

/-- **Theorem B's second step is attained** at the informative mixed witness (`p̄ = 1`, so
`(1-w)[(1-p̄)V^* + p̄/w] = (1/4)(4/3) = 1/3 = O_h`), while the first step is strict there (`gap = 1/60 < 1/3`).
With `tight_trap_pbar` (first step attained, second strict) and `theoremB_strict` (never both): each step of the
two-step bound is attained separately, never both. (Round-2 fidelity audit's probe
`probe_second_step_tight_mixed2`, moved into the library.)
Source: round-2 fidelity audit B1; [[uea-cole-shadow-mandate]] target 10
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem mixed_witness_second_step_tight :
    (1 - (sos mixedParams2).wS mixed2 0 island) *
        ((1 - (sos mixedParams2).pbar mixed2 0 island) * (sos mixedParams2).Vstar 0 island +
          (sos mixedParams2).pbar mixed2 0 island / (sos mixedParams2).wS mixed2 0 island) =
      (sos mixedParams2).odds mixed2 0 island ∧
    (sos mixedParams2).gap mixed2 0 island < (sos mixedParams2).odds mixed2 0 island := by
  obtain ⟨_, _, hw, hodds, hgap, _, _, _⟩ := mixed_witness_informative
  refine ⟨?_, by rw [hgap, hodds]; norm_num⟩
  exact ((sos mixedParams2).theoremB_second_eq_iff (π := mixed2) (by rw [hw]; norm_num)
    (by rw [hw]; norm_num)).2 mixed2_pbar

/-- The supremum `1` of `gap/O_h` is approached (`1 - δ` for every `δ`) by the tight trap, at which `p̄ = 0`: the
approach is not "through `p̄_h → 1`". Composition of `tight_trap` and `tight_trap_pbar`. (Round-2 fidelity audit's
probe `probe_sup_approached_with_pbar_zero`, moved into the library.)
Source: round-2 fidelity audit B1; [[sequential-self-game]] §3 (tightness)
Kind: C
Fidelity: n/a
Hyps: (a) -/
theorem sup_approached_with_pbar_zero (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (sos (tightParams δ hδ hδ1)).pbar trap 0 island = 0 ∧
    (sos (tightParams δ hδ hδ1)).gap trap 0 island / (sos (tightParams δ hδ hδ1)).odds trap 0 island = 1 - δ :=
  ⟨(tight_trap_pbar δ hδ hδ1).1, (tight_trap δ hδ hδ1).2.2.2⟩

end SinkOrSwim

end Cleanroom.Uea.UeaColeShadow
