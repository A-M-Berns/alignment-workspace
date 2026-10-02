import Cleanroom.Uea.UeaColeShadow.SinkOrSwim
import Cleanroom.Uea.UeaColeShadow.Floored

/-!
# Theorem A: the sink-or-swim characterization; the printed 2025 Theorem 1 refuted

The full fixed-point structure of the sink-or-swim family `SinkOrSwim.sos P` of `uea-cole-shadow`
([[sequential-self-game]] §2, Theorem A), as two-sided iffs for **every** `P : Params`: every plain
(and every floored) fixed point swims (A0); the trap is a plain fixed point iff `b(1-s) ≤ c` — no `δ`
in the condition (A1); the good point iff `b(1-δs) ≥ c` (A2); a mixed point `0 < j < 1` iff
`j = j* := δ(c - b(1-s)) / ((1-δ)(b-c))`, and `0 < j* < 1` iff both pure conditions hold strictly (A3);
the trust bound at each (A4); and the negative result (A5): for every `b, c`, every `δ < 1 - c/b` and
every `s ≥ 1 - c/b`, the trap is a plain fixed point with `w_island = 1 - δ` (the premise of the
revised Theorem 1 at the root) and `gap = b - c`, which does not shrink with `δ`. Target 2 reads the
printed 2025 Theorem 1 ([[lesswrong-post--live-2026-08-22]] line 236) in the finite shadow and refutes
it from (A5) at `b = 1, c = 1/2, s = 1`.

Scope: finite shadow of rOSI ([[sequential-self-game]] §7). Namespace `Cleanroom.Uea.UeaSinkSwim.TheoremA`
(faf-cleanroom run, `uea-sink-swim`, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Finset
open Cleanroom.Uea.UeaColeShadow
open Cleanroom.Uea.UeaColeShadow.SinkOrSwim

namespace TheoremA

variable (P : Params)

/-! ### The closed form at `σ = 1` and the mixed point -/

/-- `Q_ξ(island, jump)` at `σ = 1` as a function of `j = π(jump|island)`:
`QJ j := b((1-δ) j + δ(1-s)) / ((1-δ) j + δ)`.
Source: [[sequential-self-game]] §2 (Theorem A, the displayed formula)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def QJ (j : ℝ) : ℝ := P.b * ((1 - P.δ) * j + P.δ * (1 - P.s)) / ((1 - P.δ) * j + P.δ)

/-- The mixed fixed point `j* := δ(c - b(1-s)) / ((1-δ)(b-c))`.
Source: [[sequential-self-game]] §2 (Theorem A, mixed case)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def jstar : ℝ := P.δ * (P.c - P.b * (1 - P.s)) / ((1 - P.δ) * (P.b - P.c))

theorem one_sub_δ_pos : 0 < 1 - P.δ := by linarith [P.hδ1]
theorem b_pos : 0 < P.b := lt_trans P.hc P.hcb
theorem b_sub_c_pos : 0 < P.b - P.c := by linarith [P.hcb]

theorem QJ_zero : QJ P 0 = P.b * (1 - P.s) := by
  have hδ := P.hδ.ne'
  unfold QJ
  rw [mul_zero, zero_add, zero_add]
  field_simp

theorem QJ_one : QJ P 1 = P.b * (1 - P.δ * P.s) := by
  unfold QJ
  have h : (1 - P.δ) * 1 + P.δ = 1 := by ring
  rw [h, div_one]
  ring

/-- `QJ j = c` iff `j = j*` (the condition is affine in `j` after clearing the positive denominator).
Source: [[sequential-self-game]] §2 (proof of Theorem A: "affine in `j`")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem QJ_eq_c_iff (j : ℝ) (hj : 0 ≤ j) : QJ P j = P.c ↔ j = jstar P := by
  have hδ := P.hδ
  have h1δ := one_sub_δ_pos P
  have hbc := b_sub_c_pos P
  have hden : (1 - P.δ) * j + P.δ ≠ 0 := by
    have := mul_nonneg h1δ.le hj
    linarith
  have hden2 : (1 - P.δ) * (P.b - P.c) ≠ 0 := (mul_pos h1δ hbc).ne'
  unfold QJ jstar
  rw [div_eq_iff hden, eq_div_iff hden2]
  constructor <;> intro h <;> linear_combination h

/-- `0 < j* < 1` iff both pure conditions hold **strictly**: `b(1-s) < c` and `c < b(1-δs)`.
Source: [[sequential-self-game]] §2 (the note's own correction of the founding sketch's "when both pure fixed points exist")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem jstar_mem_Ioo_iff : (0 < jstar P ∧ jstar P < 1) ↔ (P.b * (1 - P.s) < P.c ∧ P.c < P.b * (1 - P.δ * P.s)) := by
  have hδ := P.hδ
  have h1δ := one_sub_δ_pos P
  have hbc := b_sub_c_pos P
  have hD : 0 < (1 - P.δ) * (P.b - P.c) := mul_pos h1δ hbc
  unfold jstar
  rw [div_lt_one hD]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : 0 < P.δ * (P.c - P.b * (1 - P.s)) := by
      by_contra hneg
      have hneg' : P.δ * (P.c - P.b * (1 - P.s)) ≤ 0 := not_lt.1 hneg
      have := div_nonpos_of_nonpos_of_nonneg hneg' hD.le
      linarith
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨div_pos (mul_pos hδ (by linarith)) hD, ?_⟩
    nlinarith

/-! ### (A0): every fixed point swims -/

theorem Qstar_water_0 : (sos P).Qstar 1 water 0 = P.b := by
  rw [(sos P).Qstar_eq_of_children_terminal water 0 (fun e => not_nt_two P _)]
  simp [xie_eq_one, r, water]

theorem Qstar_water_1 : (sos P).Qstar 1 water 1 = 0 := by
  rw [(sos P).Qstar_eq_of_children_terminal water 1 (fun e => not_nt_two P _)]
  simp [xie_eq_one, r, water]

/-- `π⋆(water) = swim` (the optimal action in the water is unique). -/
theorem piStar_water : (sos P).piStar 1 water = 0 := by
  apply (sos P).piStar_eq_of_unique (nt_water P)
  refine Fin.forall_fin_two.2 ⟨fun _ => rfl, fun ha => ?_⟩
  rw [Qstar_water_1, Vstar_water] at ha
  linarith [P.hc, P.hcb]

/-- **(A0, plain)**: every plain fixed point swims: `σ = π(swim|water) = 1`.
Source: [[sequential-self-game]] §2 (Theorem A, "At every fixed point the agent swims")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem swim_of_isPlainFP {π : Policy (Fin 2) Unit} (hfp : (sos P).IsPlainFP π) : π 1 water 0 = 1 := by
  have hπ := hfp.1
  have h1 : π 1 water 1 = 0 := by
    by_contra hne
    have hpos : 0 < π 1 water 1 := lt_of_le_of_ne (hπ.nonneg (nt_water P) 1) (Ne.symm hne)
    have := hfp.2 1 water (nt_water P) 1 hpos
    rw [Qxi_water_1, Mx_water] at this
    linarith [P.hc, P.hcb]
  rw [hπ.fin_two_zero (nt_water P), h1, sub_zero]

/-- **(A0, floored)**: every floored fixed point swims (`resid(water) = b(1 - w_water) ≥ 0`, and `π⋆(water) = swim`).
Source: [[sequential-self-game]] §2 (Theorem A) with the floored agent of §1
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem swim_of_isFlooredFP {π : Policy (Fin 2) Unit} (hfp : (sos P).IsFlooredFP π) : π 1 water 0 = 1 := by
  have hπ := hfp.1
  have hres : 0 ≤ (sos P).resid π 1 water := by
    unfold Model.resid
    rw [Mx_water, Vstar_water]
    have hw := (sos P).wS_le_one hπ (nt_water P)
    have := b_pos P
    nlinarith
  have h1 : π 1 water 1 = 0 := by
    by_contra hne
    have hpos : 0 < π 1 water 1 := lt_of_le_of_ne (hπ.nonneg (nt_water P) 1) (Ne.symm hne)
    rcases hfp.supp_of_nonneg (nt_water P) hres hpos with h | h
    · rw [Qxi_water_1, Mx_water] at h
      linarith [P.hc, P.hcb]
    · rw [piStar_water] at h
      exact absurd h (by decide)
  rw [hπ.fin_two_zero (nt_water P), h1, sub_zero]

/-! ### The plain fixed points, raw and cased -/

theorem Qxi_island_1_eq {π : Policy (Fin 2) Unit} (hπ : (sos P).IsPolicy π) (hσ : π 1 water 0 = 1) :
    (sos P).Qxi π 0 island 1 = QJ P (π 0 island 1) := by
  rw [Qxi_island_1 P π hπ, hσ, mul_one]
  rfl

/-- **Theorem A, raw form**: for any policy of `sos P`, `π` is a plain fixed point iff it swims and, at the
island, `j < 1 → QJ j ≤ c` (stay is supported, so it must be a best response) and `0 < j → c ≤ QJ j`.
Source: [[sequential-self-game]] §2 (Theorem A)
Kind: P
Fidelity: exact (two-sided, every `P`)
Hyps: (a) -/
theorem isPlainFP_iff {π : Policy (Fin 2) Unit} (hπ : (sos P).IsPolicy π) :
    (sos P).IsPlainFP π ↔ π 1 water 0 = 1 ∧
      (π 0 island 1 < 1 → QJ P (π 0 island 1) ≤ P.c) ∧
      (0 < π 0 island 1 → P.c ≤ QJ P (π 0 island 1)) := by
  constructor
  · intro hfp
    have hσ := swim_of_isPlainFP P hfp
    have hQ := Qxi_island_1_eq P hπ hσ
    refine ⟨hσ, fun hj => ?_, fun hj => ?_⟩
    · have h0 : 0 < π 0 island 0 := by rw [hπ.fin_two_zero (nt_island P)]; linarith
      have := hfp.2 0 island (nt_island P) 0 h0
      rw [Qxi_island_0, Model.Mx_fin_two, Qxi_island_0, hQ] at this
      exact max_eq_left_iff.1 this.symm
    · have := hfp.2 0 island (nt_island P) 1 hj
      rw [Model.Mx_fin_two, Qxi_island_0, hQ] at this
      exact max_eq_right_iff.1 this.symm
  · rintro ⟨hσ, h1, h2⟩
    have hQ := Qxi_island_1_eq P hπ hσ
    refine ⟨hπ, fun n h hnt => ?_⟩
    match n with
    | 0 =>
      rw [eq_island h]
      refine Fin.forall_fin_two.2 ⟨fun h0 => ?_, fun hj => ?_⟩
      · rw [hπ.fin_two_zero (nt_island P)] at h0
        rw [Model.Mx_fin_two, Qxi_island_0, hQ, max_eq_left (h1 (by linarith))]
      · rw [Model.Mx_fin_two, Qxi_island_0, hQ, max_eq_right (h2 hj)]
    | 1 =>
      rw [eq_water_of_nonterminal P h hnt]
      refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun ha => ?_⟩
      · rw [Mx_water, Qxi_water_0]
      · have h0 := hπ.fin_two_zero (nt_water P)
        rw [hσ] at h0
        linarith
    | n + 2 => exact absurd hnt (not_nt_ge_two P (n + 2) (by omega) h)

/-- **Theorem A, cased**: every plain fixed point swims and is the trap (`j = 0`, with `b(1-s) ≤ c`), the good
point (`j = 1`, with `c ≤ b(1-δs)`), or the mixed point (`0 < j < 1` and `j = j*`).
Source: [[sequential-self-game]] §2 (Theorem A, the three cases)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem isPlainFP_cases {π : Policy (Fin 2) Unit} (hfp : (sos P).IsPlainFP π) :
    π 1 water 0 = 1 ∧
      ((π 0 island 1 = 0 ∧ P.b * (1 - P.s) ≤ P.c) ∨
       (π 0 island 1 = 1 ∧ P.c ≤ P.b * (1 - P.δ * P.s)) ∨
       (0 < π 0 island 1 ∧ π 0 island 1 < 1 ∧ π 0 island 1 = jstar P)) := by
  have hπ := hfp.1
  obtain ⟨hσ, h1, h2⟩ := (isPlainFP_iff P hπ).1 hfp
  refine ⟨hσ, ?_⟩
  have hj0 := hπ.nonneg (nt_island P) 1
  have hj1 := hπ.le_one (nt_island P) 1
  rcases eq_or_lt_of_le hj0 with hz | hpos
  · left
    refine ⟨hz.symm, ?_⟩
    have := h1 (by rw [← hz]; norm_num)
    rwa [← hz, QJ_zero] at this
  rcases eq_or_lt_of_le hj1 with ho | hlt
  · right; left
    refine ⟨ho, ?_⟩
    have := h2 (by rw [ho]; norm_num)
    rwa [ho, QJ_one] at this
  · right; right
    refine ⟨hpos, hlt, ?_⟩
    rw [← QJ_eq_c_iff P _ hj0]
    exact le_antisymm (h1 hlt) (h2 hpos)

/-! ### The three named policies and their iffs -/

/-- The good policy: `jump` at the island, `swim` in the water. -/
noncomputable def good : Policy (Fin 2) Unit := fun n _ a =>
  if n = 0 then (if a = 1 then 1 else 0) else (if a = 0 then 1 else 0)

/-- The mixed policy with jump-probability `j` at the island, `swim` in the water. -/
noncomputable def mixedPol (j : ℝ) : Policy (Fin 2) Unit := fun n _ a =>
  if n = 0 then (if a = 1 then j else 1 - j) else (if a = 0 then 1 else 0)

theorem good_isPolicy : (sos P).IsPolicy good := by
  intro n h _
  refine ⟨fun a => ?_, ?_⟩
  · by_cases hn : n = 0 <;> fin_cases a <;> simp [good, hn]
  · by_cases hn : n = 0 <;> simp [good, hn]

theorem mixedPol_isPolicy {j : ℝ} (hj0 : 0 ≤ j) (hj1 : j ≤ 1) : (sos P).IsPolicy (mixedPol j) := by
  intro n h _
  refine ⟨fun a => ?_, ?_⟩
  · by_cases hn : n = 0 <;> fin_cases a <;> simp [mixedPol, hn] <;> linarith
  · by_cases hn : n = 0 <;> simp [mixedPol, hn, Fin.sum_univ_two]

theorem trap_j : trap 0 island 1 = 0 := by simp [trap]
theorem trap_σ : trap 1 water 0 = 1 := by simp [trap]
theorem good_j : good 0 island 1 = 1 := by simp [good]
theorem good_σ : good 1 water 0 = 1 := by simp [good]
theorem mixedPol_j (j : ℝ) : mixedPol j 0 island 1 = j := by simp [mixedPol]
theorem mixedPol_σ (j : ℝ) : mixedPol j 1 water 0 = 1 := by simp [mixedPol]

theorem trap_isPure : (sos P).IsPure trap := fun _ _ _ => ⟨0, by simp [trap]⟩
theorem good_isPure : (sos P).IsPure good := fun n _ _ => by
  by_cases hn : n = 0
  · exact ⟨1, by simp [good, hn]⟩
  · exact ⟨0, by simp [good, hn]⟩

/-- **(A1) trap**: the pure trap (`stay`, then `swim`) is a plain fixed point **iff** `b(1-s) ≤ c` — no `δ`
in the condition.
Source: [[sequential-self-game]] §2 (Theorem A, "trapped ... independent of `δ`")
Kind: P
Fidelity: exact (both directions)
Hyps: (a) -/
theorem trap_isPlainFP_iff : (sos P).IsPlainFP trap ↔ P.b * (1 - P.s) ≤ P.c := by
  rw [isPlainFP_iff P (trap_isPolicy P), trap_j, trap_σ, QJ_zero]
  simp

/-- **(A2) good**: the good point (`jump`, then `swim`) is a plain fixed point **iff** `b(1-δs) ≥ c`.
Source: [[sequential-self-game]] §2 (Theorem A, "good")
Kind: P
Fidelity: exact (both directions)
Hyps: (a) -/
theorem good_isPlainFP_iff : (sos P).IsPlainFP good ↔ P.c ≤ P.b * (1 - P.δ * P.s) := by
  rw [isPlainFP_iff P (good_isPolicy P), good_j, good_σ, QJ_one]
  simp

/-- **(A3) mixed**: for `0 < j < 1`, the mixed policy is a plain fixed point **iff** `Q_ξ(island, jump) = c`
**iff** `j = j*`; hence the mixed fixed point is unique.
Source: [[sequential-self-game]] §2 (Theorem A, "mixed")
Kind: P
Fidelity: exact (both directions)
Hyps: (a) -/
theorem mixedPol_isPlainFP_iff {j : ℝ} (hj0 : 0 < j) (hj1 : j < 1) :
    (sos P).IsPlainFP (mixedPol j) ↔ QJ P j = P.c := by
  rw [isPlainFP_iff P (mixedPol_isPolicy P hj0.le hj1.le), mixedPol_j, mixedPol_σ]
  simp only [hj0, hj1, true_implies, true_and]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

theorem mixedPol_isPlainFP_iff_jstar {j : ℝ} (hj0 : 0 < j) (hj1 : j < 1) :
    (sos P).IsPlainFP (mixedPol j) ↔ j = jstar P := by
  rw [mixedPol_isPlainFP_iff P hj0 hj1, QJ_eq_c_iff P j hj0.le]

/-! ### (A4): the trust bound at each fixed point -/

theorem Mx_trap (h : P.b * (1 - P.s) ≤ P.c) : (sos P).Mx trap 0 island = P.c := by
  rw [Model.Mx_fin_two, Qxi_island_0, Qxi_island_1_eq P (trap_isPolicy P) (trap_σ), trap_j, QJ_zero]
  exact max_eq_left h

theorem Mx_good (h : P.c ≤ P.b * (1 - P.δ * P.s)) : (sos P).Mx good 0 island = P.b * (1 - P.δ * P.s) := by
  rw [Model.Mx_fin_two, Qxi_island_0, Qxi_island_1_eq P (good_isPolicy P) (good_σ), good_j, QJ_one]
  exact max_eq_right h

theorem Mx_mixed {j : ℝ} (hj0 : 0 < j) (hj1 : j < 1) (hfp : (sos P).IsPlainFP (mixedPol j)) :
    (sos P).Mx (mixedPol j) 0 island = P.c := by
  have hQ := (mixedPol_isPlainFP_iff P hj0 hj1).1 hfp
  rw [Model.Mx_fin_two, Qxi_island_0, Qxi_island_1_eq P (mixedPol_isPolicy P hj0.le hj1.le) (mixedPol_σ j),
    mixedPol_j, hQ, max_self]

/-- `(1-δ) b ≤ c ↔ 1 - c/b ≤ δ` (the two spellings of the trust-bound condition). -/
theorem tb_cond_iff : (1 - P.δ) * P.b ≤ P.c ↔ 1 - P.c / P.b ≤ P.δ := by
  have hb := b_pos P
  constructor
  · intro h
    have := (le_div_iff₀ hb).2 h
    linarith
  · intro h
    have : 1 - P.δ ≤ P.c / P.b := by linarith
    exact (le_div_iff₀ hb).1 this

/-- **(A4, trap)**: at the trap (a fixed point), `M = c` and `TB_island` holds **iff** `(1-δ) b ≤ c`, i.e.
`δ ≥ 1 - c/b`.
Source: [[sequential-self-game]] §2 ("Trust bound")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem TB_trap_iff (h : P.b * (1 - P.s) ≤ P.c) :
    (sos P).TB trap 0 island ↔ (1 - P.δ) * P.b ≤ P.c := by
  unfold Model.TB
  rw [wS_island, Vstar_island, Mx_trap P h]

/-- **(A4, good)**: at the good point (a fixed point), `TB_island` always holds (`M = b(1-δs) ≥ (1-δ) b`).
Source: [[sequential-self-game]] §2 ("Trust bound")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem TB_good (h : P.c ≤ P.b * (1 - P.δ * P.s)) : (sos P).TB good 0 island := by
  unfold Model.TB
  rw [wS_island, Vstar_island, Mx_good P h]
  have hb := b_pos P; have hδ := P.hδ; have hs := P.hs1
  have := mul_nonneg (mul_nonneg hb.le hδ.le) (sub_nonneg.2 hs)
  nlinarith

/-- **(A4, mixed)**: at the mixed fixed point, `M = c` and `TB_island` holds **iff** `c ≥ (1-δ) b`.
Source: [[sequential-self-game]] §2 ("Where the mixed point sits")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem TB_mixed_iff {j : ℝ} (hj0 : 0 < j) (hj1 : j < 1) (hfp : (sos P).IsPlainFP (mixedPol j)) :
    (sos P).TB (mixedPol j) 0 island ↔ (1 - P.δ) * P.b ≤ P.c := by
  unfold Model.TB
  rw [wS_island, Vstar_island, Mx_mixed P hj0 hj1 hfp]

/-- **(A4, coexistence)**: for `δ < 1 - c/b ≤ s` both pure fixed points exist for the same prior, and the
trust bound selects the good one (rejects the trap).
Source: [[sequential-self-game]] §2 ("Trust bound", coexistence regime)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem coexistence (hδ : P.δ < 1 - P.c / P.b) (hs : 1 - P.c / P.b ≤ P.s) :
    (sos P).IsPlainFP trap ∧ (sos P).IsPlainFP good ∧
      ¬ (sos P).TB trap 0 island ∧ (sos P).TB good 0 island := by
  have hb := b_pos P
  have htrap : P.b * (1 - P.s) ≤ P.c := by
    have h1 : 1 - P.s ≤ P.c / P.b := by linarith
    have := (le_div_iff₀ hb).1 h1
    linarith
  have hgood : P.c ≤ P.b * (1 - P.δ * P.s) := by
    have h1 : 1 - P.δ ≤ 1 - P.c / P.b + (1 - P.δ) - (1 - P.c / P.b) := by ring_nf; linarith
    have h2 : P.δ * P.s ≤ P.δ := by nlinarith [P.hδ, P.hs1]
    have h3 : P.c / P.b < 1 - P.δ := by linarith
    have h4 := (div_lt_iff₀ hb).1 h3
    nlinarith
  refine ⟨(trap_isPlainFP_iff P).2 htrap, (good_isPlainFP_iff P).2 hgood, ?_, TB_good P hgood⟩
  rw [TB_trap_iff P htrap, tb_cond_iff]
  exact not_le.2 hδ

/-! ### (A5): the negative result -/

/-- The parameters of the negative result: `0 < c < b ≤ 1`, `0 < δ < 1 - c/b`, `1 - c/b ≤ s ≤ 1`. -/
noncomputable def negParams (b c δ s : ℝ) (hc : 0 < c) (hcb : c < b) (hb : b ≤ 1) (hδ : 0 < δ)
    (hδ' : δ < 1 - c / b) (hs : 1 - c / b ≤ s) (hs1 : s ≤ 1) : Params :=
  ⟨b, c, δ, s, hc, hcb, hb, hδ,
    by
      have hbpos : 0 < b := lt_trans hc hcb
      have : 0 < c / b := div_pos hc hbpos
      linarith,
    by
      have hbpos : 0 < b := lt_trans hc hcb
      have : c / b < 1 := (div_lt_one hbpos).2 hcb
      linarith,
    hs1⟩

/-- **(A5) The negative result** (headline). For every `b, c` with `0 < c < b ≤ 1`, every `δ ∈ (0, 1 - c/b)`
and every `s ∈ [1 - c/b, 1]`: in `sos ⟨b, c, δ, s⟩` the trap is a plain fixed point, `w_island = 1 - δ`,
`V^π(island) = c`, `V^*(island) = b`, and `gap = b - c`. The premise of the revised Theorem 1 holds at
the root (`w = 1 - δ > 1 - δ'` for every `δ' > δ`) — automatically: `w_root = 1 - δ` for every policy of
every model (`T1.wS_root`), so that conjunct is the model's convention, not a property of the trap; the
content is "the trap is a plain fixed point, with `gap = b - c`" — and the conclusion fails by `b - c`, which
does not shrink with `δ`: consistent self-knowledge alone does not give near-optimality; the `∃`-oracle existential
is load-bearing, and its finite shadow is `TB`-selection (A4). Cole's Discord message 42 ("you can still be
totally wrong off policy") is the quote ([[planning-to-write-about-coles-theorem]]).
Source: [[sequential-self-game]] §2 ("The negative result"); [[uea-inventory]] 014
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem negative_result (b c δ s : ℝ) (hc : 0 < c) (hcb : c < b) (hb : b ≤ 1) (hδ : 0 < δ)
    (hδ' : δ < 1 - c / b) (hs : 1 - c / b ≤ s) (hs1 : s ≤ 1) :
    let P := negParams b c δ s hc hcb hb hδ hδ' hs hs1
    (sos P).IsPlainFP trap ∧ (sos P).wS trap 0 island = 1 - δ ∧
      (sos P).Vpi trap 0 island = c ∧ (sos P).Vstar 0 island = b ∧
      (sos P).gap trap 0 island = b - c := by
  intro P
  have hbpos : 0 < b := lt_trans hc hcb
  have htrap : P.b * (1 - P.s) ≤ P.c := by
    show b * (1 - s) ≤ c
    have h1 : 1 - s ≤ c / b := by linarith
    have := (le_div_iff₀ hbpos).1 h1
    linarith
  have hV : (sos P).Vpi trap 0 island = c := by
    rw [Vpi_island P trap (trap_isPolicy P), trap_j]
    show (1 - 0) * c + 0 * (trap 1 water 0 * b) = c
    ring
  refine ⟨(trap_isPlainFP_iff P).2 htrap, wS_island P trap, hV, Vstar_island P, ?_⟩
  unfold Model.gap
  rw [hV, Vstar_island P]
  rfl

/-! ### The N+ witness: `b = 1, c = 1/2, δ = 1/4, s = 3/4` -/

/-- The witness parameters `b = 1, c = 1/2, δ = 1/4, s = 3/4`. -/
noncomputable def witParams : Params :=
  ⟨1, 1 / 2, 1 / 4, 3 / 4, by norm_num, by norm_num, le_rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Witness (N+)**: at `b = 1, c = 1/2, δ = 1/4, s = 3/4` both pure fixed points exist, `j* = 1/6` is the mixed
fixed point, the trust bound rejects the trap and accepts the good point, and the mixed point fails it
(`c = 1/2 < 3/4 = (1-δ) b`).
Source: [[sequential-self-game]] §2; mandate target 1 (witness)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem witness :
    (sos witParams).IsPlainFP trap ∧ (sos witParams).IsPlainFP good ∧
      jstar witParams = 1 / 6 ∧ (sos witParams).IsPlainFP (mixedPol (1 / 6)) ∧
      ¬ (sos witParams).TB trap 0 island ∧ (sos witParams).TB good 0 island ∧
      ¬ (sos witParams).TB (mixedPol (1 / 6)) 0 island := by
  have hj : jstar witParams = 1 / 6 := by
    unfold jstar witParams; norm_num
  have htrap : (sos witParams).IsPlainFP trap := (trap_isPlainFP_iff _).2 (by unfold witParams; norm_num)
  have hgood : (sos witParams).IsPlainFP good := (good_isPlainFP_iff _).2 (by unfold witParams; norm_num)
  have hmix : (sos witParams).IsPlainFP (mixedPol (1 / 6)) :=
    (mixedPol_isPlainFP_iff_jstar _ (by norm_num) (by norm_num)).2 hj.symm
  refine ⟨htrap, hgood, hj, hmix, ?_, TB_good _ (by unfold witParams; norm_num), ?_⟩
  · rw [TB_trap_iff _ (by unfold witParams; norm_num)]
    unfold witParams; norm_num
  · rw [TB_mixed_iff _ (by norm_num) (by norm_num) hmix]
    unfold witParams; norm_num

end TheoremA

/-! ### Target 2: the printed 2025 Theorem 1, refuted as printed -/

namespace Printed2025

open TheoremA

/-- **The printed 2025 Theorem 1, finite-shadow reading** (ATTRIBUTION-UNVETTED). The text
([[lesswrong-post--live-2026-08-22]] line 236): "Let the true environment ψ be deterministic. For any ε > 0,
there exists a δ > 0 such that if ξ ≥ (1−δ)ψ^{π_S}, then π_S is ε-(Bayes-)optimal for environment ψ."
Reading: deterministic percepts (here `E = Unit`, so `ψ`-values and `ξ`-values coincide), the premise
`ξ ≥ (1-δ) ξ_S` holds by construction with the model's own non-self prior `δ`, and "π_S" is any plain
fixed point: `∀ ε > 0, ∃ δ₀ > 0, ∀ M (M.δ < δ₀), ∀ π plain fixed point, gap π root ≤ ε`.
Source: [[lesswrong-post--live-2026-08-22]] line 236; [[uea-inventory]] 021
Kind: D
Fidelity: variant: the finite shadow (the rOSI statement is not formalized); the reading is the mandate's
Hyps: n/a -/
def Reading : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ (A E ι : Type) [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] [Unique E] (M : Model A E ι),
      M.δ < δ₀ → ∀ π, M.IsPlainFP π → ∀ h : Hist A E 0, M.gap π 0 h ≤ ε

/-- **The refuting family**: for every `δ ∈ (0,1)` there is a model with non-self prior `δ` (sink-or-swim at
`b = 1, c = 1/2, s = 1`) and a pure plain fixed point (the trap) with root loss exactly `1/2`.
Source: [[sequential-self-game]] §2 ("The negative result"); [[uea-inventory]] 021
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem refuting_family (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ (M : Model (Fin 2) Unit (Fin 2)) (π : Policy (Fin 2) Unit), M.δ = δ ∧ M.IsPlainFP π ∧ M.IsPure π ∧
      ∀ h : Hist (Fin 2) Unit 0, M.gap π 0 h = 1 / 2 := by
  let P : Params := ⟨1, 1 / 2, δ, 1, by norm_num, by norm_num, le_rfl, hδ, hδ1, zero_le_one, le_rfl⟩
  have hfp : (sos P).IsPlainFP trap := (trap_isPlainFP_iff P).2 (by show (1:ℝ) * (1 - 1) ≤ 1 / 2; norm_num)
  have hV : (sos P).Vpi trap 0 island = 1 / 2 := by
    rw [Vpi_island P trap (trap_isPolicy P), trap_j]
    show (1 - 0) * (1 / 2) + 0 * (trap 1 water 0 * 1) = 1 / 2
    ring
  refine ⟨sos P, trap, rfl, hfp, trap_isPure _, fun h => ?_⟩
  rw [eq_island h]
  unfold Model.gap
  rw [hV, Vstar_island P]
  show (1:ℝ) - 1 / 2 = 1 / 2
  norm_num

/-- **The printed 2025 Theorem 1 is false as printed** (finite-shadow reading): no `δ₀` works for `ε = 1/4`,
because the trap's loss `1/2` is attained at every `δ`. The trap condition being `δ`-free (A1) *is* the
refutation. The theorem was retracted by its author: the July-2025 copy
(`01-primary/lesswrong-post--logsidian-annotated-copy-2025-07.md`, line 591) carries the author's
"[EDIT: This theorem is currently broken. The problem is that, in Lemma 1, the action-values for off-policy
actions can be underestimates …]", and the live post keeps the theorem under the heading "Appendix: Original
Broken Argument" (line 233); the inline marker at line 254 ("[This is the gap, the expansion is wrong because
action-values / value functions off-policy are wrong]") locates the gap in Lemma 1's off-policy value
expansion (per [[uea-inventory]] 021 it is Abram's annotation). The live post has no `[EDIT …]` at line 198 —
the mandate's pointer was wrong (repair round 1). The same refutation holds under the charitable, existential
reading of "π_S" (some fixed point): `Printed2025.readingExists_false` (`ChainCorollaries.lean`). Surviving
neighbours: Theorem B (the conclusion at trust-bound nodes), D1 (`∀ε ∀T ∃δ ∃ fixed point`, `BestOnPath.lean`),
Theorem A's good-point condition.
Source: [[lesswrong-post--live-2026-08-22]] lines 233, 236, 254; `lesswrong-post--logsidian-annotated-copy-2025-07.md`
line 591; [[uea-inventory]] 021 (rule-3 row)
Kind: P
Fidelity: exact (against the reading above)
Hyps: (a) -/
theorem printed_theorem1_refuted : ¬ Reading := by
  intro H
  obtain ⟨δ₀, hδ₀, H⟩ := H (1 / 4) (by norm_num)
  set δ := min (δ₀ / 2) (1 / 2) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδδ₀ : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨M, π, hMδ, hfp, _, hgap⟩ := refuting_family δ hδ hδ1
  have := H (Fin 2) Unit (Fin 2) M (by rw [hMδ]; exact hδδ₀) π hfp island
  rw [hgap] at this
  norm_num at this

end Printed2025


/-! ### (A6, stretch S4): the floored fixed points of `sos P` -/

namespace TheoremA

variable (P : Params)

/-- `π⋆(island) = jump` (`b > c`). -/
theorem piStar_island : (sos P).piStar 0 island = 1 := by
  apply (sos P).piStar_eq_of_unique (nt_island P)
  refine Fin.forall_fin_two.2 ⟨fun ha => ?_, fun _ => rfl⟩
  rw [Qstar_island_0, Vstar_island] at ha
  exact absurd ha P.hcb.ne

theorem resid_island {π : Policy (Fin 2) Unit} :
    (sos P).resid π 0 island = (sos P).Mx π 0 island - (1 - P.δ) * P.b := by
  unfold Model.resid; rw [wS_island, Vstar_island]

theorem resid_water_nonneg {π : Policy (Fin 2) Unit} (hπ : (sos P).IsPolicy π) : 0 ≤ (sos P).resid π 1 water := by
  unfold Model.resid
  rw [Mx_water, Vstar_water]
  have hw := (sos P).wS_le_one hπ (nt_water P)
  have := b_pos P
  nlinarith

/-- A floored fixed point of `sos P` has `resid(island) ≥ 0`: if the floor fired, the support would be `{jump}`,
where `M = b(1-δs) ≥ (1-δ) b` — a contradiction. -/
theorem resid_island_nonneg_of_isFlooredFP {π : Policy (Fin 2) Unit} (hfp : (sos P).IsFlooredFP π) :
    0 ≤ (sos P).resid π 0 island := by
  have hπ := hfp.1
  have hσ := swim_of_isFlooredFP P hfp
  by_contra hneg
  have hneg' : (sos P).resid π 0 island < 0 := not_le.1 hneg
  have hsupp := (hfp.2 0 island (nt_island P)).1 hneg'
  have h0 : π 0 island 0 = 0 := by
    by_contra hne
    have hpos : 0 < π 0 island 0 := lt_of_le_of_ne (hπ.nonneg (nt_island P) 0) (Ne.symm hne)
    have := hsupp 0 hpos
    rw [piStar_island] at this
    exact absurd this (by decide)
  have hj : π 0 island 1 = 1 := by have := hπ.fin_two_zero (nt_island P); rw [h0] at this; linarith
  rw [resid_island, Model.Mx_fin_two, Qxi_island_0, Qxi_island_1_eq P hπ hσ, hj, QJ_one] at hneg'
  have hb := b_pos P; have hδ := P.hδ; have hs := P.hs1
  have h1 : (1 - P.δ) * P.b ≤ P.b * (1 - P.δ * P.s) := by nlinarith [mul_nonneg (mul_nonneg hb.le hδ.le) (sub_nonneg.2 hs)]
  have h2 := le_max_right P.c (P.b * (1 - P.δ * P.s))
  linarith

/-- **(A6) the trap**: the trap is a floored fixed point iff it is a plain fixed point (`b(1-s) ≤ c`) and the floor does
not fire (`(1-δ) b ≤ c`, i.e. `δ ≥ 1 - c/b`): the floor removes exactly the `TB`-rejected trap.
Source: [[sequential-self-game]] §1 (the floored agent) and §2 ("Where the mixed point sits"); the label A6 is the mandate's (target 1, stretch S4), not the note's
Kind: P
Fidelity: exact (both directions)
Hyps: (a) -/
theorem trap_isFlooredFP_iff : (sos P).IsFlooredFP trap ↔ P.b * (1 - P.s) ≤ P.c ∧ (1 - P.δ) * P.b ≤ P.c := by
  constructor
  · intro hfp
    have hr := resid_island_nonneg_of_isFlooredFP P hfp
    have hplain : P.b * (1 - P.s) ≤ P.c := by
      have := hfp.supp_of_nonneg (nt_island P) hr (show 0 < trap 0 island 0 by simp [trap])
      rcases this with h | h
      · rw [Qxi_island_0, Model.Mx_fin_two, Qxi_island_0, Qxi_island_1_eq P (trap_isPolicy P) trap_σ, trap_j, QJ_zero] at h
        exact max_eq_left_iff.1 h.symm
      · rw [piStar_island] at h; exact absurd h (by decide)
    refine ⟨hplain, ?_⟩
    rw [resid_island, Mx_trap P hplain] at hr
    linarith
  · rintro ⟨hplain, htb⟩
    refine FiveTen_floored P ((trap_isPlainFP_iff P).2 hplain) fun n h hnt => ?_
    match n with
    | 0 => rw [eq_island h, resid_island, Mx_trap P hplain]; linarith
    | 1 => rw [eq_water_of_nonterminal P h hnt]; exact resid_water_nonneg P (trap_isPolicy P)
    | n + 2 => exact absurd hnt (not_nt_ge_two P (n + 2) (by omega) h)
where
  FiveTen_floored (P : Params) {π : Policy (Fin 2) Unit} (hfp : (sos P).IsPlainFP π)
      (hr : ∀ n h, (sos P).nonterminal n h → 0 ≤ (sos P).resid π n h) : (sos P).IsFlooredFP π :=
    ⟨hfp.1, fun n h hnt => ⟨fun hneg => absurd (hr n h hnt) (not_le.2 hneg), fun _ a ha => hfp.2 n h hnt a ha,
      fun _ a ha => Or.inl (hfp.2 n h hnt a ha)⟩⟩

/-- **(A6) the good point**: the good point is a floored fixed point iff it is a plain one (`c ≤ b(1-δs)`) — the floor
never removes it (`M = b(1-δs) ≥ (1-δ) b`).
Source: [[sequential-self-game]] §1 (the floored agent) and §2 ("Where the mixed point sits"); mandate label A6, stretch S4
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem good_isFlooredFP_iff : (sos P).IsFlooredFP good ↔ P.c ≤ P.b * (1 - P.δ * P.s) := by
  have hb := b_pos P; have hδ := P.hδ; have hs := P.hs1
  have h1 : (1 - P.δ) * P.b ≤ P.b * (1 - P.δ * P.s) := by nlinarith [mul_nonneg (mul_nonneg hb.le hδ.le) (sub_nonneg.2 hs)]
  constructor
  · intro hfp
    have hr := resid_island_nonneg_of_isFlooredFP P hfp
    rcases hfp.supp_of_nonneg (nt_island P) hr (show 0 < good 0 island 1 by simp [good]) with h | h
    · rw [Model.Mx_fin_two, Qxi_island_0, Qxi_island_1_eq P (good_isPolicy P) good_σ, good_j, QJ_one] at h
      exact max_eq_right_iff.1 h.symm
    · -- `jump = π⋆`: the floor clause at `resid = 0`; then `M = (1-δ) b ≤ b(1-δs)` and `c ≤ M`
      rw [resid_island] at hr
      have hM : (sos P).Mx good 0 island = max P.c (P.b * (1 - P.δ * P.s)) := by
        rw [Model.Mx_fin_two, Qxi_island_0, Qxi_island_1_eq P (good_isPolicy P) good_σ, good_j, QJ_one]
      by_contra hc
      have hc' : P.b * (1 - P.δ * P.s) < P.c := not_le.1 hc
      rw [hM, max_eq_left hc'.le] at hr
      -- `resid = c - (1-δ) b ≥ 0`; the floored clauses at `resid > 0` force `jump ∈ argmax`, false
      rcases lt_or_eq_of_le hr with hpos | hzero
      · have := (hfp.2 0 island (nt_island P)).2.1 (by rw [resid_island, hM, max_eq_left hc'.le]; exact hpos) 1
          (by simp [good])
        rw [hM, max_eq_left hc'.le, Qxi_island_1_eq P (good_isPolicy P) good_σ, good_j, QJ_one] at this
        linarith
      · -- `resid = 0`: `c = (1-δ) b ≤ b(1-δs) < c`
        linarith
  · intro h
    refine trap_isFlooredFP_iff.FiveTen_floored P ((good_isPlainFP_iff P).2 h) fun n h' hnt => ?_
    match n with
    | 0 => rw [eq_island h', resid_island, Mx_good P h]; linarith
    | 1 => rw [eq_water_of_nonterminal P h' hnt]; exact resid_water_nonneg P (good_isPolicy P)
    | n + 2 => exact absurd hnt (not_nt_ge_two P (n + 2) (by omega) h')

/-- **(A6) the mixed point**: the mixed plain fixed point `j*` is a floored fixed point iff `(1-δ) b ≤ c`.
Source: [[sequential-self-game]] §2 ("Where the mixed point sits"); mandate label A6, stretch S4
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem mixedStar_isFlooredFP_iff (hj0 : 0 < jstar P) (hj1 : jstar P < 1) :
    (sos P).IsFlooredFP (mixedPol (jstar P)) ↔ (1 - P.δ) * P.b ≤ P.c := by
  have hfp : (sos P).IsPlainFP (mixedPol (jstar P)) := (mixedPol_isPlainFP_iff_jstar P hj0 hj1).2 rfl
  have hM := Mx_mixed P hj0 hj1 hfp
  constructor
  · intro hf
    have hr := resid_island_nonneg_of_isFlooredFP P hf
    rw [resid_island, hM] at hr
    linarith
  · intro h
    refine trap_isFlooredFP_iff.FiveTen_floored P hfp fun n h' hnt => ?_
    match n with
    | 0 => rw [eq_island h', resid_island, hM]; linarith
    | 1 => rw [eq_water_of_nonterminal P h' hnt]; exact resid_water_nonneg P (mixedPol_isPolicy P hj0.le hj1.le)
    | n + 2 => exact absurd hnt (not_nt_ge_two P (n + 2) (by omega) h')

/-- **The equality family (finding)**: at `c = (1-δ) b` every policy that swims and whose jump-value is at most `c`
(`QJ(j) ≤ c`) is a floored fixed point — the floor's `λ_h`-mixing at `resid = 0` — although only `j ∈ {0, j*}` (and
`j = 1` when `c ≤ b(1-δs)`) are plain fixed points: the floored fixed-point set is strictly larger than the plain one
on the boundary.
Source: [[sequential-self-game]] §1 (the `λ_h` clause of `π†`); stretch S4
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem isFlooredFP_of_boundary (hc : P.c = (1 - P.δ) * P.b) {j : ℝ} (hj0 : 0 ≤ j) (hj1 : j ≤ 1)
    (hQ : QJ P j ≤ P.c) : (sos P).IsFlooredFP (mixedPol j) := by
  have hπ := mixedPol_isPolicy P hj0 hj1
  have hM : (sos P).Mx (mixedPol j) 0 island = P.c := by
    rw [Model.Mx_fin_two, Qxi_island_0, Qxi_island_1_eq P hπ (mixedPol_σ j), mixedPol_j]
    exact max_eq_left hQ
  refine ⟨hπ, fun n h hnt => ?_⟩
  match n with
  | 0 =>
    rw [eq_island h]
    have hr : (sos P).resid (mixedPol j) 0 island = 0 := by rw [resid_island, hM, hc, sub_self]
    refine ⟨fun hneg => absurd hr hneg.ne, fun hpos => absurd hr hpos.ne', fun _ => ?_⟩
    refine Fin.forall_fin_two.2 ⟨fun _ => Or.inl ?_, fun _ => Or.inr (piStar_island P).symm⟩
    rw [Qxi_island_0, hM]
  | 1 =>
    rw [eq_water_of_nonterminal P h hnt]
    have hr := resid_water_nonneg P hπ
    refine ⟨fun hneg => absurd hr (not_le.2 hneg), fun _ a ha => ?_, fun _ a ha => Or.inl ?_⟩ <;>
    · have h1 : mixedPol j 1 water 1 = 0 := by simp [mixedPol]
      rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with h' | h'
      · rw [h', Qxi_water_0, Mx_water]
      · exfalso; rw [h', h1] at ha; exact lt_irrefl _ ha
  | n + 2 => exact absurd hnt (not_nt_ge_two P (n + 2) (by omega) h)

end TheoremA

end Cleanroom.Uea.UeaSinkSwim
