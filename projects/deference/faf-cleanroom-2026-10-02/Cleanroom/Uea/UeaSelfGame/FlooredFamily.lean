import Cleanroom.Uea.UeaSelfGame.Repaired
import Cleanroom.Uea.UeaSelfGame.TablesMixed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The floored family: gap `2δ + O(δ³)` at every `δ ∈ (0, 1/4]` — the constant `2` cannot be lowered

The mandate's `stretch` family for Theorem D's mixed claim (target 9), at symbolic `δ`:
`S = A = Fin 2`, `U(aa) = U(bb) = 1`, `U(ab) = U(ba) = 0`, `Po = δ_{aa}`, `piStar = bb`,
`σ_s = q a + (1−q) b` at both situations, with `q` the larger root of `q² − (1−δ) q + δ²/(1−δ) = 0`
(real for `δ ≤ 1/4`: the discriminant is `(1−δ)² − 4δ²/(1−δ) ≥ 0` iff `(1−δ)³ ≥ 4δ²`). Then
`Fext σ s a = 1 − δ = (1−δ) U*` exactly (the equality branch — this *is* the quadratic) and
`Fext σ s b = 1 − q ≤ 1 − δ`, so `σ` is a floored extension fixed point (the reset action `b = piStar s`
carries mass `1 − q` at equality), convention-free (every action available), not a plain one, with
`U(σ) = q² + (1−q)²` and gap `2 q (1−q) = δ(1−δ) + 2δ²/(1−δ) + δ √disc`, which lies between
`2δ − 8δ³` and `2δ + 2δ³/(1−δ)`. (`Section5` in `Floored.lean` is a different instance at `δ = 1/10`; the
mandate reports this family's gap as `1.895δ, 1.997δ, 2.000δ` at `δ = 1/4, 1/10, 1/100`.)

Consequence (`constant_ge_two`): **no bound of the form `U* − c δ/(1−δ) ≤ U(σ)` for floored extension
fixed points holds with `c < 2`**, already over `2 × 2` games with `δ ≤ 1/4`. So the constant `2` in the
open statement `floored_mixed_bound_open` (`Open.lean`) is the least possible; the family is consistent
with that statement (`gap_le_open_bound`: the gap is `≤ 2δ/(1−δ)`), so it does not refute it.

Scope: finite updateless self-game — product self-hypothesis, continuous extension at null actions,
floored agent; not rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, repair round 1, 2026-10-01).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

namespace FlooredFamily

/-! ### The root `q` -/

/-- The discriminant `(1−δ)² − 4δ²/(1−δ)` of `q² − (1−δ) q + δ²/(1−δ)`.
Source: [[uea-self-game-mandate]] target 9 (`stretch` family)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def D (δ : ℝ) : ℝ := (1 - δ) ^ 2 - 4 * δ ^ 2 / (1 - δ)

variable {δ : ℝ} (h0 : 0 < δ) (h4 : δ ≤ 1 / 4)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem one_sub_pos (h4 : δ ≤ 1 / 4) : 0 < 1 - δ := by linarith

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem δ_sq_le (h0 : 0 < δ) (h4 : δ ≤ 1 / 4) : δ ^ 2 ≤ 1 / 16 := by
  nlinarith [mul_le_mul_of_nonneg_left h4 h0.le]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem D_mul (h4 : δ ≤ 1 / 4) : (1 - δ) * D δ = (1 - δ) ^ 3 - 4 * δ ^ 2 := by
  have h := (one_sub_pos h4).ne'
  unfold D; field_simp

/-- The discriminant is nonnegative for `δ ≤ 1/4` (`(1−δ)³ ≥ 27/64 > 1/4 ≥ 4δ²`).
Source: [[uea-self-game-mandate]] target 9 ("discriminant `(1−δ)³ − 4δ² > 0` for `δ ≤ 1/4`")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem D_nonneg (h0 : 0 < δ) (h4 : δ ≤ 1 / 4) : 0 ≤ D δ := by
  have hx := one_sub_pos h4
  have hm := D_mul h4
  have h34 : (3 / 4 : ℝ) ≤ 1 - δ := by linarith
  have hq : 0 ≤ (1 - δ) ^ 2 + 3 / 4 * (1 - δ) + 9 / 16 := by nlinarith [sq_nonneg (1 - δ)]
  have hc : (3 / 4 : ℝ) ^ 3 ≤ (1 - δ) ^ 3 := by nlinarith [mul_nonneg (sub_nonneg.2 h34) hq]
  have hδ2 := δ_sq_le h0 h4
  have hpoly : 0 ≤ (1 - δ) ^ 3 - 4 * δ ^ 2 := by norm_num at hc; linarith
  by_contra hneg
  push Not at hneg
  have := mul_neg_of_pos_of_neg hx hneg
  linarith

/-- `r := √D`.
Source: [[uea-self-game-mandate]] target 9 (`stretch` family: "a parametric `P` over `Real.sqrt` of the discriminant")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def r (δ : ℝ) : ℝ := Real.sqrt (D δ)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem r_sq (h0 : 0 < δ) (h4 : δ ≤ 1 / 4) : r δ ^ 2 = D δ := Real.sq_sqrt (D_nonneg h0 h4)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem r_nonneg : 0 ≤ r δ := Real.sqrt_nonneg _

/-- `r ≤ 1 − δ` (`D ≤ (1−δ)²`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem r_le (h0 : 0 < δ) (h4 : δ ≤ 1 / 4) : r δ ≤ 1 - δ := by
  have hx := one_sub_pos h4
  have hD : D δ ≤ (1 - δ) ^ 2 := by
    unfold D
    have : 0 ≤ 4 * δ ^ 2 / (1 - δ) := by positivity
    linarith
  calc r δ = Real.sqrt (D δ) := rfl
    _ ≤ Real.sqrt ((1 - δ) ^ 2) := Real.sqrt_le_sqrt hD
    _ = 1 - δ := Real.sqrt_sq hx.le

/-- `(1−δ) − 8δ² ≤ r` (a clean lower bound on `√D` for `δ ≤ 1/4`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem r_ge (h0 : 0 < δ) (h4 : δ ≤ 1 / 4) : (1 - δ) - 8 * δ ^ 2 ≤ r δ := by
  have hx := one_sub_pos h4
  have hδ2 := δ_sq_le h0 h4
  have hz : 0 ≤ (1 - δ) - 8 * δ ^ 2 := by linarith
  have hzD : ((1 - δ) - 8 * δ ^ 2) ^ 2 ≤ D δ := by
    unfold D
    rw [show ((1 - δ) - 8 * δ ^ 2) ^ 2 = (1 - δ) ^ 2 - (16 * δ ^ 2 * (1 - δ) - 64 * δ ^ 4) by ring]
    have key : 4 * δ ^ 2 / (1 - δ) ≤ 16 * δ ^ 2 * (1 - δ) - 64 * δ ^ 4 := by
      rw [div_le_iff₀ hx]
      have hg : 0 ≤ 40 + 32 * δ - 64 * δ ^ 2 := by linarith
      have hp := mul_nonneg (sub_nonneg.2 h4) hg
      nlinarith [mul_nonneg (sq_nonneg δ) hp, sq_nonneg δ]
    linarith
  calc (1 - δ) - 8 * δ ^ 2 = Real.sqrt (((1 - δ) - 8 * δ ^ 2) ^ 2) := (Real.sqrt_sq hz).symm
    _ ≤ Real.sqrt (D δ) := Real.sqrt_le_sqrt hzD
    _ = r δ := rfl

/-- The larger root `q := ((1−δ) + √D)/2` of `q² − (1−δ) q + δ²/(1−δ) = 0`.
Source: [[uea-self-game-mandate]] target 9 (`stretch` family, "larger root")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def q (δ : ℝ) : ℝ := ((1 - δ) + r δ) / 2

/-- **`q` solves the quadratic**, in cleared form: `(1−δ) q² − (1−δ)² q + δ² = 0`.
Source: [[uea-self-game-mandate]] target 9 (`q² − (1−δ) q + δ²/(1−δ) = 0`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem q_cleared (h0 : 0 < δ) (h4 : δ ≤ 1 / 4) : (1 - δ) * q δ ^ 2 - (1 - δ) ^ 2 * q δ + δ ^ 2 = 0 := by
  unfold q
  linear_combination ((1 - δ) / 4) * r_sq h0 h4 + (1 / 4) * D_mul h4

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem q_le (h0 : 0 < δ) (h4 : δ ≤ 1 / 4) : q δ ≤ 1 - δ := by
  unfold q; have := r_le h0 h4; linarith

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem q_ge : (1 - δ) / 2 ≤ q δ := by
  unfold q; have := r_nonneg (δ := δ); linarith

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem δ_lt_q (h4 : δ ≤ 1 / 4) : δ < q δ := by
  have := q_ge (δ := δ); linarith

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem q_pos (h0 : 0 < δ) (h4 : δ ≤ 1 / 4) : 0 < q δ := lt_trans h0 (δ_lt_q h4)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem one_sub_q_pos (h0 : 0 < δ) (h4 : δ ≤ 1 / 4) : 0 < 1 - q δ := by
  have := q_le h0 h4; linarith

/-! ### The instance -/

/-- The family's game at `δ`: `U = (aa:1, ab:0, ba:0, bb:1)`, `Po = δ_{aa}`, `piStar = bb`.
Source: [[uea-self-game-mandate]] target 9 (`stretch` family)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def game (d : ℝ) (hd0 : 0 < d) (hd4 : d ≤ 1 / 4) : Game (Fin 2) (Fin 2) where
  U := tab2 1 0 0 1
  U_nonneg := fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) π).1
  U_le_one := fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) π).2
  piStar := ![1, 1]
  piStar_max := fun π => by
    rw [tab2_11]
    exact (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  Po := tab2 1 0 0 0
  Po_mem := ⟨fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) π).1, by rw [sum_tab2]; norm_num⟩
  δ := d
  δ_nonneg := hd0.le
  δ_lt_one := lt_of_le_of_lt hd4 (by norm_num)

/-- The mixed policy `σ_s = q a + (1−q) b` at both situations.
Source: [[uea-self-game-mandate]] target 9 (`stretch` family)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def σ (d : ℝ) : Fin 2 → Fin 2 → ℝ := fun _ a => if a = 0 then q d else 1 - q d

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem σ_0 (s : Fin 2) : σ δ s 0 = q δ := by simp [σ]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem σ_1 (s : Fin 2) : σ δ s 1 = 1 - q δ := by simp [σ]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem U_apply (π) : (game δ h0 h4).U π = tab2 1 0 0 1 π := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Po_apply (π) : (game δ h0 h4).Po π = tab2 1 0 0 0 π := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem δ_eq : (game δ h0 h4).δ = δ := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem piStar_eq : (game δ h0 h4).piStar = ![1, 1] := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ustar_eq : (game δ h0 h4).Ustar = 1 := by simp [Game.Ustar, game]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem thr_eq : (game δ h0 h4).thr = 1 - δ := by simp [Game.thr, Ustar_eq, δ_eq]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem isMixed (h0 : 0 < δ) (h4 : δ ≤ 1 / 4) : IsMixed (σ δ) := fun s =>
  ⟨fun a => by
    have := q_pos h0 h4; have := one_sub_q_pos h0 h4
    unfold σ; split_ifs <;> linarith,
   by simp [Fin.sum_univ_two]⟩

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_0 (s : Fin 2) : (game δ h0 h4).pa s 0 = 1 := by
  unfold Game.pa; rw [Game.condDen_fin2]
  revert s; simp only [Fin.forall_fin_two]
  simp [Fin.sum_univ_two, Po_apply]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_1 (s : Fin 2) : (game δ h0 h4).pa s 1 = 0 := by
  unfold Game.pa; rw [Game.condDen_fin2]
  revert s; simp only [Fin.forall_fin_two]
  simp [Fin.sum_univ_two, Po_apply]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_0 (s : Fin 2) : (game δ h0 h4).pva s 0 = 1 := by
  unfold Game.pva; rw [Game.condNum_fin2]
  revert s; simp only [Fin.forall_fin_two]
  simp [Fin.sum_univ_two, Po_apply, U_apply]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ucoord_0 (s : Fin 2) : (game δ h0 h4).Ucoord (σ δ) s 0 = q δ := by
  revert s; simp only [Fin.forall_fin_two]
  constructor
  · rw [Game.Ucoord_fin2_0]; simp [Fin.sum_univ_two, U_apply]
  · rw [Game.Ucoord_fin2_1]; simp [Fin.sum_univ_two, U_apply]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ucoord_1 (s : Fin 2) : (game δ h0 h4).Ucoord (σ δ) s 1 = 1 - q δ := by
  revert s; simp only [Fin.forall_fin_two]
  constructor
  · rw [Game.Ucoord_fin2_0]; simp [Fin.sum_univ_two, U_apply]
  · rw [Game.Ucoord_fin2_1]; simp [Fin.sum_univ_two, U_apply]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem denMix_0 (s : Fin 2) : (game δ h0 h4).denMix (σ δ) s 0 = (1 - δ) * q δ + δ := by
  unfold Game.denMix; rw [pa_0, σ_0, δ_eq]; ring

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem denMix_1 (s : Fin 2) : (game δ h0 h4).denMix (σ δ) s 1 = (1 - δ) * (1 - q δ) := by
  unfold Game.denMix; rw [pa_1, σ_1, δ_eq]; ring

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem denMix_0_pos (s : Fin 2) : 0 < (game δ h0 h4).denMix (σ δ) s 0 := by
  rw [denMix_0]; have := q_pos h0 h4; have := one_sub_pos h4; positivity

/-- **`Fext σ s a = 1 − δ = (1−δ) U*` exactly** at both situations: the equality branch. The fixed-point
equation *is* the quadratic `(1−δ) q² − (1−δ)² q + δ² = 0`.
Source: [[uea-self-game-mandate]] target 9 (`stretch` family)
Kind: P
Fidelity: exact (symbolic `δ`)
Hyps: (a) -/
theorem Fext_0 (s : Fin 2) : (game δ h0 h4).Fext (σ δ) s 0 = 1 - δ := by
  rw [(game δ h0 h4).Fext_eq_of_availMix (denMix_0_pos h0 h4 s), denMix_0, Ucoord_0, pva_0, σ_0, δ_eq]
  have hd : (1 - δ) * q δ + δ ≠ 0 := by
    have := q_pos h0 h4; have := one_sub_pos h4; positivity
  rw [div_eq_iff hd]
  linear_combination q_cleared h0 h4

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Fext_1 (s : Fin 2) : (game δ h0 h4).Fext (σ δ) s 1 = 1 - q δ := by
  rw [(game δ h0 h4).Fext_eq_Ucoord_of_pa_eq_zero (σ δ) (pa_1 h0 h4 s), Ucoord_1]

/-- Every action is available at both situations: the witness is convention-free.
Source: [[uea-self-game-mandate]] target 9
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem availMix_all (s a : Fin 2) : (game δ h0 h4).availMix (σ δ) s a := by
  unfold Game.availMix
  revert a; simp only [Fin.forall_fin_two]
  constructor
  · exact denMix_0_pos h0 h4 s
  · rw [denMix_1]; have := one_sub_q_pos h0 h4; have := one_sub_pos h4; positivity

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem maxF_eq (s : Fin 2) : (game δ h0 h4).maxF (σ δ) s = 1 - δ := by
  apply le_antisymm
  · have key : ∀ a : Fin 2, (game δ h0 h4).Fext (σ δ) s a ≤ 1 - δ := by
      simp only [Fin.forall_fin_two]
      exact ⟨by rw [Fext_0], by rw [Fext_1]; have := δ_lt_q h4; linarith⟩
    exact Finset.sup'_le _ _ fun a _ => key a
  · rw [← Fext_0 h0 h4 s]; exact (game δ h0 h4).Fext_le_maxF (σ δ) s 0

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem resid_eq (s : Fin 2) : (game δ h0 h4).resid (σ δ) s = 0 := by
  unfold Game.resid; rw [maxF_eq, thr_eq]; ring

/-- **`σ` is a floored fixed point** at every `δ ∈ (0, 1/4]` (equality branch at both situations: `a` is the
argmax, `b = piStar s` the reset action with mass `1 − q`).
Source: [[uea-self-game-mandate]] target 9 (`stretch` family)
Kind: N+
Fidelity: exact (symbolic `δ`)
Hyps: (a) -/
theorem isFlooredFPext : (game δ h0 h4).IsFlooredFPext (σ δ) := by
  refine ⟨isMixed h0 h4, fun s => ⟨fun hr => ?_, fun hr => ?_, fun _ a _ => ?_⟩⟩
  · rw [resid_eq] at hr; exact absurd hr (lt_irrefl 0)
  · rw [resid_eq] at hr; exact absurd hr (lt_irrefl 0)
  · revert a; simp only [Fin.forall_fin_two]
    constructor
    · intro _; left; rw [Fext_0, maxF_eq]
    · intro _; right; rw [piStar_eq]; fin_cases s <;> rfl

/-- **`σ` is not a plain fixed point** (`b` is supported with `Fext σ s b = 1 − q < 1 − δ = Fext σ s a`),
under either convention.
Source: [[uea-self-game-mandate]] target 9
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem not_isFPherr : ¬ (game δ h0 h4).IsFPherr (σ δ) := by
  rintro ⟨_, h⟩
  have := h 0 1 (by rw [σ_1]; exact one_sub_q_pos h0 h4) 0 (availMix_all h0 h4 0 0)
  rw [Fext_0, Fext_1] at this
  have := δ_lt_q h4
  linarith

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem not_isFPext : ¬ (game δ h0 h4).IsFPext (σ δ) := fun h => not_isFPherr h0 h4 h.isFPherr

/-- `U(σ) = q² + (1−q)²`.
Source: [[uea-self-game-mandate]] target 9 ("gap `1 − q² − (1−q)²`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Umix_eq : (game δ h0 h4).Umix (σ δ) = q δ ^ 2 + (1 - q δ) ^ 2 := by
  rw [Game.Umix_fin2]; simp [Fin.sum_univ_two, U_apply]; ring

/-! ### The gap -/

/-- **The gap in closed form**: `U* − U(σ) = 2 q (1−q) = δ(1−δ) + 2δ²/(1−δ) + δ √D`.
Source: [[uea-self-game-mandate]] target 9 (`stretch` family)
Kind: P
Fidelity: exact (symbolic `δ`)
Hyps: (a) -/
theorem gap_eq : (game δ h0 h4).Ustar - (game δ h0 h4).Umix (σ δ) =
    δ * (1 - δ) + 2 * δ ^ 2 / (1 - δ) + δ * r δ := by
  rw [Umix_eq, Ustar_eq]
  have hr := r_sq h0 h4
  unfold D at hr
  unfold q
  linear_combination (-1 / 2) * hr

/-- **Two-sided bound**: `2δ − 8δ³ ≤ gap ≤ 2δ + 2δ³/(1−δ)` — the gap is `2δ + O(δ³)`.
Source: [[uea-self-game-mandate]] target 9 (the family "shows the constant is `≥ 2δ` asymptotically")
Kind: P
Fidelity: exact (symbolic `δ`)
Hyps: (a) -/
theorem gap_bounds :
    2 * δ - 8 * δ ^ 3 ≤ (game δ h0 h4).Ustar - (game δ h0 h4).Umix (σ δ) ∧
      (game δ h0 h4).Ustar - (game δ h0 h4).Umix (σ δ) ≤ 2 * δ + 2 * δ ^ 3 / (1 - δ) := by
  rw [gap_eq]
  have hx := one_sub_pos h4
  have hge := r_ge h0 h4
  have hle := r_le h0 h4
  have hne := hx.ne'
  constructor
  · have h2 : 2 * δ ^ 2 ≤ 2 * δ ^ 2 / (1 - δ) := by
      rw [le_div_iff₀ hx]; nlinarith [sq_nonneg δ]
    have := mul_le_mul_of_nonneg_left hge h0.le
    nlinarith
  · have h3 : 2 * δ ^ 2 / (1 - δ) = 2 * δ ^ 2 + 2 * δ ^ 3 / (1 - δ) := by
      field_simp; ring
    rw [h3]
    have := mul_le_mul_of_nonneg_left hle h0.le
    nlinarith

/-- **The family is consistent with the open statement**: its gap is `≤ 2δ/(1−δ)`, so it does not refute
`floored_mixed_bound_open`; it shows the constant `2` there cannot be lowered.
Source: [[uea-self-game-mandate]] target 9 (f)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem gap_le_open_bound :
    (game δ h0 h4).Ustar - (game δ h0 h4).Umix (σ δ) ≤ 2 * δ / (1 - δ) := by
  have hx := one_sub_pos h4
  have hne := hx.ne'
  refine le_trans (gap_bounds h0 h4).2 ?_
  have h3 : 2 * δ / (1 - δ) = 2 * δ + 2 * δ ^ 2 / (1 - δ) := by field_simp; ring
  rw [h3]
  have : 2 * δ ^ 3 / (1 - δ) ≤ 2 * δ ^ 2 / (1 - δ) := by
    apply div_le_div_of_nonneg_right _ hx.le
    nlinarith [sq_nonneg δ]
  linarith

/-- **The floored family, packaged**: for every `δ ∈ (0, 1/4]` there is a `2 × 2` game at `δ` with a floored
extension fixed point `σ`, convention-free, not a plain fixed point, whose gap lies in
`[2δ − 8δ³, 2δ + 2δ³/(1−δ)]`.
Scope: finite updateless self-game — floored agent, continuous extension; not rOSI, not the sequential
model of `uea-cole-shadow`.
Source: [[uea-self-game-mandate]] target 9 (`stretch` family; (f))
Kind: P
Fidelity: exact (symbolic `δ`; the mandate's three numerical values at `δ = 1/4, 1/10, 1/100` are instances)
Hyps: (a) -/
theorem family (δ : ℝ) (h0 : 0 < δ) (h4 : δ ≤ 1 / 4) :
    ∃ (G : Game (Fin 2) (Fin 2)) (σ : Fin 2 → Fin 2 → ℝ), G.δ = δ ∧ G.IsFlooredFPext σ ∧
      (∀ s a, G.availMix σ s a) ∧ ¬ G.IsFPext σ ∧
      2 * δ - 8 * δ ^ 3 ≤ G.Ustar - G.Umix σ ∧ G.Ustar - G.Umix σ ≤ 2 * δ + 2 * δ ^ 3 / (1 - δ) :=
  ⟨game δ h0 h4, σ δ, rfl, isFlooredFPext h0 h4, availMix_all h0 h4, not_isFPext h0 h4,
    (gap_bounds h0 h4).1, (gap_bounds h0 h4).2⟩

/-- **The constant `2` cannot be lowered**: if `U* − c δ/(1−δ) ≤ U(σ)` held for every floored extension fixed
point of every `2 × 2` game with `δ ≤ 1/4`, then `c ≥ 2`. (At `δ` the family forces
`c ≥ (2 − 8δ²)(1−δ)`, and `δ ↓ 0` gives `2`.) So the constant in `floored_mixed_bound_open` cannot be
lowered below `2`; whether `2` itself works is the open statement.
Scope: finite updateless self-game — floored agent, continuous extension; not rOSI, not the sequential
model of `uea-cole-shadow`.
Source: [[uea-self-game-mandate]] target 9 (f) ("the family shows the constant is `≥ 2δ` asymptotically")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem constant_ge_two (c : ℝ)
    (hc : ∀ G : Game (Fin 2) (Fin 2), G.δ ≤ 1 / 4 → ∀ σ, G.IsFlooredFPext σ →
      G.Ustar - c * G.δ / (1 - G.δ) ≤ G.Umix σ) : 2 ≤ c := by
  by_contra hlt
  push Not at hlt
  set δ : ℝ := min (1 / 4) ((2 - c) / 4) with hδ
  have h0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have h4 : δ ≤ 1 / 4 := min_le_left _ _
  have hc4 : 4 * δ ≤ 2 - c := by
    have := min_le_right (1 / 4) ((2 - c) / 4); linarith
  have hx := one_sub_pos h4
  have hb := hc (game δ h0 h4) h4 (σ δ) (isFlooredFPext h0 h4)
  rw [δ_eq] at hb
  have hgap := (gap_bounds h0 h4).1
  have h1 : 2 * δ - 8 * δ ^ 3 ≤ c * δ / (1 - δ) := by linarith
  rw [le_div_iff₀ hx] at h1
  -- `(2 − 8δ²)(1−δ) ≤ c`, i.e. `2 − 2δ − 8δ² + 8δ³ ≤ c`, while `c ≤ 2 − 4δ` and `8δ² ≤ 2δ`
  have h2 : (2 - 8 * δ ^ 2) * (1 - δ) ≤ c := by
    have : δ * ((2 - 8 * δ ^ 2) * (1 - δ)) ≤ δ * c := by linarith
    exact le_of_mul_le_mul_left this h0
  nlinarith [mul_le_mul_of_nonneg_left h4 h0.le, pow_pos h0 3]

end FlooredFamily

end Cleanroom.Uea.UeaSelfGame
