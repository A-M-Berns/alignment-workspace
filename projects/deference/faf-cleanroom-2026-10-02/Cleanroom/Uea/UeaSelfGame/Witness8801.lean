import Cleanroom.Uea.UeaSelfGame.Section6
import Cleanroom.Uea.UeaSelfGame.TablesMixed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The exact mixed fixed point of the §6 instance: `q = (86 + √8801)/180`

On the §6 instance (`Section6.game`), `σ = (q a + (1−q) b, a, a)` with `q = (86 + √8801)/180` — the
positive root of `6480 q² − 6192 q − 281 = 0` — is an extension fixed point: at `s₀` both actions are
supported and `Fext σ s₀ a = Fext σ s₀ b = (219 + √8801)/320` (the fixed-point equation *is* the
quadratic); at `s₁`, `Fext σ s₁ a = (202 + √8801)/296 > 17/24 = Fext σ s₁ b`; at `s₂`, `Fext σ s₂ a =
(210 + √8801)/304 > 9/16 = Fext σ s₂ b`. The trust bound holds at every situation (all three maxima
`> 9/10`), and `U(σ) = (194 + √8801)/288 ≥ 8/9 = U* − δ/(1−δ)`, as Theorem C′ requires. A **real** fixed
point of **rational** data (never claim a rational one); N+ for `theoremC'_ext` and for `exists_isFPext`;
also a Herrmann fixed point by `IsFPext.isFPherr`.

Scope: finite updateless self-game — product self-hypothesis, continuous extension at null actions;
not rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

namespace Witness8801

open Section6

/-- `r := √8801`.
Source: none: infrastructure (instance datum)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def r : ℝ := Real.sqrt 8801
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem r_sq : r ^ 2 = 8801 := Real.sq_sqrt (by norm_num)
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem r_nonneg : 0 ≤ r := Real.sqrt_nonneg _
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem r_gt : 93 < r := by unfold r; rw [Real.lt_sqrt (by norm_num)]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem r_lt : r < 94 := by unfold r; rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `q := (86 + √8801)/180`, the positive root of `6480 q² − 6192 q − 281 = 0`.
Source: [[uea-inventory]] 029, [[uea-2-inventory]] 2-014 (mandate target 8(c), re-derived)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def q : ℝ := (86 + r) / 180
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem q_pos : 0 < q := by unfold q; linarith [r_gt]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem q_lt_one : q < 1 := by unfold q; linarith [r_lt]

/-- `q` solves the quadratic.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: mandate target 8(c)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem q_quadratic : 6480 * q ^ 2 - 6192 * q - 281 = 0 := by
  unfold q; linear_combination (1 / 5 : ℝ) * r_sq

/-- The mixed policy `σ = (q a + (1−q) b, a, a)`.
Source: mandate target 8(c)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def σ : Fin 3 → Fin 2 → ℝ :=
  ![fun a => if a = 0 then q else 1 - q, fun a => if a = 0 then 1 else 0, fun a => if a = 0 then 1 else 0]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

@[simp] theorem σ_00 : σ 0 0 = q := by simp [σ]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem σ_01 : σ 0 1 = 1 - q := by simp [σ]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem σ_10 : σ 1 0 = 1 := by simp [σ]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem σ_11 : σ 1 1 = 0 := by simp [σ]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem σ_20 : σ 2 0 = 1 := by simp [σ]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem σ_21 : σ 2 1 = 0 := by simp [σ]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem isMixed : IsMixed σ := by
  intro s
  refine ⟨fun a => ?_, ?_⟩
  · have := q_pos; have := q_lt_one
    revert s a; simp only [forall_fin_three, Fin.forall_fin_two]
    simp; constructor <;> linarith
  · revert s; simp only [forall_fin_three]
    simp [Fin.sum_univ_two]

/-! ### The six fixed-coordinate values -/

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ucoord_00 : game.Ucoord σ 0 0 = 1 := by
  rw [Game.Ucoord_fin3_0]; simp [Fin.sum_univ_two, U_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ucoord_01 : game.Ucoord σ 0 1 = 3 / 8 := by
  rw [Game.Ucoord_fin3_0]; simp [Fin.sum_univ_two, U_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ucoord_10 : game.Ucoord σ 1 0 = q + 3 / 8 * (1 - q) := by
  rw [Game.Ucoord_fin3_1]; simp [Fin.sum_univ_two, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ucoord_11 : game.Ucoord σ 1 1 = q + 3 / 8 * (1 - q) := by
  rw [Game.Ucoord_fin3_1]; simp [Fin.sum_univ_two, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ucoord_20 : game.Ucoord σ 2 0 = q + 3 / 8 * (1 - q) := by
  rw [Game.Ucoord_fin3_2]; simp [Fin.sum_univ_two, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ucoord_21 : game.Ucoord σ 2 1 = 1 / 2 + 1 / 4 * q := by
  rw [Game.Ucoord_fin3_2]; simp [Fin.sum_univ_two, U_apply]; ring

/-! ### The six extended conditionals -/

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem availMix_all (s : Fin 3) (a : Fin 2) : game.availMix σ s a := by
  unfold Game.availMix Game.denMix
  have hq := q_pos; have hq1 := q_lt_one
  revert s a; simp only [forall_fin_three, Fin.forall_fin_two]
  rw [pa_00, pa_01, pa_10, pa_11, pa_20, pa_21, δ_eq, σ_00, σ_01, σ_10, σ_11, σ_20, σ_21]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

/-- `Fext σ s₀ a = (219 + √8801)/320`: the fixed-point equation at `s₀`, `a`-side.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: mandate target 8(c)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Fext_00 : game.Fext σ 0 0 = (219 + r) / 320 := by
  rw [game.Fext_eq_of_availMix (availMix_all 0 0), Ucoord_00, pva_00]
  unfold Game.denMix; rw [pa_00, δ_eq, σ_00]
  have hd : (1 - 1 / 10) * q + 1 / 10 * (3 / 4) ≠ 0 := by have := q_pos; positivity
  rw [div_eq_iff hd]
  unfold q
  linear_combination (-1 / 64000 : ℝ) * r_sq

/-- `Fext σ s₀ b = (219 + √8801)/320`: the `b`-side; equality with the `a`-side is the quadratic.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: mandate target 8(c)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Fext_01 : game.Fext σ 0 1 = (219 + r) / 320 := by
  rw [game.Fext_eq_of_availMix (availMix_all 0 1), Ucoord_01, pva_01]
  unfold Game.denMix; rw [pa_01, δ_eq, σ_01]
  have hd : (1 - 1 / 10) * (1 - q) + 1 / 10 * (1 / 4) ≠ 0 := by
    have := q_lt_one; nlinarith
  rw [div_eq_iff hd]
  unfold q
  linear_combination (1 / 64000 : ℝ) * r_sq
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Fext_10 : game.Fext σ 1 0 = (202 + r) / 296 := by
  rw [game.Fext_eq_of_availMix (availMix_all 1 0), Ucoord_10, pva_10]
  unfold Game.denMix; rw [pa_10, δ_eq, σ_10]
  rw [div_eq_iff (by norm_num)]
  unfold q; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Fext_11 : game.Fext σ 1 1 = 17 / 24 := by
  rw [game.Fext_eq_of_availMix (availMix_all 1 1), Ucoord_11, pva_11]
  unfold Game.denMix; rw [pa_11, δ_eq, σ_11]
  norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Fext_20 : game.Fext σ 2 0 = (210 + r) / 304 := by
  rw [game.Fext_eq_of_availMix (availMix_all 2 0), Ucoord_20, pva_20]
  unfold Game.denMix; rw [pa_20, δ_eq, σ_20]
  rw [div_eq_iff (by norm_num)]
  unfold q; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Fext_21 : game.Fext σ 2 1 = 9 / 16 := by
  rw [game.Fext_eq_of_availMix (availMix_all 2 1), Ucoord_21, pva_21]
  unfold Game.denMix; rw [pa_21, δ_eq, σ_21]
  norm_num

/-- **`σ` is an extension fixed point** (hence a Herrmann one).
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: mandate target 8(c); [[updateless-self-game]] §6 ("An exploratory float scan finds a mixed fixed point")
Kind: N+
Fidelity: exact (the float scan's `≈ (0.999, 0.001)` made exact)
Hyps: (a) -/
theorem isFPext : game.IsFPext σ := by
  refine ⟨isMixed, ?_⟩
  have hr := r_gt
  simp only [forall_fin_three, Fin.forall_fin_two]
  refine ⟨⟨fun _ => ?_, fun _ => ?_⟩, ⟨fun _ => ?_, fun h => ?_⟩, ⟨fun _ => ?_, fun h => ?_⟩⟩
  · rw [Fext_00, Fext_01]; exact ⟨le_rfl, le_rfl⟩
  · rw [Fext_00, Fext_01]; exact ⟨le_rfl, le_rfl⟩
  · rw [Fext_10, Fext_11]; constructor
    · exact le_rfl
    · rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
  · rw [σ_11] at h; exact absurd h (lt_irrefl 0)
  · rw [Fext_20, Fext_21]; constructor
    · exact le_rfl
    · rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
  · rw [σ_21] at h; exact absurd h (lt_irrefl 0)

/-- **The trust bound holds at every situation** (all three maxima exceed `9/10`).
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: mandate target 8(c)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem TBext_all (s : Fin 3) : game.TBext σ s := by
  have hr := r_gt
  unfold Game.TBext
  revert s; simp only [forall_fin_three]
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩
  · rw [thr_eq, Fext_00, le_div_iff₀ (by norm_num)]; linarith
  · rw [thr_eq, Fext_10, le_div_iff₀ (by norm_num)]; linarith
  · rw [thr_eq, Fext_20, le_div_iff₀ (by norm_num)]; linarith

/-- `U(σ) = (194 + √8801)/288`.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: mandate target 8(c)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Umix_eq : game.Umix σ = (194 + r) / 288 := by
  rw [Game.Umix_fin3]; simp [Fin.sum_univ_two, U_apply]; unfold q; ring

/-- `U(σ) ≥ 8/9 = U* − δ/(1−δ)`: Theorem C′'s bound, checked on the witness.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: mandate target 8(c)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem theoremC'_bound_holds : game.Ustar - game.δ / (1 - game.δ) ≤ game.Umix σ := by
  rw [Umix_eq, Ustar_eq, δ_eq]
  have := r_gt
  rw [le_div_iff₀ (by norm_num)]; norm_num; linarith

/-- **The §6 instance has an exact mixed fixed point** with the trust bound everywhere and value within
Theorem C′'s bound — the N+ witness for `exists_isFPext` and `theoremC'_ext`, on an instance with no pure
fixed point (`Section6.no_pure_fp`).
Scope: finite updateless self-game — continuous extension; not rOSI, not the sequential model.
Source: [[updateless-self-game]] §6; [[uea-inventory]] 029; [[uea-2-inventory]] 2-014
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem witness :
    game.IsFPext σ ∧ game.IsFPherr σ ∧ (∀ s, game.TBext σ s) ∧ (∀ π, ¬ game.IsPureFP π) ∧
      game.Ustar - game.δ / (1 - game.δ) ≤ game.Umix σ :=
  ⟨isFPext, isFPext.isFPherr, TBext_all, Section6.no_pure_fp, theoremC'_bound_holds⟩

end Witness8801

end Cleanroom.Uea.UeaSelfGame
