import Cleanroom.Uea.UeaSelfGame.Repaired
import Cleanroom.Uea.UeaSelfGame.Tables
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Stag Hunt in the self-game: both pure fixed points at every `δ`; the trust bound rejects `HH` iff
`δ < (15 − √97)/16`

`S = A = Fin 2` (`S`tag `= 0`, `H`are `= 1`), `U(SS) = 1`, `U(HH) = 3/4`, `U(SH) = U(HS) = 3/8`,
`Po = ½ δ_{SH} + ½ δ_{HS}`, `piStar = SS`. For every `δ ∈ (0,1)`: `SS` and `HH` are pure fixed points
(`SH` too, via ties, `stretch`); the trust bound holds at `SS` everywhere; at `HH` it holds iff
`8δ² − 15δ + 4 ≤ 0` iff `(15 − √97)/16 ≤ δ` (the other root `(15 + √97)/16 > 1`). The founding sketch's
threshold "`TB` violated iff `1 − δ > c/b`" (`δ < 1/4`) drops the `Po` term in the conditional and is
wrong; the exact root is a named algebraic number. Above the threshold Theorem C's bound
`U* − δ/(1−δ) ≤ 1/2 ≤ 3/4 = U(HH)` is true and uninformative (N−).

Scope: finite updateless self-game — pointwise EDT conditional on one's own action, self-consistent
belief; not rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

namespace StagHunt

variable {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1)

/-- The Stag Hunt instance.
Source: [[updateless-self-game]] §5.1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def game : Game (Fin 2) (Fin 2) where
  U := tab2 1 (3 / 8) (3 / 8) (3 / 4)
  U_nonneg := fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) π).1
  U_le_one := fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) π).2
  piStar := ![0, 0]
  piStar_max := fun π => by
    rw [tab2_00]
    exact (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  Po := tab2 0 (1 / 2) (1 / 2) 0
  Po_mem := ⟨fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) π).1, by rw [sum_tab2]; norm_num⟩
  δ := δ
  δ_nonneg := h0.le
  δ_lt_one := h1

/-- `SS`.
Source: none: infrastructure (instance datum)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def SS : Fin 2 → Fin 2 := ![0, 0]
/-- `HH`.
Source: none: infrastructure (instance datum)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def HH : Fin 2 → Fin 2 := ![1, 1]
/-- `SH`.
Source: none: infrastructure (instance datum)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def SH : Fin 2 → Fin 2 := ![0, 1]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

@[simp] theorem SS_0 : SS 0 = 0 := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem SS_1 : SS 1 = 0 := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem HH_0 : HH 0 = 1 := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem HH_1 : HH 1 = 1 := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem SH_0 : SH 0 = 0 := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem SH_1 : SH 1 = 1 := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem U_apply (π) : (game h0 h1).U π = tab2 1 (3 / 8) (3 / 8) (3 / 4) π := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem δ_eq : (game h0 h1).δ = δ := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ustar_eq : (game h0 h1).Ustar = 1 := by simp [Game.Ustar, game]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem thr_eq : (game h0 h1).thr = 1 - δ := by simp [Game.thr, Ustar_eq, δ_eq]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem mu_apply (π π') : (game h0 h1).muSelf π π' =
    (1 - δ) * (if π' 0 = π 0 ∧ π' 1 = π 1 then 1 else 0) + δ * tab2 0 (1 / 2) (1 / 2) 0 π' := by
  rw [Game.muSelf_apply_fin2]; rfl

/-! ### `SS` -/

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SS_condDen_00 : condDen ((game h0 h1).muSelf SS) 0 0 = 1 - δ / 2 := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SS_condNum_00 : (game h0 h1).condNum ((game h0 h1).muSelf SS) 0 0 = 1 - 13 / 16 * δ := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SS_condDen_01 : condDen ((game h0 h1).muSelf SS) 0 1 = δ / 2 := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SS_condNum_01 : (game h0 h1).condNum ((game h0 h1).muSelf SS) 0 1 = δ / 2 * (3 / 8) := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SS_condDen_10 : condDen ((game h0 h1).muSelf SS) 1 0 = 1 - δ / 2 := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SS_condNum_10 : (game h0 h1).condNum ((game h0 h1).muSelf SS) 1 0 = 1 - 13 / 16 * δ := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SS_condDen_11 : condDen ((game h0 h1).muSelf SS) 1 1 = δ / 2 := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SS_condNum_11 : (game h0 h1).condNum ((game h0 h1).muSelf SS) 1 1 = δ / 2 * (3 / 8) := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem SS_cond_00 : (game h0 h1).cond ((game h0 h1).muSelf SS) 0 0 = (1 - 13 / 16 * δ) / (1 - δ / 2) := by
  unfold Game.cond; rw [SS_condNum_00, SS_condDen_00]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SS_cond_01 : (game h0 h1).cond ((game h0 h1).muSelf SS) 0 1 = 3 / 8 := by
  unfold Game.cond; rw [SS_condNum_01, SS_condDen_01]; have : δ / 2 ≠ 0 := by positivity
  field_simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SS_cond_10 : (game h0 h1).cond ((game h0 h1).muSelf SS) 1 0 = (1 - 13 / 16 * δ) / (1 - δ / 2) := by
  unfold Game.cond; rw [SS_condNum_10, SS_condDen_10]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SS_cond_11 : (game h0 h1).cond ((game h0 h1).muSelf SS) 1 1 = 3 / 8 := by
  unfold Game.cond; rw [SS_condNum_11, SS_condDen_11]; have : δ / 2 ≠ 0 := by positivity
  field_simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem SS_avail_all : ∀ s a : Fin 2, avail ((game h0 h1).muSelf SS) s a := by
  unfold avail; simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [SS_condDen_00]; linarith
  · rw [SS_condDen_01]; positivity
  · rw [SS_condDen_10]; linarith
  · rw [SS_condDen_11]; positivity

/-- `cond(S) ≥ 3/8 = cond(H)` under `μ_{SS}` (strictly, for `δ < 1`).
Source: [[updateless-self-game]] §5.1
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SS_S_ge_H (h1 : δ < 1) : (3 / 8 : ℝ) ≤ (1 - 13 / 16 * δ) / (1 - δ / 2) := by
  rw [le_div_iff₀ (by linarith)]; linarith

/-- **`SS` is a pure fixed point for every `δ ∈ (0,1)`**.
Source: [[updateless-self-game]] §5.1 ("Both `SS` and `HH` are pure fixed points for every `δ`")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem SS_isPureFP : (game h0 h1).IsPureFP SS := by
  unfold Game.IsPureFP Game.IsArgmaxH
  simp only [Fin.forall_fin_two, SS_0, SS_1]
  refine ⟨⟨SS_avail_all h0 h1 0 0, fun _ => le_rfl, fun _ => ?_⟩,
    ⟨SS_avail_all h0 h1 1 0, fun _ => le_rfl, fun _ => ?_⟩⟩
  · rw [SS_cond_00, SS_cond_01]; exact SS_S_ge_H h1
  · rw [SS_cond_10, SS_cond_11]; exact SS_S_ge_H h1

/-- **The trust bound holds at `SS` at every situation for every `δ`** (`cond(S) ≥ 1 − δ`).
Source: [[updateless-self-game]] §5.1 ("`SS` satisfies the trust bound for every `δ`")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem SS_TB_all : ∀ s, (game h0 h1).TB ((game h0 h1).muSelf SS) s := by
  simp only [Fin.forall_fin_two]
  have key : 1 - δ ≤ (1 - 13 / 16 * δ) / (1 - δ / 2) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  exact ⟨⟨0, SS_avail_all h0 h1 0 0, by rw [thr_eq, SS_cond_00]; exact key⟩,
    ⟨0, SS_avail_all h0 h1 1 0, by rw [thr_eq, SS_cond_10]; exact key⟩⟩

/-! ### `HH` -/

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HH_condDen_00 : condDen ((game h0 h1).muSelf HH) 0 0 = δ / 2 := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HH_condNum_00 : (game h0 h1).condNum ((game h0 h1).muSelf HH) 0 0 = δ / 2 * (3 / 8) := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HH_condDen_01 : condDen ((game h0 h1).muSelf HH) 0 1 = 1 - δ / 2 := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HH_condNum_01 : (game h0 h1).condNum ((game h0 h1).muSelf HH) 0 1 = 3 / 4 - 9 / 16 * δ := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HH_condDen_10 : condDen ((game h0 h1).muSelf HH) 1 0 = δ / 2 := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HH_condNum_10 : (game h0 h1).condNum ((game h0 h1).muSelf HH) 1 0 = δ / 2 * (3 / 8) := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HH_condDen_11 : condDen ((game h0 h1).muSelf HH) 1 1 = 1 - δ / 2 := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HH_condNum_11 : (game h0 h1).condNum ((game h0 h1).muSelf HH) 1 1 = 3 / 4 - 9 / 16 * δ := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem HH_cond_00 : (game h0 h1).cond ((game h0 h1).muSelf HH) 0 0 = 3 / 8 := by
  unfold Game.cond; rw [HH_condNum_00, HH_condDen_00]; have : δ / 2 ≠ 0 := by positivity
  field_simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HH_cond_01 : (game h0 h1).cond ((game h0 h1).muSelf HH) 0 1 = (3 / 4 - 9 / 16 * δ) / (1 - δ / 2) := by
  unfold Game.cond; rw [HH_condNum_01, HH_condDen_01]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HH_cond_10 : (game h0 h1).cond ((game h0 h1).muSelf HH) 1 0 = 3 / 8 := by
  unfold Game.cond; rw [HH_condNum_10, HH_condDen_10]; have : δ / 2 ≠ 0 := by positivity
  field_simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HH_cond_11 : (game h0 h1).cond ((game h0 h1).muSelf HH) 1 1 = (3 / 4 - 9 / 16 * δ) / (1 - δ / 2) := by
  unfold Game.cond; rw [HH_condNum_11, HH_condDen_11]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem HH_avail_all : ∀ s a : Fin 2, avail ((game h0 h1).muSelf HH) s a := by
  unfold avail; simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [HH_condDen_00]; positivity
  · rw [HH_condDen_01]; linarith
  · rw [HH_condDen_10]; positivity
  · rw [HH_condDen_11]; linarith
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem HH_H_ge_S (h1 : δ < 1) : (3 / 8 : ℝ) ≤ (3 / 4 - 9 / 16 * δ) / (1 - δ / 2) := by
  rw [le_div_iff₀ (by linarith)]; linarith

/-- **`HH` is a pure fixed point for every `δ ∈ (0,1)`** (the trap: playing `H` is evidence of being the
`HH`-self).
Source: [[updateless-self-game]] §5.1
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem HH_isPureFP : (game h0 h1).IsPureFP HH := by
  unfold Game.IsPureFP Game.IsArgmaxH
  simp only [Fin.forall_fin_two, HH_0, HH_1]
  refine ⟨⟨HH_avail_all h0 h1 0 1, fun _ => ?_, fun _ => le_rfl⟩,
    ⟨HH_avail_all h0 h1 1 1, fun _ => ?_, fun _ => le_rfl⟩⟩
  · rw [HH_cond_00, HH_cond_01]; exact HH_H_ge_S h1
  · rw [HH_cond_10, HH_cond_11]; exact HH_H_ge_S h1

/-- **The trust bound at `HH` holds iff `8δ² − 15δ + 4 ≤ 0`** (at either situation): the conditional of
`H` is `((1−δ)·3/4 + (δ/2)·3/8)/(1−δ/2)`, compared with `(1−δ)·1`. The `S` conditional `3/8 < 1 − δ`
never meets the threshold on `(0, 5/8)`, and is irrelevant above.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5.1 ("`HH` violates it iff … `8δ² − 15δ + 4 > 0`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem HH_TB_iff (s : Fin 2) : (game h0 h1).TB ((game h0 h1).muSelf HH) s ↔ 8 * δ ^ 2 - 15 * δ + 4 ≤ 0 := by
  have key : 1 - δ ≤ (3 / 4 - 9 / 16 * δ) / (1 - δ / 2) ↔ 8 * δ ^ 2 - 15 * δ + 4 ≤ 0 := by
    rw [le_div_iff₀ (by linarith)]; constructor <;> intro h <;> nlinarith
  have hS : (1 - δ ≤ 3 / 8) → 8 * δ ^ 2 - 15 * δ + 4 ≤ 0 := by
    intro h; nlinarith
  unfold Game.TB; rw [thr_eq]
  simp only [Fin.exists_fin_two]
  revert s; simp only [Fin.forall_fin_two]
  constructor
  · rw [HH_cond_00, HH_cond_01]
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩)
      · exact hS h
      · exact key.1 h
    · intro h; exact Or.inr ⟨HH_avail_all h0 h1 0 1, key.2 h⟩
  · rw [HH_cond_10, HH_cond_11]
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩)
      · exact hS h
      · exact key.1 h
    · intro h; exact Or.inr ⟨HH_avail_all h0 h1 1 1, key.2 h⟩

/-- The exact threshold `(15 − √97)/16`.
Source: [[updateless-self-game]] §5.1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def threshold : ℝ := (15 - Real.sqrt 97) / 16

/-- **`8δ² − 15δ + 4 ≤ 0 ↔ (15 − √97)/16 ≤ δ` on `(0,1)`** (the other root `(15 + √97)/16 > 1`).
Source: [[updateless-self-game]] §5.1 ("iff `δ < (15−√97)/16 ≈ 0.322`")
Kind: P
Fidelity: exact (named algebraic root, no decimal bracket)
Hyps: (a) -/
theorem quad_iff_threshold (h1 : δ < 1) : 8 * δ ^ 2 - 15 * δ + 4 ≤ 0 ↔ threshold ≤ δ := by
  unfold threshold
  have hs : Real.sqrt 97 ^ 2 = 97 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 97 := Real.sqrt_nonneg 97
  have hs1 : 1 < Real.sqrt 97 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  -- `8δ² − 15δ + 4 = 8 (δ − r₁)(δ − r₂)` with `r₂ = (15 + √97)/16 > 1 > δ`
  have hfac : 8 * δ ^ 2 - 15 * δ + 4 =
      8 * (δ - (15 - Real.sqrt 97) / 16) * (δ - (15 + Real.sqrt 97) / 16) := by
    ring_nf; rw [hs]; ring
  have hr2 : δ - (15 + Real.sqrt 97) / 16 < 0 := by linarith
  rw [hfac]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have : 0 < 8 * (δ - (15 - Real.sqrt 97) / 16) * (δ - (15 + Real.sqrt 97) / 16) := by
      have h1' : δ - (15 - Real.sqrt 97) / 16 < 0 := by linarith
      nlinarith
    linarith
  · intro h
    have h1' : 0 ≤ δ - (15 - Real.sqrt 97) / 16 := by linarith
    nlinarith

/-- **The trust bound rejects `HH` iff `δ < (15 − √97)/16`** — the exact, `Po`-dependent threshold.
Refutes [[00-founding-sketches]] §3's *"violates TB iff `1 − δ > c/b`"* (`δ < 1/4`), which drops the `Po`
term; the surviving neighbour is this root. The earlier lab's Prop 2 threshold `(1−δ) b ≥ c` is the C1
(interventional) threshold, a different model (findings).
Scope: finite updateless self-game — self-consistent belief; not rOSI, not the sequential model.
Source: [[updateless-self-game]] §5.1; [[uea-inventory]] 028; trust-lab 033, 2-011
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem HH_TB_iff_threshold (s : Fin 2) :
    (game h0 h1).TB ((game h0 h1).muSelf HH) s ↔ threshold ≤ δ :=
  (HH_TB_iff h0 h1 s).trans (quad_iff_threshold h1)

/-- The threshold lies in `(0, 1)` — so both regimes occur (`δ = 3/10` rejects, `δ = 1/2` accepts).
Source: [[updateless-self-game]] §5.1 (`≈ 0.322`)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem threshold_mem : 0 < threshold ∧ threshold < 1 := by
  unfold threshold
  have hs : Real.sqrt 97 ^ 2 = 97 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 97 := Real.sqrt_nonneg 97
  have h15 : Real.sqrt 97 < 15 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h9 : 9 < Real.sqrt 97 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  constructor <;> linarith

/-- At `δ = 3/10` the trust bound fails at `HH` (`93/136 < 7/10`), at `δ = 1/2` it holds: the selection is
real in both directions.
Source: [[updateless-self-game]] §5.1 (mandate's `δ = 3/10` check); §7 ("`{SS}` for `δ ≤ 0.3`, `{SS, HH}` at `δ = 1/2`")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem HH_TB_examples :
    (¬ (game (δ := 3 / 10) (by norm_num) (by norm_num)).TB
        ((game (δ := 3 / 10) (by norm_num) (by norm_num)).muSelf HH) 0) ∧
    (game (δ := 1 / 2) (by norm_num) (by norm_num)).TB
        ((game (δ := 1 / 2) (by norm_num) (by norm_num)).muSelf HH) 0 := by
  constructor
  · rw [HH_TB_iff]; norm_num
  · rw [HH_TB_iff]; norm_num

/-- Above the threshold, Theorem C's bound at `HH` is satisfied by the trap: `U* − δ/(1−δ) ≤ 3/4 = U(HH)`
(indeed `δ > 3/10` there, so `δ/(1−δ) > 3/7`). N−: the theorem is true exactly where it says nothing. The
note's sharper "`≤ 1/2`" holds only for `δ ≥ 1/3`, slightly above the threshold `≈ 0.322` (findings).
Source: [[updateless-self-game]] §5.1 ("the theorem is true and uninformative, as it should be")
Kind: N-
Fidelity: variant: `≤ U(HH)` for every `δ` above the threshold; the note's `≤ 1/2` only from `δ ≥ 1/3`
Hyps: (a) -/
theorem HH_theoremC_uninformative (hthr : threshold ≤ δ) :
    (game h0 h1).Ustar - δ / (1 - δ) ≤ (game h0 h1).U HH ∧
      (1 / 3 ≤ δ → (game h0 h1).Ustar - δ / (1 - δ) ≤ 1 / 2) := by
  have hq := (quad_iff_threshold h1).2 hthr
  have hδ : 3 / 10 < δ := by nlinarith [sq_nonneg (δ - 3 / 10)]
  rw [Ustar_eq, U_apply]
  constructor
  · have : 1 / 4 ≤ δ / (1 - δ) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    simp only [HH, tab2_11]
    linarith
  · intro h13
    have : 1 / 2 ≤ δ / (1 - δ) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    linarith

/-! ### `SH` (stretch): a fixed point via ties -/

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SH_condDen_00 : condDen ((game h0 h1).muSelf SH) 0 0 = 1 - δ / 2 := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SH_condNum_00 : (game h0 h1).condNum ((game h0 h1).muSelf SH) 0 0 = (1 - δ / 2) * (3 / 8) := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SH_condDen_01 : condDen ((game h0 h1).muSelf SH) 0 1 = δ / 2 := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SH_condNum_01 : (game h0 h1).condNum ((game h0 h1).muSelf SH) 0 1 = δ / 2 * (3 / 8) := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SH_condDen_10 : condDen ((game h0 h1).muSelf SH) 1 0 = δ / 2 := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SH_condNum_10 : (game h0 h1).condNum ((game h0 h1).muSelf SH) 1 0 = δ / 2 * (3 / 8) := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SH_condDen_11 : condDen ((game h0 h1).muSelf SH) 1 1 = 1 - δ / 2 := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SH_condNum_11 : (game h0 h1).condNum ((game h0 h1).muSelf SH) 1 1 = (1 - δ / 2) * (3 / 8) := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem SH_cond_all : ∀ s a : Fin 2, (game h0 h1).cond ((game h0 h1).muSelf SH) s a = 3 / 8 := by
  have h2 : 1 - δ / 2 ≠ 0 := by linarith
  have h3 : δ / 2 ≠ 0 := by positivity
  have h4 : (2 : ℝ) - δ ≠ 0 := by linarith
  simp only [Fin.forall_fin_two]
  unfold Game.cond
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [SH_condNum_00, SH_condDen_00]; field_simp
  · rw [SH_condNum_01, SH_condDen_01]; field_simp
  · rw [SH_condNum_10, SH_condDen_10]; field_simp
  · rw [SH_condNum_11, SH_condDen_11]; field_simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem SH_avail_all : ∀ s a : Fin 2, avail ((game h0 h1).muSelf SH) s a := by
  unfold avail; simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [SH_condDen_00]; linarith
  · rw [SH_condDen_01]; positivity
  · rw [SH_condDen_10]; positivity
  · rw [SH_condDen_11]; linarith

/-- **`SH` is a pure fixed point via ties** (every conditional equals `3/8`), for every `δ`; `HS` is
symmetric.
Source: [[updateless-self-game]] §5.1 ("so are the miscoordinated `SH`, `HS`, via ties")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem SH_isPureFP : (game h0 h1).IsPureFP SH := by
  intro s
  refine ⟨SH_avail_all h0 h1 s (SH s), fun b _ => ?_⟩
  rw [SH_cond_all h0 h1 s b, SH_cond_all h0 h1 s (SH s)]

end StagHunt

end Cleanroom.Uea.UeaSelfGame
