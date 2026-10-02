import Cleanroom.Uea.UeaSelfGame.Repaired
import Cleanroom.Uea.UeaSelfGame.Tables

/-!
# Tightness of Theorem C: T1 and T2 exact at every `δ`; the §5.5 conjecture refuted by `T3`

* **T1** (note §5.5), symbolic `δ ∈ (0,1)`: `S = A = Fin 2`, `π = ab`, `Po = (1−θ) δ_{aa} + θ δ_{ba}`,
  `U(aa) = 1`, `U(ab) = 1−θ`, `U(ba) = U(bb) = 0`, `θ = δ/(1−δ+δ²)`. A pure fixed point (tie at `s₁`),
  the trust bound at `s₀` with equality (`cond = 1−δ`), the trust bound failing at `s₁`, gap `θ`.
* **T2** (note §5.5), symbolic `δ ∈ (0,1)`: `S = Fin 3`, `π = aba`, `Po = (1−δ) δ_{aaa} + δ δ_{aab}`,
  `U(aaa) = 1`, `U(aab) = 0`, `U(aba) = 1−δ`, else `0`. A pure fixed point (tie at `s₁`; `b` unavailable at
  `s₀`), the trust bound everywhere, gap exactly `δ`.
* **T3** refutation (computed by `updateless_existence.py` §(6), never written up): at `δ = 1/10`, `S = Fin 3`,
  `π = aaa` with `U = 1−g`, deviations `aba`, `aab` with `U = 1` and `Po = 9/20` each, polluter `bbb` with
  `U = 0`, `Po = 1/10`: `g = 11/100` is a pure fixed point with the trust bound at `s₀` and gap
  `11/100 > 10/91 = δ/(1−δ+δ²)`; `g = 21/200` is a pure fixed point with the trust bound at all three
  situations and gap `21/200 > 1/10 = δ`. So the note's *"Conjecture: sup gap = δ/(1−δ+δ²) with the trust
  bound at one situation and = δ with it at all situations"* is false on both counts (the note's own
  definitions; no ambiguity). Surviving neighbour: Theorem C's `δ/(1−δ)` (`Repaired.lean`).

Scope: finite updateless self-game — pointwise EDT conditional on one's own action, self-consistent
belief; not rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

/-! ### T1 -/

namespace T1

/-- `θ(δ) := δ/(1−δ+δ²)`, T1's gap and `Po`-weight of the polluter `ba`.
Source: [[updateless-self-game]] §5.5 (T1)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def θ (δ : ℝ) : ℝ := δ / (1 - δ + δ ^ 2)

variable {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1)
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem den_pos (_h0 : 0 < δ) (h1 : δ < 1) : 0 < 1 - δ + δ ^ 2 := by nlinarith
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem θ_mul (h0 : 0 < δ) (h1 : δ < 1) : θ δ * (1 - δ + δ ^ 2) = δ := div_mul_cancel₀ _ (ne_of_gt (den_pos h0 h1))
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem θ_pos (h0 : 0 < δ) (h1 : δ < 1) : 0 < θ δ := div_pos h0 (den_pos h0 h1)
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem θ_lt_one (h0 : 0 < δ) (h1 : δ < 1) : θ δ < 1 := by
  unfold θ; rw [div_lt_one (den_pos h0 h1)]; nlinarith

/-- `θ > δ`: the gap exceeds `δ` (so the trust bound at `s₁` fails).
Source: [[updateless-self-game]] §5.5 ("`g > δ`")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem δ_lt_θ (h0 : 0 < δ) (h1 : δ < 1) : δ < θ δ := by
  unfold θ; rw [lt_div_iff₀ (den_pos h0 h1)]
  have := mul_pos (mul_pos h0 h0) (sub_pos.2 h1)
  nlinarith

/-- The T1 instance: `U = (aa:1, ab:1−θ, ba:0, bb:0)`, `piStar = aa`, `Po = (aa:1−θ, ba:θ)`.
Source: [[updateless-self-game]] §5.5 (T1)
Kind: D
Fidelity: exact (with `g = θ`)
Hyps: n/a -/
noncomputable def game : Game (Fin 2) (Fin 2) where
  U := tab2 1 (1 - θ δ) 0 0
  U_nonneg := fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num)
    ⟨by linarith [θ_lt_one h0 h1], by linarith [θ_pos h0 h1]⟩ (by norm_num) (by norm_num) π).1
  U_le_one := fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num)
    ⟨by linarith [θ_lt_one h0 h1], by linarith [θ_pos h0 h1]⟩ (by norm_num) (by norm_num) π).2
  piStar := ![0, 0]
  piStar_max := fun π => by
    rw [tab2_00]
    exact (tab2_bounds (lo := 0) (hi := 1) (by norm_num)
      ⟨by linarith [θ_lt_one h0 h1], by linarith [θ_pos h0 h1]⟩ (by norm_num) (by norm_num) π).2
  Po := tab2 (1 - θ δ) 0 (θ δ) 0
  Po_mem := ⟨fun π => (tab2_bounds (lo := 0) (hi := 1)
      ⟨by linarith [θ_lt_one h0 h1], by linarith [θ_pos h0 h1]⟩ (by norm_num)
      ⟨by linarith [θ_pos h0 h1], by linarith [θ_lt_one h0 h1]⟩ (by norm_num) π).1,
    by rw [sum_tab2]; ring⟩
  δ := δ
  δ_nonneg := h0.le
  δ_lt_one := h1

/-- The own policy `π = ab`.
Source: none: infrastructure (instance datum)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pol : Fin 2 → Fin 2 := ![0, 1]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

@[simp] theorem pol_0 : pol 0 = 0 := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem pol_1 : pol 1 = 1 := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem U_apply (π) : (game h0 h1).U π = tab2 1 (1 - θ δ) 0 0 π := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Po_apply (π) : (game h0 h1).Po π = tab2 (1 - θ δ) 0 (θ δ) 0 π := rfl
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

theorem mu_apply (π') : (game h0 h1).muSelf pol π' =
    (1 - δ) * (if π' 0 = 0 ∧ π' 1 = 1 then 1 else 0) + δ * tab2 (1 - θ δ) 0 (θ δ) 0 π' := by
  rw [Game.muSelf_apply_fin2]; rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_00 : condDen ((game h0 h1).muSelf pol) 0 0 = 1 - δ * θ δ := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_00 : (game h0 h1).condNum ((game h0 h1).muSelf pol) 0 0 = 1 - θ δ := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_01 : condDen ((game h0 h1).muSelf pol) 0 1 = δ * θ δ := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_01 : (game h0 h1).condNum ((game h0 h1).muSelf pol) 0 1 = 0 := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_10 : condDen ((game h0 h1).muSelf pol) 1 0 = δ := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_10 : (game h0 h1).condNum ((game h0 h1).muSelf pol) 1 0 = δ * (1 - θ δ) := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_11 : condDen ((game h0 h1).muSelf pol) 1 1 = 1 - δ := by
  rw [Game.condDen_fin2]; simp [Fin.sum_univ_two, mu_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_11 : (game h0 h1).condNum ((game h0 h1).muSelf pol) 1 1 = (1 - δ) * (1 - θ δ) := by
  rw [Game.condNum_fin2]; simp [Fin.sum_univ_two, mu_apply, U_apply]

/-- `cond(s₀, a) = (1−θ)/(1−δθ) = 1 − δ`: the trust bound at `s₀` holds with equality.
Source: [[updateless-self-game]] §5.5 (T1, "`TB_{s₀}` holds with equality")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem cond_00 : (game h0 h1).cond ((game h0 h1).muSelf pol) 0 0 = 1 - δ := by
  unfold Game.cond; rw [condNum_00, condDen_00]
  have hθ := θ_mul h0 h1
  have hd : 0 < 1 - δ * θ δ := by nlinarith [θ_lt_one h0 h1]
  rw [div_eq_iff (ne_of_gt hd)]
  linear_combination (-1 : ℝ) * hθ
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_01 : (game h0 h1).cond ((game h0 h1).muSelf pol) 0 1 = 0 := by
  unfold Game.cond; rw [condNum_01, zero_div]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_10 : (game h0 h1).cond ((game h0 h1).muSelf pol) 1 0 = 1 - θ δ := by
  unfold Game.cond; rw [condNum_10, condDen_10]; field_simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_11 : (game h0 h1).cond ((game h0 h1).muSelf pol) 1 1 = 1 - θ δ := by
  unfold Game.cond; rw [condNum_11, condDen_11]
  have : 1 - δ ≠ 0 := by linarith
  field_simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem avail_all : ∀ s a : Fin 2, avail ((game h0 h1).muSelf pol) s a := by
  unfold avail; simp only [Fin.forall_fin_two]
  have := θ_pos h0 h1; have := θ_lt_one h0 h1
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [condDen_00]; nlinarith
  · rw [condDen_01]; positivity
  · rw [condDen_10]; exact h0
  · rw [condDen_11]; linarith

/-- **T1 is a pure fixed point** (strict at `s₀`, a tie at `s₁`).
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5.5 (T1)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem isPureFP : (game h0 h1).IsPureFP pol := by
  unfold Game.IsPureFP Game.IsArgmaxH
  simp only [Fin.forall_fin_two, pol_0, pol_1]
  have := θ_pos h0 h1
  refine ⟨⟨avail_all h0 h1 0 0, fun _ => le_rfl, fun _ => ?_⟩,
    ⟨avail_all h0 h1 1 1, fun _ => ?_, fun _ => le_rfl⟩⟩
  · rw [cond_00, cond_01]; linarith
  · rw [cond_10, cond_11]

/-- **The trust bound at `s₀`**, with equality.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5.5 (T1)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem TB_0 : (game h0 h1).TB ((game h0 h1).muSelf pol) 0 :=
  ⟨0, avail_all h0 h1 0 0, by rw [thr_eq, cond_00]⟩

/-- **The trust bound fails at `s₁`** for every `δ ∈ (0,1)`: both conditionals equal `1−θ < 1−δ`.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5.5 (T1, "`TB_{s₁}` fails for every `δ`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem not_TB_1 : ¬ (game h0 h1).TB ((game h0 h1).muSelf pol) 1 := by
  rintro ⟨a, _, ha⟩
  rw [thr_eq] at ha
  have hlt := δ_lt_θ h0 h1
  revert ha; revert a
  simp only [Fin.forall_fin_two]
  constructor
  · rw [cond_10]; intro _ h; linarith
  · rw [cond_11]; intro _ h; linarith

/-- The gap is exactly `θ = δ/(1−δ+δ²)`.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5.5 (T1, "Gap `δ/(1−δ+δ²)`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem gap : (game h0 h1).Ustar - (game h0 h1).U pol = θ δ := by
  rw [Ustar_eq, U_apply]; simp [pol]

end T1

/-! ### T2 -/

namespace T2

variable {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1)

/-- The T2 instance: `U(aaa) = 1`, `U(aab) = 0`, `U(aba) = 1−δ`, else `0`; `piStar = aaa`;
`Po = (1−δ) δ_{aaa} + δ δ_{aab}`.
Source: [[updateless-self-game]] §5.5 (T2)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def game : Game (Fin 3) (Fin 2) where
  U := tab3 1 0 (1 - δ) 0 0 0 0 0
  U_nonneg := fun π => (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    ⟨by linarith, by linarith⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).1
  U_le_one := fun π => (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    ⟨by linarith, by linarith⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  piStar := ![0, 0, 0]
  piStar_max := fun π => by
    rw [tab3_000]
    exact (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num)
      ⟨by linarith, by linarith⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  Po := tab3 (1 - δ) δ 0 0 0 0 0 0
  Po_mem := ⟨fun π => (tab3_bounds (lo := 0) (hi := 1) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).1,
    by rw [sum_tab3]; ring⟩
  δ := δ
  δ_nonneg := h0.le
  δ_lt_one := h1

/-- The own policy `π = aba`.
Source: none: infrastructure (instance datum)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pol : Fin 3 → Fin 2 := ![0, 1, 0]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

@[simp] theorem pol_0 : pol 0 = 0 := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem pol_1 : pol 1 = 1 := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem pol_2 : pol 2 = 0 := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem U_apply (π) : (game h0 h1).U π = tab3 1 0 (1 - δ) 0 0 0 0 0 π := rfl
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

theorem mu_apply (π') : (game h0 h1).muSelf pol π' =
    (1 - δ) * (if π' 0 = 0 ∧ π' 1 = 1 ∧ π' 2 = 0 then 1 else 0) + δ * tab3 (1 - δ) δ 0 0 0 0 0 0 π' := by
  rw [Game.muSelf_apply_fin3]; rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_00 : condDen ((game h0 h1).muSelf pol) 0 0 = 1 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_00 : (game h0 h1).condNum ((game h0 h1).muSelf pol) 0 0 = 1 - δ := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_01 : condDen ((game h0 h1).muSelf pol) 0 1 = 0 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_10 : condDen ((game h0 h1).muSelf pol) 1 0 = δ := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_10 : (game h0 h1).condNum ((game h0 h1).muSelf pol) 1 0 = δ * (1 - δ) := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_11 : condDen ((game h0 h1).muSelf pol) 1 1 = 1 - δ := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_11 : (game h0 h1).condNum ((game h0 h1).muSelf pol) 1 1 = (1 - δ) * (1 - δ) := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_20 : condDen ((game h0 h1).muSelf pol) 2 0 = (1 - δ) * (1 + δ) := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_20 : (game h0 h1).condNum ((game h0 h1).muSelf pol) 2 0 = 1 - δ := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_21 : condDen ((game h0 h1).muSelf pol) 2 1 = δ * δ := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_21 : (game h0 h1).condNum ((game h0 h1).muSelf pol) 2 1 = 0 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_00 : (game h0 h1).cond ((game h0 h1).muSelf pol) 0 0 = 1 - δ := by
  unfold Game.cond; rw [condNum_00, condDen_00, div_one]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_10 : (game h0 h1).cond ((game h0 h1).muSelf pol) 1 0 = 1 - δ := by
  unfold Game.cond; rw [condNum_10, condDen_10]; field_simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_11 : (game h0 h1).cond ((game h0 h1).muSelf pol) 1 1 = 1 - δ := by
  unfold Game.cond; rw [condNum_11, condDen_11]
  have : 1 - δ ≠ 0 := by linarith
  field_simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_20 : (game h0 h1).cond ((game h0 h1).muSelf pol) 2 0 = 1 / (1 + δ) := by
  unfold Game.cond; rw [condNum_20, condDen_20]
  have : 1 - δ ≠ 0 := by linarith
  have : 1 + δ ≠ 0 := by linarith
  field_simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_21 : (game h0 h1).cond ((game h0 h1).muSelf pol) 2 1 = 0 := by
  unfold Game.cond; rw [condNum_21, zero_div]

/-- `b` is unavailable at `s₀` (no belief mass plays `b` there) — said explicitly, as the mandate asks.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5.5 (T2)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem not_avail_01 : ¬ avail ((game h0 h1).muSelf pol) 0 1 := by
  unfold avail; rw [condDen_01]; exact lt_irrefl 0
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem avail_00 : avail ((game h0 h1).muSelf pol) 0 0 := by
  unfold avail; rw [condDen_00]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem avail_10 : avail ((game h0 h1).muSelf pol) 1 0 := by
  unfold avail; rw [condDen_10]; exact h0
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem avail_11 : avail ((game h0 h1).muSelf pol) 1 1 := by
  unfold avail; rw [condDen_11]; linarith
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem avail_20 : avail ((game h0 h1).muSelf pol) 2 0 := by
  unfold avail; rw [condDen_20]; nlinarith
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem avail_21 : avail ((game h0 h1).muSelf pol) 2 1 := by
  unfold avail; rw [condDen_21]; positivity

/-- **T2 is a pure fixed point** (only `a` available at `s₀`; a tie at `s₁`; strict at `s₂`).
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5.5 (T2)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem isPureFP : (game h0 h1).IsPureFP pol := by
  unfold Game.IsPureFP Game.IsArgmaxH
  simp only [forall_fin_three, Fin.forall_fin_two, pol_0, pol_1, pol_2]
  refine ⟨⟨avail_00 h0 h1, fun _ => le_rfl, fun h => absurd h (not_avail_01 h0 h1)⟩,
    ⟨avail_11 h0 h1, fun _ => ?_, fun _ => le_rfl⟩,
    ⟨avail_20 h0 h1, fun _ => le_rfl, fun _ => ?_⟩⟩
  · rw [cond_10, cond_11]
  · rw [cond_20, cond_21]; positivity

/-- **The trust bound holds at every situation** (equality at `s₀` and `s₁`; `1/(1+δ) ≥ 1−δ` at `s₂`).
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5.5 (T2, "trust bound everywhere")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem TB_all : ∀ s, (game h0 h1).TB ((game h0 h1).muSelf pol) s := by
  simp only [forall_fin_three]
  refine ⟨⟨0, avail_00 h0 h1, ?_⟩, ⟨0, avail_10 h0 h1, ?_⟩, ⟨0, avail_20 h0 h1, ?_⟩⟩
  · rw [thr_eq, cond_00]
  · rw [thr_eq, cond_10]
  · rw [thr_eq, cond_20, le_div_iff₀ (by linarith)]; nlinarith

/-- The gap is exactly `δ`.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5.5 (T2, "gap exactly `δ`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem gap : (game h0 h1).Ustar - (game h0 h1).U pol = δ := by
  rw [Ustar_eq, U_apply]; simp [pol]

end T2

end Cleanroom.Uea.UeaSelfGame
