import Cleanroom.Uea.UeaSelfGame.Repaired
import Cleanroom.Uea.UeaSelfGame.Tables

/-!
# The `T3` family at `δ = 1/10`, `n = 3`, `θ = 1/10`: the §5.5 conjecture refuted

`S = Fin 3`, `A = Fin 2`, `π = aaa` with `U(aaa) = 1 − g`; the two deviations `aba`, `aab` have `U = 1` and
`Po = 9/20` each; the polluter `bbb` has `U = 0`, `Po = 1/10`; every other `U = 0`; `piStar = aba`. Exact
conditions in `g` (`δ = 1/10`): `π` is a pure fixed point iff `g ≤ 21/110`; the trust bound at `s₀` iff
`g ≤ 11/100` (equality `cond = 9/10`); at `s₁`, `s₂` iff `g ≤ 21/200`. Hence:

* `g = 11/100`: pure fixed point, trust bound at `s₀`, gap `11/100 > 10/91 = δ/(1−δ+δ²)`;
* `g = 21/200`: pure fixed point, trust bound at all three situations, gap `21/200 > 1/10 = δ`.

Both refute [[updateless-self-game]] §5.5: *"Conjecture: sup gap = δ/(1−δ+δ²) with the trust bound at one
situation and = δ with it at all situations."* (the note's own definitions). These instances were computed
by `updateless_existence.py` §(6) and never written up; this file is their first record. Surviving
neighbour: Theorem C's `δ/(1−δ)` (`Repaired.lean`).

Scope: finite updateless self-game — pointwise EDT conditional on one's own action, self-consistent
belief; not rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

namespace T3

variable {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)

/-- The `T3(3, 1/10, g)` instance at `δ = 1/10`.
Source: [[updateless-self-game]] §5.5 (the T3 family of `updateless_existence.py` §(6))
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def game : Game (Fin 3) (Fin 2) where
  U := tab3 (1 - g) 1 1 0 0 0 0 0
  U_nonneg := fun π => (tab3_bounds (lo := 0) (hi := 1) ⟨by linarith, by linarith⟩ (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).1
  U_le_one := fun π => (tab3_bounds (lo := 0) (hi := 1) ⟨by linarith, by linarith⟩ (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  piStar := ![0, 1, 0]
  piStar_max := fun π => by
    rw [tab3_010]
    exact (tab3_bounds (lo := 0) (hi := 1) ⟨by linarith, by linarith⟩ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  Po := tab3 0 (9 / 20) (9 / 20) 0 0 0 0 (1 / 10)
  Po_mem := ⟨fun π => (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).1,
    by rw [sum_tab3]; norm_num⟩
  δ := 1 / 10
  δ_nonneg := by norm_num
  δ_lt_one := by norm_num

/-- The own policy `π = aaa`.
Source: none: infrastructure (instance datum)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pol : Fin 3 → Fin 2 := ![0, 0, 0]
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
@[simp] theorem pol_1 : pol 1 = 0 := rfl
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

theorem U_apply (π) : (game hg0 hg1).U π = tab3 (1 - g) 1 1 0 0 0 0 0 π := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem δ_eq : (game hg0 hg1).δ = 1 / 10 := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ustar_eq : (game hg0 hg1).Ustar = 1 := by simp [Game.Ustar, game]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem thr_eq : (game hg0 hg1).thr = 9 / 10 := by simp [Game.thr, Ustar_eq, δ_eq]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem mu_apply (π') : (game hg0 hg1).muSelf pol π' =
    (1 - 1 / 10) * (if π' 0 = 0 ∧ π' 1 = 0 ∧ π' 2 = 0 then 1 else 0) +
      1 / 10 * tab3 0 (9 / 20) (9 / 20) 0 0 0 0 (1 / 10) π' := by
  rw [Game.muSelf_apply_fin3]; rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_00 : condDen ((game hg0 hg1).muSelf pol) 0 0 = 99 / 100 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_00 : (game hg0 hg1).condNum ((game hg0 hg1).muSelf pol) 0 0 = 9 / 10 * (1 - g) + 9 / 100 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]; norm_num
  try ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_01 : condDen ((game hg0 hg1).muSelf pol) 0 1 = 1 / 100 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_01 : (game hg0 hg1).condNum ((game hg0 hg1).muSelf pol) 0 1 = 0 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_10 : condDen ((game hg0 hg1).muSelf pol) 1 0 = 189 / 200 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_10 : (game hg0 hg1).condNum ((game hg0 hg1).muSelf pol) 1 0 = 9 / 10 * (1 - g) + 9 / 200 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]; norm_num
  try ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_11 : condDen ((game hg0 hg1).muSelf pol) 1 1 = 11 / 200 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_11 : (game hg0 hg1).condNum ((game hg0 hg1).muSelf pol) 1 1 = 9 / 200 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_20 : condDen ((game hg0 hg1).muSelf pol) 2 0 = 189 / 200 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_20 : (game hg0 hg1).condNum ((game hg0 hg1).muSelf pol) 2 0 = 9 / 10 * (1 - g) + 9 / 200 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]; norm_num
  try ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_21 : condDen ((game hg0 hg1).muSelf pol) 2 1 = 11 / 200 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_21 : (game hg0 hg1).condNum ((game hg0 hg1).muSelf pol) 2 1 = 9 / 200 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_00 : (game hg0 hg1).cond ((game hg0 hg1).muSelf pol) 0 0 = (9 / 10 * (1 - g) + 9 / 100) / (99 / 100) := by
  unfold Game.cond; rw [condNum_00, condDen_00]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_01 : (game hg0 hg1).cond ((game hg0 hg1).muSelf pol) 0 1 = 0 := by
  unfold Game.cond; rw [condNum_01, zero_div]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_10 : (game hg0 hg1).cond ((game hg0 hg1).muSelf pol) 1 0 = (9 / 10 * (1 - g) + 9 / 200) / (189 / 200) := by
  unfold Game.cond; rw [condNum_10, condDen_10]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_11 : (game hg0 hg1).cond ((game hg0 hg1).muSelf pol) 1 1 = 9 / 11 := by
  unfold Game.cond; rw [condNum_11, condDen_11]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_20 : (game hg0 hg1).cond ((game hg0 hg1).muSelf pol) 2 0 = (9 / 10 * (1 - g) + 9 / 200) / (189 / 200) := by
  unfold Game.cond; rw [condNum_20, condDen_20]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_21 : (game hg0 hg1).cond ((game hg0 hg1).muSelf pol) 2 1 = 9 / 11 := by
  unfold Game.cond; rw [condNum_21, condDen_21]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem avail_all : ∀ s a, avail ((game hg0 hg1).muSelf pol) s a := by
  unfold avail
  simp only [forall_fin_three, Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [condDen_00]; norm_num
  · rw [condDen_01]; norm_num
  · rw [condDen_10]; norm_num
  · rw [condDen_11]; norm_num
  · rw [condDen_20]; norm_num
  · rw [condDen_21]; norm_num

/-- **`T3` is a pure fixed point iff `g ≤ 21/110`** (automatic at `s₀`; at `s₁`, `s₂` the own action's
conditional must dominate the deviation's `9/11`).
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5.5; `updateless_existence.py` §(6) ("fixed point at `s_i` ⟺ …")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem isPureFP_iff : (game hg0 hg1).IsPureFP pol ↔ g ≤ 21 / 110 := by
  unfold Game.IsPureFP Game.IsArgmaxH
  simp only [forall_fin_three, Fin.forall_fin_two, pol_0, pol_1, pol_2]
  have h1 : (9 / 11 : ℝ) ≤ (9 / 10 * (1 - g) + 9 / 200) / (189 / 200) ↔ g ≤ 21 / 110 := by
    rw [le_div_iff₀ (by norm_num)]; constructor <;> intro h <;> linarith
  constructor
  · rintro ⟨_, ⟨_, _, h⟩, _⟩
    rw [cond_10, cond_11] at h
    exact h1.1 (h (avail_all hg0 hg1 1 1))
  · intro h
    refine ⟨⟨avail_all hg0 hg1 0 0, fun _ => le_rfl, fun _ => ?_⟩,
      ⟨avail_all hg0 hg1 1 0, fun _ => le_rfl, fun _ => ?_⟩,
      ⟨avail_all hg0 hg1 2 0, fun _ => le_rfl, fun _ => ?_⟩⟩
    · rw [cond_00, cond_01]; apply div_nonneg <;> linarith
    · rw [cond_10, cond_11]; exact h1.2 h
    · rw [cond_20, cond_21]; exact h1.2 h

/-- **The trust bound at `s₀` iff `g ≤ 11/100`** (equality `cond = 9/10` at `g = 11/100`).
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: `updateless_existence.py` §(6) ("`TB_{s₀}` ⟺ `g ≤ δ + δ²(1−θ)/(1−δ)`", which is `11/100`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem TB_0_iff : (game hg0 hg1).TB ((game hg0 hg1).muSelf pol) 0 ↔ g ≤ 11 / 100 := by
  unfold Game.TB
  rw [thr_eq]
  simp only [Fin.exists_fin_two]
  rw [cond_00, cond_01]
  have h1 : (9 / 10 : ℝ) ≤ (9 / 10 * (1 - g) + 9 / 100) / (99 / 100) ↔ g ≤ 11 / 100 := by
    rw [le_div_iff₀ (by norm_num)]; constructor <;> intro h <;> linarith
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact h1.1 h
    · norm_num at h
  · intro h; exact Or.inl ⟨avail_all hg0 hg1 0 0, h1.2 h⟩

/-- **The trust bound at `s₁` (and `s₂`) iff `g ≤ 21/200`**.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: `updateless_existence.py` §(6) ("`TB_{s_i}` ⟺ `g ≤ δ + δ²(n−2)w/(1−δ)`", which is `21/200`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem TB_1_iff : (game hg0 hg1).TB ((game hg0 hg1).muSelf pol) 1 ↔ g ≤ 21 / 200 := by
  unfold Game.TB
  rw [thr_eq]
  simp only [Fin.exists_fin_two]
  rw [cond_10, cond_11]
  have h1 : (9 / 10 : ℝ) ≤ (9 / 10 * (1 - g) + 9 / 200) / (189 / 200) ↔ g ≤ 21 / 200 := by
    rw [le_div_iff₀ (by norm_num)]; constructor <;> intro h <;> linarith
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact h1.1 h
    · norm_num at h
  · intro h; exact Or.inl ⟨avail_all hg0 hg1 1 0, h1.2 h⟩
/-- Supporting lemma (no headline claim; see the headline it serves).
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem TB_2_iff : (game hg0 hg1).TB ((game hg0 hg1).muSelf pol) 2 ↔ g ≤ 21 / 200 := by
  unfold Game.TB
  rw [thr_eq]
  simp only [Fin.exists_fin_two]
  rw [cond_20, cond_21]
  have h1 : (9 / 10 : ℝ) ≤ (9 / 10 * (1 - g) + 9 / 200) / (189 / 200) ↔ g ≤ 21 / 200 := by
    rw [le_div_iff₀ (by norm_num)]; constructor <;> intro h <;> linarith
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact h1.1 h
    · norm_num at h
  · intro h; exact Or.inl ⟨avail_all hg0 hg1 2 0, h1.2 h⟩
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem gap : (game hg0 hg1).Ustar - (game hg0 hg1).U pol = g := by
  rw [Ustar_eq, U_apply]; simp [pol]

/-- **The one-situation half of the §5.5 conjecture is false**: at `δ = 1/10` there is a pure fixed point
with the trust bound at `s₀` whose gap `11/100` exceeds `δ/(1−δ+δ²) = 10/91`.
Refutes [[updateless-self-game]] §5.5, *"Conjecture: sup gap = δ/(1−δ+δ²) with the trust bound at one
situation"* (the note's own definitions). Surviving neighbour: `theoremC` (`δ/(1−δ) = 1/9`).
Scope: finite updateless self-game — self-consistent belief; not rOSI, not the sequential model.
Source: [[updateless-self-game]] §5.5; [[uea-2-inventory]] 2-013, 2-016; `updateless_existence.py` §(6)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem conjecture_one_situation_refuted :
    ∃ (G : Game (Fin 3) (Fin 2)) (π : Fin 3 → Fin 2), G.δ = 1 / 10 ∧ G.IsPureFP π ∧ G.TB (G.muSelf π) 0 ∧
      G.Ustar - G.U π = 11 / 100 ∧ G.δ / (1 - G.δ + G.δ ^ 2) < G.Ustar - G.U π ∧
      G.Ustar - G.U π ≤ G.δ / (1 - G.δ) := by
  have hg0 : (0 : ℝ) ≤ 11 / 100 := by norm_num
  have hg1 : (11 / 100 : ℝ) ≤ 1 := by norm_num
  refine ⟨game hg0 hg1, pol, rfl, (isPureFP_iff hg0 hg1).2 (by norm_num),
    (TB_0_iff hg0 hg1).2 le_rfl, gap hg0 hg1, ?_, ?_⟩
  · rw [gap, δ_eq]; norm_num
  · rw [gap, δ_eq]; norm_num

/-- **The all-situations half of the §5.5 conjecture is false**: at `δ = 1/10` there is a pure fixed point
with the trust bound at every situation whose gap `21/200` exceeds `δ = 1/10`.
Refutes [[updateless-self-game]] §5.5, *"… and = δ with it at all situations"*. Surviving neighbour:
`theoremC`.
Scope: finite updateless self-game — self-consistent belief; not rOSI, not the sequential model.
Source: [[updateless-self-game]] §5.5; [[uea-2-inventory]] 2-013, 2-016; `updateless_existence.py` §(6)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem conjecture_all_situations_refuted :
    ∃ (G : Game (Fin 3) (Fin 2)) (π : Fin 3 → Fin 2), G.δ = 1 / 10 ∧ G.IsPureFP π ∧
      (∀ s, G.TB (G.muSelf π) s) ∧ G.Ustar - G.U π = 21 / 200 ∧ G.δ < G.Ustar - G.U π ∧
      G.Ustar - G.U π ≤ G.δ / (1 - G.δ) := by
  have hg0 : (0 : ℝ) ≤ 21 / 200 := by norm_num
  have hg1 : (21 / 200 : ℝ) ≤ 1 := by norm_num
  refine ⟨game hg0 hg1, pol, rfl, (isPureFP_iff hg0 hg1).2 (by norm_num), ?_, gap hg0 hg1, ?_, ?_⟩
  · simp only [forall_fin_three]
    exact ⟨(TB_0_iff hg0 hg1).2 (by norm_num), (TB_1_iff hg0 hg1).2 le_rfl, (TB_2_iff hg0 hg1).2 le_rfl⟩
  · rw [gap, δ_eq]; norm_num
  · rw [gap, δ_eq]; norm_num

end T3

end Cleanroom.Uea.UeaSelfGame
