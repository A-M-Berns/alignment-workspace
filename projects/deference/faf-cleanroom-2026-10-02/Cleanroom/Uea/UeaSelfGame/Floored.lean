import Cleanroom.Uea.UeaSelfGame.Repaired
import Cleanroom.Uea.UeaSelfGame.TablesMixed

/-!
# Theorem D's mixed claim refuted exactly (`section_5`)

`δ = 1/10`, `S = A = Fin 2`, `U(aa) = 819/829`, `U(ab) = U(ba) = 0`, `U(bb) = 1`, `Po = δ_{aa}`,
`piStar = bb`, `σ_s = (9/10) a + (1/10) b` at both situations. Then `Fext σ s a = 9/10 = (1−δ) U*` exactly
(the equality branch) and `Fext σ s b = 1/10`, so `σ` is a floored fixed point (the reset action `b =
piStar s` may carry mass at equality) but not a plain one (`b` is supported and not an argmax); every
action is available at both situations, so the Herrmann and extension conditionals coincide (the witness
is convention-free). Its value `U(σ) = 16792/20725 ≈ 0.8102 < 8/9 = U* − δ/(1−δ)`: gap
`3933/20725 ≈ 1.898 δ`.

Refutes [[updateless-self-game]] §7: *"The mixed version follows from Theorem C′ in the same way (at any
`s` where some support action is in the argmax branch)."* (the note's own definitions). Mechanism: at an
equality node the reset action's mass sits on the policy `bb`, which is not `piStar`-like elsewhere in
value terms — C′'s averaging over the support does not cover it. Surviving neighbour: `theoremD_pure`
(`Repaired.lean`). The instance was computed by `updateless_existence.py` `section_5` and never written up.

Scope: finite updateless self-game — product self-hypothesis, continuous extension at null actions,
floored agent; not rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

namespace Section5

/-- The `section_5` instance.
Source: `updateless_existence.py` `section_5`; [[updateless-self-game]] §7
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def game : Game (Fin 2) (Fin 2) where
  U := tab2 (819 / 829) 0 0 1
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
  δ := 1 / 10
  δ_nonneg := by norm_num
  δ_lt_one := by norm_num

/-- The mixed policy `σ_s = (9/10) a + (1/10) b`.
Source: `updateless_existence.py` `section_5`
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def σ : Fin 2 → Fin 2 → ℝ := fun _ a => if a = 0 then 9 / 10 else 1 / 10
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

@[simp] theorem σ_0 (s : Fin 2) : σ s 0 = 9 / 10 := by simp [σ]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem σ_1 (s : Fin 2) : σ s 1 = 1 / 10 := by simp [σ]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem U_apply (π) : game.U π = tab2 (819 / 829) 0 0 1 π := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Po_apply (π) : game.Po π = tab2 1 0 0 0 π := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem δ_eq : game.δ = 1 / 10 := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem piStar_eq : game.piStar = ![1, 1] := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ustar_eq : game.Ustar = 1 := by simp [Game.Ustar, game]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem thr_eq : game.thr = 9 / 10 := by simp [Game.thr, Ustar_eq, δ_eq]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem isMixed : IsMixed σ := fun s =>
  ⟨fun a => by unfold σ; split_ifs <;> norm_num, by simp [Fin.sum_univ_two]; norm_num⟩
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem pa_0 (s : Fin 2) : game.pa s 0 = 1 := by
  unfold Game.pa; rw [Game.condDen_fin2]
  revert s; simp only [Fin.forall_fin_two]
  simp [Fin.sum_univ_two, Po_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem pa_1 (s : Fin 2) : game.pa s 1 = 0 := by
  unfold Game.pa; rw [Game.condDen_fin2]
  revert s; simp only [Fin.forall_fin_two]
  simp [Fin.sum_univ_two, Po_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem pva_0 (s : Fin 2) : game.pva s 0 = 819 / 829 := by
  unfold Game.pva; rw [Game.condNum_fin2]
  revert s; simp only [Fin.forall_fin_two]
  simp [Fin.sum_univ_two, Po_apply, U_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Ucoord_0 (s : Fin 2) : game.Ucoord σ s 0 = 9 / 10 * (819 / 829) := by
  revert s; simp only [Fin.forall_fin_two]
  constructor
  · rw [Game.Ucoord_fin2_0]; simp [Fin.sum_univ_two, U_apply]
  · rw [Game.Ucoord_fin2_1]; simp [Fin.sum_univ_two, U_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Ucoord_1 (s : Fin 2) : game.Ucoord σ s 1 = 1 / 10 := by
  revert s; simp only [Fin.forall_fin_two]
  constructor
  · rw [Game.Ucoord_fin2_0]; simp [Fin.sum_univ_two, U_apply]
  · rw [Game.Ucoord_fin2_1]; simp [Fin.sum_univ_two, U_apply]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem denMix_0 (s : Fin 2) : game.denMix σ s 0 = 91 / 100 := by
  unfold Game.denMix; rw [pa_0, σ_0, δ_eq]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem denMix_1 (s : Fin 2) : game.denMix σ s 1 = 9 / 100 := by
  unfold Game.denMix; rw [pa_1, σ_1, δ_eq]; norm_num

/-- `Fext σ s a = 9/10 = (1−δ) U*` exactly: the equality branch.
Source: `updateless_existence.py` `section_5`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Fext_0 (s : Fin 2) : game.Fext σ s 0 = 9 / 10 := by
  rw [game.Fext_eq_of_availMix (by unfold Game.availMix; rw [denMix_0]; norm_num), denMix_0, Ucoord_0,
    pva_0, σ_0, δ_eq]
  norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Fext_1 (s : Fin 2) : game.Fext σ s 1 = 1 / 10 := by
  rw [game.Fext_eq_Ucoord_of_pa_eq_zero σ (pa_1 s), Ucoord_1]

/-- Every action is available at both situations: the Herrmann and extension conditionals coincide.
Source: `updateless_existence.py` `section_5` ("under both conventions")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem availMix_all (s a : Fin 2) : game.availMix σ s a := by
  unfold Game.availMix
  revert a; simp only [Fin.forall_fin_two]
  constructor
  · rw [denMix_0]; norm_num
  · rw [denMix_1]; norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem maxF_eq (s : Fin 2) : game.maxF σ s = 9 / 10 := by
  apply le_antisymm
  · have key : ∀ a : Fin 2, game.Fext σ s a ≤ 9 / 10 := by
      simp only [Fin.forall_fin_two]
      exact ⟨by rw [Fext_0], by rw [Fext_1]; norm_num⟩
    exact Finset.sup'_le _ _ fun a _ => key a
  · rw [← Fext_0 s]; exact game.Fext_le_maxF σ s 0
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem resid_eq (s : Fin 2) : game.resid σ s = 0 := by
  unfold Game.resid; rw [maxF_eq, thr_eq]; norm_num

/-- **`σ` is a floored fixed point** (equality branch at both situations: `a` is the argmax, `b = piStar s`).
Source: `updateless_existence.py` `section_5`
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem isFlooredFPext : game.IsFlooredFPext σ := by
  refine ⟨isMixed, fun s => ⟨fun hr => ?_, fun hr => ?_, fun _ a _ => ?_⟩⟩
  · rw [resid_eq] at hr; exact absurd hr (lt_irrefl 0)
  · rw [resid_eq] at hr; exact absurd hr (lt_irrefl 0)
  · revert a; simp only [Fin.forall_fin_two]
    constructor
    · intro _; left; rw [Fext_0, maxF_eq]
    · intro _; right; rw [piStar_eq]; fin_cases s <;> rfl

/-- **`σ` is not a plain fixed point** (`b` is supported but `Fext σ s b = 1/10 < 9/10 = Fext σ s a`), under
either convention.
Source: `updateless_existence.py` `section_5`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem not_isFPherr : ¬ game.IsFPherr σ := by
  rintro ⟨_, h⟩
  have := h 0 1 (by rw [σ_1]; norm_num) 0 (availMix_all 0 0)
  rw [Fext_0, Fext_1] at this
  norm_num at this
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem not_isFPext : ¬ game.IsFPext σ := fun h => not_isFPherr h.isFPherr

/-- `U(σ) = 16792/20725`.
Source: `updateless_existence.py` `section_5`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Umix_eq : game.Umix σ = 16792 / 20725 := by
  rw [Game.Umix_fin2]; simp [Fin.sum_univ_two, U_apply]; norm_num

/-- `U(σ) < U* − δ/(1−δ) = 8/9`.
Source: `updateless_existence.py` `section_5`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Umix_lt_bound : game.Umix σ < game.Ustar - game.δ / (1 - game.δ) := by
  rw [Umix_eq, Ustar_eq, δ_eq]; norm_num

/-- **Theorem D's mixed claim is false**: a floored (extension) fixed point, convention-free, with value
below `U* − δ/(1−δ)` by `3933/20725 ≈ 1.898 δ`. Refutes [[updateless-self-game]] §7 *"The mixed version
follows from Theorem C′ in the same way"*; surviving neighbour `theoremD_pure`.
Scope: finite updateless self-game — floored agent, continuous extension; not rOSI, not the sequential
model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §7; [[uea-inventory]] 030; [[uea-2-inventory]] 2-014(5); `section_5`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem theoremD_mixed_refuted :
    ∃ (G : Game (Fin 2) (Fin 2)) (σ : Fin 2 → Fin 2 → ℝ), G.δ = 1 / 10 ∧ G.IsFlooredFPext σ ∧
      (∀ s a, G.availMix σ s a) ∧ ¬ G.IsFPext σ ∧ G.Umix σ = 16792 / 20725 ∧
      G.Umix σ < G.Ustar - G.δ / (1 - G.δ) :=
  ⟨game, σ, rfl, isFlooredFPext, availMix_all, not_isFPext, Umix_eq, Umix_lt_bound⟩

/-- The gap exceeds `(3/2) δ` here, so no bound of the form `U* − c δ/(1−δ)` with `c ≤ 3/2 · (1−δ)` can hold for
floored mixed fixed points; a corrected constant must be at least `≈ 1.9` at `δ = 1/10` (and the note's
`T3`-style family suggests `2` asymptotically — recorded as OPEN).
Source: [[uea-self-game-mandate]] target 9 (f)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem gap_gt : 3 / 2 * game.δ < game.Ustar - game.Umix σ := by
  rw [Umix_eq, Ustar_eq, δ_eq]; norm_num

end Section5

end Cleanroom.Uea.UeaSelfGame
