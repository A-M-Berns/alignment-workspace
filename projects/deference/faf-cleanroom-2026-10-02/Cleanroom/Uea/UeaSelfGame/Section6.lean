import Cleanroom.Uea.UeaSelfGame.Repaired
import Cleanroom.Uea.UeaSelfGame.Tables

/-!
# The §6 instance: no pure fixed point, plain or floored, under either convention

`δ = 1/10`, `S = Fin 3`, `A = Fin 2`, `U(aaa) = U(aba) = U(bbb) = 1`, `U(aab) = 3/4`, `U(bab) = 1/2`,
`U(baa) = U(bba) = 3/8`, `U(abb) = 1/8`, `Po` uniform on `{aaa, aba, abb, bbb}`, `piStar = aaa`. For each
of the eight pure policies some situation deviates, and the deviating action is available there (so the
Herrmann, "zero" and "unconditional" conventions agree): at `s₀` for `aaa`, `aab`, `aba`, `abb` (`cond(b) =
1 > cond(a)`: `305/312`, `233/312`, `305/312`, `53/312`) and for `baa`, `bab`, `bba` (`cond(a) = 17/24 >
cond(b)`: `29/74`, `19/37`, `29/74`); at `s₁` for `bbb` (`cond(a) = 1 > 305/312 = cond(b)`). The floored
agent has no pure fixed point either: the first four deviate in the argmax branch (`max = 1 > 9/10`),
`baa`, `bab`, `bba` are in the reset branch at `s₀` (`max = 17/24 < 9/10`) and play `b ≠ piStar s₀`, and
`bbb` deviates in the argmax branch at `s₁`.

Refutes the note's status-table line *"pure fixed points always exist (plain or floored)"* (which the note
itself marks REFUTED, by this instance); surviving neighbour: mixed existence (`Existence.lean`) and the
exact mixed fixed point of this instance (`Witness8801.lean`).

Scope: finite updateless self-game — self-consistent belief, pure policies; not rOSI, not the sequential
model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

namespace Section6

/-- The §6 instance.
Source: [[updateless-self-game]] §6 ("A concrete instance")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def game : Game (Fin 3) (Fin 2) where
  U := tab3 1 (3 / 4) 1 (1 / 8) (3 / 8) (1 / 2) (3 / 8) 1
  U_nonneg := fun π => (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).1
  U_le_one := fun π => (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  piStar := ![0, 0, 0]
  piStar_max := fun π => by
    rw [tab3_000]
    exact (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  Po := tab3 (1 / 4) 0 (1 / 4) (1 / 4) 0 0 0 (1 / 4)
  Po_mem := ⟨fun π => (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).1,
    by rw [sum_tab3]; norm_num⟩
  δ := 1 / 10
  δ_nonneg := by norm_num
  δ_lt_one := by norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem U_apply (π) : game.U π = tab3 1 (3 / 4) 1 (1 / 8) (3 / 8) (1 / 2) (3 / 8) 1 π := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Po_apply (π) : game.Po π = tab3 (1 / 4) 0 (1 / 4) (1 / 4) 0 0 0 (1 / 4) π := rfl
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
theorem piStar_eq : game.piStar = ![0, 0, 0] := rfl
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

/-! ### The `Po`-marginals -/

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_00 : game.pa 0 0 = 3 / 4 := by
  unfold Game.pa; rw [Game.condDen_fin3]; simp [Po_apply] <;> norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_01 : game.pa 0 1 = 1 / 4 := by
  unfold Game.pa; rw [Game.condDen_fin3]; simp [Po_apply] <;> norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_10 : game.pa 1 0 = 1 / 4 := by
  unfold Game.pa; rw [Game.condDen_fin3]; simp [Po_apply] <;> norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_11 : game.pa 1 1 = 3 / 4 := by
  unfold Game.pa; rw [Game.condDen_fin3]; simp [Po_apply] <;> norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_20 : game.pa 2 0 = 1 / 2 := by
  unfold Game.pa; rw [Game.condDen_fin3]; simp [Po_apply] <;> norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_21 : game.pa 2 1 = 1 / 2 := by
  unfold Game.pa; rw [Game.condDen_fin3]; simp [Po_apply] <;> norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem pva_00 : game.pva 0 0 = 17 / 32 := by
  unfold Game.pva; rw [Game.condNum_fin3]; simp [Po_apply, U_apply] <;> norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_01 : game.pva 0 1 = 1 / 4 := by
  unfold Game.pva; rw [Game.condNum_fin3]; simp [Po_apply, U_apply] <;> norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_10 : game.pva 1 0 = 1 / 4 := by
  unfold Game.pva; rw [Game.condNum_fin3]; simp [Po_apply, U_apply] <;> norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_11 : game.pva 1 1 = 17 / 32 := by
  unfold Game.pva; rw [Game.condNum_fin3]; simp [Po_apply, U_apply] <;> norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_20 : game.pva 2 0 = 1 / 2 := by
  unfold Game.pva; rw [Game.condNum_fin3]; simp [Po_apply, U_apply] <;> norm_num
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_21 : game.pva 2 1 = 9 / 32 := by
  unfold Game.pva; rw [Game.condNum_fin3]; simp [Po_apply, U_apply] <;> norm_num

/-! ### The pure conditionals through the self-posterior split -/

/-- `cond (μ_π) s a` for a pure `π`, as the self-posterior split evaluates it: numerator
`(9/10)[π s = a] U π + (1/10) pva`, denominator `(9/10)[π s = a] + (1/10) pa`.
Source: [[updateless-self-game]] §6
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_eq (π : Fin 3 → Fin 2) (s : Fin 3) (a : Fin 2) :
    game.cond (game.muSelf π) s a =
      ((1 - 1 / 10) * (if π s = a then game.U π else 0) + 1 / 10 * game.pva s a) /
        ((1 - 1 / 10) * (if π s = a then 1 else 0) + 1 / 10 * game.pa s a) := by
  unfold Game.cond; rw [Game.condNum_muSelf, Game.condDen_muSelf]; rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem avail_iff (π : Fin 3 → Fin 2) (s : Fin 3) (a : Fin 2) :
    avail (game.muSelf π) s a ↔ 0 < (1 - 1 / 10) * (if π s = a then (1:ℝ) else 0) + 1 / 10 * game.pa s a := by
  unfold avail; rw [Game.condDen_muSelf]; rfl

/-- Every action is available at every situation under every `μ_π`: all six `pa s a` are positive.
Source: [[updateless-self-game]] §6 ("the counts are the same under all three conventions")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem avail_all (π : Fin 3 → Fin 2) (s : Fin 3) (a : Fin 2) : avail (game.muSelf π) s a := by
  rw [avail_iff]
  have hpa : 0 < game.pa s a := by
    revert s a; simp only [forall_fin_three, Fin.forall_fin_two]
    rw [pa_00, pa_01, pa_10, pa_11, pa_20, pa_21]; norm_num
  split_ifs <;> linarith

/-! ### The eight policies -/

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem not_fp_of_dev {π : Fin 3 → Fin 2} {s : Fin 3} {b : Fin 2}
    (h : game.cond (game.muSelf π) s (π s) < game.cond (game.muSelf π) s b) : ¬ game.IsPureFP π := by
  intro hfp
  exact absurd h (not_lt.2 ((hfp s).2 b (avail_all π s b)))

/-- **No pure plain fixed point** (Herrmann convention; every deviating action is available, so the same
under the "zero" and "unconditional" conventions).
Source: [[updateless-self-game]] §6 ("A concrete instance … has no pure fixed point")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem no_pure_fp : ∀ π : Fin 3 → Fin 2, ¬ game.IsPureFP π := by
  have hrep : ∀ π : Fin 3 → Fin 2, π = ![π 0, π 1, π 2] := fun π => by
    funext i; fin_cases i <;> rfl
  intro π
  rw [hrep π]
  generalize π 0 = x; generalize π 1 = y; generalize π 2 = z
  revert x y z
  simp only [Fin.forall_fin_two]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  -- aaa: s₀, b
  · refine not_fp_of_dev (s := 0) (b := 1) ?_
    rw [cond_eq, cond_eq]; simp [pa_00, pa_01, pva_00, pva_01, U_apply] <;> norm_num
  -- aab: s₀, b
  · refine not_fp_of_dev (s := 0) (b := 1) ?_
    rw [cond_eq, cond_eq]; simp [pa_00, pa_01, pva_00, pva_01, U_apply] <;> norm_num
  -- aba: s₀, b
  · refine not_fp_of_dev (s := 0) (b := 1) ?_
    rw [cond_eq, cond_eq]; simp [pa_00, pa_01, pva_00, pva_01, U_apply] <;> norm_num
  -- abb: s₀, b
  · refine not_fp_of_dev (s := 0) (b := 1) ?_
    rw [cond_eq, cond_eq]; simp [pa_00, pa_01, pva_00, pva_01, U_apply] <;> norm_num
  -- baa: s₀, a
  · refine not_fp_of_dev (s := 0) (b := 0) ?_
    rw [cond_eq, cond_eq]; simp [pa_00, pa_01, pva_00, pva_01, U_apply] <;> norm_num
  -- bab: s₀, a
  · refine not_fp_of_dev (s := 0) (b := 0) ?_
    rw [cond_eq, cond_eq]; simp [pa_00, pa_01, pva_00, pva_01, U_apply] <;> norm_num
  -- bba: s₀, a
  · refine not_fp_of_dev (s := 0) (b := 0) ?_
    rw [cond_eq, cond_eq]; simp [pa_00, pa_01, pva_00, pva_01, U_apply] <;> norm_num
  -- bbb: s₁, a
  · refine not_fp_of_dev (s := 1) (b := 0) ?_
    rw [cond_eq, cond_eq]; simp [pa_10, pa_11, pva_10, pva_11, U_apply] <;> norm_num

/-- The two named deviations of the note, exactly: at `aaa`, `s₀`: `cond(a) = 305/312 < 1 = cond(b)`; at
`baa`, `s₀`: `cond(a) = 17/24 > 29/74 = cond(b)`.
Source: [[updateless-self-game]] §6
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem named_deviations :
    game.cond (game.muSelf ![0, 0, 0]) 0 0 = 305 / 312 ∧ game.cond (game.muSelf ![0, 0, 0]) 0 1 = 1 ∧
    game.cond (game.muSelf ![1, 0, 0]) 0 0 = 17 / 24 ∧ game.cond (game.muSelf ![1, 0, 0]) 0 1 = 29 / 74 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [cond_eq] <;> simp [pa_00, pa_01, pva_00, pva_01, U_apply] <;> norm_num

/-- **No pure floored fixed point** (with `piStar = aaa`): the first four policies deviate in the argmax
branch at `s₀` (some available conditional `= 1 > 9/10`), `baa`, `bab`, `bba` are in the reset branch at
`s₀` (every available conditional `< 9/10`) and play `b ≠ a = piStar s₀`, and `bbb` deviates in the
argmax branch at `s₁`. The floored predicate depends on the chosen `piStar`; this instance has three
maximizers (`aaa`, `aba`, `bbb`), and the theorem is stated for `piStar = aaa`. Hand-checked by the round-1
adversarial auditor (N3), not machine-checked: the argmax-branch failures above are `piStar`-free; the
reset-branch failures of `baa`, `bab`, `bba` at `s₀` would need `piStar 0 = b`, i.e. `piStar = bbb`, and
each then fails at `s₁` (`baa`, `bab` reset there and play `a`; `bba` is in the argmax branch with
`cond(a) = 1` and plays `b`). So the conclusion is expected to hold for every maximizer; only `aaa` is proved.
Source: [[updateless-self-game]] §6 ("plain and floored agents alike")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem no_pure_floored_fp : ∀ π : Fin 3 → Fin 2, ¬ game.IsPureFPfloored π := by
  have hrep : ∀ π : Fin 3 → Fin 2, π = ![π 0, π 1, π 2] := fun π => by
    funext i; fin_cases i <;> rfl
  intro π
  rw [hrep π]
  generalize π 0 = x; generalize π 1 = y; generalize π 2 = z
  revert x y z
  simp only [Fin.forall_fin_two]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  -- the argmax-branch deviations at s₀ (b has conditional 1 > 9/10, a is worse)
  · intro h
    obtain ⟨_, hB, _⟩ := h 0
    have hb := (hB ⟨1, avail_all _ 0 1, by rw [thr_eq, cond_eq]; simp [pa_01, pva_01, U_apply] <;> norm_num⟩).2 1
      (avail_all _ 0 1)
    rw [cond_eq, cond_eq] at hb; simp [pa_00, pa_01, pva_00, pva_01, U_apply] at hb <;> norm_num at hb
  · intro h
    obtain ⟨_, hB, _⟩ := h 0
    have hb := (hB ⟨1, avail_all _ 0 1, by rw [thr_eq, cond_eq]; simp [pa_01, pva_01, U_apply] <;> norm_num⟩).2 1
      (avail_all _ 0 1)
    rw [cond_eq, cond_eq] at hb; simp [pa_00, pa_01, pva_00, pva_01, U_apply] at hb <;> norm_num at hb
  · intro h
    obtain ⟨_, hB, _⟩ := h 0
    have hb := (hB ⟨1, avail_all _ 0 1, by rw [thr_eq, cond_eq]; simp [pa_01, pva_01, U_apply] <;> norm_num⟩).2 1
      (avail_all _ 0 1)
    rw [cond_eq, cond_eq] at hb; simp [pa_00, pa_01, pva_00, pva_01, U_apply] at hb <;> norm_num at hb
  · intro h
    obtain ⟨_, hB, _⟩ := h 0
    have hb := (hB ⟨1, avail_all _ 0 1, by rw [thr_eq, cond_eq]; simp [pa_01, pva_01, U_apply] <;> norm_num⟩).2 1
      (avail_all _ 0 1)
    rw [cond_eq, cond_eq] at hb; simp [pa_00, pa_01, pva_00, pva_01, U_apply] at hb <;> norm_num at hb
  -- the reset-branch policies at s₀ (both conditionals < 9/10, must play a, play b)
  · intro h
    obtain ⟨hA, _, _⟩ := h 0
    have := hA (by
      simp only [Fin.forall_fin_two]
      refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> rw [thr_eq, cond_eq] <;>
        simp [pa_00, pa_01, pva_00, pva_01, U_apply] <;> norm_num)
    rw [piStar_eq] at this; simp at this
  · intro h
    obtain ⟨hA, _, _⟩ := h 0
    have := hA (by
      simp only [Fin.forall_fin_two]
      refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> rw [thr_eq, cond_eq] <;>
        simp [pa_00, pa_01, pva_00, pva_01, U_apply] <;> norm_num)
    rw [piStar_eq] at this; simp at this
  · intro h
    obtain ⟨hA, _, _⟩ := h 0
    have := hA (by
      simp only [Fin.forall_fin_two]
      refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> rw [thr_eq, cond_eq] <;>
        simp [pa_00, pa_01, pva_00, pva_01, U_apply] <;> norm_num)
    rw [piStar_eq] at this; simp at this
  -- bbb: argmax branch at s₁ (a has conditional 1 > 9/10, b is worse)
  · intro h
    obtain ⟨_, hB, _⟩ := h 1
    have hb := (hB ⟨0, avail_all _ 1 0, by rw [thr_eq, cond_eq]; simp [pa_10, pva_10, U_apply] <;> norm_num⟩).2 0
      (avail_all _ 1 0)
    rw [cond_eq, cond_eq] at hb; simp [pa_10, pa_11, pva_10, pva_11, U_apply] at hb <;> norm_num at hb

/-- **The status-table line "pure fixed points always exist (plain or floored)" is false**: this instance
has none, under either convention. Surviving neighbour: `exists_isFPext` and `Witness8801`.
Scope: finite updateless self-game — self-consistent belief; not rOSI, not the sequential model.
Source: [[updateless-self-game]] §6, §10 (status table); [[uea-inventory]] 029
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem pure_existence_refuted :
    ∃ G : Game (Fin 3) (Fin 2), G.δ = 1 / 10 ∧ (∀ π s a, avail (G.muSelf π) s a) ∧
      (∀ π, ¬ G.IsPureFP π) ∧ (∀ π, ¬ G.IsPureFPfloored π) :=
  ⟨game, rfl, avail_all, no_pure_fp, no_pure_floored_fp⟩

end Section6

end Cleanroom.Uea.UeaSelfGame
