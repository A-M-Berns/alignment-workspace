import Cleanroom.Uea.UeaSelfGame.Tables
import Cleanroom.Uea.UeaSelfGame.FlooredBridge

/-!
# Audit round 3 (adversarial) probe: the inclusion conjecture `inclusion_open` is false

`inclusion_open` (`Open.lean`) states: for every finite updateless self-game, if some pure Herrmann fixed
point exists then some pure extension fixed point exists ([[uea-2-inventory]] 2-014/2-015, "no instance
… on 1500 random instances"). This probe refutes it with an exact instance on two situations and three
actions `{a, b, c}`:

* `U(ab) = U(bc) = 1`, `U(cc) = 1/2`, every other `U = 0`; `π* = ab`;
* `Po = (1/4) δ_{ab} + (1/2) δ_{bb} + (1/4) δ_{bc}`; `δ = 3/4`.

**The only pure Herrmann fixed point is `ac`, the worst policy (`U(ac) = 0`)**: under `μ_{ac}` the own
action has conditional `3/7` at both situations (its fibre is `ac` itself with weight `1/4` and one
`Po`-policy of utility `1` with weight `3/16`), the available deviation `b` has the pure `Po`-conditional
`1/3` at both, and the third action is *unavailable* at both (`c` at `s₀`, `a` at `s₁`: no `Po`-policy
plays it there). So `ac` is a strict Herrmann fixed point. It is **not** an extension fixed point: the
unavailable `c` at `s₀` has `Fext = U(cc) = 1/2 > 3/7`. **No other pure policy is an extension fixed
point** (each loses to an *available* action with `Po`-conditional `1`, except `aa`, which loses to `b` at
`s₁` with `1/3 > 0`); so the game has a pure Herrmann fixed point and no pure extension fixed point.

Found by an exact-arithmetic random search over the definitions of `Defs.lean` (counterexamples appear in
every shape beyond `2 × 2` at a rate of roughly one in `10³`–`10⁴` random instances; none in `200 000`
instances at `|S| = |A| = 2`). The mechanism needs an unavailable action (where the two conventions differ),
which `|A| = 3` or `|S| = 3` supplies more readily than `2 × 2`.

Not imported by the library.
-/

namespace Cleanroom.Uea.UeaSelfGame.AuditR3.Inclusion

open Finset

/-- Utilities: `ab ↦ 1`, `bc ↦ 1`, `cc ↦ 1/2`, else `0`. -/
noncomputable def Ufun (π : Fin 2 → Fin 3) : ℝ :=
  if π 0 = 0 ∧ π 1 = 1 then 1 else if π 0 = 1 ∧ π 1 = 2 then 1 else
    if π 0 = 2 ∧ π 1 = 2 then 1 / 2 else 0

/-- `Po = (1/4) δ_{ab} + (1/2) δ_{bb} + (1/4) δ_{bc}`. -/
noncomputable def Pofun (π : Fin 2 → Fin 3) : ℝ :=
  if π 0 = 0 ∧ π 1 = 1 then 1 / 4 else if π 0 = 1 ∧ π 1 = 1 then 1 / 2 else
    if π 0 = 1 ∧ π 1 = 2 then 1 / 4 else 0

theorem Ufun_ab : Ufun ![0, 1] = 1 := by simp [Ufun]

/-- The instance as a `Game`. -/
noncomputable def game : Game (Fin 2) (Fin 3) where
  U := Ufun
  U_nonneg := fun π => by unfold Ufun; split_ifs <;> norm_num
  U_le_one := fun π => by unfold Ufun; split_ifs <;> norm_num
  piStar := ![0, 1]
  piStar_max := fun π => by rw [Ufun_ab]; unfold Ufun; split_ifs <;> norm_num
  Po := Pofun
  Po_mem := ⟨fun π => by unfold Pofun; split_ifs <;> norm_num, by
    rw [sum_fin2_arrow]
    simp [Fin.sum_univ_three, Pofun]
    norm_num⟩
  δ := 3 / 4
  δ_nonneg := by norm_num
  δ_lt_one := by norm_num

theorem δ_eq : game.δ = 3 / 4 := rfl
theorem U_apply (π) : game.U π = Ufun π := rfl
theorem Po_apply (π) : game.Po π = Pofun π := rfl
theorem Ustar_eq : game.Ustar = 1 := by show Ufun ![0, 1] = 1; exact Ufun_ab

/-! ### `pa`, `pva` -/

theorem pa_00 : game.pa 0 0 = 1 / 4 := by
  unfold Game.pa; rw [Game.condDen_fin2]; simp [Fin.sum_univ_three, Po_apply, Pofun] <;> norm_num
theorem pa_01 : game.pa 0 1 = 3 / 4 := by
  unfold Game.pa; rw [Game.condDen_fin2]; simp [Fin.sum_univ_three, Po_apply, Pofun] <;> norm_num
theorem pa_02 : game.pa 0 2 = 0 := by
  unfold Game.pa; rw [Game.condDen_fin2]; simp [Fin.sum_univ_three, Po_apply, Pofun] <;> norm_num
theorem pa_10 : game.pa 1 0 = 0 := by
  unfold Game.pa; rw [Game.condDen_fin2]; simp [Fin.sum_univ_three, Po_apply, Pofun] <;> norm_num
theorem pa_11 : game.pa 1 1 = 3 / 4 := by
  unfold Game.pa; rw [Game.condDen_fin2]; simp [Fin.sum_univ_three, Po_apply, Pofun] <;> norm_num
theorem pa_12 : game.pa 1 2 = 1 / 4 := by
  unfold Game.pa; rw [Game.condDen_fin2]; simp [Fin.sum_univ_three, Po_apply, Pofun] <;> norm_num

theorem pva_00 : game.pva 0 0 = 1 / 4 := by
  unfold Game.pva; rw [Game.condNum_fin2]; simp [Fin.sum_univ_three, Po_apply, Pofun, U_apply, Ufun] <;> norm_num
theorem pva_01 : game.pva 0 1 = 1 / 4 := by
  unfold Game.pva; rw [Game.condNum_fin2]; simp [Fin.sum_univ_three, Po_apply, Pofun, U_apply, Ufun] <;> norm_num
theorem pva_02 : game.pva 0 2 = 0 := by
  unfold Game.pva; rw [Game.condNum_fin2]; simp [Fin.sum_univ_three, Po_apply, Pofun, U_apply, Ufun] <;> norm_num
theorem pva_10 : game.pva 1 0 = 0 := by
  unfold Game.pva; rw [Game.condNum_fin2]; simp [Fin.sum_univ_three, Po_apply, Pofun, U_apply, Ufun] <;> norm_num
theorem pva_11 : game.pva 1 1 = 1 / 4 := by
  unfold Game.pva; rw [Game.condNum_fin2]; simp [Fin.sum_univ_three, Po_apply, Pofun, U_apply, Ufun] <;> norm_num
theorem pva_12 : game.pva 1 2 = 1 / 4 := by
  unfold Game.pva; rw [Game.condNum_fin2]; simp [Fin.sum_univ_three, Po_apply, Pofun, U_apply, Ufun] <;> norm_num

/-! ### The conditional under `μ_π`, and availability -/

theorem cond_eq (π : Fin 2 → Fin 3) (s : Fin 2) (a : Fin 3) :
    game.cond (game.muSelf π) s a =
      ((1 - 3 / 4) * (if π s = a then Ufun π else 0) + 3 / 4 * game.pva s a) /
        ((1 - 3 / 4) * (if π s = a then 1 else 0) + 3 / 4 * game.pa s a) := by
  unfold Game.cond; rw [Game.condNum_muSelf, Game.condDen_muSelf]; rfl

theorem avail_of_pa_pos (π : Fin 2 → Fin 3) {s : Fin 2} {b : Fin 3} (hpa : 0 < game.pa s b) :
    avail (game.muSelf π) s b := by
  unfold avail; rw [Game.condDen_muSelf, δ_eq]; split_ifs <;> linarith

theorem not_avail_of (π : Fin 2 → Fin 3) {s : Fin 2} {b : Fin 3} (hpa : game.pa s b = 0)
    (hne : π s ≠ b) : ¬ avail (game.muSelf π) s b := by
  unfold avail; rw [Game.condDen_muSelf, δ_eq, if_neg hne, hpa]; norm_num

/-! ### `ac` is a (strict) pure Herrmann fixed point of utility `0` -/

/-- The own policy `ac`. -/
def polAC : Fin 2 → Fin 3 := ![0, 2]

theorem U_ac : game.U polAC = 0 := by simp [U_apply, Ufun, polAC]

theorem cond_ac_00 : game.cond (game.muSelf polAC) 0 0 = 3 / 7 := by
  rw [cond_eq]; simp [polAC, pa_00, pva_00, Ufun]; norm_num
theorem cond_ac_01 : game.cond (game.muSelf polAC) 0 1 = 1 / 3 := by
  rw [cond_eq]; simp [polAC, pa_01, pva_01]; norm_num
theorem cond_ac_12 : game.cond (game.muSelf polAC) 1 2 = 3 / 7 := by
  rw [cond_eq]; simp [polAC, pa_12, pva_12, Ufun]; norm_num
theorem cond_ac_11 : game.cond (game.muSelf polAC) 1 1 = 1 / 3 := by
  rw [cond_eq]; simp [polAC, pa_11, pva_11]; norm_num

theorem not_avail_ac_02 : ¬ avail (game.muSelf polAC) 0 2 :=
  not_avail_of polAC pa_02 (by simp [polAC])
theorem not_avail_ac_10 : ¬ avail (game.muSelf polAC) 1 0 :=
  not_avail_of polAC pa_10 (by simp [polAC])

/-- `ac` is a pure Herrmann fixed point (strict at both situations: `1/3 < 3/7`). -/
theorem isPureFP_ac : game.IsPureFP polAC := by
  intro s
  fin_cases s
  · refine ⟨game.avail_muSelf_self polAC 0, ?_⟩
    show ∀ b, avail (game.muSelf polAC) 0 b →
      game.cond (game.muSelf polAC) 0 b ≤ game.cond (game.muSelf polAC) 0 (polAC 0)
    have h0 : polAC 0 = 0 := rfl
    rw [h0, cond_ac_00]
    simp only [forall_fin_three]
    exact ⟨fun _ => by rw [cond_ac_00], fun _ => by rw [cond_ac_01]; norm_num,
      fun hb => absurd hb not_avail_ac_02⟩
  · refine ⟨game.avail_muSelf_self polAC 1, ?_⟩
    show ∀ b, avail (game.muSelf polAC) 1 b →
      game.cond (game.muSelf polAC) 1 b ≤ game.cond (game.muSelf polAC) 1 (polAC 1)
    have h1 : polAC 1 = 2 := rfl
    rw [h1, cond_ac_12]
    simp only [forall_fin_three]
    exact ⟨fun hb => absurd hb not_avail_ac_10, fun _ => by rw [cond_ac_11]; norm_num,
      fun _ => by rw [cond_ac_12]⟩

/-- `ac` is strict: every other available action has a strictly smaller conditional. -/
theorem strict_ac : ∀ s b, avail (game.muSelf polAC) s b → b ≠ polAC s →
    game.cond (game.muSelf polAC) s b < game.cond (game.muSelf polAC) s (polAC s) := by
  intro s b hb hne
  fin_cases s <;> fin_cases b
  · exact absurd rfl hne
  · show game.cond _ 0 1 < game.cond _ 0 0; rw [cond_ac_01, cond_ac_00]; norm_num
  · exact absurd hb not_avail_ac_02
  · exact absurd hb not_avail_ac_10
  · show game.cond _ 1 1 < game.cond _ 1 2; rw [cond_ac_11, cond_ac_12]; norm_num
  · exact absurd rfl hne

/-! ### No pure policy is an extension fixed point -/

theorem not_isFPext_of {π : Fin 2 → Fin 3} {s : Fin 2} {b : Fin 3}
    (h : game.Fext (pureMix π) s (π s) < game.Fext (pureMix π) s b) : ¬ game.IsFPext (pureMix π) := by
  intro hfp
  have := hfp.2 s (π s) (Game.pureMix_self_pos π s) b
  linarith

/-- Losing to an *available* deviation (the Herrmann failure, which the extension inherits). -/
theorem not_ext_avail (π : Fin 2 → Fin 3) (s : Fin 2) (b : Fin 3) (hpa : 0 < game.pa s b)
    (h : game.cond (game.muSelf π) s (π s) < game.cond (game.muSelf π) s b) :
    ¬ game.IsFPext (pureMix π) := by
  apply not_isFPext_of (s := s) (b := b)
  rw [game.Fext_pureMix_self, game.Fext_pureMix π (avail_of_pa_pos π hpa)]
  exact h

/-- Losing to an *unavailable* deviation, whose extended conditional is the deviation's own utility. -/
theorem not_ext_unavail (π : Fin 2 → Fin 3) (s : Fin 2) (b : Fin 3) (hpa : game.pa s b = 0)
    (h : game.cond (game.muSelf π) s (π s) < game.U (Function.update π s b)) :
    ¬ game.IsFPext (pureMix π) := by
  apply not_isFPext_of (s := s) (b := b)
  rw [game.Fext_pureMix_self, game.Fext_eq_Ucoord_of_pa_eq_zero _ hpa, game.Ucoord_pureMix]
  exact h

/-- **No pure policy is an extension fixed point.** -/
theorem no_pure_ext_fp : ∀ π : Fin 2 → Fin 3, ¬ game.IsFPext (pureMix π) := by
  have hrep : ∀ π : Fin 2 → Fin 3, π = ![π 0, π 1] := fun π => by
    funext i; fin_cases i <;> rfl
  intro π
  rw [hrep π]
  generalize π 0 = x; generalize π 1 = y
  revert x y
  simp only [forall_fin_three]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  -- aa: at s₁, b (available, `1/3 > 0`)
  · refine not_ext_avail _ 1 1 (by rw [pa_11]; norm_num) ?_
    rw [cond_eq, cond_eq]; simp [pa_10, pa_11, pva_10, pva_11, Ufun]
  -- ab: at s₁, c (available, `1 > 7/13`)
  · refine not_ext_avail _ 1 2 (by rw [pa_12]; norm_num) ?_
    rw [cond_eq, cond_eq]; simp [pa_11, pa_12, pva_11, pva_12, Ufun]; norm_num
  -- ac: at s₀, c (UNAVAILABLE, `U(cc) = 1/2 > 3/7`) — the Herrmann fixed point fails only here
  · refine not_ext_unavail _ 0 2 pa_02 ?_
    have hupd : Function.update (![0, 2] : Fin 2 → Fin 3) 0 2 = ![2, 2] := by
      funext i; fin_cases i <;> rfl
    rw [cond_eq, hupd]; simp [pa_00, pva_00, U_apply, Ufun]; norm_num
  -- ba: at s₀, a (available, `1 > 3/13`)
  · refine not_ext_avail _ 0 0 (by rw [pa_00]; norm_num) ?_
    rw [cond_eq, cond_eq]; simp [pa_00, pa_01, pva_00, pva_01, Ufun]; norm_num
  -- bb: at s₀, a
  · refine not_ext_avail _ 0 0 (by rw [pa_00]; norm_num) ?_
    rw [cond_eq, cond_eq]; simp [pa_00, pa_01, pva_00, pva_01, Ufun]; norm_num
  -- bc: at s₀, a (`1 > 7/13`)
  · refine not_ext_avail _ 0 0 (by rw [pa_00]; norm_num) ?_
    rw [cond_eq, cond_eq]; simp [pa_00, pa_01, pva_00, pva_01, Ufun]; norm_num
  -- ca: at s₀, a (`1 > 0`)
  · refine not_ext_avail _ 0 0 (by rw [pa_00]; norm_num) ?_
    rw [cond_eq, cond_eq]; simp [pa_00, pa_02, pva_00, pva_02, Ufun]
  -- cb: at s₀, a
  · refine not_ext_avail _ 0 0 (by rw [pa_00]; norm_num) ?_
    rw [cond_eq, cond_eq]; simp [pa_00, pa_02, pva_00, pva_02, Ufun]
  -- cc: at s₀, a (`1 > 1/2`)
  · refine not_ext_avail _ 0 0 (by rw [pa_00]; norm_num) ?_
    rw [cond_eq, cond_eq]; simp [pa_00, pa_02, pva_00, pva_02, Ufun]; norm_num

/-- **The inclusion conjecture is false**: a game at `δ = 3/4` with a pure Herrmann fixed point and no
pure extension fixed point. -/
theorem inclusion_conjecture_refuted :
    ∃ G : Game (Fin 2) (Fin 3), G.δ = 3 / 4 ∧ (∃ π, G.IsPureFP π) ∧ ∀ π, ¬ G.IsFPext (pureMix π) :=
  ⟨game, rfl, ⟨polAC, isPureFP_ac⟩, no_pure_ext_fp⟩

/-- The universal form of `inclusion_open` (over `Type`) is false. -/
theorem not_inclusion :
    ¬ ∀ (S A : Type) [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] (G : Game S A),
        (∃ π, G.IsPureFP π) → ∃ π, G.IsFPext (pureMix π) := by
  intro h
  obtain ⟨π, hπ⟩ := h (Fin 2) (Fin 3) game ⟨polAC, isPureFP_ac⟩
  exact no_pure_ext_fp π hπ

end Cleanroom.Uea.UeaSelfGame.AuditR3.Inclusion
