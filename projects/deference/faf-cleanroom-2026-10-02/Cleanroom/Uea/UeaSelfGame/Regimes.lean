import Cleanroom.Uea.UeaSelfGame.Tables

/-!
# The two regimes of Theorem C's constant: `δ ≤ 1/2` and `δ > 1/2`

Repair round 2 of the `uea-self-game` package (faf-cleanroom run, 2026-10-01). The round-2 adversarial
audit (B1) found the OPEN statement `sup_limit_open` **false as previously written**: it asked, for every
`δ ∈ (0,1)`, for pure fixed points with the trust bound everywhere and gap `≥ δ/(1−δ) − ε`; but the gap
`U* − U(π)` of any policy is at most `1` (`U ∈ [0,1]`), while `δ/(1−δ) > 1` for `δ > 1/2`. The mandate's
target-6 sentence has the same omission. This module records the regimes:

* `Game.gap_le_one`: the gap is at most `1`, always.
* `sup_limit_previous_form_false_above_half`: the previous form's conclusion is unsatisfiable for every
  `δ ∈ (1/2, 1)` at some `ε > 0` (the auditor's probe `SupLimitFalse.lean`, statements unchanged). The
  statement restricted to `δ ≤ 1/2` is `T3Family.sup_limit`, proved (it was the OPEN `sup_limit_open`
  until the continuation of repair round 2).
* **Content regions** (the auditor's probe `TrivialRegions.lean`, statements unchanged): the conclusion of
  Theorems C, C′ and D, `U* − δ/(1−δ) ≤ U(π)`, holds for *every* policy of *every* game with `δ ≥ 1/2`
  (`theoremC_bound_trivial_of_half_le`), the strict form for `δ > 1/2`, and the conclusion of
  `floored_mixed_bound_open` for every mixed `σ` with `δ ≥ 1/3`. So those headlines have content exactly
  on `δ < U*/(1 + U*) ≤ 1/2` (resp. `δ < 1/3`); every N+ witness of the package sits there.
* **Above `1/2` the maximal gap `1` is attained** (`GapOne`): for every `δ ∈ [2/3, 1)` the three-situation
  instance `U = (aaa:0, aab:1, aba:1, else 0)`, `π* = aba`, `Po = w δ_{aab} + w δ_{aba} + θ δ_{bbb}` with
  `θ = (1−δ)/δ`, `w = (2δ−1)/(2δ)`, has `aaa` as a pure fixed point (strict at `s₀`, a tie at `s₁`, `s₂`)
  with the trust bound at every situation and gap exactly `1`. `GapOneAttained` is the auditor's exact
  instance at `δ = 3/4` (`θ = 1/2`), statement unchanged.

So the honest tightness statement is two-regime. For `δ ≤ 1/2`: `δ/(1−δ)` is an upper bound on the gap
never attained (`Attainment.theoremC_strict`) and it is the supremum (`T3Family.sup_limit`, proved from
the general `T3(n, θ, g)` family in the continuation of repair round 2; until then the OPEN
`sup_limit_open`). For `δ > 1/2`: Theorem C's bound is empty, and the supremum of the gap is the trivial
`1`, attained — proved here on `Fin 3` for `δ ≥ 2/3` (`GapOne.gap_one_attained`), and for every
`δ ∈ (1/2, 1)` by `T3Family.gap_one_attained_above_half`.

Scope: finite updateless self-game — pointwise EDT conditional on one's own action, self-consistent
belief; not rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30; repair round 2, 2026-10-01).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

namespace Game

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] (G : Game S A)

/-- The gap `U* − U(π)` of any policy in any game is at most `1` (utilities live in `[0,1]`).
Source: none: infrastructure (round-2 adversarial audit, probe `SupLimitFalse.gap_le_one`)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem gap_le_one (π : S → A) : G.Ustar - G.U π ≤ 1 := by
  have h1 := G.Ustar_le_one
  have h2 := G.U_nonneg π
  linarith

/-- **Content region of Theorem C's bound**: `U* − δ/(1−δ) ≤ U(π)` holds for *every* policy of *every* game
with `δ ≥ 1/2`, with no fixed-point or trust-bound hypothesis (`U* ≤ 1 ≤ δ/(1−δ)`, `U ≥ 0`). So Theorems C,
C′ and D say something only for `δ < U*/(1 + U*) ≤ 1/2`.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: round-2 adversarial audit N1 (probe `TrivialRegions.theoremC_bound_trivial_of_half_le`, statement unchanged); [[updateless-self-game]] §5 (Theorem C's constant)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem theoremC_bound_trivial_of_half_le (hδ : 1 / 2 ≤ G.δ) (π : S → A) :
    G.Ustar - G.δ / (1 - G.δ) ≤ G.U π := by
  have h1 := G.one_sub_δ_pos
  have hU := G.Ustar_le_one
  have hπ := G.U_nonneg π
  have : 1 ≤ G.δ / (1 - G.δ) := by
    rw [le_div_iff₀ h1]; linarith
  linarith

/-- **Content region of the strict form**: `theoremC_strict`'s conclusion holds for every policy when
`δ > 1/2`.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: round-2 adversarial audit N1 (probe `TrivialRegions.theoremC_strict_trivial_of_half_lt`, statement unchanged)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem theoremC_strict_trivial_of_half_lt (hδ : 1 / 2 < G.δ) (π : S → A) :
    G.Ustar - G.δ / (1 - G.δ) < G.U π := by
  have h1 := G.one_sub_δ_pos
  have hU := G.Ustar_le_one
  have hπ := G.U_nonneg π
  have : 1 < G.δ / (1 - G.δ) := by
    rw [lt_div_iff₀ h1]; linarith
  linarith

/-- **Content region of the open mixed floored bound**: the conclusion of `floored_mixed_bound_open`,
`U* − 2δ/(1−δ) ≤ U(σ)`, holds for every mixed `σ` of every game with `δ ≥ 1/3`, with no fixed-point
hypothesis; the open statement has content only for `δ < 1/3`.
Scope: finite updateless self-game — floored agent, continuous extension; not rOSI, not the sequential
model of `uea-cole-shadow`.
Source: round-2 adversarial audit N1 (probe `TrivialRegions.floored_open_bound_trivial_of_third_le`, statement unchanged); [[uea-self-game-mandate]] target 9 (f)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem floored_open_bound_trivial_of_third_le (hδ : 1 / 3 ≤ G.δ) (σ : S → A → ℝ) (hσ : IsMixed σ) :
    G.Ustar - 2 * G.δ / (1 - G.δ) ≤ G.Umix σ := by
  have h1 := G.one_sub_δ_pos
  have hU := G.Ustar_le_one
  have hσ0 : 0 ≤ G.Umix σ := by
    unfold Game.Umix
    exact Finset.sum_nonneg fun π' _ => mul_nonneg (prodW_nonneg hσ π') (G.U_nonneg π')
  have : 1 ≤ 2 * G.δ / (1 - G.δ) := by
    rw [le_div_iff₀ h1]; linarith
  linarith

end Game

/-- **The previous form of `sup_limit_open` was false**: for every `δ ∈ (1/2, 1)` there is an `ε > 0` for
which no `n`, game at `δ` and pure fixed point with the trust bound everywhere has gap `≥ δ/(1−δ) − ε`
(the gap is `≤ 1 < δ/(1−δ) − ε` at `ε := (δ/(1−δ) − 1)/2`). The statement quantified over all
`δ ∈ (0,1)` — the package's round-0/round-1 `sup_limit_open`, and the mandate's target-6 sentence — was
therefore refutable, not open; the OPEN statement now carries `δ ≤ 1/2`.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: round-2 adversarial audit B1 (probe `SupLimitFalse.sup_limit_conclusion_false_above_half`, statement unchanged); [[uea-self-game-mandate]] target 6 (`stretch`, the limit sentence, which omits `δ ≤ 1/2`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem sup_limit_previous_form_false_above_half (δ : ℝ) (hhalf : 1 / 2 < δ) (h1 : δ < 1) :
    ∃ ε : ℝ, 0 < ε ∧
      ¬ ∃ (n : ℕ) (G : Game (Fin n) (Fin 2)) (π : Fin n → Fin 2), G.δ = δ ∧ G.IsPureFP π ∧
        (∀ s, G.TB (G.muSelf π) s) ∧ δ / (1 - δ) - ε ≤ G.Ustar - G.U π := by
  have hgt : 1 < δ / (1 - δ) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  refine ⟨(δ / (1 - δ) - 1) / 2, by linarith, ?_⟩
  rintro ⟨n, G, π, -, -, -, hg⟩
  have := G.gap_le_one π
  linarith

/-! ### Above `δ = 1/2` the gap `1` is attained: the symbolic family on `Fin 3` for `δ ∈ [2/3, 1)` -/

namespace GapOne

variable {δ : ℝ} (h23 : 2 / 3 ≤ δ) (h1 : δ < 1)

/-- The polluter's weight `θ = (1−δ)/δ` (the least weight making `aaa` a fixed point at `s₁`, `s₂`).
Source: round-2 adversarial audit B1 (the `T3(3, θ, 1)` shape); [[uea-self-game-mandate]] target 6 (`T3`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def θ (δ : ℝ) : ℝ := (1 - δ) / δ

/-- Each deviation's weight `w = (1−θ)/2 = (2δ−1)/(2δ)`.
Source: round-2 adversarial audit B1 (the `T3(3, θ, 1)` shape)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def w (δ : ℝ) : ℝ := (2 * δ - 1) / (2 * δ)

include h23 h1 in
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem δ_pos : 0 < δ := by linarith

include h23 h1 in
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem θ_mem : 0 ≤ θ δ ∧ θ δ ≤ 1 := by
  unfold θ
  exact ⟨div_nonneg (by linarith) (by linarith), by rw [div_le_one (by linarith)]; linarith⟩

include h23 h1 in
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem w_mem : 0 ≤ w δ ∧ w δ ≤ 1 := by
  unfold w
  exact ⟨div_nonneg (by linarith) (by linarith), by rw [div_le_one (by linarith)]; linarith⟩

include h23 h1 in
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem two_w_add_θ : 2 * w δ + θ δ = 1 := by
  unfold w θ
  have : δ ≠ 0 := by linarith
  field_simp
  try ring

include h23 h1 in
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem δ_mul_w : δ * w δ = (2 * δ - 1) / 2 := by
  unfold w
  have : δ ≠ 0 := by linarith
  field_simp
  try ring

include h23 h1 in
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem δ_mul_θ : δ * θ δ = 1 - δ := by
  unfold θ
  have : δ ≠ 0 := by linarith
  field_simp
  try ring

/-- The instance: `U = (aaa:0, aab:1, aba:1, else 0)`, `piStar = aba`,
`Po = w δ_{aab} + w δ_{aba} + θ δ_{bbb}`, at `δ ∈ [2/3, 1)`.
Source: round-2 adversarial audit B1 (`GapOneAttained`, generalised in `δ`); [[uea-self-game-mandate]] target 6 (the `T3` shape with `g = 1`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def game : Game (Fin 3) (Fin 2) where
  U := tab3 0 1 1 0 0 0 0 0
  U_nonneg := fun π => (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).1
  U_le_one := fun π => (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  piStar := ![0, 1, 0]
  piStar_max := fun π => by
    rw [tab3_010]
    exact (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  Po := tab3 0 (w δ) (w δ) 0 0 0 0 (θ δ)
  Po_mem := ⟨fun π => (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (w_mem h23 h1) (w_mem h23 h1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (θ_mem h23 h1) π).1,
    by rw [sum_tab3]; linarith [two_w_add_θ h23 h1]⟩
  δ := δ
  δ_nonneg := by linarith
  δ_lt_one := h1

/-- The own policy `aaa`.
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
theorem U_apply (π) : (game h23 h1).U π = tab3 0 1 1 0 0 0 0 0 π := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem δ_eq : (game h23 h1).δ = δ := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ustar_eq : (game h23 h1).Ustar = 1 := by simp [Game.Ustar, game]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem thr_eq : (game h23 h1).thr = 1 - δ := by simp [Game.thr, Ustar_eq, δ_eq]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mu_apply (π') : (game h23 h1).muSelf pol π' =
    (1 - δ) * (if π' 0 = 0 ∧ π' 1 = 0 ∧ π' 2 = 0 then 1 else 0) +
      δ * tab3 0 (w δ) (w δ) 0 0 0 0 (θ δ) π' := by
  rw [Game.muSelf_apply_fin3]; rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_00 : condDen ((game h23 h1).muSelf pol) 0 0 = δ := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]
  linarith [δ_mul_w h23 h1]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_00 : (game h23 h1).condNum ((game h23 h1).muSelf pol) 0 0 = 2 * δ - 1 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]
  linarith [δ_mul_w h23 h1]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_01 : condDen ((game h23 h1).muSelf pol) 0 1 = 1 - δ := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]
  linarith [δ_mul_θ h23 h1]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_01 : (game h23 h1).condNum ((game h23 h1).muSelf pol) 0 1 = 0 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_10 : condDen ((game h23 h1).muSelf pol) 1 0 = 1 / 2 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]
  linarith [δ_mul_w h23 h1]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_10 : (game h23 h1).condNum ((game h23 h1).muSelf pol) 1 0 = (2 * δ - 1) / 2 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]
  linarith [δ_mul_w h23 h1]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_11 : condDen ((game h23 h1).muSelf pol) 1 1 = 1 / 2 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]
  linarith [δ_mul_w h23 h1, δ_mul_θ h23 h1]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_11 : (game h23 h1).condNum ((game h23 h1).muSelf pol) 1 1 = (2 * δ - 1) / 2 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]
  linarith [δ_mul_w h23 h1]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_20 : condDen ((game h23 h1).muSelf pol) 2 0 = 1 / 2 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]
  linarith [δ_mul_w h23 h1]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_20 : (game h23 h1).condNum ((game h23 h1).muSelf pol) 2 0 = (2 * δ - 1) / 2 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]
  linarith [δ_mul_w h23 h1]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_21 : condDen ((game h23 h1).muSelf pol) 2 1 = 1 / 2 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]
  linarith [δ_mul_w h23 h1, δ_mul_θ h23 h1]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_21 : (game h23 h1).condNum ((game h23 h1).muSelf pol) 2 1 = (2 * δ - 1) / 2 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]
  linarith [δ_mul_w h23 h1]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_00 : (game h23 h1).cond ((game h23 h1).muSelf pol) 0 0 = (2 * δ - 1) / δ := by
  unfold Game.cond; rw [condNum_00, condDen_00]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_01 : (game h23 h1).cond ((game h23 h1).muSelf pol) 0 1 = 0 := by
  unfold Game.cond; rw [condNum_01, zero_div]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_10 : (game h23 h1).cond ((game h23 h1).muSelf pol) 1 0 = 2 * δ - 1 := by
  unfold Game.cond; rw [condNum_10, condDen_10]; ring

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_11 : (game h23 h1).cond ((game h23 h1).muSelf pol) 1 1 = 2 * δ - 1 := by
  unfold Game.cond; rw [condNum_11, condDen_11]; ring

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_20 : (game h23 h1).cond ((game h23 h1).muSelf pol) 2 0 = 2 * δ - 1 := by
  unfold Game.cond; rw [condNum_20, condDen_20]; ring

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_21 : (game h23 h1).cond ((game h23 h1).muSelf pol) 2 1 = 2 * δ - 1 := by
  unfold Game.cond; rw [condNum_21, condDen_21]; ring

/-- Every action is available at every situation (the instance is convention-free).
Source: round-2 adversarial audit B1
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem avail_all : ∀ s a, avail ((game h23 h1).muSelf pol) s a := by
  unfold avail
  simp only [forall_fin_three, Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [condDen_00]; linarith
  · rw [condDen_01]; linarith
  · rw [condDen_10]; norm_num
  · rw [condDen_11]; norm_num
  · rw [condDen_20]; norm_num
  · rw [condDen_21]; norm_num

/-- **`aaa` is a pure fixed point** at every `δ ∈ [2/3, 1)`: strict at `s₀` (`(2δ−1)/δ > 0`), a tie at `s₁`
and `s₂` (both conditionals `2δ − 1`).
Source: round-2 adversarial audit B1 (`GapOneAttained.isPureFP`, generalised in `δ`)
Kind: N+
Fidelity: exact (symbolic `δ`)
Hyps: (a) -/
theorem isPureFP : (game h23 h1).IsPureFP pol := by
  unfold Game.IsPureFP Game.IsArgmaxH
  simp only [forall_fin_three, Fin.forall_fin_two, pol_0, pol_1, pol_2]
  refine ⟨⟨avail_all h23 h1 0 0, fun _ => le_rfl, fun _ => ?_⟩,
    ⟨avail_all h23 h1 1 0, fun _ => le_rfl, fun _ => ?_⟩,
    ⟨avail_all h23 h1 2 0, fun _ => le_rfl, fun _ => ?_⟩⟩
  · rw [cond_00, cond_01]; exact div_nonneg (by linarith) (by linarith)
  · rw [cond_10, cond_11]
  · rw [cond_20, cond_21]

/-- **The trust bound holds at every situation**: `(2δ−1)/δ ≥ 1−δ` at `s₀` (as `δ² + δ − 1 ≥ 0` for
`δ ≥ 2/3`) and `2δ − 1 ≥ 1 − δ` at `s₁`, `s₂` (equality at `δ = 2/3`).
Source: round-2 adversarial audit B1 (`GapOneAttained.TB_all`, generalised in `δ`)
Kind: N+
Fidelity: exact (symbolic `δ`)
Hyps: (a) -/
theorem TB_all : ∀ s, (game h23 h1).TB ((game h23 h1).muSelf pol) s := by
  simp only [forall_fin_three]
  unfold Game.TB
  rw [thr_eq]
  refine ⟨⟨0, avail_all h23 h1 0 0, ?_⟩, ⟨0, avail_all h23 h1 1 0, ?_⟩, ⟨0, avail_all h23 h1 2 0, ?_⟩⟩
  · rw [cond_00, le_div_iff₀ (δ_pos h23 h1)]
    nlinarith [mul_le_mul_of_nonneg_left h23 (δ_pos h23 h1).le]
  · rw [cond_10]; linarith
  · rw [cond_20]; linarith

/-- The gap is exactly `1`, the largest any policy can have.
Source: round-2 adversarial audit B1
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem gap : (game h23 h1).Ustar - (game h23 h1).U pol = 1 := by
  rw [Ustar_eq, U_apply]; simp [pol]

/-- **Above `δ = 1/2` the maximal gap `1` is attained** (for every `δ ∈ [2/3, 1)`): a three-situation game
at `δ` with a pure fixed point, the trust bound at every situation, and gap `U* − U(π) = 1`. So on this
range the supremum of the gap over pure fixed points with the trust bound everywhere is `1`, attained —
and Theorem C's constant `δ/(1−δ) > 1` is not the truth there (`theoremC_strict`'s strictness is the
empty one of `theoremC_strict_trivial_of_half_lt`).
Scope: finite updateless self-game — pointwise EDT conditional on one's own action, self-consistent
belief; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: round-2 adversarial audit B1 ("for `δ > 1/2` the supremum of the gap is `1` and it is attained"); [[uea-self-game-mandate]] target 6 (the `stretch` limit, corrected)
Kind: P
Fidelity: exact (symbolic `δ ∈ [2/3, 1)`; `T3Family.gap_one_attained_above_half` covers all of `(1/2, 1)`)
Hyps: (a) -/
theorem gap_one_attained (δ : ℝ) (h23 : 2 / 3 ≤ δ) (h1 : δ < 1) :
    ∃ (G : Game (Fin 3) (Fin 2)) (π : Fin 3 → Fin 2), G.δ = δ ∧ G.IsPureFP π ∧
      (∀ s, G.TB (G.muSelf π) s) ∧ G.Ustar - G.U π = 1 :=
  ⟨game h23 h1, pol, rfl, isPureFP h23 h1, TB_all h23 h1, gap h23 h1⟩

end GapOne

/-! ### The auditor's exact instance at `δ = 3/4` (`θ = 1/2`), statement unchanged -/

namespace GapOneAttained

/-- The instance: `U = (aaa:0, aab:1, aba:1, else 0)`, `π* = aba`, `Po = ¼ δ_{aab} + ¼ δ_{aba} + ½ δ_{bbb}`,
`δ = 3/4`.
Source: round-2 adversarial audit B1 (probe `GapOneAttained.game`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def game : Game (Fin 3) (Fin 2) where
  U := tab3 0 1 1 0 0 0 0 0
  U_nonneg := fun π => (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).1
  U_le_one := fun π => (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  piStar := ![0, 1, 0]
  piStar_max := fun π => by
    rw [tab3_010]
    exact (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  Po := tab3 0 (1 / 4) (1 / 4) 0 0 0 0 (1 / 2)
  Po_mem := ⟨fun π => (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).1,
    by rw [sum_tab3]; norm_num⟩
  δ := 3 / 4
  δ_nonneg := by norm_num
  δ_lt_one := by norm_num

/-- The own policy `aaa`.
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
theorem U_apply (π) : game.U π = tab3 0 1 1 0 0 0 0 0 π := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem δ_eq : game.δ = 3 / 4 := rfl

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
theorem thr_eq : game.thr = 1 / 4 := by simp [Game.thr, Ustar_eq, δ_eq]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mu_apply (π') : game.muSelf pol π' =
    (1 - 3 / 4) * (if π' 0 = 0 ∧ π' 1 = 0 ∧ π' 2 = 0 then 1 else 0) +
      3 / 4 * tab3 0 (1 / 4) (1 / 4) 0 0 0 0 (1 / 2) π' := by
  rw [Game.muSelf_apply_fin3]; rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_00 : condDen (game.muSelf pol) 0 0 = 5 / 8 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_00 : game.condNum (game.muSelf pol) 0 0 = 3 / 8 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_01 : condDen (game.muSelf pol) 0 1 = 3 / 8 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_01 : game.condNum (game.muSelf pol) 0 1 = 0 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_10 : condDen (game.muSelf pol) 1 0 = 7 / 16 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_10 : game.condNum (game.muSelf pol) 1 0 = 3 / 16 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_11 : condDen (game.muSelf pol) 1 1 = 9 / 16 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_11 : game.condNum (game.muSelf pol) 1 1 = 3 / 16 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_20 : condDen (game.muSelf pol) 2 0 = 7 / 16 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_20 : game.condNum (game.muSelf pol) 2 0 = 3 / 16 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_21 : condDen (game.muSelf pol) 2 1 = 9 / 16 := by
  rw [Game.condDen_fin3]; simp [Fin.sum_univ_two, mu_apply]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_21 : game.condNum (game.muSelf pol) 2 1 = 3 / 16 := by
  rw [Game.condNum_fin3]; simp [Fin.sum_univ_two, mu_apply, U_apply]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_00 : game.cond (game.muSelf pol) 0 0 = 3 / 5 := by
  unfold Game.cond; rw [condNum_00, condDen_00]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_01 : game.cond (game.muSelf pol) 0 1 = 0 := by
  unfold Game.cond; rw [condNum_01, zero_div]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_10 : game.cond (game.muSelf pol) 1 0 = 3 / 7 := by
  unfold Game.cond; rw [condNum_10, condDen_10]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_11 : game.cond (game.muSelf pol) 1 1 = 1 / 3 := by
  unfold Game.cond; rw [condNum_11, condDen_11]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_20 : game.cond (game.muSelf pol) 2 0 = 3 / 7 := by
  unfold Game.cond; rw [condNum_20, condDen_20]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_21 : game.cond (game.muSelf pol) 2 1 = 1 / 3 := by
  unfold Game.cond; rw [condNum_21, condDen_21]; norm_num

/-- Every action is available at every situation.
Source: round-2 adversarial audit B1 (probe)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem avail_all : ∀ s a, avail (game.muSelf pol) s a := by
  unfold avail
  simp only [forall_fin_three, Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [condDen_00]; norm_num
  · rw [condDen_01]; norm_num
  · rw [condDen_10]; norm_num
  · rw [condDen_11]; norm_num
  · rw [condDen_20]; norm_num
  · rw [condDen_21]; norm_num

/-- `aaa` is a pure fixed point (strict at every situation).
Source: round-2 adversarial audit B1 (probe `GapOneAttained.isPureFP`, statement unchanged)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem isPureFP : game.IsPureFP pol := by
  unfold Game.IsPureFP Game.IsArgmaxH
  simp only [forall_fin_three, Fin.forall_fin_two, pol_0, pol_1, pol_2]
  refine ⟨⟨avail_all 0 0, fun _ => le_rfl, fun _ => ?_⟩,
    ⟨avail_all 1 0, fun _ => le_rfl, fun _ => ?_⟩,
    ⟨avail_all 2 0, fun _ => le_rfl, fun _ => ?_⟩⟩
  · rw [cond_00, cond_01]; norm_num
  · rw [cond_10, cond_11]; norm_num
  · rw [cond_20, cond_21]; norm_num

/-- The trust bound holds at every situation (`thr = 1/4`).
Source: round-2 adversarial audit B1 (probe `GapOneAttained.TB_all`, statement unchanged)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem TB_all : ∀ s, game.TB (game.muSelf pol) s := by
  simp only [forall_fin_three]
  unfold Game.TB
  rw [thr_eq]
  exact ⟨⟨0, avail_all 0 0, by rw [cond_00]; norm_num⟩,
    ⟨0, avail_all 1 0, by rw [cond_10]; norm_num⟩,
    ⟨0, avail_all 2 0, by rw [cond_20]; norm_num⟩⟩

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem gap : game.Ustar - game.U pol = 1 := by
  rw [Ustar_eq, U_apply]; simp [pol]

/-- **At `δ = 3/4` the gap `1` is attained** by a pure fixed point with the trust bound everywhere.
Source: round-2 adversarial audit B1 (probe `GapOneAttained.gap_one_attained`, statement unchanged)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem gap_one_attained :
    ∃ (G : Game (Fin 3) (Fin 2)) (π : Fin 3 → Fin 2), G.δ = 3 / 4 ∧ G.IsPureFP π ∧
      (∀ s, G.TB (G.muSelf π) s) ∧ G.Ustar - G.U π = 1 :=
  ⟨game, pol, rfl, isPureFP, TB_all, gap⟩

/-- Theorem C's bound on this instance reads `−2 ≤ 0`: true and empty.
Source: round-2 adversarial audit B1 (probe `GapOneAttained.theoremC_bound_here`, statement unchanged)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem theoremC_bound_here : game.Ustar - game.δ / (1 - game.δ) = -2 := by
  rw [Ustar_eq, δ_eq]; norm_num

end GapOneAttained

end Cleanroom.Uea.UeaSelfGame
