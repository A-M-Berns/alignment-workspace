import Cleanroom.Uea.UeaSelfGame.TheoremA
import Cleanroom.Uea.UeaSelfGame.Tightness
import Cleanroom.Uea.UeaSelfGame.ChosenEnacted

/-!
# Non-vacuity witnesses for Theorems B, D (pure), E and the converse of Theorem B

Repair round 1 of the `uea-self-game` package (faf-cleanroom run, 2026-09-30). Both round-1 audits found
that `theoremB`, `theoremD_pure` and `theoremE` shipped no instance inhabiting their full hypothesis
packages, and that the ledger's claim "any `theoremC` witness is a floored fixed point" is false for `T1`.
This module ships the witnesses (the adversarial auditor's probes, moved into the library with their
statements unchanged) and the negative record for `T1`:

* **Theorem B** (`TheoremBWitness`): Theorem A's table with `η` *fixed* at `1/100` and `δ = 1/200`.
  `HasMargin (1/100)` holds and is tight at `s₀`; the deviation `b` is *available* at both situations with
  conditional `99/100 < 1 − δ ≤ cond(a)`, so Theorem B's strict comparison is a real comparison (contrast
  the degenerate shape `Po = δ_{π*}`, where no deviation is available and `HasMargin m` holds for every
  `m` — `hasMargin_all`, `no_deviation_available`, recorded here as well).
* **Converse of Theorem B** (`ConverseWitness`): the note's `U = (aa:1, ab:0, ba:0, bb:1)`,
  `Po = (1/8) δ_{ba} + (7/8) δ_{bb}`, `δ = 1/10`: margin `0` at `(s₁, b)`; `b` is available at `s₁` with
  conditional `1 > 72/73 = cond(a)`, so `π*(s₁) = a` is *not* an argmax there and `π* = aa` is not realized;
  the deviation `ab` is.
* **Theorem D (pure)** (`T2.isPureFPfloored`): `T2` at every `δ ∈ (0,1)` is a pure floored fixed point —
  through the **equality** branch at `s₀`, `s₁` (`cond = 1 − δ = thr`) and the argmax branch at `s₂` —
  with gap `δ` (N+). `T1.not_isPureFPfloored`: `T1` is *not* one (reset branch at `s₁`, where it plays `b`),
  so the floored hypothesis is not automatic from Theorem C's package.
* **Theorem E** (`TheoremEWitness`): `S = A = Fin 2`, `U = (aa:1, else 0)`, `δ = 1/10`: `ρ = 1/10`,
  `HasMarginC1 1`, `2ρ < 1`; every deviation is available under the C1 belief (mass `δ`).
* **Theorem A, support clause** (`TheoremA.Po_pos_iff`, `theoremA_supp`): the existential of
  `TheoremA.theoremA` restated with the conjunct `supp Po = {ab, bb}` (`|supp Po| = 2`), so the N+ grade
  is machine-stated. **`Bel` row** (`TheoremA.realized_not_bel_max`): the realized policy does not maximize
  `(1−δ) U + δ E_{Po} U` (the `E_{Po}` term is constant, so this is `U(ba) < U(aa)`: an `L` row).

Scope: finite updateless self-game — pointwise EDT conditional on one's own action; static belief
(Theorem B), self-consistent belief with the floor (Theorem D), the C1 product belief (Theorem E); not
rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30, repair round 1).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

/-! ### The degenerate shape of the margin hypothesis -/

namespace Game

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] (G : Game S A)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_dev_eq_zero (hPo : ∀ π', G.Po π' = if π' = G.piStar then 1 else 0) {s : S} {a' : A}
    (hne : a' ≠ G.piStar s) : G.pa s a' = 0 := by
  unfold Game.pa condDen
  refine Finset.sum_eq_zero fun π' _ => ?_
  rw [hPo π']
  split_ifs with h1 h2
  · subst h2; exact absurd h1.symm hne
  · rfl
  · rfl

/-- **The margin hypothesis's degenerate shape**: with `Po = δ_{π*}`, `HasMargin m` holds for every real
`m` (the note's "`m = +∞`") — there is no pair `(s, a')` with `a' ≠ π*(s)` and `Po(π'(s) = a') > 0`.
Source: [[updateless-self-game]] §4 ("`m := +∞`"); round-1 adversarial audit B1
Kind: N−
Fidelity: exact
Hyps: (a) -/
theorem hasMargin_all (hPo : ∀ π', G.Po π' = if π' = G.piStar then 1 else 0) (m : ℝ) : G.HasMargin m := by
  intro s a' hne hpa
  exfalso
  rw [G.pa_dev_eq_zero hPo hne] at hpa
  exact lt_irrefl _ hpa

/-- In the degenerate shape no deviation is available under `mu`, so "the unique realized policy is `π*`"
is forced by availability alone — the N− reading of Theorem B's conclusion, which `TheoremBWitness`
excludes.
Source: [[updateless-self-game]] §4; round-1 adversarial audit B1
Kind: N−
Fidelity: exact
Hyps: (a) -/
theorem no_deviation_available (hPo : ∀ π', G.Po π' = if π' = G.piStar then 1 else 0) (s : S) (a' : A)
    (hne : a' ≠ G.piStar s) : ¬ avail G.mu s a' := by
  rw [G.avail_mu_ne_iff hne, G.pa_dev_eq_zero hPo hne]
  rintro ⟨_, h⟩
  exact lt_irrefl _ h

end Game

/-! ### Theorem B: Theorem A's table at fixed `η = 1/100`, `δ = 1/200` -/

namespace TheoremBWitness

/-- Theorem A's table at fixed `η = 1/100`: `U = (aa:1, ab:0, ba:0, bb:99/100)`, `Po = ½ δ_{ab} + ½ δ_{bb}`,
`δ = 1/200 < η`.
Source: [[updateless-self-game]] §4 (the witness named after Theorem B); [[uea-self-game-mandate]] target 4
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def game : Game (Fin 2) (Fin 2) where
  U := tab2 1 0 0 (99 / 100)
  U_nonneg := fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) π).1
  U_le_one := fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) π).2
  piStar := ![0, 0]
  piStar_max := fun π => by
    rw [tab2_00]
    exact (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  Po := tab2 0 (1 / 2) 0 (1 / 2)
  Po_mem := ⟨fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) π).1, by rw [sum_tab2]; norm_num⟩
  δ := 1 / 200
  δ_nonneg := by norm_num
  δ_lt_one := by norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem U_apply (π) : game.U π = tab2 1 0 0 (99 / 100) π := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Po_apply (π) : game.Po π = tab2 0 (1 / 2) 0 (1 / 2) π := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem δ_eq : game.δ = 1 / 200 := rfl

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
theorem pa_01 : game.pa 0 1 = 1 / 2 := by
  unfold Game.pa condDen; rw [sum_fin2_arrow]
  simp [Fin.sum_univ_two, Po_apply, tab2]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_01 : game.pva 0 1 = 99 / 200 := by
  unfold Game.pva Game.condNum; rw [sum_fin2_arrow]
  simp [Fin.sum_univ_two, Po_apply, U_apply, tab2]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_11 : game.pa 1 1 = 1 := by
  unfold Game.pa condDen; rw [sum_fin2_arrow]
  simp [Po_apply, tab2]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_11 : game.pva 1 1 = 99 / 200 := by
  unfold Game.pva Game.condNum; rw [sum_fin2_arrow]
  simp [Fin.sum_univ_two, Po_apply, U_apply, tab2]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem piStar_apply (s : Fin 2) : game.piStar s = 0 := by fin_cases s <;> rfl

/-- The margin hypothesis, tight at `s₀`: `pva/pa = 99/100 = U* − 1/100` exactly.
Source: [[updateless-self-game]] §4 (`P_o`-margin)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem hasMargin : game.HasMargin (1 / 100) := by
  intro s a' hne hpa
  rw [piStar_apply] at hne
  fin_cases a'
  · exact absurd rfl hne
  · fin_cases s
    · show game.pva 0 1 / game.pa 0 1 ≤ game.Ustar - 1 / 100
      rw [pva_01, pa_01, Ustar_eq]; norm_num
    · show game.pva 1 1 / game.pa 1 1 ≤ game.Ustar - 1 / 100
      rw [pva_11, pa_11, Ustar_eq]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ustar_pos : 0 < game.Ustar := by rw [Ustar_eq]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem δ_lt : game.δ < (1 / 100) / game.Ustar := by rw [Ustar_eq, δ_eq]; norm_num

/-- **Theorem B on its witness**: the full package `HasMargin (1/100) ∧ 0 < U* ∧ δ < m/U*` is inhabited,
and the conclusion evaluates to: the unique realized policy is `π* = aa`, and it is realized.
Source: [[updateless-self-game]] §4 (Theorem B); [[uea-self-game-mandate]] target 4 (the fixed-`η` witness)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem theoremB_on_witness :
    game.Realizes game.mu game.piStar ∧ ∀ π, game.Realizes game.mu π → π = game.piStar :=
  ⟨game.theoremB_realizes_piStar hasMargin Ustar_pos δ_lt,
   game.theoremB_realizes hasMargin Ustar_pos δ_lt⟩

/-- **N+**: the deviation `b` is available at both situations under `mu`, so Theorem B's strictness is a
real comparison, not the vacuous case of an unavailable deviation (`no_deviation_available`).
Source: [[updateless-self-game]] §4; round-1 adversarial audit B1
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem deviation_available (s : Fin 2) : avail game.mu s 1 := by
  rw [game.avail_mu_ne_iff (by rw [piStar_apply]; decide)]
  refine ⟨by rw [δ_eq]; norm_num, ?_⟩
  fin_cases s
  · show (0 : ℝ) < game.pa 0 1
    rw [pa_01]; norm_num
  · show (0 : ℝ) < game.pa 1 1
    rw [pa_11]; norm_num

/-- The deviation's conditional at `s₀` is exactly `99/100 < 1 − δ = 199/200 ≤ cond(a)`: the strict
comparison Theorem B asserts, evaluated.
Source: [[updateless-self-game]] §4
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem cond_dev_0 : game.cond game.mu 0 1 = 99 / 100 := by
  rw [game.cond_mu_ne (by rw [piStar_apply]; decide) (deviation_available 0), pva_01, pa_01]
  norm_num

end TheoremBWitness

/-! ### Converse of Theorem B: the note's margin-zero instance -/

namespace ConverseWitness

/-- The note's converse instance: `U = (aa:1, ab:0, ba:0, bb:1)`, `Po = (1/8) δ_{ba} + (7/8) δ_{bb}`,
`piStar = aa` (a chosen maximizer; `bb` is the other), `δ = 1/10`. Margin `0` at `(s₁, b)`: all `Po`-mass
playing `b` at `s₁` sits on `bb`, which is optimal.
Source: [[updateless-self-game]] §4 ("Converse")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def game : Game (Fin 2) (Fin 2) where
  U := tab2 1 0 0 1
  U_nonneg := fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) π).1
  U_le_one := fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) π).2
  piStar := ![0, 0]
  piStar_max := fun π => by
    rw [tab2_00]
    exact (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  Po := tab2 0 0 (1 / 8) (7 / 8)
  Po_mem := ⟨fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) π).1, by rw [sum_tab2]; norm_num⟩
  δ := 1 / 10
  δ_nonneg := by norm_num
  δ_lt_one := by norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem U_apply (π) : game.U π = tab2 1 0 0 1 π := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Po_apply (π) : game.Po π = tab2 0 0 (1 / 8) (7 / 8) π := rfl

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
theorem Ustar_eq : game.Ustar = 1 := by simp [Game.Ustar, game]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem piStar_apply (s : Fin 2) : game.piStar s = 0 := by fin_cases s <;> rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_00 : game.pa 0 0 = 0 := by
  unfold Game.pa condDen; rw [sum_fin2_arrow]
  simp [Fin.sum_univ_two, Po_apply, tab2]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_00 : game.pva 0 0 = 0 := by
  unfold Game.pva Game.condNum; rw [sum_fin2_arrow]
  simp [Fin.sum_univ_two, Po_apply, U_apply, tab2]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_01 : game.pa 0 1 = 1 := by
  unfold Game.pa condDen; rw [sum_fin2_arrow]
  simp [Fin.sum_univ_two, Po_apply, tab2]; norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_01 : game.pva 0 1 = 7 / 8 := by
  unfold Game.pva Game.condNum; rw [sum_fin2_arrow]
  simp [Fin.sum_univ_two, Po_apply, U_apply, tab2]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_10 : game.pa 1 0 = 1 / 8 := by
  unfold Game.pa condDen; rw [sum_fin2_arrow]
  simp [Fin.sum_univ_two, Po_apply, tab2]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_10 : game.pva 1 0 = 0 := by
  unfold Game.pva Game.condNum; rw [sum_fin2_arrow]
  simp [Po_apply, U_apply, tab2]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_11 : game.pa 1 1 = 7 / 8 := by
  unfold Game.pa condDen; rw [sum_fin2_arrow]
  simp [Fin.sum_univ_two, Po_apply, tab2]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_11 : game.pva 1 1 = 7 / 8 := by
  unfold Game.pva Game.condNum; rw [sum_fin2_arrow]
  simp [Fin.sum_univ_two, Po_apply, U_apply, tab2]

/-- The margin is `0` at `(s₁, b)`: `pva/pa = (7/8)/(7/8) = 1 = U*`.
Source: [[updateless-self-game]] §4 ("Converse")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem margin_zero : game.pva 1 1 / game.pa 1 1 = game.Ustar := by
  rw [pva_11, pa_11, Ustar_eq]; norm_num

/-- **The converse of Theorem B on its witness**: `b` is available at `s₁` with conditional `U* = 1`, it
ties or beats `π*(s₁) = a`, and it is an argmax there.
Source: [[updateless-self-game]] §4 ("Converse")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem converse_on_witness :
    avail game.mu 1 1 ∧ game.cond game.mu 1 1 = game.Ustar ∧
      game.cond game.mu 1 (game.piStar 1) ≤ game.cond game.mu 1 1 ∧ game.IsArgmaxH game.mu 1 1 :=
  game.theoremB_converse (by rw [piStar_apply]; decide) (by rw [pa_11]; norm_num) margin_zero
    (by rw [δ_eq]; norm_num)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_11 : game.cond game.mu 1 1 = 1 := by
  rw [converse_on_witness.2.1, Ustar_eq]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_10 : game.cond game.mu 1 0 = 72 / 73 := by
  have h := game.cond_muSelf_self game.piStar 1
  rw [piStar_apply] at h
  show game.cond (game.muSelf game.piStar) 1 0 = 72 / 73
  rw [h, pva_10, pa_10, show game.U game.piStar = game.Ustar from rfl, Ustar_eq, δ_eq]
  norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_00 : game.cond game.mu 0 0 = 1 := by
  have h := game.cond_muSelf_self game.piStar 0
  rw [piStar_apply] at h
  show game.cond (game.muSelf game.piStar) 0 0 = 1
  rw [h, pva_00, pa_00, show game.U game.piStar = game.Ustar from rfl, Ustar_eq, δ_eq]
  norm_num

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem avail_01 : avail game.mu 0 1 := by
  rw [game.avail_mu_ne_iff (by rw [piStar_apply]; decide)]
  exact ⟨by rw [δ_eq]; norm_num, by rw [pa_01]; norm_num⟩

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_01 : game.cond game.mu 0 1 = 7 / 8 := by
  rw [game.cond_mu_ne (by rw [piStar_apply]; decide) avail_01, pva_01, pa_01]
  norm_num

/-- **N+ (the "beats" half)**: at `s₁` the deviation strictly beats `π*(s₁) = a` (`1 > 72/73`), so `a` is
not an argmax there and `π* = aa` is not realized.
Source: [[updateless-self-game]] §4 ("Converse": "`π*(s)` is not the strict argmax")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem not_isArgmaxH_piStar_1 : ¬ game.IsArgmaxH game.mu 1 0 := by
  rintro ⟨_, h⟩
  have := h 1 converse_on_witness.1
  rw [cond_11, cond_10] at this
  norm_num at this

/-- `π* = aa` is not realized on the converse witness.
Source: [[updateless-self-game]] §4 ("Converse")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem not_realizes_piStar : ¬ game.Realizes game.mu game.piStar :=
  fun h => not_isArgmaxH_piStar_1 (by simpa [piStar_apply] using h 1)

/-- The deviation `ab` is realized on the converse witness (`a` at `s₀` with conditional `1 > 7/8`; `b` at
`s₁` by the converse).
Source: [[updateless-self-game]] §4 ("Converse")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem realizes_ab : game.Realizes game.mu ![0, 1] := by
  intro s
  fin_cases s
  · show game.IsArgmaxH game.mu 0 0
    refine ⟨game.avail_muSelf_self game.piStar 0, fun b hb => ?_⟩
    fin_cases b
    · exact le_rfl
    · show game.cond game.mu 0 1 ≤ game.cond game.mu 0 0
      rw [cond_01, cond_00]; norm_num
  · show game.IsArgmaxH game.mu 1 1
    exact converse_on_witness.2.2.2

end ConverseWitness

/-! ### Theorem D (pure): `T2` is a floored fixed point, `T1` is not -/

namespace T2

variable {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1)

/-- **`T2` is a pure floored fixed point** at every `δ ∈ (0,1)`: through the *equality* branch at `s₀` and
`s₁` (`cond = 1 − δ = thr` there, `pol s` an argmax) and the argmax branch at `s₂`
(`cond(a) = 1/(1+δ) > 1 − δ`). The N+ witness of `theoremD_pure` (gap `δ`).
Scope: finite updateless self-game — self-consistent belief, floored agent; not rOSI, not the sequential
model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5.5 (T2), §7 (Theorem D); round-1 audits B1/B2
Kind: N+
Fidelity: exact (symbolic `δ`)
Hyps: (a) -/
theorem isPureFPfloored : (T2.game h0 h1).IsPureFPfloored T2.pol := by
  have hfp := T2.isPureFP h0 h1
  unfold Game.IsPureFPfloored
  simp only [forall_fin_three]
  refine ⟨⟨fun h => ?_, fun _ => hfp 0, fun _ _ => Or.inl (hfp 0)⟩,
    ⟨fun h => ?_, fun _ => hfp 1, fun _ _ => Or.inl (hfp 1)⟩,
    ⟨fun h => ?_, fun _ => hfp 2, fun _ _ => Or.inl (hfp 2)⟩⟩
  · exfalso
    have := h 0 (T2.avail_00 h0 h1)
    rw [T2.cond_00, T2.thr_eq] at this
    exact lt_irrefl _ this
  · exfalso
    have := h 0 (T2.avail_10 h0 h1)
    rw [T2.cond_10, T2.thr_eq] at this
    exact lt_irrefl _ this
  · exfalso
    have := h 0 (T2.avail_20 h0 h1)
    rw [T2.cond_20, T2.thr_eq, div_lt_iff₀ (by linarith)] at this
    nlinarith

/-- Theorem D's bound on `T2`, evaluated: the true, non-vacuous `1 − δ/(1−δ) ≤ 1 − δ`.
Source: [[updateless-self-game]] §7 (Theorem D)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem theoremD_on_T2 : (T2.game h0 h1).Ustar - δ / (1 - δ) ≤ (T2.game h0 h1).U T2.pol := by
  have := (T2.game h0 h1).theoremD_pure T2.pol (isPureFPfloored h0 h1)
  rwa [T2.δ_eq] at this

end T2

namespace T1

variable {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem piStar_1 : (T1.game h0 h1).piStar 1 = 0 := rfl

/-- At `s₁` every available conditional of `T1` is strictly below the threshold (the reset branch) — this is
`T1.not_TB_1` read through the floored agent's branches.
Source: [[updateless-self-game]] §5.5 (T1)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem all_below_1 :
    ∀ a, avail ((T1.game h0 h1).muSelf T1.pol) 1 a →
      (T1.game h0 h1).cond ((T1.game h0 h1).muSelf T1.pol) 1 a < (T1.game h0 h1).thr := by
  have hlt := T1.δ_lt_θ h0 h1
  simp only [Fin.forall_fin_two]
  exact ⟨fun _ => by rw [T1.cond_10, T1.thr_eq]; linarith,
    fun _ => by rw [T1.cond_11, T1.thr_eq]; linarith⟩

/-- **`T1` is not a pure floored fixed point** (at any `δ ∈ (0,1)`): at `s₁` it is in the reset branch and
must play `π*(s₁) = a`, but `pol 1 = b`. So a `theoremC` witness (pure fixed point with the trust bound at
one situation) is not automatically a floored fixed point; the ledger's earlier claim was false for `T1`.
Source: [[updateless-self-game]] §5.5 (T1), §7; round-1 audits B1/B2 (probe `T1NotFloored`)
Kind: N−
Fidelity: exact (symbolic `δ`)
Hyps: (a) -/
theorem not_isPureFPfloored : ¬ (T1.game h0 h1).IsPureFPfloored T1.pol := by
  intro h
  obtain ⟨hA, _, _⟩ := h 1
  have := hA (all_below_1 h0 h1)
  rw [T1.pol_1, piStar_1] at this
  exact absurd this (by decide)

end T1

/-! ### Theorem E: a margin-satisfying C1 instance -/

namespace TheoremEWitness

/-- `S = A = Fin 2`, `U = (aa:1, ab:0, ba:0, bb:0)`, `π* = aa`, `Po = δ_{aa}` (irrelevant to the C1 belief),
`δ = 1/10`.
Source: [[updateless-self-game]] §8 (Theorem E); round-1 adversarial audit N1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def game : Game (Fin 2) (Fin 2) where
  U := tab2 1 0 0 0
  U_nonneg := fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) π).1
  U_le_one := fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) π).2
  piStar := ![0, 0]
  piStar_max := fun π => by
    rw [tab2_00]
    exact (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  Po := tab2 1 0 0 0
  Po_mem := ⟨fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) π).1, by rw [sum_tab2]; norm_num⟩
  δ := 1 / 10
  δ_nonneg := by norm_num
  δ_lt_one := by norm_num

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
theorem piStar_apply (s : Fin 2) : game.piStar s = 0 := by fin_cases s <;> rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem hA : 2 ≤ Fintype.card (Fin 2) := by simp

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem update_0 : Function.update (![0, 0] : Fin 2 → Fin 2) 0 1 = ![1, 0] := by
  funext i; fin_cases i <;> simp

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem update_1 : Function.update (![0, 0] : Fin 2 → Fin 2) 1 1 = ![0, 1] := by
  funext i; fin_cases i <;> simp

/-- `HasMarginC1 1`: every one-coordinate deviation from `aa` has utility `0 ≤ 1 − 1`.
Source: [[updateless-self-game]] §8 (Theorem E, `m_s`)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem hasMarginC1 : game.HasMarginC1 1 := by
  intro s a hne
  rw [piStar_apply] at hne
  fin_cases a
  · exact absurd rfl hne
  · fin_cases s
    · show game.U (Function.update ![0, 0] 0 1) ≤ game.Ustar - 1
      rw [update_0, Ustar_eq]; show tab2 1 0 0 0 ![1, 0] ≤ 1 - 1; simp
    · show game.U (Function.update ![0, 0] 1 1) ≤ game.Ustar - 1
      rw [update_1, Ustar_eq]; show tab2 1 0 0 0 ![0, 1] ≤ 1 - 1; simp

/-- `ρ = 1 − (1−δ)^{|S|−1} = δ = 1/10` here.
Source: [[updateless-self-game]] §8
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem rho_eq : game.rho = 1 / 10 := by
  show 1 - (1 - 1 / 10 : ℝ) ^ (Fintype.card (Fin 2) - 1) = 1 / 10
  simp

/-- **Theorem E on its witness**: the package `2 ≤ |A| ∧ HasMarginC1 1 ∧ 2ρ < 1` is inhabited, and the
conclusion evaluates to: `π* = aa` is the unique chosen policy under the C1 belief.
Source: [[updateless-self-game]] §8 (Theorem E); round-1 adversarial audit N1
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem theoremE_on_witness :
    game.Realizes game.muC1 game.piStar ∧ ∀ π, game.Realizes game.muC1 π → π = game.piStar :=
  game.theoremE_realizes hA hasMarginC1 (by rw [rho_eq]; norm_num)

/-- **N+**: the deviation `b` is available at every situation under the C1 belief (mass `δ = 1/10`), so
Theorem E's strict argmax is a real comparison.
Source: [[updateless-self-game]] §8
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem deviation_available (s : Fin 2) : avail game.muC1 s 1 := by
  rw [game.avail_muC1_iff hA]
  show 0 < kappaOf (1 / 10) ![0, 0] s 1
  unfold kappaOf
  rw [show (![0, 0] : Fin 2 → Fin 2) s = 0 from by fin_cases s <;> rfl]
  simp

end TheoremEWitness

/-! ### Theorem A: the support clause and the `Bel` row -/

namespace TheoremA

variable {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Po_apply (π : Fin 2 → Fin 2) : (game δ h0 h1).Po π = Pofun π := rfl

/-- **`supp Po = {ab, bb}`** in Theorem A's instance: `Po π > 0` iff `π = ab` or `π = bb` (`|supp Po| = 2`).
Source: [[updateless-self-game]] §2 (Theorem A proof); round-1 adversarial audit N4
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem Po_pos_iff (π : Fin 2 → Fin 2) :
    0 < (game δ h0 h1).Po π ↔ (π = ![0, 1] ∨ π = ![1, 1]) := by
  obtain ⟨a, ha⟩ : ∃ a, π 0 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, π 1 = b := ⟨_, rfl⟩
  have hπ : π = ![a, b] := by funext i; fin_cases i <;> simp [ha, hb]
  subst hπ
  rw [Po_apply]; unfold Pofun
  fin_cases a <;> fin_cases b <;> simp

/-- **Theorem A with the support clause**: `TheoremA.theoremA`'s existential with the extra conjunct
`∀ π, 0 < Po π ↔ (π = ab ∨ π = bb)`, so the N+ grade `|S| = |A| = |supp Po| = 2` is machine-stated.
Scope: finite updateless self-game — pointwise EDT conditional, static belief; not rOSI, not the sequential
model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §2 (Theorem A); round-1 adversarial audit N4
Kind: P
Fidelity: exact (general `δ`; the support clause added)
Hyps: (a) -/
theorem theoremA_supp (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) :
    ∃ G : Game (Fin 2) (Fin 2), G.δ = δ ∧ G.Ustar = 1 ∧
      (∀ π, π ≠ G.piStar → G.U π < G.Ustar) ∧
      (∀ π, 0 < G.Po π ↔ (π = ![0, 1] ∨ π = ![1, 1])) ∧
      (∀ s a, avail G.mu s a) ∧
      G.StrictArgmax G.mu ∧
      (∀ s, G.TB G.mu s) ∧
      (∀ π, G.Realizes G.mu π → G.U π = 0) ∧
      (∃ π, G.Realizes G.mu π) :=
  ⟨game δ h0 h1, rfl, Ustar_eq h0 h1, unique_max h0 h1, Po_pos_iff h0 h1, avail_all h0 h1,
    strictArgmax h0 h1, TB_all h0 h1, fun π hπ => by
      rw [(realizes_iff h0 h1 π).1 hπ, U_apply]; simp [Ufun],
    ⟨![1, 0], (realizes_iff h0 h1 _).2 rfl⟩⟩

/-- **The realized policy does not maximize `Bel`**: with `Bel(π) := (1−δ) U(π) + δ E_{Po} U`, the
realized policy `ba` has `Bel(ba) < Bel(aa)` — the `hsel` premise of the earlier lab's Prop 1 is exactly
what the pointwise agent fails. The `E_{Po}` term is constant in `π`, so this is `U(ba) < U(aa)` from
`loss_eq_one`: an `L` row, as the mandate anticipated (`N−`/`P`).
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[uea-self-game-mandate]] target 11 (Prop 1, `hsel`); [[models--unbounded-embedded-agency-model]] Prop 1
Kind: L
Fidelity: variant: `V_other` taken constant (`E_{Po} U`); the source defines `V_other` as an arbitrary, possibly adversarial value map in `[lo, hi]` ([[models--unbounded-embedded-agency-model]] lines 60–66) — the general form is `realized_not_bel_max_general` (for every `V_other ∈ [0,1]` iff `δ < 1/2`; `exists_Vo_bel_reversed`)
Hyps: (a) -/
theorem realized_not_bel_max (π : Fin 2 → Fin 2) (hπ : (game δ h0 h1).Realizes (game δ h0 h1).mu π) :
    (1 - δ) * (game δ h0 h1).U π + δ * ∑ ρ, (game δ h0 h1).Po ρ * (game δ h0 h1).U ρ <
      (1 - δ) * (game δ h0 h1).U (game δ h0 h1).piStar +
        δ * ∑ ρ, (game δ h0 h1).Po ρ * (game δ h0 h1).U ρ := by
  have hl := loss_eq_one h0 h1 π hπ
  have hU : (game δ h0 h1).U (game δ h0 h1).piStar = (game δ h0 h1).Ustar := rfl
  rw [hU]
  have h2 : (1 - δ) * ((game δ h0 h1).Ustar - (game δ h0 h1).U π) = 1 - δ := by rw [hl, mul_one]
  linarith

/-- **The realized policy does not maximize `Bel`, for every other-value map** (repair round 2, fidelity
non-blocking 3): with `Bel(π) := (1−δ) U(π) + δ V_other(π)` for an arbitrary `V_other : (S → A) → [0,1]`
(the source's "arbitrary, possibly adversarial 'some-other-code' value map"), the realized policy `ba`
has `Bel(ba) < Bel(aa)` whenever `δ < 1/2`, since `Bel(aa) − Bel(ba) ≥ (1−δ) − δ`. The condition is exact:
`exists_Vo_bel_reversed` gives a `V_other` reversing the inequality for every `δ ≥ 1/2`.
Scope: finite updateless self-game — pointwise EDT conditional, static belief; not rOSI, not the
sequential model of `uea-cole-shadow`.
Source: [[uea-self-game-mandate]] target 11 (Prop 1, `hsel`); [[models--unbounded-embedded-agency-model]] `Bel`/`V_other` (lines 58–72), Prop 1
Kind: L
Fidelity: exact (the source's arbitrary `V_other ∈ [0,1]`; `realized_not_bel_max` is the constant-`V_other` reading)
Hyps: (a) -/
theorem realized_not_bel_max_general (hhalf : δ < 1 / 2) (Vo : (Fin 2 → Fin 2) → ℝ)
    (hVo : ∀ ρ, 0 ≤ Vo ρ ∧ Vo ρ ≤ 1) (π : Fin 2 → Fin 2)
    (hπ : (game δ h0 h1).Realizes (game δ h0 h1).mu π) :
    (1 - δ) * (game δ h0 h1).U π + δ * Vo π <
      (1 - δ) * (game δ h0 h1).U (game δ h0 h1).piStar + δ * Vo (game δ h0 h1).piStar := by
  have hl := loss_eq_one h0 h1 π hπ
  have hU : (game δ h0 h1).U (game δ h0 h1).piStar = (game δ h0 h1).Ustar := rfl
  rw [hU]
  have h2 : (1 - δ) * ((game δ h0 h1).Ustar - (game δ h0 h1).U π) = 1 - δ := by rw [hl, mul_one]
  have h3 := mul_le_mul_of_nonneg_left (hVo π).2 h0.le
  have h4 := mul_nonneg h0.le (hVo (game δ h0 h1).piStar).1
  linarith

/-- For `δ ≥ 1/2` an adversarial `V_other` (the indicator of `ba`) makes `Bel(aa) ≤ Bel(ba)`: the
condition `δ < 1/2` in `realized_not_bel_max_general` is exact.
Source: [[models--unbounded-embedded-agency-model]] `V_other` ("possibly adversarial")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem exists_Vo_bel_reversed (hhalf : 1 / 2 ≤ δ) :
    ∃ Vo : (Fin 2 → Fin 2) → ℝ, (∀ ρ, 0 ≤ Vo ρ ∧ Vo ρ ≤ 1) ∧
      (1 - δ) * (game δ h0 h1).U (game δ h0 h1).piStar + δ * Vo (game δ h0 h1).piStar ≤
        (1 - δ) * (game δ h0 h1).U ![1, 0] + δ * Vo ![1, 0] := by
  refine ⟨fun ρ => if ρ = ![1, 0] then 1 else 0, fun ρ => by dsimp only; split_ifs <;> norm_num, ?_⟩
  have hU : (game δ h0 h1).U (game δ h0 h1).piStar = 1 := Ustar_eq h0 h1
  have hba : (game δ h0 h1).U ![1, 0] = 0 := by rw [U_apply]; simp [Ufun]
  have hne : (game δ h0 h1).piStar ≠ ![1, 0] := by
    intro h
    have := congrFun h 0
    simp [game] at this
  rw [hU, hba]
  dsimp only
  rw [if_neg hne, if_pos rfl]
  linarith

end TheoremA

end Cleanroom.Uea.UeaSelfGame
