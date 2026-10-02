import Cleanroom.Corrigibility.LegitNegDynamic.Cells
import Cleanroom.Corrigibility.LegitNegPricing.Inertness
import Cleanroom.Corrigibility.LegitNegPricing.Timing
import Cleanroom.Corrigibility.LegitNegPricing.Scoring

/-!
# D1: the T2 conjecture on `toyD` — margin `v`, the cell formula, P2's threshold, R2's tie

Package `legit-neg-dynamic`, target 1. Sources: `clusters/D/NEGATIVES.md` D1 (i)–(iv);
`clusters/D/VERIFY.md` "D1 — survives, with two scope notes"; `clusters/D/fixtures/d1_t2_floor.py`;
pinned by [[corr-legit-neg-inventory]] item 045 and [[corr-legit-neg-2-inventory]] items 2-017, 2-018.

The toy is static's `toyD G v β p postg` (states `0 = g`, `1 = b` with `P(g) = postg`; `a₀ = 0`
keeps legitimacy, `a₁ = 1` voids in `b`; `u(g, a₀) = G`, `u(b, a₀) = v`, `u(g, a₁) = G + β − p`).
The headline is the **cell formula** `toyD_P1_diff`: cdot's margin for `a₀` at an information cell
with `P(g | I) = postg` is `(1 − postg) v − postg (β − p)`. Everything else is read off it: the
margin is exactly `v` at `postg = 0` (branch known), the T1 threshold at `postg = 1/2`, the
neighbourhood corollary for `v > 0` (2-018, which the run did not state), the knife-edge at `v = 0`,
and the instance where `p` enters as soon as the cell leaves legitimacy open. P2's cell threshold
(2-017) and R2's tie fixed point (D1(iv), `R2_at_void` restricted to `b`) close the target.
Registers: "handled by the floor" means "with margin `v`"; the tie at `v = 0` is real.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing

section ToyD

variable (G v β p postg : ℚ) (h0 : 0 ≤ postg) (h1 : postg ≤ 1)

/-- `toyD_P1_zero`: supporting lemma (no headline): `P1 (S1 u) a₀ = postg G + (1 − postg) v`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyD_P1_zero :
    (toyD G v β p postg h0 h1).P1 (S1 (toyD G v β p postg h0 h1).u) 0 = postg * G + (1 - postg) * v := by
  unfold toyD; rw [toyB_P1_S1_zero]; ring

/-- `toyD_P1_one`: supporting lemma (no headline): `P1 (S1 u) a₁ = postg (G + β − p)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyD_P1_one :
    (toyD G v β p postg h0 h1).P1 (S1 (toyD G v β p postg h0 h1).u) 1 = postg * (G + β - p) := by
  unfold toyD; rw [toyB_P1_S1_one]; ring

/-- `toyD_PL`: supporting lemma (no headline): `P(L | a₀) = 1`, `P(L | a₁) = postg`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyD_PL :
    (toyD G v β p postg h0 h1).PL 0 = 1 ∧ (toyD G v β p postg h0 h1).PL 1 = postg := by
  unfold toyD; rw [toyB_PL_zero, toyB_PL_one]; constructor <;> ring

/-- **D1, the cell formula (the headline).** At an information cell with `P(g | I) = postg`,
`P1 (S1 u) a₀ − P1 (S1 u) a₁ = (1 − postg) v − postg (β − p)`: cdot's margin for the
legitimacy-keeping option is the void-branch score `v` weighted by the cell's `b`-mass, minus the
`g`-branch gain net of the penalty weighted by the cell's `g`-mass. `p` enters with weight `postg`,
i.e. exactly when the cell leaves `a₁`'s legitimacy open. (The proof is `ring` after static's
`toyB` closed forms, so the kind is L; the target's content is `toyD_neighbourhood` and `toyD_P2`.)
Source: [[corr-legit-neg-2-inventory]] item 2-018; [[corr-legit-neg-inventory]] item 045 (D1(i), (ii))
Kind: L
Fidelity: exact
Hyps: (a) none beyond the toy's `0 ≤ postg ≤ 1` -/
theorem toyD_P1_diff :
    (toyD G v β p postg h0 h1).P1 (S1 (toyD G v β p postg h0 h1).u) 0
      - (toyD G v β p postg h0 h1).P1 (S1 (toyD G v β p postg h0 h1).u) 1
      = (1 - postg) * v - postg * (β - p) := by
  rw [toyD_P1_zero, toyD_P1_one]; ring

/-- **D1(i), branch `b` known (`postg = 0`): the margin is exactly `v`, for every `p` and `β`**;
cdot keeps legitimacy alone iff `0 < v` and ties iff `v = 0` ("handled by the floor" = "with
margin `v`"; the tie at the worst legitimate outcome is real).
Source: [[corr-legit-neg-inventory]] item 045 (D1(i)); `d1_t2_floor.py:33-41`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem toyD_b_known (G v β p : ℚ) :
    (toyD G v β p 0 le_rfl zero_le_one).P1 (S1 (toyD G v β p 0 le_rfl zero_le_one).u) 0
      - (toyD G v β p 0 le_rfl zero_le_one).P1 (S1 (toyD G v β p 0 le_rfl zero_le_one).u) 1 = v ∧
    (argmax ((toyD G v β p 0 le_rfl zero_le_one).P1 (S1 (toyD G v β p 0 le_rfl zero_le_one).u)) = {0}
      ↔ 0 < v) ∧
    (argmax ((toyD G v β p 0 le_rfl zero_le_one).P1 (S1 (toyD G v β p 0 le_rfl zero_le_one).u)) = univ
      ↔ v = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [toyD_P1_diff]; ring
  · rw [argmax_fin2_eq_zero_iff, toyD_P1_zero, toyD_P1_one]
    constructor <;> intro h <;> linarith
  · rw [argmax_fin2_eq_univ_iff, toyD_P1_zero, toyD_P1_one]
    constructor <;> intro h <;> linarith

/-- **D1(i), the T1 choice (`postg = 1/2`) depends on `p`**: cdot takes the voiding `a₁` alone iff
`v < β − p`, ties iff `v = β − p`.
Source: [[corr-legit-neg-inventory]] item 045 (D1(i), "T1 picks `a₁` iff `β − p > v`"); `d1_t2_floor.py:43-50`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem toyD_T1 (G v β p : ℚ) :
    (argmax ((toyD G v β p (1/2) (by norm_num) (by norm_num)).P1
      (S1 (toyD G v β p (1/2) (by norm_num) (by norm_num)).u)) = {1} ↔ v < β - p) ∧
    (argmax ((toyD G v β p (1/2) (by norm_num) (by norm_num)).P1
      (S1 (toyD G v β p (1/2) (by norm_num) (by norm_num)).u)) = univ ↔ v = β - p) := by
  constructor
  · rw [argmax_fin2_eq_one_iff, toyD_P1_zero, toyD_P1_one]
    constructor <;> intro h <;> linarith
  · rw [argmax_fin2_eq_univ_iff, toyD_P1_zero, toyD_P1_one]
    constructor <;> intro h <;> linarith

/-- **The RUN toy** (`G = 1, β = 0, p = 0`, T1): a tie at `v = 0`, `a₀` alone at `v = 1/4`.
Source: [[corr-legit-neg-inventory]] item 045; `d1_t2_floor.py:51-53`
Kind: N+
Fidelity: exact -/
theorem toyD_RUN_toy :
    argmax ((toyD 1 0 0 0 (1/2) (by norm_num) (by norm_num)).P1
      (S1 (toyD 1 0 0 0 (1/2) (by norm_num) (by norm_num)).u)) = univ ∧
    argmax ((toyD 1 (1/4) 0 0 (1/2) (by norm_num) (by norm_num)).P1
      (S1 (toyD 1 (1/4) 0 0 (1/2) (by norm_num) (by norm_num)).u)) = {0} := by
  constructor
  · exact (toyD_T1 1 0 0 0).2.2 (by norm_num)
  · rw [argmax_fin2_eq_zero_iff, toyD_P1_zero, toyD_P1_one]; norm_num

/-- **The neighbourhood corollary (2-018; not stated by the run).** For `0 < v` and `|β − p| ≤ M`,
every information cell with `postg < v / (v + M)` chooses `a₀` alone: the T2 conjecture holds on
an open neighbourhood of "branch known", not only at it.
Source: [[corr-legit-neg-2-inventory]] item 2-018
Kind: P
Fidelity: stronger: the source states the inequality; the neighbourhood is its corollary
Hyps: (a) `0 < v`, `|β − p| ≤ M`, `postg < v/(v + M)` -/
theorem toyD_neighbourhood (M : ℚ) (hv : 0 < v) (hM : |β - p| ≤ M) (hnear : postg < v / (v + M)) :
    argmax ((toyD G v β p postg h0 h1).P1 (S1 (toyD G v β p postg h0 h1).u)) = {0} := by
  rw [argmax_fin2_eq_zero_iff, toyD_P1_zero, toyD_P1_one]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) hM
  have hvM : 0 < v + M := by linarith
  have h1' : postg * (v + M) < v := by rwa [lt_div_iff₀ hvM] at hnear
  have h2 : postg * (β - p) ≤ postg * M :=
    mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hM) h0
  nlinarith

/-- **The knife-edge at the floor (`v = 0`)**: cdot keeps `a₀` alone iff `postg (β − p) < 0`, so
away from `postg = 0` the verdict depends on `p` (instances: at `postg = 3/4, β = 1/4, G = 3/4`,
`p = 0` gives `{a₁}` and `p = 1/2` gives `{a₀}`). This is the instance behind D1(ii): the T2
congruence `restrict_P1_congr` is silent about `p` only at cells where `a₁`'s legitimacy is
settled; here it is open (`P(¬L | a₁, I) = 1/4 > 0`) and `p` enters exactly as at T1.
Source: [[corr-legit-neg-inventory]] item 045 (D1(ii)); [[corr-legit-neg-2-inventory]] item 2-018; `d1_t2_floor.py:55-61`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem toyD_partial_p_enters :
    (argmax ((toyD G 0 β p postg h0 h1).P1 (S1 (toyD G 0 β p postg h0 h1).u)) = {0}
      ↔ postg * (β - p) < 0) ∧
    argmax ((toyD (3/4) 0 (1/4) 0 (3/4) (by norm_num) (by norm_num)).P1
      (S1 (toyD (3/4) 0 (1/4) 0 (3/4) (by norm_num) (by norm_num)).u)) = {1} ∧
    argmax ((toyD (3/4) 0 (1/4) (1/2) (3/4) (by norm_num) (by norm_num)).P1
      (S1 (toyD (3/4) 0 (1/4) (1/2) (3/4) (by norm_num) (by norm_num)).u)) = {0} := by
  refine ⟨?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_zero_iff, toyD_P1_zero, toyD_P1_one]
    constructor <;> intro h <;> linarith
  · rw [argmax_fin2_eq_one_iff, toyD_P1_zero, toyD_P1_one]; norm_num
  · rw [argmax_fin2_eq_zero_iff, toyD_P1_zero, toyD_P1_one]; norm_num

/-! ### D1(iii): P2 at a cell (2-017) -/

/-- **P2 at a cell, `0 < postg`** (exclusion convention): `P2 a₁ = some (G + β − p)` (the voiding
option judged on its legitimate part only), `P2 a₀ = some (postg G + (1 − postg) v)`, and P2
prefers `a₁` alone iff `p < (1 − postg)(G − v) + β`: the deterring penalty is of the order of the
whole score, not scaled by the voiding probability.
Source: [[corr-legit-neg-2-inventory]] item 2-017; [[corr-legit-neg-inventory]] item 045 (D1(iii))
Kind: P
Fidelity: exact; exclusion convention (the case `postg = 0` is `toyD_b_known_P2`)
Hyps: (a) `0 < postg` -/
theorem toyD_P2 (hpos : 0 < postg) :
    (toyD G v β p postg h0 h1).P2 (S1 (toyD G v β p postg h0 h1).u) 1 = some (G + β - p) ∧
    (toyD G v β p postg h0 h1).P2 (S1 (toyD G v β p postg h0 h1).u) 0 = some (postg * G + (1 - postg) * v) ∧
    (argmaxOpt ((toyD G v β p postg h0 h1).P2 (S1 (toyD G v β p postg h0 h1).u)) = {1}
      ↔ p < (1 - postg) * (G - v) + β) := by
  obtain ⟨hPL0, hPL1⟩ := toyD_PL G v β p postg h0 h1
  have h1' : (toyD G v β p postg h0 h1).P2 (S1 (toyD G v β p postg h0 h1).u) 1 = some (G + β - p) := by
    rw [Problem.P2_of_ne _ _ _ (by rw [hPL1]; exact hpos.ne'), hPL1, toyD_P1_one]
    congr 1; field_simp
  have h0' : (toyD G v β p postg h0 h1).P2 (S1 (toyD G v β p postg h0 h1).u) 0
      = some (postg * G + (1 - postg) * v) := by
    rw [Problem.P2_of_ne _ _ _ (by rw [hPL0]; exact one_ne_zero), hPL0, toyD_P1_zero]
    congr 1; ring
  refine ⟨h1', h0', ?_⟩
  rw [argmaxOpt_eq_argmax_of_forall_some (g := ![postg * G + (1 - postg) * v, G + β - p])
    (by rw [Fin.forall_fin_two]; exact ⟨by simp [h0'], by simp [h1']⟩)]
  rw [argmax_fin2_eq_one_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  constructor <;> intro h <;> nlinarith

/-- **D1(iii) instances** (`G = 3/4, β = 1/4, postg = 1/4`, the `b`-leaning cell): at `v = 0` the
P2 threshold is `p = 13/16` (a tie there); at `v = 1/4, p = 0` P2 voids while cdot keeps.
Exclusion convention.
Source: [[corr-legit-neg-2-inventory]] item 2-017; `d1_t2_floor.py:62-75`
Kind: N+
Fidelity: exact -/
theorem toyD_P2_instances :
    argmaxOpt ((toyD (3/4) 0 (1/4) (13/16) (1/4) (by norm_num) (by norm_num)).P2
      (S1 (toyD (3/4) 0 (1/4) (13/16) (1/4) (by norm_num) (by norm_num)).u)) = univ ∧
    argmaxOpt ((toyD (3/4) 0 (1/4) 0 (1/4) (by norm_num) (by norm_num)).P2
      (S1 (toyD (3/4) 0 (1/4) 0 (1/4) (by norm_num) (by norm_num)).u)) = {1} ∧
    argmaxOpt ((toyD (3/4) (1/4) (1/4) 0 (1/4) (by norm_num) (by norm_num)).P2
      (S1 (toyD (3/4) (1/4) (1/4) 0 (1/4) (by norm_num) (by norm_num)).u)) = {1} ∧
    argmax ((toyD (3/4) (1/4) (1/4) 0 (1/4) (by norm_num) (by norm_num)).P1
      (S1 (toyD (3/4) (1/4) (1/4) 0 (1/4) (by norm_num) (by norm_num)).u)) = {0} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨h1', h0', _⟩ := toyD_P2 (3/4) 0 (1/4) (13/16) (1/4) (by norm_num) (by norm_num) (by norm_num)
    rw [argmaxOpt_eq_argmax_of_forall_some (g := ![1/4 * (3/4) + (1 - 1/4) * 0, 3/4 + 1/4 - 13/16])
      (by rw [Fin.forall_fin_two]; exact ⟨by simpa using h0', by simpa using h1'⟩)]
    rw [argmax_fin2_eq_univ_iff]; norm_num
  · exact (toyD_P2 (3/4) 0 (1/4) 0 (1/4) (by norm_num) (by norm_num) (by norm_num)).2.2.2 (by norm_num)
  · exact (toyD_P2 (3/4) (1/4) (1/4) 0 (1/4) (by norm_num) (by norm_num) (by norm_num)).2.2.2 (by norm_num)
  · rw [argmax_fin2_eq_zero_iff, toyD_P1_zero, toyD_P1_one]; norm_num

/-- **D1(iii) at `postg = 0`: the convention decides.** With `b` known, `P2 a₁ = none` (exclusion
convention), so `argmaxOpt P2 = {a₀}` for every `v`; under the 1-at-null convention `P2li a₁ = 1`
and the voiding option wins iff `v < 1`. The run's "P2's T2 choice depends on a convention for
undefined options" is this.
Source: [[corr-legit-neg-inventory]] item 045 (D1(iii)); mandate "Known issues" 3
Kind: P
Fidelity: exact; the `_li` clause is the variant: junk value 1 at a null condition
Hyps: (a) none -/
theorem toyD_b_known_P2 (G v β p : ℚ) :
    (toyD G v β p 0 le_rfl zero_le_one).P2 (S1 (toyD G v β p 0 le_rfl zero_le_one).u) 1 = none ∧
    argmaxOpt ((toyD G v β p 0 le_rfl zero_le_one).P2 (S1 (toyD G v β p 0 le_rfl zero_le_one).u)) = {0} ∧
    (toyD G v β p 0 le_rfl zero_le_one).P2li (S1 (toyD G v β p 0 le_rfl zero_le_one).u) 1 = 1 ∧
    (argmax ((toyD G v β p 0 le_rfl zero_le_one).P2li (S1 (toyD G v β p 0 le_rfl zero_le_one).u)) = {1}
      ↔ v < 1) := by
  obtain ⟨hPL0, hPL1⟩ := toyD_PL G v β p 0 le_rfl zero_le_one
  have hn : (toyD G v β p 0 le_rfl zero_le_one).P2 (S1 (toyD G v β p 0 le_rfl zero_le_one).u) 1 = none :=
    Problem.P2_of_eq _ _ _ hPL1
  have h0' : (toyD G v β p 0 le_rfl zero_le_one).P2 (S1 (toyD G v β p 0 le_rfl zero_le_one).u) 0 = some v := by
    rw [Problem.P2_of_ne _ _ _ (by rw [hPL0]; exact one_ne_zero), hPL0, toyD_P1_zero]
    congr 1; ring
  have hli1 : (toyD G v β p 0 le_rfl zero_le_one).P2li (S1 (toyD G v β p 0 le_rfl zero_le_one).u) 1 = 1 := by
    simp [Problem.P2li, hPL1]
  have hli0 : (toyD G v β p 0 le_rfl zero_le_one).P2li (S1 (toyD G v β p 0 le_rfl zero_le_one).u) 0 = v := by
    simp only [Problem.P2li, hPL0, one_ne_zero, if_false, toyD_P1_zero, div_one]; ring
  refine ⟨hn, ?_, hli1, ?_⟩
  · refine finset_fin2_ext ?_ ?_
    · rw [mem_argmaxOpt, Finset.mem_singleton]
      refine ⟨fun _ => rfl, fun _ => ⟨v, h0', ?_⟩⟩
      rw [Fin.forall_fin_two]
      constructor
      · intro y hy; rw [h0', Option.some_inj] at hy; exact hy.symm.le
      · intro y hy; rw [hn] at hy; cases hy
    · rw [mem_argmaxOpt, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx, _⟩; rw [hn] at hx; cases hx
      · intro h10; exact absurd h10 (by decide)
  · rw [argmax_fin2_eq_one_iff, hli0, hli1]

/-- **The verifier's S2 reading of D1(iii)** (an instance under `P.S2`, the prior-referenced
bet): on `toyD (3/4) 0 (1/4) 0 (1/4)` the humans at `(g, a₁)` score `a₁` as the bet
`H a₁ = postg (G + β) = 1/4`, an effective penalty `p = 3/4 < 13/16`; P2 still voids
(`1/4 > 3/16`) and cdot still keeps (`1/16 < 3/16`). Exclusion convention.
Source: VERIFY D "D1 — survives" (Fairness); [[corr-legit-neg-inventory]] item 045
Kind: N+
Fidelity: exact (the vector is static's `P.S2`) -/
theorem toyD_S2_reading :
    (toyD (3/4) 0 (1/4) 0 (1/4) (by norm_num) (by norm_num)).H 1 = 1/4 ∧
    (toyD (3/4) 0 (1/4) 0 (1/4) (by norm_num) (by norm_num)).P2
      (toyD (3/4) 0 (1/4) 0 (1/4) (by norm_num) (by norm_num)).S2 1 = some (1/4) ∧
    (toyD (3/4) 0 (1/4) 0 (1/4) (by norm_num) (by norm_num)).P2
      (toyD (3/4) 0 (1/4) 0 (1/4) (by norm_num) (by norm_num)).S2 0 = some (3/16) ∧
    argmaxOpt ((toyD (3/4) 0 (1/4) 0 (1/4) (by norm_num) (by norm_num)).P2
      (toyD (3/4) 0 (1/4) 0 (1/4) (by norm_num) (by norm_num)).S2) = {1} ∧
    argmax ((toyD (3/4) 0 (1/4) 0 (1/4) (by norm_num) (by norm_num)).P1
      (toyD (3/4) 0 (1/4) 0 (1/4) (by norm_num) (by norm_num)).S2) = {0} := by
  set P := toyD (3/4) 0 (1/4) 0 (1/4) (by norm_num) (by norm_num) with hP
  obtain ⟨hPL0, hPL1⟩ := toyD_PL (3/4) 0 (1/4) 0 (1/4) (by norm_num) (by norm_num)
  have hH1 : P.H 1 = 1/4 := by rw [hP]; unfold toyD; rw [toyB_H_one]; norm_num
  have hH0 : P.H 0 = 3/16 := by rw [hP]; unfold toyD; rw [toyB_H_zero]; norm_num
  have h1' : P.P2 P.S2 1 = some (1/4) := by rw [P2_S2_eq _ _ (by rw [hPL1]; norm_num), hH1]
  have h0' : P.P2 P.S2 0 = some (3/16) := by rw [P2_S2_eq _ _ (by rw [hPL0]; norm_num), hH0]
  refine ⟨hH1, h1', h0', ?_, ?_⟩
  · rw [argmaxOpt_eq_argmax_of_forall_some (g := ![3/16, 1/4])
      (by rw [Fin.forall_fin_two]; exact ⟨by simpa using h0', by simpa using h1'⟩)]
    rw [argmax_fin2_eq_one_iff]; norm_num
  · rw [argmax_fin2_eq_zero_iff, P1_S2_eq, P1_S2_eq, hPL0, hPL1, hH0, hH1]; norm_num

/-! ### D1(iv): R2 at T2 in `b` -/

/-- The T2 problem of `toyD` at the known state `b` has positive mass when `postg < 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyD_b_prior_pos (hlt : postg < 1) : 0 < (toyD G v β p postg h0 h1).prior 1 := by
  unfold toyD toyB; simp; linarith

/-- The cell `{b}` has positive mass when `postg < 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyD_b_cell_pos (hlt : postg < 1) :
    0 < ∑ t ∈ ({1} : Finset (Fin 2)), (toyD G v β p postg h0 h1).prior t :=
  restrict_singleton_mass_pos (toyD G v β p postg h0 h1) 1 (toyD_b_prior_pos G v β p postg h0 h1 hlt)

/-- The `(b, a₀)` humans' vector of D1(iv): `S1 u` except that the unchosen `a₁` at the legitimate
terminal `(b, a₀)` is scored `max (v − p') 0` (the fixture's `realized["a0"]["a1"]`,
`d1_t2_floor.py:77-84`); sighted evaluators (static finding 1).
Source: [[corr-legit-neg-inventory]] item 045 (D1(iv))
Kind: D
Fidelity: exact -/
def d1R2V (G v β p p' : ℚ) : MenuVec (Fin 2) (Fin 2) :=
  fun s a c => if s = 1 ∧ a = 0 ∧ c = 1 then max (v - p') 0 else ![![G, G + β - p], ![v, 0]] s c

/-- **D1(iv), R2 at T2 in `b` is a tie fixed point for the voiding option** (`R2_at_void` restricted
to the cell `{b}`): with `a* = a₁` every option scores `0`, so `argmax (R2scores V a₁) = univ` for
*every* menu vector `V`; and `a₀` is ratifiable iff the `(b, a₀)` humans score the unchosen `a₁`
no higher than `a₀`'s own `v`, which holds under the penalised vector for every `p'` when
`0 ≤ v`: both fixed points coexist, the voiding one as a tie (verifier's scope note 2). Sighted
evaluators.
Source: [[corr-legit-neg-inventory]] item 045 (D1(iv)); VERIFY D "D1 — survives" scope note (2)
Kind: C
Fidelity: exact (the fixed point is a tie, as the verifier says)
Hyps: (a) `postg < 1` so the cell `{b}` has mass; `0 ≤ v` for the instance -/
theorem toyD_R2_at_b (hlt : postg < 1) (V : MenuVec (Fin 2) (Fin 2)) :
    argmax (((toyD G v β p postg h0 h1).restrict {1}
      (toyD_b_cell_pos G v β p postg h0 h1 hlt)).R2scores V 1) = univ ∧
    ((0 : Fin 2) ∈ ((toyD G v β p postg h0 h1).restrict {1}
      (toyD_b_cell_pos G v β p postg h0 h1 hlt)).ratifiable V
      ↔ V 1 0 1 ≤ V 1 0 0) := by
  set Q := (toyD G v β p postg h0 h1).restrict {1} (toyD_b_cell_pos G v β p postg h0 h1 hlt) with hQ
  have hpos := toyD_b_prior_pos G v β p postg h0 h1 hlt
  have hPL1 : Q.PL 1 = 0 := by
    unfold Problem.PL Problem.mass
    rw [hQ]
    simp only [restrict_prior, restrict_leg, Fin.sum_univ_two]
    rw [Problem.cellprior_singleton _ 1 hpos 0, Problem.cellprior_singleton _ 1 hpos 1]
    unfold toyD toyB; simp
  have hR2 : ∀ c, Q.R2scores V 0 c = V 1 0 c := by
    intro c
    unfold Problem.R2scores
    rw [hQ]
    simp only [restrict_prior, restrict_leg, Fin.sum_univ_two]
    rw [Problem.cellprior_singleton _ 1 hpos 0, Problem.cellprior_singleton _ 1 hpos 1]
    unfold toyD toyB; simp
  refine ⟨(R2_at_void Q V 1 hPL1).1, ?_⟩
  rw [mem_ratifiable]
  simp only [hR2, Fin.forall_fin_two, le_refl, true_and]

/-- **D1(iv), the instance**: under the penalised vector `d1R2V` both `a₀` and `a₁` are R2 fixed
points at T2 in `b`, for every penalty `0 ≤ p'` (the fixture's grid) and `0 ≤ v`:
`ratifiable = univ`.
Source: [[corr-legit-neg-inventory]] item 045 (D1(iv)); `d1_t2_floor.py:77-84`
Kind: N+
Fidelity: exact (sighted evaluators)
Hyps: (a) `0 ≤ p'`, `0 ≤ v`, `postg < 1` -/
theorem toyD_R2_instance (p' : ℚ) (hp' : 0 ≤ p') (hlt : postg < 1) (hv : 0 ≤ v) :
    ((toyD G v β p postg h0 h1).restrict {1}
      (toyD_b_cell_pos G v β p postg h0 h1 hlt)).ratifiable
        (d1R2V G v β p p') = univ := by
  obtain ⟨h1', h0'⟩ := toyD_R2_at_b G v β p postg h0 h1 hlt (d1R2V G v β p p')
  refine finset_fin2_ext ?_ ?_
  · rw [h0']; simp only [mem_univ, true_iff, d1R2V]; simp
    first
      | exact max_le (by linarith) hv
      | exact ⟨by linarith, hv⟩
      | (constructor <;> linarith)
  · simp [Problem.ratifiable, h1']

end ToyD

end Cleanroom.Corrigibility.LegitNegDynamic
