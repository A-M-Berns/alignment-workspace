import Cleanroom.Corrigibility.LegitNegPricing.Basic

/-!
# The lexical rule: C4 (no EU representation, ε-dominance, P4c's jump) and C10 (flip credence)

Package `legit-neg-pricing`, targets 23 and 24 (`stretch`). Sources: `clusters/C/NEGATIVES.md`
C4 (i), (iii), (iv) and C10, `clusters/C/VERIFY.md` "C4: survives", "C10: narrowed" (V4),
`clusters/C/fixtures/c04_lexical.py`, `c10_meta_revision.py`, pinned by
[[corr-legit-neg-inventory]] items 037, 043.

C4 (ii) (LI price noise) is ARGUMENT for LI and stays recorded only. C10's flip credences
`1/9`, `13/45` are one normalisation (V4: rescaling the current values gives `1/5`, `13/29`):
the docstrings say "illustrative"; the existence of `q* ∈ (0, 1)` is the claim.
-/

namespace Cleanroom.Corrigibility.LegitNegPricing

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

/-- On a two-option menu the lexicographic argmax is `{0}` iff `f 1 < f 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmaxLex_fin2_eq_zero_iff (f : Fin 2 → ℚ ×ₗ ℚ) : argmaxLex f = {0} ↔ f 1 < f 0 := by
  constructor
  · intro h
    have h1 : (1 : Fin 2) ∉ argmaxLex f := by rw [h]; simp
    rw [mem_argmaxLex] at h1
    simp only [Fin.forall_fin_two, le_refl, and_true, not_le] at h1
    exact h1
  · intro h
    refine finset_fin2_ext ?_ ?_ <;> simp only [mem_argmaxLex, mem_singleton, Fin.forall_fin_two]
    · simp [h.le]
    · simp [not_le.2 h]

/-! ### C4 (iii): no expected-utility representation -/

/-- The mixture `α x + (1 − α) y` on `ℚ × ℚ` (coordinatewise).
Source: [[corr-legit-neg-inventory]] item 037 (C4 (iii))
Kind: D
Fidelity: exact -/
def mix (α : ℚ) (x y : ℚ × ℚ) : ℚ × ℚ := (α * x.1 + (1 - α) * y.1, α * x.2 + (1 - α) * y.2)

/-- **C4 (iii)**: no `u : ℚ × ℚ → ℚ` is both mixture-linear (on `α ∈ [0, 1]`) and strictly
increasing for the lexicographic order — the Archimedean failure. Quantified over *all* such `u`;
the witness is `A = (1, 1) ≻ B = (1, 0) ≻ C = (0, 1)` with `mix α A C = (α, 1) <ₗ B` for `α < 1`,
and `α` is chosen explicitly from `u`'s values (`α > (u B − u C)/(u A − u C)`).
Source: [[corr-legit-neg-inventory]] item 037 (C4 (iii)); NEGATIVES C4 proof
Kind: P
Fidelity: exact (over `ℚ`; the argument is ordered-field arithmetic)
Hyps: (a) none -/
theorem no_EU_representation :
    ¬ ∃ u : ℚ × ℚ → ℚ,
      (∀ α x y, 0 ≤ α → α ≤ 1 → u (mix α x y) = α * u x + (1 - α) * u y)
      ∧ (∀ x y, toLex x < toLex y → u x < u y) := by
  rintro ⟨u, hlin, hmono⟩
  have hBA : u (1, 0) < u (1, 1) := hmono _ _ (by rw [Prod.Lex.toLex_lt_toLex]; simp)
  have hCB : u (0, 1) < u (1, 0) := hmono _ _ (by rw [Prod.Lex.toLex_lt_toLex]; simp)
  set ρ : ℚ := (u (1, 0) - u (0, 1)) / (u (1, 1) - u (0, 1)) with hρ
  have hden : 0 < u (1, 1) - u (0, 1) := by linarith
  have hρ0 : 0 < ρ := by rw [hρ]; exact div_pos (by linarith) hden
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hden]; linarith
  set α : ℚ := (ρ + 1) / 2 with hα
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith
  have hαρ : ρ < α := by rw [hα]; linarith
  have hmix : mix α (1, 1) (0, 1) = (α, 1) := by simp [mix]
  have hlt : u (mix α (1, 1) (0, 1)) < u (1, 0) :=
    hmono _ _ (by rw [hmix, Prod.Lex.toLex_lt_toLex]; simp [hα1])
  rw [hlin α _ _ hα0 hα1.le] at hlt
  have : α * (u (1, 1) - u (0, 1)) > u (1, 0) - u (0, 1) := by
    have := (div_lt_iff₀ hden).1 hαρ
    rw [← hρ] at *
    linarith [(div_lt_iff₀ hden).1 (show ρ < α from hαρ)]
  linarith

/-! ### C4 (i): ε-dominance on `epsProblem` -/

/-- `eps_PL`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eps_PL (ε w : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (a : Fin 2) :
    (epsProblem ε w h0 h1).PL a = ![1, 1 - ε] a := by
  fin_cases a <;> simp [epsProblem, Problem.PL, Problem.mass, Fin.sum_univ_two]

/-- `eps_P3`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eps_P3 (ε w w' : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (a : Fin 2) :
    (epsProblem ε w h0 h1).P3 (epsW w') 1 epsV a = ![0, (1 - ε) + ε * w'] a := by
  fin_cases a <;> simp [epsProblem, epsW, epsV, Problem.P3, Fin.sum_univ_two] <;> ring

/-- **C4 (i)**: on `epsProblem ε w` the literal lexical rule picks `safe` for every `ε > 0`
(`P4a safe = (1, 0) ≻ (1 − ε, ·)`), while `P4b(1/2, 2/5)` with `epsW w` and `epsV` is exactly
`H` on every option; with the fixture's `w = 9/10`, `H good − H safe = 1/2 − ε + (9/25) ε`
(the whole legitimate range as `ε → 0`), positive for `ε < 25/32`.
Source: [[corr-legit-neg-inventory]] item 037 (C4 (i)); `c04_lexical.py`
Kind: P
Fidelity: exact (parametric in `ε`)
Hyps: (a) `0 < ε` for the P4a clause -/
theorem C4_eps_dominance (ε w : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (0 < ε → argmaxLex ((epsProblem ε w h0 h1).P4a (epsW w) epsV) = {0})
    ∧ (∀ a, (epsProblem ε w h0 h1).P4b (epsW w) (1/2) (2/5) epsV a = (epsProblem ε w h0 h1).H a)
    ∧ (epsProblem ε (9/10) h0 h1).H 1 - (epsProblem ε (9/10) h0 h1).H 0 = 1/2 - ε + 9/25 * ε
    ∧ (ε < 25/32 → argmax (epsProblem ε (9/10) h0 h1).H = {1}) := by
  refine ⟨fun hε => ?_, fun a => ?_, ?_, fun hε => ?_⟩
  · rw [argmaxLex_fin2_eq_zero_iff]
    simp only [Problem.P4a, eps_PL, eps_P3]
    rw [Prod.Lex.toLex_lt_toLex]
    simp [hε]
  · fin_cases a <;> simp [epsProblem, epsW, epsV, Problem.P4b, Problem.H, Problem.W, EU,
      Fin.sum_univ_two] <;> ring
  · simp [epsProblem, Problem.H, Problem.W, EU, Fin.sum_univ_two]; ring
  · rw [argmax_fin2_eq_one_iff]
    simp [epsProblem, Problem.H, Problem.W, EU, Fin.sum_univ_two]; linarith

/-! ### C4 (iv): the tolerance rule's jump -/

/-- **C4 (iv)**: `P4c(1/100)` on `epsProblem t 0` (a legitimacy gap of `t`) takes the grade-`1`
option at `t = 1/100` and the grade-`0` option at `t = 1/100 + 10⁻⁶`: the jump is the whole
legitimate range.
Source: [[corr-legit-neg-inventory]] item 037 (C4 (iv)); `c04_lexical.py` C4(iv)
Kind: N+
Fidelity: exact -/
theorem C4_P4c_jump :
    (epsProblem (1/100) 0 (by norm_num) (by norm_num)).P4c (epsW 0) (1/100) epsV = {1}
    ∧ (epsProblem (1/100 + 1/1000000) 0 (by norm_num) (by norm_num)).P4c (epsW 0) (1/100) epsV = {0} := by
  have hbest : ∀ (t : ℚ) (h0 : 0 ≤ t) (h1 : t ≤ 1),
      univ.sup' univ_nonempty (epsProblem t 0 h0 h1).PL = 1 := by
    intro t h0 h1
    rw [sup'_fin2, eps_PL, eps_PL]; simp; linarith
  constructor
  · have hb := hbest (1/100) (by norm_num) (by norm_num)
    unfold Problem.P4c
    refine finset_fin2_ext ?_ ?_ <;>
      simp only [mem_filter, mem_univ, true_and, mem_singleton] <;>
      rw [hb] <;> simp only [Fin.forall_fin_two, eps_PL, eps_P3] <;> norm_num
  · have hb := hbest (1/100 + 1/1000000) (by norm_num) (by norm_num)
    unfold Problem.P4c
    refine finset_fin2_ext ?_ ?_ <;>
      simp only [mem_filter, mem_univ, true_and, mem_singleton] <;>
      rw [hb] <;> simp only [Fin.forall_fin_two, eps_PL, eps_P3] <;> norm_num

/-! ### C10: the flip credence of a learned Archimedean premium -/

/-- The keep-minus-void margin under the `q`-mixture of the current values (margin `D_cur`) and
the anticipated revision (`v − w` on one scale).
Source: [[corr-legit-neg-inventory]] item 043 (C10)
Kind: D
Fidelity: exact -/
def margin (Dcur v w q : ℚ) : ℚ := (1 - q) * Dcur + q * (v - w)

/-- **C10 (parametric)**: for `D_cur > 0` and `w > v`, the margin is positive iff
`q < q* := D_cur/(D_cur + w − v)`, and `q* ∈ (0, 1)`: every learned Archimedean premium has a
flip credence below `1`.
Source: [[corr-legit-neg-inventory]] item 043 (C10); NEGATIVES C10 proof
Kind: P
Fidelity: exact
Hyps: (a) `0 < D_cur`, `v < w` -/
theorem C10_flip (Dcur v w q : ℚ) (hD : 0 < Dcur) (hw : v < w) :
    (0 < margin Dcur v w q ↔ q < Dcur / (Dcur + w - v))
    ∧ 0 < Dcur / (Dcur + w - v) ∧ Dcur / (Dcur + w - v) < 1 := by
  have hden : 0 < Dcur + w - v := by linarith
  refine ⟨?_, div_pos hD hden, by rw [div_lt_one hden]; linarith⟩
  unfold margin
  rw [lt_div_iff₀ hden]
  constructor <;> intro h <;> nlinarith

/-- **C10's instances (illustrative, V4)**: with `v = 1/10`, `w = 9/10`: a learned floor
(`D_cur = v`) flips at `1/9`; a learned gap `D_cur = κ + (1 − κ) v − κ' w` at `(1/2, 1/4)` flips at
`13/45`; rescaling the current values by `2` gives `1/5` and `13/29` — the numbers are
normalisation-dependent, the existence of `q* ∈ (0, 1)` is not.
Source: [[corr-legit-neg-inventory]] item 043 (C10); VERIFY C "C10: narrowed" (V4)
Kind: N+
Fidelity: exact (illustrative values) -/
theorem C10_instances :
    (1/10 : ℚ) / (1/10 + 9/10 - 1/10) = 1/9
    ∧ ((1/2 : ℚ) + (1 - 1/2) * (1/10) - 1/4 * (9/10)) / ((1/2 + (1 - 1/2) * (1/10) - 1/4 * (9/10)) + 9/10 - 1/10) = 13/45
    ∧ (2 * (1/10) : ℚ) / (2 * (1/10) + 9/10 - 1/10) = 1/5
    ∧ (2 * (1/2 + (1 - 1/2) * (1/10) - 1/4 * (9/10)) : ℚ)
        / (2 * (1/2 + (1 - 1/2) * (1/10) - 1/4 * (9/10)) + 9/10 - 1/10) = 13/29 := by
  norm_num

/-- The lexical mixture of C10: tier weight `(1 − q) · 1_L`, then the mixed grade.
Source: [[corr-legit-neg-inventory]] item 043 (C10, P4a)
Kind: D
Fidelity: exact -/
def lexMix (q v w : ℚ) : Fin 2 → ℚ ×ₗ ℚ :=
  ![toLex ((1 - q) * 1, (1 - q) * v + q * v), toLex ((1 - q) * 0, (1 - q) * w + q * w)]

/-- **C10, P4a**: the lexical mixture keeps `L` for every `q < 1` (the tier survives any
positive weight).
Source: [[corr-legit-neg-inventory]] item 043 (C10, "P4a none below 1")
Kind: L
Fidelity: exact -/
theorem C10_lex_keeps (q v w : ℚ) (hq : q < 1) : argmaxLex (lexMix q v w) = {0} := by
  rw [argmaxLex_fin2_eq_zero_iff]
  simp only [lexMix, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [Prod.Lex.toLex_lt_toLex]
  left; linarith

/-- **C10, specified constraints**: a specified floor (margin `v`) or gap (margin `D₀`) does not
depend on `q`, so never flips (trivial).
Source: [[corr-legit-neg-inventory]] item 043 (C10, "specified constraints none")
Kind: L
Fidelity: exact -/
theorem C10_specified (D v w q : ℚ) (hD : 0 < D) : 0 < margin D v w 0 ∧ ((1 - q) * D + q * D = D) := by
  unfold margin; exact ⟨by simp [hD], by ring⟩

end Cleanroom.Corrigibility.LegitNegPricing
