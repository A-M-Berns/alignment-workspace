import Cleanroom.Corrigibility.LegitNegPricing.Basic

/-!
# C2b: the value of correction — P3/P5 protect legitimacy only by the agent's own VOI

Package `legit-neg-pricing`, target 22 (`stretch`). Sources: `clusters/C/NEGATIVES.md` C2b,
`clusters/C/VERIFY.md` "C2b: narrowed" (V2: P4b's decision *does* depend on `q`),
`clusters/C/fixtures/c02_sources.py` (C2b), `verify_C.py` V2, pinned by
[[corr-legit-neg-inventory]] item 035.

The model is `legit-neg-static`'s `voiProblem q r g`: value uncertainty `θ ∈ {A, B}` with
credence `q` on `A`, corrected on legitimate branches; `a₁` gains `g` and voids with
probability `r`; on the void branch the agent acts on `A`, so the true grade is `(g + [θ = A])/2`
(`voiW g`, `voiK g`). The "G1 = G2 at decision time by reflection" step of the source is
ARGUMENT: the Lean takes the accurate grades as given data, and the `q`-mixture of the true
grades is what `P3`/`P5` sum (no `(c)`: the fixture's model is exact). The source's
`r(1 − max(q, 1 − q))` is the `q ≥ 1/2` case of the identity below (the model fixes the agent's
void-branch act to `A`). Exclusion convention for P2/P5.
-/

namespace Cleanroom.Corrigibility.LegitNegPricing

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

section Voi

variable (q r g : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)

/-- `voi_PL`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma voi_PL (a : Fin 2) : (voiProblem q r g hq0 hq1 hr0 hr1).PL a = ![1, 1 - r] a := by
  fin_cases a <;> simp [voiProblem, Problem.PL, Problem.mass, Fin.sum_univ_four] <;> ring

/-- `voi_P1`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma voi_P1 (a : Fin 2) :
    (voiProblem q r g hq0 hq1 hr0 hr1).P1 (S1 (voiProblem q r g hq0 hq1 hr0 hr1).u) a
      = ![1/2, (1 - r) * (g + 1) / 2] a := by
  fin_cases a <;> simp [voiProblem, Problem.P1, Fin.sum_univ_four] <;> ring

/-- `voi_P3`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma voi_P3 (a : Fin 2) :
    (voiProblem q r g hq0 hq1 hr0 hr1).P3 (voiW g) 1 (S1 (voiProblem q r g hq0 hq1 hr0 hr1).u) a
      = ![1/2, (1 - r) * (g + 1) / 2 + r * q * (g + 1) / 2 + r * (1 - q) * g / 2] a := by
  fin_cases a <;> simp [voiProblem, voiW, voiHit, Problem.P3, Fin.sum_univ_four] <;> ring

/-- `voi_H`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma voi_H (a : Fin 2) :
    (voiProblem q r g hq0 hq1 hr0 hr1).H a
      = ![1/2, (1 - r) * (g + 1) / 2 + r * q * (g + 1) / 2 + r * (1 - q) * g / 2] a := by
  fin_cases a <;> simp [voiProblem, voiHit, Problem.H, Problem.W, EU, Fin.sum_univ_four] <;> ring

/-- `voi_Kbar`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma voi_Kbar (hr : r < 1) :
    (voiProblem q r g hq0 hq1 hr0 hr1).Kbar (voiK g) 1 = (g + q) / 2 := by
  unfold Problem.Kbar
  rw [voi_PL]
  have hne : (1 - r) ≠ 0 := by linarith
  simp [voiProblem, voiK, voiHit, Fin.sum_univ_four]
  field_simp
  ring

/-- **C2b, P3**: `P3 a₁ − P3 a₀ = (g − r(1 − q))/2`, so `P3` voids iff `g > r(1 − q)` — the agent's
own value of being corrected, vanishing as its credence `q` grows, whether or not `q` is right.
Source: [[corr-legit-neg-inventory]] item 035 (C2b); `c02_sources.py` C2b
Kind: P
Fidelity: exact (the `max(q, 1 − q)` form is the `q ≥ 1/2` case; the model fixes the void-branch act)
Hyps: (a) none -/
theorem C2b_P3 :
    (voiProblem q r g hq0 hq1 hr0 hr1).P3 (voiW g) 1 (S1 (voiProblem q r g hq0 hq1 hr0 hr1).u) 1
        - (voiProblem q r g hq0 hq1 hr0 hr1).P3 (voiW g) 1 (S1 (voiProblem q r g hq0 hq1 hr0 hr1).u) 0
      = (g - r * (1 - q)) / 2
    ∧ (argmax ((voiProblem q r g hq0 hq1 hr0 hr1).P3 (voiW g) 1
          (S1 (voiProblem q r g hq0 hq1 hr0 hr1).u)) = {1} ↔ r * (1 - q) < g) := by
  constructor
  · rw [voi_P3, voi_P3]; simp; ring
  · rw [argmax_fin2_eq_one_iff, voi_P3, voi_P3]; simp; constructor <;> intro h <;> nlinarith

/-- **C2b, P5**: with the accurate assessors `voiK g`, `P5 a₁ = some ((1 − r)(g + 1)/2 + r (g + q)/2)`
and `P5 a₁ − P5 a₀ = (g − r(1 − q))/2` — the same threshold. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 035 (C2b, "likewise P5")
Kind: P
Fidelity: exact
Hyps: (a) `r < 1` -/
theorem C2b_P5 (hr : r < 1) :
    (voiProblem q r g hq0 hq1 hr0 hr1).P5 (voiK g) (S1 (voiProblem q r g hq0 hq1 hr0 hr1).u) 1
        = some ((1 - r) * (g + 1) / 2 + r * (g + q) / 2)
    ∧ (voiProblem q r g hq0 hq1 hr0 hr1).P5 (voiK g) (S1 (voiProblem q r g hq0 hq1 hr0 hr1).u) 0
        = some (1/2)
    ∧ ((1 - r) * (g + 1) / 2 + r * (g + q) / 2) - 1/2 = (g - r * (1 - q)) / 2
    ∧ (argmaxOpt ((voiProblem q r g hq0 hq1 hr0 hr1).P5 (voiK g)
          (S1 (voiProblem q r g hq0 hq1 hr0 hr1).u)) = {1} ↔ r * (1 - q) < g) := by
  have h1 : (voiProblem q r g hq0 hq1 hr0 hr1).P5 (voiK g) (S1 (voiProblem q r g hq0 hq1 hr0 hr1).u) 1
      = some ((1 - r) * (g + 1) / 2 + r * (g + q) / 2) := by
    rw [P5_of_ne _ _ _ _ (by rw [voi_PL]; simp; linarith), voi_P1, voi_PL,
      voi_Kbar q r g hq0 hq1 hr0 hr1 hr]
    simp; ring
  have h0 : (voiProblem q r g hq0 hq1 hr0 hr1).P5 (voiK g) (S1 (voiProblem q r g hq0 hq1 hr0 hr1).u) 0
      = some (1/2) := by
    unfold Problem.P5; rw [voi_PL, voi_P1]; simp
  refine ⟨h1, h0, by ring, ?_⟩
  rw [argmaxOpt_eq_argmax_of_forall_some (g := ![1/2, (1 - r) * (g + 1) / 2 + r * (g + q) / 2])
      (Fin.forall_fin_two.2 ⟨by simpa using h0, by simpa using h1⟩), argmax_fin2_eq_one_iff]
  simp; constructor <;> intro h <;> nlinarith

/-- **C2b, cdot and conditioning**: cdot voids iff `(1 − r)(1 + g) > 1` (`q`-free); conditioning
voids iff `g > 0` (`r < 1`). Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 035 (C2b)
Kind: P
Fidelity: exact -/
theorem C2b_P1_P2 (hr : r < 1) :
    (argmax ((voiProblem q r g hq0 hq1 hr0 hr1).P1 (S1 (voiProblem q r g hq0 hq1 hr0 hr1).u)) = {1}
      ↔ 1 < (1 - r) * (1 + g))
    ∧ (argmaxOpt ((voiProblem q r g hq0 hq1 hr0 hr1).P2 (S1 (voiProblem q r g hq0 hq1 hr0 hr1).u)) = {1}
      ↔ 0 < g) := by
  constructor
  · rw [argmax_fin2_eq_one_iff, voi_P1, voi_P1]; simp; constructor <;> intro h <;> nlinarith
  · rw [argmaxOpt_P2_eq_argmax_div _ _ (fun a => by rw [voi_PL]; fin_cases a <;> simp <;> linarith),
      argmax_fin2_eq_one_iff]
    simp only [voi_P1, voi_PL, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, div_one]
    rw [mul_div_assoc, mul_div_cancel_left₀ _ (by linarith : (1 - r) ≠ 0)]
    constructor <;> intro h <;> linarith

/-- The standard with the value hypothesis fixed to `hit` (`1` for `A`, `0` for `B`):
`(1 − r)(g + 1)/2 + r (g + hit)/2` (this package's local definition).
Source: [[corr-legit-neg-inventory]] item 035 (C2b, "truly worse")
Kind: D
Fidelity: exact -/
def truthEU (r g hit : ℚ) : ℚ := (1 - r) * (g + 1) / 2 + r * (g + hit) / 2

/-- **C2b, calibration**: `P3 a₁` is the `q`-mixture of the true standards
`q · truthEU r g 1 + (1 − q) · truthEU r g 0`.
Source: [[corr-legit-neg-inventory]] item 035 (C2b, "when the agent is calibrated, P3 is EU-optimal")
Kind: L
Fidelity: exact -/
theorem C2b_calibration :
    (voiProblem q r g hq0 hq1 hr0 hr1).P3 (voiW g) 1 (S1 (voiProblem q r g hq0 hq1 hr0 hr1).u) 1
      = q * truthEU r g 1 + (1 - q) * truthEU r g 0 := by
  rw [voi_P3]; unfold truthEU; simp; ring

end Voi

/-- **C2b's instance**: `q = 99/100`, `r = 1/5`, `g = 1/100`, truth `B`: `P3` and `P5` void; the
true standard is `81/200 < 1/2`, regret `19/200`.
Source: [[corr-legit-neg-inventory]] item 035 (C2b); `c02_sources.py` C2b
Kind: N+
Fidelity: exact -/
theorem C2b_instance :
    argmax ((voiProblem (99/100) (1/5) (1/100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).P3
      (voiW (1/100)) 1 (S1 (voiProblem (99/100) (1/5) (1/100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).u)) = {1}
    ∧ argmaxOpt ((voiProblem (99/100) (1/5) (1/100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).P5
      (voiK (1/100)) (S1 (voiProblem (99/100) (1/5) (1/100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).u)) = {1}
    ∧ truthEU (1/5) (1/100) 0 = 81/200 ∧ (1/2 : ℚ) - truthEU (1/5) (1/100) 0 = 19/200 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (C2b_P3 (99/100) (1/5) (1/100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2.2
      (by norm_num)
  · exact (C2b_P5 (99/100) (1/5) (1/100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).2.2.2.2 (by norm_num)
  · unfold truthEU; norm_num
  · unfold truthEU; norm_num

/-- **V2, P4b's decision depends on `q`**: at `r = 1/5`, `P4b(1/2, 1/4)` with `voiW g` voids iff
`9 g + q > 6` — the inventory headline's "P4b `q`-free" is false; only the `(κ − κ') π(B)` term
of C5's margin is `q`-free.
Source: VERIFY C "C2b: narrowed" (V2); `verify_C.py` V2
Kind: P
Fidelity: exact (refutes the headline's `q`-independence)
Hyps: (a) none -/
theorem V2_P4b_depends_on_q (q g : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    argmax ((voiProblem q (1/5) g hq0 hq1 (by norm_num) (by norm_num)).P4b (voiW g) (1/2) (1/4)
      (S1 (voiProblem q (1/5) g hq0 hq1 (by norm_num) (by norm_num)).u)) = {1}
    ↔ 6 < 9 * g + q := by
  have hP4b : ∀ a, (voiProblem q (1/5) g hq0 hq1 (by norm_num) (by norm_num)).P4b (voiW g) (1/2) (1/4)
      (S1 (voiProblem q (1/5) g hq0 hq1 (by norm_num) (by norm_num)).u) a
      = ![3/4, 3/5 + 9 * g / 40 + q / 40] a := by
    intro a; fin_cases a <;> simp [voiProblem, voiW, voiHit, Problem.P4b, Fin.sum_univ_four] <;> ring
  rw [argmax_fin2_eq_one_iff, hP4b, hP4b]; simp; constructor <;> intro h <;> linarith

end Cleanroom.Corrigibility.LegitNegPricing
