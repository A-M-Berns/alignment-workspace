import Cleanroom.Corrigibility.LegitNegPricing.Basic

/-!
# Steering and capture: C1 thresholds, C2a capture (+ 2-031), C5 the cardinal gap, C8 positivity

Package `legit-neg-pricing`, targets 16, 17, 19, 20. Sources: `clusters/C/NEGATIVES.md` C1, C2a,
C5, C8, `clusters/C/VERIFY.md` (C1/C5/C8 survive, C2a narrowed: "G3 is the LI default" is
contested), `clusters/C/fixtures/c01_toy_thresholds.py`, `c02_sources.py`, `c05_gap.py`,
`c08_p5_voiding.py`, pinned by [[corr-legit-neg-inventory]] items 033, 034, 038, 041 and
[[corr-legit-neg-2-inventory]] items 2-019, 2-031.

Register: steering toward illegitimacy is a failure only if the void grade misrepresents human
value (C1's fairness paragraph); the void-grade *source* (G1/G2/G3) is a parameter here, never a
default. "P4b is the only row with no unconditional fails" was narrowed by the verifier and is
claimed nowhere. Exclusion convention for every P2/P5 statement.
-/

namespace Cleanroom.Corrigibility.LegitNegPricing

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

variable {S A : Type} [Fintype S] [Fintype A]

/-! ### C1: the general P3/P5 identities -/

/-- **C1, the general P3 identity**: for `a₀` legitimate everywhere and `a₁` voiding exactly on
`B`, `P3 λ a₁ − P3 λ a₀ = ∑_{s ∈ B} π (λ W_{s,a₁}(a₁) − V_{s,a₀}(a₀)) + ∑_{s ∉ B} π (V_{s,a₁}(a₁) − V_{s,a₀}(a₀))`
(indicator form; `λ = 1` is the note's). P3 steers iff the void grades on `B` beat the legitimate
scores they replace by more than the net loss off `B`.
Source: [[corr-legit-neg-inventory]] item 033 (C1, general identity); NEGATIVES C1
Kind: P
Fidelity: exact
Hyps: (a) the two legitimacy shapes -/
theorem P3_void_sub_keep [DecidableEq S] (P : Problem S A) (Wg V : MenuVec S A) (lam : ℚ)
    (a0 a1 : A) (B : Finset S) (h0 : ∀ s, P.leg s a0 = true)
    (h1 : ∀ s, P.leg s a1 = !decide (s ∈ B)) :
    P.P3 Wg lam V a1 - P.P3 Wg lam V a0
      = (∑ s, P.prior s * ind (decide (s ∈ B)) * (lam * Wg s a1 a1 - V s a0 a0))
        + ∑ s, P.prior s * ind (!decide (s ∈ B)) * (V s a1 a1 - V s a0 a0) := by
  unfold Problem.P3
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [h0 s, h1 s]
  by_cases hs : s ∈ B <;> simp [hs] <;> ring

/-- **C1, the P5 analogue**: with `a₀` fully legitimate and `a₁` voiding on `B` of positive kept
mass, `P5 a₁ − P5 a₀` (on the defined values) is the off-`B` score difference plus
`π(B) · K̄ a₁ − ∑_{s ∈ B} π V_{s,a₀}(a₀)`. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 033 (C1, "P5 with P(¬L|a₁) 𝔼(K|L,a₁) in place of the B sum")
Kind: P
Fidelity: exact
Hyps: (a) the two legitimacy shapes; `P(L | a₁) ≠ 0` -/
theorem P5_void_sub_keep [DecidableEq S] (P : Problem S A) (K V : MenuVec S A) (a0 a1 : A)
    (B : Finset S) (h0 : ∀ s, P.leg s a0 = true) (h1 : ∀ s, P.leg s a1 = !decide (s ∈ B))
    (hk : P.PL a1 ≠ 0) :
    P.P5 K V a1 = some (P.P1 V a1 + (1 - P.PL a1) * P.Kbar K a1)
    ∧ P.P5 K V a0 = some (P.P1 V a0)
    ∧ (P.P1 V a1 + (1 - P.PL a1) * P.Kbar K a1) - P.P1 V a0
      = (∑ s, P.prior s * ind (!decide (s ∈ B)) * (V s a1 a1 - V s a0 a0))
        + (P.mass (fun s => decide (s ∈ B)) * P.Kbar K a1
            - ∑ s, P.prior s * ind (decide (s ∈ B)) * V s a0 a0) := by
  have hPL0 : P.PL a0 = 1 := by
    unfold Problem.PL Problem.mass; simp only [h0, ind_true, mul_one]; exact P.prior_sum
  have hmass : 1 - P.PL a1 = P.mass (fun s => decide (s ∈ B)) := by
    unfold Problem.PL
    rw [show (fun s => P.leg s a1) = fun s => !decide (s ∈ B) from funext h1, P.mass_not]; ring
  refine ⟨P5_of_ne _ _ _ _ hk, ?_, ?_⟩
  · unfold Problem.P5; rw [if_neg (by rw [hPL0]; exact one_ne_zero), if_pos hPL0]
  · rw [hmass]
    have hP1 : P.P1 V a1 - P.P1 V a0
        = (∑ s, P.prior s * ind (!decide (s ∈ B)) * (V s a1 a1 - V s a0 a0))
          - ∑ s, P.prior s * ind (decide (s ∈ B)) * V s a0 a0 := by
      unfold Problem.P1
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [h0 s, h1 s]
      by_cases hs : s ∈ B <;> simp [hs] <;> ring
    linarith

/-! ### C1 on the toy -/

section C1Toy

variable (v p x c κ κ' : ℚ)

/-- `toyC_PL`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyC_PL (a : Fin 2) : (toyC v p x).PL a = ![1, 1/2] a := by
  fin_cases a <;> simp [toyC, Problem.PL, Problem.mass, Fin.sum_univ_two] <;> norm_num

/-- `toyC_P1`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyC_P1 (a : Fin 2) :
    (toyC v p x).P1 (S1 (toyC v p x).u) a = ![(1 + v) / 2, (1 - p) / 2] a := by
  fin_cases a <;> simp [toyC, Problem.P1, Fin.sum_univ_two] <;> ring

/-- `toyC_P3`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyC_P3 : ∀ a, (toyC v p x).P3 (toyC_W x) 1 (S1 (toyC v p x).u) a
    = ![(1 + v) / 2, (1 - p + x) / 2] a := by
  intro a; fin_cases a <;> simp [toyC, toyC_W, Problem.P3, Fin.sum_univ_two] <;> ring

/-- `toyC_P4b`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyC_P4b : ∀ a, (toyC v p x).P4b (toyC_W x) κ κ' (S1 (toyC v p x).u) a
    = ![κ + (1 - κ) * (1 + v) / 2, (κ + (1 - κ) * (1 - p)) / 2 + κ' * x / 2] a := by
  intro a; fin_cases a <;> simp [toyC, toyC_W, Problem.P4b, Fin.sum_univ_two] <;> ring

/-- `toyC_P5`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyC_P5 : (toyC v p x).P5 (toyC_K c) (S1 (toyC v p x).u) 0 = some ((1 + v) / 2)
    ∧ (toyC v p x).P5 (toyC_K c) (S1 (toyC v p x).u) 1 = some ((1 - p) / 2 + c / 2) := by
  constructor
  · simp [Problem.P5, toyC_PL, toyC_P1]
  · have hK : (toyC v p x).Kbar (toyC_K c) 1 = c := by
      unfold Problem.Kbar
      simp [toyC, toyC_K, Problem.PL, Problem.mass, Fin.sum_univ_two] <;> ring
    rw [P5_of_ne _ _ _ _ (by rw [toyC_PL]; norm_num), hK, toyC_P1, toyC_PL]
    simp <;> ring

/-- **C1 on the toy**: `P3` voids iff `x > v + p`; `P5` voids iff `c > v + p`; `P2` voids iff
`p < (1 − v)/2`; cdot strictly keeps iff `v + p > 0` with `P1 a₀ − P1 a₁ = (v + p)/2` (tie iff
`v = p = 0`, given `v, p ≥ 0` — the assertion C1's fixture never makes); and
`P4b a₀ − P4b a₁ = ½[(1 − κ)(v + p) + κ − κ' x] > 0` for `0 ≤ x ≤ 1`, `0 ≤ κ' < κ ≤ 1`,
`0 ≤ v, p`. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 033 (C1); `c01_toy_thresholds.py`
Kind: P
Fidelity: exact
Hyps: (a) the ranges on the P4b clause are the source's -/
theorem C1_toy :
    (argmax ((toyC v p x).P3 (toyC_W x) 1 (S1 (toyC v p x).u)) = {1} ↔ v + p < x)
    ∧ (argmaxOpt ((toyC v p x).P5 (toyC_K c) (S1 (toyC v p x).u)) = {1} ↔ v + p < c)
    ∧ (argmaxOpt ((toyC v p x).P2 (S1 (toyC v p x).u)) = {1} ↔ p < (1 - v) / 2)
    ∧ (toyC v p x).P1 (S1 (toyC v p x).u) 0 - (toyC v p x).P1 (S1 (toyC v p x).u) 1 = (v + p) / 2
    ∧ (0 ≤ v → 0 ≤ p →
        ((toyC v p x).P1 (S1 (toyC v p x).u) 0 = (toyC v p x).P1 (S1 (toyC v p x).u) 1
          ↔ v = 0 ∧ p = 0))
    ∧ (toyC v p x).P4b (toyC_W x) κ κ' (S1 (toyC v p x).u) 0
        - (toyC v p x).P4b (toyC_W x) κ κ' (S1 (toyC v p x).u) 1
      = ((1 - κ) * (v + p) + κ - κ' * x) / 2
    ∧ (0 ≤ x → x ≤ 1 → 0 ≤ κ' → κ' < κ → κ ≤ 1 → 0 ≤ v → 0 ≤ p →
        argmax ((toyC v p x).P4b (toyC_W x) κ κ' (S1 (toyC v p x).u)) = {0}) := by
  have hPL : ∀ a, (toyC v p x).PL a ≠ 0 := by
    intro a; rw [toyC_PL]; fin_cases a <;> simp
  refine ⟨?_, ?_, ?_, ?_, fun hv hp => ?_, ?_, fun hx0 hx1 hk0 hk hk1 hv hp => ?_⟩
  · rw [argmax_fin2_eq_one_iff, toyC_P3, toyC_P3]; simp; constructor <;> intro h <;> linarith
  · rw [argmaxOpt_eq_argmax_of_forall_some (g := ![(1 + v) / 2, (1 - p) / 2 + c / 2])
        (Fin.forall_fin_two.2 ⟨by simpa using (toyC_P5 v p x c).1, by simpa using (toyC_P5 v p x c).2⟩),
      argmax_fin2_eq_one_iff]
    simp; constructor <;> intro h <;> linarith
  · rw [argmaxOpt_P2_eq_argmax_div _ _ hPL, argmax_fin2_eq_one_iff]
    simp only [toyC_P1, toyC_PL, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    norm_num; constructor <;> intro h <;> linarith
  · rw [toyC_P1, toyC_P1]; simp; ring
  · rw [toyC_P1, toyC_P1]; simp
    constructor
    · intro h; constructor <;> linarith
    · rintro ⟨h1, h2⟩; subst h1; subst h2; norm_num
  · rw [toyC_P4b, toyC_P4b]; simp; ring
  · rw [argmax_fin2_eq_zero_iff, toyC_P4b, toyC_P4b]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ 1 - κ) (by linarith : (0:ℚ) ≤ v + p),
      mul_le_mul_of_nonneg_left hx1 hk0]

/-- **2-019, C11 (c)**: at `v = 1` (the humans at `(b, a₀)` rank `a₀` top: the S3-relative
reading of the C1 toy) no proposal strictly prefers voiding: `P1 a₀ − P1 a₁ = (1 + p)/2 > 0`,
`P2 a₀ = some 1 ≥ some (1 − p)`, `P3 a₁ − P3 a₀ = (x − 1 − p)/2 ≤ 0` and likewise `P5` with
`c`, for `x, c ≤ 1`, `p ≥ 0`. Exclusion convention.
Source: [[corr-legit-neg-2-inventory]] item 2-019; `c11_scorings.py` C11(c)
Kind: P
Fidelity: exact -/
theorem C11c_no_steering (hp : 0 ≤ p) (hx : x ≤ 1) (hc : c ≤ 1) :
    (toyC 1 p x).P1 (S1 (toyC 1 p x).u) 0 - (toyC 1 p x).P1 (S1 (toyC 1 p x).u) 1 = (1 + p) / 2
    ∧ 0 < (1 + p) / 2
    ∧ (toyC 1 p x).P2 (S1 (toyC 1 p x).u) 0 = some 1
    ∧ (toyC 1 p x).P2 (S1 (toyC 1 p x).u) 1 = some (1 - p)
    ∧ (toyC 1 p x).P3 (toyC_W x) 1 (S1 (toyC 1 p x).u) 1
        - (toyC 1 p x).P3 (toyC_W x) 1 (S1 (toyC 1 p x).u) 0 = (x - 1 - p) / 2
    ∧ (x - 1 - p) / 2 ≤ 0
    ∧ ((1 - p) / 2 + c / 2) - (1 + 1) / 2 ≤ 0 := by
  have hPL : ∀ a, (toyC 1 p x).PL a ≠ 0 := by
    intro a; rw [toyC_PL]; fin_cases a <;> simp
  refine ⟨?_, by linarith, ?_, ?_, ?_, by linarith, by linarith⟩
  · rw [toyC_P1, toyC_P1]; simp; ring
  · rw [P2_of_ne _ _ _ (hPL 0), toyC_P1, toyC_PL]; simp <;> norm_num
  · rw [P2_of_ne _ _ _ (hPL 1), toyC_P1, toyC_PL]; simp <;> ring
  · rw [toyC_P3, toyC_P3]; simp; ring

end C1Toy

/-! ### C2a: capture, and 2-031's constant void grade -/

section Capture

variable (vb r κ κ' : ℚ)

/-- `capture_PL`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma capture_PL (a : Fin 2) : (capture vb).PL a = ![1, 1/2] a := by
  fin_cases a <;> simp [capture, Problem.PL, Problem.mass, Fin.sum_univ_two] <;> norm_num

/-- `capture_P1`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma capture_P1 (a : Fin 2) :
    (capture vb).P1 (captureV vb) a = ![1/4 + vb / 2, 1/4] a := by
  fin_cases a <;> simp [capture, captureV, Problem.P1, Fin.sum_univ_two] <;> ring

/-- `capture_P3`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma capture_P3 (a : Fin 2) :
    (capture vb).P3 (captureW r) 1 (captureV vb) a = ![1/4 + vb / 2, 1/4 + r / 2] a := by
  fin_cases a <;> simp [capture, captureV, captureW, Problem.P3, Fin.sum_univ_two] <;> ring

/-- `capture_P4b`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma capture_P4b (a : Fin 2) :
    (capture vb).P4b (captureW r) κ κ' (captureV vb) a
      = ![κ + (1 - κ) * (1/4 + vb / 2), (κ + (1 - κ) / 2) / 2 + κ' * r / 2] a := by
  fin_cases a <;> simp [capture, captureV, captureW, Problem.P4b, Fin.sum_univ_two] <;> ring

/-- **C2a**: on `capture vb` with the captured report `r` as P3's G3 grade,
`P3 cap − P3 a₀ = (r − v_b)/2` (P3 captures iff `r > v_b`); `P4b a₀ − P4b cap = ½(κ + (1 − κ) v_b − κ' r)`,
at least `½(κ − κ')` for `0 ≤ v_b`, `r ≤ 1`, `κ ≤ 1`, `0 ≤ κ'`; `P1`, `P4a` and `P5` (with
`captureK ≡ 0`) choose `a₀` for every `r` (`P1`/`P5` strictly iff `v_b > 0`); `P2` never reads
`r` (syntactically: `(capture vb).P2 (captureV vb)` has no `r`) and is indifferent exactly at
`v_b = 1/2`. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 034 (C2a); `c02_sources.py` C2a; VERIFY C "C2a: narrowed"
Kind: P
Fidelity: exact (G3 as the source; "G3 is the LI default" is contested and not claimed) -/
theorem C2a_capture :
    (capture vb).P3 (captureW r) 1 (captureV vb) 1 - (capture vb).P3 (captureW r) 1 (captureV vb) 0
        = (r - vb) / 2
    ∧ (argmax ((capture vb).P3 (captureW r) 1 (captureV vb)) = {1} ↔ vb < r)
    ∧ (capture vb).P4b (captureW r) κ κ' (captureV vb) 0
        - (capture vb).P4b (captureW r) κ κ' (captureV vb) 1
        = (κ + (1 - κ) * vb - κ' * r) / 2
    ∧ (0 ≤ vb → r ≤ 1 → κ ≤ 1 → 0 ≤ κ' →
        (κ - κ') / 2 ≤ (κ + (1 - κ) * vb - κ' * r) / 2)
    ∧ (argmax ((capture vb).P1 (captureV vb)) = {0} ↔ 0 < vb)
    ∧ argmaxLex ((capture vb).P4a (captureW r) (captureV vb)) = {0}
    ∧ (argmaxOpt ((capture vb).P5 captureK (captureV vb)) = {0} ↔ 0 < vb)
    ∧ (argmaxOpt ((capture vb).P2 (captureV vb)) = univ ↔ vb = 1/2) := by
  have hPL : ∀ a, (capture vb).PL a ≠ 0 := by
    intro a; rw [capture_PL]; fin_cases a <;> simp
  have hP50 : (capture vb).P5 captureK (captureV vb) 0 = some (1/4 + vb / 2) := by
    simp [Problem.P5, capture_PL, capture_P1]
  have hP51 : (capture vb).P5 captureK (captureV vb) 1 = some (1/4) := by
    rw [P5_of_ne _ _ _ _ (hPL 1), capture_P1]
    have : (capture vb).Kbar captureK 1 = 0 := by simp [Problem.Kbar, captureK]
    rw [this]; simp
  have hP5 : ∀ a, (capture vb).P5 captureK (captureV vb) a = some (![1/4 + vb / 2, 1/4] a) :=
    Fin.forall_fin_two.2 ⟨by simpa using hP50, by simpa using hP51⟩
  refine ⟨?_, ?_, ?_, fun h0 h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [capture_P3, capture_P3]; simp; ring
  · rw [argmax_fin2_eq_one_iff, capture_P3, capture_P3]; simp; constructor <;> intro h <;> linarith
  · rw [capture_P4b, capture_P4b]; simp; ring
  · nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ 1 - κ) h0, mul_le_mul_of_nonneg_left h1 h3]
  · rw [argmax_fin2_eq_zero_iff, capture_P1, capture_P1]; simp
  · refine finset_fin2_ext ?_ ?_ <;>
      simp only [mem_argmaxLex, mem_singleton, Fin.forall_fin_two, Problem.P4a,
        Prod.Lex.toLex_le_toLex, capture_PL] <;> norm_num
  · rw [argmaxOpt_eq_argmax_of_forall_some hP5, argmax_fin2_eq_zero_iff]; simp
  · rw [argmaxOpt_P2_eq_argmax_div _ _ hPL, argmax_fin2_eq_univ_iff]
    simp only [capture_P1, capture_PL, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    norm_num; constructor <;> intro h <;> linarith

end Capture

/-- **2-031, the constant void grade**: if `Wg s a a = c` on every void terminal of `a`, then
`P4b Wg κ κ' V a = (1 − κ) P1 V a + (κ − κ' c) P(L | a) + κ' c` — cdot plus a legitimacy premium
that reads no void report (hence C2a's capture has no channel), with premium `≥ κ − κ'` for
`c ≤ 1`, `κ' ≥ 0`.
Source: [[corr-legit-neg-2-inventory]] item 2-031; `clusters/C/NEGATIVES.md:68`
Kind: P
Fidelity: exact
Hyps: (a) the constant-grade hypothesis is the workspace's window reading, taken as an assumption on `Wg` -/
theorem P4b_const_void (P : Problem S A) (Wg V : MenuVec S A) (κ κ' c : ℚ) (a : A)
    (hW : ∀ s, P.leg s a = false → Wg s a a = c) :
    P.P4b Wg κ κ' V a = (1 - κ) * P.P1 V a + (κ - κ' * c) * P.PL a + κ' * c
    ∧ (c ≤ 1 → 0 ≤ κ' → κ - κ' ≤ κ - κ' * c) := by
  constructor
  · unfold Problem.P4b Problem.P1 Problem.PL Problem.mass
    have hsum : ∑ s, P.prior s * (ind (P.leg s a) * (κ + (1 - κ) * V s a a) + ind (!P.leg s a) * κ' * Wg s a a)
        = ∑ s, ((1 - κ) * (P.prior s * ind (P.leg s a) * V s a a)
            + (κ - κ' * c) * (P.prior s * ind (P.leg s a)) + κ' * c * P.prior s) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hs : P.leg s a = true
      · simp [hs]; ring
      · simp only [Bool.not_eq_true] at hs
        rw [hW s hs]; simp [hs]; ring
    rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, P.prior_sum, mul_one]
  · intro hc hk; nlinarith [mul_le_mul_of_nonneg_left hc hk]

/-- **2-031's congruence**: two void grades agreeing off void terminals — or any two constant on
them with the same constant — give the same `P4b`; nothing written at a void terminal other
than the constant is read.
Source: [[corr-legit-neg-2-inventory]] item 2-031
Kind: C
Fidelity: exact -/
theorem P4b_const_void_congr (P : Problem S A) (Wg Wg' V : MenuVec S A) (κ κ' c : ℚ) (a : A)
    (hW : ∀ s, P.leg s a = false → Wg s a a = c) (hW' : ∀ s, P.leg s a = false → Wg' s a a = c) :
    P.P4b Wg κ κ' V a = P.P4b Wg' κ κ' V a := by
  rw [(P4b_const_void P Wg V κ κ' c a hW).1, (P4b_const_void P Wg' V κ κ' c a hW').1]

/-! ### C5: the cardinal gap -/

/-- **C5 (a), absolute protection at T2**: in any problem, at a terminal state `s` (all mass on
`s`, formalised as `P.restrict {s} _`) where `a` keeps legitimacy and `b` voids it, with
`0 ≤ V ≤ 1`, `0 ≤ Wg ≤ 1` and `0 ≤ κ' < κ ≤ 1`, `P4b b < P4b a` — whatever the void grade's
source or error.
Source: [[corr-legit-neg-inventory]] item 038 (C5 (a)); NEGATIVES C5 proof (`κ' W ≤ κ' < κ ≤ κ + (1 − κ) V`)
Kind: P
Fidelity: exact
Hyps: (a) the ranges and the gap `κ' < κ` are the source's modelling assumptions -/
theorem C5_T2 [DecidableEq S] (P : Problem S A) (s : S) (hs : 0 < P.prior s) (Wg V : MenuVec S A)
    (κ κ' : ℚ) (a b : A) (ha : P.leg s a = true) (hb : P.leg s b = false)
    (hV : 0 ≤ V s a a) (hW : Wg s b b ≤ 1) (hk0 : 0 ≤ κ') (hk : κ' < κ) (hk1 : κ ≤ 1) :
    (P.restrict {s} (by simpa using hs)).P4b Wg κ κ' V b
      < (P.restrict {s} (by simpa using hs)).P4b Wg κ κ' V a := by
  have key : ∀ c, (P.restrict {s} (by simpa using hs)).P4b Wg κ κ' V c
      = ind (P.leg s c) * (κ + (1 - κ) * V s c c) + ind (!P.leg s c) * κ' * Wg s c c := by
    intro c
    unfold Problem.P4b
    simp only [restrict_leg, restrict_prior, P.cellprior_singleton s hs]
    simp [Finset.sum_ite_eq']
  rw [key, key, ha, hb]
  simp only [ind_true, Bool.not_true, ind_false, Bool.not_false, one_mul, zero_mul, add_zero,
    zero_add]
  nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ 1 - κ) hV, mul_le_mul_of_nonneg_left hW hk0]

/-- **C5 (b), the T1 margin**: for `a₀` legitimate everywhere and `a₁` voiding on `B`, with
`0 ≤ V`, `Wg ≤ 1`, `0 ≤ κ'`, `κ ≤ 1`,
`P4b a₀ − P4b a₁ ≥ (κ − κ') π(B) − (1 − κ) ∑_{s ∉ B} π max 0 (V_{s,a₁}(a₁) − V_{s,a₀}(a₀))`:
protection per unit of voided mass at least `κ − κ'` even where `V = 0` (no tie at `v = 0`).
Source: [[corr-legit-neg-inventory]] item 038 (C5 (b)); NEGATIVES C5 proof
Kind: P
Fidelity: exact
Hyps: (a) the ranges are the source's modelling assumptions -/
theorem C5_T1_margin [DecidableEq S] (P : Problem S A) (Wg V : MenuVec S A) (κ κ' : ℚ) (a0 a1 : A)
    (B : Finset S) (h0 : ∀ s, P.leg s a0 = true) (h1 : ∀ s, P.leg s a1 = !decide (s ∈ B))
    (hV : ∀ s, 0 ≤ V s a0 a0) (hW : ∀ s, Wg s a1 a1 ≤ 1) (hk0 : 0 ≤ κ') (hk1 : κ ≤ 1) :
    (κ - κ') * P.mass (fun s => decide (s ∈ B))
        - (1 - κ) * ∑ s, P.prior s * ind (!decide (s ∈ B)) * max 0 (V s a1 a1 - V s a0 a0)
      ≤ P.P4b Wg κ κ' V a0 - P.P4b Wg κ κ' V a1 := by
  unfold Problem.P4b Problem.mass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [h0 s, h1 s]
  have hp := P.prior_nonneg s
  by_cases hs : s ∈ B
  · simp only [hs, decide_true, Bool.not_true, ind_true, ind_false, Bool.not_false, mul_one,
      mul_zero, zero_mul, add_zero, zero_add, one_mul]
    have := hV s; have := hW s
    nlinarith [mul_nonneg hp (mul_nonneg (by linarith : (0:ℚ) ≤ 1 - κ) (hV s)),
      mul_nonneg hp (mul_nonneg hk0 (sub_nonneg.2 (hW s)))]
  · simp only [hs, decide_false, Bool.not_false, ind_true, ind_false, Bool.not_true, mul_one,
      mul_zero, zero_mul, add_zero, zero_add, one_mul]
    have hmax : V s a1 a1 - V s a0 a0 ≤ max 0 (V s a1 a1 - V s a0 a0) := le_max_right _ _
    nlinarith [mul_nonneg hp (mul_nonneg (by linarith : (0:ℚ) ≤ 1 - κ)
      (sub_nonneg.2 hmax))]

/-- **C5 (b), the error bound**: two void grades in `[0, 1]` move `P4b a₁` by at most
`κ' π(B)`, against `π(B)` for `P3` at `λ = 1`.
Source: [[corr-legit-neg-inventory]] item 038 (C5 (b), error bound); `c05_gap.py`
Kind: P
Fidelity: exact
Hyps: (a) the ranges -/
theorem C5_error_bound [DecidableEq S] (P : Problem S A) (Wg Wg' V : MenuVec S A) (κ κ' : ℚ)
    (a1 : A) (B : Finset S) (h1 : ∀ s, P.leg s a1 = !decide (s ∈ B))
    (hW : ∀ s, 0 ≤ Wg s a1 a1 ∧ Wg s a1 a1 ≤ 1) (hW' : ∀ s, 0 ≤ Wg' s a1 a1 ∧ Wg' s a1 a1 ≤ 1)
    (hk0 : 0 ≤ κ') :
    P.P4b Wg' κ κ' V a1 - P.P4b Wg κ κ' V a1 ≤ κ' * P.mass (fun s => decide (s ∈ B))
    ∧ P.P3 Wg' 1 V a1 - P.P3 Wg 1 V a1 ≤ P.mass (fun s => decide (s ∈ B)) := by
  constructor
  · unfold Problem.P4b Problem.mass
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [h1 s]
    have hp := P.prior_nonneg s
    by_cases hs : s ∈ B
    · simp only [hs, decide_true, Bool.not_true, Bool.not_false, ind_true, ind_false, mul_one,
        mul_zero, zero_mul, add_zero, zero_add]
      nlinarith [mul_nonneg hp (mul_nonneg hk0 (by linarith [(hW s).1, (hW' s).2] :
        (0:ℚ) ≤ 1 - (Wg' s a1 a1 - Wg s a1 a1)))]
    · simp [hs]
  · unfold Problem.P3 Problem.mass
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [h1 s]
    have hp := P.prior_nonneg s
    by_cases hs : s ∈ B
    · simp only [hs, decide_true, Bool.not_true, Bool.not_false, ind_true, ind_false, mul_one,
        mul_zero, zero_mul, add_zero, zero_add, one_mul]
      nlinarith [mul_nonneg hp (by linarith [(hW s).1, (hW' s).2] :
        (0:ℚ) ≤ 1 - (Wg' s a1 a1 - Wg s a1 a1))]
    · simp [hs]

/-- **C5 (b)'s toy point** (`v = p = 0, x = 1`): cdot ties while `P4b(1/2, 1/4)`'s margin is
exactly `π(b)(κ − κ') = 1/8`.
Source: [[corr-legit-neg-inventory]] item 038 (C5 (b), toy); `c05_gap.py`
Kind: N+
Fidelity: exact -/
theorem C5_toy_point :
    (toyC 0 0 1).P1 (S1 (toyC 0 0 1).u) 0 = (toyC 0 0 1).P1 (S1 (toyC 0 0 1).u) 1
    ∧ (toyC 0 0 1).P4b (toyC_W 1) (1/2) (1/4) (S1 (toyC 0 0 1).u) 0
        - (toyC 0 0 1).P4b (toyC_W 1) (1/2) (1/4) (S1 (toyC 0 0 1).u) 1 = 1/8 := by
  constructor
  · rw [toyC_P1, toyC_P1]; norm_num
  · rw [toyC_P4b, toyC_P4b]; norm_num

/-- C5 (c)'s single-state problem: `bad_legit` (`0`, legitimate, worth `3/10`) against
`mild_void` (`1`, void, worth `6/10`): the humans' standard violates the gap.
Source: [[corr-legit-neg-inventory]] item 038 (C5 (c)); `c05_gap.py` C5(c)
Kind: D
Fidelity: exact -/
def c5c : Problem (Fin 1) (Fin 2) where
  prior := fun _ => 1
  prior_nonneg := fun _ => by norm_num
  prior_sum := by simp
  leg := fun _ a => decide (a = 0)
  u := fun _ a => ![3/10, 6/10] a

/-- **C5 (c), the cost when the gap is false**: `P4b(1/2, 1/4)` and cdot keep `bad_legit` while
accurate `P3` (`λ = 1`) takes `mild_void`; `H` prefers `mild_void` by `3/10`.
Source: [[corr-legit-neg-inventory]] item 038 (C5 (c)); `c05_gap.py`
Kind: N+
Fidelity: exact -/
theorem C5_gap_false :
    argmax (c5c.P4b (S1 c5c.u) (1/2) (1/4) (S1 c5c.u)) = {0}
    ∧ argmax (c5c.P1 (S1 c5c.u)) = {0}
    ∧ argmax (c5c.P3 (S1 c5c.u) 1 (S1 c5c.u)) = {1}
    ∧ c5c.H 1 - c5c.H 0 = 3/10 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_zero_iff]; simp [c5c, Problem.P4b] <;> norm_num
  · rw [argmax_fin2_eq_zero_iff]; simp [c5c, Problem.P1] <;> norm_num
  · rw [argmax_fin2_eq_one_iff]; simp [c5c, Problem.P3] <;> norm_num
  · simp [c5c, Problem.H, Problem.W, EU] <;> norm_num

/-- **C5 (d), the coupling**: `κ' < κ ↔ κ'/(1 − κ) < κ/(1 − κ)` for `κ < 1`.
Source: [[corr-legit-neg-inventory]] item 038 (C5 (d))
Kind: L
Fidelity: exact -/
theorem C5_coupling (κ κ' : ℚ) (hκ : κ < 1) : κ' < κ ↔ κ' / (1 - κ) < κ / (1 - κ) :=
  (div_lt_div_iff_of_pos_right (by linarith)).symm

/-! ### C8: structural positivity failure -/

/-- **C8 (structural)**: if `a` voids exactly on `B`, no legitimate terminal of `a` lies in `B`
(`π(L_a ∧ B) = 0`) while all of `a`'s void mass does (`π(¬L_a) = π(B)`): every `K` that enters
`P5 a` is written outside `B`.
Source: [[corr-legit-neg-inventory]] item 041 (C8, PROVED clause)
Kind: L
Fidelity: exact (named for what it is: one line) -/
theorem C8_structural [DecidableEq S] (P : Problem S A) (a : A) (B : Finset S)
    (h : ∀ s, P.leg s a = !decide (s ∈ B)) :
    P.mass (fun s => P.leg s a && decide (s ∈ B)) = 0
    ∧ P.mass (fun s => !P.leg s a) = P.mass (fun s => decide (s ∈ B)) := by
  constructor
  · unfold Problem.mass
    refine Finset.sum_eq_zero fun s _ => ?_
    simp only [h s]; by_cases hs : s ∈ B <;> simp [hs]
  · unfold Problem.mass
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [h s]

/-- **C8's witness** (`toyB (1/10) 0 1 1 (1/2)`; the assessors at `(g, a₁)` image `a₁ ▷ ¬L` at
`4/5`, the truth on `(b, a₁)` is `0`): `P5` and `P3` fed by the same number void
(`9/10 > 11/20`); `P1`, `P4a`, `P4b(1/2, 1/4)` keep; `H` keeps by `1/20 = π(b) v`; the escape
`K ≡ 0` (assessors who know `¬L` under `a₁` means `b`) keeps. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 041 (C8, fixture); `c08_p5_voiding.py`
Kind: N+
Fidelity: exact -/
theorem C8_witness :
    let P := toyB (1/10) 0 1 1 (1/2) (by norm_num) (by norm_num)
    argmaxOpt (P.P5 (toyC_K (4/5)) (S1 P.u)) = {1}
    ∧ argmax (P.P3 (toyC_W (4/5)) 1 (S1 P.u)) = {1}
    ∧ argmax (P.P1 (S1 P.u)) = {0}
    ∧ argmaxLex (P.P4a (toyC_W (4/5)) (S1 P.u)) = {0}
    ∧ argmax (P.P4b (toyC_W (4/5)) (1/2) (1/4) (S1 P.u)) = {0}
    ∧ P.H 0 - P.H 1 = 1/20
    ∧ argmaxOpt (P.P5 (toyC_K 0) (S1 P.u)) = {0} := by
  intro P
  have hPL : ∀ a, P.PL a = ![1, 1/2] a :=
    Fin.forall_fin_two.2 ⟨by simp only [P]; rw [toyB_PL_zero]; simp,
      by simp only [P]; rw [toyB_PL_one]; norm_num⟩
  have hP1 : ∀ a, P.P1 (S1 P.u) a = ![11/20, 1/2] a :=
    Fin.forall_fin_two.2 ⟨by simp only [P]; rw [toyB_P1_S1_zero]; norm_num,
      by simp only [P]; rw [toyB_P1_S1_one]; norm_num⟩
  have hP5 : ∀ k a, P.P5 (toyC_K k) (S1 P.u) a = some (![11/20, 1/2 + k / 2] a) := by
    intro k
    have hK : P.Kbar (toyC_K k) 1 = k := by
      unfold Problem.Kbar; rw [hPL]; simp [P, toyC_K, Fin.sum_univ_two] <;> ring
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · simp [Problem.P5, hPL, hP1]
    · rw [P5_of_ne _ _ _ _ (by rw [hPL]; norm_num), hK, hP1, hPL]
      simp <;> ring
  have hP3 : ∀ a, P.P3 (toyC_W (4/5)) 1 (S1 P.u) a = ![11/20, 9/10] a := by
    intro a; fin_cases a <;> simp [P, toyC_W, Problem.P3, Fin.sum_univ_two] <;> norm_num
  have hP4b : ∀ a, P.P4b (toyC_W (4/5)) (1/2) (1/4) (S1 P.u) a = ![31/40, 3/5] a := by
    intro a; fin_cases a <;> simp [P, toyC_W, Problem.P4b, Fin.sum_univ_two] <;> norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [argmaxOpt_eq_argmax_of_forall_some (hP5 (4/5)), argmax_fin2_eq_one_iff]; norm_num
  · rw [argmax_fin2_eq_one_iff, hP3, hP3]; norm_num
  · rw [argmax_fin2_eq_zero_iff, hP1, hP1]; norm_num
  · refine finset_fin2_ext ?_ ?_ <;>
      simp only [mem_argmaxLex, mem_singleton, Fin.forall_fin_two, Problem.P4a,
        Prod.Lex.toLex_le_toLex, hPL, hP3] <;> norm_num
  · rw [argmax_fin2_eq_zero_iff, hP4b, hP4b]; norm_num
  · simp only [P, toyB_H_zero, toyB_H_one]; norm_num
  · rw [argmaxOpt_eq_argmax_of_forall_some (hP5 0), argmax_fin2_eq_zero_iff]; norm_num

end Cleanroom.Corrigibility.LegitNegPricing
