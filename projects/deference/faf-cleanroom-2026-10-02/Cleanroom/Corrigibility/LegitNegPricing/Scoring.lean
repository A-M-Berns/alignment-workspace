import Cleanroom.Corrigibility.LegitNegPricing.Basic

/-!
# What the humans' number means: B10 double counting, the ŵ axis, B12 menu-relative S3,
# B11 selection collapse, B13 re-anchoring

Package `legit-neg-pricing`, targets 7–10 (load-bearing 2 is B11). Sources: `clusters/B/NEGATIVES.md`
B10–B13, `clusters/B/VERIFY.md` (B10 narrowed by V10, B11 generalised by V11, B12/B13 survive),
`clusters/B/fixtures/fx_scoring.py`, `verify_B.py` (V10, V11), pinned by
[[corr-legit-neg-inventory]] items 022–025 and [[corr-legit-neg-2-inventory]] item 2-015.

Register: B11's identification with "Abram's LI challenge" is ATTRIBUTION-UNVETTED (`RUN.md`
§2.4 item 2 is CLAUDE-register, per the verifier). "Positive for P2" under S2 means "equals
unconstrained EU" (`Problem.W`'s docstring).
-/

namespace Cleanroom.Corrigibility.LegitNegPricing

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

variable {S A : Type} [Fintype S] [Fintype A]

/-! ### B10: S2-accurate evaluators -/

/-- **B10 for cdot**: under `S2` (every legitimate terminal scores `c` as the bet `H c`),
`P1 (S2) a = P(L | a) · H a` — the voided mass is priced by the humans and discounted again by
the floor.
Source: [[corr-legit-neg-inventory]] item 022 (B10)
Kind: L
Fidelity: exact -/
theorem P1_S2_eq (P : Problem S A) (a : A) : P.P1 P.S2 a = P.PL a * P.H a := by
  unfold Problem.P1 Problem.S2 Problem.PL Problem.mass
  rw [Finset.sum_mul]

/-- **B10 for conditioning**: `P2 (S2) a = some (H a)` whenever defined — S2-accurate
conditioning *is* unconstrained EU. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 022 (B10); VERIFY B "B10 — narrowed" (register)
Kind: L
Fidelity: exact
Hyps: (a) `P(L | a) ≠ 0` -/
theorem P2_S2_eq (P : Problem S A) (a : A) (h : P.PL a ≠ 0) : P.P2 P.S2 a = some (P.H a) := by
  rw [P2_of_ne _ _ _ h, P1_S2_eq, mul_div_cancel_left₀ _ h]

/-- **B10's witness** (`v = 1/2, w = 9/10, u(g,a₀) = 1/2`): `H = (1/2, 19/20)`; conditioning
takes `a₁`, cdot takes `a₀` (`1/2 > 19/40`). Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 022 (B10); `fx_scoring.py` B10
Kind: N+
Fidelity: exact -/
theorem B10_witness :
    (toyB (1/2) (9/10) (1/2) 1 (1/2) (by norm_num) (by norm_num)).H 0 = 1/2
    ∧ (toyB (1/2) (9/10) (1/2) 1 (1/2) (by norm_num) (by norm_num)).H 1 = 19/20
    ∧ argmaxOpt ((toyB (1/2) (9/10) (1/2) 1 (1/2) (by norm_num) (by norm_num)).P2
        (toyB (1/2) (9/10) (1/2) 1 (1/2) (by norm_num) (by norm_num)).S2) = {1}
    ∧ argmax ((toyB (1/2) (9/10) (1/2) 1 (1/2) (by norm_num) (by norm_num)).P1
        (toyB (1/2) (9/10) (1/2) 1 (1/2) (by norm_num) (by norm_num)).S2) = {0} := by
  have hH0 := toyB_H_zero (1/2) (9/10) (1/2) 1 (1/2) (by norm_num) (by norm_num)
  have hH1 := toyB_H_one (1/2) (9/10) (1/2) 1 (1/2) (by norm_num) (by norm_num)
  refine ⟨by rw [hH0]; norm_num, by rw [hH1]; norm_num, ?_, ?_⟩
  · rw [argmaxOpt_P2_eq_argmax_div _ _
        (Fin.forall_fin_two.2 ⟨by rw [toyB_PL_zero]; norm_num, by rw [toyB_PL_one]; norm_num⟩),
      argmax_fin2_eq_one_iff]
    simp only [P1_S2_eq, toyB_PL_zero, toyB_PL_one, hH0, hH1]; norm_num
  · rw [argmax_fin2_eq_zero_iff]
    simp only [P1_S2_eq, toyB_PL_zero, toyB_PL_one, hH0, hH1]; norm_num

/-- **V10, double counting at the floor** (`v = 1/10, w = 0, u(g,a₀) = 1/2`): `P1 (S2)` keeps
while `H`, `P2 (S2)` and `P1 (S1)` all void. Exclusion convention.
Source: [[corr-legit-neg-2-inventory]] item 2-014 (V10); VERIFY B "B10 — narrowed"
Kind: N+
Fidelity: exact -/
theorem V10_witness :
    argmax ((toyB (1/10) 0 (1/2) 1 (1/2) (by norm_num) (by norm_num)).P1
        (toyB (1/10) 0 (1/2) 1 (1/2) (by norm_num) (by norm_num)).S2) = {0}
    ∧ argmax (toyB (1/10) 0 (1/2) 1 (1/2) (by norm_num) (by norm_num)).H = {1}
    ∧ argmaxOpt ((toyB (1/10) 0 (1/2) 1 (1/2) (by norm_num) (by norm_num)).P2
        (toyB (1/10) 0 (1/2) 1 (1/2) (by norm_num) (by norm_num)).S2) = {1}
    ∧ argmax ((toyB (1/10) 0 (1/2) 1 (1/2) (by norm_num) (by norm_num)).P1
        (S1 (toyB (1/10) 0 (1/2) 1 (1/2) (by norm_num) (by norm_num)).u)) = {1} := by
  have hH0 := toyB_H_zero (1/10) 0 (1/2) 1 (1/2) (by norm_num) (by norm_num)
  have hH1 := toyB_H_one (1/10) 0 (1/2) 1 (1/2) (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_zero_iff]
    simp only [P1_S2_eq, toyB_PL_zero, toyB_PL_one, hH0, hH1]; norm_num
  · rw [argmax_fin2_eq_one_iff, hH0, hH1]; norm_num
  · rw [argmaxOpt_P2_eq_argmax_div _ _
        (Fin.forall_fin_two.2 ⟨by rw [toyB_PL_zero]; norm_num, by rw [toyB_PL_one]; norm_num⟩),
      argmax_fin2_eq_one_iff]
    simp only [P1_S2_eq, toyB_PL_zero, toyB_PL_one, hH0, hH1]; norm_num
  · rw [argmax_fin2_eq_one_iff, toyB_P1_S1_zero, toyB_P1_S1_one]; norm_num

/-- The importance-weighted report `V s a c = H c / P(L | c)` (B10's escape for cdot).
Source: [[corr-legit-neg-inventory]] item 022 (B10, escape)
Kind: D
Fidelity: exact -/
def impWeighted (P : Problem S A) : MenuVec S A := fun _ _ c => P.H c / P.PL c

/-- **B10's escape**: the importance-weighted report makes `P1 = H` exactly where defined.
Source: [[corr-legit-neg-inventory]] item 022 (B10, escape)
Kind: L
Fidelity: exact
Hyps: (a) `P(L | a) ≠ 0` -/
theorem P1_impWeighted (P : Problem S A) (a : A) (h : P.PL a ≠ 0) :
    P.P1 (impWeighted P) a = P.H a := by
  show ∑ s, P.prior s * ind (P.leg s a) * (P.H a / P.PL a) = P.H a
  rw [← Finset.sum_mul]
  change P.PL a * (P.H a / P.PL a) = P.H a
  rw [mul_div_cancel₀ _ h]

/-- **B10's escape leaves `[0, 1]`**: on the witness the report for `a₁` is `19/10`, and on
`toyB 0 1 1 1 π_b` it is `1/(1 − π_b)`, unbounded as `π_b → 1` (`∀ M ∃ π_b`).
Source: [[corr-legit-neg-inventory]] item 022 (B10, escape N−)
Kind: N+
Fidelity: exact -/
theorem impWeighted_unbounded :
    impWeighted (toyB (1/2) (9/10) (1/2) 1 (1/2) (by norm_num) (by norm_num)) 0 0 1 = 19/10
    ∧ ∀ M : ℚ, ∃ πb : ℚ, ∃ h0 : 0 ≤ πb, ∃ h1 : πb ≤ 1,
        M < impWeighted (toyB 0 1 1 1 πb h0 h1) 0 0 1 := by
  constructor
  · unfold impWeighted; rw [toyB_H_one, toyB_PL_one]; norm_num
  · intro M
    refine ⟨1 - 1 / (max M 0 + 2), ?_, ?_, ?_⟩
    · have : (1 : ℚ) / (max M 0 + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [le_max_right M 0]
      linarith
    · have : 0 < (1 : ℚ) / (max M 0 + 2) := by positivity
      linarith
    · unfold impWeighted; rw [toyB_H_one, toyB_PL_one]
      have hpos : (0 : ℚ) < max M 0 + 2 := by positivity
      rw [show (1 : ℚ) - (1 - 1 / (max M 0 + 2)) = 1 / (max M 0 + 2) by ring]
      rw [show (1 / (max M 0 + 2) * 1 + (1 - 1 / (max M 0 + 2)) * 1 : ℚ) = 1 by ring,
        one_div_one_div]
      linarith [le_max_left M 0]

/-! ### The ŵ interpolation (item 2-015) -/

/-- The bet-scoring evaluator with void-value estimate `ŵ`: at every terminal the number for
option `c` is `P(L | c) 𝔼[u_c | L_c] + (1 − P(L | c)) ŵ c` (V11's `w_hat` loop). Junk `Hcond` at
`P(L | c) = 0` is multiplied by `0`.
Source: [[corr-legit-neg-2-inventory]] item 2-015; `verify_B.py:97-104`
Kind: D
Fidelity: exact -/
def betScore (P : Problem S A) (ŵ : A → ℚ) : MenuVec S A :=
  fun _ _ c => P.PL c * P.Hcond (fun t => P.leg t c) c + (1 - P.PL c) * ŵ c

/-- The tower identity: `P(L | a) · 𝔼[u_a | L_a] = P1 (S1 u) a` (the numerator of `Hcond`), for
every action — at `P(L | a) = 0` both sides are `0`.
Source: [[corr-legit-neg-inventory]] item 023 (B11, the tower step)
Kind: L
Fidelity: exact -/
theorem PL_mul_Hcond_self (P : Problem S A) (a : A) :
    P.PL a * P.Hcond (fun t => P.leg t a) a = P.P1 (S1 P.u) a := by
  unfold Problem.Hcond
  by_cases h : P.PL a = 0
  · rw [h, zero_mul, P.P1_eq_zero_of_PL_eq_zero _ _ h]
  · change P.PL a * ((∑ s, P.prior s * ind (P.leg s a) * P.u s a) / P.PL a) = _
    rw [mul_div_cancel₀ _ h]
    rfl

/-- **The ŵ lemma**: `P1 (betScore ŵ) a = P(L | a) · (P(L | a) 𝔼[u_a | L_a] + (1 − P(L | a)) ŵ a)`,
affine in `ŵ a`.
Source: [[corr-legit-neg-2-inventory]] item 2-015
Kind: L
Fidelity: exact -/
theorem P1_betScore (P : Problem S A) (ŵ : A → ℚ) (a : A) :
    P.P1 (betScore P ŵ) a
      = P.PL a * (P.PL a * P.Hcond (fun t => P.leg t a) a + (1 - P.PL a) * ŵ a) := by
  unfold Problem.P1
  simp only [betScore]
  rw [← Finset.sum_mul]
  rfl

/-- **ŵ = 𝔼[u_a | L_a] gives S2sel's value**, i.e. `P2 (betScore E_L) a = P2 (S1 u) a`: the
selection-conditioned bet-scorer collapses to outcome scoring. Exclusion convention.
Source: [[corr-legit-neg-2-inventory]] item 2-015 (`w_hat = E[u|L]` reproduces S2sel = S1-P2)
Kind: C
Fidelity: exact -/
theorem P2_betScore_EL (P : Problem S A) (a : A) :
    P.P2 (betScore P fun c => P.Hcond (fun t => P.leg t c) c) a = P.P2 (S1 P.u) a := by
  unfold Problem.P2
  rw [P1_betScore]
  by_cases h : P.PL a = 0
  · simp [h]
  · rw [if_neg h, if_neg h]
    congr 1
    rw [show P.PL a * P.Hcond (fun t => P.leg t a) a + (1 - P.PL a) * P.Hcond (fun t => P.leg t a) a
        = P.Hcond (fun t => P.leg t a) a by ring, mul_div_cancel_left₀ _ h,
      ← PL_mul_Hcond_self, mul_div_cancel_left₀ _ h]

/-- The `L`/`¬L` decomposition of `H`: `H a = P(L | a) 𝔼[u_a | L_a] + P(¬L | a) 𝔼[u_a | ¬L_a]`
when both masses are positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem H_eq_mix (P : Problem S A) (a : A) (hL : P.PL a ≠ 0) (hN : 1 - P.PL a ≠ 0) :
    P.H a = P.PL a * P.Hcond (fun t => P.leg t a) a
      + (1 - P.PL a) * P.Hcond (fun t => !P.leg t a) a := by
  have hsplit := P.W_split P.u (fun t => P.leg t a) a
  have hmass : P.mass (fun t => !P.leg t a) = 1 - P.PL a := P.mass_not _
  unfold Problem.Hcond
  rw [← hmass, mul_div_cancel₀ _ (hmass ▸ hN)]
  change P.H a = P.PL a * ((∑ s, P.prior s * ind (P.leg s a) * P.u s a) / P.PL a) + _
  rw [mul_div_cancel₀ _ hL]
  exact hsplit

/-- **ŵ = 𝔼[u_a | ¬L_a] gives S2's value**: `P2 (betScore E_N) a = some (H a)` for `0 < P(L | a) < 1`.
The whole S1–S2 axis is the one parameter "what the evaluators believe the void world is worth".
Exclusion convention.
Source: [[corr-legit-neg-2-inventory]] item 2-015 (`w_hat = E[u|¬L]` gives S2 = H)
Kind: C
Fidelity: exact
Hyps: (a) `0 < P(L | a) < 1` (so `E_N` is not junk) -/
theorem P2_betScore_EN (P : Problem S A) (a : A) (hL : P.PL a ≠ 0) (hN : 1 - P.PL a ≠ 0) :
    P.P2 (betScore P fun c => P.Hcond (fun t => !P.leg t c) c) a = some (P.H a) := by
  rw [P2_of_ne _ _ _ hL, P1_betScore, mul_div_cancel_left₀ _ hL, H_eq_mix P a hL hN]

/-! ### B12: menu-relative S3 -/

section B12

variable (v w ug0 πb : ℚ) (h0 : 0 ≤ πb) (h1 : πb ≤ 1)

/-- **B12, the `(b, a₀)` diagonal under S3**: `S3 D (b, a₀)(a₀) = 1 − max 0 (w − v)/D`.
Source: [[corr-legit-neg-inventory]] item 024 (B12); `fx_scoring.py` B12 (`rel(b,a0)`)
Kind: L
Fidelity: exact -/
theorem toyB_S3_b_diag (D : ℚ) :
    (toyB v w ug0 1 πb h0 h1).S3 D 1 0 0 = 1 - max 0 (w - v) / D := by
  unfold Problem.S3
  rw [toyB_umax_one]
  simp only [toyB_u]
  congr 2
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
  rcases le_total v w with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
  · rw [max_eq_left h, max_eq_left (by linarith)]; ring

/-- **B12 for cdot with sighted evaluators** (`w ≤ v`, `ug0 ≤ 1`): under `S3 D`,
`P1 a₀ − P1 a₁ = π_b − π_g (1 − ug0)/D` — the protection of `b` is `π_b`, independent of `v` —
so cdot keeps iff `π_b > π_g δ/D` with `δ = 1 − ug0`.
Source: [[corr-legit-neg-inventory]] item 024 (B12); `fx_scoring.py` B12 ("P1 S3 rule")
Kind: P
Fidelity: exact
Hyps: (a) `w ≤ v` (the evaluators at `(b, a₀)` can see that voiding would have been worse), `ug0 ≤ 1` -/
theorem B12_sighted (D : ℚ) (hw : w ≤ v) (hu : ug0 ≤ 1) :
    (toyB v w ug0 1 πb h0 h1).P1 ((toyB v w ug0 1 πb h0 h1).S3 D) 0
        - (toyB v w ug0 1 πb h0 h1).P1 ((toyB v w ug0 1 πb h0 h1).S3 D) 1
      = πb - (1 - πb) * (1 - ug0) / D
    ∧ (argmax ((toyB v w ug0 1 πb h0 h1).P1 ((toyB v w ug0 1 πb h0 h1).S3 D)) = {0}
        ↔ (1 - πb) * (1 - ug0) / D < πb) := by
  have hS3 : ∀ s c, (toyB v w ug0 1 πb h0 h1).S3 D s c c
      = ![![1 - (1 - ug0) / D, 1], ![1, 1 - (v - w) / D]] s c := by
    intro s c
    unfold Problem.S3
    fin_cases s <;> fin_cases c <;>
      simp [toyB_umax_zero, toyB_umax_one, max_eq_right hu, max_eq_left hw]
  have hP : ∀ c, (toyB v w ug0 1 πb h0 h1).P1 ((toyB v w ug0 1 πb h0 h1).S3 D) c
      = ![(1 - πb) * (1 - (1 - ug0) / D) + πb * 1, (1 - πb) * 1] c := by
    intro c; fin_cases c <;> simp [Problem.P1, Fin.sum_univ_two, hS3]
  rw [argmax_fin2_eq_zero_iff, hP, hP]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have key : ((1 - πb) * (1 - (1 - ug0) / D) + πb * 1) - (1 - πb) * 1
      = πb - (1 - πb) * (1 - ug0) / D := by ring
  constructor
  · linarith
  · constructor <;> intro h <;> linarith

/-- The **blind menu-relative vector**: the S3 formula applied to the blind-imputed values
(`blindImpute y`: the humans at `(s, a)` write `y` for a voiding unchosen option). This is
B12's "blind evaluators imputing `y`" (`fx_scoring.py:82-95`, `S3(P, base=S1(P, blind_impute=y))`);
it is not `legit-neg-static`'s `blindImpute` (which is S1-blind) but the S3 built from it.
Source: [[corr-legit-neg-inventory]] item 024 (B12, blind evaluators)
Kind: D
Fidelity: exact -/
def blindRelS3 (P : Problem S A) [DecidableEq A] [Nonempty A] (y D : ℚ) : MenuVec S A :=
  fun s a c => 1 - (univ.sup' univ_nonempty (fun c' => P.blindImpute y s a c') - P.blindImpute y s a c) / D

/-- **B12 with blind evaluators** (`v = 1/4, u(g,a₀) = 1/2, w = −1, D = 1`): at `y = 3/4` cdot
ties, at `y = 1` it voids `b` while `H` keeps — the S3 rescue needs evaluators who can see the
voiding option's outcome on the branch it voids.
Source: [[corr-legit-neg-inventory]] item 024 (B12); `fx_scoring.py` B12 ("tie at y = 3/4", "blind imputation kills S3's protection")
Kind: N+
Fidelity: exact -/
theorem B12_blind :
    let P := toyB (1/4) (-1) (1/2) 1 (1/2) (by norm_num) (by norm_num)
    argmax (P.P1 (blindRelS3 P (3/4) 1)) = univ
    ∧ argmax (P.P1 (blindRelS3 P 1 1)) = {1}
    ∧ argmax P.H = {0} := by
  intro P
  have hB : ∀ y : ℚ, 1/4 ≤ y → ∀ c,
      P.P1 (blindRelS3 P y 1) c = ![1/4 + (1/2) * (1 - (y - 1/4)), 1/2] c := by
    intro y hy c
    have hy' : (4 : ℚ)⁻¹ ≤ y := by rw [inv_eq_one_div]; exact hy
    fin_cases c <;>
      simp [P, Problem.P1, blindRelS3, Problem.blindImpute, Fin.sum_univ_two, sup'_fin2,
        max_eq_right hy'] <;> norm_num [max_eq_right hy'] <;> ring
  refine ⟨?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_univ_iff, hB (3/4) (by norm_num), hB (3/4) (by norm_num)]; norm_num
  · rw [argmax_fin2_eq_one_iff, hB 1 (by norm_num), hB 1 (by norm_num)]; norm_num
  · rw [argmax_fin2_eq_zero_iff]; simp only [P, toyB_H_zero, toyB_H_one]; norm_num

end B12

/-- **B12 for conditioning (general)**: an action that is hindsight-best wherever it keeps
legitimacy scores `P2 (S3 D) = some 1`, the maximum — a news-managing action is always
P2-optimal under S3. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 024 (B12, conditioning); `fx_scoring.py` B12 (`newsman`)
Kind: P
Fidelity: exact
Hyps: (a) `P(L | a) ≠ 0` -/
theorem P2_S3_eq_one_of_hindsight_best [Nonempty A] (P : Problem S A) (D : ℚ) (a : A)
    (hmax : ∀ s, P.leg s a = true → P.u s a = P.umax s) (h : P.PL a ≠ 0) :
    P.P2 (P.S3 D) a = some 1 := by
  rw [P2_of_ne _ _ _ h]
  congr 1
  have : P.P1 (P.S3 D) a = P.PL a := by
    unfold Problem.P1 Problem.PL Problem.mass
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : P.leg s a = true
    · simp [Problem.S3, hs, hmax s hs]
    · simp [Bool.not_eq_true] at hs; simp [hs]
  rw [this, div_self h]

/-! ### B11: the selection collapse (load-bearing 2) -/

/-- **B11 (i), cdot**: `P1 (S2sel) a = P1 (S1 u) a` for every problem and action — the tower
property `𝔼[ℓ_a 𝔼[u_a | L_a]] = 𝔼[ℓ_a u_a]`. Docstring consequence: every S1 negative (B1–B4,
B7) returns under S2sel; the escape is a genuine `¬L` estimate (`P2_betScore_EN`).
Source: [[corr-legit-neg-inventory]] item 023 (B11); NEGATIVES B11
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem P1_S2sel_eq_P1_S1 (P : Problem S A) (a : A) : P.P1 P.S2sel a = P.P1 (S1 P.u) a := by
  have : P.P1 P.S2sel a = P.PL a * P.Hcond (fun t => P.leg t a) a := by
    unfold Problem.P1 Problem.S2sel Problem.PL Problem.mass
    rw [Finset.sum_mul]
  rw [this, PL_mul_Hcond_self]

/-- **B11 (i), conditioning**: `P2 (S2sel) a = P2 (S1 u) a` (`none` on both sides at
`P(L | a) = 0`). Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 023 (B11)
Kind: C
Fidelity: exact -/
theorem P2_S2sel_eq_P2_S1 (P : Problem S A) (a : A) : P.P2 P.S2sel a = P.P2 (S1 P.u) a := by
  unfold Problem.P2; rw [P1_S2sel_eq_P1_S1]

/-- **B11's toy** (`v = 1/4, w = 0`): `P2 (S2sel) = (5/8, 1)`, conditioning takes `a₁`, `H` keeps.
Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 023 (B11, toy); `fx_scoring.py` B11
Kind: N+
Fidelity: exact -/
theorem B11_toy :
    (toyB (1/4) 0 1 1 (1/2) (by norm_num) (by norm_num)).P2
        (toyB (1/4) 0 1 1 (1/2) (by norm_num) (by norm_num)).S2sel 0 = some (5/8)
    ∧ (toyB (1/4) 0 1 1 (1/2) (by norm_num) (by norm_num)).P2
        (toyB (1/4) 0 1 1 (1/2) (by norm_num) (by norm_num)).S2sel 1 = some 1
    ∧ argmaxOpt ((toyB (1/4) 0 1 1 (1/2) (by norm_num) (by norm_num)).P2
        (toyB (1/4) 0 1 1 (1/2) (by norm_num) (by norm_num)).S2sel) = {1}
    ∧ argmax (toyB (1/4) 0 1 1 (1/2) (by norm_num) (by norm_num)).H = {0} := by
  have hPL : ∀ a, (toyB (1/4) 0 1 1 (1/2) (by norm_num) (by norm_num)).PL a ≠ 0 :=
    Fin.forall_fin_two.2 ⟨by rw [toyB_PL_zero]; norm_num, by rw [toyB_PL_one]; norm_num⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [P2_S2sel_eq_P2_S1, P2_of_ne _ _ _ (hPL 0), toyB_P1_S1_zero, toyB_PL_zero]; norm_num
  · rw [P2_S2sel_eq_P2_S1, P2_of_ne _ _ _ (hPL 1), toyB_P1_S1_one, toyB_PL_one]; norm_num
  · rw [argmaxOpt_P2_eq_argmax_div _ _ hPL, argmax_fin2_eq_one_iff]
    simp only [P1_S2sel_eq_P1_S1, toyB_P1_S1_zero, toyB_P1_S1_one, toyB_PL_zero, toyB_PL_one]
    norm_num
  · rw [argmax_fin2_eq_zero_iff, toyB_H_zero, toyB_H_one]; norm_num

section Cells

variable [DecidableEq S] (P : Problem S A) (cellOf : S → Finset S) (a : A)

/-- `P(L_a | cell t)`: the legitimacy probability of `a` within the cell of `t` (junk `/0` on a
mass-zero cell, where every use multiplies by the cell's prior).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def condLeg (t : S) : ℚ :=
  (∑ s ∈ cellOf t, P.prior s * ind (P.leg s a)) / ∑ s ∈ cellOf t, P.prior s

/-- **The S2cell identity (no purity)**: for a partition (`s ∈ cellOf s`, and `t ∈ cellOf s`
implies `cellOf t = cellOf s`), `P1 (S2cell) a = ∑ t, π t · u t a · P(L_a | cell t)` — the
cell-conditional legitimacy probability replaces the legitimacy indicator.
Source: [[corr-legit-neg-inventory]] item 023 (B11, V11's generalisation); mandate extension
Kind: P
Fidelity: exact (stronger: no purity, no positivity)
Hyps: (a) the two partition axioms -/
theorem P1_S2cell_eq (hmem : ∀ s, s ∈ cellOf s)
    (hcell : ∀ s t, t ∈ cellOf s → cellOf t = cellOf s) :
    P.P1 (P.S2cell cellOf) a = ∑ t, P.prior t * P.u t a * condLeg P cellOf a t := by
  unfold Problem.P1 Problem.S2cell Problem.Hc Problem.cellprior condLeg
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun s => s ∈ cellOf t)]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_eq_zero (s := univ.filter fun s => s ∉ cellOf t), add_zero]
  · rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hst : t ∈ cellOf s := by rw [hcell t s hs]; exact hmem t
    have hsame : cellOf s = cellOf t := hcell t s hs
    rw [if_pos hst, hsame]; ring
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs
    have : t ∉ cellOf s := fun h => hs (by rw [hcell s t h]; exact hmem s)
    rw [if_neg this]; ring

/-- Under `L_a`-purity and positive cell mass, `P(L_a | cell t) = [leg t a]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condLeg_eq_ind_of_pure (hpos : ∀ s, 0 < ∑ t ∈ cellOf s, P.prior t)
    (hpure : ∀ s t, t ∈ cellOf s → P.leg t a = P.leg s a) (t : S) :
    condLeg P cellOf a t = ind (P.leg t a) := by
  unfold condLeg
  rw [div_eq_iff (hpos t).ne', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [hpure t s hs]; ring

/-- **B11 (ii), the generalised selection collapse** (V11): for any partition of the states into
cells of positive mass that are `L_a`-pure (every cell lies inside `L_a` or inside `¬L_a`),
`P1 (S2cell) a = P1 (S1 u) a`. Instances: the full-state partition and `L_a`'s own partition
(`P1_S2cell_singleton_eq`, `P1_S2cell_legPartition_eq`); `S2cell_witness4` is a cell strictly
between them.
Source: [[corr-legit-neg-inventory]] item 023 (B11); VERIFY B "B11 — survives (generalised)" (V11)
Kind: P
Fidelity: exact
Hyps: (a) partition, positive cell mass, `L_a`-purity -/
theorem P1_S2cell_eq_P1_S1_of_pure (hmem : ∀ s, s ∈ cellOf s)
    (hcell : ∀ s t, t ∈ cellOf s → cellOf t = cellOf s)
    (hpos : ∀ s, 0 < ∑ t ∈ cellOf s, P.prior t)
    (hpure : ∀ s t, t ∈ cellOf s → P.leg t a = P.leg s a) :
    P.P1 (P.S2cell cellOf) a = P.P1 (S1 P.u) a := by
  rw [P1_S2cell_eq P cellOf a hmem hcell]
  unfold Problem.P1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [condLeg_eq_ind_of_pure P cellOf a hpos hpure t]; simp; ring

/-- **B11 (ii) for conditioning**: hence `P2 (S2cell) a = P2 (S1 u) a`. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 023 (B11)
Kind: C
Fidelity: exact -/
theorem P2_S2cell_eq_P2_S1_of_pure (hmem : ∀ s, s ∈ cellOf s)
    (hcell : ∀ s t, t ∈ cellOf s → cellOf t = cellOf s)
    (hpos : ∀ s, 0 < ∑ t ∈ cellOf s, P.prior t)
    (hpure : ∀ s t, t ∈ cellOf s → P.leg t a = P.leg s a) :
    P.P2 (P.S2cell cellOf) a = P.P2 (S1 P.u) a := by
  unfold Problem.P2; rw [P1_S2cell_eq_P1_S1_of_pure P cellOf a hmem hcell hpos hpure]

/-- The full-state partition `cellOf s = {s}` (positive prior everywhere) is an instance.
Source: [[corr-legit-neg-inventory]] item 023 (B11, "the full state included")
Kind: C
Fidelity: exact -/
theorem P1_S2cell_singleton_eq (hprior : ∀ s, 0 < P.prior s) :
    P.P1 (P.S2cell fun s => {s}) a = P.P1 (S1 P.u) a :=
  P1_S2cell_eq_P1_S1_of_pure P (fun s => {s}) a (fun s => mem_singleton_self s)
    (fun s t ht => by rw [mem_singleton.1 ht]) (fun s => by simpa using hprior s)
    (fun s t ht => by rw [mem_singleton.1 ht])

/-- `L_a`'s own partition (`cellOf s = {t | leg t a = leg s a}`) is an instance when both
parts have positive mass; its `S2cell` is `S2sel` at `a`'s own terminals.
Source: [[corr-legit-neg-inventory]] item 023 (B11 (i) as a cell instance)
Kind: C
Fidelity: exact
Hyps: (a) `0 < P(L | a) < 1` -/
theorem P1_S2cell_legPartition_eq (hL : 0 < P.PL a) (hN : 0 < 1 - P.PL a) :
    P.P1 (P.S2cell fun s => univ.filter fun t => P.leg t a = P.leg s a) a = P.P1 (S1 P.u) a := by
  refine P1_S2cell_eq_P1_S1_of_pure P _ a (fun s => by simp) ?_ ?_ ?_
  · intro s t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    ext r; simp [ht]
  · intro s
    rw [Finset.sum_filter]
    by_cases hs : P.leg s a = true
    · have : (∑ t, if P.leg t a = P.leg s a then P.prior t else 0) = P.PL a := by
        unfold Problem.PL Problem.mass
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hs]; by_cases ht : P.leg t a = true <;> simp [ht]
      rw [this]; exact hL
    · simp only [Bool.not_eq_true] at hs
      have : (∑ t, if P.leg t a = P.leg s a then P.prior t else 0) = 1 - P.PL a := by
        unfold Problem.PL
        rw [← P.mass_not]
        unfold Problem.mass
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hs]; by_cases ht : P.leg t a = true <;> simp [ht]
      rw [this]; exact hN
  · intro s t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    exact ht

end Cells

/-- **B11 (ii)'s N+ witness**: a four-state problem (`1/4` each) with two-element cells
`{0, 1}`, `{2, 3}` that are `L_{a₁}`-pure (`a₁` legitimate on `{0, 1}`, void on `{2, 3}`) and
strictly coarser than the full-state partition and finer than `L`'s own (which here coincides
with the cells only for `a₁`; for `a₀`, legitimate everywhere, `L`'s partition is trivial).
`u` is non-constant, and `P1 (S2cell) = P1 (S1)` for both actions.
Source: [[corr-legit-neg-inventory]] item 023 (B11); VERIFY B V11
Kind: N+
Fidelity: exact -/
theorem S2cell_witness4 :
    let P : Problem (Fin 4) (Fin 2) :=
      { prior := fun _ => 1/4
        prior_nonneg := fun _ => by norm_num
        prior_sum := by simp
        leg := fun s a => !(decide (2 ≤ s.val) && decide (a = 1))
        u := fun s a => ![![1/2, 1], ![1/4, 3/4], ![0, 1/3], ![1, 1/5]] s a }
    let cellOf : Fin 4 → Finset (Fin 4) := fun s => if s.val < 2 then {0, 1} else {2, 3}
    (∀ s, s ∈ cellOf s) ∧ (∀ s t, t ∈ cellOf s → cellOf t = cellOf s)
    ∧ (∀ s, 0 < ∑ t ∈ cellOf s, P.prior t)
    ∧ (∀ a s t, t ∈ cellOf s → P.leg t a = P.leg s a)
    ∧ cellOf 0 = {0, 1} ∧ (cellOf 0).card = 2
    ∧ (∀ a, P.P1 (P.S2cell cellOf) a = P.P1 (S1 P.u) a) := by
  intro P cellOf
  have hmem : ∀ s, s ∈ cellOf s := by decide
  have hcell : ∀ s t, t ∈ cellOf s → cellOf t = cellOf s := by decide
  have hpos : ∀ s, 0 < ∑ t ∈ cellOf s, P.prior t := by
    intro s; fin_cases s <;> simp [cellOf, P] <;> norm_num
  have hpure : ∀ a s t, t ∈ cellOf s → P.leg t a = P.leg s a := by decide
  refine ⟨hmem, hcell, hpos, hpure, rfl, by decide, fun a => ?_⟩
  exact P1_S2cell_eq_P1_S1_of_pure P cellOf a hmem hcell hpos (hpure a)

/-! ### B13: re-anchoring -/

/-- The re-anchored vector `V' s a c = α · V s a c + β s`.
Source: [[corr-legit-neg-inventory]] item 025 (B13)
Kind: D
Fidelity: exact -/
def reanchor (V : MenuVec S A) (α : ℚ) (β : S → ℚ) : MenuVec S A := fun s a c => α * V s a c + β s

/-- **B13 under R1**: `P1 V' c = α · P1 V c + 𝔼[ℓ_c β]` — a legitimacy bonus on the states where
`β` is large.
Source: [[corr-legit-neg-inventory]] item 025 (B13)
Kind: L
Fidelity: exact -/
theorem P1_reanchor (P : Problem S A) (V : MenuVec S A) (α : ℚ) (β : S → ℚ) (c : A) :
    P.P1 (reanchor V α β) c = α * P.P1 V c + ∑ s, P.prior s * ind (P.leg s c) * β s := by
  unfold Problem.P1 reanchor
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **B13, a constant `β` shifts the floor**: `P1 V' c = α · P1 V c + β · P(L | c)`.
Source: [[corr-legit-neg-inventory]] item 025 (B13)
Kind: L
Fidelity: exact -/
theorem P1_reanchor_const (P : Problem S A) (V : MenuVec S A) (α β : ℚ) (c : A) :
    P.P1 (reanchor V α fun _ => β) c = α * P.P1 V c + β * P.PL c := by
  rw [P1_reanchor]; unfold Problem.PL Problem.mass; rw [Finset.mul_sum]
  congr 1; exact Finset.sum_congr rfl fun s _ => by ring

/-- **B13 under R2**: the realized legitimacy is common to the menu, so the `β` term is a
constant independent of the scored option.
Source: [[corr-legit-neg-inventory]] item 025 (B13)
Kind: L
Fidelity: exact -/
theorem R2scores_reanchor (P : Problem S A) (V : MenuVec S A) (α : ℚ) (β : S → ℚ) (astar c : A) :
    P.R2scores (reanchor V α β) astar c
      = α * P.R2scores V astar c + ∑ s, P.prior s * ind (P.leg s astar) * β s := by
  unfold Problem.R2scores reanchor
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **B13, R2 invisibility**: for `α > 0` the ratifiable set is unchanged by re-anchoring.
Source: [[corr-legit-neg-inventory]] item 025 (B13); `fx_scoring.py` B13 ("R2 not invariant" check)
Kind: P
Fidelity: exact
Hyps: (a) `0 < α` -/
theorem ratifiable_reanchor (P : Problem S A) (V : MenuVec S A) {α : ℚ} (hα : 0 < α) (β : S → ℚ) :
    P.ratifiable (reanchor V α β) = P.ratifiable V := by
  ext a
  simp only [mem_ratifiable, R2scores_reanchor]
  constructor
  · intro h b
    have := h b
    exact le_of_mul_le_mul_left (by linarith) hα
  · intro h b
    have := mul_le_mul_of_nonneg_left (h b) hα.le
    linarith

/-- **S3 is S1 re-anchored** with `α = 1/D`, `β s = 1 − umax s / D`.
Source: [[corr-legit-neg-inventory]] item 025 (B13)
Kind: L
Fidelity: exact -/
theorem S3_eq_reanchor [Nonempty A] (P : Problem S A) (D : ℚ) :
    P.S3 D = reanchor (S1 P.u) (1 / D) fun s => 1 - P.umax s / D := by
  funext s a c; unfold Problem.S3 reanchor; simp only [S1_apply]; ring

/-- **B13's toy** (`v = 1/20, u(g,a₀) = 9/10, w = 0, D = 1`): R1-cdot picks `a₁` under S1 and
`a₀` under S3, while the ratifiable set is `{a₁}` under both.
Source: [[corr-legit-neg-inventory]] item 025 (B13); `fx_scoring.py` B13
Kind: N+
Fidelity: exact -/
theorem B13_toy :
    let P := toyB (1/20) 0 (9/10) 1 (1/2) (by norm_num) (by norm_num)
    argmax (P.P1 (S1 P.u)) = {1}
    ∧ argmax (P.P1 (P.S3 1)) = {0}
    ∧ P.ratifiable (S1 P.u) = {1}
    ∧ P.ratifiable (P.S3 1) = {1} := by
  intro P
  have hS3a : ∀ s c, P.S3 1 s 0 c = ![![9/10, 1], ![1, 19/20]] s c := by
    intro s c; unfold Problem.S3
    fin_cases s <;> fin_cases c <;> simp [P, toyB_umax_zero, toyB_umax_one] <;> norm_num
  have hS3b : ∀ c, P.S3 1 0 1 c = ![9/10, 1] c := by
    intro c; unfold Problem.S3
    fin_cases c <;> simp [P, toyB_umax_zero, toyB_umax_one] <;> norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_one_iff]; simp only [P, toyB_P1_S1_zero, toyB_P1_S1_one]; norm_num
  · rw [argmax_fin2_eq_zero_iff]
    simp only [Problem.P1, Fin.sum_univ_two, hS3a, hS3b]
    simp [P]; norm_num
  · refine finset_fin2_ext ?_ ?_ <;>
      simp only [mem_ratifiable, mem_singleton, Fin.forall_fin_two, P, toyB_R2scores_S1_zero,
        toyB_R2scores_S1_one, toyB_H_zero, toyB_H_one] <;> norm_num
  · refine finset_fin2_ext ?_ ?_ <;>
      simp only [mem_ratifiable, mem_singleton, Fin.forall_fin_two, Problem.R2scores,
        Fin.sum_univ_two, hS3a, hS3b] <;> simp [P] <;> norm_num

end Cleanroom.Corrigibility.LegitNegPricing
