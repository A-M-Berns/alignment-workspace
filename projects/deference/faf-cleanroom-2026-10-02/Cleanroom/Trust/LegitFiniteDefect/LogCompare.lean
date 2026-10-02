import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Cleanroom.Trust.LegitFiniteDefect.Residue
import Cleanroom.Trust.LegitFiniteDefect.Vec

/-!
# The log-score signs

Package `legit-finite-defect`, Target 10 (item 2-047 (a)–(c), (e)). Expected log scores of
rational laws are transcendental, but their *comparisons* are decidable exactly: for natural
weights, `∑ nᵢ log vᵢ ≤ ∑ mⱼ log uⱼ ⟺ ∏ vᵢ^nᵢ ≤ ∏ uⱼ^mⱼ` (`sum_log_le_iff`, `sum_log_lt_iff`) —
the reusable device; rational weights are cleared to a common denominator by the caller. The log
objective `Jlog` is the plug-in expected log score of the conditional-mean prediction, and
`log_propriety` (Gibbs) certifies the plug-in is optimal on every interior group, so `Jlog` means
the optimal score. Instances at the baseline (core): the log residue at `σ = 1/5` is negative, at
`σ = 2/5` **positive** (the log flip lies strictly below Brier's exact zero at `2/5`: a
rule-dependence of the boundary, recorded as a finding), at `σ = 3/5` positive; and the strict
wirehead sign under log.
-/

namespace Cleanroom.Trust.LegitFiniteDefect.LogCompare

open Finset Cleanroom.Trust.LegitFiniteDefect.Residue

noncomputable section

/-! ## The product-comparison device -/

/-- `log ∏ vᵢ^nᵢ = ∑ nᵢ log vᵢ` for positive `v`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem log_prod_pow {ι : Type*} (s : Finset ι) (n : ι → ℕ) (v : ι → ℝ) (hv : ∀ i ∈ s, 0 < v i) :
    Real.log (∏ i ∈ s, v i ^ n i) = ∑ i ∈ s, (n i : ℝ) * Real.log (v i) := by
  rw [Real.log_prod (fun i hi => pow_ne_zero _ (hv i hi).ne')]
  exact Finset.sum_congr rfl (fun i _ => Real.log_pow _ _)

/-- A product of positive powers is positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem prod_pow_pos {ι : Type*} (s : Finset ι) (n : ι → ℕ) (v : ι → ℝ) (hv : ∀ i ∈ s, 0 < v i) :
    0 < ∏ i ∈ s, v i ^ n i :=
  Finset.prod_pos (fun i hi => pow_pos (hv i hi) _)

/-- **Product comparison (≤).** For natural weights and positive values,
`∑ nᵢ log vᵢ ≤ ∑ mⱼ log uⱼ ⟺ ∏ vᵢ^nᵢ ≤ ∏ uⱼ^mⱼ` — an exact rational decision of a
transcendental comparison.
Source: trust-lab-2-047 (a) ("the product trick"); [[stop-gradient-steering]] §E (glue lemma)
Kind: P
Fidelity: exact
Hyps: (a) positivity of the values -/
theorem sum_log_le_iff {ι κ : Type*} (s : Finset ι) (t : Finset κ) (n : ι → ℕ) (m : κ → ℕ)
    (v : ι → ℝ) (u : κ → ℝ) (hv : ∀ i ∈ s, 0 < v i) (hu : ∀ j ∈ t, 0 < u j) :
    ∑ i ∈ s, (n i : ℝ) * Real.log (v i) ≤ ∑ j ∈ t, (m j : ℝ) * Real.log (u j) ↔
      ∏ i ∈ s, v i ^ n i ≤ ∏ j ∈ t, u j ^ m j := by
  rw [← log_prod_pow s n v hv, ← log_prod_pow t m u hu]
  exact Real.log_le_log_iff (prod_pow_pos s n v hv) (prod_pow_pos t m u hu)

/-- **Product comparison (<).**
Source: trust-lab-2-047 (a)
Kind: P
Fidelity: exact
Hyps: (a) positivity of the values -/
theorem sum_log_lt_iff {ι κ : Type*} (s : Finset ι) (t : Finset κ) (n : ι → ℕ) (m : κ → ℕ)
    (v : ι → ℝ) (u : κ → ℝ) (hv : ∀ i ∈ s, 0 < v i) (hu : ∀ j ∈ t, 0 < u j) :
    ∑ i ∈ s, (n i : ℝ) * Real.log (v i) < ∑ j ∈ t, (m j : ℝ) * Real.log (u j) ↔
      ∏ i ∈ s, v i ^ n i < ∏ j ∈ t, u j ^ m j := by
  rw [← log_prod_pow s n v hv, ← log_prod_pow t m u hu]
  exact Real.log_lt_log_iff (prod_pow_pos s n v hv) (prod_pow_pos t m u hu)

/-! ## The log objective and its propriety -/

/-- The negative binary entropy `p log p + (1 − p) log (1 − p)`: the expected log score of
predicting `p` when the truth has probability `p`.
Source: [[stop-gradient-steering]] §B.1 (log score)
Kind: D
Fidelity: exact -/
def negEnt (p : ℝ) : ℝ := p * Real.log p + (1 - p) * Real.log (1 - p)

/-- **Gibbs' inequality**: predicting `p` when the truth has probability `q` scores at most
`negEnt q`.
Source: [[stop-gradient-steering]] §B.1 ("log via Gibbs"); mandate Target 10
Kind: P
Fidelity: exact
Hyps: (a) interior `p, q` -/
theorem gibbs {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    q * Real.log p + (1 - q) * Real.log (1 - p) ≤ negEnt q := by
  unfold negEnt
  have h1 := Real.log_le_sub_one_of_pos (div_pos hp0 hq0)
  have h2 := Real.log_le_sub_one_of_pos (div_pos (sub_pos.2 hp1) (sub_pos.2 hq1))
  rw [Real.log_div hp0.ne' hq0.ne'] at h1
  rw [Real.log_div (sub_pos.2 hp1).ne' (sub_pos.2 hq1).ne'] at h2
  have e1 : q * (p / q - 1) = p - q := by field_simp
  have e2 : (1 - q) * ((1 - p) / (1 - q) - 1) = q - p := by
    have : (1 - q) ≠ 0 := (sub_pos.2 hq1).ne'
    field_simp
    ring
  have m1 := mul_le_mul_of_nonneg_left h1 hq0.le
  have m2 := mul_le_mul_of_nonneg_left h2 (sub_pos.2 hq1).le
  rw [e1] at m1
  rw [e2] at m2
  nlinarith [m1, m2]

/-- **The log objective** `Jlog`: the plug-in expected log score of the conditional-mean
prediction under the (conditioned) law, over `ℝ`.
Source: [[stop-gradient-steering]] §B.1 (`J_all`, `J_L` under log); mandate Target 10
Kind: D
Fidelity: exact (optimality is `log_propriety`, not built in) -/
def Jlog (L : Law) (c : Bool) : ℝ :=
  ((Pmarg L c true : ℝ) * negEnt (condMean L c true) +
    (Pmarg L c false : ℝ) * negEnt (condMean L c false)) / (Z L c : ℝ)

/-- **Log propriety.** On a group of positive restricted mass with interior conditional mean,
the expected log score of any interior prediction `p` is at most the plug-in's.
Source: [[stop-gradient-steering]] §B.1 (propriety via Gibbs); mandate Target 10
Kind: L
Fidelity: exact -/
theorem log_propriety (L : Law) (c y : Bool) (hP : 0 < Pmarg L c y) (hq0 : 0 < condMean L c y)
    (hq1 : condMean L c y < 1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (restrict L c y true : ℝ) * Real.log p + (restrict L c y false : ℝ) * Real.log (1 - p) ≤
      (Pmarg L c y : ℝ) * negEnt (condMean L c y) := by
  have hN : (restrict L c y true : ℝ) = (condMean L c y : ℝ) * (Pmarg L c y : ℝ) := by
    unfold condMean Njoint
    rw [Rat.cast_div, div_mul_cancel₀ _ (by exact_mod_cast hP.ne')]
  have hF : (restrict L c y false : ℝ) = (1 - (condMean L c y : ℝ)) * (Pmarg L c y : ℝ) := by
    have hPm : (Pmarg L c y : ℝ) = (restrict L c y true : ℝ) + (restrict L c y false : ℝ) := by
      unfold Pmarg; push_cast; rfl
    rw [sub_mul, one_mul, ← hN, hPm]
    ring
  rw [hN, hF]
  have hq0' : (0 : ℝ) < condMean L c y := by exact_mod_cast hq0
  have hq1' : (condMean L c y : ℝ) < 1 := by exact_mod_cast hq1
  have hg := gibbs hp0 hp1 hq0' hq1'
  have hP' : (0 : ℝ) ≤ Pmarg L c y := by exact_mod_cast hP.le
  nlinarith [mul_le_mul_of_nonneg_left hg hP']

/-! ## Baseline instances -/

/-- The steered conditional means are `σ + (1 − σ) P_y`.
Source: [[stop-gradient-steering]] §B.4 ("`q_y = σ + (1 − σ) P_y`")
Kind: L
Fidelity: n/a -/
theorem steer_condMean (P : Params) (σ : ℚ) (y : Bool) (h : 0 < Py P y) :
    condMean (steer P σ) true y = σ + (1 - σ) * Pgy P y := by
  obtain ⟨hPm, hN, _⟩ := steer_values P σ
  unfold condMean
  rw [hN y, hPm y]
  simp only [Pgy, condMean, Py] at h ⊢
  field_simp

/-- Evaluation of `Jlog` from the group data.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Jlog_eval (L : Law) (c : Bool) {a b qt qf : ℚ} (hZ : Z L c = 1)
    (hPt : Pmarg L c true = a) (hPf : Pmarg L c false = b) (hqt : condMean L c true = qt)
    (hqf : condMean L c false = qf) :
    Jlog L c = (a : ℝ) * negEnt qt + (b : ℝ) * negEnt qf := by
  simp [Jlog, hZ, hPt, hPf, hqt, hqf]

/-- The baseline log objectives, evaluated: honest, and steer at `σ ∈ {1/5, 2/5, 3/5}`.
Source: mandate Target 10 (core instances)
Kind: L
Fidelity: n/a -/
theorem base_log_values :
    Jlog (honest base) true = (1 / 2 : ℝ) * negEnt (3 / 4) + (1 / 2 : ℝ) * negEnt (1 / 4) ∧
      Jlog (steer base (1 / 5)) true = (1 / 2 : ℝ) * negEnt (4 / 5) + (1 / 2 : ℝ) * negEnt (2 / 5) ∧
      Jlog (steer base (2 / 5)) true =
        (1 / 2 : ℝ) * negEnt (17 / 20) + (1 / 2 : ℝ) * negEnt (11 / 20) ∧
      Jlog (steer base (3 / 5)) true =
        (1 / 2 : ℝ) * negEnt (9 / 10) + (1 / 2 : ℝ) * negEnt (7 / 10) := by
  obtain ⟨h1, h0, hgt, hgf, _, _, _⟩ := base_values
  have hZh : Z (honest base) true = 1 := (honest_values base).2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Jlog_eval _ _ hZh h1 h0 hgt hgf]; push_cast; ring
  all_goals
    obtain ⟨hPm, _, hZ⟩ := steer_values base _
    rw [Jlog_eval _ _ hZ ((hPm true).trans h1) ((hPm false).trans h0)
      (steer_condMean base _ true (by rw [h1]; norm_num))
      (steer_condMean base _ false (by rw [h0]; norm_num)), hgt, hgf]
    push_cast
    norm_num

/-- **The baseline log residue signs**: negative at `σ = 1/5`, **positive at `σ = 2/5`** (where
Brier is exactly zero), positive at `σ = 3/5`. Each is one rational inequality after the
product-comparison lemma.
Source: trust-lab-2-047 (a) ("log `(7/20, 2/5): − → +`"); [[stop-gradient-steering]] §B.4
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem base_log_residue :
    Jlog (steer base (1 / 5)) true < Jlog (honest base) true ∧
      Jlog (honest base) true < Jlog (steer base (2 / 5)) true ∧
      Jlog (honest base) true < Jlog (steer base (3 / 5)) true := by
  obtain ⟨hh, h15, h25, h35⟩ := base_log_values
  have hH : 20 * Jlog (honest base) true =
      ∑ i : Fin 2, ((![15, 5] : Fin 2 → ℕ) i : ℝ) * Real.log ((![3 / 4, 1 / 4] : Fin 2 → ℝ) i) := by
    rw [hh]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Nat.cast_ofNat, negEnt]
    rw [show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num, show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num]
    ring
  have hH40 : 40 * Jlog (honest base) true =
      ∑ i : Fin 2, ((![30, 10] : Fin 2 → ℕ) i : ℝ) * Real.log ((![3 / 4, 1 / 4] : Fin 2 → ℝ) i) := by
    rw [hh]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Nat.cast_ofNat, negEnt]
    rw [show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num, show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num]
    ring
  have hS15 : 20 * Jlog (steer base (1 / 5)) true =
      ∑ i : Fin 4, ((![8, 2, 4, 6] : Fin 4 → ℕ) i : ℝ) *
        Real.log ((![4 / 5, 1 / 5, 2 / 5, 3 / 5] : Fin 4 → ℝ) i) := by
    rw [h15]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      vec4_two, vec4_three, Nat.cast_ofNat, negEnt]
    rw [show (1 : ℝ) - 4 / 5 = 1 / 5 by norm_num, show (1 : ℝ) - 2 / 5 = 3 / 5 by norm_num]
    ring
  have hS25 : 40 * Jlog (steer base (2 / 5)) true =
      ∑ i : Fin 4, ((![17, 3, 11, 9] : Fin 4 → ℕ) i : ℝ) *
        Real.log ((![17 / 20, 3 / 20, 11 / 20, 9 / 20] : Fin 4 → ℝ) i) := by
    rw [h25]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      vec4_two, vec4_three, Nat.cast_ofNat, negEnt]
    rw [show (1 : ℝ) - 17 / 20 = 3 / 20 by norm_num, show (1 : ℝ) - 11 / 20 = 9 / 20 by norm_num]
    ring
  have hS35 : 20 * Jlog (steer base (3 / 5)) true =
      ∑ i : Fin 4, ((![9, 1, 7, 3] : Fin 4 → ℕ) i : ℝ) *
        Real.log ((![9 / 10, 1 / 10, 7 / 10, 3 / 10] : Fin 4 → ℝ) i) := by
    rw [h35]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      vec4_two, vec4_three, Nat.cast_ofNat, negEnt]
    rw [show (1 : ℝ) - 9 / 10 = 1 / 10 by norm_num, show (1 : ℝ) - 7 / 10 = 3 / 10 by norm_num]
    ring
  refine ⟨?_, ?_, ?_⟩
  · have := (sum_log_lt_iff univ univ _ _ _ _ (fun i _ => by fin_cases i <;> norm_num)
      (fun i _ => by fin_cases i <;> norm_num)).2
      (by simp only [Fin.prod_univ_four, Fin.prod_univ_two, vec4_two, vec4_three]; norm_num :
        ∏ i : Fin 4, (![4 / 5, 1 / 5, 2 / 5, 3 / 5] : Fin 4 → ℝ) i ^ (![8, 2, 4, 6] : Fin 4 → ℕ) i <
          ∏ i : Fin 2, (![3 / 4, 1 / 4] : Fin 2 → ℝ) i ^ (![15, 5] : Fin 2 → ℕ) i)
    rw [← hS15, ← hH] at this
    linarith
  · have := (sum_log_lt_iff univ univ _ _ _ _ (fun i _ => by fin_cases i <;> norm_num)
      (fun i _ => by fin_cases i <;> norm_num)).2
      (by simp only [Fin.prod_univ_four, Fin.prod_univ_two, vec4_two, vec4_three]; norm_num :
        ∏ i : Fin 2, (![3 / 4, 1 / 4] : Fin 2 → ℝ) i ^ (![30, 10] : Fin 2 → ℕ) i <
          ∏ i : Fin 4, (![17 / 20, 3 / 20, 11 / 20, 9 / 20] : Fin 4 → ℝ) i ^
            (![17, 3, 11, 9] : Fin 4 → ℕ) i)
    rw [← hS25, ← hH40] at this
    linarith
  · have := (sum_log_lt_iff univ univ _ _ _ _ (fun i _ => by fin_cases i <;> norm_num)
      (fun i _ => by fin_cases i <;> norm_num)).2
      (by simp only [Fin.prod_univ_four, Fin.prod_univ_two, vec4_two, vec4_three]; norm_num :
        ∏ i : Fin 2, (![3 / 4, 1 / 4] : Fin 2 → ℝ) i ^ (![15, 5] : Fin 2 → ℕ) i <
          ∏ i : Fin 4, (![9 / 10, 1 / 10, 7 / 10, 3 / 10] : Fin 4 → ℝ) i ^
            (![9, 1, 7, 3] : Fin 4 → ℕ) i)
    rw [← hS35, ← hH] at this
    linarith

/-- The baseline log objective at `σ = 7/20`: steered means `67/80, 41/80`.
Source: mandate Target 10 (stretch grid point); [[stop-gradient-steering]] §B.4 (sigma grid `k/20`)
Kind: L
Fidelity: n/a -/
theorem base_log_value_720 :
    Jlog (steer base (7 / 20)) true =
      (1 / 2 : ℝ) * negEnt (67 / 80) + (1 / 2 : ℝ) * negEnt (41 / 80) := by
  obtain ⟨h1, h0, hgt, hgf, _, _, _⟩ := base_values
  obtain ⟨hPm, _, hZ⟩ := steer_values base (7 / 20)
  rw [Jlog_eval _ _ hZ ((hPm true).trans h1) ((hPm false).trans h0)
    (steer_condMean base _ true (by rw [h1]; norm_num))
    (steer_condMean base _ false (by rw [h0]; norm_num)), hgt, hgf]
  push_cast
  norm_num

/-- **The log flip is bracketed to `(7/20, 2/5)`**, as the source's sweep says: the log residue is
strictly negative at `σ = 7/20` — decided by
`(67/80)^67 (13/80)^13 (41/80)^41 (39/80)^39 < (3/4)^120 (1/4)^40` — and strictly positive at
`2/5` (`base_log_residue`). With Brier's exact zero at `2/5` (`Residue.base_flip`), the log
boundary lies strictly below the Brier one, inside `(7/20, 2/5)`.
Source: trust-lab-2-047 (a) ("log `(7/20, 2/5): − → +`"); [[stop-gradient-steering]] §B.4
("positive already somewhere in `(7/20, 2/5)`"); mandate Target 10 stretch; repair round 1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem base_log_flip_bracket :
    Jlog (steer base (7 / 20)) true < Jlog (honest base) true ∧
      Jlog (honest base) true < Jlog (steer base (2 / 5)) true := by
  refine ⟨?_, base_log_residue.2.1⟩
  obtain ⟨hh, _, _, _⟩ := base_log_values
  have hH : 160 * Jlog (honest base) true =
      ∑ i : Fin 2, ((![120, 40] : Fin 2 → ℕ) i : ℝ) * Real.log ((![3 / 4, 1 / 4] : Fin 2 → ℝ) i) := by
    rw [hh]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_ofNat, negEnt]
    rw [show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num, show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num]
    ring
  have hS : 160 * Jlog (steer base (7 / 20)) true =
      ∑ i : Fin 4, ((![67, 13, 41, 39] : Fin 4 → ℕ) i : ℝ) *
        Real.log ((![67 / 80, 13 / 80, 41 / 80, 39 / 80] : Fin 4 → ℝ) i) := by
    rw [base_log_value_720]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, vec4_two, vec4_three,
      Nat.cast_ofNat, negEnt]
    rw [show (1 : ℝ) - 67 / 80 = 13 / 80 by norm_num, show (1 : ℝ) - 41 / 80 = 39 / 80 by norm_num]
    ring
  have := (sum_log_lt_iff univ univ _ _ _ _ (fun i _ => by fin_cases i <;> norm_num)
    (fun i _ => by fin_cases i <;> norm_num)).2
    (by simp only [Fin.prod_univ_four, Fin.prod_univ_two, vec4_two, vec4_three]; norm_num :
      ∏ i : Fin 4, (![67 / 80, 13 / 80, 41 / 80, 39 / 80] : Fin 4 → ℝ) i ^
          (![67, 13, 41, 39] : Fin 4 → ℕ) i <
        ∏ i : Fin 2, (![3 / 4, 1 / 4] : Fin 2 → ℝ) i ^ (![120, 40] : Fin 2 → ℕ) i)
  rw [← hS, ← hH] at this
  linarith

/-- **The strict wirehead sign under log** at the baseline: `J_L(wirehead 3/4) = negEnt (1/2) <
J_L(honest)` — decided by `(1/2)^4 < (3/4)^3 (1/4)`.
Source: trust-lab-2-047 (a) ("the strict wirehead sign under log"); [[stop-gradient-steering]]
§B.3 ("same strict sign under log score")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem base_log_wirehead : Jlog (wirehead base (3 / 4)) true < Jlog (honest base) true := by
  obtain ⟨hh, _, _, _⟩ := base_log_values
  obtain ⟨w1, w2, w3, w4⟩ := wirehead_values base (3 / 4)
  have hZ : Z (wirehead base (3 / 4)) true = 1 / 4 := by
    unfold Z Pmarg; rw [w1, w2, w3, w4]; norm_num [g, base]
  have hPt : Pmarg (wirehead base (3 / 4)) true true = 1 / 4 := by
    unfold Pmarg; rw [w1, w2]; norm_num [g, base]
  have hPf : Pmarg (wirehead base (3 / 4)) true false = 0 := by
    unfold Pmarg; rw [w3, w4]; norm_num
  have hqt : condMean (wirehead base (3 / 4)) true true = 1 / 2 := by
    unfold condMean Njoint; rw [w1, hPt]; norm_num [g, base]
  have hW : Jlog (wirehead base (3 / 4)) true = negEnt (1 / 2) := by
    unfold Jlog
    rw [hZ, hPt, hPf, hqt]
    push_cast
    ring
  have hW4 : 4 * Jlog (wirehead base (3 / 4)) true =
      ∑ i : Fin 2, ((![2, 2] : Fin 2 → ℕ) i : ℝ) * Real.log ((![1 / 2, 1 / 2] : Fin 2 → ℝ) i) := by
    rw [hW]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Nat.cast_ofNat, negEnt]
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    ring
  have hH : 4 * Jlog (honest base) true =
      ∑ i : Fin 2, ((![3, 1] : Fin 2 → ℕ) i : ℝ) * Real.log ((![3 / 4, 1 / 4] : Fin 2 → ℝ) i) := by
    rw [hh]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Nat.cast_ofNat, Nat.cast_one, negEnt]
    rw [show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num, show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num]
    ring
  have := (sum_log_lt_iff univ univ _ _ _ _ (fun i _ => by fin_cases i <;> norm_num)
    (fun i _ => by fin_cases i <;> norm_num)).2
    (by simp only [Fin.prod_univ_two]; norm_num :
      ∏ i : Fin 2, (![1 / 2, 1 / 2] : Fin 2 → ℝ) i ^ (![2, 2] : Fin 2 → ℕ) i <
        ∏ i : Fin 2, (![3 / 4, 1 / 4] : Fin 2 → ℝ) i ^ (![3, 1] : Fin 2 → ℕ) i)
  rw [← hW4, ← hH] at this
  linarith

end

end Cleanroom.Trust.LegitFiniteDefect.LogCompare
