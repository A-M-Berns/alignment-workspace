import Cleanroom.Corrigibility.CorrLandscape.Erosion

/-!
# `corr-landscape` — `Drift`: the fresh-draw kernel's certificate (E2(ii))

Mandate E2(ii) asks whether `|β_t − β_stat|` is a potential (a Lyapunov certificate, here for the
deterministic mass dynamics `freshStep`) for the fresh-draw kernel of `Erosion` (wentworth-respondent
item 2, `selection_drift.py`), "a linear contraction to the stationary mass". Audit round 1 (fidelity N6,
adversarial N3) asked for the statement to be settled or stated OPEN. Settled:

* **Refuted as stated** (`beta_not_potential`): `β_{t+1} = (1 + (ε/3)∑v) β_t − ε ∑_v v² m_v` depends on the
  second moment of the mass, not on `β_t` alone, so `|β_t − β_stat|` is not a one-step certificate — at
  `m = (15/22, 0, 7/22)`, `β = β_stat = 27/55` exactly, yet `β' = 5373/11000 ≠ 27/55`: the deviation grows
  from `0` to `27/11000`.
* **The certificate is on the mass vector** (`l1_nonexpansive`): the ℓ¹ deviation
  `‖m − m_stat‖₁ = ∑_v |m_v − m_stat,v|` is non-increasing under `freshStep ε` for every `ε` with
  `0 ≤ ε` and `ε · max v ≤ 1` (the map is `x ↦ x(1 − εv) + (ε/3)⟨v, x⟩` on the deviation, and the triangle
  inequality closes exactly), and `|β − β_stat| ≤ (max v) ‖m − m_stat‖₁` (`beta_le_l1`), so the ℓ¹
  deviation controls `β`. `m_stat ∝ 1/v` is stationary for every `ε` (`freshStep_mstat`).

Direction and order only; the strict contraction rate is not computed (the map is non-expansive in ℓ¹,
strictly contracting on deviations with `∑ x = 0` — not proved here).
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open Finset

set_option linter.unusedSectionVars false

namespace Drift

open Erosion

/-- The ℓ¹ deviation of a mass vector from the stationary mass.
Source: mandate E2(ii) ("a potential … linear contraction to the stationary mass")
Kind: D
Fidelity: exact -/
noncomputable def l1Dev (m : Fin 3 → ℝ) : ℝ := ∑ v, |m v - mstat v|

/-- The visibility-weighted deviation `⟨v, m − m_stat⟩`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def devSum (m : Fin 3 → ℝ) : ℝ := ∑ u, (m u - mstat u) * vis u

/-- **`m_stat ∝ 1/v` is stationary for every retirement rate `ε`** (not only `1/10`): `v · m_stat,v` is
constant, so the retired mass `ε ∑ v m_v` is `3 ε · (that constant)` and the uniform redraw restores it.
Source: [[corr-wf14b-inventory]] 065 / `selection_drift.py` ("mass `m_v ∝ 1/(eps*v)`")
Kind: P (small)
Fidelity: exact
Hyps: (a) only -/
theorem freshStep_mstat (ε : ℝ) : freshStep ε mstat = mstat := by
  funext v
  fin_cases v <;> simp [freshStep, mstat, vis, Fin.sum_univ_three] <;> ring

/-- The deviation evolves affinely: `x'_v = x_v (1 − ε v) + (ε/3) ⟨v, x⟩`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma freshStep_sub (ε : ℝ) (m : Fin 3 → ℝ) :
    freshStep ε m 0 - mstat 0 = (m 0 - mstat 0) * (1 - ε * (3 / 10)) + ε / 3 * devSum m ∧
      freshStep ε m 1 - mstat 1 = (m 1 - mstat 1) * (1 - ε * (3 / 5)) + ε / 3 * devSum m ∧
      freshStep ε m 2 - mstat 2 = (m 2 - mstat 2) * (1 - ε * (9 / 10)) + ε / 3 * devSum m := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [freshStep, devSum, mstat, vis, Fin.sum_univ_three] <;> ring

/-- `|⟨v, x⟩| ≤ ∑ v_u |x_u|`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma abs_devSum_le (m : Fin 3 → ℝ) :
    |devSum m| ≤ |m 0 - mstat 0| * (3 / 10) + |m 1 - mstat 1| * (3 / 5) + |m 2 - mstat 2| * (9 / 10) := by
  simp only [devSum, Fin.sum_univ_three, vis]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  calc |(m 0 - mstat 0) * (3 / 10) + (m 1 - mstat 1) * (3 / 5) + (m 2 - mstat 2) * (9 / 10)|
      ≤ |(m 0 - mstat 0) * (3 / 10) + (m 1 - mstat 1) * (3 / 5)| + |(m 2 - mstat 2) * (9 / 10)| :=
        abs_add_le _ _
    _ ≤ |(m 0 - mstat 0) * (3 / 10)| + |(m 1 - mstat 1) * (3 / 5)| + |(m 2 - mstat 2) * (9 / 10)| := by
        gcongr; exact abs_add_le _ _
    _ = |m 0 - mstat 0| * (3 / 10) + |m 1 - mstat 1| * (3 / 5) + |m 2 - mstat 2| * (9 / 10) := by
        rw [abs_mul, abs_mul, abs_mul]; norm_num

/-- **The ℓ¹ deviation from `m_stat` is non-increasing under the fresh-draw kernel** for every `ε` with
`0 ≤ ε` and `ε · (9/10) ≤ 1`: this is the Lyapunov certificate E2(ii) asked for, on the mass vector.
Source: mandate E2(ii); wentworth-respondent.md item 2 (kernel (A))
Kind: P
Fidelity: variant: the certificate is `‖m − m_stat‖₁`, not `|β − β_stat|` (which fails,
`beta_not_potential`)
Hyps: (a) only -/
theorem l1_nonexpansive (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε * (9 / 10) ≤ 1) (m : Fin 3 → ℝ) :
    l1Dev (freshStep ε m) ≤ l1Dev m := by
  obtain ⟨e0, e1, e2⟩ := freshStep_sub ε m
  have hσ := abs_devSum_le m
  have hσ' := mul_le_mul_of_nonneg_left hσ hε0
  have hε3 : 0 ≤ ε / 3 := by positivity
  have b0 : |freshStep ε m 0 - mstat 0| ≤ (1 - ε * (3 / 10)) * |m 0 - mstat 0| + ε / 3 * |devSum m| := by
    rw [e0]
    calc |(m 0 - mstat 0) * (1 - ε * (3 / 10)) + ε / 3 * devSum m|
        ≤ |(m 0 - mstat 0) * (1 - ε * (3 / 10))| + |ε / 3 * devSum m| := abs_add_le _ _
      _ = (1 - ε * (3 / 10)) * |m 0 - mstat 0| + ε / 3 * |devSum m| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε * (3 / 10)), abs_of_nonneg hε3]
          ring
  have b1 : |freshStep ε m 1 - mstat 1| ≤ (1 - ε * (3 / 5)) * |m 1 - mstat 1| + ε / 3 * |devSum m| := by
    rw [e1]
    calc |(m 1 - mstat 1) * (1 - ε * (3 / 5)) + ε / 3 * devSum m|
        ≤ |(m 1 - mstat 1) * (1 - ε * (3 / 5))| + |ε / 3 * devSum m| := abs_add_le _ _
      _ = (1 - ε * (3 / 5)) * |m 1 - mstat 1| + ε / 3 * |devSum m| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε * (3 / 5)), abs_of_nonneg hε3]
          ring
  have b2 : |freshStep ε m 2 - mstat 2| ≤ (1 - ε * (9 / 10)) * |m 2 - mstat 2| + ε / 3 * |devSum m| := by
    rw [e2]
    calc |(m 2 - mstat 2) * (1 - ε * (9 / 10)) + ε / 3 * devSum m|
        ≤ |(m 2 - mstat 2) * (1 - ε * (9 / 10))| + |ε / 3 * devSum m| := abs_add_le _ _
      _ = (1 - ε * (9 / 10)) * |m 2 - mstat 2| + ε / 3 * |devSum m| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε * (9 / 10)), abs_of_nonneg hε3]
          ring
  unfold l1Dev
  simp only [Fin.sum_univ_three]
  nlinarith [b0, b1, b2, hσ']

/-- **`β` is controlled by the ℓ¹ deviation**: `|β − β_stat| ≤ (9/10) ‖m − m_stat‖₁`.
Source: mandate E2(ii)
Kind: L
Fidelity: exact -/
theorem beta_le_l1 (m : Fin 3 → ℝ) : |popBeta m - popBeta mstat| ≤ (9 / 10) * l1Dev m := by
  have h : popBeta m - popBeta mstat = devSum m := by
    simp [popBeta, devSum, Fin.sum_univ_three]; ring
  rw [h]
  refine (abs_devSum_le m).trans ?_
  unfold l1Dev
  simp only [Fin.sum_univ_three]
  nlinarith [abs_nonneg (m 0 - mstat 0), abs_nonneg (m 1 - mstat 1), abs_nonneg (m 2 - mstat 2)]

/-- The mass vector `(15/22, 0, 7/22)`: `β = β_stat` with a different second moment.
Source: mandate E2(ii) (refutation cell). Kind: D. Fidelity: n/a (witness) -/
noncomputable def mCell : Fin 3 → ℝ := ![15 / 22, 0, 7 / 22]

/-- **`|β_t − β_stat|` is not a potential for the fresh-draw kernel** — refuting E2(ii) as stated: `mCell`
is a probability vector with `β = β_stat = 27/55` exactly, and one fresh-draw step at `ε = 1/10` moves
`β` to `5373/11000 ≠ 27/55`, so the scalar deviation grows (from `0` to `27/11000`). `β_{t+1}` depends on
`∑_v v² m_v`, not on `β_t` alone; the certificate lives on the mass vector (`l1_nonexpansive`).
Source: mandate E2(ii) ("`|β_t − β_stat|` as a potential"); `selection_drift.py`
Kind: N+ (refutation of the mandate's conjectured certificate)
Fidelity: exact
Hyps: (a) only -/
theorem beta_not_potential :
    (∑ v, mCell v) = 1 ∧ (∀ v, 0 ≤ mCell v) ∧ popBeta mCell = popBeta mstat ∧
      popBeta (freshStep (1 / 10) mCell) = 5373 / 11000 ∧
      |popBeta mCell - popBeta mstat| < |popBeta (freshStep (1 / 10) mCell) - popBeta mstat| := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [mCell, Fin.sum_univ_three]; norm_num
  · intro v; fin_cases v <;> simp [mCell] <;> norm_num
  · simp [popBeta, mCell, mstat, vis, Fin.sum_univ_three]; norm_num
  · simp [popBeta, freshStep, mCell, vis, Fin.sum_univ_three]; norm_num
  · simp [popBeta, freshStep, mCell, mstat, vis, Fin.sum_univ_three]; norm_num

end Drift

end Cleanroom.Corrigibility.CorrLandscape
