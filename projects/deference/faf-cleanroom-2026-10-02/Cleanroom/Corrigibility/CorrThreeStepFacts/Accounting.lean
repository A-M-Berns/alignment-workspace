import Cleanroom.Corrigibility.CorrThreeStepFacts.Basic

/-!
# T7: whole-line versus pause accounting (and the `c + h = 1 + κ` lemma)

The two accountings of `fud.md` R2 are the same inequality with different stakes:
pause `(c_p, h_p) = (δ, 1 − δ + κ)`, whole line `(c_w, h_w) = (1 − ρ, ρ + κ)`. The file records
the margins, the compliance thresholds, the two `ε*` cells (`1/3583`, `1/23`), the ratio of
margins, and the one-line lemma `c + h = 1 + κ` under both accountings (used by T25 against
`legitimacy-general-final` Statement 16, remark (i)).

Source: `fud.md` R2 items 4–7 (corr-wf14-011).
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open Cleanroom.Found.CorrThreeStep

/-- Pause accounting: complying when right forgoes the pause, `c_p = δ`.
Source: [[corr-wf14-inventory]] 011 / fud.md R2 item 4. Kind: D. Fidelity: exact -/
def pauseC (δ : ℝ) : ℝ := δ

/-- Pause accounting: complying when wrong gains `h_p = (1 − δ) + κ`.
Source: fud.md R2 item 4. Kind: D. Fidelity: exact -/
def pauseH (δ κ : ℝ) : ℝ := 1 - δ + κ

/-- Whole-line accounting: complying when right ends the line, `c_w = 1 − ρ`.
Source: fud.md R2 item 5. Kind: D. Fidelity: exact -/
def wholeC (ρ : ℝ) : ℝ := 1 - ρ

/-- Whole-line accounting: complying when wrong averts the catastrophe, `h_w = ρ + κ`.
Source: fud.md R2 item 5. Kind: D. Fidelity: exact -/
def wholeH (ρ κ : ℝ) : ℝ := ρ + κ

/-- **T7, the margins.** `h_p/c_p = (1 − δ + κ)/δ` and `h_w/c_w = (ρ + κ)/(1 − ρ)`.
Source: [[corr-wf14-inventory]] 011 / fud.md R2 items 4–5
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem accounting_margins (δ κ ρ : ℝ) :
    pauseH δ κ / pauseC δ = (1 - δ + κ) / δ ∧ wholeH ρ κ / wholeC ρ = (ρ + κ) / (1 - ρ) :=
  ⟨rfl, rfl⟩

/-- **T7, `c + h = 1 + κ` under both accountings** — the one-line lemma that refutes
`legitimacy-general-final` Statement 16 remark (i) (T25): the band half-width `2Mδ/(c + h)` is
accounting-independent.
Source: [[corr-wf14-inventory]] 011 / fud.md R2 (derived here); [[corr-wf14b-inventory]] 055 / legitimacy-general-final.md Statement 16 (refuted remark)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem accounting_sum (δ κ ρ : ℝ) :
    pauseC δ + pauseH δ κ = 1 + κ ∧ wholeC ρ + wholeH ρ κ = 1 + κ := by
  unfold pauseC pauseH wholeC wholeH; constructor <;> ring

/-- **T7, the thresholds.** `c/(c + h)` is `δ/(1 + κ)` under pauses and `(1 − ρ)/(1 + κ)` on the
whole line.
Source: fud.md R2 items 4–5 (`0.005`; `0.45`, `0.25`, …)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem accounting_thresholds (δ κ ρ : ℝ) :
    complianceThreshold (pauseC δ) (pauseH δ κ) = δ / (1 + κ) ∧
      complianceThreshold (wholeC ρ) (wholeH ρ κ) = (1 - ρ) / (1 + κ) := by
  unfold complianceThreshold pauseC pauseH wholeC wholeH
  constructor <;> congr 1 <;> ring

/-- **T7, the `ε*` cells.** At `(α, β) = (1/20, 9/10)`: `ε*_p = 1/3583` for `δ = 1/100`, `κ = 1`
(the source's `0.00028`) and `ε*_w = 1/23` for `ρ = 1/10`, `κ = 1` (the source's `0.0435`).
Source: fud.md R2 item 6
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w_accounting_epsStar :
    epsStar (1/20) (9/10) (pauseC (1/100)) (pauseH (1/100) 1) = 1/3583 ∧
      epsStar (1/20) (9/10) (wholeC (1/10)) (wholeH (1/10) 1) = 1/23 := by
  unfold epsStar pauseC pauseH wholeC wholeH; constructor <;> norm_num

/-- **T7, the ratio of margins.** `(h_p/c_p)/(h_w/c_w) = (1 + κ − δ)(1 − ρ)/(δ(ρ + κ))` where
the divisions are defined.
Source: fud.md R2 item 6 ("about two orders of magnitude")
Kind: L
Fidelity: exact
Hyps: (a) the nonvanishing hypotheses are where the ratios are defined -/
theorem accounting_margin_ratio (δ κ ρ : ℝ) (hδ : δ ≠ 0) (hρ : 1 - ρ ≠ 0) (hκ : ρ + κ ≠ 0) :
    (pauseH δ κ / pauseC δ) / (wholeH ρ κ / wholeC ρ) = (1 + κ - δ) * (1 - ρ) / (δ * (ρ + κ)) := by
  unfold pauseH pauseC wholeH wholeC
  field_simp
  ring

/-- The ratio of margins on the source's cell: `δ = 1/100`, `κ = 1`, `ρ = 1/10` gives `1791/11`
(the source's "`163×`").
Source: fud.md R2 item 6. Kind: N+. Fidelity: exact -/
theorem w_accounting_margin_ratio :
    (pauseH (1/100) 1 / pauseC (1/100)) / (wholeH (1/10) 1 / wholeC (1/10)) = 1791 / 11 := by
  unfold pauseH pauseC wholeH wholeC; norm_num

end Cleanroom.Corrigibility.CorrThreeStepFacts
