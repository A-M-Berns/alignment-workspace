import Cleanroom.Lit.LitDdbAccuracyMm

/-!
# lit-ddb-accuracy-mm — audit round 2 (fidelity), probe: the six-case rule

Not imported by the library. Elaborated with `scripts/lean-check`. Evidence for one item of
`lit-ddb-accuracy-mm-audit-r2-fidelity.md`: the report says `ruleC` "is the printed rule
verbatim once `(x − v)² + C(...)` is expanded, not re-verified case by case", and the ledger
grades `ruleC` `Fidelity: exact (closed form of the printed six-case rule)`. The six theorems
below check that claim case by case against DDB App. B l. 720 (the six printed expressions,
transcribed verbatim on the right-hand sides), under DDB's case hypotheses (`x ≤ α`,
`α < x < β`, `x ≥ β`; `v_i < α`, `v_i > β`) and `α ≤ β`. Each is `simp` with the clamp
evaluation lemmas of `Rules.lean` followed by `ring`; no `sorry`.
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm.AuditR2Fidelity

open Cleanroom.Lit.LitDdbAccuracyMm

variable {α β C x v : ℝ}

/-- DDB l. 720, case 1: `x ≤ α`, `v < α`: `(x − v)²`. -/
theorem sixcase_1 (hx : x ≤ α) (hv : v < α) : ruleC α β C x v = (x - v) ^ 2 := by
  simp only [ruleC, mixRule, clampTerm, clamp_eq_left hx, clamp_eq_left hv.le]
  ring

/-- DDB l. 720, case 2: `α < x < β`, `v < α`: `(α − v)² + C (x − α)(x + α − 2v)`. -/
theorem sixcase_2 (hx1 : α < x) (hx2 : x < β) (hv : v < α) :
    ruleC α β C x v = (α - v) ^ 2 + C * (x - α) * (x + α - 2 * v) := by
  simp only [ruleC, mixRule, clampTerm, clamp_eq_self hx1.le hx2.le, clamp_eq_left hv.le]
  ring

/-- DDB l. 720, case 3: `x ≥ β`, `v < α`:
`(α − v)² + C (β − α)(β + α − 2v) + (x − β)(x + β − 2v)`. -/
theorem sixcase_3 (hαβ : α ≤ β) (hx : β ≤ x) (hv : v < α) :
    ruleC α β C x v =
      (α - v) ^ 2 + C * (β - α) * (β + α - 2 * v) + (x - β) * (x + β - 2 * v) := by
  simp only [ruleC, mixRule, clampTerm, clamp_eq_right hαβ hx, clamp_eq_left hv.le]
  ring

/-- DDB l. 720, case 4: `x ≤ α`, `v > β`:
`(α − x)(2v − α − x) + C (β − α)(2v − β − α) + (β − v)²`. -/
theorem sixcase_4 (hαβ : α ≤ β) (hx : x ≤ α) (hv : β < v) :
    ruleC α β C x v =
      (α - x) * (2 * v - α - x) + C * (β - α) * (2 * v - β - α) + (β - v) ^ 2 := by
  simp only [ruleC, mixRule, clampTerm, clamp_eq_left hx, clamp_eq_right hαβ hv.le]
  ring

/-- DDB l. 720, case 5: `α < x < β`, `v > β`: `(β − v)² + C (β − x)(2v − β − x)`. -/
theorem sixcase_5 (hαβ : α ≤ β) (hx1 : α < x) (hx2 : x < β) (hv : β < v) :
    ruleC α β C x v = (β - v) ^ 2 + C * (β - x) * (2 * v - β - x) := by
  simp only [ruleC, mixRule, clampTerm, clamp_eq_self hx1.le hx2.le, clamp_eq_right hαβ hv.le]
  ring

/-- DDB l. 720, case 6: `x ≥ β`, `v > β`: `(x − v)²`. -/
theorem sixcase_6 (hαβ : α ≤ β) (hx : β ≤ x) (hv : β < v) : ruleC α β C x v = (x - v) ^ 2 := by
  simp only [ruleC, mixRule, clampTerm, clamp_eq_right hαβ hx, clamp_eq_right hαβ hv.le]
  ring

/-- All six cases at once: under `α ≤ β`, `ruleC α β C` agrees with DDB's printed six-case
rule wherever the printed rule is defined (`v ∉ [α, β]`, all `x`). -/
theorem sixcase_all (hαβ : α ≤ β) (hv : v < α ∨ β < v) :
    ruleC α β C x v =
      if v < α then
        (if x ≤ α then (x - v) ^ 2
         else if x < β then (α - v) ^ 2 + C * (x - α) * (x + α - 2 * v)
         else (α - v) ^ 2 + C * (β - α) * (β + α - 2 * v) + (x - β) * (x + β - 2 * v))
      else
        (if x ≤ α then (α - x) * (2 * v - α - x) + C * (β - α) * (2 * v - β - α) + (β - v) ^ 2
         else if x < β then (β - v) ^ 2 + C * (β - x) * (2 * v - β - x)
         else (x - v) ^ 2) := by
  rcases hv with hv | hv
  · rw [if_pos hv]
    by_cases hx : x ≤ α
    · rw [if_pos hx]; exact sixcase_1 hx hv
    · rw [if_neg hx]
      by_cases hx2 : x < β
      · rw [if_pos hx2]; exact sixcase_2 (not_le.1 hx) hx2 hv
      · rw [if_neg hx2]; exact sixcase_3 hαβ (not_lt.1 hx2) hv
  · have hv' : ¬ v < α := not_lt.2 (hαβ.trans hv.le)
    rw [if_neg hv']
    by_cases hx : x ≤ α
    · rw [if_pos hx]; exact sixcase_4 hαβ hx hv
    · rw [if_neg hx]
      by_cases hx2 : x < β
      · rw [if_pos hx2]; exact sixcase_5 hαβ (not_le.1 hx) hx2 hv
      · rw [if_neg hx2]; exact sixcase_6 hαβ (not_lt.1 hx2) hv

end Cleanroom.Lit.LitDdbAccuracyMm.AuditR2Fidelity
