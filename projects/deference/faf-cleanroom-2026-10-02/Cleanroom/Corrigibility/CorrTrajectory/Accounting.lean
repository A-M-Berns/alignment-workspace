import Cleanroom.Found.CorrThreeStep.Setting
import Mathlib.Tactic.FieldSimp

/-!
# `corr-trajectory` — `Accounting`: whole-line accounting, `ε*`, the recovery threshold (T11)

Arithmetic over the parent's `complianceThreshold c h = c/(c+h)` and `epsStar α β c h = αc/(αc+βh)`:

* the §P.10 rows (`F = 100`, `d = 1`, `h = 4`, `(α, β) = (1/10, 3/5)`, `c = (1 − r)F + r d`): the exact
  end rows `r = 0` (`25/26`, `25/31`) and `r = 1` (`1/5`, `1/25`), and `r = 1/2` (`101/109`,
  `101/149`); symmetric accounting `c = h = 100` (`1/2`, `1/7`) and `h = 200` (`1/3`, `1/13`);
* **Prop. 9 sharpened, not refuted** (`prop9_lever_is_ratio`; audit r1 B3): the thresholds depend on
  `(c, h)` only through `h/c` (`epsStar_homogeneous`, `complianceThreshold_homogeneous`). On Prop. 9's
  stated domain — `h` fixed and small against `F`, `c = (1 − r)F + r d` — this *confirms* "resumability
  is what makes (i) satisfiable": with `h` fixed only `r` moves `h/c`. The source's own clause "unless
  `h_t` is itself of the order of `F_t`" names the other lever, and the instance `h = 200` against
  `c = F = 100` (threshold `1/3`, `ε* = 1/13`, the same as `(1, 2)`) sits exactly in that excluded case.
  Surviving neighbour: gap accounting `c = F_agent − F_alt`, `h = F_alt − F_mis`, the parent's stakes;
* 2-041: `ε† = epsStar (1/10) (1/2) 20 2 = 2/3`, and the effective rate `(1 − μ)ε + μρε` lies between
  `ε` and `ρε`, so no self-suspicion weight reaches `ε†` unless `max(ε, ρε) ≥ ε†`.

S2 vs S2′ (per-round vs whole-line) is Abram's Question 5: both are defined (`Process.executedWL`),
nothing is decided here.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open Cleanroom.Found.CorrThreeStep

namespace Accounting

/-- §P.10, `r = 0` (whole-line): threshold `25/26`, `ε* = 25/31`.
Source: [[corr-wf14-inventory]] 2-004 / joint.md §P.10
Kind: N+
Fidelity: exact -/
theorem row_r0 : complianceThreshold 100 4 = 25 / 26 ∧ epsStar (1 / 10) (3 / 5) 100 4 = 25 / 31 := by
  unfold complianceThreshold epsStar <;> norm_num

/-- §P.10, `r = 1` (fully resumable): threshold `1/5`, `ε* = 1/25`.
Source: [[corr-wf14-inventory]] 2-004 / joint.md §P.10
Kind: N+
Fidelity: exact -/
theorem row_r1 : complianceThreshold 1 4 = 1 / 5 ∧ epsStar (1 / 10) (3 / 5) 1 4 = 1 / 25 := by
  unfold complianceThreshold epsStar <;> norm_num

/-- §P.10, `r = 1/2` (`c = 101/2`): threshold `101/109`, `ε* = 101/149`.
Source: [[corr-wf14-inventory]] 2-004 / joint.md §P.10 (the `≈ 0.93`, `≈ 0.68` row, exact)
Kind: N+
Fidelity: exact -/
theorem row_half :
    complianceThreshold (101 / 2) 4 = 101 / 109 ∧ epsStar (1 / 10) (3 / 5) (101 / 2) 4 = 101 / 149 := by
  unfold complianceThreshold epsStar <;> norm_num

/-- Symmetric accounting `c = h = 100`: `1/2`, `1/7`.
Source: mandate T11. Kind: N+. Fidelity: exact -/
theorem row_symmetric : complianceThreshold 100 100 = 1 / 2 ∧ epsStar (1 / 10) (3 / 5) 100 100 = 1 / 7 := by
  unfold complianceThreshold epsStar <;> norm_num

/-- `h = 200` against `c = 100`: `1/3`, `1/13`.
Source: mandate T11. Kind: N+. Fidelity: exact -/
theorem row_h200 : complianceThreshold 100 200 = 1 / 3 ∧ epsStar (1 / 10) (3 / 5) 100 200 = 1 / 13 := by
  unfold complianceThreshold epsStar <;> norm_num

/-- **`ε*` is homogeneous of degree `0` in `(c, h)`**: if both scale, the threshold depends only on `h/c`.
Source: [[corr-wf14-inventory]] 2-041 / mandate T11 ("if both scale, the threshold depends only on `h/c`")
Kind: L
Fidelity: exact -/
theorem epsStar_homogeneous (α β c h k : ℝ) (hk : k ≠ 0) :
    epsStar α β (k * c) (k * h) = epsStar α β c h := by
  unfold epsStar
  rcases eq_or_ne (α * c + β * h) 0 with h0 | h0
  · have : α * (k * c) + β * (k * h) = k * (α * c + β * h) := by ring
    rw [this, h0, mul_zero, div_zero, div_zero]
  · field_simp <;> ring

/-- The compliance threshold is homogeneous of degree `0` too.
Source: mandate T11. Kind: L. Fidelity: exact -/
theorem complianceThreshold_homogeneous (c h k : ℝ) (hk : k ≠ 0) :
    complianceThreshold (k * c) (k * h) = complianceThreshold c h := by
  unfold complianceThreshold
  rcases eq_or_ne (c + h) 0 with h0 | h0
  · have : k * c + k * h = k * (c + h) := by ring
    rw [this, h0, mul_zero, div_zero, div_zero]
  · field_simp <;> ring

/-- **Prop. 9's clause carries the content: the lever is `h/c`** (a sharpening, not a refutation).
Prop. 9 reads "*unless `h_t` is itself of the order of `F_t` (an irreversible catastrophe)*,
resumability is what makes (i) satisfiable for a long-horizon agent at all". On its stated domain
(`h` fixed and small against `F`, `c = (1 − r)F + r d`) homogeneity confirms it: the thresholds move
with `(c, h)` only through `h/c`, and with `h` fixed only `r` moves `h/c`. The instance here —
`h = 200` against `c = F = 100` — is the case the clause excludes, and shows why the clause is where
the content sits: scaling `h` with `F` is the other way to move `h/c` (threshold `1/3`, `ε* = 1/13`,
the same as at `(c, h) = (1, 2)`). Audit r1 B3: this theorem's former name `prop9_refuted` and the
ledger's "refuted" oversold it. Surviving neighbour: gap accounting (the parent's stakes).
Source: [[corr-wf14-inventory]] 2-004 / joint.md Prop. 9 l. 141 ("Unless `h_t` is itself of the order of `F_t` (an irreversible catastrophe), resumability is what makes (i) satisfiable for a long-horizon agent at all")
Kind: N+ (sharpening: the design lever is the ratio `h/c`; resumability lowers `c`, catastrophe scales `h`)
Fidelity: exact (the instance is the source's excluded case, stated as such)
Hyps: (a) only -/
theorem prop9_lever_is_ratio :
    complianceThreshold 100 200 = complianceThreshold 1 2 ∧ epsStar (1 / 10) (3 / 5) 100 200 = epsStar (1 / 10) (3 / 5) 1 2 ∧
      complianceThreshold 100 200 = 1 / 3 := by
  refine ⟨?_, ?_, row_h200.1⟩
  · have := complianceThreshold_homogeneous 1 2 100 (by norm_num)
    norm_num at this; exact this
  · have := epsStar_homogeneous (1 / 10) (3 / 5) 1 2 100 (by norm_num)
    norm_num at this; exact this

/-- **2-041: `ε† = 2/3`** at `(c, h, α, β) = (20, 2, 1/10, 1/2)`.
Source: [[corr-wf14-inventory]] 2-041 / caution-adversary.md A8.4
Kind: N+
Fidelity: exact -/
theorem epsDagger : epsStar (1 / 10) (1 / 2) 20 2 = 2 / 3 := by
  unfold epsStar <;> norm_num

/-- The effective rate `ε^eff = (1 − μ)ε + μρε` lies between `ε` and `ρε` for `μ ∈ [0, 1]`.
Source: [[corr-wf14-inventory]] 2-041 / caution-adversary.md A8.4
Kind: L
Fidelity: exact -/
theorem epsEff_mem (ε ρ μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    min ε (ρ * ε) ≤ (1 - μ) * ε + μ * (ρ * ε) ∧ (1 - μ) * ε + μ * (ρ * ε) ≤ max ε (ρ * ε) := by
  constructor
  · nlinarith [min_le_left ε (ρ * ε), min_le_right ε (ρ * ε), hμ.1, hμ.2]
  · nlinarith [le_max_left ε (ρ * ε), le_max_right ε (ρ * ε), hμ.1, hμ.2]

/-- **No self-suspicion weight reaches `ε†` unless `max(ε, ρε) ≥ ε†`** (A8.4: "self-suspicion cannot
produce compliance at all for any agent that is right more than a third of the time").
Source: [[corr-wf14-inventory]] 2-041 / caution-adversary.md A8.4
Kind: L
Fidelity: exact -/
theorem no_reach (ε ρ εd : ℝ) (h : max ε (ρ * ε) < εd) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    (1 - μ) * ε + μ * (ρ * ε) < εd :=
  (epsEff_mem ε ρ μ hμ).2.trans_lt h

end Accounting

end Cleanroom.Corrigibility.CorrTrajectory
