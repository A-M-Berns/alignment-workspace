import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# `corr-power-channel` — T10: the component-hazard model and the affine margin

The `d1` thread's finite model in which "which component of the humans' advantage carries D1" is
computable. Faults `θ, N, π, r` (mutually exclusive, rates `p_k`, `p₀ = 1 − ∑ p_k`), stakes `c₀`
on no fault and `h_k` on fault `k`, one detector per component with sensitivity `b_k` and false-alarm
rate `a_k`, independent, the humans pressing iff any fires. The agent clears `θ` with probability
`λ`. Derived: `q_k = 1 − (1 − b_k)∏_{j≠k}(1 − a_j)` (press probability on fault `k`),
`α = 1 − ∏_j (1 − a_j)` (false-press probability), `F = p₀ α c₀`, `H(λ) = ∑_k p_k q_k h_k −
λ p_θ q_θ h_θ`, `margin λ = H λ − F`.

* `margin_affine`: `margin λ = margin 0 − λ p_θ q_θ h_θ` (L).
* `wholeLine_margin_one_neg_iff`: under whole-line stakes (`c₀ = 9/10`, `h = 11/10`) and the
  worked parameters with `a_θ` free, `margin 1 < 0 ⟺ a_θ > 31603/894103` — `F` and `H(1)` are
  affine in `a_θ` and this is their exact crossing; the companion `wholeLine_margin_zero_pos_iff`
  gives `margin 0 > 0 ⟺ a_θ < 311795/1788206`, so **the margin changes sign on `[0, 1]` iff
  `31603/894103 < a_θ < 311795/1788206`** (`wholeLine_sign_change_iff`); `3/100` is below the
  lower threshold and `4/100` above it (`wholeLine_cells`).
* `wholeLine_lambdaStar`: at the worked `a_θ = 1/20`, `H 1 < F < H 0` and the exact root is
  `λ* = 71737/80190`.
* `pause_no_crossing`: under pause stakes (`c₀ = 1`, `h = 10`) `F < H 1`, no crossing.

(H1)–(H4) of the source are what the model *is* (constants); witnesses are N+ *for the model*.

Sources: `research/corrigibility/workflow-2026-09-14b/develop/d1-special-case-final.md` (cited
as d1-final.md) D6 (l. 38), S3 (l. 50), P3 (l. 82); corr-wf14b-037, 039.
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel

noncomputable section

/-- **The component-hazard model** (D6): fault rates, detector sensitivities and false-alarm
rates per component, stakes. Independence and "press iff any fires" are built into the derived
quantities below.
Source: d1-final.md D6 (l. 38)
Kind: D
Fidelity: exact (one time step; `λ` is an argument of `H`, not a trajectory) -/
structure HazardModel where
  /-- fault rates -/
  pθ : ℝ
  pN : ℝ
  pπ : ℝ
  pr : ℝ
  /-- detector sensitivities `b_k` -/
  bθ : ℝ
  bN : ℝ
  bπ : ℝ
  br : ℝ
  /-- detector false-alarm rates `a_k` -/
  aθ : ℝ
  aN : ℝ
  aπ : ℝ
  ar : ℝ
  /-- stake on no fault -/
  c₀ : ℝ
  /-- stakes on each fault -/
  hθ : ℝ
  hN : ℝ
  hπ : ℝ
  hr : ℝ

namespace HazardModel

variable (M : HazardModel)

/-- `p₀ = 1 − ∑ p_k`. Source: d1-final.md D6 (l. 38). Kind: D. Fidelity: exact -/
def p₀ : ℝ := 1 - (M.pθ + M.pN + M.pπ + M.pr)

/-- `q_θ = 1 − (1 − b_θ)(1 − a_N)(1 − a_π)(1 − a_r)`. Source: d1-final.md S3 (l. 50). Kind: D.
Fidelity: exact -/
def qθ : ℝ := 1 - (1 - M.bθ) * ((1 - M.aN) * (1 - M.aπ) * (1 - M.ar))

/-- `q_N`. Source: d1-final.md S3 (l. 50). Kind: D. Fidelity: exact -/
def qN : ℝ := 1 - (1 - M.bN) * ((1 - M.aθ) * (1 - M.aπ) * (1 - M.ar))

/-- `q_π`. Source: d1-final.md S3 (l. 50). Kind: D. Fidelity: exact -/
def qπ : ℝ := 1 - (1 - M.bπ) * ((1 - M.aθ) * (1 - M.aN) * (1 - M.ar))

/-- `q_r`. Source: d1-final.md S3 (l. 50). Kind: D. Fidelity: exact -/
def qr : ℝ := 1 - (1 - M.br) * ((1 - M.aθ) * (1 - M.aN) * (1 - M.aπ))

/-- `α = 1 − ∏_j (1 − a_j)`, the false-press probability on no fault.
Source: d1-final.md S3 (l. 50). Kind: D. Fidelity: exact -/
def α : ℝ := 1 - (1 - M.aθ) * (1 - M.aN) * (1 - M.aπ) * (1 - M.ar)

/-- `F = p₀ α c₀`, the false-press side (constant in `λ`).
Source: d1-final.md S3 (l. 50). Kind: D. Fidelity: exact -/
def F : ℝ := M.p₀ * M.α * M.c₀

/-- `H(λ) = ∑_k p_k q_k h_k − λ p_θ q_θ h_θ`, the harm side on the agent's cleared branch.
Source: d1-final.md S3 (l. 50). Kind: D. Fidelity: exact -/
def H (l : ℝ) : ℝ :=
  M.pθ * M.qθ * M.hθ + M.pN * M.qN * M.hN + M.pπ * M.qπ * M.hπ + M.pr * M.qr * M.hr -
    l * (M.pθ * M.qθ * M.hθ)

/-- `margin λ = H λ − F`: D2's target on the cleared branch holds iff `margin λ ≥ 0`.
Source: d1-final.md S3 (l. 50, "`M(λ_t) := H_0 − F − λ_t p_θ q_θ h_θ ≥ 0`")
Kind: D
Fidelity: exact -/
def margin (l : ℝ) : ℝ := M.H l - M.F

/-- **S3/P3: the margin is affine in `λ`** with slope `−p_θ q_θ h_θ` and the false-press side
constant: `margin λ = margin 0 − λ p_θ q_θ h_θ`.
Source: d1-final.md S3 (l. 50), P3 (l. 82, "Harm side affine in `λ` with slope `−p_θ q_θ h_θ`;
false side constant")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem margin_affine (l : ℝ) : M.margin l = M.margin 0 - l * (M.pθ * M.qθ * M.hθ) := by
  unfold margin H; ring

/-- The exact root `λ* = (H 0 − F)/(H 0 − H 1)` when `H 1 < F < H 0`.
Source: d1-final.md P3 (l. 82, "`λ* = (H_0 − F)/(H_0 − H_1)` when `H_1 < F < H_0`")
Kind: L
Fidelity: exact
Hyps: (a) `H 1 < F < H 0` -/
theorem margin_root (h1 : M.H 1 < M.F) (h0 : M.F < M.H 0) :
    M.margin ((M.H 0 - M.F) / (M.H 0 - M.H 1)) = 0 ∧
      0 < (M.H 0 - M.F) / (M.H 0 - M.H 1) ∧ (M.H 0 - M.F) / (M.H 0 - M.H 1) < 1 := by
  have hd : 0 < M.H 0 - M.H 1 := by linarith
  have hslope : M.H 0 - M.H 1 = M.pθ * M.qθ * M.hθ := by unfold H; ring
  refine ⟨?_, div_pos (by linarith) hd, (div_lt_one hd).2 (by linarith)⟩
  rw [margin_affine, hslope, div_mul_cancel₀ _ (by rw [← hslope]; exact hd.ne')]
  unfold margin; ring

end HazardModel

/-! ## The worked parameters -/

/-- **The worked parameters** (D6): `p_θ = 1/10`, `p_N = p_π = p_r = 1/50`; detectors
`θ (9/10, a_θ)`, `N (9/10, 1/50)`, `π (1, 0)`, `r (3/5, 1/50)`; stakes `c₀` and a common fault
stake `h`. `a_θ` is left free for the threshold statement (the worked value is `1/20`).
Source: d1-final.md D6 (l. 38, "Worked parameters throughout")
Kind: D
Fidelity: exact -/
def worked (aθ c₀ h : ℝ) : HazardModel where
  pθ := 1 / 10
  pN := 1 / 50
  pπ := 1 / 50
  pr := 1 / 50
  bθ := 9 / 10
  bN := 9 / 10
  bπ := 1
  br := 3 / 5
  aθ := aθ
  aN := 1 / 50
  aπ := 0
  ar := 1 / 50
  c₀ := c₀
  hθ := h
  hN := h
  hπ := h
  hr := h

/-- Whole-line stakes `c₀ = 9/10`, `h = 11/10`. Source: d1-final.md D6 (l. 38). Kind: D.
Fidelity: exact -/
def wholeLine (aθ : ℝ) : HazardModel := worked aθ (9 / 10) (11 / 10)

/-- Pause stakes `c₀ = 1`, `h = 10`. Source: d1-final.md D6 (l. 38). Kind: D. Fidelity: exact -/
def pause (aθ : ℝ) : HazardModel := worked aθ 1 10

/-- `margin 1` under whole-line stakes is affine in `a_θ`: `31603/1250000 − (894103/1250000) a_θ`.
Source: d1-final.md P3 (l. 82). Kind: L. Fidelity: exact -/
theorem wholeLine_margin_one_eq (aθ : ℝ) :
    (wholeLine aθ).margin 1 = 31603 / 1250000 - 894103 / 1250000 * aθ := by
  simp only [wholeLine, worked, HazardModel.margin, HazardModel.H, HazardModel.F, HazardModel.p₀,
    HazardModel.α, HazardModel.qθ, HazardModel.qN, HazardModel.qπ, HazardModel.qr]
  ring

/-- `margin 0` under whole-line stakes is affine in `a_θ`: `62359/500000 − (894103/1250000) a_θ`.
Source: d1-final.md P3 (l. 82). Kind: L. Fidelity: exact -/
theorem wholeLine_margin_zero_eq (aθ : ℝ) :
    (wholeLine aθ).margin 0 = 62359 / 500000 - 894103 / 1250000 * aθ := by
  simp only [wholeLine, worked, HazardModel.margin, HazardModel.H, HazardModel.F, HazardModel.p₀,
    HazardModel.α, HazardModel.qθ, HazardModel.qN, HazardModel.qπ, HazardModel.qr]
  ring

/-- **The lower threshold, exact: `margin 1 < 0 ⟺ a_θ > 31603/894103`** under whole-line stakes
(`F(a_θ)` and `H_1(a_θ)` are affine in `a_θ`; this is their crossing).
Source: d1-final.md S3 (l. 50, "iff `a_θ > a_θ* = 31603/894103`"), P3 (l. 82)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem wholeLine_margin_one_neg_iff (aθ : ℝ) :
    (wholeLine aθ).margin 1 < 0 ↔ (31603 : ℝ) / 894103 < aθ := by
  rw [wholeLine_margin_one_eq]
  constructor <;> intro h <;> linarith

/-- **The upper threshold, exact: `margin 0 > 0 ⟺ a_θ < 311795/1788206`** under whole-line
stakes (where `F(a_θ)` crosses `H_0(a_θ)`). Not in the source; it completes "changes sign on
`[0, 1]`" into an exact two-sided statement.
Source: d1-final.md S3 (l. 50) (completed here)
Kind: P
Fidelity: stronger: the source states only the lower threshold
Hyps: (a) none -/
theorem wholeLine_margin_zero_pos_iff (aθ : ℝ) :
    0 < (wholeLine aθ).margin 0 ↔ aθ < (311795 : ℝ) / 1788206 := by
  rw [wholeLine_margin_zero_eq]
  constructor <;> intro h <;> linarith

/-- **S3, exact: under whole-line stakes the margin changes sign on `[0, 1]`
(`margin 0 > 0 > margin 1`) iff `31603/894103 < a_θ < 311795/1788206`.**
Source: d1-final.md S3 (l. 50, "the sign changes at `λ*` … iff `a_θ > a_θ*`")
Kind: C
Fidelity: stronger: two-sided (the source's one-sided "iff" presupposes `margin 0 > 0`)
Hyps: (a) none -/
theorem wholeLine_sign_change_iff (aθ : ℝ) :
    (0 < (wholeLine aθ).margin 0 ∧ (wholeLine aθ).margin 1 < 0) ↔
      ((31603 : ℝ) / 894103 < aθ ∧ aθ < (311795 : ℝ) / 1788206) := by
  rw [wholeLine_margin_one_neg_iff, wholeLine_margin_zero_pos_iff]
  exact and_comm

/-- **The cells**: `a_θ = 3/100` is below the lower threshold (no sign change: `margin 1 ≥ 0`);
`a_θ = 4/100` is above it (sign change).
Source: d1-final.md P3 (l. 82, "at `a_θ = 0.03` … holds; at `0.04` … fails")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem wholeLine_cells :
    ¬ (wholeLine (3 / 100)).margin 1 < 0 ∧ (wholeLine (4 / 100)).margin 1 < 0 ∧
      0 < (wholeLine (4 / 100)).margin 0 := by
  rw [wholeLine_margin_one_neg_iff, wholeLine_margin_one_neg_iff, wholeLine_margin_zero_pos_iff]
  norm_num

/-- **The worked instance: `λ* = 71737/80190`** — at `a_θ = 1/20`, whole-line stakes,
`H 1 < F < H 0` and the margin vanishes exactly at `71737/80190 ∈ (0, 1)`.
Source: d1-final.md S3 (l. 50, "`λ* = 71737/80190`"), P3 (l. 82)
Kind: N+
Fidelity: exact (rule 4: the exact rational, no decimals)
Hyps: none -/
theorem wholeLine_lambdaStar :
    (wholeLine (1 / 20)).H 1 < (wholeLine (1 / 20)).F ∧
      (wholeLine (1 / 20)).F < (wholeLine (1 / 20)).H 0 ∧
      (wholeLine (1 / 20)).margin (71737 / 80190) = 0 := by
  simp only [wholeLine, worked, HazardModel.margin, HazardModel.H, HazardModel.F, HazardModel.p₀,
    HazardModel.α, HazardModel.qθ, HazardModel.qN, HazardModel.qπ, HazardModel.qr]
  norm_num

/-- **Pause stakes: no crossing** — `F < H 1` at the worked parameters, so the margin is positive
on all of `[0, 1]`.
Source: d1-final.md S3 (l. 50, "and never under pause stakes"), P3 (l. 82, "Pause:
`F = 0.07360 < H_1 = 0.50690`")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem pause_no_crossing :
    (pause (1 / 20)).F < (pause (1 / 20)).H 1 ∧ ∀ l ∈ Set.Icc (0 : ℝ) 1, 0 < (pause (1 / 20)).margin l := by
  have key : (pause (1 / 20)).F < (pause (1 / 20)).H 1 := by
    simp only [pause, worked, HazardModel.H, HazardModel.F, HazardModel.p₀, HazardModel.α,
      HazardModel.qθ, HazardModel.qN, HazardModel.qπ, HazardModel.qr]
    norm_num
  refine ⟨key, fun l hl => ?_⟩
  rw [HazardModel.margin_affine]
  have h1 : (pause (1 / 20)).margin 1 = (pause (1 / 20)).margin 0 - 1 * ((pause (1 / 20)).pθ *
      (pause (1 / 20)).qθ * (pause (1 / 20)).hθ) := HazardModel.margin_affine _ 1
  have hslope : 0 ≤ (pause (1 / 20)).pθ * (pause (1 / 20)).qθ * (pause (1 / 20)).hθ := by
    simp only [pause, worked, HazardModel.qθ]; norm_num
  have hm1 : 0 < (pause (1 / 20)).margin 1 := by unfold HazardModel.margin; linarith
  nlinarith [hl.1, hl.2]

end

end Cleanroom.Corrigibility.CorrPowerChannel
