import Cleanroom.Corrigibility.CorrThreeStepFacts.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# T18: pointwise (refined-press) trust after a scan

Pattern A with `Ω = World × S`: the agent's scan `s` is drawn from `P(s | w)` independently of
the press given the world (`press (w, s) = twoPress α β w`), and the payoff is the two-state
value on `w`. Pointwise trust — the below-threshold inequality on every scan cell — is the
family `(1 − ε)·α·P(s₀ | R)·c ≤ ε·β·P(s₀ | W)·h` (`scan_pointwise_iff`), product form with no
`min` and no division; the source's `min_s P(s | W)/P(s | R)` form is its corollary when every
`P(s₀ | R)` is positive. A cell the scan can rule out (`P(s₀ | W) = 0 < P(s₀ | R)`) forces
`α = 0` or `c ≤ 0` (`scan_forces_alpha_zero`). Witnesses in this file.

Source: `taylor-voice.md` l. 27–31 (corr-wf14b-2-014); `substitution.md` R7 item 13.
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

section Scan

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **The scan setting.** `Ω = World × S`, joint `μ(w) · P(s | w)`, sensor reading the world
only (`s ⊥ Pr | w`), two-state value on the world; `Sh = {stop}`.
Source: [[corr-wf14b-2-inventory]] 014 / taylor-voice.md l. 27–31; substitution.md R7 item 13
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def scan (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (k : World → Distr S) : ThreeStep (World × S) Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => kernelProd (twoPoint ε hε) k
  press := fun _ p => twoPress α β p.1
  press_nonneg := fun _ p => by cases p.1 <;> simp [twoPress, hα.1, hβ.1]
  press_le_one := fun _ p => by cases p.1 <;> simp [twoPress, hα.2, hβ.2]
  V := fun _ _ b p => twoValue c h b p.1

/-- The scan cell `{(w, s) | s = s₀}`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def sCell (s₀ : S) : Finset (World × S) := univ.filter fun p => p.2 = s₀

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1) (k : World → Distr S)

/-- The press-weighted two-option sum on a scan cell:
`(1 − ε)·α·P(s₀ | R)·c − ε·β·P(s₀ | W)·h`.
Source: substitution.md R7 item 13 (the posterior odds on the cell). Kind: L. Fidelity: exact -/
theorem scan_pressExpectOn_sCell (s₀ : S) :
    (scan ε α β c h hε hα hβ k).pressExpectOn () (sCell s₀)
        ((scan ε α β c h hε hα hβ k).Xo () .press .cont .stop) =
      (1 - ε) * α * (k .right).mass s₀ * c - ε * β * (k .wrong).mass s₀ * h := by
  unfold pressExpectOn sCell
  rw [sum_filter, Fintype.sum_prod_type, World.sum_eq]
  simp only [sum_ite_eq', mem_univ, if_true, scan, kernelProd_mass, twoPoint_right, twoPoint_wrong,
    twoPress, twoValue, Xo]
  ring

/-- **T18, pointwise trust as a product-form family.** The below-threshold inequality holds on
every scan cell iff `(1 − ε)·α·P(s₀ | R)·c ≤ ε·β·P(s₀ | W)·h` for every `s₀` — no `min`, no
division; the source's `α/β ≤ (ε/(1 − ε))(h/c)·min_s P(s | W)/P(s | R)` is this family divided
through where the divisors are positive.
Source: [[corr-wf14b-2-inventory]] 014 / taylor-voice.md l. 27–31; substitution.md R7 item 13
Kind: L
Fidelity: exact (product form; the ratio form is a corollary under positivity)
Hyps: (a) only -/
theorem scan_pointwise_iff :
    (∀ s₀, (scan ε α β c h hε hα hβ k).pressExpectOn () (sCell s₀)
        ((scan ε α β c h hε hα hβ k).Xo () .press .cont .stop) ≤ 0) ↔
      ∀ s₀, (1 - ε) * α * (k .right).mass s₀ * c ≤ ε * β * (k .wrong).mass s₀ * h := by
  simp only [scan_pressExpectOn_sCell, sub_nonpos]

/-- **T18, corollary.** If some scan cell is impossible when wrong but possible when right
(`P(s₀ | W) = 0 < P(s₀ | R)`) and `ε < 1`, pointwise trust forces `α = 0` or `c ≤ 0`: a perfect
scan leaves no room for a false press. (At `P(s₀ | R) = 0` the ratio form is undefined but the
cell is trivially compliant — the junk the product form avoids.)
Source: substitution.md R7 item 13 ("a perfect scan forces `α = 0`"); taylor-voice.md l. 31
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem scan_forces_alpha_zero (hε1 : ε < 1) (s₀ : S) (hW : (k .wrong).mass s₀ = 0)
    (hR : 0 < (k .right).mass s₀)
    (hpt : ∀ s₀, (scan ε α β c h hε hα hβ k).pressExpectOn () (sCell s₀)
        ((scan ε α β c h hε hα hβ k).Xo () .press .cont .stop) ≤ 0) :
    α = 0 ∨ c ≤ 0 := by
  have := (scan_pointwise_iff ε α β c h hε hα hβ k).mp hpt s₀
  rw [hW, mul_zero, zero_mul] at this
  have h1 : 0 < (1 - ε) * (k .right).mass s₀ := mul_pos (by linarith) hR
  have h2 : ((1 - ε) * (k .right).mass s₀) * (α * c) ≤ 0 := by linarith
  have h3 : α * c ≤ 0 := nonpos_of_mul_nonpos_right h2 h1
  rcases hα.1.lt_or_eq with hα0 | hα0
  · exact Or.inr (nonpos_of_mul_nonpos_right h3 hα0)
  · exact Or.inl hα0.symm

end Scan

/-! ## Witnesses -/

/-- The two-point distribution on `Fin 2` with `mass 0 = p`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def fin2Point (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) : Distr (Fin 2) where
  mass i := if i = 0 then p else 1 - p
  nonneg i := by fin_cases i <;> simp <;> linarith [hp.1, hp.2]
  sum_eq_one := by rw [Fin.sum_univ_two]; simp

/-- The scan kernel `P(s | W) = (3/4, 1/4)`, `P(s | R) = (1/4, 3/4)`.
Source: mandate T18 (witness parameters). Kind: D. Fidelity: n/a -/
noncomputable def scanKernel : World → Distr (Fin 2)
  | .right => fin2Point (1/4) (by constructor <;> norm_num)
  | .wrong => fin2Point (3/4) (by constructor <;> norm_num)

/-- **T18 witness, both cells comply** on the `w3` numbers (`h = 20`): `19/1600 ≤ 1080/1600` and
`57/1600 ≤ 360/1600`.
Source: mandate T18. Kind: N+. Fidelity: exact -/
theorem w_scan_both_hold :
    ∀ s₀, (scan (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10 scanKernel).pressExpectOn
        () (sCell s₀)
        ((scan (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10 scanKernel).Xo () .press
          .cont .stop) ≤ 0 := by
  rw [scan_pointwise_iff]
  intro s₀; fin_cases s₀ <;> simp [scanKernel, fin2Point] <;> norm_num

/-- **T18 witness, one cell fails** at `h = 1`: the scan cell `s = 1` (likely when right) has
`57/1600 > 18/1600`, while `s = 0` still complies (`19/1600 ≤ 54/1600`): pointwise trust fails.
Source: mandate T18. Kind: N+. Fidelity: exact -/
theorem w_scan_one_fails :
    ¬ (∀ s₀, (scan (1/20) (1/20) (9/10) 1 1 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10 scanKernel).pressExpectOn
        () (sCell s₀)
        ((scan (1/20) (1/20) (9/10) 1 1 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10 scanKernel).Xo () .press
          .cont .stop) ≤ 0) ∧
      (scan (1/20) (1/20) (9/10) 1 1 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10 scanKernel).pressExpectOn
        () (sCell 0)
        ((scan (1/20) (1/20) (9/10) 1 1 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10 scanKernel).Xo () .press
          .cont .stop) ≤ 0 := by
  constructor
  · rw [scan_pointwise_iff]
    intro hall
    have := hall 1
    simp [scanKernel, fin2Point] at this
    norm_num at this
  · rw [scan_pressExpectOn_sCell]; simp [scanKernel, fin2Point]; norm_num

end Cleanroom.Corrigibility.CorrThreeStepFacts
