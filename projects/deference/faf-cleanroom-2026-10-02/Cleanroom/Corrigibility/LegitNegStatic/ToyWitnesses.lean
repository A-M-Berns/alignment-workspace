import Cleanroom.Corrigibility.LegitNegStatic.Readouts
import Cleanroom.Corrigibility.LegitNegStatic.Toys

/-!
# Boundary witnesses over the toys

Package `legit-neg-static`. The N− witnesses the mandate requires for the definitions of
record: S3 leaves `[0, 1]` (target 2), and the R2-S1 lemma of `Readouts.lean` fails under
`blindImpute` and when the reference action itself voids somewhere (target 4, B17).
-/

namespace Cleanroom.Corrigibility.LegitNegStatic

open Finset Problem

/-- **S3 is not a `[0, 1]` score** (finding 2): on B's toy with `v = 1/4`, `w = −1` and `D = 1`,
the legitimate humans at `(b, a₀)` score `a₁` at `−1/4` (B12's instance).
Source: [[corr-legit-neg-2-inventory]] item 2-002 (finding: S3 ∉ [0,1])
Kind: N-
Fidelity: exact -/
theorem S3_toy_neg :
    (toyB (1/4) (-1) 1 1 (1/2) (by norm_num) (by norm_num)).S3 1 1 0 1 = -1/4 := by
  have hmax : (toyB (1/4) (-1) 1 1 (1/2) (by norm_num) (by norm_num)).umax 1 = 1/4 := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun c _ => by fin_cases c <;> simp [toyB] <;> norm_num
    · have := (toyB (1/4) (-1) 1 1 (1/2) (by norm_num) (by norm_num)).le_umax 1 0
      simpa [toyB] using this
  unfold S3
  rw [hmax]
  simp [toyB]
  norm_num

/-- **The R2-S1 lemma fails under `blindImpute`** (B17 with `y = 1`): on B's toy with
`v = 1/2`, `w = 0`, `u_g ≡ 1`, `π_b = 1/2`, the fully legitimate `a₀` is `H`-optimal but not
ratifiable under `blindImpute 1`, because the blind evaluators at `(b, a₀)` write `1` for the
voiding `a₁`.
Source: [[corr-legit-neg-2-inventory]] item 2-004 (B17)
Kind: N-
Fidelity: exact -/
theorem R2_S1_lemma_fails_blindImpute :
    let P := toyB (1/2) 0 1 1 (1/2) (by norm_num) (by norm_num)
    0 ∈ argmax P.H ∧ 0 ∉ P.ratifiable (P.blindImpute 1) := by
  intro P
  constructor
  · rw [mem_argmax]; intro b; fin_cases b <;> simp [P, toyB, H, W, EU, Fin.sum_univ_two]
  · rw [mem_ratifiable]; push Not
    refine ⟨1, ?_⟩
    simp [P, toyB, R2scores, blindImpute, Fin.sum_univ_two]
    norm_num

/-- **The R2-S1 lemma fails when the reference action voids somewhere** (B17's "voiding
reference hides the `b`-branch"): on B's toy with `v = 1`, `w = 0`, `u_{g0} = 1/2`, `u_{g1} = 1`,
`π_b = 1/2`, the action `a₁` (void in `b`) is R2-S1-ratifiable — its realized vector only
sees `g` — but is not `H`-optimal.
Source: [[corr-legit-neg-2-inventory]] item 2-004 (B17)
Kind: N-
Fidelity: exact -/
theorem R2_S1_lemma_fails_voiding_ref :
    let P := toyB 1 0 (1/2) 1 (1/2) (by norm_num) (by norm_num)
    1 ∈ P.ratifiable (S1 P.u) ∧ 1 ∉ argmax P.H := by
  intro P
  constructor
  · rw [mem_ratifiable]; intro b; fin_cases b <;> simp [P, toyB, R2scores, Fin.sum_univ_two] <;> norm_num
  · rw [mem_argmax]; push Not
    refine ⟨0, ?_⟩
    simp [P, toyB, H, W, EU, Fin.sum_univ_two]
    norm_num

end Cleanroom.Corrigibility.LegitNegStatic
