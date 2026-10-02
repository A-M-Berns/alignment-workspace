import Cleanroom.Corrigibility.CorrLegitGeneral.ThreeCellRefuted

/-! Audit r4 (adversarial) probe: does the refuting instance's hypothesis package bite?

A refutation of `TotalTrustWrt Q π F → WeakValuesWrt Q π F` by one instance is only evidence
against the conjecture if (i) the hypothesis is not automatic on the instance's frame — here:
some other deferrer fails local Total Trust on `F7` — and (ii) the conclusion does not fail for
a junk reason — here: the menu does have a recommended strategy, so "no recommended strategy
beats `x₁`" is a real failure, not an empty existential.

(i) `F7_uniform_not_totalTrustWrt`: the uniform deferrer fails local Total Trust on `F7` at
`X = 𝟙_{cell 1}`, `s = 17/25` (only the two `p₄`-worlds qualify; the sum is
`(1/7)(0 − 17/25) + (1/7)(1 − 17/25) = −9/175`).
(ii) `S7_recommended`: `S7` is a recommended strategy for the menu (membership, the cell
constraint, optimality at every world). -/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

set_option linter.unusedSimpArgs false

/-- The uniform deferrer on seven worlds. -/
def πu7 : Fin 7 → ℝ := fun _ => 1 / 7

/-- The local-Total-Trust hypothesis is not automatic on `F7`: the uniform deferrer fails it. -/
theorem F7_uniform_not_totalTrustWrt : ¬ TotalTrustWrt Q7 πu7 F7 := by
  intro h
  have hm : MeasurableWrt Q7 ((![0, 1, 0] : Fin 3 → ℝ) ∘ Q7) :=
    (measurableWrt_iff_exists_comp Q7 _).2 ⟨_, rfl⟩
  have := h _ hm (17 / 25)
  have hP : ∀ w, F7.P w = P7 w := fun _ => rfl
  simp only [Fin.sum_univ_seven, hP, P7_0, P7_1, P7_2, P7_3, P7_4, P7_5, P7_6, E_r7a, E_r7b,
    E_r7c, E_r7d, Function.comp, Q7_0, Q7_1, Q7_2, Q7_3, Q7_4, Q7_5, Q7_6, πu7,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, vec3_two] at this
  norm_num at this

/-- `S7` is a recommended strategy for the menu `{x₀, x₁, x₂}` on `F7`. -/
theorem S7_recommended : F7.Recommended {x7_0, x7_1, x7_2} S7 := by
  obtain ⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩, ⟨c0, c1, c2⟩, ⟨d0, d1, d2⟩⟩ := scores7
  have hP : ∀ w, F7.P w = P7 w := fun _ => rfl
  refine ⟨⟨fun w => ?_, fun w v h => ?_⟩, fun w o ho => ?_⟩
  · fin_cases w <;> simp [S7]
  · simp only [hP] at h
    fin_cases w <;> fin_cases v <;>
      first
        | rfl
        | (exfalso
           have h0 := congrFun h 0
           have h1 := congrFun h 1
           first
             | (norm_num [P7, r7a, r7b, r7c, r7d] at h0; done)
             | (norm_num [P7, r7a, r7b, r7c, r7d] at h1; done))
  · simp only [mem_insert, mem_singleton] at ho
    rcases ho with rfl | rfl | rfl <;> fin_cases w <;>
      norm_num [hP, P7, S7, a0, a1, a2, b0, b1, b2, c0, c1, c2, d0, d1, d2]

end

end Cleanroom.Corrigibility.CorrLegitGeneral
