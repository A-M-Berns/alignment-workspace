import Cleanroom.Corrigibility.CorrLegitGeneral.LocalValue
import Cleanroom.Found.LitDdbFrames.ExamplesFact21

/-!
# corr-legit-general — finite evaluation helpers for the witnesses

Masses of threshold events as full sums of `if`s, so that a witness on `Fin n` reduces to a
case split on the threshold (`split_ifs`) followed by linear arithmetic. No `decide`.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Lit.LitDdbAccuracyMm

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- `fin_cases` produces `⟨2, h⟩ : Fin 4`; this normalizes it to the literal `2` for `simp`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem fin4_mk_two (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl

/-- `fin_cases` produces `⟨3, h⟩ : Fin 4`; this normalizes it to the literal `3` for `simp`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem fin4_mk_three (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl

attribute [simp] Cleanroom.Found.LitDdbFrames.Examples.fin3_mk_two

/-- Mass as a full sum of `if`s.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_eq_sum_ite (ρ : W → ℝ) (q : Finset W) :
    mass ρ q = ∑ w, if w ∈ q then ρ w else 0 := by
  rw [sum_ite_mem, univ_inter]
  rfl

/-- Mass of `[P(q) ≥ t]` as a full sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_probEvent_eq (π : W → ℝ) (F : Frame W) (q : Finset W) (t : ℝ) :
    mass π (F.probEvent q t) = ∑ w, if t ≤ mass (F.P w) q then π w else 0 := by
  show (∑ w ∈ F.probEvent q t, π w) = _
  unfold Frame.probEvent
  rw [sum_filter]

/-- Mass of `q ∧ [P(q) ≥ t]` as a full sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_inter_probEvent_eq (π : W → ℝ) (F : Frame W) (q : Finset W) (t : ℝ) :
    mass π (q ∩ F.probEvent q t) =
      ∑ w, if (t ≤ mass (F.P w) q ∧ w ∈ q) then π w else 0 := by
  show (∑ w ∈ q ∩ F.probEvent q t, π w) = _
  unfold Frame.probEvent
  rw [inter_comm, ← filter_mem_eq_inter, filter_filter, sum_filter]

/-- Mass of `[P(q) ≤ t]` as a full sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_probEventLE_eq (π : W → ℝ) (F : Frame W) (q : Finset W) (t : ℝ) :
    mass π (probEventLE F q t) = ∑ w, if mass (F.P w) q ≤ t then π w else 0 := by
  show (∑ w ∈ probEventLE F q t, π w) = _
  unfold probEventLE
  rw [sum_filter]

/-- Mass of `q ∧ [P(q) ≤ t]` as a full sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_inter_probEventLE_eq (π : W → ℝ) (F : Frame W) (q : Finset W) (t : ℝ) :
    mass π (q ∩ probEventLE F q t) =
      ∑ w, if (mass (F.P w) q ≤ t ∧ w ∈ q) then π w else 0 := by
  show (∑ w ∈ q ∩ probEventLE F q t, π w) = _
  unfold probEventLE
  rw [inter_comm, ← filter_mem_eq_inter, filter_filter, sum_filter]

/-- The restricted deferrer's mass of a threshold event, as a full sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_apply' (π : W → ℝ) (L : Finset W) (w : W) :
    Cleanroom.Corrigibility.CorrReflectFrames.restrict π L w = if w ∈ L then π w else 0 :=
  Cleanroom.Corrigibility.CorrReflectFrames.restrict_apply π L w

/-- A partial answer to a two-cell question: `answer (questionOf q) {true} = q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem answer_questionOf_true (q : Finset W) : answer (questionOf q) {true} = q := by
  ext w; simp [answer, questionOf]

/-- The complementary partial answer: `answer (questionOf q) {false} = qᶜ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem answer_questionOf_false (q : Finset W) : answer (questionOf q) {false} = qᶜ := by
  ext w; simp [answer, questionOf]

end

end Cleanroom.Corrigibility.CorrLegitGeneral
