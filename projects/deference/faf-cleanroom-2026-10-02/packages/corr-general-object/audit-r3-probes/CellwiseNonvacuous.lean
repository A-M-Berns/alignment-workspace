import Cleanroom.Corrigibility.CorrGeneralObject.ActAdopt

/-!
# Audit r3 (adversarial) probe — `CellwiseAct` never quantifies over an empty set

`CellwiseAct P F V` and "Value on the menu" both begin `∀ S, F.Recommended (menuOf V) S → …`.
If no strategy were recommended on `menuOf V` for some frame, T7(b)'s conclusion
(`cellwiseAct_of_value`) would be vacuous there. `lit-ddb-frames`' informed strategy is
recommended on every nonempty menu, and `menuOf V` is nonempty for a nonempty `A`, so the
quantifier is inhabited for *every* frame and menu — not only on the package's Example A
instance (`exA_S_recommended`).

Not imported by the library. Namespace `…AuditR3`.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject.AuditR3

open FactoredSpaces Cleanroom.Found.LitDdbFrames
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]

theorem menuOf_nonempty (V : A → Ω → ℝ) : (menuOf V).Nonempty :=
  Finset.univ_nonempty.image V

/-- For every frame and every menu a recommended strategy exists. -/
theorem exists_recommended (F : Frame Ω) (V : A → Ω → ℝ) :
    ∃ S, F.Recommended (menuOf V) S :=
  ⟨_, F.informedStrategy_recommended (menuOf V) (menuOf_nonempty V)⟩

end

end Cleanroom.Corrigibility.CorrGeneralObject.AuditR3
