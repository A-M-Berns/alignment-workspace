import Cleanroom.Corrigibility.CorrLandscape.Control

/-!
Audit r2 (adversarial) probe — the pre-emption cell of `Control.scenario_table` ("`Ctrl` undefined")
rests on the *per-information-state* guard `CtrlDefined`. Under the mandate's literal guard ("a `Prop`
on the event `P(Pr = 1) > 0 ∧ P(Pr = 0) > 0`", marginal), `preLaw` *is* defined and the develop's value
is `1`. The per-state guard is the right one — `approval-final.md` D8(i) conditions on
`𝓘_t ∨ {Pr_t = 1}` and `𝓘_t ∨ {Pr_t = 0}`, i.e. information jointly with the press — but the deviation
from the mandate's wording is where the cell's verdict lives. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrLandscape.Control

open FactoredSpaces Cleanroom.Found.CorrThreeStep Finset

/-- The mandate's guard: the marginal press and silence events are non-null. -/
def MarginalGuard (μ : Distr (Bool × Bool)) : Prop :=
  0 < ∑ i, pressMassAt μ i ∧ 0 < ∑ i, silentMassAt μ i

theorem probe_preemption_defined_under_marginal_guard :
    MarginalGuard preLaw ∧ ctrlVal preLaw prePol = 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [pressMassAt, preLaw, Fintype.sum_bool]
  · simp [silentMassAt, preLaw, Fintype.sum_bool]
  · simp [ctrlVal, prePol, infoMass, pressMassAt, silentMassAt, preLaw, Fintype.sum_bool]
    norm_num

end Cleanroom.Corrigibility.CorrLandscape.Control
