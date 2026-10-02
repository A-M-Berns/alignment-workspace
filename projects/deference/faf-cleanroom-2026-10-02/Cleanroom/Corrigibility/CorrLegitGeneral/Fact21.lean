import Cleanroom.Corrigibility.CorrLegitGeneral.Defs
import Cleanroom.Found.LitDdbFrames.ExamplesFact21

/-!
# corr-legit-general — T11: Fact 2.1 as a shutdown counterexample

DDB's Fact 2.1 (Trust ⇏ Value) read as a shutdown problem: `O₀ ≡ 0` is *shut down*, `O₁ = (29,
−3, −13)` is *continue*; every candidate expert strictly prefers continuing (`69/10, 3/10, 3/5`),
the deferrer prefers shutting down (`−13/50`), and `lit-ddb-frames` proves `¬ Value π21 fact21`.
The Trust half of Fact 2.1 is DDB's unprinted Mathematica claim; it was stated OPEN here
(`fact21_trust_open`) and is proved in `Fact21Trust.lean` (`fact21_trust`, repair round 2) —
never cited as (b).
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

/-- **Fact 2.1 is a shutdown problem**: every candidate strictly prefers continuing, the deferrer
strictly prefers shutting down, and the deferrer does not value the frame (cited). An agent that
trusts its overseers' probabilities can rationally refuse their unanimous verdict on a
stakes-weighted question; legitimacy for the button must be Total Trust with respect to the
stakes variable.
Source: [[ddb]] I4.3 l. 119, Fact 2.1 l. 35; corr-wf13-041; `fact21_E_O1`, `fact21_not_value`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem fact21_shutdown : (∀ w, 0 < E (fact21.P w) O1) ∧ E π21 O1 < E π21 (fun _ => 0) ∧
    ¬ Value π21 fact21 := by
  obtain ⟨e0, e1, e2, eπ⟩ := fact21_E_O1
  refine ⟨fun w => ?_, ?_, fact21_not_value⟩
  · fin_cases w
    · show 0 < E (fact21.P 0) O1
      rw [e0]; norm_num
    · show 0 < E (fact21.P 1) O1
      rw [e1]; norm_num
    · show 0 < E (fact21.P 2) O1
      rw [e2]; norm_num
  · rw [eπ]; simp [E]; norm_num

/-! The Trust half of Fact 2.1 — `π21` trusts `fact21` in DDB's sense — was stated OPEN here
(`fact21_trust_open`) through repair round 1 and is proved in repair round 2 as `fact21_trust`
(`Fact21Trust.lean`): `trust_iff_attained` plus the finite table. The OPEN entry is retired. -/

end

end Cleanroom.Corrigibility.CorrLegitGeneral
