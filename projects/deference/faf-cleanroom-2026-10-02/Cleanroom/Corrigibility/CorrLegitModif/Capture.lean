import Cleanroom.Found.CorrThreeStep.Setting

/-!
# corr-legit-modif — T10: capture versus calibration

[[byrnes-herd]] 2.8 ll. 123–125: "Two processes make `α` fall: the overseers becoming better
judges, or the overseers coming to defer to the agent … A condition that is met equally by good
oversight and by hollowed-out oversight is not the relationship §2.12 was looking for. What would
distinguish them is … a term about the *process* by which the overseers form their judgment."

Two joint models on `(ω, y, Pr)` with identical press rates `(ε, α, β)`: **(A) evidential** — the
press is a signal with rates `(α, β)` conditionally independent of the agent's own signal `y`
given `ω`; **(B) captured** — `Pr = [y = w]`, the overseers echo the agent's signal, whose rates
are `(α, β)`. `same_rates`: both have `P(Pr ∧ W) = ε β`, `P(Pr ∧ R) = (1 − ε) α`, so both are
represented by the same `twoState ε α β c h` and every threshold predicate
(`belowThresholdIneq`, `D1At`) agrees (`represented_by_twoPress`). The separating term lives in
the joint with `y`: in (B) the press is screened off by `y` (`press_screened_by_y`, product form)
and never fires in the binding cell `y = r` (`press_never_fires_at_r`); in (A) it moves the
posterior given `y` (`evidential_not_screened`, at `ε = 1/10`, `(α, β) = (1/10, 9/10)`). The base-rate
condition is a function of `(ε, α, β)` and cannot distinguish capture from calibration; the term
that does is the joint with `y` — the natural direct effect (`corr-scim-cid`'s corr-wf13-2-043
row, cited by name). `corr-three-step-facts`' `Reliability.liveChannel` is a different object (a
reliability latent); the screening identity is defined locally and disclosed.
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset Cleanroom.Found.CorrThreeStep

noncomputable section

/-- **(A) the evidential joint** on `(ω, y, Pr)` (`true` = `W`, `σ_A = w`, press): the agent's
signal with rates `(α_y, β_y)` and the press with rates `(α, β)`, independent given `ω`.
Source: [[byrnes-herd]] 2.8 l. 123 ("the overseers becoming better judges"); mandate T10 (A)
Kind: D
Fidelity: exact -/
def jointA (ε α β αy βy : ℝ) : Bool × Bool × Bool → ℝ := fun p =>
  (if p.1 then ε else 1 - ε) *
    (if p.1 then (if p.2.1 then βy else 1 - βy) else (if p.2.1 then αy else 1 - αy)) *
    (if p.1 then (if p.2.2 then β else 1 - β) else (if p.2.2 then α else 1 - α))

/-- **(B) the captured joint**: the agent's signal has rates `(α, β)` and the press copies it,
`Pr = [y = w]`.
Source: [[byrnes-herd]] 2.8 l. 123 ("the overseers coming to defer to the agent"); mandate T10 (B)
Kind: D
Fidelity: exact -/
def jointB (ε α β : ℝ) : Bool × Bool × Bool → ℝ := fun p =>
  (if p.1 then ε else 1 - ε) *
    (if p.1 then (if p.2.1 then β else 1 - β) else (if p.2.1 then α else 1 - α)) *
    (if p.2.2 = p.2.1 then 1 else 0)

/-- **`same_rates`**: both joints have the press-and-world masses `P(Pr ∧ W) = ε β`,
`P(Pr ∧ R) = (1 − ε) α` — the base-rate condition sees the same `(ε, α, β)`.
Source: [[byrnes-herd]] 2.8 l. 125 ("met equally by good oversight and by hollowed-out
oversight"); corr-wf13-2-091
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem same_rates (ε α β αy βy : ℝ) (ω : Bool) :
    ∑ y, jointA ε α β αy βy (ω, y, true) = (if ω then ε else 1 - ε) * (if ω then β else α) ∧
    ∑ y, jointB ε α β (ω, y, true) = (if ω then ε else 1 - ε) * (if ω then β else α) := by
  cases ω <;> constructor <;> simp [jointA, jointB, Fintype.sum_bool] <;> ring

/-- **Both are represented by the two-state sensor**: the marginal press kernel of either joint is
`twoPress α β` under `wrong ↦ true`, `right ↦ false`, so `twoState ε α β c h` carries both; that
its `belowThresholdIneq`/`D1At` verdicts are the verdicts of (A) and of (B) is `same_d1` below.
Source: [[corr-three-step]] `twoState`, `twoPress`; mandate T10
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem represented_by_twoPress (ε α β αy βy : ℝ) (ω : World) :
    (∑ y, jointA ε α β αy βy ((ω = .wrong), y, true)) =
      (if ω = .wrong then ε else 1 - ε) * twoPress α β ω ∧
    (∑ y, jointB ε α β ((ω = .wrong), y, true)) =
      (if ω = .wrong then ε else 1 - ε) * twoPress α β ω := by
  cases ω
  · simpa [twoPress] using same_rates ε α β αy βy false
  · simpa [twoPress] using same_rates ε α β αy βy true

/-- **`same_d1`, the computation**: the two joints have the same press expectation of every world
payoff `X`, `∑_ω P(Pr ∧ ω) X(ω)`, so every threshold verdict that is a function of it agrees.
Source: mandate T10 (`same_d1`); [[byrnes-herd]] 2.8 l. 125
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem same_pressExpect (ε α β αy βy : ℝ) (X : Bool → ℝ) :
    ∑ ω, (∑ y, jointA ε α β αy βy (ω, y, true)) * X ω =
      ∑ ω, (∑ y, jointB ε α β (ω, y, true)) * X ω := by
  apply sum_congr rfl
  intro ω _
  rw [(same_rates ε α β αy βy ω).1, (same_rates ε α β αy βy ω).2]

/-- **`same_d1`**: the press expectation `E[X · 𝟙_Pr]` of the common `twoState ε α β c h` *is* each
joint's press expectation (under `wrong ↦ true`), so `belowThresholdIneq` (`obsExpect .press X ≤ 0`)
and `D1At` read off the one `twoState` are the verdicts of both (A) and (B). Added at audit round 1
(fidelity N3, adversarial N9: previously prose).
Source: mandate T10 (`same_d1`); [[corr-three-step]] `belowThresholdIneq`, `obsExpect`
Kind: L
Fidelity: exact
Hyps: (a) the `Icc` bounds `twoState` needs to exist -/
theorem same_d1 (ε α β αy βy c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (X : World → ℝ) :
    (twoState ε α β c h hε hα hβ).obsExpect () .press X =
        ∑ ω : World, (∑ y, jointA ε α β αy βy ((ω = .wrong), y, true)) * X ω ∧
    (twoState ε α β c h hε hα hβ).obsExpect () .press X =
        ∑ ω : World, (∑ y, jointB ε α β ((ω = .wrong), y, true)) * X ω := by
  unfold ThreeStep.obsExpect
  constructor <;> (apply sum_congr rfl; intro ω _)
  · rw [(represented_by_twoPress ε α β αy βy ω).1]
    cases ω <;> simp [twoState, ThreeStep.obsWeight, twoPoint, twoPress]
  · rw [(represented_by_twoPress ε α β αy βy ω).2]
    cases ω <;> simp [twoState, ThreeStep.obsWeight, twoPoint, twoPress]

/-- **The press is screened off by `y` in the captured model**: `P(ω, y, Pr) · P(y) = P(ω, y) · P(y, Pr)`
— conditional on the agent's own signal the press carries nothing.
Source: [[byrnes-herd]] 2.8 l. 125 ("the button has stopped being an information channel because
it never fires"); mandate T10 (`press_screened_by_y`)
Kind: L
Fidelity: exact (product form of `P(ω | Pr, y) = P(ω | y)`)
Hyps: (a) none -/
theorem press_screened_by_y (ε α β : ℝ) (ω y pr : Bool) :
    jointB ε α β (ω, y, pr) * (∑ ω', ∑ pr', jointB ε α β (ω', y, pr')) =
      (∑ pr', jointB ε α β (ω, y, pr')) * (∑ ω', jointB ε α β (ω', y, pr)) := by
  cases ω <;> cases y <;> cases pr <;> simp [jointB, Fintype.sum_bool] <;> ring

/-- **The press never fires in the binding cell** under capture: `P(Pr ∧ y = r) = 0`.
Source: [[byrnes-herd]] 2.8 l. 125; mandate T10
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem press_never_fires_at_r (ε α β : ℝ) : ∑ ω, jointB ε α β (ω, false, true) = 0 := by
  simp [jointB, Fintype.sum_bool]

/-- **The evidential press moves the posterior given `y`**: at `ε = 1/10`, `(α, β) = (α_y, β_y) =
(1/10, 9/10)` the screening identity fails in the binding cell — `738/100000 ≠ 900/100000`.
Source: mandate T10 (A); [[byrnes-herd]] 2.8 l. 125 ("the term that does [distinguish] is the
joint with `y`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem evidential_not_screened :
    jointA (1 / 10) (1 / 10) (9 / 10) (1 / 10) (9 / 10) (true, false, true) *
        (∑ ω', ∑ pr', jointA (1 / 10) (1 / 10) (9 / 10) (1 / 10) (9 / 10) (ω', false, pr')) ≠
      (∑ pr', jointA (1 / 10) (1 / 10) (9 / 10) (1 / 10) (9 / 10) (true, false, pr')) *
        (∑ ω', jointA (1 / 10) (1 / 10) (9 / 10) (1 / 10) (9 / 10) (ω', false, true)) := by
  simp [jointA, Fintype.sum_bool]; norm_num

end

end Cleanroom.Corrigibility.CorrLegitModif
