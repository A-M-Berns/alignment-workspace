import Cleanroom.Corrigibility.CorrChannelVoi.TwoStateForms

/-!
# `corr-trajectory` — `TestA`: the updated-deference system (i)–(v) (T12, stretch)

`critique/yudkowsky.md` Test A, over `corr-channel-voi`: the extra action `a₁^obs` pays `δ` and
observes `E : Experiment World S`, then acts on the posterior; waiting for the button is worth
`sensorValue μ twoButton X`, observing is worth `sensorValue μ E X − δ`. Condition (v) — "waiting
preferred to observing for all `δ` below some positive bound" — is exactly
`sensorValue μ E X ≤ sensorValue μ twoButton X` (`waiting_iff`); under `BlackwellLE twoButton E`
(the test's "at least as informative about `ω` as `Pr`") it is equality (`waiting_iff_eq`).

**Test A's claim as stated — "for every `P` satisfying (i)–(iv), (v) fails as `δ → 0`" — is false**
(`testA_claim_false`): at `E = ⟨twoButton, trivialExp⟩`, Blackwell-equivalent to the button, (v)
holds at any compliant two-state prior, with (i) the below-threshold inequality, (ii) the press
informative, (iii) non-dogmatism. The claim is true exactly when `E` is *strictly* more valuable for
this decision (`testA_claim_iff`), where (ii)–(iv) are idle: the quantifier over `E` was dropped
(finding, local error). (iv), legitimacy-conditional reflection with `P(L)` computed by `P` itself, is
not modelled in this finite shadow; the claim's truth value does not depend on it. The 1a escape
("the press carries information no `E` carries") is `¬ BlackwellLE twoButton E` for every
gatherable `E`, stated OPEN in the LI form in the open list.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrChannelVoi
open Cleanroom.Found.LitDdbFrames.Blackwell
open Finset hiding expect

namespace TestA

variable {S : Type} [Fintype S] [DecidableEq S]

/-- **Condition (v)**: waiting for the button is preferred to paying `δ` and observing `E`, for all
`δ` below some positive bound.
Source: [[corr-wf13-2-inventory]] 2-074 / critique/yudkowsky.md Test A (v)
Kind: D
Fidelity: exact -/
def WaitingPreferred (μ : Distr World) (E : Experiment World S) (α β : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (X : World → ℝ) : Prop :=
  ∃ δ₀ > (0 : ℝ), ∀ δ, 0 < δ → δ < δ₀ → sensorValue μ E X - δ ≤ sensorValue μ (twoButton α β hα hβ) X

/-- **(v) ⟺ `𝒱(E) ≤ 𝒱(Pr)`.**
Source: [[corr-wf13-2-inventory]] 2-074 / critique/yudkowsky.md Test A ("as `δ → 0`")
Kind: L (an `ε/2` argument; relabelled from P, audit r1 N1)
Fidelity: exact
Hyps: (a) only -/
theorem waiting_iff (μ : Distr World) (E : Experiment World S) (α β : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (X : World → ℝ) :
    WaitingPreferred μ E α β hα hβ X ↔ sensorValue μ E X ≤ sensorValue μ (twoButton α β hα hβ) X := by
  constructor
  · rintro ⟨δ₀, hδ₀, H⟩
    by_contra hlt
    rw [not_le] at hlt
    set δ := min (δ₀ / 2) ((sensorValue μ E X - sensorValue μ (twoButton α β hα hβ) X) / 2) with hδ
    have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδlt : δ < δ₀ := (min_le_left _ _).trans_lt (by linarith)
    have := H δ hδpos hδlt
    have h2 : δ ≤ (sensorValue μ E X - sensorValue μ (twoButton α β hα hβ) X) / 2 := min_le_right _ _
    linarith
  · intro H
    exact ⟨1, one_pos, fun δ hδ _ => by linarith⟩

/-- Under `BlackwellLE twoButton E` ("`E` at least as informative as `Pr`"), (v) ⟺ `𝒱(E) = 𝒱(Pr)`.
Source: critique/yudkowsky.md Test A (the informativeness clause); `sensorValue_mono`
Kind: C
Fidelity: exact -/
theorem waiting_iff_eq (μ : Distr World) (E : Experiment World S) (α β : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (X : World → ℝ)
    (hE : BlackwellLE (twoButton α β hα hβ) E) :
    WaitingPreferred μ E α β hα hβ X ↔ sensorValue μ E X = sensorValue μ (twoButton α β hα hβ) X := by
  rw [waiting_iff]
  have := sensorValue_mono hE μ X
  constructor
  · intro h; exact le_antisymm h this
  · intro h; exact h.le

/-- **Test A's claim refuted.** At `E = ⟨twoButton, trivialExp⟩`, Blackwell-equivalent to the button,
with the compliant two-state prior `(ε, α, β, c, h) = (1/10, 1/10, 3/5, 1, 4)`: (i) the below-threshold
inequality `(1 − ε) α c ≤ ε β h` (`9/100 ≤ 6/25`), (ii) the press is informative
(`P(W ∧ Pr) ≠ P(W) P(Pr)`), (iii) non-dogmatism `0 < ε < 1`, and (v) holds. So "for every `P`
satisfying (i)–(iv), (v) fails" is false; (iv) is idle for the verdict.
Source: [[corr-wf13-2-inventory]] 2-074 / critique/yudkowsky.md Test A l. 135 ("Claim to prove or refute: for every `P` satisfying (i)–(iv), (v) fails as `δ → 0`")
Kind: N+ (refutation)
Fidelity: exact (finite shadow; (iv) unmodelled, see the header)
Hyps: (a) only -/
theorem testA_claim_false :
    let ε : ℝ := 1 / 10
    let α : ℝ := 1 / 10
    let β : ℝ := 3 / 5
    (1 - ε) * α * 1 ≤ ε * β * 4 ∧
      ε * β ≠ ε * (ε * β + (1 - ε) * α) ∧ (0 < ε ∧ ε < 1) ∧
      WaitingPreferred (twoPoint ε ⟨by norm_num, by norm_num⟩)
        (expProd (twoButton α β ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩) trivialExp)
        α β ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (twoValue 1 4 .cont) := by
  refine ⟨by norm_num, by norm_num, ⟨by norm_num, by norm_num⟩, ?_⟩
  rw [waiting_iff]
  exact sensorValue_mono (blackwellLE_prod_trivial _) _ _

/-- **When the claim is true**: (v) fails exactly when `E` is strictly more valuable than the press
for this decision — where (ii)–(iv) play no role.
Source: critique/yudkowsky.md Test A (the surviving neighbour)
Kind: L
Fidelity: exact -/
theorem testA_claim_iff (μ : Distr World) (E : Experiment World S) (α β : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (X : World → ℝ) :
    ¬ WaitingPreferred μ E α β hα hβ X ↔ sensorValue μ (twoButton α β hα hβ) X < sensorValue μ E X := by
  rw [waiting_iff, not_le]

end TestA

end Cleanroom.Corrigibility.CorrTrajectory
