import Cleanroom.Corrigibility.CorrLegitModif.Plumbing
import Cleanroom.Corrigibility.CorrThreeStepFacts.Basic
import Cleanroom.Corrigibility.CorrReflectFrames.Selection

/-!
# corr-legit-modif — T8: deception does not break the reflection identity

[[armstrong]] item 7 ll. 91–93: "the reflection identity is not broken by deceiving the
programmers — the agent's update on their silence is a perfectly Bayesian update on a signal
whose likelihoods it has itself changed; the martingale holds. So the work is done entirely by
'`E` lowers `P_{t₁}(L)`'". Over a `ThreeStep` (`corr-three-step`), for *every* first action `a₁`
— deception being a different press kernel `press a₁` — the agent's own posterior frame
`o ↦ P(· | o; a₁)` on the joint `(ω, o)` is the Bayesian refinement of the joint along the
observation coordinate, which the joint reflects and totally trusts (`refineFrame_reflects`,
`refineFrame_totalTrust`). The `ThreeStep`-native form of the same identity is
`corr-three-step-facts`' `tower_level_set` (a T-grade anchor there).

(b) Under A0 (the prior does not depend on the act) the epistemic lift of a world event `L ⊆ Ω`
is `0` for every pair of acts (`lift_zero_of_world_event`), and the causal relation (C) sees the
agent's own posterior frame as trusted for every kernel (`selfReflects_any_act`): neither
relation can register deception. §2.11's two disjuncts therefore collapse to "lowers `P(L)`",
which needs `L` defined on the act — Armstrong's two definitions (by method; by counterfactual
default policy). Surviving neighbours in the run, cited not restated: `influenceDefect` with
`brainReader_defect_deceive = max α β / 2 > 0` and `Faking.LegitimizingFor`
(`corr-channel-voi`, `corr-general-object`); item 4 (1a makes the scan more attractive):
`brainReader_separation`.
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames
  Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω A₁ A₂ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype A₂] [DecidableEq A₂]

/-- The joint `P(ω, o; a₁) = μ_{a₁}(ω) · P(o | ω; a₁)` on `Ω × Obs`, as a deferrer on the joint
carrier.
Source: [[corr-three-step]] Setting ("The joint is `P(ω, o; a₁) = μ_{a₁}(ω) · P(o | ω; a₁)`")
Kind: D
Fidelity: exact -/
def jointObs (S : ThreeStep Ω A₁ A₂) (a : A₁) : Ω × Obs → ℝ :=
  fun p => (S.μ a).mass p.1 * S.obsWeight a p.2 p.1

/-- The joint is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem jointObs_nonneg (S : ThreeStep Ω A₁ A₂) (a : A₁) : ∀ p, 0 ≤ jointObs S a p :=
  fun p => mul_nonneg ((S.μ a).nonneg p.1) (S.obsWeight_nonneg a p.2 p.1)

/-- **The agent's own posterior frame** after `a₁`: at `(ω, o)` the row is `P(· | o; a₁)` on the
joint carrier — the Bayesian refinement of the joint along the observation coordinate.
Source: [[armstrong]] item 7 l. 91 ("the agent's update on their silence is a perfectly Bayesian
update on a signal whose likelihoods it has itself changed")
Kind: D
Fidelity: exact -/
def postFrame (S : ThreeStep Ω A₁ A₂) (a : A₁) : Frame (Ω × Obs) :=
  refineFrame (jointObs S a) (jointObs_nonneg S a) (fun p => p.2)

/-- The rows of the posterior frame at a positive-probability observation: the conditional
`P(ω', o' | o; a₁) = 𝟙[o' = o] · P(ω', o'; a₁) / P(o; a₁)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem postFrame_P (S : ThreeStep Ω A₁ A₂) (a : A₁) (p : Ω × Obs)
    (h : 0 < mass (jointObs S a) (fibre (fun q : Ω × Obs => q.2) p)) (q : Ω × Obs) :
    (postFrame S a).P p q =
      ind (fibre (fun q : Ω × Obs => q.2) p) q * jointObs S a q /
        mass (jointObs S a) (fibre (fun q : Ω × Obs => q.2) p) := by
  unfold postFrame
  rw [refineFrame_P, condRow_apply_of_pos h]

/-- **`selfReflects_any_act`**: for every first action — deception included, as a different press
kernel — the joint reflects and totally trusts the agent's own posterior frame. The reflection
identity toward oneself is untouched by what the act did to the overseers' signal.
Source: [[armstrong]] item 7 ll. 91–93; corr-wf13-2-088; `tower_level_set` (the `ThreeStep`
form)
Kind: L (cited `refineFrame_reflects`, `refineFrame_totalTrust`)
Fidelity: exact
Hyps: (a) none -/
theorem selfReflects_any_act (S : ThreeStep Ω A₁ A₂) (a : A₁) :
    Reflects (jointObs S a) (postFrame S a) ∧ TotalTrust (jointObs S a) (postFrame S a) :=
  ⟨refineFrame_reflects _ _, refineFrame_totalTrust _ _⟩

/-- **`lift_zero_of_world_event`**: under A0 the prior probability of a world event `L ⊆ Ω` is the
same after every act — the epistemic lift `λ_L(a₁) − λ_L(a₁⁻)` of S9 is `0` when the act changes
only the kernel.
Source: [[legitimacy-general-final]] S9 l. 37 ((E) epistemic lift); [[armstrong]] item 7 l. 91
Kind: T (`rw [hA0 a a']`: it holds for any functional of the prior; regraded at audit round 1)
Fidelity: exact
Hyps: (a) `S.A0` -/
theorem lift_zero_of_world_event (S : ThreeStep Ω A₁ A₂) (hA0 : S.A0) (a a' : A₁)
    (L : Finset Ω) : ∑ ω ∈ L, (S.μ a).mass ω = ∑ ω ∈ L, (S.μ a').mass ω := by
  rw [hA0 a a']

/-- **The causal relation cannot register deception toward the self-frame**: for every two acts
the agent's posterior frames are both reflected by their joints (`selfReflects_any_act` twice);
whether the act is honest or deceptive, the agent is inside the region where the reflection
identity holds toward its own successor.
Source: [[legitimacy-general-final]] S9 l. 37 ((C) causal); [[armstrong]] item 7 l. 93
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem causal_blind_to_act (S : ThreeStep Ω A₁ A₂) (a a' : A₁) :
    Reflects (jointObs S a) (postFrame S a) ∧ Reflects (jointObs S a') (postFrame S a') :=
  ⟨(selfReflects_any_act S a).1, (selfReflects_any_act S a').1⟩

end

end Cleanroom.Corrigibility.CorrLegitModif
