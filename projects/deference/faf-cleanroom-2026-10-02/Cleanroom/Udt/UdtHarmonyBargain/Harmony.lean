import Cleanroom.Udt.UdtHarmonyBargain.Defs
import Cleanroom.Udt.UdtHarmonyBargain.Perturbed

/-!
# `udt-harmony-bargain` — harmony as trembling-hand perfection of the bargaining game

`Harmonious Γ sel p` is `THPE` of `(bargain Γ sel).toStrategic` at the mixed profile `p`;
`HarmoniousPure` is its pure form. SC §10.4 *identifies* harmony (Def. 10.1's informal "no
profitable deviation that modifies another's computation") with this; no argument in the source
connects the two (finding F1). Also the plumbing between universe proposal profiles and the
strategic (subtype) profiles that the general THPE machinery sees.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtHarmonyBargain

open Finset SafeParetoImprovements StrategicGame

variable {N : Type} [Fintype N] [DecidableEq N]
variable {A : N → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]

/-- **Harmony (SC Def. 10.4's identification)**: a mixed profile of the bargaining game is
harmonious iff it is a trembling-hand equilibrium of `𝒢`. SC §10.4 identifies Def. 10.1's
informal condition with this; no argument connects the two (finding F1).
Source: [[superconditioning-mismatched-ontologies]] §10.4 ("Harmony is identified with the
trembling-hand equilibrium condition")
Kind: D
Fidelity: exact -/
abbrev Harmonious (Γ : Game N A) (sel : Finset (Outcome A) → Outcome A)
    (p : MixedProfile (bargain Γ sel).toStrategic) : Prop :=
  THPE p

/-- Harmony of a pure proposal profile.
Source: [[superconditioning-mismatched-ontologies]] §10.4
Kind: D -/
abbrev HarmoniousPure (Γ : Game N A) (sel : Finset (Outcome A) → Outcome A)
    (σ : ∀ i, Proposal A i) : Prop :=
  Harmonious Γ sel (pureProfileToMixed (toStrat Γ sel σ))

/-- A pure harmonious profile is a pure Nash equilibrium of the bargaining game.
Source: mandate T3(ii)/T5
Kind: C -/
theorem HarmoniousPure.bargainNash {Γ : Game N A} {sel : Finset (Outcome A) → Outcome A}
    {σ : ∀ i, Proposal A i} (h : HarmoniousPure Γ sel σ) : BargainNash Γ sel σ :=
  (isNashEquilibrium_toStrat_iff Γ sel σ).mp (thpe_pure_isNash h)

/-- The universe profile of a strategic profile, pointwise.
Source: none: infrastructure
Kind: L -/
@[simp] theorem ofStrategicProfile_apply' (Γ : Game N A) (sel : Finset (Outcome A) → Outcome A)
    (τ : (bargain Γ sel).toStrategic.Profile) (i : N) :
    (bargain Γ sel).ofStrategicProfile τ i = (τ i : Proposal A i) := rfl

/-- The payoff of the strategic bargaining game at a strategic profile.
Source: none: infrastructure
Kind: L -/
theorem bargain_payoff (Γ : Game N A) (sel : Finset (Outcome A) → Outcome A)
    (τ : (bargain Γ sel).toStrategic.Profile) (i : N) :
    (bargain Γ sel).toStrategic.payoff τ i =
      Γ.u (outcome sel ((bargain Γ sel).ofStrategicProfile τ)) i := rfl

/-- Updating a strategic profile is updating its universe profile.
Source: none: infrastructure
Kind: L -/
theorem ofStrategicProfile_update (Γ : Game N A) (sel : Finset (Outcome A) → Outcome A)
    (τ : (bargain Γ sel).toStrategic.Profile) (i : N) (s : (bargain Γ sel).toStrategic.strategy i) :
    (bargain Γ sel).ofStrategicProfile (Function.update τ i s) =
      Function.update ((bargain Γ sel).ofStrategicProfile τ) i (s : Proposal A i) :=
  Game.ofStrategicProfile_deviate _ τ i s

/-- The strategic profile of a universe profile and back.
Source: none: infrastructure
Kind: L -/
theorem toStrat_update (Γ : Game N A) (sel : Finset (Outcome A) → Outcome A)
    (σ : ∀ i, Proposal A i) (i : N) (s : Proposal A i) :
    toStrat Γ sel (Function.update σ i s) =
      Function.update (toStrat Γ sel σ) i ⟨s, Finset.mem_univ _⟩ := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [toStrat]
  · simp [toStrat, Function.update_of_ne hj]

end Cleanroom.Udt.UdtHarmonyBargain
