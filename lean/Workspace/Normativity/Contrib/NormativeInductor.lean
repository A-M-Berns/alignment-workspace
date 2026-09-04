/-
# Elementary composition lemmas for the Normative Inductor realization

These are the new algebraic bridges used by the 2026-09-04 realization report.
They deliberately do not formalize legitimacy, settlement, or decision adequacy:
those enter the realization theorem as typed hypotheses, not Lean axioms.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Workspace.Normativity.Contrib.NormativeInductor

/-- Uniform calibration plus an `η`-approximate comparison in the displayed
coordinates transfers to a `2r + η` comparison in the certified coordinates. -/
theorem approximate_argmax_transfer {Q : Type*} {b v : Q → ℝ} {qStar q : Q}
    {r η : ℝ} (hcal : ∀ x, |v x - b x| ≤ r)
    (hchoice : b qStar ≤ b q + η) :
    v qStar - v q ≤ 2 * r + η := by
  have hs := (abs_le.mp (hcal qStar)).2
  have hq := (abs_le.mp (hcal q)).1
  linarith

/-- The decision and semantic certificates compose with the constants used by
the abstract practical-response interface. -/
theorem practical_response_compose {decisionDefect operativeDefect loss C η L ε : ℝ}
    (hL : 0 ≤ L)
    (hdecision : decisionDefect ≤ C * operativeDefect + η)
    (hsemantic : loss ≤ L * decisionDefect + ε) :
    loss ≤ (L * C) * operativeDefect + (L * η + ε) := by
  calc
    loss ≤ L * decisionDefect + ε := hsemantic
    _ ≤ L * (C * operativeDefect + η) + ε := by gcongr
    _ = (L * C) * operativeDefect + (L * η + ε) := by ring

/-- Quantitative semantic transport composes in the affine-error monoid.  This
orientation means that `(L₁,ε₁)` is applied after `(L₂,ε₂)`. -/
theorem affine_transport_compose {x y z L₁ L₂ ε₁ ε₂ : ℝ}
    (hL₁ : 0 ≤ L₁)
    (hfirst : y ≤ L₂ * x + ε₂)
    (hsecond : z ≤ L₁ * y + ε₁) :
    z ≤ (L₁ * L₂) * x + (ε₁ + L₁ * ε₂) := by
  calc
    z ≤ L₁ * y + ε₁ := hsecond
    _ ≤ L₁ * (L₂ * x + ε₂) + ε₁ := by gcongr
    _ = (L₁ * L₂) * x + (ε₁ + L₁ * ε₂) := by ring

/-- Exact carry, used for a pure challenge/defeat disposition, is the identity
of affine transport. -/
theorem exact_carry_left {x y L ε : ℝ} (h : y ≤ L * x + ε) :
    y ≤ (1 * L) * x + (0 + 1 * ε) := by
  simpa using h

#print axioms approximate_argmax_transfer
#print axioms practical_response_compose
#print axioms affine_transport_compose
#print axioms exact_carry_left

end Workspace.Normativity.Contrib.NormativeInductor
