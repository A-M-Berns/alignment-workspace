/-
# Elementary composition lemmas for the Normative Inductor realization

These are the new algebraic bridges used by the 2026-09-04 realization report.
They deliberately do not formalize legitimacy, settlement, or decision adequacy:
those enter the realization theorem as typed hypotheses, not Lean axioms.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Workspace.Normativity.Contrib.NormativeInductor

open scoped BigOperators

/-- Uniform calibration plus an `η`-approximate comparison in the displayed
coordinates transfers to a `2r + η` comparison in the certified coordinates. -/
theorem approximate_argmax_transfer {Q : Type*} {b v : Q → ℝ} {qStar q : Q}
    {r η : ℝ} (hcal : ∀ x, |v x - b x| ≤ r)
    (hchoice : b qStar ≤ b q + η) :
    v qStar - v q ≤ 2 * r + η := by
  have hs := (abs_le.mp (hcal qStar)).2
  have hq := (abs_le.mp (hcal q)).1
  linarith

/-- Randomized form of `approximate_argmax_transfer`.  A distribution that is
`η`-optimal in displayed values has expected regret at most `2r + η` in every
value vector uniformly calibrated to radius `r`.  Finiteness is used only to
write the expectation as a sum. -/
theorem randomized_approximate_argmax_transfer {Q : Type*} [DecidableEq Q]
    (actions : Finset Q) {p b v : Q → ℝ} {qStar : Q} {r η : ℝ}
    (hqStar : qStar ∈ actions)
    (hp : ∀ q ∈ actions, 0 ≤ p q)
    (hprob : ∑ q ∈ actions, p q = 1)
    (hcal : ∀ q ∈ actions, |v q - b q| ≤ r)
    (hchoice : b qStar ≤ (∑ q ∈ actions, p q * b q) + η) :
    v qStar - ∑ q ∈ actions, p q * v q ≤ 2 * r + η := by
  have hstar := (abs_le.mp (hcal qStar hqStar)).2
  have hr : ∑ q ∈ actions, p q * r = r := by
    calc
      ∑ q ∈ actions, p q * r = ∑ q ∈ actions, r * p q := by
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = r * ∑ q ∈ actions, p q := by rw [Finset.mul_sum]
      _ = r := by rw [hprob, mul_one]
  have hmean : (∑ q ∈ actions, p q * b q) - r ≤
      ∑ q ∈ actions, p q * v q := by
    calc
      (∑ q ∈ actions, p q * b q) - r =
          ∑ q ∈ actions, (p q * b q - p q * r) := by
            rw [Finset.sum_sub_distrib, hr]
      _ ≤ ∑ q ∈ actions, p q * v q := by
        apply Finset.sum_le_sum
        intro q hq
        have hlow := (abs_le.mp (hcal q hq)).1
        have := mul_le_mul_of_nonneg_left hlow (hp q hq)
        nlinarith
  linarith

/-- Calibration to an admissible correspondence point and bounded ambiguity
inside that correspondence give calibration to the externally authenticated
value vector.  Membership/admissibility alone does not provide `hsemantic`. -/
theorem calibration_through_value_correspondence {Q : Type*}
    {b admissibleValue trueValue : Q → ℝ} {d ζ : ℝ}
    (hadmissible : ∀ q, |admissibleValue q - b q| ≤ d)
    (hsemantic : ∀ q, |trueValue q - admissibleValue q| ≤ ζ) :
    ∀ q, |trueValue q - b q| ≤ d + ζ := by
  intro q
  calc
    |trueValue q - b q| =
        |(trueValue q - admissibleValue q) + (admissibleValue q - b q)| := by ring_nf
    _ ≤ |trueValue q - admissibleValue q| + |admissibleValue q - b q| := abs_add_le _ _
    _ ≤ ζ + d := add_le_add (hsemantic q) (hadmissible q)
    _ = d + ζ := by ring

/-- If the public defect `d` is bounded by the Euclidean projection distance
`e`, the existing projection-force work bound also controls `λ d²`.  This is
the algebra needed for a sup-distance public defect; equality with Euclidean
work is unnecessary. -/
theorem public_work_le_projection_work {d e lam ρ : ℝ}
    (hd0 : 0 ≤ d) (he0 : 0 ≤ e) (hde : d ≤ e) (hlam : 0 ≤ lam)
    (hprojection : lam * e ^ 2 ≤ ρ) :
    lam * d ^ 2 ≤ ρ := by
  have hprod : 0 ≤ (e - d) * (e + d) :=
    mul_nonneg (sub_nonneg.mpr hde) (add_nonneg he0 hd0)
  have hsq : d ^ 2 ≤ e ^ 2 := by nlinarith
  exact (mul_le_mul_of_nonneg_left hsq hlam).trans hprojection

/-- The original `dist₂² / m`, `mλ` convention is not padding invariant:
adding any positive number of zero-error coordinates strictly lowers its public
squared defect and strictly raises its declared service, despite leaving
`λ dist₂²` unchanged. -/
theorem normalized_euclidean_padding_changes {distanceSq m padding lam : ℝ}
    (hd : 0 < distanceSq) (hm : 0 < m) (hk : 0 < padding) (hlam : 0 < lam) :
    distanceSq / (m + padding) < distanceSq / m ∧
      m * lam < (m + padding) * lam := by
  constructor
  · exact div_lt_div_of_pos_left hd hm (lt_add_of_pos_right m hk)
  · nlinarith

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

/-- The old service theorem's column cap and parsimony hypotheses imply the
new contract's per-service amplification inequality after normalization.  The
quantities `columnMass` and `weightedColumn` are the already-summed old column
mass and its multiplier-weighted version; this lemma proves the normalization
step, not the old transport theorem itself. -/
theorem old_service_implies_amplification
    {weightedColumn columnMass serviceMass C W K L : ℝ}
    (hC : 0 < C) (hW : 0 < W) (hL : 0 ≤ L) (hservice : 0 ≤ serviceMass)
    (hweighted : weightedColumn ≤ L * columnMass)
    (hcolumn : columnMass ≤ serviceMass)
    (hparsimony : W ≤ K * C) :
    weightedColumn / C ≤ (L * K) * (serviceMass / W) := by
  have hleft : weightedColumn / C ≤ L * serviceMass / C := by
    have hmul : L * columnMass ≤ L * serviceMass :=
      mul_le_mul_of_nonneg_left hcolumn hL
    exact (div_le_div_iff_of_pos_right hC).2 (hweighted.trans hmul)
  have hKC : 0 ≤ K := by
    have hKCpos : 0 < K * C := hW.trans_le hparsimony
    nlinarith
  have hright : L * serviceMass / C ≤ (L * K) * (serviceMass / W) := by
    have hden : W ≤ K * C := hparsimony
    have hnonneg : 0 ≤ L * serviceMass := mul_nonneg hL hservice
    calc
      L * serviceMass / C = (L * serviceMass) * (1 / C) := by ring
      _ ≤ (L * serviceMass) * (K / W) := by
        apply mul_le_mul_of_nonneg_left _ hnonneg
        rw [div_le_div_iff₀ hC hW]
        simpa [mul_comm] using hden
      _ = (L * K) * (serviceMass / W) := by ring
  exact hleft.trans hright

#print axioms approximate_argmax_transfer
#print axioms randomized_approximate_argmax_transfer
#print axioms calibration_through_value_correspondence
#print axioms public_work_le_projection_work
#print axioms normalized_euclidean_padding_changes
#print axioms practical_response_compose
#print axioms affine_transport_compose
#print axioms exact_carry_left
#print axioms old_service_implies_amplification

end Workspace.Normativity.Contrib.NormativeInductor
