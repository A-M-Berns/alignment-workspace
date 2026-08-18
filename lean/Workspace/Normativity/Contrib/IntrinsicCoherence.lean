/-
# Force with an intrinsic target

`EnforcementStrategy.rowViolation_le_of_intensity_ge` bounds every *displayed* row's
violation.  `CoherenceModulus` says when that is a statement about the region rather
than about the presentation.  This file composes them, so that the force guarantee
reads

    there is an admissible credence whose expectations are within `δ` of the
    displayed prices, in every priced coordinate

rather than "each row of this list is violated by at most `δ`".

The composition needs the presentation's rows to be *support-function* rows — each
right-hand side read off the worlds — and the family to be distance-complete.  For
the exact dual-distance family of a rational polytope both hold; the round proves
that on paper and verifies it exhaustively over rational grids in
`tests/test_coherence.py`, and it is the one link in this arc that is not
kernel-checked.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.CoherenceModulus
import Workspace.Normativity.Contrib.EnforcementStrategy

namespace Workspace.Normativity.Contrib.IntrinsicCoherence

open LogicalInduction
open Workspace.Normativity.Contrib.TraderizedEnforcement
open Workspace.Normativity.Contrib.CoherenceModulus
open Workspace.Normativity.Contrib.EnforcementStrategy

variable {ι : Type*}

/-- A presentation is a **support-function presentation** for a lower envelope when
every row's right-hand side is that envelope at the row's normal. -/
def IsSupportPresentation (pres : Presentation) (low : (Sentence → ℚ) → ℚ) : Prop :=
  ∀ i : Fin pres.rows.length, pres.rhss i = low (pres.normals i)

/-- The presentation's coefficient vectors, as the net the modulus is stated over.
A `Set`, not a `Finset`: it is only ever a membership test in a hypothesis, and
coefficient vectors are functions, which carry no decidable equality. -/
def presentationNet (pres : Presentation) : Set (Sentence → ℚ) :=
  Set.range pres.normals

lemma gap_le_of_rowViolation_le (pres : Presentation) (low : (Sentence → ℚ) → ℚ)
    (hsupp : IsSupportPresentation pres low) (p : Sentence → ℚ) (δ : ℚ)
    (hconf : ∀ i : Fin pres.rows.length, pres.rowViolation i p ≤ δ)
    (c : Sentence → ℚ) (hc : c ∈ presentationNet pres) :
    gap pres.coords low p c ≤ δ := by
  simp only [presentationNet, Set.mem_range] at hc
  obtain ⟨i, rfl⟩ := hc
  have h := hconf i
  unfold Presentation.rowViolation violation at h
  have hle : pres.rhss i - pair pres.coords (pres.normals i) p ≤ δ :=
    le_trans (le_max_right 0 _) h
  unfold gap
  rw [← hsupp i]
  exact hle

/-- **The intrinsic force theorem.**  Per-row conformance at `δ` under a
distance-complete support-function presentation says that some admissible credence
is within `δ` of the displayed prices in every priced coordinate — which is the
sup-norm distance statement, with no mesh and no presentation-dependent constant. -/
theorem exists_credence_of_rowViolation_le (pres : Presentation)
    (worlds : Finset ι) (Wld : ι → Sentence → ℚ) (low : (Sentence → ℚ) → ℚ)
    (hsupp : IsSupportPresentation pres low)
    (hcomplete : DistanceComplete pres.coords worlds Wld low (presentationNet pres))
    (p : Sentence → ℚ) (δ : ℚ) (hδ : 0 ≤ δ)
    (hconf : ∀ i : Fin pres.rows.length, pres.rowViolation i p ≤ δ) :
    ∃ μ : ι → ℚ, IsCredence worlds μ ∧
      ∀ φ ∈ pres.coords, |mixture worlds Wld μ φ - p φ| ≤ δ :=
  exists_credence_of_conformance pres.coords worlds Wld low (presentationNet pres)
    hcomplete p δ hδ (gap_le_of_rowViolation_le pres low hsupp p δ hconf)

/-- **From the market maker's contract to an admissible credence.**  The whole force
chain in one statement: the contract on the aggregate plus a bound on the ordinary
aggregate's opposing value plus an intensity floor on every row gives a credence
whose expectations track the displayed prices to `δ`.

`0 < ε + M` is the hypothesis `rowViolation_le_of_intensity_ge` needs and the source
market supplies, since the market maker's slack is strictly positive at every
date. -/
theorem exists_credence_of_contract (pres : Presentation) (n : ℕ)
    (Q : ℕ → Sentence → ℚ) (x τ : Sentence → ℚ) (ε M δ : ℚ)
    (worlds : Finset ι) (Wld : ι → Sentence → ℚ) (low : (Sentence → ℚ) → ℚ)
    (hsupp : IsSupportPresentation pres low)
    (hcomplete : DistanceComplete pres.coords worlds Wld low (presentationNet pres))
    (hδ : 0 < δ) (hEM : 0 < ε + M)
    (hx : ∀ i ∈ pres.rowIndex, pres.rhss i ≤ pair pres.coords (pres.normals i) x)
    (hcontract : pair pres.coords
      (fun φ => pres.compiledPosition (Q n) φ + τ φ) (fun φ => x φ - Q n φ) ≤ ε)
    (hτ : -M ≤ pair pres.coords τ (fun φ => x φ - Q n φ))
    (hβ : ∀ i : Fin pres.rows.length, (ε + M) / δ ^ 2 ≤ pres.intensities i) :
    ∃ μ : ι → ℚ, IsCredence worlds μ ∧
      ∀ φ ∈ pres.coords, |mixture worlds Wld μ φ - Q n φ| ≤ δ := by
  have hbound := weighted_square_le_slack_add_volume_at_strategy pres n Q x τ ε M
    hx hcontract hτ
  have hconf : ∀ i : Fin pres.rows.length, pres.rowViolation i (Q n) ≤ δ := fun i =>
    rowViolation_le_of_intensity_ge pres n Q ε M δ hδ hEM hbound i (hβ i)
  exact exists_credence_of_rowViolation_le pres worlds Wld low hsupp hcomplete
    (Q n) δ hδ.le hconf

/-- A support-function presentation is world-inclusive: every world satisfies every
row, so the enforcement position's value at every world is nonnegative and the
cumulative liability is zero.  This is what keeps the deductive case at `B = 0`
however many rows the exact family has. -/
theorem rowViolation_eq_zero_at_world (pres : Presentation) (worlds : Finset ι)
    (Wld : ι → Sentence → ℚ) (low : (Sentence → ℚ) → ℚ)
    (hsupp : IsSupportPresentation pres low)
    (hlow_le : ∀ c, ∀ w ∈ worlds, low c ≤ pair pres.coords c (Wld w))
    {w : ι} (hw : w ∈ worlds) (i : Fin pres.rows.length) :
    pres.rowViolation i (Wld w) = 0 := by
  unfold Presentation.rowViolation violation
  have h : pres.rhss i - pair pres.coords (pres.normals i) (Wld w) ≤ 0 := by
    rw [hsupp i]
    have := hlow_le (pres.normals i) w hw
    linarith
  exact max_eq_left h

/-- And therefore the region admits every world, which is the hypothesis
`DeductiveEnforcement.enforcement_day_value_nonneg` consumes. -/
theorem rhss_le_pair_at_world (pres : Presentation) (worlds : Finset ι)
    (Wld : ι → Sentence → ℚ) (low : (Sentence → ℚ) → ℚ)
    (hsupp : IsSupportPresentation pres low)
    (hlow_le : ∀ c, ∀ w ∈ worlds, low c ≤ pair pres.coords c (Wld w))
    {w : ι} (hw : w ∈ worlds) :
    ∀ i ∈ pres.rowIndex, pres.rhss i ≤ pair pres.coords (pres.normals i) (Wld w) := by
  intro i _
  rw [hsupp i]
  exact hlow_le (pres.normals i) w hw

end Workspace.Normativity.Contrib.IntrinsicCoherence

#print axioms Workspace.Normativity.Contrib.IntrinsicCoherence.gap_le_of_rowViolation_le
#print axioms Workspace.Normativity.Contrib.IntrinsicCoherence.exists_credence_of_rowViolation_le
#print axioms Workspace.Normativity.Contrib.IntrinsicCoherence.exists_credence_of_contract
#print axioms Workspace.Normativity.Contrib.IntrinsicCoherence.rowViolation_eq_zero_at_world
#print axioms Workspace.Normativity.Contrib.IntrinsicCoherence.rhss_le_pair_at_world
