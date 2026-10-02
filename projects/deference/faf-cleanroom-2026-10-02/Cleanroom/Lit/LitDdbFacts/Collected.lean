import Cleanroom.Lit.LitDdbFacts.Convexity
import Cleanroom.Lit.LitDdbFacts.DutchBook
import Cleanroom.Lit.LitDdbFacts.Geometry

/-!
# Theorem 5.1 collected

Package `lit-ddb-facts`, Target 15. DDB's characterization of Value, with every bullet this
package or `lit-ddb-frames` proves: Value; no fixed-option Dutch book; Total Trust (record
form); the biconvex version; the hull condition; and its λ-form. The third bullet of DDB's
theorem — *epistemic* Value, Theorem 3.2 — belongs to `lit-ddb-accuracy-mm` and is deliberately
absent; the orchestrator may add the bridge once both packages land.
-/

namespace Cleanroom.Lit.LitDdbFacts

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The λ-form of Theorem 5.1's fourth bullet: weights for `π` over `C_π`, and for every
candidate a positive self-cell with weights over `{P̂_ρ} ∪ C_ρ⁻`.
Source: [[Deference Done Better]] §5 l. 375 (Theorem 5.1, fourth bullet)
Kind: D
Fidelity: exact -/
def LambdaForm (π : W → ℝ) (F : Frame W) : Prop :=
  (∃ lam : (W → ℝ) → ℝ, (∀ ρ ∈ F.cands π, 0 ≤ lam ρ) ∧ ∑ ρ ∈ F.cands π, lam ρ = 1 ∧
    ∑ ρ ∈ F.cands π, lam ρ • ρ = π) ∧
  ∀ ρ ∈ F.cands π, 0 < F.selfMass ρ ∧ ∃ c : (W → ℝ) → ℝ,
    (∀ y ∈ insert (F.informed ρ) (F.candsMinus ρ), 0 ≤ c y) ∧
    ∑ y ∈ insert (F.informed ρ) (F.candsMinus ρ), c y = 1 ∧
    ∑ y ∈ insert (F.informed ρ) (F.candsMinus ρ), c y • y = ρ

/-- The hull condition and its λ-form are the same statement (`Finset.mem_convexHull'`).
Source: [[Deference Done Better]] §5 l. 375
Kind: L
Fidelity: exact -/
theorem hullAndModestlyInformed_iff_lambdaForm {π : W → ℝ} {F : Frame W} :
    HullAndModestlyInformed π F ↔ LambdaForm π F := by
  unfold HullAndModestlyInformed LambdaForm
  rw [Finset.mem_convexHull']
  apply and_congr Iff.rfl
  apply forall_congr'
  intro ρ
  apply imp_congr Iff.rfl
  apply and_congr Iff.rfl
  exact modestlyInformedU_iff_weights F ρ

/-- **Target 15 (Theorem 5.1 collected).** For a distribution `π`, the following are equivalent:
`π` values the frame; there is no fixed-option Dutch book against `π → P` (stated at the
sure-loss grade: Theorem 5.1 names the object without saying which of DDB's two inequivalent
definitions, fn 20's sure loss or the glossary's almost-sure loss, it means — findings F1;
immaterial, since the three grades give equivalent bullets by
`not_value_iff_exists_book_sureLoss`/`_almostSureLoss`/`_expectedLoss`); `π`
totally trusts the frame (record form); the biconvex version of Total Trust; `π` lies in the hull
of its candidates and every candidate is modestly informed; the λ-form of the latter. Epistemic
Value (Theorem 3.2) is not included — it is `lit-ddb-accuracy-mm`'s, and is not cited as (b).
Source: [[Deference Done Better]] §5 l. 375 (Theorem 5.1); item 075
Kind: C
Fidelity: weaker: DDB's third bullet (epistemic Value, Theorem 3.2) omitted, see docstring
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` -/
theorem tfae_thm51 {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    List.TFAE [Value π F,
      ¬ ∃ (𝒪₁ 𝒪₂ : DecisionProblem W) (O : W → ℝ) (S : W → (W → ℝ)),
        FixedOptionBook π F 𝒪₁ 𝒪₂ O S SureLoss,
      TotalTrust π F, TotalTrustBiconvex π F, HullAndModestlyInformed π F, LambdaForm π F] := by
  tfae_have 1 ↔ 2 := value_iff_no_book hπ
  tfae_have 1 ↔ 3 := value_iff_totalTrust hπ F
  tfae_have 3 ↔ 4 := totalTrust_iff_totalTrustBiconvex hπ
  tfae_have 3 ↔ 5 := totalTrust_iff_hullAndModestlyInformed hπ F
  tfae_have 5 ↔ 6 := hullAndModestlyInformed_iff_lambdaForm
  tfae_finish

end

end Cleanroom.Lit.LitDdbFacts
