import Cleanroom.Corrigibility.CorrJointProcess.Cellwise

/-!
# `corr-trajectory` — `Inclusion`: `joint`'s Open problem 1 lifted to the trajectory (T13, stretch)

A trajectory of rounds each built by information inclusion (`corr-joint-process`'s `inclusionRound`,
Prop. 1′) satisfies cellwise (i) at every round and every cell — automatically, because inclusion is
re-imposed each round (`inclusion_trajectory_cellwise`, honestly graded `C`: it is `inclusion_cellwise`
applied round by round). The content is a **law**: a transition on `(A_t, y_t, h_t)` under which
`σ(y_{t+1}) ⊆ σ(h_{t+1})` follows from `σ(y_t) ⊆ σ(h_t)` plus disclosure, with the rational cell-aware
overseer of 2-009. No such law is formulated here; the failure mode when growth is *undisclosed* is
E1 (`corr-joint-process`'s `Battery`, and `Margin.e1` on the trajectory): the agent refines its cell,
the overseers keep their old partition, and (i) fails in a sub-cell. `undisclosedLift` is the exact
object of that failure: the overseers' signal lifted to the refined cells.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect

namespace Inclusion

variable {Θ Y K : Type} [Fintype Θ] [Fintype Y] [DecidableEq Y] [Fintype K] [DecidableEq K]

/-- **A trajectory of inclusion rounds is cellwise compliant at every round** — automatic, because
inclusion is re-imposed each round (`C` over `inclusion_cellwise`; no law of motion is involved).
Source: [[corr-wf14-2-inventory]] 2-086 / joint-final.md Open problem 1 (l. 274), lifted to the trajectory
Kind: C
Fidelity: exact (the invariant is re-imposed, not propagated)
Hyps: (a) `hg`: the overseers observe the agent's cell at every round (Pattern B) -/
theorem inclusion_trajectory_cellwise (P : ℕ → Distr (Θ × Y)) (wrong : ℕ → Θ → Bool) (c h : ℕ → ℝ)
    (f : ℕ → Θ × Y → K) (g : ℕ → K → Y) (hg : ∀ t ω, g t (f t ω) = ω.2) :
    ∀ t i, (inclusionRound (P t) (wrong t) (c t) (h t) (f t)).cellwiseBelowThreshold i :=
  fun t i => inclusion_cellwise (P t) (wrong t) (c t) (h t) (f t) (g t) (hg t) i

/-- **The undisclosed refinement**: the agent's cells refine from `Y` to `Y × Z` while the overseers'
signal `f` still reads only `(θ, y)` — the object of E1's failure mode (the law that would preserve
inclusion across this step is the open question).
Source: [[corr-wf14-2-inventory]] 2-086 / joint-final.md Open problem 1; §P.11 (E1)
Kind: D
Fidelity: exact -/
def undisclosedLift {Z : Type} (f : Θ × Y → K) : Θ × (Y × Z) → K := fun ω => f (ω.1, ω.2.1)

/-- The lifted signal is still a function of the old cell, so the overseers cannot distinguish the
refined sub-cells: the inclusion hypothesis `g ∘ f' = snd` of `inclusion_cellwise` **fails** for the
refined cells whenever `Z` has two points — the precise sense in which undisclosed growth breaks
Prop. 1′'s hypothesis.
Source: [[corr-wf14-2-inventory]] 2-086 / joint-final.md Open problem 1 (the failure mode)
Kind: L
Fidelity: exact -/
theorem undisclosedLift_not_inclusion {Z : Type} (f : Θ × Y → K) (θ : Θ) (y : Y) (z₁ z₂ : Z) (hz : z₁ ≠ z₂) :
    ¬ ∃ g : K → Y × Z, ∀ ω : Θ × (Y × Z), g (undisclosedLift f ω) = ω.2 := by
  rintro ⟨g, hg⟩
  have h1 := hg (θ, (y, z₁))
  have h2 := hg (θ, (y, z₂))
  simp only [undisclosedLift] at h1 h2
  rw [h1] at h2
  exact hz (congrArg Prod.snd h2)

end Inclusion

end Cleanroom.Corrigibility.CorrTrajectory
