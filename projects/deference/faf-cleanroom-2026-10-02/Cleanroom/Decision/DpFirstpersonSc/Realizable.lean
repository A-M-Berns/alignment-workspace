import Cleanroom.Found.DpCoreTree.Defs
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Rat

/-!
# T16(b): continuity of the value functional in the product topology (Q11, dp-core-2-051)

The procedure space `Proc ι acts K = (d : ι) → FinDistr K (acts d)` carries the product
topology of the coordinate topologies on `FinDistr K (acts d)` — each induced by the weight
map `w : acts d → K` from the product topology of `K`'s (`finDistrTopology`, a scoped instance
of this package; `Proc` is an `abbrev`, so Mathlib's `Pi.topologicalSpace` applies). Every leaf
law `C ↦ μ_{B,C}(ℓ)` is a finite product of coordinates `(C d).w a` and chance constants
(`continuous_leafLaw`, by structural induction on the tree), so `C ↦ V_B(C)`, `C ↦ μ_{B,C}(S)`
and `C ↦ ν_{B,C}(X)` are continuous (`continuous_value`, `continuous_mass`, `continuous_nu`) —
over any topological field with continuous `+` and `·`, in particular `ℚ` with its order/metric
topology (`value_continuous_rat`). Together with T16(a) (`Dictionary.lean`: the functional
depends on finitely many coordinates), this is Q11's second necessary condition for
tree-realizability: a realizable functional is a continuous function of finitely many
coordinates — the infinite-family functional fails the first, and any discontinuous functional
of finitely many coordinates would fail the second (no such witness is built here).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

section topology

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
variable {α : Type} [Fintype α]

/-- **The coordinate topology on `FinDistr K α`**: the topology induced by the weight map
`w : FinDistr K α → (α → K)` from the product topology — the subspace topology of the simplex
in `K^α`. A scoped instance (the mandate's "product topology on `(d : ι) → FinDistr ℚ (acts d)`
(coordinate topology from `ℚ`)").
Source: mandate T16(b); [[decision-problems-v2]] Q11
Kind: D
Fidelity: exact -/
scoped instance finDistrTopology : TopologicalSpace (FinDistr K α) :=
  TopologicalSpace.induced FinDistr.w inferInstance

/-- The weight map is continuous (by construction). Source: none: infrastructure. Kind: L -/
theorem continuous_finDistr_w : Continuous (FinDistr.w : FinDistr K α → (α → K)) :=
  continuous_induced_dom

/-- Each weight is a continuous coordinate. Source: none: infrastructure. Kind: L -/
theorem continuous_finDistr_w_apply (a : α) : Continuous fun P : FinDistr K α => P.w a :=
  (continuous_apply a).comp continuous_finDistr_w

variable {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)]

/-- The coordinate `C ↦ (C d).w a` of the procedure space is continuous.
Source: none: infrastructure. Kind: L -/
theorem continuous_proc_w (d : ι) (a : acts d) :
    Continuous fun C : Proc ι acts K => (C d).w a :=
  (continuous_finDistr_w_apply a).comp (continuous_apply d)

variable [ContinuousMul K] [ContinuousAdd K]

/-- **Every leaf law is continuous in the procedure**: a finite product of coordinates
`(C d).w a` and chance constants along the path (structural induction on the tree).
Source: mandate T16(b) ("a polynomial in finitely many coordinates"); [[decision-problems-v2]]
Q11
Kind: P
Fidelity: exact
Hyps: none -/
theorem continuous_leafLaw :
    (B : Tree Ω ι acts K) → ∀ ℓ : B.Leaves, Continuous fun C : Proc ι acts K => leafLaw C B ℓ
  | .leaf _ _, _ => by
      show Continuous fun _ : Proc ι acts K => (1 : K)
      exact continuous_const
  | .chance _ β child, ⟨i, ℓ⟩ => by
      show Continuous fun C : Proc ι acts K => β.w i * leafLaw C (child i) ℓ
      exact continuous_const.mul (continuous_leafLaw (child i) ℓ)
  | .decision d child, ⟨a, ℓ⟩ => by
      show Continuous fun C : Proc ι acts K => (C d).w a * leafLaw C (child a) ℓ
      exact (continuous_proc_w d a).mul (continuous_leafLaw (child a) ℓ)

/-- **The value functional `C ↦ V_B(C)` is continuous in the product topology** (T16(b)): a
finite sum of continuous leaf laws times payoff constants.
Source: mandate T16(b) ("`value · B` is continuous"); [[decision-problems-v2]] Q11, Remark 7.3
Kind: P
Fidelity: exact
Hyps: none -/
theorem continuous_value (B : Tree Ω ι acts K) :
    Continuous fun C : Proc ι acts K => value C B := by
  unfold value
  exact continuous_finsetSum _ fun ℓ _ => (continuous_leafLaw B ℓ).mul continuous_const

/-- The mass of any leaf set is continuous in the procedure. Source: mandate T16(b). Kind: P -/
theorem continuous_mass (B : Tree Ω ι acts K) (S : Finset B.Leaves) :
    Continuous fun C : Proc ι acts K => mass C B S := by
  unfold mass
  exact continuous_finsetSum _ fun ℓ _ => continuous_leafLaw B ℓ

/-- **`C ↦ ν_{B,C}(X)` is continuous** for every event. Source: mandate T16(b). Kind: P -/
theorem continuous_nu [DecidableEq Ω] (B : Tree Ω ι acts K) (X : Finset Ω) :
    Continuous fun C : Proc ι acts K => nu C B X :=
  continuous_mass B _

end topology

section rat

variable {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)]

/-- **T16(b) over `ℚ`**: with `ℚ`'s order topology, `C ↦ V_B(C)` is continuous on
`(d : ι) → FinDistr ℚ (acts d)` with the product of the coordinate topologies — Q11's
continuity condition on tree-realizable functionals.
Source: mandate T16(b); [[decision-problems-v2]] Q11
Kind: P
Fidelity: exact
Hyps: none -/
theorem value_continuous_rat (B : Tree Ω ι acts ℚ) :
    Continuous fun C : Proc ι acts ℚ => value C B :=
  continuous_value B

/-- **T16(b) over `ℚ`, for `ν`**. Source: mandate T16(b). Kind: P -/
theorem nu_continuous_rat [DecidableEq Ω] (B : Tree Ω ι acts ℚ) (X : Finset Ω) :
    Continuous fun C : Proc ι acts ℚ => nu C B X :=
  continuous_nu B X

end rat

end Cleanroom.Decision.DpFirstpersonSc
