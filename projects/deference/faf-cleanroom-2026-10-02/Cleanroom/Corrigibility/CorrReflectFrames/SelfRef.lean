import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Metrizable.Basic

/-!
# corr-reflect-frames — T13(c): the self-referential space (OPEN)

Radical Claim I7.1: a total-world space `Ω ≃ W × Δ(Ω)^T`. The smallest case, `T = Unit` and `W`
finite discrete. Repair round 1 (audit r1 fidelity B1, adversarial 3): the round-0 statement
`∃ Ω, Nonempty (Ω ≃ₜ W × ProbabilityMeasure Ω)` was provable with `Ω := Empty` (no probability
measure on an empty type), and true for other wrong reasons at an indiscrete or one-point `W`;
it was not the claim. What I7.1 asks for is a *type space*: a nonempty, compact metrizable Borel
`Ω` whose *canonical* maps `state : Ω → W`, `cred : Ω → Δ(Ω)` jointly form a homeomorphism, and —
what makes it Mertens–Zamir's *universal* type space rather than any fixed point of `X ↦ W × Δ X`
— the universal property: every other continuous coalgebra `Ω' → W × Δ(Ω')` factors uniquely
through it (the terminal coalgebra of the functor `X ↦ W × Δ(X)`).

Why the bare existence of a `SelfRefSpace` is *not* stated as the open claim (argument from the
round-1 fidelity audit, not machine-checked): for `Ω := W × Q` with `Q` the Hilbert cube,
`ProbabilityMeasure (W × Q)` is an infinite-dimensional compact convex metrizable set, hence
homeomorphic to `Q` by Keller's theorem, so `W × Q ≃ₜ W × ProbabilityMeasure (W × Q)` with no
self-reference in it. The universality clause is what excludes such solutions. Mathlib has the
weak topology on `ProbabilityMeasure` and `ProbabilityMeasure.map` but no universal type space
(Mertens–Zamir 1985, Brandenburger–Dekel 1993); the projective-limit construction needs
Prokhorov and a Kolmogorov extension along coherent hierarchies, neither packaged for this use.
Stated and left open after the attempt recorded in the findings (F16). This file imports only
Mathlib.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open MeasureTheory

/-- **A self-referential (type) space over `W`** (radical Claim I7.1, `T = Unit`): a nonempty
compact metrizable Borel space `Ω` with a state map `state : Ω → W` and a credence map
`cred : Ω → Δ(Ω)` (weak topology) such that `ω ↦ (state ω, cred ω)` is a homeomorphism
`Ω ≃ₜ W × Δ(Ω)`. The homeomorphism is the *canonical* one (its coordinates are the two maps), so
`{ω | cred ω ∈ B}` is an event of `Ω` and a total world is an external state plus a credence
over total worlds. Existence of *some* such space is not the open claim (Keller's theorem gives
non-self-referential solutions; module docstring); `IsUniversal` is.
Source: [[radical]] Claim I7.1 l. 197 ("a measurable `Ω` with `Ω ≅ W × Δ(Ω)^T`")
Kind: D
Fidelity: variant: `T = Unit`; topological reading (compact metrizable, Borel, weak topology),
which is the literature's setting for the construction -/
structure SelfRefSpace (W : Type) [TopologicalSpace W] where
  /-- the carrier of total worlds -/
  Ω : Type
  [top : TopologicalSpace Ω]
  [meas : MeasurableSpace Ω]
  [borel : BorelSpace Ω]
  [nonempty : Nonempty Ω]
  [compact : CompactSpace Ω]
  [metrizable : TopologicalSpace.MetrizableSpace Ω]
  /-- the external state of a total world -/
  state : Ω → W
  /-- the credence (over total worlds) of a total world -/
  cred : Ω → ProbabilityMeasure Ω
  /-- the canonical map is a homeomorphism `Ω ≃ₜ W × Δ(Ω)` -/
  isHomeomorph : IsHomeomorph (fun ω => (state ω, cred ω))

attribute [instance] SelfRefSpace.top SelfRefSpace.meas SelfRefSpace.borel SelfRefSpace.nonempty
  SelfRefSpace.compact SelfRefSpace.metrizable

/-- **Universality** (the terminal-coalgebra property, Mertens–Zamir): for every topological
measurable `Ω'` (opens measurable) with a continuous coalgebra structure `ω' ↦ (st' ω', cr' ω')`
into `W × Δ(Ω')`, there is a unique continuous `h : Ω' → Ω` commuting with the structure maps:
`state (h ω') = st' ω'` and `cred (h ω') = (cr' ω').map h`. Test coalgebras range over all
opens-measurable topological spaces with continuous structure maps (a topological reading of
Mertens–Zamir's belief morphisms; their category is the measurable one — variant).
Source: [[radical]] Claim I7.1 l. 197 (the type-space reading); Mertens–Zamir 1985 Thm 2.9,
Brandenburger–Dekel 1993 Prop. 2 (universality of the hierarchy space)
Kind: D
Fidelity: variant: topological test coalgebras with continuous structure maps -/
def SelfRefSpace.IsUniversal {W : Type} [TopologicalSpace W] (X : SelfRefSpace W) : Prop :=
  ∀ (Ω' : Type) [TopologicalSpace Ω'] [MeasurableSpace Ω'] [OpensMeasurableSpace Ω']
    (st' : Ω' → W) (cr' : Ω' → ProbabilityMeasure Ω'),
    Continuous (fun ω' => (st' ω', cr' ω')) →
    ∃! h : {h : Ω' → X.Ω // Continuous h}, ∀ ω',
      X.state (h.1 ω') = st' ω' ∧
        X.cred (h.1 ω') = (cr' ω').map h.2.measurable.aemeasurable

/-- **OPEN (radical Claim I7.1, smallest case, universal form).** For a finite discrete `W` with
at least two points there is a universal self-referential space: a `SelfRefSpace W` with the
terminal-coalgebra property. This is Mertens–Zamir's universal type space for `T = Unit`. The
`[DiscreteTopology W]` and `[Nontrivial W]` hypotheses exclude the parameters at which a
degenerate `Ω` solves the fixed-point equation for reasons unrelated to the claim (audit r1,
adversarial 3); the universality clause excludes Keller-type solutions of the bare fixed-point
equation (audit r1, fidelity B1). Not in Mathlib; see `corr-reflect-frames-findings` F16 for
what was tried.
Source: [[radical]] Claim I7.1 l. 197
Kind: OPEN
Fidelity: variant: `T = Unit`, `W` finite discrete nontrivial, topological reading, universality
over continuous test coalgebras
Hyps: n/a -/
theorem universalSelfRefSpace_exists_open (W : Type) [Fintype W] [TopologicalSpace W]
    [DiscreteTopology W] [Nontrivial W] :
    ∃ X : SelfRefSpace W, X.IsUniversal := by
  sorry

end Cleanroom.Corrigibility.CorrReflectFrames
