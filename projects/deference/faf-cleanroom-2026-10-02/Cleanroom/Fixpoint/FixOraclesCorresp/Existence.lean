import Cleanroom.Fixpoint.FixOraclesCorresp.Defs

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.Existence`: the "generalized Kakutani" refuted, and the repair

Target 4: the notes' existence theorem — *every* `G : Δ(X) ⇉ Δ²(X)` with nonempty convex values and
convex graph has a Dirac fixed point (theoretical-insights §6 "Existence (Generalized Kakutani)",
mathematical-formulation §6 (1), `ReflectiveOracles.lean:49` `fixedPoint_nonempty`) — is stated as
the notes state it (`GeneralizedKakutaniClaim`) and refuted on `X = Fin 2` by the constant
correspondence `G p = {U}`, `U = ½ δ_{e₀} + ½ δ_{e₁}`. The refutation survives adding a closed
(indeed compact) graph for *any* T1 topology on `Δ²(X)` (`not_generalizedKakutaniClaim_closed_fin2`).

Target 5: the repair — under the collapse reading (`p ∈ bary '' G p`), nonempty convex values and a
closed graph of the *collapsed* correspondence `p ↦ bary '' G p` suffice, by `kakutani_findim`
(`fix-kakutani`, grade (a)). Whole-graph convexity is not assumed: that is the repair.
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set Cleanroom.Found.FixKakutani

variable {X : Type*} [Fintype X]

/-- **The notes' "generalized Kakutani" claim, as stated**: every correspondence `G : Δ(X) ⇉ Δ²(X)`
with nonempty convex values and convex graph has a Dirac fixed point.
Source: [[fixpoint-lit-inventory]] 004 (theoretical-insights §6 "Existence (Generalized Kakutani):
Every convex-graph correspondence has a non-empty fixed point set"; mathematical-formulation §6 (1);
`proofs/ReflectiveOracles.lean:49` `fixedPoint_nonempty`)
Kind: D
Fidelity: variant: Δ² finitely supported (the notes' `G` is valued in Borel `Δ²(X)`; the values-in-Δ²
hypothesis is kept so the refutation refutes the notes' claim, not a weaker one)
Hyps: n/a -/
def GeneralizedKakutaniClaim (X : Type*) [Fintype X] : Prop :=
  ∀ G : (X → ℝ) → Set ((X → ℝ) →₀ ℝ),
    (∀ p ∈ stdSimplex ℝ X, G p ⊆ FinMeasure X) →
    (∀ p ∈ stdSimplex ℝ X, (G p).Nonempty ∧ Convex ℝ (G p)) →
    HasConvexGraph G → ∃ p, IsDiracFixedPoint G p

/-- The counterexample measure `U = ½ δ_{e₀} + ½ δ_{e₁}` on `Δ(Fin 2)`.
Source: [[fixpoint-lit-inventory]] 004 ("the constant correspondence `G(p) = {U}` with `U` … any
non-Dirac measure")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def counterU : (Fin 2 → ℝ) →₀ ℝ :=
  (1 / 2 : ℝ) • dirac (Pi.single 0 1) + (1 / 2 : ℝ) • dirac (Pi.single 1 1)

/-- `U ∈ Δ²(Fin 2)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem counterU_mem_finMeasure : counterU ∈ FinMeasure (Fin 2) :=
  convex_finMeasure (dirac_mem_finMeasure (single_mem_stdSimplex ℝ 0))
    (dirac_mem_finMeasure (single_mem_stdSimplex ℝ 1)) (by norm_num) (by norm_num) (by norm_num)

/-- `U` is not a point mass.
Source: none: infrastructure (target 2's key lemma, instantiated)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem counterU_ne_dirac (p : Fin 2 → ℝ) : counterU ≠ dirac p := by
  intro h
  have h' : (1 / 2 : ℝ) • dirac (Pi.single (0 : Fin 2) (1 : ℝ)) +
      (1 - 1 / 2 : ℝ) • dirac (Pi.single 1 1) = dirac p := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    exact h
  have := eq_of_combo_dirac_eq_dirac (by norm_num) (by norm_num) h'
  have := congrFun this 0
  simp at this

/-- The graph of the constant correspondence `p ↦ {U}` is `Δ(X) ×ˢ {U}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem graph_const (U : (X → ℝ) →₀ ℝ) :
    Graph (fun _ : X → ℝ => ({U} : Set ((X → ℝ) →₀ ℝ))) = stdSimplex ℝ X ×ˢ {U} := by
  ext ⟨p, μ⟩
  simp [Graph, graphOn]

/-- **Target 4: the notes' existence theorem is false as stated** (`X = Fin 2`). The constant
correspondence `G p = {U}` has nonempty convex values in `Δ²`, and the convex graph `Δ × {U}`, but no
Dirac fixed point, because `U` is not a point mass.
Source: [[fixpoint-lit-inventory]] 004 (theoretical-insights §6; mathematical-formulation §6 (1);
`ReflectiveOracles.lean:49`)
Kind: P
Fidelity: variant: Δ² finitely supported (the counterexample lives in finitely supported measures,
which are a subset of the notes' `Δ²(X)`, so it refutes the notes' claim a fortiori)
Hyps: (a) none — this is a refutation; (c) carrier: Δ² as finitely supported measures -/
theorem not_generalizedKakutaniClaim_fin2 : ¬ GeneralizedKakutaniClaim (Fin 2) := by
  intro h
  obtain ⟨p, -, hp⟩ := h (fun _ => {counterU})
    (fun _ _ => by rintro _ rfl; exact counterU_mem_finMeasure)
    (fun _ _ => ⟨⟨counterU, rfl⟩, convex_singleton _⟩)
    (by
      unfold HasConvexGraph
      rw [graph_const]
      exact (convex_stdSimplex ℝ (Fin 2)).prod (convex_singleton _))
  exact counterU_ne_dirac p (Set.mem_singleton_iff.1 hp).symm

/-- **Target 4, sharpened: closed and compact graphs do not help.** For *any* T1 topology on
`Δ²(Fin 2)` (there is no canonical one on `Finsupp`; the statement quantifies over all of them), the
same counterexample has a closed graph over `Δ(Fin 2)` (in the product topology) and a compact graph,
and still no Dirac fixed point.
Source: [[fixpoint-lit-inventory]] 004 ("Even adding closed graph and compactness does not help")
Kind: P
Fidelity: stronger: quantifies over every T1 topology on the measures
Hyps: (a) none — this is a refutation; (c) carrier: Δ² as finitely supported measures -/
theorem not_generalizedKakutaniClaim_closed_fin2 [TopologicalSpace ((Fin 2 → ℝ) →₀ ℝ)]
    [T1Space ((Fin 2 → ℝ) →₀ ℝ)] :
    ¬ ∀ G : (Fin 2 → ℝ) → Set ((Fin 2 → ℝ) →₀ ℝ),
      (∀ p ∈ stdSimplex ℝ (Fin 2), G p ⊆ FinMeasure (Fin 2)) →
      (∀ p ∈ stdSimplex ℝ (Fin 2), (G p).Nonempty ∧ Convex ℝ (G p)) →
      HasConvexGraph G → HasClosedGraphOn G (stdSimplex ℝ (Fin 2)) → IsCompact (Graph G) →
      ∃ p, IsDiracFixedPoint G p := by
  intro h
  obtain ⟨p, -, hp⟩ := h (fun _ => {counterU})
    (fun _ _ => by rintro _ rfl; exact counterU_mem_finMeasure)
    (fun _ _ => ⟨⟨counterU, rfl⟩, convex_singleton _⟩)
    (by
      unfold HasConvexGraph
      rw [graph_const]
      exact (convex_stdSimplex ℝ (Fin 2)).prod (convex_singleton _))
    (by
      rw [hasClosedGraphOn_iff_isClosed_graphOn]
      change IsClosed (Graph _)
      rw [graph_const]
      exact (isCompact_stdSimplex ℝ (Fin 2)).isClosed.prod isClosed_singleton)
    (by
      rw [graph_const]
      exact (isCompact_stdSimplex ℝ (Fin 2)).prod isCompact_singleton)
  exact counterU_ne_dirac p (Set.mem_singleton_iff.1 hp).symm

/-- **Target 5, the repair: collapse fixed points exist.** If `G : Δ(X) ⇉ Δ²(X)` has nonempty convex
values and the *collapsed* correspondence `p ↦ bary '' G p` has a closed graph over `Δ(X)`, then some
`p ∈ Δ(X)` satisfies `p ∈ bary '' G p`. Proof: `kakutani_findim` (`fix-kakutani`) on `E = X → ℝ`,
`K = Δ(X)`, `F p = bary '' G p` (values in `Δ(X)` by `bary_mem_stdSimplex`, nonempty as an image,
convex as the linear image of a convex set). Whole-graph convexity of `G` is **not** assumed.
**Disclosure**: the source's closed-graph hypothesis is on `G` itself in the weak-* topology of
`Δ²(X)`; here it is placed on the collapsed correspondence (a `variant`). Nonemptiness of `X` is
needed for `Δ(X) ≠ ∅`.
Source: [[fixpoint-lit-inventory]] 005 (conversation-reconstruction "Option 3: With Monad Collapse";
`distribution_fixed_points.py:find_fixed_points`)
Kind: C
Fidelity: variant: Δ² finitely supported; the closed-graph hypothesis is on `bary ∘ G`
Hyps: (a) all: Kakutani is `Cleanroom.Found.FixKakutani.kakutani_findim` (proved from FAF's Brouwer); (c) carrier: Δ² as finitely supported measures -/
theorem exists_collapse_fixed_point [Nonempty X] (G : (X → ℝ) → Set ((X → ℝ) →₀ ℝ))
    (hval : ∀ p ∈ stdSimplex ℝ X, G p ⊆ FinMeasure X)
    (hne : ∀ p ∈ stdSimplex ℝ X, (G p).Nonempty)
    (hconv : ∀ p ∈ stdSimplex ℝ X, Convex ℝ (G p))
    (hgraph : HasClosedGraphOn (fun p => bary '' G p) (stdSimplex ℝ X)) :
    ∃ p, IsCollapseFixedPoint G p := by
  classical
  obtain ⟨p, hp, hpF⟩ := kakutani_findim (E := X → ℝ) (isCompact_stdSimplex ℝ X)
    (convex_stdSimplex ℝ X) ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary X)⟩
    (fun p => bary '' G p)
    (fun p hp => by
      rintro _ ⟨μ, hμ, rfl⟩
      exact bary_mem_stdSimplex (hval p hp hμ))
    (fun p hp => (hne p hp).image _)
    (fun p hp => (hconv p hp).is_linear_image bary.isLinear)
    hgraph
  exact ⟨p, hp, hpF⟩

/-- **N− instance of target 5** (single-valued, so Kakutani degenerates to Brouwer): for `f`
continuous on `Δ(X)` with values in `Δ(X)`, the barycentric lift `baryLift f` satisfies the
hypotheses of `exists_collapse_fixed_point` and so has a collapse fixed point. The genuinely
set-valued N+ witness is `liarCollapse` in `Liar.lean`.
Source: [[fixpoint-lit-inventory]] 005; mandate target 5 ("a single-valued `G` … is N−")
Kind: N-
Fidelity: n/a
Hyps: (a) none -/
theorem exists_collapse_fixed_point_baryLift [Nonempty X] (f : (X → ℝ) → (X → ℝ))
    (hf : MapsTo f (stdSimplex ℝ X) (stdSimplex ℝ X)) (hc : ContinuousOn f (stdSimplex ℝ X)) :
    ∃ p, IsCollapseFixedPoint (baryLift f) p := by
  refine exists_collapse_fixed_point (baryLift f) (fun p _ μ hμ => hμ.1)
    (fun p hp => ⟨dirac (f p), dirac_mem_finMeasure (hf hp), by simp⟩)
    (fun p _ => ?_) ?_
  · have : baryLift f p = FinMeasure X ∩ bary ⁻¹' {f p} := by
      ext μ; simp [baryLift]
    rw [this]
    exact convex_finMeasure.inter ((convex_singleton _).linear_preimage bary)
  · have himg : ∀ p ∈ stdSimplex ℝ X, bary '' baryLift f p = {f p} := by
      intro p hp
      ext q
      constructor
      · rintro ⟨μ, ⟨-, hμ⟩, rfl⟩; exact hμ
      · rintro rfl; exact ⟨dirac (f p), ⟨dirac_mem_finMeasure (hf hp), by simp⟩, by simp⟩
    rw [hasClosedGraphOn_iff_isClosed_graphOn]
    have : graphOn (stdSimplex ℝ X) (fun p => bary '' baryLift f p) =
        {q : (X → ℝ) × (X → ℝ) | q.1 ∈ stdSimplex ℝ X ∧ q.2 = f q.1} := by
      ext ⟨p, q⟩
      simp only [graphOn, mem_setOf_eq]
      constructor
      · rintro ⟨hp, hq⟩; rw [himg p hp] at hq; exact ⟨hp, hq⟩
      · rintro ⟨hp, hq⟩; exact ⟨hp, by rw [himg p hp]; exact hq⟩
    rw [this]
    have hK : IsClosed (stdSimplex ℝ X) := (isCompact_stdSimplex ℝ X).isClosed
    have h1 : IsClosed {q : (X → ℝ) × (X → ℝ) | q.1 ∈ stdSimplex ℝ X} := hK.preimage continuous_fst
    have h2 : ContinuousOn (fun q : (X → ℝ) × (X → ℝ) => (q.2, f q.1))
        {q : (X → ℝ) × (X → ℝ) | q.1 ∈ stdSimplex ℝ X} :=
      continuous_snd.continuousOn.prodMk (hc.comp continuous_fst.continuousOn (fun q hq => hq))
    have := h2.preimage_isClosed_of_isClosed h1 isClosed_diagonal
    convert this using 1
    ext q
    simp [Set.mem_diagonal_iff]

end Cleanroom.Fixpoint.FixOraclesCorresp
