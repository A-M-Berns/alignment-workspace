import Cleanroom.Found.FixKakutani.Kakutani
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Kakutani transported to finite-dimensional normed spaces, products of simplices and cubes

`kakutani_findim` moves `kakutani_euclidean` along a continuous linear equivalence
`E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))` to any finite-dimensional real normed space
`E` (target 4a). The two corollaries the consumer packages cite are then one application each:

* `kakutani_pi_stdSimplex`: the domain `Set.univ.pi (fun i => stdSimplex ℝ (A i))` of mixed
  strategy profiles in `(i : ι) → (A i → ℝ)` (target 4b); needs every `A i` nonempty
  (`univ_pi_stdSimplex_eq_empty_of_isEmpty` shows the statement is false otherwise);
* `kakutani_pi_Icc`: the cube `Set.univ.pi (fun _ : Q => Icc 0 1)` in `Q → ℝ` (target 4c, the
  reflective-oracle form).

The closed-graph hypothesis in each is literally `HasClosedGraphOn F (Set.univ.pi …)`, so a
consumer discharges its "Kakutani 1941" (b) hypothesis with one `exact`.
-/

namespace Cleanroom.Found.FixKakutani

open Set Filter Topology

/-- **Kakutani on a finite-dimensional real normed space**: `K ⊆ E` nonempty compact convex,
`F` with nonempty convex values in `K` and a closed graph over `K` ⟹ `∃ x ∈ K, x ∈ F x`.
Transport of `kakutani_euclidean` along `ContinuousLinearEquiv.ofFinrankEq`.
Source: [[fixpoint-lit-inventory]] 017/094 (mathematical-formulation §1)
Kind: C
Fidelity: stronger: the corpus says "a Euclidean space"; here the norm on `E` is arbitrary
(every finite-dimensional real normed space is linearly homeomorphic to a Euclidean one)
Hyps: (a) all -/
theorem kakutani_findim {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) (hK_nonempty : K.Nonempty)
    (F : E → Set E)
    (hF_maps : ∀ x ∈ K, F x ⊆ K)
    (hF_nonempty : ∀ x ∈ K, (F x).Nonempty)
    (hF_convex : ∀ x ∈ K, Convex ℝ (F x))
    (hF_graph : HasClosedGraphOn F K) :
    ∃ x ∈ K, x ∈ F x := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let G : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →
      Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := fun y => e '' F (e.symm y)
  have hK'c : IsCompact (e '' K) := hK_compact.image e.continuous
  have hK'v : Convex ℝ (e '' K) := hK_convex.is_linear_image ⟨e.map_add, e.map_smul⟩
  have hK'n : (e '' K).Nonempty := hK_nonempty.image e
  have hG_maps : ∀ y ∈ e '' K, G y ⊆ e '' K := by
    rintro y ⟨x, hx, rfl⟩
    simp only [G, e.symm_apply_apply]
    exact Set.image_mono (hF_maps x hx)
  have hG_nonempty : ∀ y ∈ e '' K, (G y).Nonempty := by
    rintro y ⟨x, hx, rfl⟩
    simp only [G, e.symm_apply_apply]
    exact (hF_nonempty x hx).image e
  have hG_convex : ∀ y ∈ e '' K, Convex ℝ (G y) := by
    rintro y ⟨x, hx, rfl⟩
    simp only [G, e.symm_apply_apply]
    exact (hF_convex x hx).is_linear_image ⟨e.map_add, e.map_smul⟩
  have hG_graph : HasClosedGraphOn G (e '' K) := by
    unfold HasClosedGraphOn
    have hset : {p : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ×
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) | p.1 ∈ e '' K ∧ p.2 ∈ G p.1} =
        (fun p : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ×
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => (e.symm p.1, e.symm p.2)) ⁻¹'
          {p : E × E | p.1 ∈ K ∧ p.2 ∈ F p.1} := by
      ext ⟨y₁, y₂⟩
      simp only [G, Set.mem_setOf_eq, Set.mem_preimage, e.image_eq_preimage_symm]
    rw [hset]
    exact hF_graph.preimage (by fun_prop)
  obtain ⟨y, hyK, hyG⟩ := kakutani_euclidean hK'c hK'v hK'n G hG_maps hG_nonempty hG_convex
    hG_graph
  obtain ⟨x, hx, rfl⟩ := hyK
  refine ⟨x, hx, ?_⟩
  simp only [G, e.symm_apply_apply] at hyG
  exact e.injective.mem_set_image.1 hyG

/-- **Kakutani on a product of standard simplices** (the mixed-strategy form the decision, UEA
and reflective-oracle packages cite): `ι` finite, each `A i` finite and nonempty, the domain
`Set.univ.pi (fun i => stdSimplex ℝ (A i)) ⊆ ((i : ι) → (A i → ℝ))`, and `F` with nonempty
convex values in the domain and a closed graph over it. `Nonempty (A i)` is needed: with one
empty `A i` the domain is empty (`univ_pi_stdSimplex_eq_empty_of_isEmpty`). Unlike
Wyeth–Hutter–Leike–Taylor's Thm 33 (Kakutani–Ky Fan on a locally convex TVS with an upper
semicontinuous map), this is the finite-dimensional case with a closed graph; the two
hypotheses coincide here by `HasClosedGraphOn.upperHemicontinuousOn` and
`HasClosedGraphOn.of_upperHemicontinuousOn`.
Source: [[fixpoint-lit-inventory]] 094; [[uea-2-inventory]] 017 (Thm 33)
Kind: C
Fidelity: variant: finite-dimensional, closed graph (see the docstring)
Hyps: (a) all -/
theorem kakutani_pi_stdSimplex {ι : Type*} [Fintype ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (F : ((i : ι) → (A i → ℝ)) → Set ((i : ι) → (A i → ℝ)))
    (hF_maps : ∀ x ∈ Set.univ.pi (fun i => stdSimplex ℝ (A i)),
      F x ⊆ Set.univ.pi (fun i => stdSimplex ℝ (A i)))
    (hF_nonempty : ∀ x ∈ Set.univ.pi (fun i => stdSimplex ℝ (A i)), (F x).Nonempty)
    (hF_convex : ∀ x ∈ Set.univ.pi (fun i => stdSimplex ℝ (A i)), Convex ℝ (F x))
    (hF_graph : HasClosedGraphOn F (Set.univ.pi (fun i => stdSimplex ℝ (A i)))) :
    ∃ x ∈ Set.univ.pi (fun i => stdSimplex ℝ (A i)), x ∈ F x := by
  classical
  refine kakutani_findim (isCompact_univ_pi fun i => isCompact_stdSimplex ℝ (A i))
    (convex_pi fun i _ => convex_stdSimplex ℝ (A i)) ?_ F hF_maps hF_nonempty hF_convex hF_graph
  exact Set.univ_pi_nonempty_iff.2 fun i =>
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary (A i))⟩

/-- The nonemptiness hypothesis of `kakutani_pi_stdSimplex` is needed: if some `A i₀` is empty,
the domain `Set.univ.pi (fun i => stdSimplex ℝ (A i))` is empty (`stdSimplex ℝ (A i₀)` is
empty because the empty sum is `0 ≠ 1`), so no correspondence has a fixed point in it.
Source: none: infrastructure (target 4b's N− check)
Kind: N-
Fidelity: n/a
Hyps: (a) -/
theorem univ_pi_stdSimplex_eq_empty_of_isEmpty {ι : Type*} {A : ι → Type*}
    [∀ i, Fintype (A i)] (i₀ : ι) [IsEmpty (A i₀)] :
    Set.univ.pi (fun i => stdSimplex ℝ (A i)) = ∅ := by
  rw [Set.univ_pi_eq_empty_iff]
  refine ⟨i₀, ?_⟩
  ext f
  simp [stdSimplex]

/-- **Kakutani on the cube** `Set.univ.pi (fun _ : Q => Icc 0 1) ⊆ (Q → ℝ)`, `Q` finite (the
finite-query reflective-oracle form: one probability per query; the countable-query oracle of
the source needs an infinite-dimensional form that this package does not provide). `F` with
nonempty convex values in the cube and a closed graph over it has a fixed point.
Source: [[fixpoint-lit-inventory]] 018; [[uea-2-inventory]] 017 (Thm 33, finite-dimensional
case)
Kind: C
Fidelity: variant: finite-dimensional, closed graph (Thm 33 is Kakutani–Ky Fan on a locally
convex TVS with an upper semicontinuous map; the hypotheses coincide here by the
hemicontinuity bridge in ClosedGraph.lean)
Hyps: (a) all -/
theorem kakutani_pi_Icc {Q : Type*} [Fintype Q]
    (F : (Q → ℝ) → Set (Q → ℝ))
    (hF_maps : ∀ x ∈ Set.univ.pi (fun _ : Q => Icc (0 : ℝ) 1),
      F x ⊆ Set.univ.pi (fun _ : Q => Icc (0 : ℝ) 1))
    (hF_nonempty : ∀ x ∈ Set.univ.pi (fun _ : Q => Icc (0 : ℝ) 1), (F x).Nonempty)
    (hF_convex : ∀ x ∈ Set.univ.pi (fun _ : Q => Icc (0 : ℝ) 1), Convex ℝ (F x))
    (hF_graph : HasClosedGraphOn F (Set.univ.pi (fun _ : Q => Icc (0 : ℝ) 1))) :
    ∃ x ∈ Set.univ.pi (fun _ : Q => Icc (0 : ℝ) 1), x ∈ F x :=
  kakutani_findim (isCompact_univ_pi fun _ => isCompact_Icc)
    (convex_pi fun _ _ => convex_Icc 0 1)
    (Set.univ_pi_nonempty_iff.2 fun _ => Set.nonempty_Icc.2 zero_le_one)
    F hF_maps hF_nonempty hF_convex hF_graph

end Cleanroom.Found.FixKakutani
