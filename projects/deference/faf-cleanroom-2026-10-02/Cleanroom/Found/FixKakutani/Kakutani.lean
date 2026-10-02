import LogicalInduction.Construction.Brouwer
import Cleanroom.Found.FixKakutani.Defs
import Cleanroom.Found.FixKakutani.Selection
import Cleanroom.Found.FixKakutani.ClosedGraph
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Kakutani's fixed-point theorem from FAF's Brouwer

`kakutani_euclidean`: a correspondence `F` on a nonempty compact convex `K ⊆ EuclideanSpace ℝ
(Fin d)` with nonempty convex values in `K` and a closed graph over `K` has a fixed point
`x ∈ F x`. Proved from `LogicalInduction.brouwer_fixed_point` (FAF, Sperner over the
Freudenthal/Kuhn triangulation) by the classical approximate-selection argument:

1. `exists_approx_selection` (Selection.lean) gives, for `ε = 1/(n+1)`, a continuous
   `f_n : K → K` with `f_n x ∈ convexHull ℝ (⋃ x' ∈ K ∩ ball x ε, F x')`;
2. Brouwer gives a fixed point `x_n = f_n x_n ∈ K`;
3. compactness gives a convergent subsequence `x_{φ n} → x*`;
4. `mem_of_hasClosedGraphOn_of_tendsto_approx` (ClosedGraph.lean) gives `x* ∈ F x*`.

Every step is proved; no selection is hypothesized (mandate traps (i)–(iii)).
-/

namespace Cleanroom.Found.FixKakutani

open Set Filter Topology

/-- **Kakutani's fixed-point theorem** on a nonempty compact convex `K ⊆ EuclideanSpace ℝ (Fin d)`:
if `F` has nonempty convex values in `K` at every point of `K` and a closed graph over `K`
(`HasClosedGraphOn F K`, i.e. `{(x, y) | x ∈ K ∧ y ∈ F x}` is closed), then some `x ∈ K` has
`x ∈ F x`. Values of `F` off `K` are irrelevant. Proved from FAF's `brouwer_fixed_point` via
the approximate-selection lemma `exists_approx_selection` and the limit step
`mem_of_hasClosedGraphOn_of_tendsto_approx`.
Source: [[fixpoint-lit-inventory]] 017/094 (mathematical-formulation §1)
Kind: P
Fidelity: exact (the corpus's statement for a Euclidean space; the graph is taken over `K`)
Hyps: (a) all — every hypothesis is one of the corpus's four (compact convex nonempty domain,
nonempty values, convex values, closed graph) plus the values-in-`K` clause that makes `F` a
self-correspondence of `K`; nothing is a modelling substitution -/
theorem kakutani_euclidean {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) (hK_nonempty : K.Nonempty)
    (F : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
    (hF_maps : ∀ x ∈ K, F x ⊆ K)
    (hF_nonempty : ∀ x ∈ K, (F x).Nonempty)
    (hF_convex : ∀ x ∈ K, Convex ℝ (F x))
    (hF_graph : HasClosedGraphOn F K) :
    ∃ x ∈ K, x ∈ F x := by
  -- 1. approximate continuous selections at scale `1/(n+1)`
  have hsel : ∀ n : ℕ, ∃ f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      ContinuousOn f K ∧ MapsTo f K K ∧
        ∀ x ∈ K, f x ∈ convexHull ℝ (⋃ x' ∈ K ∩ Metric.ball x (1 / ((n : ℝ) + 1)), F x') :=
    fun n => exists_approx_selection hK_compact hK_convex hF_maps hF_nonempty
      (by positivity)
  choose f hf_cont hf_maps hf_approx using hsel
  -- 2. Brouwer on each approximant
  have hfix : ∀ n : ℕ, ∃ x ∈ K, f n x = x := fun n =>
    LogicalInduction.brouwer_fixed_point hK_compact hK_convex hK_nonempty (f n)
      (hf_cont n) (hf_maps n)
  choose xs hxsK hxsfix using hfix
  -- 3. a convergent subsequence
  obtain ⟨x, hxK, φ, hφ, hlim⟩ := hK_compact.tendsto_subseq hxsK
  refine ⟨x, hxK, ?_⟩
  -- 4. the closed-graph limit step
  have hε : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  refine mem_of_hasClosedGraphOn_of_tendsto_approx hK_compact hF_maps hF_convex hF_graph
    (xs := xs ∘ φ) (fun n => hxsK (φ n)) hlim hε ?_
  intro n
  have := hf_approx (φ n) (xs (φ n)) (hxsK (φ n))
  rw [hxsfix (φ n)] at this
  exact this

end Cleanroom.Found.FixKakutani
