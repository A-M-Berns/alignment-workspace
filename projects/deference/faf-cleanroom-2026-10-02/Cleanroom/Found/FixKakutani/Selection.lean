import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.MulAction

/-!
# The approximate continuous selection lemma (von Neumann / Cellina)

For a compact convex `K` in a real normed space and a correspondence `F` with nonempty values
in `K`, every `ε > 0` admits a continuous `f : K → K` whose value at `x` is a convex
combination of points of `F x'` with `x' ∈ K` within `ε` of `x`. This is the approximation
step of the Kakutani proof; it is *proved* here (target 2 of the mandate), never assumed.

The construction is the classical partition-of-unity one on a finite `ε`-ball cover of `K`:
bump weights `ψ_c x = max 0 (ε − dist x c)`, normalized on `K` where their sum is positive,
applied to one chosen point `y c ∈ F c` per centre `c`.
-/

namespace Cleanroom.Found.FixKakutani

open Set Filter Topology Finset

/-- **Approximate continuous selection.** `K` compact convex, `F` with nonempty values in `K`
on `K`, `ε > 0`: there is `f` continuous on `K`, mapping `K` into `K`, with
`f x ∈ convexHull ℝ (⋃ x' ∈ K ∩ ball x ε, F x')` for every `x ∈ K`. No convexity of the values
and no closed graph is assumed.
Source: [[fixpoint-lit-inventory]] 094 ("Cellina / von Neumann's approximation lemma"); none:
infrastructure
Kind: P
Fidelity: stronger: stated for any real normed space (the mandate asks for `EuclideanSpace`
first) and without `K.Nonempty`, which the construction does not need
Hyps: (a) all: compactness and convexity of `K`, nonempty values in `K`, `0 < ε` -/
theorem exists_approx_selection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK_compact : IsCompact K) (hK_convex : Convex ℝ K)
    {F : E → Set E} (hF_maps : ∀ x ∈ K, F x ⊆ K) (hF_nonempty : ∀ x ∈ K, (F x).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : E → E, ContinuousOn f K ∧ MapsTo f K K ∧
      ∀ x ∈ K, f x ∈ convexHull ℝ (⋃ x' ∈ K ∩ Metric.ball x ε, F x') := by
  classical
  obtain ⟨t, htK, htfin, hcover⟩ := hK_compact.finite_cover_balls hε
  -- one chosen point of `F c` at each `c ∈ K`
  have hsel : ∀ c : E, ∃ y : E, c ∈ K → y ∈ F c := by
    intro c
    by_cases h : c ∈ K
    · exact ⟨(hF_nonempty c h).some, fun _ => (hF_nonempty c h).some_mem⟩
    · exact ⟨c, fun h' => absurd h' h⟩
  choose y hy using hsel
  set T : Finset E := htfin.toFinset with hT
  have hTK : ∀ c ∈ T, c ∈ K := fun c hc => htK (htfin.mem_toFinset.1 hc)
  -- bump weights
  let ψ : E → E → ℝ := fun c x => max 0 (ε - dist x c)
  have hψ_cont : ∀ c, Continuous (ψ c) := fun c =>
    continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  have hψ_nonneg : ∀ c x, 0 ≤ ψ c x := fun c x => le_max_left _ _
  have hψ_pos : ∀ c x, dist x c < ε → 0 < ψ c x := fun c x h =>
    lt_max_of_lt_right (by linarith)
  have hψ_zero : ∀ c x, ¬ dist x c < ε → ψ c x = 0 := fun c x h =>
    max_eq_left (by linarith [not_lt.1 h])
  let S : E → ℝ := fun x => ∑ c ∈ T, ψ c x
  have hS_cont : Continuous S := continuous_finsetSum _ fun c _ => hψ_cont c
  have hS_pos : ∀ x ∈ K, 0 < S x := by
    intro x hx
    obtain ⟨c, hct, hxc⟩ : ∃ c ∈ t, x ∈ Metric.ball c ε := by
      simpa only [Set.mem_iUnion, exists_prop] using hcover hx
    exact Finset.sum_pos' (fun c _ => hψ_nonneg c x)
      ⟨c, htfin.mem_toFinset.2 hct, hψ_pos c x (Metric.mem_ball.1 hxc)⟩
  let w : E → E → ℝ := fun c x => ψ c x / S x
  have hw_nonneg : ∀ x ∈ K, ∀ c, 0 ≤ w c x := fun x hx c =>
    div_nonneg (hψ_nonneg c x) (hS_pos x hx).le
  have hw_sum : ∀ x ∈ K, ∑ c ∈ T, w c x = 1 := by
    intro x hx
    simp only [w]
    rw [← Finset.sum_div, div_self (hS_pos x hx).ne']
  have hw_zero : ∀ x c, ¬ dist x c < ε → w c x = 0 := by
    intro x c h
    simp only [w, hψ_zero c x h, zero_div]
  refine ⟨fun x => ∑ c ∈ T, w c x • y c, ?_, ?_, ?_⟩
  · -- continuity on `K`: the denominator is positive there
    refine continuousOn_finsetSum _ fun c _ => ?_
    exact ((hψ_cont c).continuousOn.div hS_cont.continuousOn
      fun x hx => (hS_pos x hx).ne').smul continuousOn_const
  · -- maps `K` into `K`: a convex combination of points of `K`
    intro x hx
    refine hK_convex.sum_mem (fun c _ => hw_nonneg x hx c) (hw_sum x hx) ?_
    intro c hc
    exact hF_maps c (hTK c hc) (hy c (hTK c hc))
  · -- the convex-hull clause: only centres within `ε` of `x` carry positive weight
    intro x hx
    have hfilter : ∑ c ∈ T, w c x • y c = ∑ c ∈ T.filter (fun c => dist x c < ε), w c x • y c := by
      symm
      apply Finset.sum_filter_of_ne
      intro c _ hne
      by_contra h
      exact hne (by simp [hw_zero x c h])
    have hfilter_w : ∑ c ∈ T.filter (fun c => dist x c < ε), w c x = 1 := by
      rw [← hw_sum x hx]
      apply Finset.sum_filter_of_ne
      intro c _ hne
      by_contra h
      exact hne (hw_zero x c h)
    show ∑ c ∈ T, w c x • y c ∈ convexHull ℝ (⋃ x' ∈ K ∩ Metric.ball x ε, F x')
    rw [hfilter]
    refine (convex_convexHull ℝ _).sum_mem (fun c _ => hw_nonneg x hx c) hfilter_w ?_
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨hcT, hxc⟩ := hc
    have hcK : c ∈ K := hTK c hcT
    apply subset_convexHull
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_ball, exists_prop]
    exact ⟨c, ⟨hcK, by rwa [dist_comm]⟩, hy c hcK⟩

end Cleanroom.Found.FixKakutani
