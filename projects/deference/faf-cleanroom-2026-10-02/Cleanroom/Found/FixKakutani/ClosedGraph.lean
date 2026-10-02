import Cleanroom.Found.FixKakutani.Defs
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Hull

/-!
# Closed graphs, upper hemicontinuity, and the closed-graph limit step

Two things live here (target 3 of the mandate):

1. **The hemicontinuity bridge.** `HasClosedGraphOn F K` is shown to be the classical notion:
   with compact `K` and values in a compact set it implies Mathlib's `UpperHemicontinuousOn F K`
   (`HasClosedGraphOn.upperHemicontinuousOn`), and conversely upper hemicontinuity with closed
   values on a closed `K` gives a closed graph (`HasClosedGraphOn.of_upperHemicontinuousOn`).
   Both go through `restrictTo F K` (`F` extended by `∅` off `K`) and Mathlib's sequential
   characterizations (`UpperHemicontinuousAt.of_sequences`, `.mem_of_tendsto`).

2. **The closed-graph limit step** (`mem_of_hasClosedGraphOn_of_tendsto_approx`): if `x_n ∈ K`
   converge to `x`, `ε_n → 0`, and each `x_n` lies in the convex hull of the values of `F` on
   the `ε_n`-ball around `x_n`, then `x ∈ F x` — provided `F` has a closed graph over compact
   `K` and convex values in `K`. This is step 4 of the Kakutani proof, split out so it can be
   audited on its own.
-/

namespace Cleanroom.Found.FixKakutani

open Set Filter Topology

section Bridge

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- Upper hemicontinuity of `F` within `K` at a point of `K` is upper hemicontinuity of the
`∅`-extension `restrictTo F K` at that point (in the whole space).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem upperHemicontinuousWithinAt_iff_restrictTo {F : α → Set β} {K : Set α} {x : α}
    (hx : x ∈ K) :
    UpperHemicontinuousWithinAt F K x ↔ UpperHemicontinuousAt (restrictTo F K) x := by
  rw [upperHemicontinuousWithinAt_iff, upperHemicontinuousAt_iff]
  constructor
  · intro h t ht
    rw [restrictTo_of_mem hx] at ht
    have := h t ht
    rw [eventually_nhdsWithin_iff] at this
    filter_upwards [this] with x' hx'
    by_cases h' : x' ∈ K
    · rw [restrictTo_of_mem h']
      exact hx' h'
    · rw [restrictTo_of_not_mem h', nhdsSet_empty]
      exact mem_bot
  · intro h t ht
    have := h t (by rwa [restrictTo_of_mem hx])
    rw [eventually_nhdsWithin_iff]
    filter_upwards [this] with x' hx' hx'K
    rwa [restrictTo_of_mem hx'K] at hx'

/-- **Closed graph ⟹ upper hemicontinuous** (first-countable spaces): if `F` has a closed graph
over `K` and its values on `K` lie in a compact set `L`, then `F` is upper hemicontinuous on
`K` in Mathlib's sense. Via `UpperHemicontinuousAt.of_sequences` applied to `restrictTo F K`.
Source: none: infrastructure (target 3: the hemicontinuity bridge, forward direction)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HasClosedGraphOn.upperHemicontinuousOn [FirstCountableTopology α]
    [FirstCountableTopology β] {F : α → Set β} {K : Set α} {L : Set β}
    (hL : IsCompact L) (hF : ∀ x ∈ K, F x ⊆ L) (h : HasClosedGraphOn F K) :
    UpperHemicontinuousOn F K := by
  rw [upperHemicontinuousOn_iff]
  intro x hx
  rw [upperHemicontinuousWithinAt_iff_restrictTo hx]
  refine UpperHemicontinuousAt.of_sequences hL.isSeqCompact
    (Eventually.of_forall fun x' => restrictTo_subset hF x') ?_
  intro xs hxs ys hys y₀ hy₀
  rw [restrictTo_of_mem hx]
  exact (h.mem_of_tendsto (Eventually.of_forall fun n => (hys n : xs n ∈ K ∧ ys n ∈ F (xs n)))
    hxs hy₀).2

/-- **Upper hemicontinuous with closed values on a closed domain ⟹ closed graph** (regular
codomain). Via `UpperHemicontinuousAt.mem_of_tendsto` applied to `restrictTo F K`.
Source: none: infrastructure (target 3: the hemicontinuity bridge, converse direction)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HasClosedGraphOn.of_upperHemicontinuousOn [RegularSpace β] {F : α → Set β} {K : Set α}
    (hK : IsClosed K) (hcl : ∀ x ∈ K, IsClosed (F x)) (h : UpperHemicontinuousOn F K) :
    HasClosedGraphOn F K := by
  unfold HasClosedGraphOn
  rw [isClosed_iff_frequently]
  rintro ⟨x, y⟩ hfreq
  have hx : x ∈ K := by
    rw [isClosed_iff_frequently] at hK
    exact hK x ((continuous_fst.tendsto (x, y)).frequently (hfreq.mono fun p hp => hp.1))
  refine ⟨hx, ?_⟩
  have huhc : UpperHemicontinuousAt (restrictTo F K) x :=
    (upperHemicontinuousWithinAt_iff_restrictTo hx).mp (h x hx)
  have hcl' : IsClosed (restrictTo F K x) := by
    rw [restrictTo_of_mem hx]
    exact hcl x hx
  have := huhc.mem_of_tendsto hcl' (continuous_fst.tendsto (x, y))
    (hfreq.mono fun p hp => (mem_restrictTo.2 hp : p.2 ∈ restrictTo F K p.1))
    (continuous_snd.tendsto (x, y))
  rwa [restrictTo_of_mem hx] at this

end Bridge

section LimitStep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- **Upper hemicontinuity, `ε`–`δ` form**, from a closed graph over a compact `K` with values in
`K`: for every `x ∈ K` and `η > 0` there is `δ > 0` such that `F x' ⊆ thickening η (F x)` for
all `x' ∈ K` within `δ` of `x`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HasClosedGraphOn.exists_delta_subset_thickening {K : Set E} (hK_compact : IsCompact K)
    {F : E → Set E} (hF_maps : ∀ x ∈ K, F x ⊆ K) (hF_graph : HasClosedGraphOn F K)
    {x : E} (hx : x ∈ K) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x' ∈ K, dist x' x < δ → F x' ⊆ Metric.thickening η (F x) := by
  have huhc : UpperHemicontinuousAt (restrictTo F K) x :=
    (upperHemicontinuousWithinAt_iff_restrictTo hx).mp
      (hF_graph.upperHemicontinuousOn hK_compact hF_maps x hx)
  have hmem : Metric.thickening η (F x) ∈ 𝓝ˢ (restrictTo F K x) := by
    rw [restrictTo_of_mem hx]
    exact Metric.isOpen_thickening.mem_nhdsSet.mpr (Metric.self_subset_thickening hη _)
  have := (upperHemicontinuousAt_iff.1 huhc) _ hmem
  rw [Metric.eventually_nhds_iff] at this
  obtain ⟨δ, hδ, hδ'⟩ := this
  refine ⟨δ, hδ, fun x' hx'K hx'δ => ?_⟩
  have := hδ' hx'δ
  rw [restrictTo_of_mem hx'K] at this
  exact subset_of_mem_nhdsSet this

/-- **The closed-graph limit step.** `K` compact, `F` with closed graph over `K` and convex values
in `K`. If `xs n ∈ K`, `xs → x`, `ε → 0`, and each `xs n` lies in the convex hull of
`⋃ x' ∈ K ∩ ball (xs n) (ε n), F x'`, then `x ∈ F x`. (Step 4 of the Kakutani proof; the
thickening route: for large `n` the hull lies in `thickening η (F x)`, which is convex.)
Source: none: infrastructure (target 3 of the mandate)
Kind: P
Fidelity: n/a
Hyps: (a) all -/
theorem mem_of_hasClosedGraphOn_of_tendsto_approx {K : Set E} (hK_compact : IsCompact K)
    {F : E → Set E} (hF_maps : ∀ x ∈ K, F x ⊆ K) (hF_convex : ∀ x ∈ K, Convex ℝ (F x))
    (hF_graph : HasClosedGraphOn F K)
    {xs : ℕ → E} (hxs : ∀ n, xs n ∈ K) {x : E} (hlim : Tendsto xs atTop (𝓝 x))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (happrox : ∀ n, xs n ∈ convexHull ℝ (⋃ x' ∈ K ∩ Metric.ball (xs n) (ε n), F x')) :
    x ∈ F x := by
  have hxK : x ∈ K := hK_compact.isClosed.mem_of_tendsto hlim (Eventually.of_forall hxs)
  have hFx_closed : IsClosed (F x) := hF_graph.isClosed_apply hxK
  rw [← hFx_closed.closure_eq, Metric.mem_closure_iff]
  intro η hη
  obtain ⟨δ, hδ, hδ'⟩ :=
    hF_graph.exists_delta_subset_thickening hK_compact hF_maps hxK (half_pos hη)
  have h1 : ∀ᶠ n in atTop, ε n < δ / 2 := hε.eventually (gt_mem_nhds (half_pos hδ))
  have h2 : ∀ᶠ n in atTop, dist (xs n) x < min (δ / 2) (η / 2) :=
    (Metric.tendsto_nhds.1 hlim) _ (lt_min (half_pos hδ) (half_pos hη))
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  have hn2' := lt_min_iff.1 hn2
  have hsub : (⋃ x' ∈ K ∩ Metric.ball (xs n) (ε n), F x') ⊆ Metric.thickening (η / 2) (F x) := by
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_ball, exists_prop] at hy
    obtain ⟨x', ⟨hx'K, hx'ball⟩, hy⟩ := hy
    have : dist x' x < δ := by
      calc dist x' x ≤ dist x' (xs n) + dist (xs n) x := dist_triangle _ _ _
        _ < δ / 2 + δ / 2 := by linarith [hn2'.1]
        _ = δ := by ring
    exact hδ' x' hx'K this hy
  have hxn : xs n ∈ Metric.thickening (η / 2) (F x) :=
    convexHull_min hsub ((hF_convex x hxK).thickening _) (happrox n)
  obtain ⟨z, hz, hdz⟩ := Metric.mem_thickening_iff.1 hxn
  refine ⟨z, hz, ?_⟩
  calc dist x z ≤ dist x (xs n) + dist (xs n) z := dist_triangle _ _ _
    _ < η / 2 + η / 2 := by rw [dist_comm]; linarith [hn2'.2]
    _ = η := by ring

end LimitStep

end Cleanroom.Found.FixKakutani
