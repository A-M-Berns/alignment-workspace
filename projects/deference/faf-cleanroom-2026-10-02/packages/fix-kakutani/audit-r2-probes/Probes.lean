import Cleanroom.Found.FixKakutani

/-!
# `fix-kakutani` audit round 2 (adversarial lens): probes

Written 2026-09-29 by the round-2 adversarial auditor of the faf-cleanroom run. Not imported by
the library (the gate's lint refuses `run.*` imports). Round 1's probes (`audit-r1-probes/
Vacuity.lean`) are not repeated; these attack what round 1 did not: the content of the hull
clause of `exists_approx_selection`, the empty-index instance of `kakutani_pi_stdSimplex`, the
hemicontinuity bridge on the package's own positive and negative examples, the literal
irrelevance of values off `K`, and the axioms of the declarations added in repair round 1.
See `fix-kakutani-audit-r2-adversarial.md` for what each probe shows.
-/

namespace Cleanroom.Found.FixKakutani.AuditR2

open Set Filter Topology Cleanroom.Found.FixKakutani

/-- Probe 1. **The hull clause of `exists_approx_selection` has content.** For `wedgeF` on
`Icc 0 1` at `ε = 1/4`, *any* `f` satisfying the clause alone (continuity and `MapsTo` not
even assumed) has `f 1 = 1` and `f 0 ≤ 5/8`. So the lemma's conclusion is not "`f x ∈ K`" in
disguise (mandate target 2's trap): it pins the approximant to the local values of the
correspondence and forces it to move from `≤ 5/8` at `0` to exactly `1` at `1`. -/
theorem probe_hull_clause_has_content (f : ℝ → ℝ)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1,
      f x ∈ convexHull ℝ (⋃ x' ∈ Icc (0 : ℝ) 1 ∩ Metric.ball x (1 / 4), wedgeF x')) :
    f 1 = 1 ∧ f 0 ≤ 5 / 8 := by
  constructor
  · have h := hf 1 ⟨zero_le_one, le_rfl⟩
    have hsub : (⋃ x' ∈ Icc (0 : ℝ) 1 ∩ Metric.ball (1 : ℝ) (1 / 4), wedgeF x') ⊆ {1} := by
      intro y hy
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_ball, exists_prop] at hy
      obtain ⟨x', ⟨_, hx'b⟩, hy⟩ := hy
      have hx' : 1 / 2 < x' := by
        rw [Real.dist_eq, abs_lt] at hx'b
        linarith [hx'b.1]
      rw [wedgeF_of_gt hx'] at hy
      exact hy
    have hhull : convexHull ℝ (⋃ x' ∈ Icc (0 : ℝ) 1 ∩ Metric.ball (1 : ℝ) (1 / 4), wedgeF x')
        ⊆ {1} := convexHull_min hsub (convex_singleton 1)
    exact Set.mem_singleton_iff.1 (hhull h)
  · have h := hf 0 ⟨le_rfl, zero_le_one⟩
    have hsub : (⋃ x' ∈ Icc (0 : ℝ) 1 ∩ Metric.ball (0 : ℝ) (1 / 4), wedgeF x') ⊆ Iic (5 / 8) := by
      intro y hy
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_ball, exists_prop] at hy
      obtain ⟨x', ⟨_, hx'b⟩, hy⟩ := hy
      have hx' : x' < 1 / 2 := by
        rw [Real.dist_eq, abs_lt] at hx'b
        linarith [hx'b.2]
      have hx'4 : x' < 1 / 4 := by
        rw [Real.dist_eq, abs_lt] at hx'b
        linarith [hx'b.2]
      rw [wedgeF_of_lt hx', Set.mem_singleton_iff] at hy
      rw [hy, Set.mem_Iic]
      linarith
    have hhull : convexHull ℝ (⋃ x' ∈ Icc (0 : ℝ) 1 ∩ Metric.ball (0 : ℝ) (1 / 4), wedgeF x')
        ⊆ Iic (5 / 8) := convexHull_min hsub (convex_Iic _)
    exact Set.mem_Iic.1 (hhull h)

/-- Probe 2. The matching-pennies correspondence takes all three value shapes: a singleton off
the mid-lines (round 1, probe 2), the whole square at the fixed point (round 1, probe 1), and a
*segment* on a mid-line: at `(1/2, 0)` the value is `{0} × Icc 0 1`. So "one factor is
`Icc 0 1`" in the ledger's Witness cell is literally what happens. -/
theorem probe_mpBR_segment : mpBR ![1 / 2, 0] = {y | y 0 = 0 ∧ y 1 ∈ Icc (0 : ℝ) 1} := by
  ext y
  simp only [mpBR, Set.mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [bestResponse_row_of_lt (q := 0) (by norm_num), bestResponse_col_half]
  simp

/-- Probe 3a. With an empty index type the domain of `kakutani_pi_stdSimplex` is everything
(the pi type is a point). -/
theorem probe_pi_stdSimplex_empty_index {A : Fin 0 → Type} [∀ i, Fintype (A i)] :
    Set.univ.pi (fun i => stdSimplex ℝ (A i)) = (univ : Set ((i : Fin 0) → (A i → ℝ))) := by
  ext x
  simp only [Set.mem_univ_pi, Set.mem_univ, iff_true]
  intro i
  exact i.elim0

/-- Probe 3b. **The empty-index instance is a tautology**: over `ι = Fin 0` the conclusion of
`kakutani_pi_stdSimplex` follows from `hF_nonempty` alone (the domain is a point, so any element
of any `F x` is `x`). This is inherent to the statement — the mandate says not to require
`Nonempty ι` — and not a defect; recorded so nobody reads the empty-index case as a check. -/
theorem probe_pi_stdSimplex_empty_index_trivial {A : Fin 0 → Type} [∀ i, Fintype (A i)]
    (F : ((i : Fin 0) → (A i → ℝ)) → Set ((i : Fin 0) → (A i → ℝ)))
    (hF_nonempty : ∀ x ∈ Set.univ.pi (fun i => stdSimplex ℝ (A i)), (F x).Nonempty) :
    ∃ x ∈ Set.univ.pi (fun i => stdSimplex ℝ (A i)), x ∈ F x := by
  have hx : (fun i : Fin 0 => (i.elim0 : A i → ℝ)) ∈ Set.univ.pi (fun i => stdSimplex ℝ (A i)) := by
    intro i _
    exact i.elim0
  obtain ⟨y, hy⟩ := hF_nonempty _ hx
  refine ⟨_, hx, ?_⟩
  have hy' : y = fun i : Fin 0 => (i.elim0 : A i → ℝ) := funext fun i => i.elim0
  rw [hy'] at hy
  exact hy

/-- Probe 4a. The forward bridge is inhabited on a real instance: `wedgeF` is upper
hemicontinuous on `Icc 0 1` in Mathlib's sense, read off its closed graph. -/
theorem probe_wedgeF_upperHemicontinuousOn : UpperHemicontinuousOn wedgeF (Icc 0 1) :=
  wedgeF_hasClosedGraphOn.upperHemicontinuousOn isCompact_Icc wedgeF_maps

/-- Probe 4b. The converse bridge closes the loop on the same instance: from upper
hemicontinuity plus closed values on the closed domain, back to `HasClosedGraphOn`. -/
theorem probe_wedgeF_closedGraph_of_uhc : HasClosedGraphOn wedgeF (Icc 0 1) :=
  HasClosedGraphOn.of_upperHemicontinuousOn isClosed_Icc
    (fun _ hx => wedgeF_hasClosedGraphOn.isClosed_apply hx) probe_wedgeF_upperHemicontinuousOn

/-- Probe 4c. The bridge has teeth on the negative example too: the jump correspondence
`sharpGraphF` (closed singleton values, no closed graph) is **not** upper hemicontinuous on
`Icc 0 1` — by the converse bridge, upper hemicontinuity would give the closed graph that
`sharp_graph` refutes. So `HasClosedGraphOn` and Mathlib's `UpperHemicontinuousOn` agree on the
package's positive and negative examples, not only in the abstract. -/
theorem probe_sharpGraphF_not_upperHemicontinuousOn :
    ¬ UpperHemicontinuousOn sharpGraphF (Icc 0 1) := by
  intro h
  apply sharp_graph.2.2.2.1
  refine HasClosedGraphOn.of_upperHemicontinuousOn isClosed_Icc (fun x _ => ?_) h
  unfold sharpGraphF
  split_ifs <;> exact isClosed_singleton

/-- Probe 5. **Values off `K` are literally irrelevant**: two correspondences that agree on `K`
have the same `HasClosedGraphOn F K`. This is the docstring's claim ("values of `F` outside `K`
are irrelevant") as a theorem, so a consumer may define its correspondence arbitrarily off the
domain. -/
theorem probe_hasClosedGraphOn_congr {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {F F' : α → Set β} {K : Set α} (h : ∀ x ∈ K, F x = F' x) :
    HasClosedGraphOn F K ↔ HasClosedGraphOn F' K := by
  unfold HasClosedGraphOn
  have hset : {p : α × β | p.1 ∈ K ∧ p.2 ∈ F p.1} = {p : α × β | p.1 ∈ K ∧ p.2 ∈ F' p.1} := by
    ext p
    constructor
    · rintro ⟨hp, hy⟩
      refine ⟨hp, ?_⟩
      rw [← h p.1 hp]
      exact hy
    · rintro ⟨hp, hy⟩
      refine ⟨hp, ?_⟩
      rw [h p.1 hp]
      exact hy
  rw [hset]

/-- Probe 6. The witness's fixed point is the one the theorem finds, and the wedge's is too —
stated as the direct memberships, so the reader can see that `mpBR_exists_fixed` and
`wedgeF_exists_fixed` are consistent with the uniqueness certificates (nothing here is a check
of the theorem; it is a check that the certificates and the witnesses talk about the same
points). -/
theorem probe_fixed_points_agree :
    (fun _ : Fin 2 => (1 / 2 : ℝ)) ∈ mpBR (fun _ => 1 / 2) ∧ (1 : ℝ) ∈ wedgeF 1 :=
  ⟨mem_mpBR_self_iff.2 rfl, mem_wedgeF_self_iff.2 rfl⟩

end Cleanroom.Found.FixKakutani.AuditR2

-- Evidence for the axiom claims: FAF's Brouwer (the one external input) and every declaration
-- added in repair round 1, plus the bridge and limit-step lemmas the headlines rest on.
#print axioms LogicalInduction.brouwer_fixed_point
#print axioms Cleanroom.Found.FixKakutani.wedgeF_exists_fixed
#print axioms Cleanroom.Found.FixKakutani.wedgeF_no_continuous_selection
#print axioms Cleanroom.Found.FixKakutani.wedgeF_approx_selection
#print axioms Cleanroom.Found.FixKakutani.mem_wedgeF_self_iff
#print axioms Cleanroom.Found.FixKakutani.HasClosedGraphOn.upperHemicontinuousOn
#print axioms Cleanroom.Found.FixKakutani.HasClosedGraphOn.of_upperHemicontinuousOn
#print axioms Cleanroom.Found.FixKakutani.mem_of_hasClosedGraphOn_of_tendsto_approx
#print axioms Cleanroom.Found.FixKakutani.brouwer_findim_of_kakutani
-- Evidence that the bridge targets Mathlib's predicate, not a local look-alike.
#print UpperHemicontinuousOn
