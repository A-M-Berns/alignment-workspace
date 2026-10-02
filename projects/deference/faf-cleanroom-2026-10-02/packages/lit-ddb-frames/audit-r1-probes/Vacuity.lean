import Cleanroom.Found.LitDdbFrames

/-!
# Audit round 1 (adversarial) — probes for `lit-ddb-frames`

Evidence file for `run/wp/lit-ddb-frames/lit-ddb-frames-audit-r1-adversarial.md`. Not imported
by the library. Each probe checks that a definition of record bites where the package gives it
no direct witness, or that an encoding choice does not change a headline's meaning.
-/

namespace Cleanroom.Found.LitDdbFrames.AuditR1

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Probe 1: the `0 < selfMass` guard in `ModestlyInformed` does not strengthen 7.6 (iv)

DDB's glossary defines "modestly informed" with no explicit positivity clause (the informed
expert `P̂_i` is presupposed to exist). `Frame.ModestlyInformed` adds `0 < ρ(P = ρ)`. Under
`π ∈ convexHull C_π` the guard is *derivable* from the unguarded hull membership (with Lean's
junk value `P̂ = 0` at a null self-cell), so the fourth condition of Theorem 7.6 is the same
predicate with or without the guard: the encoding neither strengthens nor weakens DDB's. -/

/-- The unguarded reading of the fourth condition. -/
def HullAndMIUnguarded (π : W → ℝ) (F : Frame W) : Prop :=
  π ∈ convexHull ℝ (↑(F.cands π) : Set (W → ℝ)) ∧
    ∀ ρ ∈ F.cands π, ρ ∈ convexHull ℝ (insert (F.informed ρ) (↑(F.candsMinus ρ) : Set (W → ℝ)))

theorem hullAndMIUnguarded_iff {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    HullAndMIUnguarded π F ↔ HullAndModestlyInformed π F := by
  constructor
  · rintro ⟨hhull, hmi⟩
    have hdec : F.DecompOver π := fun ρ hρ =>
      ⟨F.candsMinus ρ, fun σ hσ => by
        obtain ⟨hne, hσc⟩ := Frame.mem_candsMinus.1 hσ
        obtain ⟨v, hv, rfl⟩ := Frame.mem_cands.1 hσc
        exact ⟨hne, v, rfl, Or.inr hv⟩, hmi ρ hρ⟩
    exact ⟨hhull, fun ρ hρ => ⟨F.selfMass_pos_of_hull hπ hhull hdec hρ, hmi ρ hρ⟩⟩
  · rintro ⟨hhull, hmi⟩
    exact ⟨hhull, fun ρ hρ => (hmi ρ hρ).2⟩

/-! ## Probe 2: NR-vac and NR-str are genuinely different predicates (findings F8)

Rows `P_a = (0, 1)`, `P_b = (1, 0)` (each expert certain of the *other* world), `π = (½, ½)`.
Both candidates have a null self-cell, so NR-vac holds vacuously while NR-str fails. -/

/-- The swapped-certainty frame. -/
def swap2 : Frame (Fin 2) :=
  mk2 ![0, 1] ![1, 0]
    (simplex2 _ _ (by norm_num) (by norm_num) (by norm_num))
    (simplex2 _ _ (by norm_num) (by norm_num) (by norm_num))

theorem swap2_P0 : swap2.P 0 = ![0, 1] := rfl
theorem swap2_P1 : swap2.P 1 = ![1, 0] := rfl

theorem swap2_ne : swap2.P 0 ≠ swap2.P 1 := by
  intro h
  have := congrFun h 0
  rw [swap2_P0, swap2_P1] at this
  norm_num at this

theorem swap2_selfMass : swap2.selfMass (swap2.P 0) = 0 ∧ swap2.selfMass (swap2.P 1) = 0 := by
  obtain ⟨hc0, hc1⟩ := cell_of_ne swap2 swap2_ne
  constructor
  · rw [Frame.selfMass, hc0]; norm_num [mass, swap2_P0]
  · rw [Frame.selfMass, hc1]; norm_num [mass, swap2_P1]

theorem swap2_newReflectsVac_not_newReflects :
    NewReflectsVac half swap2 ∧ ¬ NewReflects half swap2 := by
  obtain ⟨hs0, hs1⟩ := swap2_selfMass
  have hcands := cands_eq_pair swap2 (by norm_num [half] : (0 : ℝ) < half 0)
    (by norm_num [half] : (0 : ℝ) < half 1)
  constructor
  · intro ρ hρ hpos
    rw [hcands] at hρ
    simp only [mem_insert, mem_singleton] at hρ
    rcases hρ with rfl | rfl
    · rw [hs0] at hpos; exact absurd hpos (lt_irrefl _)
    · rw [hs1] at hpos; exact absurd hpos (lt_irrefl _)
  · intro h
    have := (h (swap2.P 0) (by rw [hcands]; simp)).1
    rw [hs0] at this
    exact lt_irrefl _ this

/-! ## Probe 3: `SimpleTrust` and `Trust` bite — both fail directly on Figure 2

The package witnesses these two definitions of record only through `TotalTrust.simpleTrust` /
`TotalTrust.trust` on Figure 3. Here both fail on the anti-expert frame at `q = {a}`,
`t = 4/5`: the event `[P(a) ≥ 4/5]` is `{b}`, of `π`-mass `½ > 0`, and
`π(a ∧ [P(a) ≥ 4/5]) = 0 < 4/5 · ½`. -/

theorem fig2_probEvent : fig2.probEvent {0} (4 / 5) = {1} := by
  ext w
  fin_cases w <;> simp [Frame.probEvent, mass, fig2_P0, fig2_P1] <;> norm_num

theorem fig2_not_simpleTrust : ¬ SimpleTrust half fig2 := by
  intro h
  have hint : ({0} : Finset (Fin 2)) ∩ {1} = ∅ := by ext w; fin_cases w <;> simp
  have := h {0} (4 / 5) (by rw [fig2_probEvent]; norm_num [mass, half])
  rw [fig2_probEvent, hint] at this
  norm_num [mass, half] at this

theorem fig2_condProbEvent : fig2.condProbEvent {0} univ (4 / 5) = {1} := by
  ext w
  fin_cases w <;>
    simp [Frame.condProbEvent, mass, Fin.sum_univ_two, fig2_P0, fig2_P1] <;> norm_num

theorem fig2_not_trust : ¬ Trust half fig2 := by
  intro h
  have hint : ({0} : Finset (Fin 2)) ∩ (univ ∩ {1}) = ∅ := by ext w; fin_cases w <;> simp
  have := h {0} univ (4 / 5) (by rw [fig2_condProbEvent, univ_inter]; norm_num [mass, half])
  rw [fig2_condProbEvent, hint, univ_inter] at this
  norm_num [mass, half] at this

/-! ## Probe 4: a vertex deferrer — Total Trust at `δ_a` on Figure 3 fails

Degenerate-deferrer check: with `π = (1, 0)` the only candidate is `P_a = (0.9, 0.1) ≠ π`, so
`π ∉ convexHull C_π` and Lemma 7.2 (`TotalTrust.mem_convexHull_cands`) refutes Total Trust.
At a vertex the definitions still bite: the theorem does not become trivially true. -/

/-- The point mass on world `a`. -/
def vert0 : Fin 2 → ℝ := ![1, 0]

theorem vert0_mem : vert0 ∈ stdSimplex ℝ (Fin 2) :=
  simplex2 _ _ (by norm_num) (by norm_num) (by norm_num)

theorem fig3_cands_vert0 : fig3.cands vert0 = {fig3.P 0} := by
  ext σ
  rw [Frame.mem_cands]
  constructor
  · rintro ⟨w, hw, rfl⟩
    fin_cases w
    · simp
    · simp [vert0] at hw
  · intro h
    rw [mem_singleton] at h
    exact ⟨0, by norm_num [vert0], h.symm⟩

theorem fig3_not_totalTrust_vert0 : ¬ TotalTrust vert0 fig3 := by
  intro h
  have hmem := h.mem_convexHull_cands vert0_mem
  rw [fig3_cands_vert0, coe_singleton, convexHull_singleton, Set.mem_singleton_iff] at hmem
  have := congrFun hmem 0
  rw [fig3_P0] at this
  norm_num [vert0] at this

end

end Cleanroom.Found.LitDdbFrames.AuditR1
