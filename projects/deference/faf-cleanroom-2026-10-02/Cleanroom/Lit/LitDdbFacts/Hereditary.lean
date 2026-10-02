import Cleanroom.Lit.LitDdbFacts.Geometry

/-!
# Hereditary deference (fn 56) and positive access (§5 l. 392)

Package `lit-ddb-facts`, Targets 14 and 16. Total Trust, Value and Reflection pass from `π` to
every candidate of `π` (fn 56: "`π` reflects/values/totally-trusts the frame only if every
`P_i ∈ W_π` does"); New Reflection does not (the witness `nonHered4` is in `Examples.lean`).
Positive access (DDB's paraphrase at §5 l. 392 of Dorst 2020a, Fact 8.2; the Lean proves the
paraphrase — ATTRIBUTION-UNVETTED that it is Dorst's exact statement): a candidate of a valuing deferrer that is
certain of `q` is certain that the expert is certain of `q` — derived here from Simple Trust,
converting DDB's (b) citation to (a).
-/

namespace Cleanroom.Lit.LitDdbFacts

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Target 14(i): Total Trust, Value and Reflection are hereditary -/

/-- **Fn 56, Total Trust.** If `π` totally trusts the frame, so does every candidate `ρ ∈ C_π`:
under the hull condition `ρ ∈ C_ρ` (`Frame.mem_cands_self_of_hull`), so `ρ ∈ hull C_ρ`, and
`C_ρ ⊆ C_π` (`Frame.cands_subset_of_hull`) makes every candidate of `ρ` modestly informed.
Source: [[Deference Done Better]] fn 56; item 071
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` -/
theorem totalTrust_cands {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : TotalTrust π F) : ∀ ρ ∈ F.cands π, TotalTrust ρ F := by
  intro ρ hρ
  have hρs := F.mem_stdSimplex_of_mem_cands hρ
  have hmi := h.hullAndModestlyInformed hπ
  have hdec := hmi.decompOver
  rw [totalTrust_iff_hullAndModestlyInformed hρs F]
  refine ⟨subset_convexHull ℝ _ (mem_coe.2 (F.mem_cands_self_of_hull hπ hmi.1 hdec hρ)), ?_⟩
  intro σ hσ
  exact hmi.2 σ (F.cands_subset_of_hull hπ hmi.1 hdec hρ hσ)

/-- **Fn 56, Value.** If `π` values the frame, so does every candidate (through Theorem 2.2).
Source: [[Deference Done Better]] fn 56
Kind: C
Fidelity: exact
Hyps: (a) `hπ` -/
theorem value_cands {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W} (h : Value π F) :
    ∀ ρ ∈ F.cands π, Value ρ F := fun ρ hρ =>
  (value_iff_totalTrust (F.mem_stdSimplex_of_mem_cands hρ) F).2
    (totalTrust_cands hπ ((value_iff_totalTrust hπ F).1 h) ρ hρ)

/-- **Fn 56, Reflection.** If `π` reflects the frame, so does every candidate: each is immodest
(Target 1), hence reflects trivially (its only candidate is itself).
Source: [[Deference Done Better]] fn 56
Kind: C
Fidelity: exact
Hyps: (a) nonnegativity of `π` -/
theorem reflects_cands {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} (h : Reflects π F) :
    ∀ ρ ∈ F.cands π, Reflects ρ F := fun ρ hρ =>
  reflects_self_of_selfMass_eq_one F (F.mem_stdSimplex_of_mem_cands hρ)
    (selfMass_eq_one_of_reflects hπ h hρ)

/-! ## Target 16: positive access -/

/-- **Positive access** of a distribution `ρ` on the frame: whenever `ρ(q) = 1`,
`ρ(P(q) = 1) = 1` — certainty of `q` comes with certainty that the expert is certain of `q`.
Source: [[Deference Done Better]] §5 l. 392 (Dorst 2020a Fact 8.2 as paraphrased there)
Kind: D
Fidelity: exact -/
def PositiveAccess (F : Frame W) (ρ : W → ℝ) : Prop :=
  ∀ q : Finset W, mass ρ q = 1 → mass ρ (univ.filter (fun w => mass (F.P w) q = 1)) = 1

/-- **Simple Trust gives positive access.** If `ρ(q) = 1` but some support world `w₀` has
`s := P_{w₀}(q) < 1`, the symmetric form of Simple Trust at `(qᶜ, 1 − s)` reads
`(1 − s) · ρ(P(q) ≤ s) ≤ ρ(qᶜ ∧ P(q) ≤ s) ≤ ρ(qᶜ) = 0` with `ρ(P(q) ≤ s) ≥ ρ(w₀) > 0`.
Source: [[Deference Done Better]] §5 l. 392 (Dorst 2020a Fact 8.2 as paraphrased there;
derived, not cited)
Kind: P
Fidelity: exact
Hyps: (a) `hρ : ρ ∈ stdSimplex ℝ W` -/
theorem positiveAccess_of_simpleTrust {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) {F : Frame W}
    (h : SimpleTrust ρ F) : PositiveAccess F ρ := by
  intro q hq
  have key : ∀ w, 0 < ρ w → mass (F.P w) q = 1 := by
    intro w₀ hw₀
    by_contra hne
    have hlt : mass (F.P w₀) q < 1 := lt_of_le_of_ne (mass_le_one (F.P_mem w₀) q) hne
    have hmem : w₀ ∈ F.probEvent (univ \ q) (1 - mass (F.P w₀) q) := by
      rw [Frame.probEvent, mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have := mass_inter_add_mass_sdiff (F.P w₀) univ q
      rw [univ_inter, mass_univ (F.P_mem w₀)] at this
      linarith
    have hpos : 0 < mass ρ (F.probEvent (univ \ q) (1 - mass (F.P w₀) q)) :=
      mass_pos_of_mem hρ.1 hmem hw₀
    have hst := h (univ \ q) (1 - mass (F.P w₀) q) hpos
    have h0 : mass ρ (univ \ q) = 0 := by
      have := mass_inter_add_mass_sdiff ρ univ q
      rw [univ_inter, mass_univ hρ, hq] at this
      linarith
    have hle : mass ρ ((univ \ q) ∩ F.probEvent (univ \ q) (1 - mass (F.P w₀) q)) ≤ 0 := by
      rw [← h0]
      exact mass_mono hρ.1 inter_subset_left
    have : 0 < (1 - mass (F.P w₀) q) * mass ρ (F.probEvent (univ \ q) (1 - mass (F.P w₀) q)) :=
      mul_pos (by linarith) hpos
    linarith
  have hsub : supp ρ ⊆ univ.filter (fun w => mass (F.P w) q = 1) := by
    intro w hw
    rw [mem_supp] at hw
    rw [mem_filter]
    exact ⟨mem_univ _, key w hw⟩
  refine le_antisymm (mass_le_one hρ _) ?_
  have h1 := mass_mono hρ.1 hsub
  rw [mass_supp hρ] at h1
  exact h1

/-- **Target 16.** If `π` values the frame, every candidate `ρ ∈ C_π` has positive access
(the paper's claim is about the expert's opinions, i.e. the candidates): `ρ` totally trusts
the frame (fn 56), hence simply trusts it, hence has positive access.
Source: [[Deference Done Better]] §5 l. 392 ("to value an expert, their opinions must obey
positive access"); Fact 8.2 as paraphrased at l. 392, converted from (b) to (a); item 078
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` -/
theorem positiveAccess_of_value {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : Value π F) : ∀ ρ ∈ F.cands π, PositiveAccess F ρ := fun ρ hρ =>
  positiveAccess_of_simpleTrust (F.mem_stdSimplex_of_mem_cands hρ)
    (totalTrust_cands hπ ((value_iff_totalTrust hπ F).1 h) ρ hρ).simpleTrust

/-- The deferrer's own positive access under Value (a different, weaker-looking claim than the
paper's, which is about the candidates; recorded so the two are not confused).
Source: [[Deference Done Better]] §5 l. 392 (variant)
Kind: L
Fidelity: variant: about the deferrer `π`, not the expert's opinions
Hyps: (a) `hπ` -/
theorem positiveAccess_self_of_value {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : Value π F) : PositiveAccess F π :=
  positiveAccess_of_simpleTrust hπ ((value_iff_totalTrust hπ F).1 h).simpleTrust

end

end Cleanroom.Lit.LitDdbFacts
