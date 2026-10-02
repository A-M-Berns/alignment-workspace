import Cleanroom.Found.LitDdbFrames.Hull

/-!
# Self-cell dominance, Lemma 7.4, and the strict inequality (**) of Lemma 7.5

Package `lit-ddb-frames`, Target 15. Under the hull condition every candidate is the candidate
most confident of its own cell (`mass_cell_le_selfMass_of_hull`), and *strictly* so against every
other candidate (`mass_cell_lt_selfMass_of_hull`, DDB's inequality (**) in Lemma 7.5). Lemma 7.4
(no candidate lies in the hull of `C_ρ⁻`; every self-weight is positive) sits between them.

DDB prove 7.4 by applying the whole cycle to each candidate as a deferrer and then a delicate
conditional-Trust argument. Here all three facts follow from the maximal-set lemma of `Hull.lean`
alone, so 7.4 is kind P rather than a composition through the cycle.
-/

namespace Cleanroom.Found.LitDdbFrames

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **Self-cell dominance.** Under the hull condition, no candidate gives `ρ`'s cell more
probability than `ρ` itself: `σ(P = ρ) ≤ ρ(P = ρ)` for all `σ, ρ ∈ C_π`. Proof: if the maximum
of `τ ↦ τ(P = ρ)` over `C_π` exceeded `ρ(P = ρ)`, every maximiser `τ ≠ ρ` would decompose (modest
informedness) over its informed self — which has mass `0` on `ρ`'s cell — and other candidates
no higher than it, contradicting the maximal-set lemma.
Source: [[Deference Done Better]] App. B Lemma 7.4 proof l. 577 (the pointwise claim there
derived from Simple Trust)
Kind: P
Fidelity: variant: cell-level form derived from the hull condition rather than from Trust
Hyps: (a) none beyond the stated ones -/
theorem Frame.mass_cell_le_selfMass_of_hull (F : Frame W) {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    (h : HullAndModestlyInformed π F) {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) {σ : W → ℝ}
    (hσ : σ ∈ F.cands π) : mass σ (F.cell ρ) ≤ F.selfMass ρ := by
  have hdec := h.decompOver
  obtain ⟨m, hm, hmax⟩ := (F.cands π).exists_max_image (fun τ => mass τ (F.cell ρ))
    (F.cands_nonempty hπ)
  have hρt : F.selfMass ρ ≤ mass m (F.cell ρ) := hmax ρ hρ
  have htpos : 0 < mass m (F.cell ρ) :=
    lt_of_lt_of_le (F.selfMass_pos_of_hull hπ h.1 hdec hρ) hρt
  suffices hρM : F.selfMass ρ = mass m (F.cell ρ) by rw [hρM]; exact hmax σ hσ
  by_contra hne
  have hρlt : F.selfMass ρ < mass m (F.cell ρ) := lt_of_le_of_ne hρt hne
  set M := (F.cands π).filter (fun τ => mass τ (F.cell ρ) = mass m (F.cell ρ)) with hM
  have hMne : M.Nonempty := ⟨m, mem_filter.2 ⟨hm, rfl⟩⟩
  refine no_selfless_maximal_set M hMne (ind (F.cell ρ)) (mass m (F.cell ρ)) ?_ ?_
  · intro τ hτ; rw [E_ind]; exact (mem_filter.1 hτ).2
  · intro τ hτ
    obtain ⟨hτc, hτt⟩ := mem_filter.1 hτ
    have hτne : τ ≠ ρ := by
      rintro rfl
      exact hρlt.ne hτt
    have hmi := (h.2 τ hτc).2
    rw [← coe_insert] at hmi
    obtain ⟨c, hc₀, hc₁, hs⟩ := Finset.mem_convexHull'.1 hmi
    refine ⟨_, c, hc₀, hc₁, hs, ?_⟩
    intro y hy _
    rw [E_ind]
    rcases mem_insert.1 hy with rfl | hyC
    · rw [F.mass_informed_cell_of_ne hτne]
      exact ⟨htpos.le, fun e => absurd e htpos.ne⟩
    · obtain ⟨hne', hyc⟩ := Frame.mem_candsMinus.1 hyC
      have hyπ : y ∈ F.cands π := F.cands_subset_of_hull hπ h.1 hdec hτc hyc
      exact ⟨hmax y hyπ, fun e => ⟨mem_filter.2 ⟨hyπ, e⟩, hne'⟩⟩

/-- **Target 15 (Lemma 7.4).** Under the hull condition no candidate lies in the convex hull of
the other candidates it leaves open: `ρ ∉ convexHull C_ρ⁻`. Proof: otherwise the set of
candidates giving `ρ`'s cell its maximal mass `ρ(P = ρ)` (dominance) would be selfless —
`ρ` decomposes over `C_ρ⁻`, every other maximiser over an informed self of mass `0` on the cell —
contradicting the maximal-set lemma.
Source: [[Deference Done Better]] App. B Lemma 7.4 l. 575
Kind: P
Fidelity: exact (DDB's "`λ_ii > 0` in every decomposition" is `selfWeight_pos_of_hull`)
Hyps: (a) none beyond the stated ones -/
theorem Frame.not_mem_convexHull_candsMinus_of_hull (F : Frame W) {π : W → ℝ}
    (hπ : π ∈ stdSimplex ℝ W) (h : HullAndModestlyInformed π F) {ρ : W → ℝ}
    (hρ : ρ ∈ F.cands π) : ρ ∉ convexHull ℝ (↑(F.candsMinus ρ) : Set (W → ℝ)) := by
  intro hmem
  have hdec := h.decompOver
  have hcpos : 0 < F.selfMass ρ := F.selfMass_pos_of_hull hπ h.1 hdec hρ
  set M := (F.cands π).filter (fun τ => mass τ (F.cell ρ) = F.selfMass ρ) with hM
  have hMne : M.Nonempty := ⟨ρ, mem_filter.2 ⟨hρ, rfl⟩⟩
  refine no_selfless_maximal_set M hMne (ind (F.cell ρ)) (F.selfMass ρ) ?_ ?_
  · intro τ hτ; rw [E_ind]; exact (mem_filter.1 hτ).2
  · intro τ hτ
    obtain ⟨hτc, hτt⟩ := mem_filter.1 hτ
    by_cases hτρ : τ = ρ
    · obtain ⟨μ, hμ₀, hμ₁, hs⟩ := Finset.mem_convexHull'.1 hmem
      refine ⟨_, μ, hμ₀, hμ₁, by rw [hτρ]; exact hs, ?_⟩
      intro y hy _
      rw [E_ind]
      obtain ⟨hne, hyc⟩ := Frame.mem_candsMinus.1 hy
      have hyπ := F.cands_subset_of_hull hπ h.1 hdec hρ hyc
      exact ⟨F.mass_cell_le_selfMass_of_hull hπ h hρ hyπ,
        fun e => ⟨mem_filter.2 ⟨hyπ, e⟩, by rw [hτρ]; exact hne⟩⟩
    · have hmi := (h.2 τ hτc).2
      rw [← coe_insert] at hmi
      obtain ⟨c, hc₀, hc₁, hs⟩ := Finset.mem_convexHull'.1 hmi
      refine ⟨_, c, hc₀, hc₁, hs, ?_⟩
      intro y hy _
      rw [E_ind]
      rcases mem_insert.1 hy with rfl | hyC
      · rw [F.mass_informed_cell_of_ne hτρ]
        exact ⟨hcpos.le, fun e => absurd e hcpos.ne⟩
      · obtain ⟨hne, hyc⟩ := Frame.mem_candsMinus.1 hyC
        have hyπ := F.cands_subset_of_hull hπ h.1 hdec hτc hyc
        exact ⟨F.mass_cell_le_selfMass_of_hull hπ h hρ hyπ,
          fun e => ⟨mem_filter.2 ⟨hyπ, e⟩, hne⟩⟩

/-- In any decomposition of a point `σ ∉ convexHull C_σ⁻` over `{P̂_σ} ∪ C_σ⁻`, the informed
self is not itself in `C_σ⁻` and carries positive weight.
Source: none: infrastructure (Target 15)
Kind: L
Fidelity: n/a -/
theorem Frame.informed_weight_pos (F : Frame W) {σ : W → ℝ}
    (hnot : σ ∉ convexHull ℝ (↑(F.candsMinus σ) : Set (W → ℝ))) {c : (W → ℝ) → ℝ}
    (hc₀ : ∀ y ∈ insert (F.informed σ) (F.candsMinus σ), 0 ≤ c y)
    (hc₁ : ∑ y ∈ insert (F.informed σ) (F.candsMinus σ), c y = 1)
    (hs : ∑ y ∈ insert (F.informed σ) (F.candsMinus σ), c y • y = σ) :
    F.informed σ ∉ F.candsMinus σ ∧ 0 < c (F.informed σ) := by
  have hnotin : F.informed σ ∉ F.candsMinus σ := by
    intro hin
    rw [insert_eq_of_mem hin] at hc₀ hc₁ hs
    exact hnot (Finset.mem_convexHull'.2 ⟨c, hc₀, hc₁, hs⟩)
  refine ⟨hnotin, ?_⟩
  rcases (hc₀ _ (mem_insert_self _ _)).lt_or_eq with hpos | hzero
  · exact hpos
  exfalso
  rw [sum_insert hnotin, ← hzero, zero_add] at hc₁
  rw [sum_insert hnotin, ← hzero, zero_smul, zero_add] at hs
  exact hnot (Finset.mem_convexHull'.2 ⟨c, fun y hy => hc₀ y (mem_insert_of_mem hy), hc₁, hs⟩)

/-- **Target 15 in DDB's phrasing.** Under the hull condition, every decomposition
`ρ = λ_ρρ P̂_ρ + ∑_{σ ∈ C_ρ⁻} λ_ρσ σ` of a candidate has `λ_ρρ > 0`.
Source: [[Deference Done Better]] App. B Lemma 7.4 l. 575
Kind: C
Fidelity: exact
Hyps: (a) none beyond the stated ones -/
theorem Frame.selfWeight_pos_of_hull (F : Frame W) {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    (h : HullAndModestlyInformed π F) {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) {c : (W → ℝ) → ℝ}
    (hc₀ : ∀ y ∈ insert (F.informed ρ) (F.candsMinus ρ), 0 ≤ c y)
    (hc₁ : ∑ y ∈ insert (F.informed ρ) (F.candsMinus ρ), c y = 1)
    (hs : ∑ y ∈ insert (F.informed ρ) (F.candsMinus ρ), c y • y = ρ) :
    0 < c (F.informed ρ) :=
  (F.informed_weight_pos (F.not_mem_convexHull_candsMinus_of_hull hπ h hρ) hc₀ hc₁ hs).2

/-- **Inequality (**) of Lemma 7.5, strict self-cell dominance.** Under the hull condition,
distinct candidates satisfy `σ(P = ρ) < ρ(P = ρ)`: `σ` decomposes with positive weight on its
informed self (Lemma 7.4), which has mass `0` on `ρ`'s cell, and the rest is a sub-convex
combination of candidates each with mass at most `ρ(P = ρ)` (dominance).
Source: [[Deference Done Better]] App. B Lemma 7.5 l. 601–610 (inequality (**))
Kind: P
Fidelity: exact
Hyps: (a) none beyond the stated ones -/
theorem Frame.mass_cell_lt_selfMass_of_hull (F : Frame W) {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    (h : HullAndModestlyInformed π F) {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) {σ : W → ℝ}
    (hσ : σ ∈ F.cands π) (hne : σ ≠ ρ) : mass σ (F.cell ρ) < F.selfMass ρ := by
  have hdec := h.decompOver
  have hcpos : 0 < F.selfMass ρ := F.selfMass_pos_of_hull hπ h.1 hdec hρ
  have hmi := (h.2 σ hσ).2
  rw [← coe_insert] at hmi
  obtain ⟨c, hc₀, hc₁, hs⟩ := Finset.mem_convexHull'.1 hmi
  obtain ⟨hnotin, hwpos⟩ :=
    F.informed_weight_pos (F.not_mem_convexHull_candsMinus_of_hull hπ h hσ) hc₀ hc₁ hs
  have hmass : mass σ (F.cell ρ) = ∑ y ∈ F.candsMinus σ, c y * mass y (F.cell ρ) := by
    conv_lhs => rw [← hs]
    rw [mass_sum_left, sum_insert hnotin, F.mass_informed_cell_of_ne hne, mul_zero, zero_add]
  rw [sum_insert hnotin] at hc₁
  have hle : ∑ y ∈ F.candsMinus σ, c y * mass y (F.cell ρ) ≤
      ∑ y ∈ F.candsMinus σ, c y * F.selfMass ρ := by
    apply sum_le_sum
    intro y hy
    obtain ⟨_, hyc⟩ := Frame.mem_candsMinus.1 hy
    have hyπ := F.cands_subset_of_hull hπ h.1 hdec hσ hyc
    exact mul_le_mul_of_nonneg_left (F.mass_cell_le_selfMass_of_hull hπ h hρ hyπ)
      (hc₀ y (mem_insert_of_mem hy))
  rw [← sum_mul] at hle
  have hrest : ∑ y ∈ F.candsMinus σ, c y = 1 - c (F.informed σ) := by linarith
  rw [hrest] at hle
  rw [hmass]
  have hprod := mul_pos hwpos hcpos
  have e : (1 - c (F.informed σ)) * F.selfMass ρ =
      F.selfMass ρ - c (F.informed σ) * F.selfMass ρ := by ring
  linarith

end

end Cleanroom.Found.LitDdbFrames
