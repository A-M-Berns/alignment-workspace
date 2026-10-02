import Cleanroom.Lit.LitDdbFacts.Examples

/-!
# Figure 5: `F₁` is totally trusted (with explicit weights), `F₂` by no deferrer

Package `lit-ddb-facts`, Target 13. `F₁` (rows `(2/4, 1/4, 1/4)`, `(5/16, 8/16, 3/16)`,
`(1/4, 1/4, 2/4)`) with the uniform `π`: the hull condition with the mandate's weights, verified
here — `π = ¼ P₁ + ⅓ P₂ + 5/12 P₃`, `P₁ = 4/13 δ₁ + 4/13 P₂ + 5/13 P₃`,
`P₂ = ⅓ δ₂ + 7/12 P₁ + 1/12 P₃`, `P₃ = 4/11 δ₃ + 4/11 P₂ + 3/11 P₁` — hence Total Trust and Value,
and `F₁` validates Total Trust. `F₂` (`lit-ddb-frames`' `fig5F2`) is totally trusted by *no*
distribution: if `π(w₂) > 0` its candidate `P₂` is not modestly informed; if `π(w₂) = 0` its
candidates lie on the line `ρ(w₂) = ¼`, which `π` does not.
-/

namespace Cleanroom.Lit.LitDdbFacts.Examples

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples
  Cleanroom.Lit.LitDdbFacts

noncomputable section

/-- Figure 5's `F₁`.
Source: [[Deference Done Better]] §4 l. 316 (Figure 5)
Kind: D
Fidelity: exact -/
def fig5F1 : Frame (Fin 3) :=
  mk3 ![2 / 4, 1 / 4, 1 / 4] ![5 / 16, 8 / 16, 3 / 16] ![1 / 4, 1 / 4, 2 / 4]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- `F₁`'s rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig5F1_P : fig5F1.P 0 = ![2 / 4, 1 / 4, 1 / 4] ∧ fig5F1.P 1 = ![5 / 16, 8 / 16, 3 / 16] ∧
    fig5F1.P 2 = ![1 / 4, 1 / 4, 2 / 4] := ⟨rfl, rfl, rfl⟩

/-- `F₁`'s rows are pairwise distinct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig5F1_ne : (![2 / 4, 1 / 4, 1 / 4] : Fin 3 → ℝ) ≠ ![5 / 16, 8 / 16, 3 / 16] ∧
    (![2 / 4, 1 / 4, 1 / 4] : Fin 3 → ℝ) ≠ ![1 / 4, 1 / 4, 2 / 4] ∧
    (![5 / 16, 8 / 16, 3 / 16] : Fin 3 → ℝ) ≠ ![1 / 4, 1 / 4, 2 / 4] := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    · have := congrFun h 0; norm_num at this

/-- `F₁`'s cells are singletons.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig5F1_cell : fig5F1.cell ![2 / 4, 1 / 4, 1 / 4] = {0} ∧
    fig5F1.cell ![5 / 16, 8 / 16, 3 / 16] = {1} ∧ fig5F1.cell ![1 / 4, 1 / 4, 2 / 4] = {2} := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · ext w
      fin_cases w <;> simp [Frame.mem_cell, fig5F1_P] <;> norm_num

/-- `F₁`'s self-cell masses are all `½`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig5F1_selfMass : fig5F1.selfMass (fig5F1.P 0) = 1 / 2 ∧
    fig5F1.selfMass (fig5F1.P 1) = 1 / 2 ∧ fig5F1.selfMass (fig5F1.P 2) = 1 / 2 := by
  obtain ⟨hc0, hc1, hc2⟩ := fig5F1_cell
  refine ⟨?_, ?_, ?_⟩
  · rw [Frame.selfMass, fig5F1_P.1, hc0, mass, sum_singleton]; norm_num
  · rw [Frame.selfMass, fig5F1_P.2.1, hc1, mass, sum_singleton]; norm_num
  · rw [Frame.selfMass, fig5F1_P.2.2, hc2, mass, sum_singleton]; norm_num [vec3_two]

/-- `F₁`'s informed experts are the three vertices.
Source: [[Deference Done Better]] §4 l. 323 ("`P̂_w` is certain it's at `w`")
Kind: L
Fidelity: n/a -/
theorem fig5F1_informed : fig5F1.informed (fig5F1.P 0) = ![1, 0, 0] ∧
    fig5F1.informed (fig5F1.P 1) = ![0, 1, 0] ∧ fig5F1.informed (fig5F1.P 2) = ![0, 0, 1] := by
  obtain ⟨hs0, hs1, hs2⟩ := fig5F1_selfMass
  refine ⟨?_, ?_, ?_⟩
  · funext w
    unfold Frame.informed
    rw [hs0]
    fin_cases w <;> simp [fig5F1_P, vec3_two, fin3_mk_two] <;> norm_num
  · funext w
    unfold Frame.informed
    rw [hs1]
    fin_cases w <;> simp [fig5F1_P, vec3_two, fin3_mk_two] <;> norm_num
  · funext w
    unfold Frame.informed
    rw [hs2]
    fin_cases w <;> simp [fig5F1_P, vec3_two, fin3_mk_two] <;> norm_num

/-- Candidates of a fully supported deferrer on a three-world frame.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cands_eq_triple (F : Frame (Fin 3)) {ρ : Fin 3 → ℝ} (h0 : 0 < ρ 0) (h1 : 0 < ρ 1)
    (h2 : 0 < ρ 2) : F.cands ρ = {F.P 0, F.P 1, F.P 2} := by
  ext σ
  rw [Frame.mem_cands]
  constructor
  · rintro ⟨w, _, rfl⟩
    fin_cases w <;> simp
  · intro hσ
    simp only [mem_insert, mem_singleton] at hσ
    rcases hσ with rfl | rfl | rfl
    · exact ⟨0, h0, rfl⟩
    · exact ⟨1, h1, rfl⟩
    · exact ⟨2, h2, rfl⟩

/-- `C_i⁻` on `F₁` for each row: the other two rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig5F1_candsMinus : fig5F1.candsMinus (fig5F1.P 0) = {fig5F1.P 1, fig5F1.P 2} ∧
    fig5F1.candsMinus (fig5F1.P 1) = {fig5F1.P 0, fig5F1.P 2} ∧
    fig5F1.candsMinus (fig5F1.P 2) = {fig5F1.P 0, fig5F1.P 1} := by
  obtain ⟨h01, h02, h12⟩ := fig5F1_ne
  have hc : ∀ i : Fin 3, fig5F1.cands (fig5F1.P i) = {fig5F1.P 0, fig5F1.P 1, fig5F1.P 2} := by
    intro i
    apply cands_eq_triple <;> fin_cases i <;> norm_num [fig5F1_P, vec3_two, fin3_mk_two]
  refine ⟨?_, ?_, ?_⟩
  · rw [Frame.candsMinus, hc]
    ext σ
    simp only [mem_erase, mem_insert, mem_singleton, fig5F1_P]
    constructor
    · rintro ⟨hne, h | h | h⟩
      · exact absurd h hne
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · exact ⟨h01.symm, Or.inr (Or.inl rfl)⟩
      · exact ⟨h02.symm, Or.inr (Or.inr rfl)⟩
  · rw [Frame.candsMinus, hc]
    ext σ
    simp only [mem_erase, mem_insert, mem_singleton, fig5F1_P]
    constructor
    · rintro ⟨hne, h | h | h⟩
      · exact Or.inl h
      · exact absurd h hne
      · exact Or.inr h
    · rintro (rfl | rfl)
      · exact ⟨h01, Or.inl rfl⟩
      · exact ⟨h12.symm, Or.inr (Or.inr rfl)⟩
  · rw [Frame.candsMinus, hc]
    ext σ
    simp only [mem_erase, mem_insert, mem_singleton, fig5F1_P]
    constructor
    · rintro ⟨hne, h | h | h⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hne
    · rintro (rfl | rfl)
      · exact ⟨h02, Or.inl rfl⟩
      · exact ⟨h12, Or.inr (Or.inl rfl)⟩

/-- **Target 13(i), the weights verified.** Every row of `F₁` is modestly informed (unguarded,
hence guarded) with the mandate's weights: `P₁ = 4/13 δ₁ + 4/13 P₂ + 5/13 P₃`,
`P₂ = ⅓ δ₂ + 7/12 P₁ + 1/12 P₃`, `P₃ = 4/11 δ₃ + 4/11 P₂ + 3/11 P₁`.
Source: [[Deference Done Better]] §4 l. 316, Figure 5 (bottom row); mandate Target 13
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem fig5F1_modestlyInformedU : ∀ i, ModestlyInformedU fig5F1 (fig5F1.P i) := by
  obtain ⟨hi0, hi1, hi2⟩ := fig5F1_informed
  obtain ⟨hcm0, hcm1, hcm2⟩ := fig5F1_candsMinus
  intro i
  fin_cases i
  · show ModestlyInformedU fig5F1 (fig5F1.P 0)
    unfold ModestlyInformedU
    rw [hcm0, hi0]
    exact mem_hull_of_comb3 (x := ![1, 0, 0]) (y := fig5F1.P 1) (z := fig5F1.P 2)
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (by simp)) (Set.mem_insert_of_mem _ (by simp))
      (by norm_num : (0 : ℝ) ≤ 4 / 13) (by norm_num : (0 : ℝ) ≤ 4 / 13)
      (by norm_num : (0 : ℝ) ≤ 5 / 13) (by norm_num)
      (by ext w; fin_cases w <;> norm_num [fig5F1_P, vec3_two])
  · show ModestlyInformedU fig5F1 (fig5F1.P 1)
    unfold ModestlyInformedU
    rw [hcm1, hi1]
    exact mem_hull_of_comb3 (x := ![0, 1, 0]) (y := fig5F1.P 0) (z := fig5F1.P 2)
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (by simp)) (Set.mem_insert_of_mem _ (by simp))
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (0 : ℝ) ≤ 7 / 12)
      (by norm_num : (0 : ℝ) ≤ 1 / 12) (by norm_num)
      (by ext w; fin_cases w <;> norm_num [fig5F1_P, vec3_two])
  · show ModestlyInformedU fig5F1 (fig5F1.P 2)
    unfold ModestlyInformedU
    rw [hcm2, hi2]
    exact mem_hull_of_comb3 (x := ![0, 0, 1]) (y := fig5F1.P 1) (z := fig5F1.P 0)
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (by simp)) (Set.mem_insert_of_mem _ (by simp))
      (by norm_num : (0 : ℝ) ≤ 4 / 11) (by norm_num : (0 : ℝ) ≤ 4 / 11)
      (by norm_num : (0 : ℝ) ≤ 3 / 11) (by norm_num)
      (by ext w; fin_cases w <;> norm_num [fig5F1_P, vec3_two])

/-- **Target 13(i).** The uniform `π` satisfies the hull condition on `F₁`:
`π = ¼ P₁ + ⅓ P₂ + 5/12 P₃` and every candidate is modestly informed.
Source: [[Deference Done Better]] §4 l. 313 ("the uniform distribution … totally trusts the
first frame"); mandate Target 13
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig5F1_hull : HullAndModestlyInformed π5 fig5F1 := by
  obtain ⟨hs0, hs1, hs2⟩ := fig5F1_selfMass
  have hcands : fig5F1.cands π5 = {fig5F1.P 0, fig5F1.P 1, fig5F1.P 2} :=
    cands_eq_triple fig5F1 (by norm_num [π5]) (by norm_num [π5]) (by norm_num [π5, vec3_two])
  refine ⟨?_, ?_⟩
  · rw [hcands]
    exact mem_hull_of_comb3 (x := fig5F1.P 0) (y := fig5F1.P 1) (z := fig5F1.P 2)
      (by simp) (by simp) (by simp)
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (0 : ℝ) ≤ 5 / 12) (by norm_num)
      (by ext w; fin_cases w <;> norm_num [π5, fig5F1_P, vec3_two])
  · intro ρ hρ
    rw [hcands] at hρ
    simp only [mem_insert, mem_singleton] at hρ
    rcases hρ with rfl | rfl | rfl
    · exact ⟨by rw [hs0]; norm_num, fig5F1_modestlyInformedU 0⟩
    · exact ⟨by rw [hs1]; norm_num, fig5F1_modestlyInformedU 1⟩
    · exact ⟨by rw [hs2]; norm_num, fig5F1_modestlyInformedU 2⟩

/-- **Target 13(i).** The uniform `π` totally trusts and values `F₁` (via Theorem 7.6).
Source: [[Deference Done Better]] §4 l. 313, Figure 5
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig5F1_totalTrust_value : TotalTrust π5 fig5F1 ∧ Value π5 fig5F1 :=
  ⟨(totalTrust_iff_hullAndModestlyInformed π5_mem fig5F1).2 fig5F1_hull,
    (value_iff_totalTrust π5_mem fig5F1).2
      ((totalTrust_iff_hullAndModestlyInformed π5_mem fig5F1).2 fig5F1_hull)⟩

/-- **Target 13(i).** `F₁` validates Total Trust (Corollary 4.5 with the same weights).
Source: [[Deference Done Better]] §4 l. 363 (Corollary 4.5), Figure 5
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig5F1_validates_totalTrust : fig5F1.Validates TotalTrust :=
  (validates_totalTrust_iff fig5F1).2 fig5F1_modestlyInformedU

/-- **Target 13(ii).** `F₂` is totally trusted by no distribution: with `π(w₂) > 0`, `P₂` is a
candidate that is not modestly informed (`fig5F2_not_modestlyInformed`); with `π(w₂) = 0`,
the candidates are among `P₁, P₃`, whose hull lies on the line `ρ(w₂) = ¼`, but Lemma 7.2 puts
`π` in that hull. Strengthens `fig5F2_not_totalTrust` (uniform `π` only) to the paper's claim.
Source: [[Deference Done Better]] §4 l. 313 ("there are no probability distributions that
totally trust the second"); mandate Target 13
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ (Fin 3)` -/
theorem fig5F2_no_totalTrust : ∀ π ∈ stdSimplex ℝ (Fin 3), ¬ TotalTrust π fig5F2 := by
  intro π hπ h
  rcases (hπ.1 1).lt_or_eq with hpos | hzero
  · exact fig5F2_not_modestlyInformed
      ((h.hullAndModestlyInformed hπ).2 _ (fig5F2.P_mem_cands hpos))
  · have hhull := h.mem_convexHull_cands hπ
    have hsub : (↑(fig5F2.cands π) : Set (Fin 3 → ℝ)) ⊆ {ρ : Fin 3 → ℝ | ρ 1 = 1 / 4} := by
      intro σ hσ
      rw [mem_coe, Frame.mem_cands] at hσ
      obtain ⟨w, hw, rfl⟩ := hσ
      fin_cases w
      · simp [fig5F2_P.1]
      · exfalso
        have hw' : 0 < π 1 := hw
        rw [← hzero] at hw'
        exact lt_irrefl _ hw'
      · show fig5F2.P 2 ∈ {ρ : Fin 3 → ℝ | ρ 1 = 1 / 4}
        simp [fig5F2_P.2.2]
    have hconv : Convex ℝ {ρ : Fin 3 → ℝ | ρ 1 = 1 / 4} :=
      convex_hyperplane ⟨fun a b => rfl, fun c a => rfl⟩ _
    have := convexHull_min hsub hconv hhull
    rw [Set.mem_setOf_eq] at this
    rw [this] at hzero
    norm_num at hzero

end

end Cleanroom.Lit.LitDdbFacts.Examples
