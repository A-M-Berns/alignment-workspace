import Cleanroom.Trust.TtFiniteFrames.Blackwell
import Cleanroom.Trust.TtFiniteFrames.Geanakoplos
import Cleanroom.Found.LitDdbFrames.Strategies

/-!
# The strategy bridge: DDB's recommended strategies and Blackwell's decision rules

Package `tt-finite-frames`, Target B5.

For a partition expert `F = ofPartition π f` under full support, every recommended strategy for a
menu `𝒪` enumerated as `u : Fin (n+1) → W → ℝ` is worth exactly the Bayes value
`bayesValue π (ofMap f) u`: a recommended strategy is a decision rule on the signals `f w`, and a
decision rule is a strategy that a recommended one dominates cellwise. Through the bridge,
Weatherson's second Blackwell result (a non-refinement is beaten by some prior and menu) is B2 +
B4; his first is the partition case of G3 (`Geanakoplos.weatherson_i`) and is not proved twice.

Trap noted in the mandate: DDB's cell constraint is phrased through `P`, Weatherson's through the
partition; they agree under `hpos` (`ofPartition_P_inj`), which is why full support is assumed.
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Blackwell

noncomputable section

set_option linter.unusedSectionVars false

variable {W S : Type} [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S]

/-- The value of a decision rule on a deterministic experiment: `∑ w, π w · u (δ (f w)) w`.
Source: none: infrastructure (B5)
Kind: L
Fidelity: n/a -/
theorem ruleValue_ofMap (π : W → ℝ) (f : W → S) {n : ℕ} (u : Fin (n + 1) → W → ℝ)
    (δ : S → Fin (n + 1)) : ruleValue π (ofMap f) u δ = ∑ w, π w * u (δ (f w)) w := by
  unfold ruleValue
  apply sum_congr rfl
  intro w _
  congr 1
  simp only [ofMap, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, if_true]

/-- **Cellwise dominance on a partition frame**: under full support, a recommended strategy is
worth at least any strategy — the cellwise maximisation summed over the cells.
Source: none: infrastructure (B5(a), the "improve cellwise" step)
Kind: L
Fidelity: n/a -/
theorem stratValue_le_of_recommended_partition {π : W → ℝ} (hpos : ∀ w, 0 < π w) (f : W → S)
    {𝒪 : DecisionProblem W} {S₀ S' : W → (W → ℝ)}
    (hS : (Frame.ofPartition π hpos f).Recommended 𝒪 S₀)
    (hS' : (Frame.ofPartition π hpos f).IsStrategy 𝒪 S') :
    stratValue π S' ≤ stratValue π S₀ := by
  unfold stratValue
  have hK := Corr.ofMap_partitional f
  rw [hK.sum_cells (fun w => π w * S' w w), hK.sum_cells (fun w => π w * S₀ w w)]
  apply sum_le_sum
  intro C hC
  obtain ⟨v, _, rfl⟩ := mem_image.1 hC
  have hrow : ∀ w ∈ Corr.ofMap f v, (Frame.ofPartition π hpos f).P w =
      (Frame.ofPartition π hpos f).P v := fun w hw =>
    (Frame.ofPartition_P_inj π hpos f w v).2 (Corr.mem_ofMap.1 hw)
  have hc' : ∀ w ∈ Corr.ofMap f v, S' w = S' v := fun w hw => hS'.2 w v (hrow w hw)
  have hc : ∀ w ∈ Corr.ofMap f v, S₀ w = S₀ v := fun w hw => hS.cell (hrow w hw)
  calc ∑ w ∈ Corr.ofMap f v, π w * S' w w = ∑ w ∈ Corr.ofMap f v, π w * S' v w :=
        sum_congr rfl fun w hw => by rw [hc' w hw]
    _ ≤ ∑ w ∈ Corr.ofMap f v, π w * S₀ v w := by
        rw [← Frame.ofPartition_E π hpos f v (S' v), ← Frame.ofPartition_E π hpos f v (S₀ v)]
        exact mul_le_mul_of_nonneg_right (hS.le v (hS'.1 v))
          (Corr.mass_pos_of_reflexive hpos hK.1 v).le
    _ = ∑ w ∈ Corr.ofMap f v, π w * S₀ w w := sum_congr rfl fun w hw => by rw [hc w hw]

/-- **B5(a), the strategy bridge.** For a partition expert under full support and a menu
enumerated as `𝒪 = {u j}`, every recommended strategy is worth exactly the Bayes value of the
deterministic experiment `ofMap f` on `u`.
Source: fixpoint-lit-025 (Blackwell's results in DDB's language); mandate B5(a)
Kind: P
Fidelity: exact
Hyps: (a) `hpos` (full support: DDB's and Weatherson's cell constraints agree), `h𝒪`, `hS` -/
theorem stratValue_eq_bayesValue {π : W → ℝ} (hpos : ∀ w, 0 < π w) (f : W → S) {n : ℕ}
    (u : Fin (n + 1) → W → ℝ) {𝒪 : DecisionProblem W} (h𝒪 : 𝒪 = univ.image u)
    {S₀ : W → (W → ℝ)} (hS : (Frame.ofPartition π hpos f).Recommended 𝒪 S₀) :
    stratValue π S₀ = bayesValue π (ofMap f) u := by
  classical
  apply le_antisymm
  · -- a recommended strategy is a decision rule
    have hmem : ∀ w, ∃ j, u j = S₀ w := fun w => by
      have := hS.mem w
      rw [h𝒪, mem_image] at this
      obtain ⟨j, _, hj⟩ := this
      exact ⟨j, hj⟩
    set δ : S → Fin (n + 1) := fun s =>
      if hs : ∃ w, f w = s then (hmem hs.choose).choose else 0 with hδ
    have hδf : ∀ w, u (δ (f w)) = S₀ w := by
      intro w
      have hs : ∃ v, f v = f w := ⟨w, rfl⟩
      simp only [hδ, dif_pos hs]
      rw [(hmem hs.choose).choose_spec]
      exact hS.cell ((Frame.ofPartition_P_inj π hpos f _ _).2 hs.choose_spec)
    calc stratValue π S₀ = ruleValue π (ofMap f) u δ := by
          rw [ruleValue_ofMap]
          unfold stratValue
          apply sum_congr rfl
          intro w _
          rw [hδf w]
      _ ≤ bayesValue π (ofMap f) u := ruleValue_le_bayesValue π (ofMap f) u δ
  · -- every decision rule is a strategy, dominated by the recommended one
    apply bayesValue_le
    intro δ
    rw [ruleValue_ofMap]
    have hS' : (Frame.ofPartition π hpos f).IsStrategy 𝒪 (fun w => u (δ (f w))) := by
      refine ⟨fun w => ?_, fun w v e => ?_⟩
      · rw [h𝒪]; exact mem_image_of_mem u (mem_univ _)
      · show u (δ (f w)) = u (δ (f v))
        rw [(Frame.ofPartition_P_inj π hpos f w v).1 e]
    exact stratValue_le_of_recommended_partition hpos f hS hS'

/-- A nonempty finite menu is the image of some `Fin (n+1)`-indexed family.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem exists_enum_of_nonempty {𝒪 : DecisionProblem W} (h : 𝒪.Nonempty) :
    ∃ (n : ℕ) (u : Fin (n + 1) → W → ℝ), 𝒪 = univ.image u := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, 𝒪.card = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.2 h).ne'
  let e : 𝒪 ≃ Fin (n + 1) := 𝒪.equivFin.trans (finCongr hn)
  refine ⟨n, fun j => (e.symm j : W → ℝ), ?_⟩
  ext o
  rw [mem_image]
  constructor
  · intro ho
    exact ⟨e ⟨o, ho⟩, mem_univ _, by simp⟩
  · rintro ⟨j, _, rfl⟩
    exact (e.symm j).2

/-- **Weatherson's first Blackwell result, through the bridge** (the Blackwell route; the same
statement is `weatherson_i` in `Geanakoplos.lean` by the Geanakoplos route): if `f₁` refines
`f₂`, every strategy recommended by the partition expert on `f₁` is worth at least every
strategy recommended by the one on `f₂`.
Source: [[Deference and Infinite Frames]] §2 l. 122; fixpoint-lit-025 (i)
Kind: C (B1 + B5(a))
Fidelity: exact
Hyps: (a) `hπ`, `hpos`, `href` -/
theorem weatherson_i_blackwell {T : Type} [Fintype T] [DecidableEq T] {π : W → ℝ}
    (hπ : π ∈ stdSimplex ℝ W) (hpos : ∀ w, 0 < π w) {f₁ : W → S} {f₂ : W → T}
    (href : Blackwell.Refines f₁ f₂)
    {𝒪 : DecisionProblem W} (h𝒪 : 𝒪.Nonempty) {S₁ S₂ : W → (W → ℝ)}
    (hS₁ : (Frame.ofPartition π hpos f₁).Recommended 𝒪 S₁)
    (hS₂ : (Frame.ofPartition π hpos f₂).Recommended 𝒪 S₂) :
    stratValue π S₂ ≤ stratValue π S₁ := by
  obtain ⟨n, u, hu⟩ := exists_enum_of_nonempty h𝒪
  rw [stratValue_eq_bayesValue hpos f₁ u hu hS₁, stratValue_eq_bayesValue hpos f₂ u hu hS₂]
  exact moreValuable_of_blackwellLE (Refines.blackwellLE href) π hπ n u

/-- **B5(b), Weatherson's second Blackwell result in DDB's language.** If `f₁` does not refine
`f₂`, there are a full-support prior, a menu, and recommended strategies `S₁` (for `f₁`) and
`S₂` (for `f₂`) with `E_π(S₁) < E_π(S₂)`: B4 turns non-refinement into non-garbling, B2 supplies
the prior and menu, the bridge turns Bayes values into strategy values.
Source: [[Deference and Infinite Frames]] §2 l. 124 (Blackwell (ii)); fixpoint-lit-025 (ii)
Kind: C (B2 + B4 + B5(a))
Fidelity: exact (`[Nonempty W]`, `[Nonempty T]` as in B2/B4)
Hyps: (a) none -/
theorem weatherson_ii [Nonempty W] {T : Type} [Fintype T] [DecidableEq T] [Nonempty T]
    {f₁ : W → S} {f₂ : W → T} (h : ¬ Blackwell.Refines f₁ f₂) :
    ∃ (π : W → ℝ) (hpos : ∀ w, 0 < π w) (𝒪 : DecisionProblem W) (S₁ S₂ : W → (W → ℝ)),
      (Frame.ofPartition π hpos f₁).Recommended 𝒪 S₁ ∧
      (Frame.ofPartition π hpos f₂).Recommended 𝒪 S₂ ∧ stratValue π S₁ < stratValue π S₂ := by
  have hng : ¬ BlackwellLE (ofMap f₂) (ofMap f₁) := fun hle =>
    h ((blackwellLE_ofMap_iff f₁ f₂).1 hle)
  obtain ⟨μ, -, hμpos, n, u, hlt⟩ := exists_prior_menu_of_not_blackwellLE hng
  set 𝒪 : DecisionProblem W := univ.image u with h𝒪
  have hne : 𝒪.Nonempty := (univ_nonempty).image u
  refine ⟨μ, hμpos, 𝒪, _, _, (Frame.ofPartition μ hμpos f₁).informedStrategy_recommended 𝒪 hne,
    (Frame.ofPartition μ hμpos f₂).informedStrategy_recommended 𝒪 hne, ?_⟩
  rw [stratValue_eq_bayesValue hμpos f₁ u h𝒪
      ((Frame.ofPartition μ hμpos f₁).informedStrategy_recommended 𝒪 hne),
    stratValue_eq_bayesValue hμpos f₂ u h𝒪
      ((Frame.ofPartition μ hμpos f₂).informedStrategy_recommended 𝒪 hne)]
  exact hlt

/-- **Geanakoplos's second result, existential form** (the shape of `weatherson_ii`): a
reflexive `E₁` that does not refine a partitional `E₂` is beaten, under every full-support
prior, by some menu with recommended strategies `S₁`, `S₂` (the dependency's
`informedStrategy`) and `E_π(S₁) < E_π(S₂)`.
Source: [[Deference and Infinite Frames]] §2 ll. 142–146; fixpoint-lit-026 (second half)
Kind: C (from `partition_coarse_converse`)
Fidelity: stronger: as `partition_coarse_converse`
Hyps: (a) `hpos`, `hK₁`, `hK₂`, `hnref` -/
theorem partition_coarse_converse_exists {π : W → ℝ} (hpos : ∀ w, 0 < π w) {K₁ K₂ : Corr W}
    (hK₁ : K₁.Reflexive) (hK₂ : K₂.Partitional) (hnref : ¬ Corr.Refines K₁ K₂) :
    ∃ (𝒪 : DecisionProblem W) (S₁ S₂ : W → (W → ℝ)),
      (Frame.ofCorr π (fun w => (hpos w).le) K₁
        (Corr.mass_pos_of_reflexive hpos hK₁)).Recommended 𝒪 S₁ ∧
      (Frame.ofCorr π (fun w => (hpos w).le) K₂
        (Corr.mass_pos_of_reflexive hpos hK₂.1)).Recommended 𝒪 S₂ ∧
      stratValue π S₁ < stratValue π S₂ := by
  obtain ⟨𝒪, hne, h⟩ := partition_coarse_converse hpos hK₁ hK₂ hnref
  refine ⟨𝒪, _, _, Frame.informedStrategy_recommended _ 𝒪 hne,
    Frame.informedStrategy_recommended _ 𝒪 hne, ?_⟩
  exact h _ _ (Frame.informedStrategy_recommended _ 𝒪 hne)
    (Frame.informedStrategy_recommended _ 𝒪 hne)

end

end Cleanroom.Trust.TtFiniteFrames
