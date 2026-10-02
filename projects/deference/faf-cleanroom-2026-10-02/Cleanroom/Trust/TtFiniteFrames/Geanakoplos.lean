import Cleanroom.Trust.TtFiniteFrames.Partition
import Cleanroom.Found.LitDdbFrames.Value

/-!
# The finite Geanakoplos lemma

Package `tt-finite-frames`, Targets G2 (load-bearing 4) and G3.

* **G2**: for a reflexive, transitive (corrected direction) and nested correspondence `E` and a
  full-support prior `π`, the conditioning frame `ofCorr π E` is **Valued** by `π` in the
  dependency's sense: every recommended strategy beats every fixed option (value of information
  is nonnegative). Corollaries through Theorem 7.6: `π` totally trusts it, and the hull-and-
  modestly-informed condition holds — root-deference-2-010 (ii)'s "S4 ⟹ Total Trust" at grade (a).
* **G3**: the same against a coarser *partitional* experiment: if `E₁` is RTN, `E₂` is
  partitional and `E₁` refines `E₂`, every `E₁`-recommended strategy is worth at least every
  `E₂`-recommended one. Blackwell's first result for partitions is the special case `E₁`
  partitional (`Strategies.lean` records it; it is not proved twice).

The engine is one strong induction (`closed_sum_le`): on every set `A` closed under `E`
(`w ∈ A → E w ⊆ A`), the `π`-weighted return of a recommended strategy dominates that of every
fixed option. In the step, a largest cell `E w₀` inside `A` is split off (nesting makes the rest
closed), and the cell itself splits into its top `{w ∈ E w₀ : E w = E w₀}` — where the strategy is
constant and optimal for `π(· | E w₀)` — and the closed remainder of strictly smaller cells
(transitivity), to which the induction hypothesis applies at the option chosen on the top.
This is the mandate's proof of record; Geanakoplos's own argument is a variant.

The only structural hypotheses are `E.RTN` and full support; recommendation is the dependency's
(no tie-break is hard-coded), so "every recommended strategy" is not vacuous.
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- A set of worlds is **closed** under a correspondence when it contains the cell of each of its
worlds.
Source: none: infrastructure (G2's induction)
Kind: D
Fidelity: n/a -/
def Corr.Closed (K : Corr W) (A : Finset W) : Prop := ∀ w ∈ A, K w ⊆ A

/-- **The cell master lemma.** For an RTN correspondence under full support and a recommended
strategy `S` for `𝒪` on the conditioning frame: on every closed set `A`, the `π`-weighted return
of `S` dominates that of every fixed option `o ∈ 𝒪`. Strong induction on `A`.
Source: mandate G2 (proof of record); Geanakoplos 1989 (the result)
Kind: P
Fidelity: n/a (the engine of G2/G3)
Hyps: (a) `hpos`, `hK`, `hS` -/
theorem closed_sum_le {π : W → ℝ} (hpos : ∀ w, 0 < π w) {K : Corr W} (hK : K.RTN)
    (h : ∀ w, 0 < mass π (K w)) {𝒪 : DecisionProblem W} {S : W → (W → ℝ)}
    (hS : (Frame.ofCorr π (fun w => (hpos w).le) K h).Recommended 𝒪 S)
    (A : Finset W) (hA : K.Closed A) :
    ∀ o ∈ 𝒪, ∑ w ∈ A, π w * o w ≤ ∑ w ∈ A, π w * S w w := by
  induction A using Finset.strongInduction with
  | H A ih =>
  intro o ho
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨w₀, hw₀A, hmax⟩ := exists_max_image A (fun w => (K w).card) hne
  have hKA : K w₀ ⊆ A := hA w₀ hw₀A
  -- (1) the rest of `A` outside the largest cell is closed and smaller
  have hA' : K.Closed (A \ K w₀) := by
    intro w hw u hu
    rw [mem_sdiff] at hw ⊢
    refine ⟨hA w hw.1 hu, ?_⟩
    intro huK
    rcases hK.2.2 w w₀ with hdis | hsub | hsup
    · exact Finset.disjoint_left.1 hdis hu huK
    · exact hw.2 (hsub (hK.1 w))
    · have heq : K w₀ = K w := eq_of_subset_of_card_le hsup (hmax w hw.1)
      exact hw.2 (heq ▸ hK.1 w)
  have hssub : A \ K w₀ ⊂ A := sdiff_ssubset hKA ⟨w₀, hK.1 w₀⟩
  have ih1 := ih _ hssub hA' o ho
  -- (2) the cell splits into its top `T` and the closed remainder `N` of strictly smaller cells
  set T := (K w₀).filter (fun w => K w = K w₀) with hT
  set N := (K w₀).filter (fun w => ¬ K w = K w₀) with hN
  have hNclosed : K.Closed N := by
    intro w hw u hu
    rw [hN, mem_filter] at hw ⊢
    have hsub : K w ⊆ K w₀ := hK.2.1 w₀ w hw.1
    refine ⟨hsub hu, ?_⟩
    intro hu'
    apply hw.2
    apply Finset.Subset.antisymm hsub
    rw [← hu']
    exact hK.2.1 w u hu
  have hNssub : N ⊂ A := by
    rw [Finset.ssubset_iff_of_subset ((filter_subset _ _).trans hKA)]
    exact ⟨w₀, hw₀A, by simp⟩
  have ih2 := ih _ hNssub hNclosed (S w₀) (hS.mem w₀)
  -- on the top the strategy is constant (cell constraint through `P`-injectivity)
  have hTconst : ∀ w ∈ T, S w = S w₀ := by
    intro w hw
    rw [hT, mem_filter] at hw
    exact hS.cell (Frame.ofCorr_P_eq_of_eq π _ K h hw.2)
  -- recommended at `w₀`: `∑_{E w₀} π o ≤ ∑_{E w₀} π (S w₀)`
  have hrec : ∑ w ∈ K w₀, π w * o w ≤ ∑ w ∈ K w₀, π w * S w₀ w := by
    have := hS.le w₀ ho
    rw [← Frame.ofCorr_E π (fun w => (hpos w).le) K h w₀ o,
      ← Frame.ofCorr_E π (fun w => (hpos w).le) K h w₀ (S w₀)]
    exact mul_le_mul_of_nonneg_right this (h w₀).le
  have hsplit : ∀ g : W → ℝ, ∑ w ∈ K w₀, g w = ∑ w ∈ T, g w + ∑ w ∈ N, g w := fun g =>
    (sum_filter_add_sum_filter_not (K w₀) (fun w => K w = K w₀) g).symm
  have hcell : ∑ w ∈ K w₀, π w * o w ≤ ∑ w ∈ K w₀, π w * S w w := by
    calc ∑ w ∈ K w₀, π w * o w ≤ ∑ w ∈ K w₀, π w * S w₀ w := hrec
      _ = ∑ w ∈ T, π w * S w₀ w + ∑ w ∈ N, π w * S w₀ w := hsplit _
      _ ≤ ∑ w ∈ T, π w * S w w + ∑ w ∈ N, π w * S w w :=
          add_le_add (le_of_eq (sum_congr rfl fun w hw => by rw [hTconst w hw])) ih2
      _ = ∑ w ∈ K w₀, π w * S w w := (hsplit _).symm
  -- combine the two parts of `A`
  rw [← sum_sdiff hKA (f := fun w => π w * o w), ← sum_sdiff hKA (f := fun w => π w * S w w)]
  exact add_le_add ih1 hcell

/-- **G2 (load-bearing 4). Finite Geanakoplos lemma.** For a reflexive, transitive and nested
correspondence `E` and a full-support prior `π`, the conditioning frame `ofCorr π E` is Valued by
`π`: for every nonempty menu, every recommended strategy is worth at least every fixed option
(value of information is nonnegative). Stated for an arbitrary `Fintype W`.
Source: [[Deference and Infinite Frames]] §2 ll. 142–146 (Geanakoplos, with `E₂ ≡ W`);
root-deference-2-010 (iii); trust-lab-2-026; trust-lab-004/039
Kind: P
Fidelity: exact (with the corrected transitivity; `E₂ ≡ W` case)
Hyps: (a) `hpos` full support, `hK : E.RTN` -/
theorem value_ofCorr_of_rtn {π : W → ℝ} (hpos : ∀ w, 0 < π w) {K : Corr W} (hK : K.RTN) :
    Value π (Frame.ofCorr π (fun w => (hpos w).le) K (Corr.mass_pos_of_reflexive hpos hK.1)) := by
  intro 𝒪 _ S hS o ho
  exact closed_sum_le hpos hK _ hS univ (fun w _ => subset_univ _) o ho

/-- **G2, corollary.** A full-support prior in the simplex totally trusts the conditioning frame
of any RTN correspondence (Value ⟹ Total Trust, Theorem 7.6): root-deference-2-010 (ii)'s
"S4 ⟹ Total Trust", at grade (a).
Source: root-deference-2-010 (ii); [[Deference Done Better]] Thm 2.2
Kind: C
Fidelity: exact
Hyps: (a) `hπ`, `hpos`, `hK` -/
theorem totalTrust_ofCorr_of_rtn {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (hpos : ∀ w, 0 < π w)
    {K : Corr W} (hK : K.RTN) :
    TotalTrust π (Frame.ofCorr π (fun w => (hpos w).le) K (Corr.mass_pos_of_reflexive hpos hK.1)) :=
  (value_iff_totalTrust hπ _).1 (value_ofCorr_of_rtn hpos hK)

/-- **G2, corollary.** The conditioning frame of an RTN correspondence satisfies DDB's
hull-and-modestly-informed condition for its prior (Theorem 4.1).
Source: [[Deference Done Better]] Thm 4.1; mandate G2
Kind: C
Fidelity: exact
Hyps: (a) `hπ`, `hpos`, `hK` -/
theorem hullAndModestlyInformed_ofCorr_of_rtn {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    (hpos : ∀ w, 0 < π w) {K : Corr W} (hK : K.RTN) :
    HullAndModestlyInformed π
      (Frame.ofCorr π (fun w => (hpos w).le) K (Corr.mass_pos_of_reflexive hpos hK.1)) :=
  (totalTrust_iff_hullAndModestlyInformed hπ _).1 (totalTrust_ofCorr_of_rtn hπ hpos hK)

/-- **T1 again, as the partition case of G2** (the mandate's second route): a full-support prior
totally trusts its own partition expert.
Source: trust-lab-063 `TT_condExpert`, via Geanakoplos
Kind: C
Fidelity: exact
Hyps: (a) `hπ`, `hpos` -/
theorem totalTrust_ofPartition_via_geanakoplos {ι : Type} [DecidableEq ι] {π : W → ℝ}
    (hπ : π ∈ stdSimplex ℝ W) (hpos : ∀ w, 0 < π w) (f : W → ι) :
    TotalTrust π (Frame.ofPartition π hpos f) :=
  totalTrust_ofCorr_of_rtn hπ hpos (Corr.ofMap_rtn f)

/-- **G3. Geanakoplos with a partitional coarser experiment.** If `E₁` is RTN, `E₂` is
partitional and `E₁` refines `E₂`, then under a full-support prior every strategy recommended by
the finer frame is worth at least every strategy recommended by the coarser one. On each
`E₂`-cell `C` the coarse strategy is a constant option `o_C ∈ 𝒪` and `C` is `E₁`-closed
(`E₁ w ⊆ E₂ w = C`), so the master lemma at `o_C` gives the inequality cellwise.
Source: [[Deference and Infinite Frames]] §2 ll. 142–146 (Geanakoplos's generalisation of
Blackwell's first result)
Kind: C
Fidelity: exact (with the corrected transitivity)
Hyps: (a) `hpos`, `hK₁ : E₁.RTN`, `hK₂ : E₂.Partitional`, `href` -/
theorem geanakoplos_partition_coarse {π : W → ℝ} (hpos : ∀ w, 0 < π w) {K₁ K₂ : Corr W}
    (hK₁ : K₁.RTN) (hK₂ : K₂.Partitional) (href : Corr.Refines K₁ K₂)
    (𝒪 : DecisionProblem W) (S₁ S₂ : W → (W → ℝ))
    (hS₁ : (Frame.ofCorr π (fun w => (hpos w).le) K₁
      (Corr.mass_pos_of_reflexive hpos hK₁.1)).Recommended 𝒪 S₁)
    (hS₂ : (Frame.ofCorr π (fun w => (hpos w).le) K₂
      (Corr.mass_pos_of_reflexive hpos hK₂.1)).Recommended 𝒪 S₂) :
    stratValue π S₂ ≤ stratValue π S₁ := by
  unfold stratValue
  rw [hK₂.sum_cells (fun w => π w * S₂ w w), hK₂.sum_cells (fun w => π w * S₁ w w)]
  apply sum_le_sum
  intro C hC
  obtain ⟨v, _, rfl⟩ := mem_image.1 hC
  have hconst : ∀ w ∈ K₂ v, S₂ w = S₂ v := fun w hw =>
    hS₂.cell (Frame.ofCorr_P_eq_of_eq π _ K₂ _ (hK₂.2 v w hw).symm)
  have hclosed : K₁.Closed (K₂ v) := fun w hw => (href w).trans (hK₂.2 v w hw).symm.subset
  calc ∑ w ∈ K₂ v, π w * S₂ w w = ∑ w ∈ K₂ v, π w * S₂ v w :=
        sum_congr rfl fun w hw => by rw [hconst w hw]
    _ ≤ ∑ w ∈ K₂ v, π w * S₁ w w :=
        closed_sum_le hpos hK₁ _ hS₁ (K₂ v) hclosed (S₂ v) (hS₂.mem v)

/-- A refinement of maps gives a refinement of their fibre correspondences (the direction of
`Corr.refines_ofMap_iff` that needs no `Nonempty`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem corrRefines_of_refines {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    {f₁ : W → ι} {f₂ : W → κ} (h : Blackwell.Refines f₁ f₂) :
    Corr.Refines (Corr.ofMap f₁) (Corr.ofMap f₂) := by
  obtain ⟨g, rfl⟩ := h
  intro w v hv
  rw [Corr.mem_ofMap] at hv ⊢
  simp [Function.comp, hv]

/-- **Weatherson's first Blackwell result for partitions**, as the partition case of G3: if `f₁`
refines `f₂`, every strategy recommended by `π`'s partition expert on `f₁` is worth at least every
strategy recommended by its partition expert on `f₂`, for every menu. Not proved twice: this is
G3 with `E₁ = ofMap f₁`.
Source: [[Deference and Infinite Frames]] §2 l. 122 (Blackwell (i)); fixpoint-lit-025
Kind: C
Fidelity: exact (partition experts of one prior; DDB's `Recommended`, which agrees with
Weatherson's under `hpos` by `ofCorr_P_inj`)
Hyps: (a) `hpos`, `href` -/
theorem weatherson_i {ι κ : Type} [DecidableEq ι] [DecidableEq κ] {π : W → ℝ}
    (hpos : ∀ w, 0 < π w) {f₁ : W → ι} {f₂ : W → κ} (href : Blackwell.Refines f₁ f₂)
    (𝒪 : DecisionProblem W) (S₁ S₂ : W → (W → ℝ))
    (hS₁ : (Frame.ofPartition π hpos f₁).Recommended 𝒪 S₁)
    (hS₂ : (Frame.ofPartition π hpos f₂).Recommended 𝒪 S₂) :
    stratValue π S₂ ≤ stratValue π S₁ :=
  geanakoplos_partition_coarse hpos (Corr.ofMap_rtn f₁) (Corr.ofMap_partitional f₂)
    (corrRefines_of_refines href) 𝒪 S₁ S₂ hS₁ hS₂

/-! ## Repair round 1: Geanakoplos's second result for a partitional coarser experiment -/

/-- **Geanakoplos's second result for a partitional coarser experiment — with neither
transitivity nor nesting of `E₁`, and for every prior.** If `E₂` is partitional and a reflexive
`E₁` does not refine it, then for *every* full-support prior there is a menu on which every
`E₂`-recommended strategy is strictly more valuable than every `E₁`-recommended one. Proof: pick
`w` with `E₁ w ⊄ E₂ w`; menu `{0, O}` with `O = 𝟙_{E₂ w} − d · 𝟙_{W ∖ E₂ w}` and
`d = π(E₁ w ∩ E₂ w)/π(E₁ w ∖ E₂ w) + 1`. The `E₂`-agent takes `O` exactly on the cell `E₂ w`
(strict preferences either way), earning the pointwise maximum `max(O, 0)` everywhere; the
`E₁`-agent's return is pointwise at most that maximum, and at `w` it is `0 < 1`, because
`∑_{E₁ w} π O = −π(E₁ w ∖ E₂ w) < 0` forces it to decline `O` there.
Source: [[Deference and Infinite Frames]] §2 ll. 142–146 ("both of Blackwell's results"),
fixpoint-lit-026 (second half); audit r1 (fidelity N6, adversarial N3)
Kind: P
Fidelity: stronger: `E₁` only reflexive (Weatherson assumes RTN), every full-support prior
(Weatherson: some prior), every pair of recommended strategies — finding F-G3b
Hyps: (a) `hpos`, `hK₁` (reflexive), `hK₂` (partitional), `hnref` -/
theorem partition_coarse_converse {π : W → ℝ} (hpos : ∀ w, 0 < π w) {K₁ K₂ : Corr W}
    (hK₁ : K₁.Reflexive) (hK₂ : K₂.Partitional) (hnref : ¬ Corr.Refines K₁ K₂) :
    ∃ 𝒪 : DecisionProblem W, 𝒪.Nonempty ∧ ∀ S₁ S₂,
      (Frame.ofCorr π (fun w => (hpos w).le) K₁
        (Corr.mass_pos_of_reflexive hpos hK₁)).Recommended 𝒪 S₁ →
      (Frame.ofCorr π (fun w => (hpos w).le) K₂
        (Corr.mass_pos_of_reflexive hpos hK₂.1)).Recommended 𝒪 S₂ →
      stratValue π S₁ < stratValue π S₂ := by
  set F₁ := Frame.ofCorr π (fun w => (hpos w).le) K₁ (Corr.mass_pos_of_reflexive hpos hK₁)
    with hF₁
  set F₂ := Frame.ofCorr π (fun w => (hpos w).le) K₂ (Corr.mass_pos_of_reflexive hpos hK₂.1)
    with hF₂
  -- the world where refinement fails
  obtain ⟨w, hw⟩ : ∃ w, ¬ K₁ w ⊆ K₂ w := by
    by_contra h
    push_neg at h
    exact hnref h
  obtain ⟨v₀, hv₀₁, hv₀₂⟩ := not_subset.1 hw
  set A := (K₁ w).filter (fun v => v ∈ K₂ w) with hA
  set B := (K₁ w).filter (fun v => v ∉ K₂ w) with hB
  have hBpos : 0 < mass π B :=
    sum_pos (fun v _ => hpos v) ⟨v₀, by simp [hB, hv₀₁, hv₀₂]⟩
  have hA0 : 0 ≤ mass π A := sum_nonneg fun v _ => (hpos v).le
  set d : ℝ := mass π A / mass π B + 1 with hd
  have hdpos : 0 < d := by positivity
  set O : W → ℝ := fun v => if v ∈ K₂ w then 1 else -d with hO
  set Z : W → ℝ := fun _ => 0 with hZ
  refine ⟨{Z, O}, ⟨Z, mem_insert_self _ _⟩, ?_⟩
  intro S₁ S₂ hS₁ hS₂
  have hZmem : Z ∈ ({Z, O} : DecisionProblem W) := mem_insert_self _ _
  have hOmem : O ∈ ({Z, O} : DecisionProblem W) := mem_insert_of_mem (mem_singleton_self _)
  have hEZ : ∀ (F : Frame W) (u : W), E (F.P u) Z = 0 := fun F u => E_const (F.P_mem u) 0
  -- the `E₂`-agent's estimate of `O`: positive on the cell of `w`, negative off it
  have hE₂pos : ∀ u ∈ K₂ w, 0 < E (F₂.P u) O := by
    intro u hu
    have hcell : K₂ u = K₂ w := (hK₂.2 w u hu).symm
    have hid : E (F₂.P u) O * mass π (K₂ u) = ∑ v ∈ K₂ u, π v * O v :=
      Frame.ofCorr_E π _ K₂ _ u O
    rw [hcell] at hid
    have hsum : ∑ v ∈ K₂ w, π v * O v = mass π (K₂ w) := by
      unfold mass
      apply sum_congr rfl
      intro v hv
      simp only [hO, if_pos hv, mul_one]
    rw [hsum] at hid
    have hm : 0 < mass π (K₂ w) := Corr.mass_pos_of_reflexive hpos hK₂.1 w
    by_contra hnot
    push_neg at hnot
    have := mul_nonpos_of_nonpos_of_nonneg hnot hm.le
    linarith
  have hE₂neg : ∀ u, u ∉ K₂ w → E (F₂.P u) O < 0 := by
    intro u hu
    have hoff : ∀ v ∈ K₂ u, v ∉ K₂ w := by
      intro v hv hvw
      apply hu
      have h1 : K₂ u = K₂ v := hK₂.2 u v hv
      have h2 : K₂ w = K₂ v := hK₂.2 w v hvw
      rw [← h2] at h1
      rw [← h1]
      exact hK₂.1 u
    have hid : E (F₂.P u) O * mass π (K₂ u) = ∑ v ∈ K₂ u, π v * O v :=
      Frame.ofCorr_E π _ K₂ _ u O
    have hsum : ∑ v ∈ K₂ u, π v * O v = -(d * mass π (K₂ u)) := by
      unfold mass
      rw [mul_sum, ← sum_neg_distrib]
      apply sum_congr rfl
      intro v hv
      simp only [hO, if_neg (hoff v hv)]
      ring
    rw [hsum] at hid
    have hm : 0 < mass π (K₂ u) := Corr.mass_pos_of_reflexive hpos hK₂.1 u
    by_contra hnot
    push_neg at hnot
    have := mul_nonneg hnot hm.le
    linarith [mul_pos hdpos hm]
  -- `S₂` takes `O` exactly on the cell of `w`
  have hS₂val : ∀ u, S₂ u u = if u ∈ K₂ w then 1 else 0 := by
    intro u
    rcases mem_insert.1 (hS₂.1.1 u) with h | h
    · by_cases hu : u ∈ K₂ w
      · exfalso
        have := hS₂.2 u O hOmem
        rw [h, hEZ] at this
        exact absurd (hE₂pos u hu) (not_lt.2 this)
      · simp [h, hZ, hu]
    · rw [mem_singleton] at h
      by_cases hu : u ∈ K₂ w
      · simp [h, hO, hu]
      · exfalso
        have := hS₂.2 u Z hZmem
        rw [h, hEZ] at this
        exact absurd (hE₂neg u hu) (not_lt.2 this)
  -- `S₁`'s return is pointwise at most `max(O, 0)`
  have hopt : ∀ u, S₁ u u ≤ (if u ∈ K₂ w then 1 else 0) := by
    intro u
    rcases mem_insert.1 (hS₁.1.1 u) with h | h
    · simp only [h, hZ]
      split_ifs <;> norm_num
    · simp only [mem_singleton.1 h, hO]
      split_ifs <;> linarith
  -- and at `w` it is `0`: the `E₁`-agent declines `O` there
  have hS₁w : S₁ w w = 0 := by
    rcases mem_insert.1 (hS₁.1.1 w) with h | h
    · simp [h, hZ]
    · exfalso
      have hid : E (F₁.P w) O * mass π (K₁ w) = ∑ v ∈ K₁ w, π v * O v :=
        Frame.ofCorr_E π _ K₁ _ w O
      have hsplit : ∑ v ∈ K₁ w, π v * O v = mass π A - d * mass π B := by
        rw [← sum_filter_add_sum_filter_not (K₁ w) (fun v => v ∈ K₂ w) (fun v => π v * O v)]
        show ∑ v ∈ A, π v * O v + ∑ v ∈ B, π v * O v = mass π A - d * mass π B
        have h1 : ∑ v ∈ A, π v * O v = mass π A := by
          unfold mass
          apply sum_congr rfl
          intro v hv
          have : v ∈ K₂ w := (mem_filter.1 hv).2
          simp only [hO, if_pos this, mul_one]
        have h2 : ∑ v ∈ B, π v * O v = -(d * mass π B) := by
          unfold mass
          rw [mul_sum, ← sum_neg_distrib]
          apply sum_congr rfl
          intro v hv
          have : v ∉ K₂ w := (mem_filter.1 hv).2
          simp only [hO, if_neg this]
          ring
        rw [h1, h2]
        ring
      have hval : mass π A - d * mass π B = -mass π B := by
        rw [hd, add_mul, div_mul_cancel₀ _ hBpos.ne']
        ring
      rw [hsplit, hval] at hid
      have hm : 0 < mass π (K₁ w) := Corr.mass_pos_of_reflexive hpos hK₁ w
      have hneg : E (F₁.P w) O < 0 := by
        by_contra hnot
        push_neg at hnot
        have := mul_nonneg hnot hm.le
        linarith
      have := hS₁.2 w Z hZmem
      rw [mem_singleton.1 h, hEZ] at this
      exact absurd hneg (not_lt.2 this)
  have hS₂w : S₂ w w = 1 := by rw [hS₂val w, if_pos (hK₂.1 w)]
  unfold stratValue
  apply sum_lt_sum
  · intro u _
    apply mul_le_mul_of_nonneg_left _ (hpos u).le
    rw [hS₂val u]
    exact hopt u
  · exact ⟨w, mem_univ w, by rw [hS₁w, hS₂w]; simp [hpos w]⟩

end

end Cleanroom.Trust.TtFiniteFrames
