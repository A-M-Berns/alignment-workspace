import Cleanroom.Found.LitDdbFrames.Value
import Mathlib.Data.Fin.VecNotation

/-!
# Witnesses on two worlds: Figure 2, Figure 3, and the cell constraint

Package `lit-ddb-frames`, Targets 18, 19, 23. Every number is DDB's, checked against
`DORDDBv1.pdf` (`lit-ddb-frames-findings.md`, record item). Proofs are explicit rationals cast to
`ℝ`, closed by `norm_num`/`simp`; no `decide`, no `native_decide`. Cells and self-masses are
computed as separate lemmas and rewritten before the rows are evaluated.
-/

namespace Cleanroom.Found.LitDdbFrames.Examples

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

/-- A two-world frame from its two rows.
Source: none: infrastructure (Targets 18, 19, 23)
Kind: D
Fidelity: n/a -/
def mk2 (r₀ r₁ : Fin 2 → ℝ) (h₀ : r₀ ∈ stdSimplex ℝ (Fin 2)) (h₁ : r₁ ∈ stdSimplex ℝ (Fin 2)) :
    Frame (Fin 2) where
  P := ![r₀, r₁]
  P_mem := fun w => by fin_cases w <;> assumption

/-- A nonnegative pair summing to one is a distribution on two worlds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem simplex2 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 1) :
    (![a, b] : Fin 2 → ℝ) ∈ stdSimplex ℝ (Fin 2) :=
  ⟨fun x => by fin_cases x <;> simp [ha, hb], by simp [Fin.sum_univ_two, h]⟩

/-- The uniform deferrer on two worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def half : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- The uniform deferrer is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem half_mem : half ∈ stdSimplex ℝ (Fin 2) := simplex2 _ _ (by norm_num) (by norm_num) (by norm_num)

/-- Cells of a two-world frame with distinct rows are singletons.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cell_of_ne (F : Frame (Fin 2)) (hne : F.P 0 ≠ F.P 1) :
    F.cell (F.P 0) = {0} ∧ F.cell (F.P 1) = {1} := by
  constructor
  · ext w; fin_cases w <;> simp [Frame.mem_cell, hne.symm]
  · ext w; fin_cases w <;> simp [Frame.mem_cell, hne]

/-- Candidates of a fully supported deferrer on a two-world frame.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cands_eq_pair (F : Frame (Fin 2)) {ρ : Fin 2 → ℝ} (h0 : 0 < ρ 0) (h1 : 0 < ρ 1) :
    F.cands ρ = {F.P 0, F.P 1} := by
  ext σ
  rw [Frame.mem_cands]
  constructor
  · rintro ⟨w, _, rfl⟩
    fin_cases w <;> simp
  · intro hσ
    simp only [mem_insert, mem_singleton] at hσ
    rcases hσ with rfl | rfl
    · exact ⟨0, h0, rfl⟩
    · exact ⟨1, h1, rfl⟩

/-- `C_ρ⁻` for a two-world frame with distinct rows, at the first row.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem candsMinus_eq (F : Frame (Fin 2)) (hne : F.P 0 ≠ F.P 1) {ρ : Fin 2 → ℝ} (h0 : 0 < ρ 0)
    (h1 : 0 < ρ 1) : F.candsMinus ρ = (({F.P 0, F.P 1} : Finset (Fin 2 → ℝ)).erase ρ) := by
  rw [Frame.candsMinus, cands_eq_pair F h0 h1]

/-- Membership of a convex combination of two hull points, in the form used below.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_hull_of_comb {s : Set (Fin 2 → ℝ)} {x y z : Fin 2 → ℝ} (hx : x ∈ s) (hy : y ∈ s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hz : z = a • x + b • y) :
    z ∈ convexHull ℝ s := by
  rw [hz]
  exact (convex_convexHull ℝ s) (subset_convexHull ℝ s hx) (subset_convexHull ℝ s hy) ha hb hab

/-! ## Figure 2: the anti-expert frame (Target 18) -/

/-- Figure 2's rows: `P_a = (0.2, 0.8)`, `P_b = (0.8, 0.2)`.
Source: [[Deference Done Better]] §1 l. 105 (Figure 2)
Kind: D
Fidelity: exact -/
def fig2 : Frame (Fin 2) :=
  mk2 ![1 / 5, 4 / 5] ![4 / 5, 1 / 5]
    (simplex2 _ _ (by norm_num) (by norm_num) (by norm_num))
    (simplex2 _ _ (by norm_num) (by norm_num) (by norm_num))

/-- Figure 2's first row.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig2_P0 : fig2.P 0 = ![1 / 5, 4 / 5] := rfl

/-- Figure 2's second row.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig2_P1 : fig2.P 1 = ![4 / 5, 1 / 5] := rfl

/-- Figure 2's two rows are distinct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig2_ne : fig2.P 0 ≠ fig2.P 1 := by
  intro h
  have := congrFun h 0
  rw [fig2_P0, fig2_P1] at this
  norm_num at this

/-- Figure 2's self-cell masses are both `0.2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig2_selfMass : fig2.selfMass (fig2.P 0) = 1 / 5 ∧ fig2.selfMass (fig2.P 1) = 1 / 5 := by
  obtain ⟨hc0, hc1⟩ := cell_of_ne fig2 fig2_ne
  constructor
  · rw [Frame.selfMass, hc0]; norm_num [mass, fig2_P0]
  · rw [Frame.selfMass, hc1]; norm_num [mass, fig2_P1]

/-- The uniform deferrer gives each Figure 2 cell mass `½`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig2_mass : mass half (fig2.cell (fig2.P 0)) = 1 / 2 ∧
    mass half (fig2.cell (fig2.P 1)) = 1 / 2 := by
  obtain ⟨hc0, hc1⟩ := cell_of_ne fig2 fig2_ne
  constructor
  · rw [hc0]; norm_num [mass, half]
  · rw [hc1]; norm_num [mass, half]

/-- **Target 18 (Figure 2), New Reflection.** The uniform deferrer new-reflects the anti-expert
frame in the strong reading.
Source: [[Deference Done Better]] §1 l. 102, fn 13
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig2_newReflects : NewReflects half fig2 := by
  intro ρ hρ
  rw [cands_eq_pair fig2 (by norm_num [half]) (by norm_num [half])] at hρ
  obtain ⟨hc0, hc1⟩ := cell_of_ne fig2 fig2_ne
  obtain ⟨hs0, hs1⟩ := fig2_selfMass
  obtain ⟨hm0, hm1⟩ := fig2_mass
  simp only [mem_insert, mem_singleton] at hρ
  rcases hρ with rfl | rfl
  · refine ⟨by rw [hs0]; norm_num, fun w => ?_⟩
    rw [hs0, hm0, hc0]
    fin_cases w <;> norm_num [ind, half, fig2_P0]
  · refine ⟨by rw [hs1]; norm_num, fun w => ?_⟩
    rw [hs1, hm1, hc1]
    fin_cases w <;> norm_num [ind, half, fig2_P1]

/-- **Target 18 (Figure 2), Value fails.** On the bet `{O_a, O_b}` the frame recommends the wrong
side at each world: `E_π(S) = −1 < 0 = E_π(O_a)`. So New Reflection does not imply Value.
Source: [[Deference Done Better]] §1 l. 113–117
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig2_not_value : ¬ Value half fig2 := by
  intro h
  have hrec : fig2.Recommended {![1, -1], ![-1, 1]} ![![-1, 1], ![1, -1]] := by
    refine ⟨⟨fun w => ?_, fun w v e => ?_⟩, fun w o ho => ?_⟩
    · fin_cases w <;> simp
    · fin_cases w <;> fin_cases v <;> first | rfl | (exact absurd e fig2_ne) |
        (exact absurd e.symm fig2_ne)
    · simp only [mem_insert, mem_singleton] at ho
      fin_cases w <;> rcases ho with rfl | rfl <;>
        norm_num [E, Fin.sum_univ_two, fig2_P0, fig2_P1]
  have := h _ (insert_nonempty _ _) _ hrec ![1, -1] (by simp)
  norm_num [E, stratValue, Fin.sum_univ_two, half] at this

/-- **Target 18 (Figure 2), the hull half holds.** `π = ½ P_a + ½ P_b` lies in the convex hull
of the candidates.
Source: [[Deference Done Better]] fn 32 ("this condition is necessary but not sufficient")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig2_mem_hull : half ∈ convexHull ℝ (↑(fig2.cands half) : Set (Fin 2 → ℝ)) := by
  rw [cands_eq_pair fig2 (by norm_num [half]) (by norm_num [half])]
  exact mem_hull_of_comb (x := fig2.P 0) (y := fig2.P 1) (by simp) (by simp)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (by ext w; fin_cases w <;> norm_num [half, fig2_P0, fig2_P1])

/-- Figure 2's informed expert at `a` is certain of `a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig2_informed0 : fig2.informed (fig2.P 0) 0 = 1 := by
  obtain ⟨hs0, _⟩ := fig2_selfMass
  simp only [Frame.informed, hs0]
  norm_num [fig2_P0]

/-- **Target 18 (Figure 2), modest informedness fails.** `P_a` is not modestly informed:
`C_a⁻ = {P_b}`, `P̂_a = (1, 0)`, and every point of `convexHull {(1, 0), (0.8, 0.2)}` has first
coordinate `≥ 0.8 > 0.2 = P_a(a)`. So the hull half of the fourth condition of Theorem 7.6 does
not imply the modest-informedness half.
Source: [[Deference Done Better]] §4 l. 325 (modestly informed), fn 32
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig2_not_modestlyInformed : ¬ fig2.ModestlyInformed (fig2.P 0) := by
  rintro ⟨_, hmem⟩
  have hsub : insert (fig2.informed (fig2.P 0)) (↑(fig2.candsMinus (fig2.P 0)) : Set (Fin 2 → ℝ)) ⊆
      {x : Fin 2 → ℝ | 4 / 5 ≤ x 0} := by
    intro y hy
    rcases Set.mem_insert_iff.1 hy with rfl | hy
    · show (4 : ℝ) / 5 ≤ fig2.informed (fig2.P 0) 0
      rw [fig2_informed0]; norm_num
    · rw [mem_coe, Frame.mem_candsMinus, Frame.mem_cands] at hy
      obtain ⟨hne, w, _, rfl⟩ := hy
      fin_cases w
      · exact absurd rfl hne
      · show (4 : ℝ) / 5 ≤ fig2.P 1 0
        norm_num [fig2_P1]
  have hconv : Convex ℝ {x : Fin 2 → ℝ | 4 / 5 ≤ x 0} :=
    convex_halfSpace_ge ⟨fun a b => rfl, fun c a => rfl⟩ _
  have := convexHull_min hsub hconv hmem
  rw [Set.mem_setOf_eq, fig2_P0] at this
  norm_num at this

/-- **Target 18 (Figure 2), summary.** New Reflection holds, `π` is in the hull of the candidates,
yet `P_a` is not modestly informed and Value fails.
Source: [[Deference Done Better]] §1 l. 102, fn 32
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig2_summary :
    NewReflects half fig2 ∧ half ∈ convexHull ℝ (↑(fig2.cands half) : Set (Fin 2 → ℝ)) ∧
    ¬ fig2.ModestlyInformed (fig2.P 0) ∧ ¬ Value half fig2 :=
  ⟨fig2_newReflects, fig2_mem_hull, fig2_not_modestlyInformed, fig2_not_value⟩

/-! ## Figure 3: valued but not reflected (Target 19) -/

/-- Figure 3's rows: `P_a = (0.9, 0.1)`, `P_b = (0.2, 0.8)`.
Source: [[Deference Done Better]] §1 l. 131 (Figure 3)
Kind: D
Fidelity: exact -/
def fig3 : Frame (Fin 2) :=
  mk2 ![9 / 10, 1 / 10] ![1 / 5, 4 / 5]
    (simplex2 _ _ (by norm_num) (by norm_num) (by norm_num))
    (simplex2 _ _ (by norm_num) (by norm_num) (by norm_num))

/-- Figure 3's first row.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig3_P0 : fig3.P 0 = ![9 / 10, 1 / 10] := rfl

/-- Figure 3's second row.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig3_P1 : fig3.P 1 = ![1 / 5, 4 / 5] := rfl

/-- Figure 3's two rows are distinct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig3_ne : fig3.P 0 ≠ fig3.P 1 := by
  intro h
  have := congrFun h 0
  rw [fig3_P0, fig3_P1] at this
  norm_num at this

/-- Figure 3's self-cell masses: `0.9` and `0.8`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig3_selfMass : fig3.selfMass (fig3.P 0) = 9 / 10 ∧ fig3.selfMass (fig3.P 1) = 4 / 5 := by
  obtain ⟨hc0, hc1⟩ := cell_of_ne fig3 fig3_ne
  constructor
  · rw [Frame.selfMass, hc0]; norm_num [mass, fig3_P0]
  · rw [Frame.selfMass, hc1]; norm_num [mass, fig3_P1]

/-- The uniform deferrer gives each Figure 3 cell mass `½`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig3_mass : mass half (fig3.cell (fig3.P 0)) = 1 / 2 ∧
    mass half (fig3.cell (fig3.P 1)) = 1 / 2 := by
  obtain ⟨hc0, hc1⟩ := cell_of_ne fig3 fig3_ne
  constructor
  · rw [hc0]; norm_num [mass, half]
  · rw [hc1]; norm_num [mass, half]

/-- Figure 3's informed experts are the two vertices.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig3_informed : fig3.informed (fig3.P 0) = ![1, 0] ∧ fig3.informed (fig3.P 1) = ![0, 1] := by
  obtain ⟨hs0, hs1⟩ := fig3_selfMass
  constructor
  · ext w
    fin_cases w
    · simp only [Frame.informed, hs0]; norm_num [fig3_P0]
    · norm_num [Frame.informed, hs0, fig3_ne.symm]
  · ext w
    fin_cases w
    · norm_num [Frame.informed, hs1, fig3_ne]
    · simp only [Frame.informed, hs1]; norm_num [fig3_P1]

/-- **Target 19 (Figure 3), Reflection fails.** `π(a | P = P_a) = 1 ≠ 0.9 = P_a(a)`.
Source: [[Deference Done Better]] §1 l. 128
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig3_not_reflects : ¬ Reflects half fig3 := by
  intro h
  obtain ⟨hc0, _⟩ := cell_of_ne fig3 fig3_ne
  obtain ⟨hm0, _⟩ := fig3_mass
  have := h (fig3.P 0) (fig3.P_mem_cands (by norm_num [half] : (0 : ℝ) < half 0)) 0
  rw [hm0, hc0] at this
  norm_num [ind, half, fig3_P0] at this

/-- **Target 19 (Figure 3), the frame is modest** at both worlds.
Source: [[Deference Done Better]] §1 l. 128 ("This frame is modest")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig3_modest : fig3.ModestAt 0 ∧ fig3.ModestAt 1 := by
  obtain ⟨hs0, hs1⟩ := fig3_selfMass
  constructor
  · rw [Frame.ModestAt, hs0]; norm_num
  · rw [Frame.ModestAt, hs1]; norm_num

/-- **Target 19 (Figure 3), the fourth condition of 7.6 holds** with explicit weights:
`P_a = 7/8·(1,0) + 1/8·P_b`, `P_b = 7/9·(0,1) + 2/9·P_a`, `π = 3/7·P_a + 4/7·P_b`. Non-degenerate:
the frame is modest, the two candidates are distinct, and `π` is strictly inside their segment.
Source: [[Deference Done Better]] §1 l. 128, §4 l. 327
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig3_hull : HullAndModestlyInformed half fig3 := by
  obtain ⟨hs0, hs1⟩ := fig3_selfMass
  obtain ⟨hi0, hi1⟩ := fig3_informed
  have hcands := cands_eq_pair fig3 (by norm_num [half] : (0 : ℝ) < half 0)
    (by norm_num [half] : (0 : ℝ) < half 1)
  have hcm0 : fig3.candsMinus (fig3.P 0) = {fig3.P 1} := by
    rw [candsMinus_eq fig3 fig3_ne (by norm_num [fig3_P0]) (by norm_num [fig3_P0])]
    ext σ
    simp only [mem_erase, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact absurd h2 h1
      · exact h2
    · rintro rfl; exact ⟨fig3_ne.symm, Or.inr rfl⟩
  have hcm1 : fig3.candsMinus (fig3.P 1) = {fig3.P 0} := by
    rw [candsMinus_eq fig3 fig3_ne (by norm_num [fig3_P1]) (by norm_num [fig3_P1])]
    ext σ
    simp only [mem_erase, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact h2
      · exact absurd h2 h1
    · rintro rfl; exact ⟨fig3_ne, Or.inl rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hcands]
    exact mem_hull_of_comb (x := fig3.P 0) (y := fig3.P 1) (by simp) (by simp)
      (by norm_num : (0 : ℝ) ≤ 3 / 7) (by norm_num : (0 : ℝ) ≤ 4 / 7) (by norm_num)
      (by ext w; fin_cases w <;> norm_num [half, fig3_P0, fig3_P1])
  · intro ρ hρ
    rw [hcands] at hρ
    simp only [mem_insert, mem_singleton] at hρ
    rcases hρ with rfl | rfl
    · refine ⟨by rw [hs0]; norm_num, ?_⟩
      rw [hcm0, hi0]
      exact mem_hull_of_comb (x := ![1, 0]) (y := fig3.P 1)
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (by simp))
        (by norm_num : (0 : ℝ) ≤ 7 / 8) (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num)
        (by ext w; fin_cases w <;> norm_num [fig3_P0, fig3_P1])
    · refine ⟨by rw [hs1]; norm_num, ?_⟩
      rw [hcm1, hi1]
      exact mem_hull_of_comb (x := ![0, 1]) (y := fig3.P 0)
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (by simp))
        (by norm_num : (0 : ℝ) ≤ 7 / 9) (by norm_num : (0 : ℝ) ≤ 2 / 9) (by norm_num)
        (by ext w; fin_cases w <;> norm_num [fig3_P0, fig3_P1])

/-- **Target 19 (Figure 3), Total Trust and Value hold** (through Theorem 7.6) although
Reflection fails and the frame is modest.
Source: [[Deference Done Better]] §1 l. 128, fn 18
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig3_totalTrust_value : TotalTrust half fig3 ∧ Value half fig3 :=
  ⟨(totalTrust_iff_hullAndModestlyInformed half_mem fig3).2 fig3_hull,
    (value_iff_totalTrust half_mem fig3).2
      ((totalTrust_iff_hullAndModestlyInformed half_mem fig3).2 fig3_hull)⟩

/-! ## The cell constraint is load-bearing (Target 23) -/

/-- **Value without the cell constraint** (an encoding variant, not DDB's notion): strategies are
any world-indexed choices that are optimal at each world.
Source: mandate Target 23 (encoding artifact)
Kind: D
Fidelity: variant: drops `P_w = P_v → S w = S v` -/
def ValueNoCell (π : Fin 2 → ℝ) (F : Frame (Fin 2)) : Prop :=
  ∀ 𝒪 : DecisionProblem (Fin 2), 𝒪.Nonempty → ∀ S : Fin 2 → (Fin 2 → ℝ), (∀ w, S w ∈ 𝒪) →
    (∀ w, ∀ o ∈ 𝒪, E (F.P w) o ≤ E (F.P w) (S w)) → ∀ o ∈ 𝒪, E π o ≤ stratValue π S

/-- The immodest frame with both rows `(½, ½)`.
Source: mandate Target 23
Kind: D
Fidelity: n/a -/
def flat : Frame (Fin 2) := mk2 half half half_mem half_mem

/-- Both rows of `flat` are the uniform distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem flat_P : flat.P 0 = half ∧ flat.P 1 = half := ⟨rfl, rfl⟩

/-- **Target 23.** On the immodest frame with both rows `(½, ½)` and `π = (½, ½)`, Value holds
(Theorem 7.6: `C_π = {P_a}`, `π = P_a`, `P_a` modestly informed with `P̂_a = P_a`), but the
*unconstrained* variant fails: `S_a = (−1, 1)`, `S_b = (1, −1)` on the menu `{(1, −1), (−1, 1)}`
is world-wise optimal (every option has expectation `0`) yet `E_π(S) = −1 < 0`. A Value
definition without the cell constraint would "refute" Theorem 2.2 — an encoding artifact.
Source: mandate Target 23; [[Deference Done Better]] §1 l. 117 (the cell constraint)
Kind: N-
Fidelity: variant: refutes the unconstrained encoding, not DDB's claim
Hyps: (a) none -/
theorem flat_value_not_valueNoCell : Value half flat ∧ ¬ ValueNoCell half flat := by
  obtain ⟨hP0, hP1⟩ := flat_P
  constructor
  · rw [value_iff_totalTrust half_mem, totalTrust_iff_hullAndModestlyInformed half_mem]
    have hcands : flat.cands half = {flat.P 0} := by
      ext σ
      rw [Frame.mem_cands]
      constructor
      · rintro ⟨w, _, rfl⟩
        fin_cases w
        · simp
        · rw [mem_singleton]; exact hP1.trans hP0.symm
      · intro h
        rw [mem_singleton] at h
        exact ⟨0, by norm_num [half], h.symm⟩
    have hcell : flat.cell (flat.P 0) = univ := by
      ext w
      fin_cases w
      · simp
      · simp only [Frame.mem_cell, mem_univ, iff_true]; exact hP1.trans hP0.symm
    have hsm : flat.selfMass (flat.P 0) = 1 := by
      rw [Frame.selfMass, hcell]
      norm_num [mass, Fin.sum_univ_two, hP0, half]
    refine ⟨?_, ?_⟩
    · rw [hcands]
      exact subset_convexHull ℝ _ (by simp [hP0])
    · intro ρ hρ
      rw [hcands, mem_singleton] at hρ
      subst hρ
      refine ⟨by rw [hsm]; norm_num, ?_⟩
      apply subset_convexHull ℝ _
      -- on an immodest frame the informed self is the row itself: `P̂_a = P_a`
      apply Set.mem_insert_iff.2
      left
      ext w
      fin_cases w
      · simp only [Frame.informed, hsm]; norm_num [hP0, half]
      · have e : flat.P 1 = flat.P 0 := hP1.trans hP0.symm
        simp only [Frame.informed, hsm]; norm_num [e, hP0, half]
  · intro h
    have := h {![1, -1], ![-1, 1]} (insert_nonempty _ _) ![![-1, 1], ![1, -1]]
      (fun w => by fin_cases w <;> simp)
      (fun w o ho => by
        simp only [mem_insert, mem_singleton] at ho
        fin_cases w <;> rcases ho with rfl | rfl <;>
          norm_num [E, Fin.sum_univ_two, hP0, hP1, half])
      ![1, -1] (by simp)
    norm_num [E, stratValue, Fin.sum_univ_two, half] at this

end

end Cleanroom.Found.LitDdbFrames.Examples
