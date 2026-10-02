import Cleanroom.Corrigibility.CorrLegitGeneral.Eval
import Cleanroom.Corrigibility.CorrLegitGeneral.WitnessesCompose
import Cleanroom.Found.LitDdbFrames.TotalTrust

/-!
# corr-legit-general — T10: full updating lands on the informed expert (ddb I17)

(a) Under Total Trust, New Reflection (`TotalTrust.newReflects`) gives the **informed tower**
`E_π(X) = ∑_{ρ ∈ C_π} π(P = ρ) · E_{P̂_ρ}(X)`: the current estimate is the expected
*informed*-expert estimate (ddb I17.2's reading of ABRAM's "a corrigible agent already believes
what it expects to be legitimately taught" — that this identity is what the sentence meant is a
bridge claim, ATTRIBUTION-UNVETTED; the identity itself is proved). The naive tower `E_π(X) = ∑_w π_w E_{P_w}(X)` is false
under Total Trust (fn 18): the witness below has `−1/5 ≠ −41/100`.
(b) ddb I17's witness: `W = Fin 3`, `X = (1, −2, 1)`, rows `(1/2, 1/2, 0)`, `(1/5, 4/5, 0)`,
`δ₂`, `π = (3/10, 2/5, 3/10)`. Total Trust holds (Theorem 4.1: `π = 8/15 P₀ + 1/6 P₁ + 3/10 δ₂`,
`P₀ = 3/8 δ₀ + 5/8 P₁`, `P₁ = 3/5 δ₁ + 2/5 P₀`); the press cell `{0, 1}` has
`E_π(X·𝟙_Pr) = −1/2 ≤ 0` (the coarse agent stops) while `π(· | P = P₀) = δ₀` and `E_{δ₀}(X) = 1 >
0` (the informed agent continues, the informed overseer agreeing).
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples
  Cleanroom.Lit.LitDdbFacts.Examples

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- Under New Reflection, a candidate's cell mass times its informed expectation is the
deferrer's partial expectation over the cell.
Source: [[ddb]] I17.2 l. 233 ("by total expectation and New Reflection")
Kind: L
Fidelity: exact -/
theorem cell_informed_expectation {π : W → ℝ} {F : Frame W} (hNR : NewReflects π F)
    {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) (X : W → ℝ) :
    mass π (F.cell ρ) * E (F.informed ρ) X = ∑ w, π w * ind (F.cell ρ) w * X w := by
  obtain ⟨hs, hid⟩ := hNR ρ hρ
  unfold E Frame.informed
  rw [mul_sum]
  apply sum_congr rfl
  intro w _
  by_cases hw : F.P w = ρ
  · have h := hid w
    rw [ind_cell_apply, if_pos hw] at h ⊢
    have e : mass π (F.cell ρ) * ρ w = π w * F.selfMass ρ := by linarith
    have key : mass π (F.cell ρ) * (ρ w / F.selfMass ρ) = π w := by
      rw [mul_div_assoc', e, mul_div_assoc, div_self hs.ne', mul_one]
    rw [if_pos hw, ← mul_assoc, key]
    ring
  · rw [ind_cell_apply, if_neg hw, if_neg hw]
    ring

/-- **The informed tower** (ddb I17.2; that it is "ABRAM's sentence in its true form" is ddb's
reading, ATTRIBUTION-UNVETTED): under Total Trust,
`E_π(X) = ∑_{ρ ∈ C_π} π(P = ρ) · E_{P̂_ρ}(X)`.
Source: [[ddb]] I17.2 l. 233; corr-wf13-040
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, `TotalTrust π F` -/
theorem informed_tower {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} (h : TotalTrust π F)
    (X : W → ℝ) : E π X = ∑ ρ ∈ F.cands π, mass π (F.cell ρ) * E (F.informed ρ) X := by
  have hNR := TotalTrust.newReflects hπ h
  have h1 : ∑ ρ ∈ F.cands π, mass π (F.cell ρ) * E (F.informed ρ) X =
      ∑ ρ ∈ F.cands π, ∑ w, π w * ind (F.cell ρ) w * X w :=
    sum_congr rfl (fun ρ hρ => cell_informed_expectation hNR hρ X)
  rw [h1, sum_comm]
  unfold E
  apply sum_congr rfl
  intro w _
  rcases (hπ w).lt_or_eq with hw | hw
  · have e : ∑ ρ ∈ F.cands π, π w * ind (F.cell ρ) w * X w =
        π w * X w * ∑ ρ ∈ F.cands π, ind (F.cell ρ) w := by
      rw [mul_sum]; apply sum_congr rfl; intro ρ _; ring
    rw [e]
    have hone : ∑ ρ ∈ F.cands π, ind (F.cell ρ) w = 1 := by
      simp only [ind_cell_apply]
      rw [sum_ite_eq (F.cands π) (F.P w) (fun _ => (1 : ℝ))]
      rw [if_pos (F.P_mem_cands hw)]
    rw [hone, mul_one]
  · rw [← hw]; simp

/-! ## ddb I17's witness -/

/-- ddb I17's frame: rows `(1/2, 1/2, 0)`, `(1/5, 4/5, 0)`, `δ₂`.
Source: [[ddb]] I17.3 l. 234
Kind: D
Fidelity: exact -/
def inf3 : Frame (Fin 3) :=
  mk3 ![1 / 2, 1 / 2, 0] ![1 / 5, 4 / 5, 0] ![0, 0, 1]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- ddb I17's deferrer `(3/10, 2/5, 3/10)`.
Source: [[ddb]] I17.3 l. 234
Kind: D
Fidelity: exact -/
def πinf : Fin 3 → ℝ := ![3 / 10, 2 / 5, 3 / 10]

/-- ddb I17's stakes variable `(1, −2, 1)`.
Source: [[ddb]] I17.3 l. 234
Kind: D
Fidelity: exact -/
def Xinf : Fin 3 → ℝ := ![1, -2, 1]

/-- The rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem inf3_P : inf3.P 0 = ![1 / 2, 1 / 2, 0] ∧ inf3.P 1 = ![1 / 5, 4 / 5, 0] ∧
    inf3.P 2 = ![0, 0, 1] := ⟨rfl, rfl, rfl⟩

/-- The rows are pairwise distinct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem inf3_ne : (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ) ≠ ![1 / 5, 4 / 5, 0] ∧
    (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ) ≠ ![0, 0, 1] ∧
    (![1 / 5, 4 / 5, 0] : Fin 3 → ℝ) ≠ ![0, 0, 1] := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrFun h 0; norm_num at this
  · have := congrFun h 0; norm_num at this
  · have := congrFun h 0; norm_num at this

/-- The cells are singletons.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem inf3_cell : inf3.cell ![1 / 2, 1 / 2, 0] = {0} ∧ inf3.cell ![1 / 5, 4 / 5, 0] = {1} ∧
    inf3.cell ![0, 0, 1] = {2} := by
  obtain ⟨h0, h1, h2⟩ := inf3_P
  obtain ⟨n01, n02, n12⟩ := inf3_ne
  refine ⟨?_, ?_, ?_⟩ <;>
    · ext w
      fin_cases w <;> simp +decide [Frame.mem_cell, h0, h1, h2, n01, n02, n12, n01.symm, n02.symm, n12.symm] <;>
        norm_num

/-- Supports of the rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem inf3_supp : supp (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ) = {0, 1} ∧
    supp (![1 / 5, 4 / 5, 0] : Fin 3 → ℝ) = {0, 1} ∧ supp (![0, 0, 1] : Fin 3 → ℝ) = {2} := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · ext w; fin_cases w <;> simp [supp, vec3_two] <;> norm_num

/-- Candidates of the rows under `inf3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem inf3_cands : inf3.cands ![1 / 2, 1 / 2, 0] = {![1 / 2, 1 / 2, 0], ![1 / 5, 4 / 5, 0]} ∧
    inf3.cands ![1 / 5, 4 / 5, 0] = {![1 / 2, 1 / 2, 0], ![1 / 5, 4 / 5, 0]} ∧
    inf3.cands ![0, 0, 1] = {![0, 0, 1]} := by
  obtain ⟨h0, h1, h2⟩ := inf3_P
  obtain ⟨s0, s1, s2⟩ := inf3_supp
  refine ⟨?_, ?_, ?_⟩
  · rw [Frame.cands, s0, image_insert, image_singleton, h0, h1]
  · rw [Frame.cands, s1, image_insert, image_singleton, h0, h1]
  · rw [Frame.cands, s2, image_singleton, h2]

/-- Self-masses and informed experts.
Source: [[ddb]] I17.3 l. 234 ("`P̂₁ = δ₁`")
Kind: L
Fidelity: n/a -/
theorem inf3_informed : inf3.selfMass ![1 / 2, 1 / 2, 0] = 1 / 2 ∧
    inf3.selfMass ![1 / 5, 4 / 5, 0] = 4 / 5 ∧ inf3.selfMass ![0, 0, 1] = 1 ∧
    inf3.informed ![1 / 2, 1 / 2, 0] = ![1, 0, 0] ∧ inf3.informed ![1 / 5, 4 / 5, 0] = ![0, 1, 0] ∧
    inf3.informed ![0, 0, 1] = ![0, 0, 1] := by
  obtain ⟨h0, h1, h2⟩ := inf3_P
  obtain ⟨n01, n02, n12⟩ := inf3_ne
  obtain ⟨c0, c1, c2⟩ := inf3_cell
  have s0 : inf3.selfMass ![1 / 2, 1 / 2, 0] = 1 / 2 := by
    unfold Frame.selfMass; rw [c0, mass_singleton]; rfl
  have s1 : inf3.selfMass ![1 / 5, 4 / 5, 0] = 4 / 5 := by
    unfold Frame.selfMass; rw [c1, mass_singleton]; rfl
  have s2 : inf3.selfMass ![0, 0, 1] = 1 := by
    unfold Frame.selfMass; rw [c2, mass_singleton]; rfl
  refine ⟨s0, s1, s2, ?_, ?_, ?_⟩
  · funext w
    fin_cases w
    · show inf3.informed ![1 / 2, 1 / 2, 0] 0 = ![1, 0, 0] 0
      rw [informed_apply, if_pos h0, s0]; norm_num
    · show inf3.informed ![1 / 2, 1 / 2, 0] 1 = ![1, 0, 0] 1
      rw [informed_apply, if_neg (by rw [h1]; exact n01.symm)]; simp
    · show inf3.informed ![1 / 2, 1 / 2, 0] 2 = ![1, 0, 0] 2
      rw [informed_apply, if_neg (by rw [h2]; exact n02.symm)]; simp [vec3_two]
  · funext w
    fin_cases w
    · show inf3.informed ![1 / 5, 4 / 5, 0] 0 = ![0, 1, 0] 0
      rw [informed_apply, if_neg (by rw [h0]; exact n01)]; simp
    · show inf3.informed ![1 / 5, 4 / 5, 0] 1 = ![0, 1, 0] 1
      rw [informed_apply, if_pos h1, s1]; norm_num
    · show inf3.informed ![1 / 5, 4 / 5, 0] 2 = ![0, 1, 0] 2
      rw [informed_apply, if_neg (by rw [h2]; exact n12.symm)]; simp [vec3_two]
  · funext w
    fin_cases w
    · show inf3.informed ![0, 0, 1] 0 = ![0, 0, 1] 0
      rw [informed_apply, if_neg (by rw [h0]; exact n02)]; simp
    · show inf3.informed ![0, 0, 1] 1 = ![0, 0, 1] 1
      rw [informed_apply, if_neg (by rw [h1]; exact n12)]; simp
    · show inf3.informed ![0, 0, 1] 2 = ![0, 0, 1] 2
      rw [informed_apply, if_pos h2, s2]; simp [vec3_two]

/-- The rows are modestly informed: `P₀ = 3/8 δ₀ + 5/8 P₁`, `P₁ = 3/5 δ₁ + 2/5 P₀`, `δ₂ ∈ CH{δ₂}`.
Source: [[ddb]] I17.3 l. 234
Kind: L
Fidelity: n/a -/
theorem inf3_modestlyInformed : inf3.ModestlyInformed ![1 / 2, 1 / 2, 0] ∧
    inf3.ModestlyInformed ![1 / 5, 4 / 5, 0] ∧ inf3.ModestlyInformed ![0, 0, 1] := by
  obtain ⟨s0, s1, s2, i0, i1, i2⟩ := inf3_informed
  obtain ⟨c0, c1, c2⟩ := inf3_cands
  obtain ⟨n01, _, _⟩ := inf3_ne
  refine ⟨⟨by rw [s0]; norm_num, ?_⟩, ⟨by rw [s1]; norm_num, ?_⟩, ⟨by rw [s2]; norm_num, ?_⟩⟩
  · rw [i0]
    have hcm : inf3.candsMinus ![1 / 2, 1 / 2, 0] = {![1 / 5, 4 / 5, 0]} := by
      rw [Frame.candsMinus, c0]
      exact erase_insert (by rw [mem_singleton]; exact n01)
    rw [hcm]
    exact mem_hull_of_comb2 (x := ![1, 0, 0]) (y := ![1 / 5, 4 / 5, 0])
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (by simp))
      (by norm_num : (0 : ℝ) ≤ 3 / 8) (by norm_num : (0 : ℝ) ≤ 5 / 8) (by norm_num)
      (by ext w; fin_cases w <;> norm_num [vec3_two])
  · rw [i1]
    have hcm : inf3.candsMinus ![1 / 5, 4 / 5, 0] = {![1 / 2, 1 / 2, 0]} := by
      rw [Frame.candsMinus, c1]
      ext σ
      simp only [mem_erase, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hne, h | h⟩
        · exact h
        · exact absurd h hne
      · rintro rfl; exact ⟨n01, Or.inl rfl⟩
    rw [hcm]
    exact mem_hull_of_comb2 (x := ![0, 1, 0]) (y := ![1 / 2, 1 / 2, 0])
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (by simp))
      (by norm_num : (0 : ℝ) ≤ 3 / 5) (by norm_num : (0 : ℝ) ≤ 2 / 5) (by norm_num)
      (by ext w; fin_cases w <;> norm_num [vec3_two])
  · rw [i2]
    exact subset_convexHull ℝ _ (Set.mem_insert _ _)

/-- **ddb I17's deferrer totally trusts the frame** (Theorem 4.1 with the stated weights:
`π = 8/15 P₀ + 1/6 P₁ + 3/10 δ₂`).
Source: [[ddb]] I17.3 l. 234
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem inf3_totalTrust : TotalTrust πinf inf3 := by
  obtain ⟨h0, h1, h2⟩ := inf3_P
  obtain ⟨mi0, mi1, mi2⟩ := inf3_modestlyInformed
  have hπ : πinf ∈ stdSimplex ℝ (Fin 3) :=
    simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hc : inf3.cands πinf = {![1 / 2, 1 / 2, 0], ![1 / 5, 4 / 5, 0], ![0, 0, 1]} := by
    rw [cands_eq_triple inf3 (by norm_num [πinf]) (by norm_num [πinf])
      (by norm_num [πinf, vec3_two]), h0, h1, h2]
  refine (totalTrust_iff_hullAndModestlyInformed hπ inf3).2 ⟨?_, ?_⟩
  · rw [hc]
    exact mem_hull_of_comb3 (x := ![1 / 2, 1 / 2, 0]) (y := ![1 / 5, 4 / 5, 0]) (z := ![0, 0, 1])
      (by simp) (by simp) (by simp)
      (by norm_num : (0 : ℝ) ≤ 8 / 15) (by norm_num : (0 : ℝ) ≤ 1 / 6)
      (by norm_num : (0 : ℝ) ≤ 3 / 10) (by norm_num)
      (by ext w; fin_cases w <;> norm_num [πinf, vec3_two])
  · intro ρ hρ
    rw [hc] at hρ
    simp only [mem_insert, mem_singleton] at hρ
    rcases hρ with rfl | rfl | rfl
    · exact mi0
    · exact mi1
    · exact mi2

/-- **ddb I17's arithmetic**: the coarse agent stops (`E_π(X·𝟙_{0,1}) = −1/2`), the informed
agent continues (`E_{P̂₀}(X) = 1`), and the naive tower is false (`∑_w π_w E_{P_w}(X) = −41/100`
while `E_π(X) = −1/5`).
Source: [[ddb]] I17.3 l. 234; fn 18
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem inf3_arithmetic : E πinf (fun w => Xinf w * ind {0, 1} w) = -1 / 2 ∧
    E (inf3.informed (inf3.P 0)) Xinf = 1 ∧
    ∑ w, πinf w * E (inf3.P w) Xinf = -41 / 100 ∧ E πinf Xinf = -1 / 5 := by
  obtain ⟨h0, h1, h2⟩ := inf3_P
  obtain ⟨_, _, _, i0, _, _⟩ := inf3_informed
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp +decide [E, Fin.sum_univ_three, Xinf, ind, πinf, vec3_two] <;> norm_num
  · rw [h0, i0]; simp [E, Fin.sum_univ_three, Xinf, vec3_two] <;> norm_num
  · simp [E, Fin.sum_univ_three, Xinf, πinf, h0, h1, h2, vec3_two] <;> norm_num
  · simp [E, Fin.sum_univ_three, Xinf, πinf, vec3_two] <;> norm_num

/-- **The naive tower is refuted under Total Trust** (fn 18): on `inf3`,
`E_π(X) ≠ ∑_w π_w E_{P_w}(X)` while the informed tower holds.
Source: [[ddb]] I17.2 l. 233 ("false in the tower form … which Value does not entail (fn 18)")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem inf3_tower_refuted : TotalTrust πinf inf3 ∧ E πinf Xinf ≠ ∑ w, πinf w * E (inf3.P w) Xinf := by
  obtain ⟨_, _, h3, h4⟩ := inf3_arithmetic
  refine ⟨inf3_totalTrust, ?_⟩
  rw [h3, h4]; norm_num

end

end Cleanroom.Corrigibility.CorrLegitGeneral
