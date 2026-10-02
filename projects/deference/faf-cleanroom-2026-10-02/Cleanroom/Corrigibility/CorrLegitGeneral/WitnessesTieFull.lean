import Cleanroom.Corrigibility.CorrLegitGeneral.WitnessesFn66

/-!
# corr-legit-general — witnesses on four worlds, IV: the tie refutation with full support

`tie4` (`WitnessesFn66.lean`) refutes "two-cell local Total Trust ⟹ two-cell local Value" (fn 64's
reading) with a deferrer `(3/5, 2/5, 0, 0)` whose second support row lives on `π`-null worlds.
The round-1 adversarial audit asked whether the refutation needs null worlds (N4(b)) and showed
it does not; its probe `TieFullSupport.lean` is adopted here. The deferrer
`πF = (2/5, 1/10, 1/5, 3/10)` has full support and so does every row: `A = (2/5, 1/5, 1/5, 1/5)`
at worlds `0, 1`, `B = (1/5, 1/5, 2/5, 1/5)` at worlds `2, 3`; `q = {0, 2}` (the package's `qtie`);
`A(q) = B(q) = πF(q) = 3/5`. The menu `{oA, oB} = {𝟙_q − 3/5, 3/5 − 𝟙_q}` ties at every world; the
strategy `oB` on the `A`-cell, `oA` on the `B`-cell is cellwise in the row and recommended, and
`E_π(S) = −1/5 < 0 = E_π(oB)`. So the refutation is not an artifact of null worlds or Dirac rows.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Lit.LitDdbAccuracyMm
  Cleanroom.Lit.LitDdbFacts.Examples

noncomputable section

/-- The full-support tie frame: rows `A = (2/5, 1/5, 1/5, 1/5)` at `0, 1` and
`B = (1/5, 1/5, 2/5, 1/5)` at `2, 3`.
Source: audit r1 adversarial N4(b) (probe `TieFullSupport.lean`); this package (T4(b) refutation)
Kind: D
Fidelity: n/a -/
def tieF : Frame (Fin 4) :=
  mk4 ![2 / 5, 1 / 5, 1 / 5, 1 / 5] ![2 / 5, 1 / 5, 1 / 5, 1 / 5] ![1 / 5, 1 / 5, 2 / 5, 1 / 5]
    ![1 / 5, 1 / 5, 2 / 5, 1 / 5]
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- The full-support deferrer `(2/5, 1/10, 1/5, 3/10)`.
Source: audit r1 adversarial N4(b)
Kind: D
Fidelity: n/a -/
def πF : Fin 4 → ℝ := ![2 / 5, 1 / 10, 1 / 5, 3 / 10]

/-- `tieF`'s rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tieF_P : tieF.P 0 = ![2 / 5, 1 / 5, 1 / 5, 1 / 5] ∧ tieF.P 1 = ![2 / 5, 1 / 5, 1 / 5, 1 / 5] ∧
    tieF.P 2 = ![1 / 5, 1 / 5, 2 / 5, 1 / 5] ∧ tieF.P 3 = ![1 / 5, 1 / 5, 2 / 5, 1 / 5] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The two rows differ.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tieF_AB_ne : (![2 / 5, 1 / 5, 1 / 5, 1 / 5] : Fin 4 → ℝ) ≠ ![1 / 5, 1 / 5, 2 / 5, 1 / 5] := by
  intro h; have := congrFun h 0; norm_num at this

/-- The deferrer has full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πF_pos : ∀ w, 0 < πF w := by
  intro w; fin_cases w <;> norm_num [πF, vec4_two, vec4_three]

/-- Every row has full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tieF_rows_pos : ∀ w v, 0 < tieF.P w v := by
  obtain ⟨h0, h1, h2, h3⟩ := tieF_P
  intro w v
  fin_cases w <;> fin_cases v <;> norm_num [h0, h1, h2, h3, vec4_two, vec4_three]

/-- Every row gives `q` probability `3/5`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tieF_mass_q : mass (tieF.P 0) qtie = 3 / 5 ∧ mass (tieF.P 1) qtie = 3 / 5 ∧
    mass (tieF.P 2) qtie = 3 / 5 ∧ mass (tieF.P 3) qtie = 3 / 5 := by
  obtain ⟨h0, h1, h2, h3⟩ := tieF_P
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp +decide [mass_eq_sum_ite, Fin.sum_univ_four, qtie, h0, h1, h2, h3, vec4_two, vec4_three] <;>
    norm_num

/-- **`tieF` totally trusts on `{q, ¬q}`**: a single cluster at `P(q) = 3/5` with `πF(q) = 3/5`,
so both Simple-Trust cuts hold at every threshold.
Source: audit r1 adversarial N4(b); this package (T4(b) refutation)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem tieF_totalTrustWrt : TotalTrustWrt (questionOf qtie) πF tieF := by
  rw [totalTrustWrt_questionOf_iff (fun w => (πF_pos w).le)]
  obtain ⟨m0, m1, m2, m3⟩ := tieF_mass_q
  constructor
  · intro t
    rw [mass_probEvent_eq, mass_inter_probEvent_eq]
    simp only [Fin.sum_univ_four, m0, m1, m2, m3]
    simp +decide [πF, qtie, vec4_two, vec4_three]
    split_ifs <;> (try norm_num) <;> (try linarith)
  · intro t
    rw [mass_probEventLE_eq, mass_inter_probEventLE_eq]
    simp only [Fin.sum_univ_four, m0, m1, m2, m3]
    simp +decide [πF, qtie, vec4_two, vec4_three]
    split_ifs <;> (try norm_num) <;> (try linarith)

/-- The tie-split strategy: `oB` on the `A`-cell `{0, 1}`, `oA` on the `B`-cell `{2, 3}`.
Source: audit r1 adversarial N4(b)
Kind: D
Fidelity: n/a -/
def SF : Fin 4 → (Fin 4 → ℝ) := ![oB, oB, oA, oA]

/-- `SF` is recommended for the menu `{oA, oB}`: cellwise in the row, and every option ties at
every world (`E_{P_w}(oA) = 0 = E_{P_w}(oB)`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem SF_recommended : tieF.Recommended {oA, oB} SF := by
  obtain ⟨h0, h1, h2, h3⟩ := tieF_P
  refine ⟨⟨fun w => ?_, fun w v hwv => ?_⟩, fun w o ho => ?_⟩
  · fin_cases w <;> simp [SF, vec4_two, vec4_three]
  · fin_cases w <;> fin_cases v <;>
      first
        | rfl
        | (have := congrFun hwv 0; norm_num [h0, h1, h2, h3, vec4_two, vec4_three] at this; done)
  · simp only [mem_insert, mem_singleton] at ho
    fin_cases w <;> rcases ho with rfl | rfl <;>
      simp +decide [E, Fin.sum_univ_four, SF, oA, oB, ind, qtie, h0, h1, h2, h3, vec4_two,
        vec4_three] <;> norm_num

/-- **`tieF` does not value on `{q, ¬q}`**: `E_π(SF) = −1/5 < 0 = E_π(oB)`.
Source: audit r1 adversarial N4(b); this package (T4(b) refutation)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem tieF_not_valuesWrt : ¬ ValuesWrt (questionOf qtie) πF tieF := by
  intro h
  have hmeas : ∀ o ∈ ({oA, oB} : DecisionProblem (Fin 4)), MeasurableWrt (questionOf qtie) o := by
    intro o ho
    simp only [mem_insert, mem_singleton] at ho
    have hq := measurableWrt_questionOf_ind qtie
    rcases ho with rfl | rfl
    · intro w v hwv; simp only [oA, hq w v hwv]
    · intro w v hwv; simp only [oB, hq w v hwv]
  have := h {oA, oB} (insert_nonempty _ _) hmeas SF SF_recommended oB (by simp)
  simp +decide [E, stratValue, Fin.sum_univ_four, SF, oA, oB, ind, qtie, πF, vec4_two,
    vec4_three] at this <;> norm_num at this

/-- **The tie refutation is not a null-world artifact**: a full-support simplex deferrer and a
frame with full-support rows, with two-cell local Total Trust and without two-cell local Value
(fn 64's reading). Both `q`-cells have positive mass (`3/5`, `2/5`) and the rows differ.
Source: audit r1 adversarial N4(b); [[ddb-mm-authors]] C5 l. 93 (the refuted claim); findings F1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem tieF_witness : (∀ w, 0 < πF w) ∧ (∀ w v, 0 < tieF.P w v) ∧ πF ∈ stdSimplex ℝ (Fin 4) ∧
    TotalTrustWrt (questionOf qtie) πF tieF ∧ ¬ ValuesWrt (questionOf qtie) πF tieF :=
  ⟨πF_pos, tieF_rows_pos,
    simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    tieF_totalTrustWrt, tieF_not_valuesWrt⟩

end

end Cleanroom.Corrigibility.CorrLegitGeneral
