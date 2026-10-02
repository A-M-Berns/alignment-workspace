import Cleanroom.Corrigibility.CorrLegitGeneral.Eval
import Cleanroom.Lit.LitDdbFacts.Examples

/-!
# corr-legit-general — witnesses on four worlds, I: DDB fn 66 and the tie counterexample

* `fn66`: DDB's fn 66 frame (rows `δ₀, (0, 3/5, 2/5, 0), (0, 3/5, 2/5, 0), δ₃`, uniform `π`,
  `q = {w₁, w₂}` in DDB's 1-indexed labels = `{0, 1}` here): immodest, local Reflection on
  `{q, ¬q}` fails (`π(q | P(q) = 3/5) = 1/2`), local Total Trust holds (the Simple-Trust cuts
  `2/3 ≥ 3/5` and `1/3 ≤ 3/5` at the attained thresholds). Local Value for this frame is
  `TwoCell.lean`'s corollary (its rows are determined by `P_w(q)`).
* `tie4`: the refutation of "two-cell local Total Trust ⟹ two-cell local Value" in fn 64's
  literal reading: `q = {0, 2}`, `π = (3/5, 2/5, 0, 0)`, rows `(3/5, 2/5, 0, 0)`,
  `(0, 0, 3/5, 2/5)`, `δ₂`, `δ₃`. Both support rows have `P(q) = 3/5` and `π(q) = 3/5`, so
  `π(q | P(q) = 3/5) = π(q)` on the `P(q)`-level set and the deferrer totally trusts on `{q, ¬q}`
  (not DDB's local Reflection, which conditions on the cell `[P = ρ]` and fails here: at `ρ = P₀`,
  `π(q ∩ {0}) = 3/5 ≠ 9/25`; audit r1 N1/N7); but the rows differ, so a strategy may break the tie
  of the menu `{𝟙_q − 3/5, 3/5 − 𝟙_q}` oppositely at the two worlds and loses `12/25` against the
  constant-sign option. The same refutation with full support everywhere is
  `WitnessesTieFull.lean`'s `tieF`.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Lit.LitDdbAccuracyMm
  Cleanroom.Lit.LitDdbFacts.Examples

noncomputable section

/-! ## DDB fn 66 -/

/-- DDB fn 66's frame.
Source: [[Deference Done Better]] fn 66 l. 1239
Kind: D
Fidelity: exact -/
def fn66 : Frame (Fin 4) :=
  mk4 ![1, 0, 0, 0] ![0, 3 / 5, 2 / 5, 0] ![0, 3 / 5, 2 / 5, 0] ![0, 0, 0, 1]
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- The uniform deferrer on four worlds.
Source: [[Deference Done Better]] fn 66 l. 1239
Kind: D
Fidelity: exact -/
def quarter : Fin 4 → ℝ := fun _ => 1 / 4

/-- fn 66's proposition `q` (DDB's blue worlds `w₁, w₂`, 0-indexed `{0, 1}`).
Source: [[Deference Done Better]] fn 66 l. 1239
Kind: D
Fidelity: exact (index shift disclosed) -/
def q66 : Finset (Fin 4) := {0, 1}

/-- `fn66`'s rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fn66_P : fn66.P 0 = ![1, 0, 0, 0] ∧ fn66.P 1 = ![0, 3 / 5, 2 / 5, 0] ∧
    fn66.P 2 = ![0, 3 / 5, 2 / 5, 0] ∧ fn66.P 3 = ![0, 0, 0, 1] := ⟨rfl, rfl, rfl, rfl⟩

/-- `fn66`'s three distinct rows differ pairwise.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fn66_ne : (![1, 0, 0, 0] : Fin 4 → ℝ) ≠ ![0, 3 / 5, 2 / 5, 0] ∧
    (![1, 0, 0, 0] : Fin 4 → ℝ) ≠ ![0, 0, 0, 1] ∧
    (![0, 3 / 5, 2 / 5, 0] : Fin 4 → ℝ) ≠ ![0, 0, 0, 1] := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrFun h 0; norm_num at this
  · have := congrFun h 0; norm_num at this
  · have := congrFun h 1; norm_num at this

/-- `fn66`'s cells.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fn66_cell : fn66.cell ![1, 0, 0, 0] = {0} ∧ fn66.cell ![0, 3 / 5, 2 / 5, 0] = {1, 2} ∧
    fn66.cell ![0, 0, 0, 1] = {3} := by
  obtain ⟨h0, h1, h2, h3⟩ := fn66_P
  obtain ⟨n01, n03, n13⟩ := fn66_ne
  refine ⟨?_, ?_, ?_⟩ <;>
    · ext w
      fin_cases w <;> simp [Frame.mem_cell, h0, h1, h2, h3, n01, n03, n13, n01.symm, n03.symm,
        n13.symm]

/-- The rows' probabilities of `q`: `1, 3/5, 3/5, 0`.
Source: [[Deference Done Better]] fn 66 l. 1239
Kind: L
Fidelity: n/a -/
theorem fn66_mass_q : mass (fn66.P 0) q66 = 1 ∧ mass (fn66.P 1) q66 = 3 / 5 ∧
    mass (fn66.P 2) q66 = 3 / 5 ∧ mass (fn66.P 3) q66 = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := fn66_P
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp +decide [mass_eq_sum_ite, Fin.sum_univ_four, q66, h0, h1, h2, h3, vec4_two, vec4_three] <;>
    norm_num

/-- **fn 66 is immodest**: each row's self-cell has mass one.
Source: [[Deference Done Better]] fn 66 l. 1239 ("since the frame is immodest")
Kind: L
Fidelity: exact -/
theorem fn66_immodest : fn66.Immodest := by
  obtain ⟨h0, h1, h2, h3⟩ := fn66_P
  obtain ⟨c0, c1, c3⟩ := fn66_cell
  intro w
  fin_cases w
  · show fn66.selfMass (fn66.P 0) = 1
    unfold Frame.selfMass; rw [h0, c0]; unfold mass; rw [Finset.sum_singleton]; norm_num
  · show fn66.selfMass (fn66.P 1) = 1
    unfold Frame.selfMass; rw [h1, c1]; unfold mass
    rw [Finset.sum_pair (by decide)]; norm_num [vec4_two]
  · show fn66.selfMass (fn66.P 2) = 1
    unfold Frame.selfMass; rw [h2, c1]; unfold mass
    rw [Finset.sum_pair (by decide)]; norm_num [vec4_two]
  · show fn66.selfMass (fn66.P 3) = 1
    unfold Frame.selfMass; rw [h3, c3]; unfold mass; rw [Finset.sum_singleton]; norm_num [vec4_three]

/-- **fn 66, local Reflection fails**: at the candidate `(0, 3/5, 2/5, 0)` (cell `{1, 2}`) and
the answer `q`, `π(q ∧ [P = ρ]) = 1/4 ≠ 3/10 = π(P = ρ) · ρ(q)`.
Source: [[Deference Done Better]] fn 66 l. 1239 (`π(q | P(q) = 0.6) = 0.5`); [[legitimacy]]
R2.3 l. 58 (E4)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fn66_not_reflectsWrt : ¬ ReflectsWrt (questionOf q66) quarter fn66 := by
  intro h
  obtain ⟨_, h1, _, _⟩ := fn66_P
  obtain ⟨_, c1, _⟩ := fn66_cell
  have hc : fn66.P 1 ∈ fn66.cands quarter := fn66.P_mem_cands (by norm_num [quarter])
  have := h _ hc {true}
  rw [answer_questionOf_true, h1, c1] at this
  simp +decide [mass_eq_sum_ite, Fin.sum_univ_four, q66, quarter, vec4_two, vec4_three] at this <;>
    norm_num at this

/-- **fn 66, local Total Trust holds**: the Simple-Trust cuts at `q` for every threshold
(attained values `0, 3/5, 1`: `π(q | P(q) ≥ 3/5) = 2/3 ≥ 3/5`, `π(q | P(q) ≤ 3/5) = 1/3 ≤ 3/5`).
Source: [[Deference Done Better]] fn 66 l. 1239; [[legitimacy]] R2.3 l. 58
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fn66_totalTrustWrt : TotalTrustWrt (questionOf q66) quarter fn66 := by
  rw [totalTrustWrt_questionOf_iff (fun _ => by norm_num [quarter])]
  obtain ⟨m0, m1, m2, m3⟩ := fn66_mass_q
  constructor
  · intro t
    rw [mass_probEvent_eq, mass_inter_probEvent_eq]
    simp only [Fin.sum_univ_four, m0, m1, m2, m3]
    simp +decide [quarter, q66, vec4_two, vec4_three]
    split_ifs <;> (try norm_num) <;> (try linarith)
  · intro t
    rw [mass_probEventLE_eq, mass_inter_probEventLE_eq]
    simp only [Fin.sum_univ_four, m0, m1, m2, m3]
    simp +decide [quarter, q66, vec4_two, vec4_three]
    split_ifs <;> (try norm_num) <;> (try linarith)

/-! ## The tie counterexample -/

/-- The tie frame: rows `(3/5, 2/5, 0, 0)`, `(0, 0, 3/5, 2/5)`, `δ₂`, `δ₃`.
Source: this package (T4(b) refutation; no example in the sources)
Kind: D
Fidelity: n/a -/
def tie4 : Frame (Fin 4) :=
  mk4 ![3 / 5, 2 / 5, 0, 0] ![0, 0, 3 / 5, 2 / 5] ![0, 0, 1, 0] ![0, 0, 0, 1]
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- The tie deferrer `(3/5, 2/5, 0, 0)`.
Source: this package (T4(b) refutation)
Kind: D
Fidelity: n/a -/
def πtie : Fin 4 → ℝ := ![3 / 5, 2 / 5, 0, 0]

/-- The tie proposition `q = {0, 2}`: both support rows give it probability `3/5`.
Source: this package (T4(b) refutation)
Kind: D
Fidelity: n/a -/
def qtie : Finset (Fin 4) := {0, 2}

/-- `tie4`'s rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tie4_P : tie4.P 0 = ![3 / 5, 2 / 5, 0, 0] ∧ tie4.P 1 = ![0, 0, 3 / 5, 2 / 5] ∧
    tie4.P 2 = ![0, 0, 1, 0] ∧ tie4.P 3 = ![0, 0, 0, 1] := ⟨rfl, rfl, rfl, rfl⟩

/-- `tie4`'s rows are pairwise distinct (so the cell constraint never binds).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tie4_ne : tie4.P 0 ≠ tie4.P 1 ∧ tie4.P 0 ≠ tie4.P 2 ∧ tie4.P 0 ≠ tie4.P 3 ∧
    tie4.P 1 ≠ tie4.P 2 ∧ tie4.P 1 ≠ tie4.P 3 ∧ tie4.P 2 ≠ tie4.P 3 := by
  obtain ⟨h0, h1, h2, h3⟩ := tie4_P
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrFun h 0; rw [h0, h1] at this; norm_num at this
  · have := congrFun h 0; rw [h0, h2] at this; norm_num at this
  · have := congrFun h 0; rw [h0, h3] at this; norm_num at this
  · have := congrFun h 2; rw [h1, h2] at this; norm_num [vec4_two] at this
  · have := congrFun h 2; rw [h1, h3] at this; norm_num [vec4_two] at this
  · have := congrFun h 2; rw [h2, h3] at this; norm_num [vec4_two] at this

/-- The rows' probabilities of `q`: `3/5, 3/5, 1, 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tie4_mass_q : mass (tie4.P 0) qtie = 3 / 5 ∧ mass (tie4.P 1) qtie = 3 / 5 ∧
    mass (tie4.P 2) qtie = 1 ∧ mass (tie4.P 3) qtie = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := tie4_P
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp +decide [mass_eq_sum_ite, Fin.sum_univ_four, qtie, h0, h1, h2, h3, vec4_two, vec4_three] <;>
    norm_num

/-- **`tie4` totally trusts on `{q, ¬q}`**: the single support cluster at `P(q) = 3/5` has
`π(q | P(q) = 3/5) = 3/5 = π(q)`, so both Simple-Trust cuts hold at every threshold. (This is
agreement on the `P(q)`-level set, not DDB's cellwise `ReflectsWrt`, which fails on `tie4`.)
Source: this package (T4(b) refutation)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem tie4_totalTrustWrt : TotalTrustWrt (questionOf qtie) πtie tie4 := by
  rw [totalTrustWrt_questionOf_iff (fun w => by fin_cases w <;> norm_num [πtie, vec4_two, vec4_three])]
  obtain ⟨m0, m1, m2, m3⟩ := tie4_mass_q
  constructor
  · intro t
    rw [mass_probEvent_eq, mass_inter_probEvent_eq]
    simp only [Fin.sum_univ_four, m0, m1, m2, m3]
    simp +decide [πtie, qtie, vec4_two, vec4_three]
    split_ifs <;> (try norm_num) <;> (try linarith)
  · intro t
    rw [mass_probEventLE_eq, mass_inter_probEventLE_eq]
    simp only [Fin.sum_univ_four, m0, m1, m2, m3]
    simp +decide [πtie, qtie, vec4_two, vec4_three]
    split_ifs <;> (try norm_num) <;> (try linarith)

/-- The two tied options: `𝟙_q − 3/5` and `3/5 − 𝟙_q`.
Source: this package (T4(b) refutation)
Kind: D
Fidelity: n/a -/
def oA : Fin 4 → ℝ := fun w => ind qtie w - 3 / 5

/-- The second tied option.
Source: this package (T4(b) refutation)
Kind: D
Fidelity: n/a -/
def oB : Fin 4 → ℝ := fun w => 3 / 5 - ind qtie w

/-- The adversarial tie-break: the decreasing option at `0 ∈ q`, the increasing one at `1 ∉ q`
(and the unique optimum at the null worlds).
Source: this package (T4(b) refutation)
Kind: D
Fidelity: n/a -/
def Stie : Fin 4 → (Fin 4 → ℝ) := ![oB, oA, oA, oB]

/-- `Stie` is recommended by `tie4` for `{oA, oB}`: both options have expectation `0` at the two
support rows (a tie), `oA` is optimal at `δ₂` and `oB` at `δ₃`; the rows are distinct, so the
cell constraint is vacuous.
Source: this package (T4(b) refutation)
Kind: L
Fidelity: n/a -/
theorem Stie_recommended : tie4.Recommended {oA, oB} Stie := by
  obtain ⟨h0, h1, h2, h3⟩ := tie4_P
  obtain ⟨n01, n02, n03, n12, n13, n23⟩ := tie4_ne
  refine ⟨⟨fun w => ?_, fun w v hwv => ?_⟩, fun w o ho => ?_⟩
  · fin_cases w <;> simp [Stie, vec4_two, vec4_three]
  · fin_cases w <;> fin_cases v <;>
      first
        | rfl
        | (have := congrFun hwv 0; norm_num [h0, h1, h2, h3, vec4_two, vec4_three] at this; done)
        | (have := congrFun hwv 2; norm_num [h0, h1, h2, h3, vec4_two, vec4_three] at this; done)
  · simp only [mem_insert, mem_singleton] at ho
    fin_cases w <;> rcases ho with rfl | rfl <;>
      simp +decide [E, Fin.sum_univ_four, Stie, oA, oB, ind, qtie, h0, h1, h2, h3, vec4_two,
        vec4_three] <;> norm_num

/-- **The refutation**: `tie4` does not value the frame with respect to `{q, ¬q}` — the menu
`{oA, oB}` is `{q, ¬q}`-measurable, `Stie` is recommended, and
`E_π(Stie) = −12/25 < 0 = E_π(oB)`.
Source: this package (T4(b) refutation of [[ddb-mm-authors]] C5 l. 95, [[legitimacy]] R5.3
l. 100, [[legitimacy-general-final]] Open problem 4 l. 205; [[Deference Done Better]] fn 64/65)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem tie4_not_valuesWrt : ¬ ValuesWrt (questionOf qtie) πtie tie4 := by
  intro h
  have hmeas : ∀ o ∈ ({oA, oB} : DecisionProblem (Fin 4)), MeasurableWrt (questionOf qtie) o := by
    intro o ho
    simp only [mem_insert, mem_singleton] at ho
    have hq := measurableWrt_questionOf_ind qtie
    rcases ho with rfl | rfl
    · intro w v hwv; simp only [oA, hq w v hwv]
    · intro w v hwv; simp only [oB, hq w v hwv]
  have := h {oA, oB} (insert_nonempty _ _) hmeas Stie Stie_recommended oB (by simp)
  simp +decide [E, stratValue, Fin.sum_univ_four, Stie, oA, oB, ind, qtie, πtie, vec4_two,
    vec4_three] at this <;> norm_num at this

/-- **The refutation, packaged**: two-cell local Total Trust without two-cell local Value.
Source: this package (T4(b) refutation)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem tie4_refutes_two_cell : πtie ∈ stdSimplex ℝ (Fin 4) ∧
    TotalTrustWrt (questionOf qtie) πtie tie4 ∧ ¬ ValuesWrt (questionOf qtie) πtie tie4 :=
  ⟨simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    tie4_totalTrustWrt, tie4_not_valuesWrt⟩

end

end Cleanroom.Corrigibility.CorrLegitGeneral
