import Cleanroom.Lit.LitDdbAccuracyMm.MM.Defs

/-!
# MM Theorem 3.2 = DDB Theorem 2.2 — three readings (Target 14)

MM (l. 79–81): "We represent this with an expert strategy `S = {S_ω}` where
`S_ω ∈ argmax_{O ∈ 𝒪} E_ω[O]` … We say the principal values the agent if delegation is always
weakly preferred: for any decision problem `𝒪` and any option `O ∈ 𝒪`, `E_π[S] ≥ E_π[O]`."
Theorem 3.2 (l. 87): "The principal values the agent if and only if she totally trusts the agent."
MM's `S` is world-indexed with **no cell constraint** (DDB's `S_w` is determined by `P_w`).
Three readings:

(a) `ValuesAllSel` — every world-indexed optimal selection is valued: **refuted**; the "if"
    direction of 3.2 is false. The N+ witness (audit r1 repair) is `dup`: three worlds, rows
    `(½, ½, 0)`, `(½, ½, 0)`, `(0, 0, 1)` (the expert knows the world at world `2`, no row equals
    `π`), `π = (⅓, ⅓, ⅓)` totally trusts the frame, and the world-indexed optimal selection on the
    tie menu `{(1, −1, 0), (−1, 1, 0)}` is worth `−2/3 < 0`. The foundation's `flat` frame (both
    rows `= π`) refutes the reading too but is graded N− (the expert is the deferrer). A
    refutation needs a duplicated row: with pairwise-distinct rows the reading is `Value`
    (`valuesAllSel_iff_value_of_rows_distinct`).
(b) `ValuesSomeSel` — some world-indexed optimal selection is valued: **proved** equivalent to
    Total Trust. (⟸) the foundation's cell-wise recommended strategy is a selection; (⟹) on a
    tie-free two-option menu `{X, const s'}` the selection is forced, and a midpoint choice of
    `s'` below `s` avoids the limit.
(c) the cell-constrained reading is DDB's `Value`; the foundation's `value_iff_totalTrust`.
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm.MM

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- A **world-indexed optimal selection** `S_ω ∈ argmax_{O ∈ 𝒪} E_ω[O]` — MM's expert strategy,
without DDB's cell constraint.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.1.1 l. 79
Kind: D
Fidelity: exact (MM's literal `S`) -/
def IsSelection (F : Frame W) (𝒪 : DecisionProblem W) (S : W → (W → ℝ)) : Prop :=
  (∀ w, S w ∈ 𝒪) ∧ ∀ w, ∀ o ∈ 𝒪, E (F.P w) o ≤ E (F.P w) (S w)

/-- **Reading (a), literal-universal**: every world-indexed optimal selection is valued.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.1.1 l. 81
(literal reading, ATTRIBUTION-UNVETTED: MM do not say which selection `S` is meant)
Kind: D
Fidelity: variant: no cell constraint (MM's text); the foundation's `ValueNoCell` on `Fin 2` -/
def ValuesAllSel (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ 𝒪 : DecisionProblem W, 𝒪.Nonempty → ∀ S, IsSelection F 𝒪 S → ∀ o ∈ 𝒪, E π o ≤ stratValue π S

/-- **Reading (b), literal-existential**: some world-indexed optimal selection is valued.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.1.1 l. 81
(reading, ATTRIBUTION-UNVETTED)
Kind: D
Fidelity: variant: no cell constraint, existential over selections -/
def ValuesSomeSel (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ 𝒪 : DecisionProblem W, 𝒪.Nonempty →
    ∃ S, IsSelection F 𝒪 S ∧ ∀ o ∈ 𝒪, E π o ≤ stratValue π S

/-- A recommended strategy (cell-constrained) is a selection.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Recommended.isSelection {F : Frame W} {𝒪 : DecisionProblem W} {S : W → (W → ℝ)}
    (h : F.Recommended 𝒪 S) : IsSelection F 𝒪 S :=
  ⟨h.1.1, h.2⟩

/-- **Reading (a) refuted on the smallest frame (degenerate).** On the foundation's immodest
frame `flat` (both rows `(½, ½)`) with `π = (½, ½)`, `π` totally trusts the frame, yet the
world-wise optimal selection `S_a = (−1, 1)`, `S_b = (1, −1)` on the menu `{(1, −1), (−1, 1)}`
has `E_π(S) = −1 < 0`. Graded **N−** with the foundation (`flat_value_not_valueNoCell`, "an
encoding artifact"): both rows equal `π`, so Total Trust holds because the expert *is* the
deferrer, and the failure is pure exploitation of a tie between options every candidate values
at `0`; the smallest frame with a multi-world cell. The non-degenerate witness is
`dup_totalTrust_not_valuesAllSel`. What is refuted is MM's literal-universal reading of `S`
(l. 79–81, no cell constraint), not DDB's Theorem 2.2.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.2 l. 87
("The principal values the agent if and only if she totally trusts the agent"), read with l. 79–81's
world-indexed `S`; foundation Target 23 (`flat_value_not_valueNoCell`); audit r1 B2(a)
Kind: N-
Fidelity: variant: refutes the no-cell-constraint reading, not DDB's Theorem 2.2
Hyps: (a) none -/
theorem flat_totalTrust_not_valuesAllSel : TotalTrust half flat ∧ ¬ ValuesAllSel half flat := by
  obtain ⟨hval, hnc⟩ := flat_value_not_valueNoCell
  refine ⟨(value_iff_totalTrust half_mem flat).1 hval, fun h => hnc ?_⟩
  intro 𝒪 hne S h1 h2
  exact h 𝒪 hne S ⟨h1, h2⟩

/-- When the expert's rows are pairwise distinct, world-indexed selections are exactly the
cell-constrained strategies, so reading (a) is the foundation's `Value`: a refutation of (a)
needs a duplicated row and an agent tie broken world-by-world inside the cell. (Adopted from the
round-1 adversarial audit's probe `Readings.lean`.)
Source: none: infrastructure; audit r1 (adversarial) B2, N4
Kind: L
Fidelity: n/a -/
theorem valuesAllSel_iff_value_of_rows_distinct {π : W → ℝ} {F : Frame W}
    (hinj : ∀ w v, F.P w = F.P v → w = v) : ValuesAllSel π F ↔ Value π F := by
  constructor
  · intro h 𝒪 hne S hS o ho
    exact h 𝒪 hne S ⟨hS.1.1, hS.2⟩ o ho
  · intro h 𝒪 hne S hS o ho
    exact h 𝒪 hne S ⟨⟨hS.1, fun w v e => by rw [hinj w v e]⟩, hS.2⟩ o ho

/-! ### The non-degenerate witness for reading (a) (audit r1 repair, B2(a)) -/

/-- The uniform distribution on three worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def unif3 : Fin 3 → ℝ := ![1 / 3, 1 / 3, 1 / 3]

/-- `unif3` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem unif3_mem : unif3 ∈ stdSimplex ℝ (Fin 3) :=
  simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The frame `dup`: rows `P₀ = P₁ = (½, ½, 0)`, `P₂ = (0, 0, 1)` — one two-world cell `{0, 1}`
and one informed world (at world `2` the expert knows the world). No row equals `unif3`.
(Adopted from the round-1 fidelity audit's probe `Fidelity.lean`.)
Source: audit r1 (fidelity) B2; mandate Target 14 (reading (a))
Kind: D
Fidelity: n/a -/
def dup : Frame (Fin 3) :=
  mk3 ![1 / 2, 1 / 2, 0] ![1 / 2, 1 / 2, 0] ![0, 0, 1]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- `dup`'s rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem dup_P : dup.P 0 = ![1 / 2, 1 / 2, 0] ∧ dup.P 1 = ![1 / 2, 1 / 2, 0] ∧
    dup.P 2 = ![0, 0, 1] := ⟨rfl, rfl, rfl⟩

/-- No row of `dup` is the deferrer `unif3`, and the expert is informative (`P₂ = δ₂`).
Source: none: infrastructure (the non-degeneracy of the witness)
Kind: L
Fidelity: n/a -/
theorem dup_rows_ne_unif3 (w : Fin 3) : dup.P w ≠ unif3 := by
  obtain ⟨h0, h1, h2⟩ := dup_P
  intro h
  have := congrFun h 2
  fin_cases w <;> simp [h0, h1, h2, unif3, vec3_two] at this <;> norm_num at this

/-- **`unif3` totally trusts `dup`** (direct check of the product form, all four sign cases).
Source: audit r1 (fidelity) B2
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem dup_totalTrust : TotalTrust unif3 dup := by
  intro X s
  obtain ⟨h0, h1, h2⟩ := dup_P
  simp only [Fin.sum_univ_three, h0, h1, h2, E, unif3, vec3_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  split_ifs <;> nlinarith

/-- The tie menu's first option `(1, −1, 0)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def dupOa : Fin 3 → ℝ := ![1, -1, 0]

/-- The tie menu's second option `(−1, 1, 0)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def dupOb : Fin 3 → ℝ := ![-1, 1, 0]

/-- Every row of `dup` values `dupOa` at `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem dup_E_Oa (w : Fin 3) : E (dup.P w) dupOa = 0 := by
  obtain ⟨h0, h1, h2⟩ := dup_P
  fin_cases w <;> simp [E, Fin.sum_univ_three, h0, h1, h2, dupOa, vec3_two]

/-- Every row of `dup` values `dupOb` at `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem dup_E_Ob (w : Fin 3) : E (dup.P w) dupOb = 0 := by
  obtain ⟨h0, h1, h2⟩ := dup_P
  fin_cases w <;> simp [E, Fin.sum_univ_three, h0, h1, h2, dupOb, vec3_two]

/-- **Reading (a) fails on `dup`**: the world-indexed optimal selection `S₀ = dupOb`,
`S₁ = S₂ = dupOa` on the tie menu is worth `−2/3 < 0 = E_π(dupOa)`.
Source: audit r1 (fidelity) B2
Kind: P
Fidelity: exact (for the literal-universal reading)
Hyps: (a) none -/
theorem dup_not_valuesAllSel : ¬ ValuesAllSel unif3 dup := by
  intro h
  have hsel : IsSelection dup {dupOa, dupOb} ![dupOb, dupOa, dupOa] := by
    refine ⟨fun w => ?_, fun w o ho => ?_⟩
    · fin_cases w <;> simp
    · simp only [mem_insert, mem_singleton] at ho
      rcases ho with rfl | rfl <;> fin_cases w <;> simp [dup_E_Oa, dup_E_Ob]
  have := h {dupOa, dupOb} (insert_nonempty _ _) _ hsel dupOa (mem_insert_self _ _)
  simp [E, stratValue, Fin.sum_univ_three, unif3, dupOa, dupOb, vec3_two] at this
  norm_num at this

/-- **Reading (a) is refuted, non-degenerately.** On `dup` (rows `(½, ½, 0)`, `(½, ½, 0)`,
`(0, 0, 1)`; the expert knows the world at world `2`; no row is `π`) with `π = (⅓, ⅓, ⅓)`: `π`
totally trusts the frame (indeed `π(· | P = (½, ½, 0)) = (½, ½, 0)`, so New Reflection holds on
the two-world cell), yet the world-indexed optimal selection that at each world of the cell picks
the tied option worth `−1` there is valued at `−2/3 < 0`. So "totally trusts ⟹ values" fails
under the literal-universal reading of MM's `S` (l. 79–81, no cell constraint); the readings that
survive are (b) (`valuesSomeSel_iff_totalTrust`) and (c) (DDB's cell constraint,
`mm_theorem32_cell`). Not DDB's Theorem 2.2.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.2 l. 87
("The principal values the agent if and only if she totally trusts the agent"), read with l. 79–81's
world-indexed `S` (ATTRIBUTION-UNVETTED); audit r1 B2(a); item 082
Kind: N+
Fidelity: variant: refutes the no-cell-constraint reading, not DDB's Theorem 2.2
Hyps: (a) none -/
theorem dup_totalTrust_not_valuesAllSel : TotalTrust unif3 dup ∧ ¬ ValuesAllSel unif3 dup :=
  ⟨dup_totalTrust, dup_not_valuesAllSel⟩

/-- **Reading (b), (⟸).** Total Trust gives a valued world-indexed selection on every menu (the
foundation's cell-wise recommended strategy).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.2 l. 87
Kind: C
Fidelity: exact (for the existential reading)
Hyps: (a) `hπ` only -/
theorem TotalTrust.valuesSomeSel {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : TotalTrust π F) : ValuesSomeSel π F := by
  intro 𝒪 hne
  obtain ⟨S, hS, hval⟩ := ((value_iff_weakValue hπ F).1 ((value_iff_totalTrust hπ F).2 h)) 𝒪 hne
  exact ⟨S, Recommended.isSelection hS, hval⟩

/-- **Reading (b), (⟹).** If some world-indexed optimal selection is valued on every menu, then
`π` totally trusts the frame. On the tie-free menu `{X, const s'}` (no attained estimate equals
`s'`) the selection is forced — `X` where `E_w(X) > s'`, `const s'` elsewhere — so valuing gives
`s' π(E(X) > s') ≤ ∑_{E(X) > s'} π X`; choosing `s'` strictly between the largest attained
estimate below `s` (and `∑_U π X / π(U)`) and `s` makes `[E(X) > s'] = [E(X) ≥ s]` and
contradicts a failure at `s` directly, with no limit.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.2 l. 87;
mandate Target 14(b) ("my derivation", verified here)
Kind: P
Fidelity: exact (for the existential reading)
Hyps: (a) `hπ` only -/
theorem ValuesSomeSel.totalTrust {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : ValuesSomeSel π F) : TotalTrust π F := by
  intro X s
  rw [totalTrust_sum_eq]
  by_contra hcon
  rw [not_le] at hcon
  set U := F.estEvent X s with hU
  set m := mass π U with hm_def
  set Cs := ∑ w ∈ U, π w * X w with hCs_def
  have hsum : ∑ w ∈ U, π w * (X w - s) = Cs - s * m := by
    simp only [hCs_def, hm_def, mass, mul_sub, sum_sub_distrib, mul_sum]
    congr 1
    apply sum_congr rfl; intro w _; ring
  have hCs : Cs < s * m := by linarith
  have hm : 0 < m := by
    rcases (mass_nonneg hπ.1 U).lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have : ∑ w ∈ U, π w * (X w - s) = 0 :=
        sum_eq_zero fun w hw => by rw [eq_zero_of_mass_eq_zero hπ.1 h'.symm hw, zero_mul]
      linarith
  -- the tie-free threshold `s'`
  set T : Finset ℝ := insert (Cs / m) ((univ \ U).image (fun w => E (F.P w) X)) with hT
  have hTne : T.Nonempty := insert_nonempty _ _
  have hTlt : T.max' hTne < s := by
    rw [max'_lt_iff]
    intro x hx
    simp only [hT, mem_insert, mem_image, mem_sdiff, mem_univ, true_and] at hx
    rcases hx with rfl | ⟨w, hw, rfl⟩
    · rw [div_lt_iff₀ hm]; exact hCs
    · have : ¬ s ≤ E (F.P w) X := by simpa [hU, Frame.mem_estEvent] using hw
      exact not_le.1 this
  set s' := (T.max' hTne + s) / 2 with hs'
  have hs's : s' < s := by rw [hs']; linarith
  have hCs' : Cs < s' * m := by
    have : Cs / m ≤ T.max' hTne := le_max' T _ (by simp [hT])
    have : Cs / m < s' := by rw [hs']; linarith
    rwa [div_lt_iff₀ hm] at this
  have hs'w : ∀ w, w ∉ U → E (F.P w) X < s' := by
    intro w hw
    have : E (F.P w) X ≤ T.max' hTne := by
      apply le_max' T _
      simp only [hT, mem_insert, mem_image, mem_sdiff, mem_univ, true_and]
      exact Or.inr ⟨w, hw, rfl⟩
    rw [hs']; linarith
  -- the forced selection on `{X, const s'}`
  obtain ⟨S, ⟨hSmem, hSopt⟩, hSval⟩ := h {X, fun _ => s'} (insert_nonempty _ _)
  have hval := hSval (fun _ => s') (mem_insert_of_mem (mem_singleton_self _))
  rw [E_const hπ] at hval
  have hSU : ∀ w ∈ U, S w = X := by
    intro w hw
    rcases mem_insert.1 (hSmem w) with h1 | h1
    · exact h1
    · exfalso
      rw [mem_singleton] at h1
      have := hSopt w X (mem_insert_self _ _)
      rw [h1, E_const (F.P_mem w)] at this
      have := Frame.mem_estEvent.1 hw
      linarith
  have hSUc : ∀ w, w ∉ U → S w = fun _ => s' := by
    intro w hw
    rcases mem_insert.1 (hSmem w) with h1 | h1
    · exfalso
      have := hSopt w (fun _ => s') (mem_insert_of_mem (mem_singleton_self _))
      rw [h1, E_const (F.P_mem w)] at this
      linarith [hs'w w hw]
    · exact mem_singleton.1 h1
  have hsv : stratValue π S = Cs + s' * (1 - m) := by
    unfold stratValue
    rw [← sum_filter_add_sum_filter_not univ (fun w => w ∈ U)]
    have e1 : univ.filter (fun w => w ∈ U) = U := by ext; simp
    have e2 : univ.filter (fun w => ¬ w ∈ U) = univ \ U := by ext; simp
    rw [e1, e2]
    have h1 : ∑ w ∈ U, π w * S w w = Cs :=
      sum_congr rfl fun w hw => by rw [hSU w hw]
    have h2 : ∑ w ∈ univ \ U, π w * S w w = s' * (1 - m) := by
      rw [show ∑ w ∈ univ \ U, π w * S w w = ∑ w ∈ univ \ U, π w * s' from
        sum_congr rfl fun w hw => by rw [hSUc w (mem_sdiff.1 hw).2]]
      rw [← sum_mul, sum_sdiff_eq_sub (subset_univ U), hπ.2]
      simp only [hm_def, mass]
      ring
    rw [h1, h2]
  rw [hsv] at hval
  nlinarith

/-- **Reading (b), the iff.** "Some world-indexed optimal selection is valued on every menu"
is exactly Total Trust.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.2 l. 87
Kind: C
Fidelity: exact (for the existential reading; the universal reading is refuted, the
cell-constrained reading is the foundation's `value_iff_totalTrust`)
Hyps: (a) `hπ` only -/
theorem valuesSomeSel_iff_totalTrust {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    ValuesSomeSel π F ↔ TotalTrust π F :=
  ⟨ValuesSomeSel.totalTrust hπ, TotalTrust.valuesSomeSel hπ⟩

/-- **Reading (c), the pointer row.** With DDB's cell constraint (`Frame.IsStrategy`), MM's
Theorem 3.2 is the foundation's Theorem 2.2, `value_iff_totalTrust`, at grade (a).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.2 l. 87;
[[Deference Done Better]] Thm 2.2
Kind: C
Fidelity: exact
Hyps: (a) `hπ` only -/
theorem mm_theorem32_cell {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    Value π F ↔ TotalTrust π F :=
  value_iff_totalTrust hπ F

end

end Cleanroom.Lit.LitDdbAccuracyMm.MM
