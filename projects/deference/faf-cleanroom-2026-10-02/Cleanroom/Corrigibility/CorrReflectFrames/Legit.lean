import Cleanroom.Corrigibility.CorrReflectFrames.Collapse

/-!
# corr-reflect-frames — T6 and T11: legitimizing events

Radical Def I5.1 / Lemma I5.2 (`LegitimizingVal`, the linear characterization *as* the
definition; the ratio form is the iff), Theorem I5.3's closure structure (disjoint unions, proper
differences; non-closure under union/intersection is `Witnesses`' Model A), Theorem I5.4's
defect decomposition, Theorem I5.5's per-cell mass bounds and their summed finite form; ddb's
partition lemma (L-C) and the coincidence of the two "legitimizing event" senses under
introspection (T11(c)).

Findings recorded here: `L = ∅` is vacuously legitimizing (`legitimizingVal_empty`); I5.3(e) as
printed ("unconditional reflection ⟺ both `L` and `Lᶜ` legitimizing, for any `L`") is false in
the ⟹ direction for arbitrary `L` (I5.6(a)'s own `L = φ`), the surviving statement is
`legitimizingVal_compl_iff`; the finite I5.5 is a bound, not an equality.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W] {π : W → ℝ} {F : Frame W}

/-! ## Mass arithmetic -/

/-- Mass of a proper difference.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_sdiff_of_subset (π : W → ℝ) {A B : Finset W} (h : B ⊆ A) :
    mass π (A \ B) = mass π A - mass π B := by
  have := mass_inter_add_mass_sdiff π A B
  rw [inter_eq_right.2 h] at this
  linarith

/-- Mass of a disjoint union.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_union_of_disjoint (π : W → ℝ) {A B : Finset W} (h : Disjoint A B) :
    mass π (A ∪ B) = mass π A + mass π B :=
  sum_union h

/-- Splitting a mass along an event and its complement.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_split (π : W → ℝ) (A L : Finset W) :
    mass π A = mass π (L ∩ A) + mass π ((univ \ L) ∩ A) := by
  have := mass_inter_add_mass_sdiff π A L
  have e : A \ L = (univ \ L) ∩ A := by ext w; simp [and_comm]
  rw [e, inter_comm A L] at this
  linarith

/-! ## Value-form reflection on one event; the ratio forms -/

/-- **Value-form reflection for one event** `φ`: `ValueReflects` restricted to `φ`.
Source: [[radical]] Theorem I5.3(d) ("unconditional (R-val) holds for `φ`")
Kind: D
Fidelity: exact -/
def ValueReflectsOn (π : W → ℝ) (F : Frame W) (φ : Finset W) : Prop :=
  ∀ c : ℝ, mass π (φ ∩ valCell F φ c) = c * mass π (valCell F φ c)

/-- Value-form reflection is value-form reflection on every event.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem valueReflects_iff_forall_on :
    ValueReflects π F ↔ ∀ φ, ValueReflectsOn π F φ := Iff.rfl

/-- **Def I5.1, ratio form.** `L` is legitimizing for `φ` iff for every `c` with
`π(L ∩ C_c) > 0`, `π(φ ∩ L ∩ C_c) / π(L ∩ C_c) = c`.
Source: [[radical]] Def I5.1 l. 147 (ratio form), Lemma I5.2 l. 149 (the iff)
Kind: L
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem legitimizingVal_iff_ratio (hπ : ∀ w, 0 ≤ π w) (φ L : Finset W) :
    LegitimizingVal π F φ L ↔ ∀ c, 0 < mass π (L ∩ valCell F φ c) →
      mass π (φ ∩ L ∩ valCell F φ c) / mass π (L ∩ valCell F φ c) = c := by
  constructor
  · intro h c hc
    rw [h c, mul_div_assoc, div_self hc.ne', mul_one]
  · intro h c
    by_cases hc : 0 < mass π (L ∩ valCell F φ c)
    · have := h c hc
      rw [div_eq_iff hc.ne'] at this
      exact this
    · have h0 : mass π (L ∩ valCell F φ c) = 0 :=
        le_antisymm (not_lt.1 hc) (mass_nonneg hπ _)
      rw [h0, mul_zero]
      apply le_antisymm _ (mass_nonneg hπ _)
      calc mass π (φ ∩ L ∩ valCell F φ c) ≤ mass π (L ∩ valCell F φ c) :=
            mass_mono hπ (inter_subset_inter inter_subset_right (Subset.refl _))
        _ = 0 := h0

/-- **(R-val), ratio form** on one event: for every `c` with `π(C_c) > 0`,
`π(φ ∩ C_c) / π(C_c) = c`.
Source: [[radical]] S3 (R-val) l. 24
Kind: L
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem valueReflectsOn_iff_ratio (hπ : ∀ w, 0 ≤ π w) (φ : Finset W) :
    ValueReflectsOn π F φ ↔ ∀ c, 0 < mass π (valCell F φ c) →
      mass π (φ ∩ valCell F φ c) / mass π (valCell F φ c) = c := by
  have := legitimizingVal_iff_ratio (F := F) hπ φ univ
  simp only [LegitimizingVal, inter_univ, univ_inter] at this
  exact this

/-! ## T6(b): the whole space, the empty event -/

/-- **I5.3(d).** `Ω` is legitimizing for `φ` iff unconditional value-form reflection holds for `φ`.
Source: [[radical]] Theorem I5.3(d) l. 155
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem legitimizingVal_univ_iff (φ : Finset W) :
    LegitimizingVal π F φ univ ↔ ValueReflectsOn π F φ := by
  simp only [LegitimizingVal, ValueReflectsOn, inter_univ, univ_inter]

/-- **Finding (T6 (i)).** The empty event is vacuously legitimizing: the definition quantifies
over positive-mass cells, and `∅` meets none. "Minimal viability" has a trivial member.
Source: [[radical]] Def I5.1 l. 147 (the quantifier), Theorem I5.5(c) l. 163 ("almost no
content")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem legitimizingVal_empty (φ : Finset W) : LegitimizingVal π F φ ∅ := by
  intro c; simp [mass]

/-! ## T6(a): closure under disjoint unions and proper differences -/

/-- **I5.3(a).** Legitimizing events are closed under disjoint unions (both sides of the linear
characterization are additive).
Source: [[radical]] Theorem I5.3(a) l. 152
Kind: P
Fidelity: exact (finite; countable unions are finite here)
Hyps: (a) none -/
theorem legitimizingVal_union_of_disjoint {φ L₁ L₂ : Finset W} (h₁ : LegitimizingVal π F φ L₁)
    (h₂ : LegitimizingVal π F φ L₂) (hd : Disjoint L₁ L₂) :
    LegitimizingVal π F φ (L₁ ∪ L₂) := by
  intro c
  have e1 : φ ∩ (L₁ ∪ L₂) ∩ valCell F φ c =
      (φ ∩ L₁ ∩ valCell F φ c) ∪ (φ ∩ L₂ ∩ valCell F φ c) := by
    ext w; simp only [mem_inter, mem_union]; tauto
  have e2 : (L₁ ∪ L₂) ∩ valCell F φ c = (L₁ ∩ valCell F φ c) ∪ (L₂ ∩ valCell F φ c) := by
    ext w; simp only [mem_inter, mem_union]; tauto
  have d1 : Disjoint (φ ∩ L₁ ∩ valCell F φ c) (φ ∩ L₂ ∩ valCell F φ c) :=
    hd.mono (inter_subset_left.trans inter_subset_right)
      (inter_subset_left.trans inter_subset_right)
  have d2 : Disjoint (L₁ ∩ valCell F φ c) (L₂ ∩ valCell F φ c) :=
    hd.mono inter_subset_left inter_subset_left
  rw [e1, e2, mass_union_of_disjoint π d1, mass_union_of_disjoint π d2, h₁ c, h₂ c]
  ring

/-- **I5.3(b).** Legitimizing events are closed under proper differences.
Source: [[radical]] Theorem I5.3(b) l. 153
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem legitimizingVal_sdiff {φ L₁ L₂ : Finset W} (h₁ : LegitimizingVal π F φ L₁)
    (h₂ : LegitimizingVal π F φ L₂) (hsub : L₂ ⊆ L₁) :
    LegitimizingVal π F φ (L₁ \ L₂) := by
  intro c
  have e1 : φ ∩ (L₁ \ L₂) ∩ valCell F φ c =
      (φ ∩ L₁ ∩ valCell F φ c) \ (φ ∩ L₂ ∩ valCell F φ c) := by
    ext w; simp only [mem_inter, mem_sdiff]; tauto
  have e2 : (L₁ \ L₂) ∩ valCell F φ c = (L₁ ∩ valCell F φ c) \ (L₂ ∩ valCell F φ c) := by
    ext w; simp only [mem_inter, mem_sdiff]; tauto
  have s1 : φ ∩ L₂ ∩ valCell F φ c ⊆ φ ∩ L₁ ∩ valCell F φ c :=
    inter_subset_inter (inter_subset_inter (Subset.refl _) hsub) (Subset.refl _)
  have s2 : L₂ ∩ valCell F φ c ⊆ L₁ ∩ valCell F φ c := inter_subset_inter hsub (Subset.refl _)
  rw [e1, e2, mass_sdiff_of_subset π s1, mass_sdiff_of_subset π s2, h₁ c, h₂ c]
  ring

/-- **I5.3(e), corrected.** For a legitimizing `L`, its complement is legitimizing iff `Ω` is
(iff unconditional value-form reflection holds for `φ`). The printed "unconditional reflection
⟺ both `L` and `Lᶜ` legitimizing, for any `L`" fails in the ⟹ direction for arbitrary `L`
(I5.6(a): `L = φ`); this is the surviving statement (findings).
Source: [[radical]] Theorem I5.3(e) l. 156, I5.6(a)(b) ll. 172–173
Kind: C
Fidelity: variant: conditional on `L` legitimizing (the printed biconditional is false for
arbitrary `L`); two lines from `legitimizingVal_union_of_disjoint` and `legitimizingVal_sdiff`
Hyps: (a) none -/
theorem legitimizingVal_compl_iff {φ L : Finset W} (h : LegitimizingVal π F φ L) :
    LegitimizingVal π F φ (univ \ L) ↔ LegitimizingVal π F φ univ := by
  constructor
  · intro hc
    have := legitimizingVal_union_of_disjoint h hc disjoint_sdiff
    rwa [union_sdiff_of_subset (subset_univ L)] at this
  · intro hu
    exact legitimizingVal_sdiff hu h (subset_univ L)

/-! ## T6(d): the defect decomposition -/

/-- **I5.4 (defect decomposition), product form.** For a legitimizing `L` and any cell `C_c`, the
unconditional reflection defect `π(φ ∩ C_c) − c · π(C_c)` equals the defect on the illegitimate
part, `π(φ ∩ Lᶜ ∩ C_c) − c · π(Lᶜ ∩ C_c)`.
Source: [[radical]] Theorem I5.4 l. 159
Kind: P
Fidelity: exact (product form; the ratio form with two positivity guards is
`defect_decomposition_ratio`)
Hyps: (a) none -/
theorem defect_decomposition {φ L : Finset W} (h : LegitimizingVal π F φ L) (c : ℝ) :
    mass π (φ ∩ valCell F φ c) - c * mass π (valCell F φ c) =
      mass π (φ ∩ (univ \ L) ∩ valCell F φ c) - c * mass π ((univ \ L) ∩ valCell F φ c) := by
  have e1 := mass_split π (φ ∩ valCell F φ c) L
  have e2 := mass_split π (valCell F φ c) L
  have r1 : L ∩ (φ ∩ valCell F φ c) = φ ∩ L ∩ valCell F φ c := by
    ext w; simp only [mem_inter]; tauto
  have r2 : (univ \ L) ∩ (φ ∩ valCell F φ c) = φ ∩ (univ \ L) ∩ valCell F φ c := by
    ext w; simp only [mem_inter]; tauto
  rw [r1, r2] at e1
  rw [e1, e2, h c]
  ring

/-- **I5.4 (defect decomposition), ratio form**: with `π(C_c) > 0` and `π(Lᶜ ∩ C_c) > 0`,
`π(φ | C_c) − c = π(Lᶜ | C_c) · (π(φ | Lᶜ ∩ C_c) − c)`.
Source: [[radical]] Theorem I5.4 l. 159 (as displayed)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem defect_decomposition_ratio {φ L : Finset W} (h : LegitimizingVal π F φ L) (c : ℝ)
    (hC : 0 < mass π (valCell F φ c)) (hL : 0 < mass π ((univ \ L) ∩ valCell F φ c)) :
    mass π (φ ∩ valCell F φ c) / mass π (valCell F φ c) - c =
      (mass π ((univ \ L) ∩ valCell F φ c) / mass π (valCell F φ c)) *
        (mass π (φ ∩ (univ \ L) ∩ valCell F φ c) / mass π ((univ \ L) ∩ valCell F φ c) - c) := by
  have hd := defect_decomposition h c
  have hCne := hC.ne'
  have hLne := hL.ne'
  field_simp
  linarith

/-! ## T6(e): the per-cell mass bounds and the summed finite form -/

/-- **I5.5, hits bound (product form).** For a legitimizing `L` and every cell,
`c · π(L ∩ C_c) ≤ h_c := π(φ ∩ C_c)`.
Source: [[radical]] Theorem I5.5(a) l. 161 (`a ≤ h_c`)
Kind: L
Fidelity: exact (product form, no division; one-step monotonicity from the definition)
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem legit_hits_bound (hπ : ∀ w, 0 ≤ π w) {φ L : Finset W} (h : LegitimizingVal π F φ L)
    (c : ℝ) : c * mass π (L ∩ valCell F φ c) ≤ mass π (φ ∩ valCell F φ c) := by
  rw [← h c]
  exact mass_mono hπ (inter_subset_inter inter_subset_left (Subset.refl _))

/-- **I5.5, misses bound (product form).** For a legitimizing `L` and every cell,
`(1 − c) · π(L ∩ C_c) ≤ m_c := π(C_c ∖ φ)`.
Source: [[radical]] Theorem I5.5(a) l. 161 (`b ≤ m_c`)
Kind: L
Fidelity: exact (product form, no division; one-step monotonicity from the definition)
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem legit_misses_bound (hπ : ∀ w, 0 ≤ π w) {φ L : Finset W} (h : LegitimizingVal π F φ L)
    (c : ℝ) : (1 - c) * mass π (L ∩ valCell F φ c) ≤ mass π (valCell F φ c \ φ) := by
  have e := mass_inter_add_mass_sdiff π (L ∩ valCell F φ c) φ
  have r : L ∩ valCell F φ c ∩ φ = φ ∩ L ∩ valCell F φ c := by
    ext w; simp only [mem_inter]; tauto
  rw [r, h c] at e
  have hsub : (L ∩ valCell F φ c) \ φ ⊆ valCell F φ c \ φ :=
    sdiff_subset_sdiff inter_subset_right (le_refl φ)
  have := mass_mono hπ hsub
  linarith

/-- The finite per-cell bound of I5.5: `m_c` at `c ≤ 0`, `h_c` at `c ≥ 1`, and
`min(h_c / c, m_c / (1 − c))` strictly between (the atomless maximal mass, an upper bound in
general).
Source: [[radical]] Theorem I5.5(a) l. 161
Kind: D
Fidelity: exact (finite bound; the endpoint cases made explicit) -/
def cellBound (π : W → ℝ) (F : Frame W) (φ : Finset W) (c : ℝ) : ℝ :=
  if c ≤ 0 then mass π (valCell F φ c \ φ)
  else if 1 ≤ c then mass π (φ ∩ valCell F φ c)
  else min (mass π (φ ∩ valCell F φ c) / c) (mass π (valCell F φ c \ φ) / (1 - c))

/-- **I5.5, per-cell form.** For a legitimizing `L`, `π(L ∩ C_c) ≤ cellBound c` in every cell.
Source: [[radical]] Theorem I5.5(a) l. 161
Kind: P
Fidelity: exact (finite bound; equality needs atomless cells — findings)
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem legit_cell_le_cellBound (hπ : ∀ w, 0 ≤ π w) {φ L : Finset W}
    (h : LegitimizingVal π F φ L) (c : ℝ) :
    mass π (L ∩ valCell F φ c) ≤ cellBound π F φ c := by
  have hh := legit_hits_bound hπ h c
  have hm := legit_misses_bound hπ h c
  have hn := mass_nonneg hπ (L ∩ valCell F φ c)
  unfold cellBound
  split_ifs with h0 h1
  · nlinarith [mul_nonneg (neg_nonneg.2 h0) hn]
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) hn]
  · push Not at h0 h1
    refine le_min ?_ ?_
    · rw [le_div_iff₀ h0]; linarith
    · rw [le_div_iff₀ (by linarith)]; linarith

/-- The mass of an event is the sum of its masses over the announced-value cells.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_eq_sum_valCells (π : W → ℝ) (F : Frame W) (φ L : Finset W) :
    mass π L = ∑ c ∈ univ.image (fun w => mass (F.P w) φ), mass π (L ∩ valCell F φ c) := by
  have hmaps : ∀ w ∈ L, mass (F.P w) φ ∈ univ.image (fun w => mass (F.P w) φ) :=
    fun w _ => mem_image_of_mem _ (mem_univ w)
  have e1 : mass π L = ∑ w ∈ L, π w := rfl
  have e2 : ∀ c, mass π (L ∩ valCell F φ c) = ∑ w ∈ L ∩ valCell F φ c, π w := fun c => rfl
  rw [e1, ← sum_fiberwise_of_maps_to hmaps π]
  apply sum_congr rfl
  intro c _
  rw [e2]
  apply sum_congr _ (fun _ _ => rfl)
  ext w; simp [mem_valCell]

/-- **I5.5, summed finite form.** For a legitimizing `L`,
`π(L) ≤ ∑_c cellBound c` over the announced values — the atomless maximal-mass formula is an
upper bound on finite frames (attained in `Witnesses`' Model B, not in Model A).
Source: [[radical]] Theorem I5.5(a) l. 161 ("the right-hand side is an upper bound in general")
Kind: C
Fidelity: weaker: bound, not equality (equality needs atomless cells)
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem legit_mass_le_sum_cellBound (hπ : ∀ w, 0 ≤ π w) {φ L : Finset W}
    (h : LegitimizingVal π F φ L) :
    mass π L ≤ ∑ c ∈ univ.image (fun w => mass (F.P w) φ), cellBound π F φ c := by
  rw [mass_eq_sum_valCells π F φ L]
  exact sum_le_sum (fun c _ => legit_cell_le_cellBound hπ h c)

/-! ## T11: the partition lemma; the two senses of "legitimizing" -/

/-- Total Trust is additive in the deferrer.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem totalTrust_add {π₁ π₂ : W → ℝ} (h₁ : TotalTrust π₁ F) (h₂ : TotalTrust π₂ F) :
    TotalTrust (π₁ + π₂) F := by
  intro X s
  have h := add_nonneg (h₁ X s) (h₂ X s)
  have e : ∑ w, (π₁ + π₂) w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) =
      ∑ w, π₁ w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) +
        ∑ w, π₂ w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) := by
    rw [← sum_add_distrib]; apply sum_congr rfl; intro w _; simp only [Pi.add_apply]; ring
  rw [e]; exact h

/-- The restricted deferrer splits along an event and its complement.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_add_restrict_compl (π : W → ℝ) (L : Finset W) :
    restrict π L + restrict π (univ \ L) = π := by
  funext w
  simp only [Pi.add_apply, restrict_apply, mem_sdiff, mem_univ, true_and]
  split_ifs <;> simp_all

/-- Restriction to a disjoint union is the sum of the restrictions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_union_of_disjoint (π : W → ℝ) {E E' : Finset W} (h : Disjoint E E') :
    restrict π (E ∪ E') = restrict π E + restrict π E' := by
  funext w
  simp only [Pi.add_apply, restrict_apply, mem_union]
  by_cases h1 : w ∈ E
  · have h2 : w ∉ E' := disjoint_left.1 h h1
    simp [h1, h2]
  · simp [h1]

/-- **ddb's partition lemma (L-C), two-event form.** Total Trust conditional on `L` and
conditional on `Lᶜ` gives Total Trust unconditionally (sum the product forms).
Source: [[ddb]] L-C l. 49
Kind: P
Fidelity: exact (two-event partition; `totalTrust_of_partition` is the `J`-indexed form)
Hyps: (a) none -/
theorem totalTrust_of_restrict_compl {L : Finset W} (h₁ : TotalTrust (restrict π L) F)
    (h₂ : TotalTrust (restrict π (univ \ L)) F) : TotalTrust π F := by
  have := totalTrust_add h₁ h₂
  rwa [restrict_add_restrict_compl] at this

/-- **ddb's partition lemma (L-C).** If `L : J → Finset W` partitions `W` (every world lies in
exactly one part, `∑ j, 𝟙_{L j} w = 1`) and Total Trust holds conditional on every part, it
holds unconditionally.
Source: [[ddb]] L-C l. 49
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem totalTrust_of_partition {J : Type} [Fintype J] (L : J → Finset W)
    (hpart : ∀ w, ∑ j, ind (L j) w = 1) (h : ∀ j, TotalTrust (restrict π (L j)) F) :
    TotalTrust π F := by
  intro X s
  have hsum : ∀ w, π w = ∑ j, restrict π (L j) w := by
    intro w
    simp only [restrict]
    rw [← mul_sum, hpart w, mul_one]
  calc (0 : ℝ) ≤ ∑ j, ∑ w, restrict π (L j) w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) :=
        sum_nonneg (fun j _ => h j X s)
    _ = ∑ w, π w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro w _
        rw [hsum w, sum_mul, sum_mul]

/-- Value-form reflection of the restricted deferrer is "`L` is legitimizing for every event".
Source: none: infrastructure (the bridge between the two senses)
Kind: L
Fidelity: n/a -/
theorem valueReflects_restrict_iff (L : Finset W) :
    ValueReflects (restrict π L) F ↔ ∀ φ, LegitimizingVal π F φ L := by
  have e1 : ∀ (φ : Finset W) (c : ℝ), φ ∩ valCell F φ c ∩ L = φ ∩ L ∩ valCell F φ c := by
    intro φ c; ext w; simp only [mem_inter]; tauto
  have e2 : ∀ (φ : Finset W) (c : ℝ), valCell F φ c ∩ L = L ∩ valCell F φ c :=
    fun φ c => inter_comm _ _
  unfold ValueReflects LegitimizingVal
  simp only [mass_restrict, e1, e2]

/-- **T11(c): the two senses of "legitimizing event" coincide under introspection.** For a
deferrer introspective at the candidates of `restrict π L`, ddb's strong sense (Total Trust
conditional on `L`) is radical's value-form class taken over every event `φ`. Without
introspection they differ: `fig3` with `L = Ω` (`Witnesses`).
Source: [[radical]] Def I5.1 l. 147 vs [[ddb]] L-C l. 49; mandate T11(c), Known issue 13
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`; INT at the candidates of `restrict π L` is the scope hypothesis
Scope: under introspection at the candidates of the restricted deferrer -/
theorem legitimizingTT_iff_forall_legitimizingVal (hπ : ∀ w, 0 ≤ π w) (L : Finset W)
    (hINT : CandsIntrospective (restrict π L) F) :
    LegitimizingTT π F L ↔ ∀ φ, LegitimizingVal π F φ L := by
  have hπ' := restrict_nonneg hπ L
  rw [← valueReflects_restrict_iff]
  unfold LegitimizingTT
  constructor
  · intro h
    exact ((reflects_iff_valueReflects_and_int hπ').1
      ((reflects_iff_totalTrust_and_int hπ').2 ⟨h, hINT⟩)).1
  · intro h
    exact ((reflects_iff_totalTrust_and_int hπ').1
      ((reflects_iff_valueReflects_and_int hπ').2 ⟨h, hINT⟩)).1

/-- **T11(d), positive half.** Disjoint TT-legitimizing events have a TT-legitimizing union.
Source: [[ddb]] L-C l. 49 (conjectured extension); mandate T11(d)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem legitimizingTT_union_of_disjoint {E E' : Finset W} (h₁ : LegitimizingTT π F E)
    (h₂ : LegitimizingTT π F E') (hd : Disjoint E E') : LegitimizingTT π F (E ∪ E') := by
  unfold LegitimizingTT at *
  rw [restrict_union_of_disjoint π hd]
  exact totalTrust_add h₁ h₂

end

end Cleanroom.Corrigibility.CorrReflectFrames
