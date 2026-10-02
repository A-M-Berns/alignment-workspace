import Cleanroom.Corrigibility.CorrReflectFrames.Basic

/-!
# corr-reflect-frames — T1: the collapse of the reflection forms under introspection

Radical Theorem I4.1 / Armstrong Theorem A on `lit-ddb-frames`' frames. The five implications
are proved separately so the report can say which need introspection:

* no INT: `Reflects → VarReflects` (i), `VarReflects → ValueReflects` (i), `VarReflects →
  EstimateMatching` (i), `VarReflects → TotalTrust` (iv);
* with INT: `ValueReflects → Reflects` (ii), `EstimateMatching → VarReflects` (iii),
  `TotalTrust → VarReflects` (v);
* Theorem A(c): `Reflects → CandsIntrospective` — reflection *forces* introspection at
  candidates, so the INT-free forms of the collapse read `Reflects ↔ Φ ∧ CandsIntrospective`.

Nothing here routes through `Value`; `Value` enters only through `lit-ddb-frames`'
`value_iff_totalTrust` in the final `collapse`. Scope: introspection at candidates is the
hypothesis of every (ii)/(iii)/(v) step; `fig3` (modest, valued, not reflected) separates the
forms without it (`Witnesses.lean`).
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W] {π : W → ℝ} {F : Frame W}

/-! ## (i) Function form ⟹ variable form ⟹ value form and estimate matching (no INT) -/

/-- **Theorem I4.1 (i), first arrow.** Reflection implies variable-form reflection: condition on
the state. No introspection needed.
Source: [[radical]] Theorem I4.1 (i) l. 129; [[armstrong]] Theorem A (b)
Kind: P
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only
Scope: no INT -/
theorem varReflects_of_reflects (hπ : ∀ w, 0 ≤ π w) (h : Reflects π F) : VarReflects π F := by
  intro X s
  have hA : ∀ w v, F.P w = F.P v → w ∈ estCell F X s → v ∈ estCell F X s := by
    intro w v hwv hw
    rw [mem_estCell] at hw ⊢
    rw [← hwv]; exact hw
  rw [sum_rowClosed F hA, mass, sum_rowClosed F hA, mul_sum]
  apply sum_congr rfl
  intro ρ hρ
  obtain ⟨w, hw, rfl⟩ := mem_image.1 hρ
  rw [reflects_cell_sum hπ h, mem_estCell.1 hw]
  unfold mass; ring

/-- **Theorem I4.1 (i), second arrow.** Variable-form reflection implies value-form reflection
(`X := 𝟙_φ`). No introspection needed.
Source: [[radical]] Theorem I4.1 (i) l. 129
Kind: P
Fidelity: exact
Hyps: (a) none
Scope: no INT -/
theorem valueReflects_of_varReflects (h : VarReflects π F) : ValueReflects π F := by
  intro φ c
  have := h (ind φ) c
  rw [estCell_ind] at this
  rw [← this]
  unfold mass
  simp only [ind, mul_ite, mul_one, mul_zero]
  rw [sum_ite_mem, inter_comm]

/-- **Theorem I4.1 (i), third arrow.** Variable-form reflection implies estimate matching: take
expectations over the estimate cells. No introspection needed.
Source: [[radical]] Theorem I4.1 (i) l. 129 ("take expectations")
Kind: P
Fidelity: exact
Hyps: (a) none
Scope: no INT -/
theorem estimateMatching_of_varReflects (h : VarReflects π F) : EstimateMatching π F := by
  intro X
  have hmaps : ∀ w ∈ (univ : Finset W), E (F.P w) X ∈ univ.image (fun w => E (F.P w) X) :=
    fun w _ => mem_image_of_mem _ (mem_univ w)
  show ∑ w, π w * E (F.P w) X = ∑ w, π w * X w
  rw [← sum_fiberwise_of_maps_to hmaps (fun w => π w * E (F.P w) X),
    ← sum_fiberwise_of_maps_to hmaps (fun w => π w * X w)]
  apply sum_congr rfl
  intro s _
  have hfil : univ.filter (fun w => E (F.P w) X = s) = estCell F X s := rfl
  rw [hfil, h X s, sum_congr rfl (fun w hw => by rw [mem_estCell.1 hw]), ← sum_mul]
  unfold mass; ring

/-! ## (ii) Value form ⟹ function form (INT) -/

/-- **Theorem I4.1 (ii).** Under introspection at candidates, value-form reflection for the
state-identifying events `{w}` implies Reflection: on the branch of a candidate `ρ`, the cell
`{P_{t₂}({w}) = ρ w}` is the branch itself (off the branch every candidate gives `w` probability
zero, by INT), so value-form calibration at `{w}` is `π(w ∩ [P = ρ]) = ρ w · π(P = ρ)`; the case
`ρ w = 0` forces `π w = 0` the same way.
Source: [[radical]] Theorem I4.1 (ii) l. 130; [[armstrong]] Theorem A (a)
Kind: P
Fidelity: exact (singleton events suffice; radical's `{w} ∪ [P ≠ ρ]` is not needed)
Hyps: (a) `∀ w, 0 ≤ π w`; INT at candidates is the theorem's scope hypothesis
Scope: under introspection at candidates; `fig3` separates without it -/
theorem reflects_of_valueReflects (hπ : ∀ w, 0 ≤ π w) (hINT : CandsIntrospective π F)
    (h : ValueReflects π F) : Reflects π F := by
  intro ρ hρ w
  by_cases hw : F.P w = ρ
  · have hind : ind (F.cell ρ) w = 1 := by simp [ind, hw]
    rw [hind, mul_one]
    by_cases h0 : ρ w = 0
    · have hv := h {w} 0
      have hwcell : w ∈ valCell F {w} 0 := by rw [mem_valCell, hw, mass_singleton, h0]
      rw [zero_mul, singleton_inter_of_mem hwcell, mass_singleton] at hv
      rw [hv, h0]; ring
    · have hv := h {w} (ρ w)
      have hwcell : w ∈ valCell F {w} (ρ w) := by rw [mem_valCell, hw, mass_singleton]
      rw [singleton_inter_of_mem hwcell, mass_singleton] at hv
      have hcong : mass π (valCell F {w} (ρ w)) = mass π (F.cell ρ) := by
        apply mass_congr_supp hπ
        intro v hv'
        rw [mem_valCell, Frame.mem_cell, mass_singleton]
        constructor
        · intro hvw
          by_contra hne
          have : F.P v w = 0 := hINT.zero_of_ne (F.P_mem_cands hv') (by rw [hw]; exact Ne.symm hne)
          exact h0 (by rw [← hvw, this])
        · intro hvρ; rw [hvρ]
      rw [hcong] at hv
      rw [hv]; ring
  · have hind : ind (F.cell ρ) w = 0 := by simp [ind, hw]
    rw [hind, mul_zero, hINT.zero_of_ne hρ hw, mul_zero]

/-! ## (iii) Estimate matching ⟹ variable form (INT) -/

/-- **Theorem I4.1 (iii).** Under introspection at candidates, estimate matching applied to
`X · 𝟙[E_{P_{t₂}}X = s]` gives variable-form reflection: on a candidate's cell the estimate of
that variable is `s · 𝟙[cell ⊆ {E X = s}]`.
Source: [[radical]] Theorem I4.1 (iii) l. 131; [[armstrong]] Theorem A (a)
Kind: P
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`; INT at candidates is the scope hypothesis
Scope: under introspection at candidates; the twist family separates without it -/
theorem varReflects_of_estimateMatching (hπ : ∀ w, 0 ≤ π w) (hINT : CandsIntrospective π F)
    (h : EstimateMatching π F) : VarReflects π F := by
  intro X s
  set X' : W → ℝ := fun v => X v * ind (estCell F X s) v with hX'
  have hm := h X'
  have hr : E π X' = ∑ w ∈ estCell F X s, π w * X w := by
    unfold E
    rw [hX']
    simp only [ind, mul_ite, mul_one, mul_zero]
    rw [sum_ite_mem, univ_inter]
  have hl : ∀ w, π w * E (F.P w) X' = π w * (s * ind (estCell F X s) w) := by
    intro w
    by_cases hpw : 0 < π w
    · have hc : F.P w ∈ F.cands π := F.P_mem_cands hpw
      congr 1
      by_cases hin : w ∈ estCell F X s
      · have hs : E (F.P w) X = s := mem_estCell.1 hin
        have hE : E (F.P w) X' = E (F.P w) X := by
          apply hINT.E_congr hc
          intro v hv
          have hvin : v ∈ estCell F X s := by rw [mem_estCell, hv, hs]
          simp only [hX', ind, if_pos hvin, mul_one]
        rw [hE, hs]
        simp [ind, hin]
      · have hE : E (F.P w) X' = 0 := by
          apply hINT.E_of_const_on_cell hc
          intro v hv
          have hvin : v ∉ estCell F X s := by
            rw [mem_estCell, hv]
            exact fun e => hin (mem_estCell.2 e)
          simp only [hX', ind, if_neg hvin, mul_zero]
        rw [hE]
        simp [ind, hin]
    · have : π w = 0 := le_antisymm (not_lt.1 hpw) (hπ w)
      rw [this]; ring
  rw [hr] at hm
  rw [← hm, sum_congr rfl (fun w _ => hl w)]
  have : ∑ w, π w * (s * ind (estCell F X s) w) = s * ∑ w, ind (estCell F X s) w * π w := by
    rw [mul_sum]; apply sum_congr rfl; intro w _; ring
  rw [this, sum_ind_mul]

/-! ## (iv) Variable form ⟹ Total Trust (no INT) -/

/-- **Theorem I4.1 (iv).** Variable-form reflection implies Total Trust: the above-threshold sum
is `∑_{t ≥ s} (t − s) · π(E X = t) ≥ 0`. No introspection needed.
Source: [[radical]] Theorem I4.1 (iv) l. 132
Kind: P
Fidelity: exact (DDB's `≥`-threshold record form; radical's strict form is
`TotalTrust.strict`)
Hyps: (a) `∀ w, 0 ≤ π w` only
Scope: no INT -/
theorem totalTrust_of_varReflects (hπ : ∀ w, 0 ≤ π w) (h : VarReflects π F) :
    TotalTrust π F := by
  intro X s
  rw [totalTrust_sum_eq]
  have hmaps : ∀ w ∈ F.estEvent X s,
      E (F.P w) X ∈ (F.estEvent X s).image (fun w => E (F.P w) X) :=
    fun w hw => mem_image_of_mem _ hw
  rw [← sum_fiberwise_of_maps_to hmaps (fun w => π w * (X w - s))]
  apply sum_nonneg
  intro t ht
  obtain ⟨w₀, hw₀, rfl⟩ := mem_image.1 ht
  have hst : s ≤ E (F.P w₀) X := Frame.mem_estEvent.1 hw₀
  have hfil : (F.estEvent X s).filter (fun w => E (F.P w) X = E (F.P w₀) X) =
      estCell F X (E (F.P w₀) X) := by
    ext w
    simp only [mem_filter, Frame.mem_estEvent, mem_estCell]
    exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hst, h⟩⟩
  rw [hfil]
  have hsum : ∑ w ∈ estCell F X (E (F.P w₀) X), π w * (X w - s) =
      (E (F.P w₀) X - s) * mass π (estCell F X (E (F.P w₀) X)) := by
    simp only [mul_sub, sum_sub_distrib]
    rw [h X (E (F.P w₀) X), ← sum_mul]
    unfold mass; ring
  rw [hsum]
  exact mul_nonneg (by linarith) (mass_nonneg hπ _)

/-! ## (v) Total Trust ⟹ variable form (INT) -/

/-- **Theorem I4.1 (v).** Under introspection at candidates, Total Trust implies variable-form
reflection: with `X₋ := X` on the cell `{E X = s}` and `s − 1` off it, every candidate off the
cell estimates `X₋` at `s − 1 < s` and every candidate on it at `s`, so the above-threshold
event at `s` is the cell (up to `π`-null worlds) and Total Trust gives `≥`; the dual at
`X₊ := X` on the cell, `s + 1` off it, gives `≤`. On a finite frame with DDB's `≥`-thresholds no
limit in the threshold is needed.
Source: [[radical]] Theorem I4.1 (v) l. 133
Kind: P
Fidelity: exact (no limit; the strict-threshold form would need one)
Hyps: (a) `∀ w, 0 ≤ π w`; INT at candidates is the scope hypothesis
Scope: under introspection at candidates; `fig3` (Total Trust, not reflected) separates
without it -/
theorem varReflects_of_totalTrust (hπ : ∀ w, 0 ≤ π w) (hINT : CandsIntrospective π F)
    (h : TotalTrust π F) : VarReflects π F := by
  intro X s
  -- the general step: a variable equal to `X` on the cell and to a constant `a` off it
  have key : ∀ (a : ℝ) (w : W), 0 < π w →
      E (F.P w) (fun v => if v ∈ estCell F X s then X v else a) =
        if w ∈ estCell F X s then s else a := by
    intro a w hw
    have hc := F.P_mem_cands hw
    by_cases hin : w ∈ estCell F X s
    · have hs : E (F.P w) X = s := mem_estCell.1 hin
      rw [if_pos hin]
      calc E (F.P w) (fun v => if v ∈ estCell F X s then X v else a) = E (F.P w) X := by
            apply hINT.E_congr hc
            intro v hv
            have hvin : v ∈ estCell F X s := by rw [mem_estCell, hv, hs]
            simp only [if_pos hvin]
        _ = s := hs
    · rw [if_neg hin]
      apply hINT.E_of_const_on_cell hc
      intro v hv
      have hvin : v ∉ estCell F X s := by
        rw [mem_estCell, hv]
        exact fun e => hin (mem_estCell.2 e)
      simp only [if_neg hvin]
  -- lower bound
  have h1 := h (fun v => if v ∈ estCell F X s then X v else s - 1) s
  rw [totalTrust_sum_eq] at h1
  have hE1 : ∀ w, 0 < π w →
      (w ∈ F.estEvent (fun v => if v ∈ estCell F X s then X v else s - 1) s ↔
        w ∈ estCell F X s) := by
    intro w hw
    rw [Frame.mem_estEvent, key (s - 1) w hw]
    split_ifs with hin <;> simp [hin]
  rw [sum_congr_supp hπ hE1] at h1
  have h1' : 0 ≤ ∑ w ∈ estCell F X s, π w * (X w - s) := by
    refine le_trans h1 (le_of_eq (sum_congr rfl fun w hw => ?_))
    simp [hw]
  -- upper bound via the dual form
  have h2 := totalTrust_iff_dual.1 h (fun v => if v ∈ estCell F X s then X v else s + 1) s
  rw [totalTrust_dual_sum_eq] at h2
  have hE2 : ∀ w, 0 < π w →
      (w ∈ F.estEventLE (fun v => if v ∈ estCell F X s then X v else s + 1) s ↔
        w ∈ estCell F X s) := by
    intro w hw
    rw [Frame.mem_estEventLE, key (s + 1) w hw]
    split_ifs with hin <;> simp [hin]
  rw [sum_congr_supp hπ hE2] at h2
  have h2' : ∑ w ∈ estCell F X s, π w * (X w - s) ≤ 0 := by
    refine le_trans (le_of_eq (sum_congr rfl fun w hw => ?_)) h2
    simp [hw]
  have heq : ∑ w ∈ estCell F X s, π w * (X w - s) = 0 := le_antisymm h2' h1'
  simp only [mul_sub, sum_sub_distrib, ← sum_mul] at heq
  unfold mass; linarith

/-! ## Theorem A(c): reflection forces introspection at candidates -/

/-- **Theorem A(c).** Reflection forces introspection at every candidate: off the cell of a
candidate `ρ`, `0 = π(P = ρ) · ρ w` with `π(P = ρ) > 0`, so `ρ` lives on its cell. (`lit-ddb-facts`
proves this too; it is not a dependency, so it is re-proved here — a duplication by the
dependency graph, not a second definition.)
Source: [[armstrong]] Theorem A (c) l. 107; [[radical]] I4 DDB l. 80 (reflection presupposes
immodesty)
Kind: P
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem candsIntrospective_of_reflects (hπ : ∀ w, 0 ≤ π w) (h : Reflects π F) :
    CandsIntrospective π F := by
  intro ρ hρ
  have hρs := F.mem_stdSimplex_of_mem_cands hρ
  have hpos : 0 < mass π (F.cell ρ) := (F.mem_cands_iff_mass_cell_pos hπ).1 hρ
  have hz : ∀ v, v ∉ F.cell ρ → ρ v = 0 := by
    intro v hv
    have := h ρ hρ v
    have hind : ind (F.cell ρ) v = 0 := by simp [ind, hv]
    rw [hind, mul_zero] at this
    rcases mul_eq_zero.1 this.symm with h0 | h0
    · exact absurd h0 hpos.ne'
    · exact h0
  unfold Frame.selfMass
  rw [← mass_univ hρs]
  unfold mass
  apply sum_subset (subset_univ _)
  intro v _ hv
  exact hz v hv

/-! ## The collapse -/

/-- **Theorem I4.1 / Theorem A (the collapse).** Under introspection at candidates the five
reflection forms and DDB's Value are equivalent: Reflection (function form), value-form
reflection, variable-form reflection, estimate matching (Mart / sequential unbiasedness in one
step / stationarity) and Total Trust; `Value` by `lit-ddb-frames`' Theorem 2.2. Assembled from
the seven separately proved arrows above; the report records which need INT.
Source: [[radical]] Theorem I4.1 ll. 127–133; [[armstrong]] Theorem A ll. 103–109;
[[mm]] Corollary I4.1 l. 140
Kind: C
Fidelity: exact (DDB's `≥`-threshold Total Trust; finite frames)
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W`; INT at candidates is the scope hypothesis
Scope: under introspection at candidates (`CandsIntrospective π F`); `fig3` separates the
forms without it (Total Trust and Value hold, Reflection fails), the twist family separates
estimate matching from Reflection -/
theorem collapse (hπ : π ∈ stdSimplex ℝ W) (hINT : CandsIntrospective π F) :
    List.TFAE [Reflects π F, ValueReflects π F, VarReflects π F, EstimateMatching π F,
      TotalTrust π F, Value π F] := by
  tfae_have 1 → 3 := varReflects_of_reflects hπ.1
  tfae_have 3 → 2 := valueReflects_of_varReflects
  tfae_have 2 → 1 := reflects_of_valueReflects hπ.1 hINT
  tfae_have 3 → 4 := estimateMatching_of_varReflects
  tfae_have 4 → 3 := varReflects_of_estimateMatching hπ.1 hINT
  tfae_have 3 → 5 := totalTrust_of_varReflects hπ.1
  tfae_have 5 → 3 := varReflects_of_totalTrust hπ.1 hINT
  tfae_have 5 ↔ 6 := (value_iff_totalTrust hπ F).symm
  tfae_finish

/-- **Theorem A, INT-free form.** Reflection is exactly estimate matching together with
introspection at candidates (Armstrong: `SU ∧ introspection ⟺ general reflection`).
Source: [[armstrong]] Theorem A l. 108 ("Hence … SU ∧ introspection ⟺ general reflection")
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem reflects_iff_estimateMatching_and_int (hπ : ∀ w, 0 ≤ π w) :
    Reflects π F ↔ EstimateMatching π F ∧ CandsIntrospective π F :=
  ⟨fun h => ⟨estimateMatching_of_varReflects (varReflects_of_reflects hπ h),
      candsIntrospective_of_reflects hπ h⟩,
    fun ⟨h, hI⟩ => reflects_of_valueReflects hπ hI
      (valueReflects_of_varReflects (varReflects_of_estimateMatching hπ hI h))⟩

/-- Reflection is exactly value-form reflection together with introspection at candidates.
Source: [[radical]] Theorem I4.1 (ii) with Theorem A (c)
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem reflects_iff_valueReflects_and_int (hπ : ∀ w, 0 ≤ π w) :
    Reflects π F ↔ ValueReflects π F ∧ CandsIntrospective π F :=
  ⟨fun h => ⟨valueReflects_of_varReflects (varReflects_of_reflects hπ h),
      candsIntrospective_of_reflects hπ h⟩,
    fun ⟨h, hI⟩ => reflects_of_valueReflects hπ hI h⟩

/-- Reflection is exactly Total Trust together with introspection at candidates.
Source: [[radical]] Theorem I4.1 (iv)/(v) with Theorem A (c)
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem reflects_iff_totalTrust_and_int (hπ : ∀ w, 0 ≤ π w) :
    Reflects π F ↔ TotalTrust π F ∧ CandsIntrospective π F :=
  ⟨fun h => ⟨totalTrust_of_varReflects hπ (varReflects_of_reflects hπ h),
      candsIntrospective_of_reflects hπ h⟩,
    fun ⟨h, hI⟩ => reflects_of_valueReflects hπ hI
      (valueReflects_of_varReflects (varReflects_of_totalTrust hπ hI h))⟩

/-! ## T2(a): estimate matching is stationarity -/

/-- **Estimate matching is stationarity** `π = πP`: `∑ w, π w · P_w(w') = π w'` for every `w'`.
Source: [[ddb]] iteration item l. 149; [[armstrong]] I2.2 (`∑_c P(c) q_c = P`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem estimateMatching_iff_stationary :
    EstimateMatching π F ↔ ∀ w', ∑ w, π w * F.P w w' = π w' := by
  constructor
  · intro h w'
    have := h (ind {w'})
    simpa only [E_ind, mass_singleton] using this
  · intro h X
    unfold E
    calc ∑ w, π w * ∑ v, F.P w v * X v = ∑ v, (∑ w, π w * F.P w v) * X v := by
          simp only [mul_sum, sum_mul]
          rw [sum_comm]
          apply sum_congr rfl; intro v _; apply sum_congr rfl; intro w _; ring
      _ = ∑ v, π v * X v := by simp only [h]

end

end Cleanroom.Corrigibility.CorrReflectFrames
