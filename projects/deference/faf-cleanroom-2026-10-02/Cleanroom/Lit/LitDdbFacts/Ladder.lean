import Cleanroom.Lit.LitDdbFacts.Reflection

/-!
# The ladder: Total Trust ⟹ conditional Total Trust ⟹ Trust ⟹ New Reflection, and the
immodest collapse

Package `lit-ddb-facts`, Targets 6 and 5. Conditional Total Trust (fn 36's shape) is Total Trust
(`q = W` recovers the record form), so the plan's "frames on which conditional Total Trust is
strictly weaker" is empty by a two-line lemma. Trust implies New Reflection (fn 37, both
inequalities, with the self-cell positivity derived from Simple Trust's symmetric form). The
comparative (fn 29) and averaged (fn 38) forms. Then the immodest collapse of §5: on an immodest
frame the six principles Reflection, New Reflection, Simple Trust, Trust, Total Trust and Value
coincide, the new arrow being Simple Trust ⟹ Reflection.
-/

namespace Cleanroom.Lit.LitDdbFacts

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Target 6(a): conditional Total Trust is Total Trust -/

/-- **Conditional Total Trust** (fn 36's shape, product form): for every variable `X`,
proposition `q` and threshold `t`, `t · π(q ∧ [E(X | q) ≥ t]) ≤ ∑_{w ∈ q ∧ [E(X | q) ≥ t]} π w · X w`
— the statement `TotalTrust.cond` proves.
Source: [[Deference Done Better]] §2 l. 182, fn 36
Kind: D
Fidelity: exact -/
def CondTotalTrust (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ (X : W → ℝ) (q : Finset W) (t : ℝ),
    t * mass π (q ∩ F.condEstEvent X q t) ≤ ∑ w ∈ q ∩ F.condEstEvent X q t, π w * X w

/-- Total Trust implies conditional Total Trust (`lit-ddb-frames`, `TotalTrust.cond`).
Source: [[Deference Done Better]] §2 l. 182, fn 36
Kind: L
Fidelity: exact -/
theorem condTotalTrust_of_totalTrust {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : TotalTrust π F) : CondTotalTrust π F :=
  fun X q t => h.cond hπ X q t

/-- `[E(X | W) ≥ t] = [E(X) ≥ t]`: conditioning on everything is not conditioning.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condEstEvent_univ (F : Frame W) (X : W → ℝ) (t : ℝ) :
    F.condEstEvent X univ t = F.estEvent X t := by
  ext w
  simp only [Frame.mem_condEstEvent, Frame.mem_estEvent, mass_univ (F.P_mem w), mul_one, E]
  simp

/-- **Target 6(a).** Conditional Total Trust implies Total Trust: instantiate at `q = W`.
Together with the converse this shows the plan's `extension` for this package ("frames on which
conditional Total Trust is strictly weaker than Total Trust") is empty.
Source: [[Deference Done Better]] §2 l. 182; plan entry `lit-ddb-facts` (extension), refuted
Kind: L
Fidelity: exact -/
theorem totalTrust_of_condTotalTrust {π : W → ℝ} {F : Frame W} (h : CondTotalTrust π F) :
    TotalTrust π F := by
  intro X s
  have := h X univ s
  rw [condEstEvent_univ, univ_inter] at this
  rw [totalTrust_sum_eq]
  have e : ∑ w ∈ F.estEvent X s, π w * (X w - s) =
      (∑ w ∈ F.estEvent X s, π w * X w) - s * mass π (F.estEvent X s) := by
    simp [mul_sub, sum_sub_distrib, mass, mul_sum, mul_comm]
  rw [e]
  linarith

/-- Conditional Total Trust *is* Total Trust.
Source: [[Deference Done Better]] §2 l. 182, fn 36; plan extension (vacuous)
Kind: L
Fidelity: exact -/
theorem condTotalTrust_iff_totalTrust {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} :
    CondTotalTrust π F ↔ TotalTrust π F :=
  ⟨totalTrust_of_condTotalTrust, condTotalTrust_of_totalTrust hπ⟩

/-! ## Target 6(b): Trust ⟹ New Reflection -/

/-- `[P(q | W) ≥ t] = [P(q) ≥ t]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condProbEvent_univ (F : Frame W) (q : Finset W) (t : ℝ) :
    F.condProbEvent q univ t = F.probEvent q t := by
  ext w
  simp [Frame.condProbEvent, Frame.probEvent, mass_univ (F.P_mem w)]

/-- Trust implies Simple Trust (`p = W`).
Source: [[Deference Done Better]] §2 l. 154 (Trust generalises Simple Trust)
Kind: L
Fidelity: exact -/
theorem simpleTrust_of_trust {π : W → ℝ} {F : Frame W} (h : Trust π F) : SimpleTrust π F := by
  intro q t hpos
  have := h q univ t (by rwa [condProbEvent_univ, univ_inter])
  rwa [condProbEvent_univ, univ_inter] at this

/-- **Simple Trust forces positive self-cells at candidates.** The symmetric form
`π(p | P(p) ≤ s) ≤ s` at `p = [P = ρ]`, `s = 0` — derived from Simple Trust at
`q = [P = ρ]ᶜ`, `t = 1` — has an event containing the cell, forcing `π(P = ρ) ≤ 0` if
`ρ(P = ρ) = 0`.
Source: [[Deference Done Better]] §2 l. 150 (symmetry of Simple Trust), fn 37 (presupposition)
Kind: P
Fidelity: exact
Hyps: (a) `hπ` -/
theorem selfMass_pos_of_simpleTrust {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : SimpleTrust π F) {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) : 0 < F.selfMass ρ := by
  have hρs := F.mem_stdSimplex_of_mem_cands hρ
  have hm : 0 < mass π (F.cell ρ) := (F.mem_cands_iff_mass_cell_pos hπ).1 hρ
  by_contra hnot
  have h0 : F.selfMass ρ = 0 := le_antisymm (not_lt.1 hnot) (mass_nonneg hρs.1 _)
  set q := univ \ F.cell ρ with hq
  have hsub : F.cell ρ ⊆ F.probEvent q 1 := by
    intro u hu
    rw [Frame.probEvent, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [Frame.mem_cell] at hu
    rw [hu]
    have := mass_inter_add_mass_sdiff ρ univ (F.cell ρ)
    rw [univ_inter, mass_univ hρs] at this
    unfold Frame.selfMass at h0
    rw [hq]
    linarith
  have hpos : 0 < mass π (F.probEvent q 1) := lt_of_lt_of_le hm (mass_mono hπ hsub)
  have hst := h q 1 hpos
  rw [one_mul] at hst
  have hsplit := mass_inter_add_mass_sdiff π (F.probEvent q 1) (F.cell ρ)
  rw [inter_eq_right.2 hsub] at hsplit
  have h2 : q ∩ F.probEvent q 1 ⊆ F.probEvent q 1 \ F.cell ρ := by
    intro u hu
    rw [mem_inter] at hu
    rw [mem_sdiff]
    refine ⟨hu.2, fun hc => ?_⟩
    have := hu.1
    rw [hq, mem_sdiff] at this
    exact this.2 hc
  have := mass_mono hπ h2
  linarith

/-- **Target 6(b), fn 37.** Trust implies New Reflection (strong reading): the self-cell of a
candidate is positive by `selfMass_pos_of_simpleTrust`, and for each world `v` of the cell, Trust
at `q = {v}`, `p = [P = ρ]`, `t = ρ(v | P = ρ)` gives `ρ(v | P = ρ) · π(P = ρ) ≤ π v`; summing over
the cell turns these into equalities (fn 37's second inequality is replaced by the sum). The
null-event reading of `Frame.condProbEvent` (worlds with `P_w(p) = 0` are excluded from
`[P(q | p) ≥ t]`, frames' audit NB7) is immaterial here: every `u` in the cell `p = [P = ρ]` has
`P_u = ρ` and `P_u(p) = ρ(P = ρ) > 0`, so no world of `p` is excluded under either reading and
`p ∩ [P(q | p) ≥ t]` is the whole cell either way.
Source: [[Deference Done Better]] §2 l. 182, l. 227, fn 37
Kind: P
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` -/
theorem newReflects_of_trust {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : Trust π F) : NewReflects π F := by
  intro ρ hρ
  have hpos := selfMass_pos_of_simpleTrust hπ.1 (simpleTrust_of_trust h) hρ
  refine ⟨hpos, fun w => ?_⟩
  have hρs := F.mem_stdSimplex_of_mem_cands hρ
  have hm : 0 < mass π (F.cell ρ) := (F.mem_cands_iff_mass_cell_pos hπ.1).1 hρ
  have hs : 0 < mass ρ (F.cell ρ) := hpos
  have hA : ∀ v ∈ F.cell ρ, ρ v * mass π (F.cell ρ) ≤ π v * F.selfMass ρ := by
    intro v hv
    have hvc : ({v} : Finset W) ∩ F.cell ρ = {v} :=
      inter_eq_left.2 (singleton_subset_iff.2 hv)
    have hev : F.cell ρ ∩ F.condProbEvent {v} (F.cell ρ) (ρ v / F.selfMass ρ) = F.cell ρ := by
      apply inter_eq_left.2
      intro u hu
      rw [Frame.condProbEvent, mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rw [Frame.mem_cell] at hu
      rw [hu, hvc, mass_singleton]
      refine ⟨hs, ?_⟩
      unfold Frame.selfMass
      rw [div_mul_cancel₀ _ hs.ne']
    have ht := h {v} (F.cell ρ) (ρ v / F.selfMass ρ) (by rw [hev]; exact hm)
    rw [hev, hvc, mass_singleton] at ht
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos] at ht
    exact ht
  have hB : ∀ v ∈ F.cell ρ, π v * F.selfMass ρ = ρ v * mass π (F.cell ρ) := by
    have hsum : ∑ v ∈ F.cell ρ, (π v * F.selfMass ρ - ρ v * mass π (F.cell ρ)) = 0 := by
      rw [sum_sub_distrib, ← sum_mul, ← sum_mul]
      have e1 : ∑ v ∈ F.cell ρ, π v = mass π (F.cell ρ) := rfl
      have e2 : ∑ v ∈ F.cell ρ, ρ v = F.selfMass ρ := rfl
      rw [e1, e2]
      ring
    have hnn : ∀ v ∈ F.cell ρ, 0 ≤ π v * F.selfMass ρ - ρ v * mass π (F.cell ρ) :=
      fun v hv => by linarith [hA v hv]
    intro v hv
    have := (sum_eq_zero_iff_of_nonneg hnn).1 hsum v hv
    linarith
  by_cases hw : F.P w = ρ
  · have hind : ind (F.cell ρ) w = 1 := by simp [ind, hw]
    rw [hind, mul_one, mul_one, hB w (Frame.mem_cell.2 hw)]
    ring
  · have hind : ind (F.cell ρ) w = 0 := by simp [ind, hw]
    rw [hind]
    ring

/-! ## Target 6(c): the comparative form -/

/-- **Comparative Total Trust** (fn 29, product form): for all `X, Y`,
`0 ≤ ∑ w, π w · (X w − Y w) · 𝟙[E_w(Y) ≤ E_w(X)]`, i.e. `E_π(X | E(X) ≥ E(Y)) ≥ E_π(Y | E(X) ≥ E(Y))`
off null events.
Source: [[Deference Done Better]] §2 l. 184, fn 29
Kind: D
Fidelity: exact -/
def ComparativeTotalTrust (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ X Y : W → ℝ, 0 ≤ ∑ w, π w * (X w - Y w) * (if E (F.P w) Y ≤ E (F.P w) X then 1 else 0)

/-- **Target 6(c).** The comparative form is equivalent to Total Trust: (⇐) instance at
`X − Y`, threshold `0`; (⇒) `Y := const t`.
Source: [[Deference Done Better]] fn 29
Kind: L
Fidelity: exact -/
theorem comparativeTotalTrust_iff_totalTrust {π : W → ℝ} {F : Frame W} :
    ComparativeTotalTrust π F ↔ TotalTrust π F := by
  constructor
  · intro h X s
    have := h X (fun _ => s)
    have e : ∀ w, E (F.P w) (fun _ => s) = s := fun w => E_const (F.P_mem w) s
    simp only [e] at this
    exact this
  · intro h X Y
    have := h (X - Y) 0
    simp only [Pi.sub_apply, sub_zero, E_sub_right, sub_nonneg] at this
    exact this

/-! ## Target 6(d): the averaged form -/

/-- The event "the expert's average credence across `q_1, …, q_n` is at least `t`".
Source: [[Deference Done Better]] fn 38
Kind: D
Fidelity: exact -/
def averagedEvent (F : Frame W) {n : ℕ} (q : Fin n → Finset W) (t : ℝ) : Finset W :=
  univ.filter (fun w => t ≤ (1 / (n : ℝ)) * ∑ i, mass (F.P w) (q i))

/-- **Averaged Total Trust** (fn 38, product form): conditional on the expert's average
credence across `q_1, …, q_n` being at least `t`, `π`'s average credence is at least `t`.
Source: [[Deference Done Better]] fn 38
Kind: D
Fidelity: exact -/
def AveragedTotalTrust (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (q : Fin n → Finset W) (t : ℝ),
    t * mass π (averagedEvent F q t) ≤ (1 / (n : ℝ)) * ∑ i, mass π (q i ∩ averagedEvent F q t)

/-- The expectation of an average of indicators is the average of the masses.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_avg_ind (ρ : W → ℝ) {n : ℕ} (q : Fin n → Finset W) :
    E ρ ((1 / (n : ℝ)) • ∑ i, ind (q i)) = (1 / (n : ℝ)) * ∑ i, mass ρ (q i) := by
  rw [E_smul_right]
  congr 1
  simp only [E, Finset.sum_apply, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [mass_eq_E_ind, E]

/-- **Target 6(d).** Total Trust implies averaged Total Trust: the record form at
`X = (1/n) ∑_i 𝟙_{q_i}`.
Source: [[Deference Done Better]] fn 38
Kind: L
Fidelity: exact -/
theorem averagedTotalTrust_of_totalTrust {π : W → ℝ} {F : Frame W} (h : TotalTrust π F) :
    AveragedTotalTrust π F := by
  intro n _ q t
  set X : W → ℝ := (1 / (n : ℝ)) • ∑ i, ind (q i) with hX
  have hev : F.estEvent X t = averagedEvent F q t := by
    ext w
    rw [Frame.mem_estEvent, averagedEvent, mem_filter, hX, E_avg_ind]
    simp
  have h1 := h.event_sum X t
  rw [hev] at h1
  have e : ∑ w ∈ averagedEvent F q t, π w * (X w - t) =
      (1 / (n : ℝ)) * (∑ i, mass π (q i ∩ averagedEvent F q t)) -
        t * mass π (averagedEvent F q t) := by
    simp only [mul_sub, sum_sub_distrib]
    congr 1
    · simp only [hX, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [mass, inter_comm, ← sum_ite_mem, mul_sum]
      apply sum_congr rfl
      intro w _
      simp only [ind]
      split_ifs <;> ring
    · rw [mass, mul_sum]
      apply sum_congr rfl
      intro w _
      ring
  rw [e] at h1
  linarith

/-! ## Target 5: the immodest collapse -/

/-- **Target 5, the new arrow.** On immodest candidates, Simple Trust implies Reflection: for a
candidate `ρ` and a world `v` of its cell, the event `[P({v}) ≥ ρ v]` agrees with `[P = ρ]` on the
support of `π` (any other candidate is immodest, hence supported on its own disjoint cell, and
gives `v` probability `0 < ρ v`), so Simple Trust gives `ρ v · π(P = ρ) ≤ π v`; summing over the
cell makes these equalities.
Source: [[Deference Done Better]] §5 l. 390 ("in the context of immodesty … all the plausible
theories … coincide")
Kind: P
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W`; immodesty of the candidates is the theorem's antecedent -/
theorem reflects_of_simpleTrust_of_immodest {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (himm : ∀ ρ ∈ F.cands π, F.selfMass ρ = 1) (h : SimpleTrust π F) : Reflects π F := by
  intro ρ hρ w
  have hρs := F.mem_stdSimplex_of_mem_cands hρ
  have hone := himm ρ hρ
  have hm : 0 < mass π (F.cell ρ) := (F.mem_cands_iff_mass_cell_pos hπ.1).1 hρ
  have hA : ∀ v ∈ F.cell ρ, ρ v * mass π (F.cell ρ) ≤ π v := by
    intro v hv
    rcases (hρs.1 v).lt_or_eq with hρv | hρv
    · have hev : ∀ u, 0 < π u → (u ∈ F.probEvent {v} (ρ v) ↔ u ∈ F.cell ρ) := by
        intro u hu
        rw [Frame.probEvent, mem_filter, Frame.mem_cell, mass_singleton]
        constructor
        · rintro ⟨_, hle⟩
          by_contra hne
          have hu1 := himm (F.P u) (F.P_mem_cands hu)
          have := eq_zero_of_selfMass_eq_one F (F.P_mem u) hu1
            (show F.P v ≠ F.P u from fun e => hne ((Frame.mem_cell.1 hv).symm.trans e).symm)
          linarith
        · intro hu
          exact ⟨mem_univ _, by rw [hu]⟩
      have hmass : mass π (F.probEvent {v} (ρ v)) = mass π (F.cell ρ) :=
        mass_eq_of_supp_iff hπ.1 hev
      have hpos : 0 < mass π (F.probEvent {v} (ρ v)) := by rw [hmass]; exact hm
      have hst := h {v} (ρ v) hpos
      rw [hmass] at hst
      have hle : mass π ({v} ∩ F.probEvent {v} (ρ v)) ≤ π v := by
        rw [← mass_singleton π v]
        exact mass_mono hπ.1 inter_subset_left
      linarith
    · rw [← hρv, zero_mul]
      exact hπ.1 v
  have hB : ∀ v ∈ F.cell ρ, π v = ρ v * mass π (F.cell ρ) := by
    have hsum : ∑ v ∈ F.cell ρ, (π v - ρ v * mass π (F.cell ρ)) = 0 := by
      rw [sum_sub_distrib, ← sum_mul]
      have e1 : ∑ v ∈ F.cell ρ, π v = mass π (F.cell ρ) := rfl
      have e2 : ∑ v ∈ F.cell ρ, ρ v = F.selfMass ρ := rfl
      rw [e1, e2, hone]
      ring
    have hnn : ∀ v ∈ F.cell ρ, 0 ≤ π v - ρ v * mass π (F.cell ρ) :=
      fun v hv => by linarith [hA v hv]
    intro v hv
    have := (sum_eq_zero_iff_of_nonneg hnn).1 hsum v hv
    linarith
  by_cases hw : F.P w = ρ
  · have hind : ind (F.cell ρ) w = 1 := by simp [ind, hw]
    rw [hind, mul_one, hB w (Frame.mem_cell.2 hw)]
    ring
  · have hind : ind (F.cell ρ) w = 0 := by simp [ind, hw]
    have hz : ρ w = 0 := eq_zero_of_selfMass_eq_one F hρs hone hw
    rw [hind, hz]
    ring

/-- **Target 5, the immodest collapse (headline).** When every candidate of `π` is immodest, the
six principles coincide: Reflection, New Reflection, Simple Trust, Trust, Total Trust, Value.
Arrows: Reflection ⟺ New Reflection (Target 1); Reflection ⟹ Value (Target 3); Value ⟹ Total
Trust (Theorem 2.2, `lit-ddb-frames`); Total Trust ⟹ Trust (`TotalTrust.trust`); Trust ⟹ Simple
Trust; Simple Trust ⟹ Reflection (`reflects_of_simpleTrust_of_immodest`). Not a squeeze: the only
hypothesis is immodesty of the candidates, and the weakest rung (Simple Trust) closes the cycle.
Source: [[Deference Done Better]] §5 l. 390; plan extension for `lit-ddb-facts` ("none exists on
immodest frames")
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` -/
theorem tfae_immodest {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (himm : ∀ ρ ∈ F.cands π, F.selfMass ρ = 1) :
    List.TFAE [Reflects π F, NewReflects π F, SimpleTrust π F, Trust π F, TotalTrust π F,
      Value π F] := by
  tfae_have 1 ↔ 2 := reflects_iff_newReflects_of_immodest hπ.1 himm
  tfae_have 1 → 6 := value_of_reflects hπ.1
  tfae_have 6 → 5 := (value_iff_totalTrust hπ F).1
  tfae_have 5 → 4 := TotalTrust.trust hπ.1
  tfae_have 4 → 3 := simpleTrust_of_trust
  tfae_have 3 → 1 := reflects_of_simpleTrust_of_immodest hπ himm
  tfae_finish

/-- **Target 5, whole-frame form.** On an immodest frame the six principles coincide.
Source: [[Deference Done Better]] §5 l. 390
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` -/
theorem tfae_immodestFrame {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (hF : F.Immodest) :
    List.TFAE [Reflects π F, NewReflects π F, SimpleTrust π F, Trust π F, TotalTrust π F,
      Value π F] :=
  tfae_immodest hπ (immodest_cands hF π)

end

end Cleanroom.Lit.LitDdbFacts
