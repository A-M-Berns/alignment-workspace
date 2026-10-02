import Cleanroom.Lit.LitDdbFacts.Cells

/-!
# The Reflection facts of Deference Done Better §1

Package `lit-ddb-facts`, Targets 1–4: Reflection forces immodest candidates (the opening
impossibility, fn 11); New Reflection is Reflection of the informed expert (fn 12, with the junk
cell where the vacuous reading hides); Reflection implies Value directly (fn 16) and is
equivalent to it on immodest frames (fn 17); Value implies New Reflection by fn 19's conditional
bet, not through the cycle. Target 5 (the immodest collapse) is in `Ladder.lean`, after
Trust ⟹ Simple Trust.

Every predicate is `lit-ddb-frames`'s definition of record; nothing from DDB is assumed.
-/

namespace Cleanroom.Lit.LitDdbFacts

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Target 1: Reflection forces immodest candidates -/

/-- **Target 1.** If `π` reflects the frame, every candidate `ρ ∈ C_π` is immodest,
`ρ(P = ρ) = 1`: summing the product identity `π w · 𝟙[P_w = ρ] = π(P = ρ) · ρ w` over the cell
gives `π(P = ρ) = π(P = ρ) · ρ(P = ρ)` with `π(P = ρ) > 0` by candidacy. This is the opening
impossibility of §1: Reflection is incompatible with leaving a modest expert open.
Source: [[Deference Done Better]] §1 l. 80, fn 11
Kind: P
Fidelity: exact
Hyps: (a) `hπ : ∀ w, 0 ≤ π w` (nonnegativity, part of `π ∈ stdSimplex`) -/
theorem selfMass_eq_one_of_reflects {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : Reflects π F) {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) : F.selfMass ρ = 1 := by
  have hm : 0 < mass π (F.cell ρ) := (F.mem_cands_iff_mass_cell_pos hπ).1 hρ
  have hsum : ∑ w ∈ F.cell ρ, π w * ind (F.cell ρ) w =
      ∑ w ∈ F.cell ρ, mass π (F.cell ρ) * ρ w :=
    sum_congr rfl fun w _ => h ρ hρ w
  have hl : ∑ w ∈ F.cell ρ, π w * ind (F.cell ρ) w = mass π (F.cell ρ) := by
    unfold mass
    apply sum_congr rfl
    intro w hw
    simp [ind, hw]
  have hr : ∑ w ∈ F.cell ρ, mass π (F.cell ρ) * ρ w = mass π (F.cell ρ) * F.selfMass ρ := by
    rw [← mul_sum]; rfl
  rw [hl, hr] at hsum
  exact mul_left_cancel₀ hm.ne' (hsum.symm.trans (mul_one _).symm)

/-- Reflection implies New Reflection (strong reading): every candidate is immodest, so the
informed expert exists and the two product identities agree.
Source: [[Deference Done Better]] §1 l. 89 (fn 17, first half)
Kind: L
Fidelity: exact -/
theorem newReflects_of_reflects {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : Reflects π F) : NewReflects π F := by
  intro ρ hρ
  have h1 := selfMass_eq_one_of_reflects hπ h hρ
  refine ⟨by rw [h1]; exact one_pos, fun w => ?_⟩
  rw [h1, mul_one, h ρ hρ w]
  by_cases hw : F.P w = ρ
  · simp [ind, hw]
  · have hz : ρ w = 0 := eq_zero_of_selfMass_eq_one F (F.mem_stdSimplex_of_mem_cands hρ) h1 hw
    simp [ind, hw, hz]

/-- **Fn 17, first half.** When every candidate of `π` is immodest, Reflection and New
Reflection coincide: with `ρ(P = ρ) = 1` the candidate is supported on its cell, so the two
product identities agree off the cell as well.
Source: [[Deference Done Better]] §1 l. 89, fn 17
Kind: L
Fidelity: exact -/
theorem reflects_iff_newReflects_of_immodest {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (himm : ∀ ρ ∈ F.cands π, F.selfMass ρ = 1) : Reflects π F ↔ NewReflects π F := by
  refine ⟨newReflects_of_reflects hπ, fun h ρ hρ w => ?_⟩
  have h1 := himm ρ hρ
  have := (h ρ hρ).2 w
  rw [h1, mul_one] at this
  rw [this]
  by_cases hw : F.P w = ρ
  · simp [ind, hw]
  · have hz : ρ w = 0 := eq_zero_of_selfMass_eq_one F (F.mem_stdSimplex_of_mem_cands hρ) h1 hw
    simp [ind, hw, hz]

/-- On an immodest frame Reflection and New Reflection coincide (whole-frame form).
Source: [[Deference Done Better]] §1 l. 89
Kind: L
Fidelity: exact -/
theorem reflects_iff_newReflects_of_immodestFrame {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (hF : F.Immodest) : Reflects π F ↔ NewReflects π F :=
  reflects_iff_newReflects_of_immodest hπ (immodest_cands hF π)

/-- **Target 1, contrapositive.** A deferrer that leaves a modest world open does not reflect the
frame.
Source: [[Deference Done Better]] §1 l. 80 ("it's impossible for any distribution to reflect a
frame while assigning non-zero probability to the possibility that the expert is modest")
Kind: L
Fidelity: exact -/
theorem not_reflects_of_modestAt {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} {w : W}
    (hmod : F.ModestAt w) (hw : 0 < π w) : ¬ Reflects π F := fun h => by
  have := selfMass_eq_one_of_reflects hπ h (F.P_mem_cands hw)
  unfold Frame.ModestAt at hmod
  linarith

/-- On a candidate's cell, Reflection turns a `π`-weighted sum into `π(P = ρ) · E_ρ(X)` (total
probability with the candidate supported on its cell).
Source: [[Deference Done Better]] fn 16 (the total-expectation step)
Kind: L
Fidelity: n/a -/
theorem reflects_cell_sum {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} (h : Reflects π F)
    {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) (X : W → ℝ) :
    ∑ w ∈ F.cell ρ, π w * X w = mass π (F.cell ρ) * E ρ X := by
  have hρs := F.mem_stdSimplex_of_mem_cands hρ
  have hone := selfMass_eq_one_of_reflects hπ h hρ
  have hsupp : ∀ w, w ∉ F.cell ρ → ρ w = 0 := fun w hw =>
    eq_zero_of_selfMass_eq_one F hρs hone (fun e => hw (Frame.mem_cell.2 e))
  rw [E_eq_sum_of_support_left hsupp, mul_sum]
  apply sum_congr rfl
  intro w hw
  have := h ρ hρ w
  rw [show ind (F.cell ρ) w = 1 by simp [ind, hw], mul_one] at this
  rw [this]; ring

/-! ## Target 2: New Reflection is Reflection of the informed expert -/

/-- The informed cell `[P̂ = σ]`: the worlds at which the informed expert's distribution is `σ`.
At a world with a null self-cell `P̂_w` is the junk vector `0`, so `[P̂ = 0]` is the set of such
worlds (`informedCell_zero`).
Source: [[Deference Done Better]] §1 l. 97 (informed version), fn 12
Kind: D
Fidelity: exact -/
def informedCell (F : Frame W) (σ : W → ℝ) : Finset W :=
  univ.filter (fun w => F.informed (F.P w) = σ)

/-- Membership in an informed cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem mem_informedCell {F : Frame W} {σ : W → ℝ} {w : W} :
    w ∈ informedCell F σ ↔ F.informed (F.P w) = σ := by
  simp [informedCell]

/-- **New Reflection (informed version)**: `π(· | P̂ = σ) = σ` in product form, for every `σ`
whose informed cell has positive `π`-mass — quantified over *all* vectors `σ`, so that the junk
cell `[P̂ = 0]` is constrained too (it is forced `π`-null, `informedReflects_junk_null`). The
reading with `σ ∈ stdSimplex` only is `InformedReflectsSimplex`.
Source: [[Deference Done Better]] §1 l. 97, fn 12
Kind: D
Fidelity: exact -/
def InformedReflects (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ σ, 0 < mass π (informedCell F σ) →
    ∀ w, π w * ind (informedCell F σ) w = mass π (informedCell F σ) * σ w

/-- **Fn 12 as a lemma.** At a positive self-cell, `[P̂ = P̂_ρ] = [P = ρ]`: the informed vector of
a different row has mass `0` on `[P = ρ]`, while `P̂_ρ` has mass `1` there.
Source: [[Deference Done Better]] fn 12
Kind: P
Fidelity: exact
Hyps: (a) `0 < ρ(P = ρ)` (the informed expert exists) -/
theorem informedCell_informed (F : Frame W) {ρ : W → ℝ} (hpos : 0 < F.selfMass ρ) :
    informedCell F (F.informed ρ) = F.cell ρ := by
  ext v
  rw [mem_informedCell, Frame.mem_cell]
  constructor
  · intro hv
    by_contra hne
    have h0 : mass (F.informed (F.P v)) (F.cell ρ) = 0 := F.mass_informed_cell_of_ne hne
    have h1 : mass (F.informed ρ) (F.cell ρ) = 1 := by
      have := F.mass_informed_cell_mul hpos
      exact (mul_left_inj' hpos.ne').1 (by rw [this, one_mul])
    rw [hv] at h0
    rw [h0] at h1
    exact zero_ne_one h1
  · intro hv; rw [hv]

/-- The junk informed cell `[P̂ = 0]` is the set of worlds with a null self-cell.
Source: none: infrastructure (Target 2(b))
Kind: L
Fidelity: n/a -/
theorem informedCell_zero (F : Frame W) :
    informedCell F 0 = univ.filter (fun w => F.selfMass (F.P w) = 0) := by
  ext w
  simp [mem_informedCell, informed_eq_zero_iff F (F.P_nonneg w)]

/-- **Target 2(b).** The informed version of New Reflection forces the junk cell `[P̂ = 0]` to be
`π`-null: the identity at `σ = 0` reads `π w = 0` on the event.
Source: [[Deference Done Better]] fn 12 (item 039's partition worry)
Kind: P
Fidelity: exact
Hyps: (a) `hπ` -/
theorem informedReflects_junk_null {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : InformedReflects π F) : mass π (informedCell F 0) = 0 := by
  by_contra hne
  have hpos : 0 < mass π (informedCell F 0) := lt_of_le_of_ne (mass_nonneg hπ _) (Ne.symm hne)
  have hz : ∀ w ∈ informedCell F 0, π w = 0 := by
    intro w hw
    have := h 0 hpos w
    simpa [ind, hw] using this
  exact hne (sum_eq_zero hz)

/-- **Target 2(c).** New Reflection (strong reading) is exactly Reflection of the informed expert.
(⇒) a candidate with a null self-cell would lie in the `π`-null junk cell; at a positive
self-cell fn 12 identifies the cells and the identities. (⇐) a positive-mass informed cell
contains a `π`-support world `w₀`, whose row is a candidate with a positive self-cell by NR-str,
so the cell is `[P = P_{w₀}]` and the identity is NR-str's divided by `ρ(P = ρ)`.
Source: [[Deference Done Better]] §1 ll. 93–99, fn 12; item 039
Kind: P
Fidelity: exact
Hyps: (a) `hπ` -/
theorem informedReflects_iff_newReflects {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} :
    InformedReflects π F ↔ NewReflects π F := by
  constructor
  · intro h ρ hρ
    have hnull := informedReflects_junk_null hπ h
    obtain ⟨w₀, hw₀, rfl⟩ := Frame.mem_cands.1 hρ
    have hpos : 0 < F.selfMass (F.P w₀) := by
      by_contra hnot
      have h0 : F.selfMass (F.P w₀) = 0 :=
        le_antisymm (not_lt.1 hnot) (mass_nonneg (F.P_nonneg w₀) _)
      have hmem : w₀ ∈ informedCell F 0 := by
        rw [mem_informedCell, informed_eq_zero_iff F (F.P_nonneg w₀)]; exact h0
      have := eq_zero_of_mass_eq_zero hπ hnull hmem
      linarith
    refine ⟨hpos, fun w => ?_⟩
    have hcell := informedCell_informed F hpos
    have hm : 0 < mass π (F.cell (F.P w₀)) := (F.mem_cands_iff_mass_cell_pos hπ).1 hρ
    have hid := h (F.informed (F.P w₀)) (by rw [hcell]; exact hm) w
    rw [hcell] at hid
    by_cases hw : F.P w = F.P w₀
    · have hind : ind (F.cell (F.P w₀)) w = 1 := by simp [ind, hw]
      rw [hind, mul_one] at hid
      rw [hind, mul_one, mul_one, hid, mul_assoc, F.informed_mul_selfMass hpos hw]
    · have hind : ind (F.cell (F.P w₀)) w = 0 := by simp [ind, hw]
      rw [hind]; ring
  · intro h σ hσ w
    obtain ⟨w₀, hw₀mem, hw₀pos⟩ := (mass_pos_iff hπ).1 hσ
    rw [mem_informedCell] at hw₀mem
    have hρ : F.P w₀ ∈ F.cands π := F.P_mem_cands hw₀pos
    obtain ⟨hpos, hid⟩ := h (F.P w₀) hρ
    have hcell := informedCell_informed F hpos
    rw [hw₀mem] at hcell
    rw [hcell, ← hw₀mem]
    have := hid w
    by_cases hw : F.P w = F.P w₀
    · have hind : ind (F.cell (F.P w₀)) w = 1 := by simp [ind, hw]
      rw [hind, mul_one, mul_one] at this
      rw [hind, mul_one]
      have hims := F.informed_mul_selfMass hpos hw
      apply mul_right_cancel₀ hpos.ne'
      rw [this, mul_assoc, hims]
    · have hind : ind (F.cell (F.P w₀)) w = 0 := by simp [ind, hw]
      rw [hind, mul_zero, F.informed_eq_zero_of_ne hw, mul_zero]

/-- The informed version of New Reflection quantified over distributions `σ ∈ stdSimplex` only —
the reading that cannot see the junk cell.
Source: [[Deference Done Better]] §1 l. 97 (reading)
Kind: D
Fidelity: variant: `σ` restricted to distributions -/
def InformedReflectsSimplex (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ σ ∈ stdSimplex ℝ W, 0 < mass π (informedCell F σ) →
    ∀ w, π w * ind (informedCell F σ) w = mass π (informedCell F σ) * σ w

/-- **Target 2, stretch.** The two readings of the informed version are exactly the two readings
of New Reflection: over distributions `σ` only, it is the vacuous reading NR-vac.
Source: [[Deference Done Better]] §1 l. 97; item 039
Kind: P
Fidelity: exact (NR-vac reading)
Hyps: (a) nonnegativity of `π` -/
theorem informedReflectsSimplex_iff_newReflectsVac {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w)
    {F : Frame W} : InformedReflectsSimplex π F ↔ NewReflectsVac π F := by
  constructor
  · intro h ρ hρ hpos w
    have hρs := F.mem_stdSimplex_of_mem_cands hρ
    have hcell := informedCell_informed F hpos
    have hm : 0 < mass π (F.cell ρ) := (F.mem_cands_iff_mass_cell_pos hπ).1 hρ
    have hid := h (F.informed ρ) (F.informed_mem_stdSimplex hρs.1 hpos) (by rw [hcell]; exact hm) w
    rw [hcell] at hid
    by_cases hw : F.P w = ρ
    · have hind : ind (F.cell ρ) w = 1 := by simp [ind, hw]
      rw [hind, mul_one] at hid
      rw [hind, mul_one, mul_one, hid, mul_assoc, F.informed_mul_selfMass hpos hw]
    · have hind : ind (F.cell ρ) w = 0 := by simp [ind, hw]
      rw [hind]; ring
  · intro h σ hσs hσ w
    obtain ⟨w₀, hw₀mem, hw₀pos⟩ := (mass_pos_iff hπ).1 hσ
    rw [mem_informedCell] at hw₀mem
    have hρ : F.P w₀ ∈ F.cands π := F.P_mem_cands hw₀pos
    have hpos : 0 < F.selfMass (F.P w₀) := by
      by_contra hnot
      have h0 : F.selfMass (F.P w₀) = 0 :=
        le_antisymm (not_lt.1 hnot) (mass_nonneg (F.P_nonneg w₀) _)
      have hz := (informed_eq_zero_iff F (F.P_nonneg w₀)).2 h0
      rw [hz] at hw₀mem
      have := hσs.2
      rw [← hw₀mem] at this
      simp at this
    have hid := h (F.P w₀) hρ hpos
    have hcell := informedCell_informed F hpos
    rw [hw₀mem] at hcell
    rw [hcell, ← hw₀mem]
    have := hid w
    by_cases hw : F.P w = F.P w₀
    · have hind : ind (F.cell (F.P w₀)) w = 1 := by simp [ind, hw]
      rw [hind, mul_one, mul_one] at this
      rw [hind, mul_one]
      have hims := F.informed_mul_selfMass hpos hw
      apply mul_right_cancel₀ hpos.ne'
      rw [this, mul_assoc, hims]
    · have hind : ind (F.cell (F.P w₀)) w = 0 := by simp [ind, hw]
      rw [hind, mul_zero, F.informed_eq_zero_of_ne hw, mul_zero]

/-! ## Target 3: Reflection ⟹ Value; on immodest frames Reflection ⟺ Value -/

/-- **Target 3(i), fn 16.** Reflection implies Value, directly: for a recommended `S` and an
option `o`, group `E_π(S)` by candidate cells; on the cell of `ρ` the strategy is constant
(cell constraint), `ρ` is supported on its cell (Target 1), and Reflection gives
`∑_{w ∈ [P = ρ]} π w · S_w(w) = π(P = ρ) · E_ρ(S_ρ) ≥ π(P = ρ) · E_ρ(o) = ∑_{w ∈ [P = ρ]} π w · o w`.
Not via the cycle.
Source: [[Deference Done Better]] §1 l. 128, fn 16
Kind: P
Fidelity: exact
Hyps: (a) `hπ` -/
theorem value_of_reflects {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} (h : Reflects π F) :
    Value π F := by
  intro 𝒪 _ S hS o ho
  rw [stratValue_eq_E]
  unfold E
  have e := sum_mul_eq_sum_cands F hπ (fun w => S w w)
  rw [sum_mul_eq_sum_cands F hπ o, e]
  apply sum_le_sum
  intro ρ hρ
  obtain ⟨w₀, _, hPw₀⟩ := Frame.mem_cands.1 hρ
  have hSc : ∀ w ∈ F.cell ρ, S w = S w₀ := fun w hw =>
    hS.cell ((Frame.mem_cell.1 hw).trans hPw₀.symm)
  have e1 : ∑ w ∈ F.cell ρ, π w * S w w = ∑ w ∈ F.cell ρ, π w * S w₀ w :=
    sum_congr rfl fun w hw => by rw [hSc w hw]
  rw [e1, reflects_cell_sum hπ h hρ, reflects_cell_sum hπ h hρ]
  apply mul_le_mul_of_nonneg_left _ (mass_nonneg hπ _)
  rw [← hPw₀]
  exact hS.le w₀ ho

/-- **Target 3(ii), fn 17.** When every candidate of `π` is immodest, Reflection and Value
coincide: (⇒) is Target 3(i); (⇐) Value gives New Reflection (`Value.newReflects`), which on
immodest candidates is Reflection.
Source: [[Deference Done Better]] §1 l. 128, fn 17
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` -/
theorem reflects_iff_value_of_immodest {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (himm : ∀ ρ ∈ F.cands π, F.selfMass ρ = 1) : Reflects π F ↔ Value π F :=
  ⟨value_of_reflects hπ.1, fun h =>
    (reflects_iff_newReflects_of_immodest hπ.1 himm).2 (h.newReflects hπ)⟩

/-- **Fn 17, whole-frame form.** On an immodest frame, Reflection ⟺ Value.
Source: [[Deference Done Better]] §1 l. 128, fn 17
Kind: C
Fidelity: exact
Hyps: (a) `hπ` -/
theorem reflects_iff_value_of_immodestFrame {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (hF : F.Immodest) : Reflects π F ↔ Value π F :=
  reflects_iff_value_of_immodest hπ (immodest_cands hF π)

/-! ## Target 4: Value ⟹ New Reflection by fn 19's conditional bet -/

/-- Fn 19's conditional bet on `q` at the cell of `ρ` with stake `t`: pays `1 − t` on
`q ∧ [P = ρ]`, `−t` on `¬q ∧ [P = ρ]`, `0` off the cell.
Source: [[Deference Done Better]] fn 19
Kind: D
Fidelity: exact -/
def condBet (F : Frame W) (ρ : W → ℝ) (q : Finset W) (t : ℝ) : W → ℝ :=
  fun w => if F.P w = ρ then (if w ∈ q then 1 - t else -t) else 0

/-- The conditional bet vanishes off the cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condBet_eq_zero_of_ne (F : Frame W) (ρ : W → ℝ) (q : Finset W) (t : ℝ) {w : W}
    (hw : F.P w ≠ ρ) : condBet F ρ q t w = 0 := by
  simp [condBet, hw]

/-- The cell sum of the conditional bet under any weights: `σ(q ∧ [P = ρ]) − t · σ(P = ρ)`.
Source: [[Deference Done Better]] fn 19 (the two evaluations)
Kind: L
Fidelity: n/a -/
theorem sum_cell_condBet (F : Frame W) (ρ σ : W → ℝ) (q : Finset W) (t : ℝ) :
    ∑ w ∈ F.cell ρ, σ w * condBet F ρ q t w =
      mass σ (q ∩ F.cell ρ) - t * mass σ (F.cell ρ) := by
  have : ∀ w ∈ F.cell ρ, σ w * condBet F ρ q t w =
      (if w ∈ q then σ w else 0) - t * σ w := by
    intro w hw
    rw [Frame.mem_cell] at hw
    simp only [condBet, hw, if_true]
    split_ifs <;> ring
  rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, mass, mass, inter_comm, ← sum_ite_mem]

/-- The expectation of the conditional bet: `E_σ(O₁) = σ(q ∧ [P = ρ]) − t · σ(P = ρ)`.
Source: [[Deference Done Better]] fn 19
Kind: L
Fidelity: n/a -/
theorem E_condBet (F : Frame W) (ρ σ : W → ℝ) (q : Finset W) (t : ℝ) :
    E σ (condBet F ρ q t) = mass σ (q ∩ F.cell ρ) - t * mass σ (F.cell ρ) := by
  rw [E_eq_sum_of_support (q := F.cell ρ), sum_cell_condBet]
  intro w hw
  exact condBet_eq_zero_of_ne F ρ q t (fun e => hw (Frame.mem_cell.2 e))

/-- **Target 4, fn 19's case.** Value implies New Reflection in the vacuous reading, by the
paper's own construction: if the identity fails at a candidate `ρ` with `0 < ρ(P = ρ)` at a world
`w` of its cell, then for `q = {w}` or `q = [P = ρ] \ {w}` we have `π(q | P = ρ) < t < ρ(q | P = ρ)`
for some real `t`; the frame recommends fn 19's conditional bet `O₁` against `const 0`
(`E_ρ(O₁) > 0`, and the bet is `0` off the cell), while `E_π(S) = π(q ∧ [P = ρ]) − t · π(P = ρ) < 0
= E_π(const 0)`.
Source: [[Deference Done Better]] §1 l. 133, fn 19; item 042
Kind: P
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` -/
theorem newReflectsVac_of_value {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : Value π F) : NewReflectsVac π F := by
  intro ρ hρ hpos w
  have hm : 0 < mass π (F.cell ρ) := (F.mem_cands_iff_mass_cell_pos hπ.1).1 hρ
  have hρs := F.mem_stdSimplex_of_mem_cands hρ
  by_cases hw : F.P w = ρ
  swap
  · simp [ind, hw]
  have hind : ind (F.cell ρ) w = 1 := by simp [ind, hw]
  rw [hind, mul_one, mul_one]
  by_contra hne
  have hwc : w ∈ F.cell ρ := Frame.mem_cell.2 hw
  -- a proposition `q ⊆ [P = ρ]` on which `π(q | P = ρ) < ρ(q | P = ρ)`
  have key : ∃ q : Finset W, q ⊆ F.cell ρ ∧
      mass π q * F.selfMass ρ < mass ρ q * mass π (F.cell ρ) := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨{w}, singleton_subset_iff.2 hwc, ?_⟩
      rw [mass_singleton, mass_singleton, mul_comm (ρ w)]
      exact hlt
    · refine ⟨F.cell ρ \ {w}, sdiff_subset, ?_⟩
      have h1 := mass_inter_add_mass_sdiff π (F.cell ρ) {w}
      have h2 := mass_inter_add_mass_sdiff ρ (F.cell ρ) {w}
      have hi : F.cell ρ ∩ {w} = {w} := inter_eq_right.2 (singleton_subset_iff.2 hwc)
      rw [hi, mass_singleton] at h1 h2
      unfold Frame.selfMass at hgt ⊢
      have ha : mass π (F.cell ρ \ {w}) = mass π (F.cell ρ) - π w := by linarith
      have hb : mass ρ (F.cell ρ \ {w}) = mass ρ (F.cell ρ) - ρ w := by linarith
      rw [ha, hb]
      nlinarith [hgt]
  obtain ⟨q, hq, hlt⟩ := key
  have hqc : q ∩ F.cell ρ = q := inter_eq_left.2 hq
  have hdiv : mass π q / mass π (F.cell ρ) < mass ρ q / F.selfMass ρ := by
    rw [div_lt_div_iff₀ hm hpos]; exact hlt
  obtain ⟨t, ht1, ht2⟩ := exists_between hdiv
  rw [div_lt_iff₀ hm] at ht1
  rw [lt_div_iff₀ hpos] at ht2
  set O := condBet F ρ q t with hO
  have hEρ : 0 < E ρ O := by
    rw [hO, E_condBet, hqc]
    unfold Frame.selfMass at ht2
    linarith
  have hval := h {O, fun _ => 0} (insert_nonempty _ _) _ (F.twoOption_recommended O 0)
    (fun _ => 0) (by simp)
  rw [E_const hπ] at hval
  have hsv := stratValue_twoOption hπ F O 0
  have hsum : ∑ v, π v * (O v - 0) * (if (0 : ℝ) ≤ E (F.P v) O then 1 else 0) =
      mass π q - t * mass π (F.cell ρ) := by
    have hs := sum_cell_condBet F ρ π q t
    rw [hqc] at hs
    rw [← hs, ← sum_subset (subset_univ (F.cell ρ))]
    · apply sum_congr rfl
      intro v hv
      rw [Frame.mem_cell] at hv
      rw [hv, if_pos hEρ.le]
      ring
    · intro v _ hv
      rw [Frame.mem_cell] at hv
      rw [hO, condBet_eq_zero_of_ne F ρ q t hv]
      ring
  rw [hsum] at hsv
  linarith

/-- **Target 4, the null-self-cell case as a bet.** Under Value every candidate has a positive
self-cell: otherwise the bet `−𝟙[P = ρ]` against `const 0` is recommended everywhere on the cell
(`E_ρ(−𝟙[P = ρ]) = −ρ(P = ρ) = 0`), yet costs `π` exactly `π(P = ρ) > 0`. (The argument of
`TotalTrust.selfMass_pos`, run as a Value failure.)
Source: [[Deference Done Better]] fn 19 (presupposition `P_w(q | P = P_w)` defined); item 042
Kind: P
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` -/
theorem selfMass_pos_of_value {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : Value π F) {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) : 0 < F.selfMass ρ := by
  have hm : 0 < mass π (F.cell ρ) := (F.mem_cands_iff_mass_cell_pos hπ.1).1 hρ
  have hρs := F.mem_stdSimplex_of_mem_cands hρ
  by_contra hnot
  have h0 : F.selfMass ρ = 0 := le_antisymm (not_lt.1 hnot) (mass_nonneg hρs.1 _)
  set X : W → ℝ := -(ind (F.cell ρ)) with hX
  have hval := h {X, fun _ => 0} (insert_nonempty _ _) _ (F.twoOption_recommended X 0)
    (fun _ => 0) (by simp)
  rw [E_const hπ] at hval
  have hsv := stratValue_twoOption hπ F X 0
  have hEρ : E ρ X = 0 := by
    rw [hX, E_neg_right, E_ind]
    unfold Frame.selfMass at h0
    rw [h0, neg_zero]
  have hsum : ∑ v, π v * (X v - 0) * (if (0 : ℝ) ≤ E (F.P v) X then 1 else 0) =
      -(mass π (F.cell ρ)) := by
    rw [mass, ← sum_neg_distrib, ← sum_subset (subset_univ (F.cell ρ))]
    · apply sum_congr rfl
      intro v hv
      have hv' := Frame.mem_cell.1 hv
      have hXv : X v = -1 := by simp [hX, ind, hv']
      rw [hv', if_pos hEρ.ge, hXv]
      ring
    · intro v _ hv
      have hv' : F.P v ≠ ρ := fun e => hv (Frame.mem_cell.2 e)
      have hXv : X v = 0 := by simp [hX, ind, hv']
      rw [hXv]
      ring
  rw [hsum] at hsv
  linarith

/-- **Target 4.** Value implies New Reflection in the strong reading, directly: positive
self-cells by `selfMass_pos_of_value`, the identity by `newReflectsVac_of_value`. Both halves
are bets, not the cycle (`Value.newReflects` in `lit-ddb-frames` is the same statement through
Theorem 7.6).
Source: [[Deference Done Better]] §1 l. 133, fn 19; item 042
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` -/
theorem newReflects_of_value_direct {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : Value π F) : NewReflects π F := fun ρ hρ =>
  ⟨selfMass_pos_of_value hπ h hρ, newReflectsVac_of_value hπ h ρ hρ (selfMass_pos_of_value hπ h hρ)⟩

/-- **What the all-`σ` reading adds, exactly.** `InformedReflects` (all vectors `σ`) is the
distributions-only reading plus the junk cell `[P̂ = 0]` being `π`-null — nothing else, since a
non-distribution `σ ≠ 0` has an empty informed cell. So the "exact (all-`σ` reading)" fidelity of
`informedReflects_iff_newReflects` is a theorem, not a hedge (findings F7).
Source: [[Deference Done Better]] fn 12; [[lit-ddb-facts-audit-r2-adversarial]] Q2 (copied)
Kind: P
Fidelity: n/a
Hyps: (a) nonnegativity of `π` -/
theorem informedReflects_iff_simplex_and_junk {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} :
    InformedReflects π F ↔ InformedReflectsSimplex π F ∧ mass π (informedCell F 0) = 0 := by
  constructor
  · intro h
    exact ⟨fun σ _ hσ w => h σ hσ w, informedReflects_junk_null hπ h⟩
  · rintro ⟨h, hjunk⟩ σ hσ w
    obtain ⟨w₀, hw₀mem, hw₀pos⟩ := (mass_pos_iff hπ).1 hσ
    rw [mem_informedCell] at hw₀mem
    have hpos : 0 < F.selfMass (F.P w₀) := by
      by_contra hnot
      have h0 : F.selfMass (F.P w₀) = 0 :=
        le_antisymm (not_lt.1 hnot) (mass_nonneg (F.P_nonneg w₀) _)
      have hmem : w₀ ∈ informedCell F 0 := by
        rw [mem_informedCell, informed_eq_zero_iff F (F.P_nonneg w₀)]; exact h0
      have := eq_zero_of_mass_eq_zero hπ hjunk hmem
      linarith
    have hσs : σ ∈ stdSimplex ℝ W := by
      rw [← hw₀mem]
      exact F.informed_mem_stdSimplex (F.P_nonneg w₀) hpos
    exact h σ hσs hσ w

end

end Cleanroom.Lit.LitDdbFacts
