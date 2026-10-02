import Cleanroom.Corrigibility.CorrReflectFrames.Legit
import Cleanroom.Corrigibility.CorrReflectFrames.Selection

/-!
# corr-reflect-frames — T8: minimal viability and legitimizing world events

miri I5.2: for the agent's own transition (a Bayesian refinement, hence value-reflective for
every `φ`), an event `L` is minimally viable for `φ` iff `L` and `φ` are independent
*conditional on the cell partition* `σ(P(φ | O))` — `legitimizingVal_iff_condIndep_cells`,
stated for every value-reflective frame. The source's `L ⊥ φ | O` (conditional independence
given the observation) is sufficient (`legitimizingVal_of_condIndep_fibres`) but not necessary
when two observations announce the same value (finding 2-007; witness in `Witnesses.lean`).
Every `σ(O)`-event is viable; "the sensor reported correctly" is not (witness). The
legitimizing / delegitimizing world events of miri I6.3 are the Blackwell order on the two
conditional experiments (`LegitimizingEvent`, `DelegitimizingEvent`); miri I6.4 is recorded in
findings, not as a theorem. "I will believe `ρ`" is `σ(O)`-measurable for candidate rows
(`cell_condRow`; null-fibre rows are `δ_w`, caveat in the docstring).
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W] {π : W → ℝ}

/-- **Minimal viability is conditional independence given the cell partition.** For a frame
that is value-reflective for `φ` (every Bayesian refinement is), `L` is legitimizing for `φ` iff
in every cell `C_c`, `π(φ ∩ L ∩ C_c) · π(C_c) = π(φ ∩ C_c) · π(L ∩ C_c)` — `L ⊥ φ` conditional
on `σ(P_{t₂}(φ))`.
Source: [[miri]] I5.2 l. 143 (corrected: cells of `P(φ | O)` in place of `O`); mandate T8(a)
Kind: L
Fidelity: variant: conditional independence given the *cell partition*, the iff the note needs
(its `L ⊥ φ | O` is sufficient, not necessary — findings, corr-wf13-2-007). Under `hV` the
right-hand side is the defining identity times `π(C_c)`, so this is a restatement (L); the
content of T8(a) is the choice of partition, `legitimizingVal_of_condIndep_fibres`, and the
two-observation witness `Witnesses.twoObs_legit_not_condIndep`
Hyps: (a) `∀ w, 0 ≤ π w`, value-form reflection for `φ` (derived for refinements) -/
theorem legitimizingVal_iff_condIndep_cells (hπ : ∀ w, 0 ≤ π w) {F : Frame W} {φ : Finset W}
    (hV : ValueReflectsOn π F φ) (L : Finset W) :
    LegitimizingVal π F φ L ↔ ∀ c, mass π (φ ∩ L ∩ valCell F φ c) * mass π (valCell F φ c) =
      mass π (φ ∩ valCell F φ c) * mass π (L ∩ valCell F φ c) := by
  constructor
  · intro h c
    rw [h c, hV c]; ring
  · intro h c
    by_cases hC : 0 < mass π (valCell F φ c)
    · have := h c
      rw [hV c] at this
      have e : mass π (φ ∩ L ∩ valCell F φ c) * mass π (valCell F φ c) =
          (c * mass π (L ∩ valCell F φ c)) * mass π (valCell F φ c) := by rw [this]; ring
      exact mul_right_cancel₀ hC.ne' e
    · have h0 : mass π (valCell F φ c) = 0 := le_antisymm (not_lt.1 hC) (mass_nonneg hπ _)
      have h1 : mass π (L ∩ valCell F φ c) = 0 :=
        le_antisymm (h0 ▸ mass_mono hπ inter_subset_right) (mass_nonneg hπ _)
      have h2 : mass π (φ ∩ L ∩ valCell F φ c) = 0 :=
        le_antisymm (h0 ▸ mass_mono hπ inter_subset_right) (mass_nonneg hπ _)
      rw [h1, h2, mul_zero]

/-! ## The refinement frame: cells are unions of fibres -/

variable {O : Type} [DecidableEq O]

/-- On a positive fibre of the refinement frame, the announced value of `φ` is the conditional
probability in product form: `P_w(φ) · π(fibre) = π(φ ∩ fibre)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condRow_mass_mul {o : W → O} {w : W} (h : 0 < mass π (fibre o w)) (φ : Finset W) :
    mass (condRow π o w) φ * mass π (fibre o w) = mass π (φ ∩ fibre o w) := by
  show (∑ v ∈ φ, condRow π o w v) * mass π (fibre o w) = ∑ v ∈ φ ∩ fibre o w, π v
  rw [← filter_mem_eq_inter, sum_filter, sum_mul]
  apply sum_congr rfl
  intro v _
  rw [condRow_apply_of_pos h]
  simp only [ind]
  split_ifs
  · rw [one_mul, div_mul_cancel₀ _ h.ne']
  · simp

/-- **Sufficiency of `L ⊥ φ | O`.** If `L` and `φ` are independent conditional on every
observation fibre — `π(φ ∩ L ∩ f_o) · π(f_o) = π(φ ∩ f_o) · π(L ∩ f_o)` — then `L` is
legitimizing for `φ` toward the agent's own refinement: a cell of announced value `c` is a
union of fibres on each of which `π(φ ∩ L ∩ f) = c · π(L ∩ f)`.
Source: [[miri]] I5.2 l. 143 ("`L` is minimally viable iff `L ⊥ φ | O`" — the `⇐` half)
Kind: P
Fidelity: exact for the `⇐` half; the `⇒` half is false (findings, 2-007)
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem legitimizingVal_of_condIndep_fibres (hπ : ∀ w, 0 ≤ π w) (o : W → O) (φ L : Finset W)
    (h : ∀ w, mass π (φ ∩ L ∩ fibre o w) * mass π (fibre o w) =
      mass π (φ ∩ fibre o w) * mass π (L ∩ fibre o w)) :
    LegitimizingVal π (refineFrame π hπ o) φ L := by
  intro c
  -- both sides are sums over the fibres inside the cell; group by `o`
  have hmaps : ∀ w ∈ (univ : Finset W), o w ∈ univ.image o := fun w _ => mem_image_of_mem _ (mem_univ w)
  have key : ∀ (A : Finset W), mass π (A ∩ valCell (refineFrame π hπ o) φ c) =
      ∑ x ∈ univ.image o, ∑ w ∈ univ.filter (fun w => o w = x),
        (if w ∈ A ∩ valCell (refineFrame π hπ o) φ c then π w else 0) := by
    intro A
    rw [sum_fiberwise_of_maps_to hmaps, sum_ite_mem, univ_inter]
    rfl
  rw [key, key, mul_sum]
  apply sum_congr rfl
  intro x hx
  obtain ⟨w₀, _, rfl⟩ := mem_image.1 hx
  -- the fibre of `w₀`
  have hfib : univ.filter (fun w => o w = o w₀) = fibre o w₀ := rfl
  rw [hfib]
  by_cases hpos : 0 < mass π (fibre o w₀)
  · -- on a positive fibre all rows agree; the fibre is inside or outside the cell
    have hrow : ∀ w ∈ fibre o w₀, (refineFrame π hπ o).P w = condRow π o w₀ :=
      fun w hw => condRow_eq_of_mem hpos hw
    by_cases hc : mass (condRow π o w₀) φ = c
    · have hin : ∀ w ∈ fibre o w₀, w ∈ valCell (refineFrame π hπ o) φ c := by
        intro w hw; rw [mem_valCell, hrow w hw]; exact hc
      have e : ∀ (A : Finset W), ∑ w ∈ fibre o w₀,
          (if w ∈ A ∩ valCell (refineFrame π hπ o) φ c then π w else 0) =
            mass π (A ∩ fibre o w₀) := by
        intro A
        rw [← sum_filter, filter_mem_eq_inter]
        show _ = ∑ w ∈ A ∩ fibre o w₀, π w
        apply sum_congr _ (fun _ _ => rfl)
        ext w
        simp only [mem_inter]
        constructor
        · rintro ⟨hw, hA, _⟩; exact ⟨hA, hw⟩
        · rintro ⟨hA, hw⟩; exact ⟨hw, hA, hin w hw⟩
      rw [e, e]
      have hcm := condRow_mass_mul hpos φ
      rw [hc] at hcm
      have hL := h w₀
      -- π(φ ∩ L ∩ f) · π(f) = π(φ ∩ f) · π(L ∩ f) = c · π(f) · π(L ∩ f)
      rw [← hcm] at hL
      have : mass π (φ ∩ L ∩ fibre o w₀) * mass π (fibre o w₀) =
          (c * mass π (L ∩ fibre o w₀)) * mass π (fibre o w₀) := by rw [hL]; ring
      exact mul_right_cancel₀ hpos.ne' this
    · have hout : ∀ w ∈ fibre o w₀, w ∉ valCell (refineFrame π hπ o) φ c := by
        intro w hw; rw [mem_valCell, hrow w hw]; exact hc
      have e : ∀ (A : Finset W), ∑ w ∈ fibre o w₀,
          (if w ∈ A ∩ valCell (refineFrame π hπ o) φ c then π w else 0) = 0 := by
        intro A
        apply sum_eq_zero
        intro w hw
        rw [if_neg]
        rw [mem_inter]; exact fun h' => hout w hw h'.2
      rw [e, e, mul_zero]
  · -- a null fibre contributes nothing
    have hz : ∀ w ∈ fibre o w₀, π w = 0 := by
      intro w hw
      have h0 : mass π (fibre o w₀) = 0 := le_antisymm (not_lt.1 hpos) (mass_nonneg hπ _)
      exact eq_zero_of_mass_eq_zero hπ h0 hw
    have e : ∀ (A : Finset W), ∑ w ∈ fibre o w₀,
        (if w ∈ A ∩ valCell (refineFrame π hπ o) φ c then π w else 0) = 0 := by
      intro A
      apply sum_eq_zero
      intro w hw
      rw [hz w hw]; simp
    rw [e, e, mul_zero]

/-- **Every `σ(O)`-event is minimally viable** for the agent's own refinement: for `L = o⁻¹ T`
each fibre lies inside or outside `L`, so `L ⊥ φ | O` holds trivially.
Source: [[miri]] I5.2 l. 143 ("Trivially viable: any `L ∈ σ(O)`")
Kind: L
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem legitimizingVal_preimage (hπ : ∀ w, 0 ≤ π w) (o : W → O) (φ : Finset W) (T : Finset O) :
    LegitimizingVal π (refineFrame π hπ o) φ (univ.filter (fun w => o w ∈ T)) := by
  apply legitimizingVal_of_condIndep_fibres hπ o
  intro w
  by_cases hw : o w ∈ T
  · have e1 : φ ∩ univ.filter (fun v => o v ∈ T) ∩ fibre o w = φ ∩ fibre o w := by
      ext v; simp only [mem_inter, mem_filter, mem_univ, true_and, mem_fibre]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [h3]; exact hw⟩, h3⟩
    have e2 : univ.filter (fun v => o v ∈ T) ∩ fibre o w = fibre o w := by
      ext v; simp only [mem_inter, mem_filter, mem_univ, true_and, mem_fibre]
      constructor
      · rintro ⟨_, h3⟩; exact h3
      · intro h3; exact ⟨by rw [h3]; exact hw, h3⟩
    rw [e1, e2]
  · have e1 : φ ∩ univ.filter (fun v => o v ∈ T) ∩ fibre o w = ∅ := by
      ext v; simp only [mem_inter, mem_filter, mem_univ, true_and, mem_fibre, notMem_empty,
        iff_false, not_and]
      rintro ⟨_, h2⟩ h3; rw [h3] at h2; exact hw h2
    have e2 : univ.filter (fun v => o v ∈ T) ∩ fibre o w = ∅ := by
      ext v; simp only [mem_inter, mem_filter, mem_univ, true_and, mem_fibre, notMem_empty,
        iff_false, not_and]
      intro h2 h3; rw [h3] at h2; exact hw h2
    rw [e1, e2]; simp [mass]

/-! ## Legitimizing and delegitimizing world events (miri I6.3) -/

/-- **A legitimizing world event** (miri I6.3): given the two conditional experiments `kE`
(the true sensor given `E`) and `kNE` (given `¬E`), `E` is legitimizing when the sensor given
`E` is at least as informative — `kNE` is a garbling of `kE` (Blackwell order,
`lit-ddb-frames`' `BlackwellLE`, first argument the less informative).
Source: [[miri]] I6.3 l. 157; mandate T8(c) (the definition `corr-general-object` imports)
Kind: D
Fidelity: exact -/
def LegitimizingEvent {Ω S : Type} [Fintype S] (kE kNE : Blackwell.Experiment Ω S) : Prop :=
  Blackwell.BlackwellLE kNE kE

/-- **A delegitimizing world event** (miri I6.3): the sensor given `E` is a garbling of the
sensor given `¬E`.
Source: [[miri]] I6.3 l. 157
Kind: D
Fidelity: exact -/
def DelegitimizingEvent {Ω S : Type} [Fintype S] (kE kNE : Blackwell.Experiment Ω S) : Prop :=
  Blackwell.BlackwellLE kE kNE

/-- Strictly legitimizing: strictly more informative given `E`.
Source: [[miri]] I6.1 l. 153 ("delegitimizing relative to … iff the garbling is strict")
Kind: D
Fidelity: exact -/
def StrictlyLegitimizingEvent {Ω S : Type} [Fintype S] (kE kNE : Blackwell.Experiment Ω S) :
    Prop :=
  Blackwell.BlackwellLT kNE kE

/-- Strictly delegitimizing: strictly less informative given `E`.
Source: [[miri]] I6.1 l. 153
Kind: D
Fidelity: exact -/
def StrictlyDelegitimizingEvent {Ω S : Type} [Fintype S] (kE kNE : Blackwell.Experiment Ω S) :
    Prop :=
  Blackwell.BlackwellLT kE kNE

/-- **"I will believe `ρ`" is a `σ(O)`-event** (miri I7.2, 2-010) for every candidate row of
the agent's own refinement: the cell of a positive-fibre row is its fibre. (Rows on `π`-null
fibres are the junk `δ_w` and their cells are not fibres; candidates never sit there.)
Source: [[miri]] I7.2 l. 165; corr-wf13-2-010
Kind: L
Fidelity: exact for candidate rows (null-fibre caveat in the docstring)
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem cell_refineFrame_eq_fibre (hπ : ∀ w, 0 ≤ π w) (o : W → O) {ρ : W → ℝ}
    (hρ : ρ ∈ (refineFrame π hπ o).cands π) :
    ∃ w₀, 0 < π w₀ ∧ (refineFrame π hπ o).cell ρ = fibre o w₀ := by
  obtain ⟨w₀, hw₀, rfl⟩ := Frame.mem_cands.1 hρ
  exact ⟨w₀, hw₀, cell_condRow hπ (mass_fibre_pos_of_pos hπ hw₀)⟩

end

end Cleanroom.Corrigibility.CorrReflectFrames
