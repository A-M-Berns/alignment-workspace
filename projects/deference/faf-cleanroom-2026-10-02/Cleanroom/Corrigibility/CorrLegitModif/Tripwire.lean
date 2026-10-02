import Cleanroom.Corrigibility.CorrLegitModif.Plumbing
import Cleanroom.Corrigibility.CorrReflectFrames.Collapse

/-!
# corr-legit-modif — T6: the tripwire as a pre-declared-false `L`

[[anthropic-davis]] item 4 l. 69: "'If Claude ever finds itself reasoning towards such actions …
it should treat this as a strong signal that it has been compromised' is
`P_t(compromised | P_{t+1}(φ) high)` high for specified `φ` — i.e. `L_{t,t+1,φ}` pre-declared
false." `tripwire F Φ θ` is the legitimacy event excluding every successor confident (`≥ θ`) in a
forbidden `φ ∈ Φ`. (i) membership; (ii) under the criterion with `L = tripwire` a confident
candidate's cell has zero restricted mass — the criterion constrains nothing there and the per-`Q`
rule at `π(L ∩ cell) = 0` is "resist" (`PerQ.perQ_threshold`, cited); (iii) the participation /
stop asymmetry (item 3): two tripwires on one frame, the criterion holding under one (`{1, 2}`,
a refinement cell) and failing under the other (`univ`); (iv) on that witness the tripwire is not a
union of the observation question's cells. Traps: `θ > 1` gives `univ`, `θ ≤ 0` gives `∅`
(`tripwire_univ_of_one_lt`, `tripwire_empty_of_nonpos`).
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames
  Cleanroom.Corrigibility.CorrLegitGeneral

noncomputable section

set_option linter.unusedSectionVars false

variable {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]

/-- **The tripwire event**: the worlds whose successor is confident (`≥ θ`) in no forbidden `φ`.
Source: [[anthropic-davis]] item 4 l. 69 (`L_{t,t+1,φ}` pre-declared false); corr-wf13-2-087
Kind: D
Fidelity: exact -/
def tripwire (F : Frame W) (Φ : Finset (Finset W)) (θ : ℝ) : Finset W :=
  univ.filter (fun w => ∀ φ ∈ Φ, mass (F.P w) φ < θ)

/-- Membership in the tripwire.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_tripwire_iff {F : Frame W} {Φ : Finset (Finset W)} {θ : ℝ} {w : W} :
    w ∈ tripwire F Φ θ ↔ ∀ φ ∈ Φ, mass (F.P w) φ < θ := by
  simp [tripwire]

/-- **A confident candidate's cell is null under the tripwire**: if `w` is confident in some
forbidden `φ`, every world of its cell is (same row), so the deferrer restricted to the tripwire
gives the cell mass `0` — the criterion with `L = tripwire` constrains nothing there.
Source: [[anthropic-davis]] item 4 l. 69; mandate T6(ii)
Kind: L
Fidelity: exact
Hyps: (a) `w ∉ tripwire F Φ θ` -/
theorem tripwire_cell_null (π : W → ℝ) {F : Frame W} {Φ : Finset (Finset W)} {θ : ℝ} {w : W}
    (hw : w ∉ tripwire F Φ θ) : mass (restrict π (tripwire F Φ θ)) (F.cell (F.P w)) = 0 := by
  rw [mass_restrict]
  apply sum_eq_zero
  intro v hv
  rw [mem_inter, Frame.mem_cell] at hv
  exfalso
  apply hw
  rw [mem_tripwire_iff] at hv ⊢
  rw [← hv.1]
  exact hv.2

/-- `θ > 1` disarms the tripwire (every row has mass at most one).
Source: mandate T6 (trap)
Kind: L
Fidelity: n/a -/
theorem tripwire_univ_of_one_lt (F : Frame W) (Φ : Finset (Finset W)) {θ : ℝ} (hθ : 1 < θ) :
    tripwire F Φ θ = univ := by
  ext w
  simp only [mem_tripwire_iff, mem_univ, iff_true]
  intro φ _
  exact lt_of_le_of_lt (mass_le_one (F.P_mem w) φ) hθ

/-- `θ ≤ 0` with a nonempty forbidden set empties the tripwire.
Source: mandate T6 (trap)
Kind: L
Fidelity: n/a -/
theorem tripwire_empty_of_nonpos (F : Frame W) {Φ : Finset (Finset W)} (hΦ : Φ.Nonempty) {θ : ℝ}
    (hθ : θ ≤ 0) : tripwire F Φ θ = ∅ := by
  ext w
  constructor
  · intro hw
    rw [mem_tripwire_iff] at hw
    obtain ⟨φ, hφ⟩ := hΦ
    exact absurd (hw φ hφ) (not_lt.2 (le_trans hθ (mass_nonneg (F.P_mem w).1 φ)))
  · intro hw; simp at hw

/-! ## The participation / stop asymmetry on three worlds -/

/-- The uniform deferrer on three worlds.
Source: mandate T6(iii) (witness)
Kind: D
Fidelity: exact -/
def πtw : Fin 3 → ℝ := fun _ => 1 / 3

/-- The successor frame: at world `0` the row `δ₁` (confident in `{1}`), at worlds `1, 2` the row
`(0, 1/2, 1/2)` (the conditional of the uniform prior on `{1, 2}`).
Source: mandate T6(iii) (witness)
Kind: D
Fidelity: exact -/
def Ftw : Frame (Fin 3) where
  P := fun w => if w = 0 then ![0, 1, 0] else ![0, 1 / 2, 1 / 2]
  P_mem := fun w => by
    rw [mem_stdSimplex_iff]
    split_ifs
    · exact ⟨fun v => by fin_cases v <;> norm_num, by simp [Fin.sum_univ_three]⟩
    · exact ⟨fun v => by fin_cases v <;> norm_num, by simp [Fin.sum_univ_three]; norm_num⟩

/-- The two tripwires: forbidding confidence `≥ 3/4` in `{1}` excludes world `0`
(`tripwire = {1, 2}`); forbidding confidence `≥ 3/4` in `{2}` excludes nothing (`tripwire = univ`).
Source: mandate T6(iii)
Kind: L
Fidelity: exact -/
theorem tripwires_tw :
    tripwire Ftw {({1} : Finset (Fin 3))} (3 / 4) = {1, 2} ∧
    tripwire Ftw {({2} : Finset (Fin 3))} (3 / 4) = univ := by
  constructor <;> ext w <;> fin_cases w <;>
    simp [mem_tripwire_iff, Ftw, mass] <;> norm_num

/-- **The asymmetry (item 3)**: two question-indexed tripwires on one three-world frame with
opposite verdicts. Under the tripwire for `{1}` (forbid confidence `≥ 3/4` in `{1}`) the event is
`{1, 2}` and the global `L`-conditioned criterion holds (the restricted deferrer is the conditional
on `{1, 2}`, a refinement cell, and the one untrusted row `δ₁` at world `0` is excluded — the
one-candidate case); under the tripwire for `{2}` the event is `univ`, nothing is excluded, and the
criterion fails (`X = 𝟙_{1}`, `s = 1`: the cut is world `0` alone, where the deferrer loses `1/3`).
The content is that legitimacy is proposition-indexed, so one frame satisfies the criterion under
one `L_φ` and fails it under another. Which proposition is "stop" and which "participation" is the
source's gloss (anthropic-davis 2.13(a): the stop-proposition is the cheap one to defer on), not
something the Lean distinguishes.
Source: [[anthropic-davis]] item 3 l. 67 (the participation / stop asymmetry); mandate T6(iii)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem tripwire_asymmetry :
    LegitimizingTT πtw Ftw (tripwire Ftw {({1} : Finset (Fin 3))} (3 / 4)) ∧
    ¬ LegitimizingTT πtw Ftw (tripwire Ftw {({2} : Finset (Fin 3))} (3 / 4)) := by
  obtain ⟨h1, h2⟩ := tripwires_tw
  rw [h1, h2]
  constructor
  · unfold LegitimizingTT
    intro X s
    simp only [Fin.sum_univ_three, restrict_apply, Ftw]
    simp [πtw]
    split_ifs <;> simp [E, Fin.sum_univ_three] at * <;> nlinarith
  · intro h
    unfold LegitimizingTT at h
    have := h (ind {1}) 1
    simp +decide [Fin.sum_univ_three, restrict_univ, Ftw, E, ind, πtw] at this
    norm_num at this

/-- **The tripwire is not a union of observation cells**: with the observation question
`O = 𝟙[w ∈ {0, 1}]` the stop-tripwire `{1, 2}` splits the cell `{0, 1}` — one of T7's
`L ∉ σ(O)`.
Source: mandate T6(iv); [[yudkowsky]] C5 l. 84
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem tripwire_not_observation_measurable :
    ∃ w v : Fin 3, questionOf ({0, 1} : Finset (Fin 3)) w = questionOf {0, 1} v ∧
      w ∈ tripwire Ftw {({1} : Finset (Fin 3))} (3 / 4) ∧
      v ∉ tripwire Ftw {({1} : Finset (Fin 3))} (3 / 4) := by
  refine ⟨1, 0, by simp [questionOf], ?_, ?_⟩ <;> rw [tripwires_tw.1] <;> simp

end

end Cleanroom.Corrigibility.CorrLegitModif
