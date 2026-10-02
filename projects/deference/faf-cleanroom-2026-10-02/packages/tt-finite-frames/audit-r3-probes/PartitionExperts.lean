import Cleanroom.Trust.TtFiniteFrames.SoftCollapse
import Cleanroom.Trust.TtFiniteFrames.Corr

/-!
# Audit round 3 (fidelity) — probe for `tt-finite-frames`

Evidence file for `run/wp/tt-finite-frames/tt-finite-frames-audit-r3-fidelity.md` (issue N1).
Not imported by the library. Mathlib-only.

**What it shows.** The docstring of `softCM_immodest`, the header of `Witnesses.lean`, the
ledger's I2 Witness cell, F-I2b and the report all say that "for a full-support prior the
inhabitants of `hsoft` are exactly T1's partition experts". The package proves half of that
sentence — `hsoft ↔ ∀ w, CondMartingaleAt π F w` (`softCM_iff_condMartingaleAt_all`) — and
asserts the other half in prose. This probe supplies it: under full support the hard identity at
every world holds iff `F` is `π`'s own partition expert on `F`'s own cells,
`F.P = (Frame.ofPartition π hpos F.P).P` (P1 and P2), so the gap-form hypothesis of
`softCM_immodest` holds iff `F` is such a partition expert (P3). The claim is true; the probe is
the missing Lean statement, offered for the library.
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- P1. Under full support, the hard identity at every world makes `F` the partition expert of
`π` on `F`'s own cells: the map `F.P : W → (W → ℝ)` has fibres `F.cell (F.P w)`, and the identity
at `𝟙_{v}` reads `P_w v · π(cell w) = 𝟙[v ∈ cell w] · π v`. -/
theorem eq_ofPartition_of_condMartingaleAt_all {π : W → ℝ} (hpos : ∀ w, 0 < π w)
    {F : Frame W} (hCM : ∀ w, CondMartingaleAt π F w) :
    F.P = (Frame.ofPartition π hpos F.P).P := by
  funext w v
  rw [Frame.ofPartition_P_apply]
  have hcell : Corr.ofMap F.P w = F.cell (F.P w) := by
    ext u
    simp [Corr.mem_ofMap, Frame.mem_cell]
  rw [hcell]
  have hm : 0 < mass π (F.cell (F.P w)) :=
    mass_pos_of_mem (fun w => (hpos w).le) (F.mem_cell_self w) (hpos w)
  rw [eq_div_iff hm.ne']
  rw [(hCM w).apply_single v]
  simp [Frame.mem_cell]

/-- P2. Conversely, every partition expert of a full-support prior satisfies the hard identity at
every world (its cell at `w` is the fibre of `w`, and `Frame.ofPartition_E` is the identity). -/
theorem condMartingaleAt_all_ofPartition {ι : Type} [DecidableEq ι] {π : W → ℝ}
    (hpos : ∀ w, 0 < π w) (f : W → ι) :
    ∀ w, CondMartingaleAt π (Frame.ofPartition π hpos f) w := by
  intro w X
  rw [Frame.ofPartition_cell]
  exact Frame.ofPartition_E π hpos f w X

/-- The hard identity depends on a frame only through its rows. -/
theorem condMartingaleAt_of_P_eq {π : W → ℝ} {F G : Frame W} (h : F.P = G.P) (w : W)
    (hG : CondMartingaleAt π G w) : CondMartingaleAt π F w := by
  unfold CondMartingaleAt Frame.cell at *
  rw [h]
  exact hG

/-- P3. Under full support, the gap-form hypothesis of `softCM_immodest` holds iff `F` is `π`'s
partition expert on its own cells — the sentence "the inhabitants are exactly T1's partition
experts", as a theorem (any ramp family). -/
theorem softCM_hyp_iff_eq_ofPartition {π : W → ℝ} (hpos : ∀ w, 0 < π w) {F : Frame W}
    {ι : ℝ → ℝ → ℝ → ℝ} (hι : IsRamp ι) :
    (∀ (X : W → ℝ) (t δ : ℝ), 0 < δ → δ < Frame.gap F X →
      ∑ w, π w * X w * ι δ t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * ι δ t (E (F.P w) X)) ↔
    F.P = (Frame.ofPartition π hpos F.P).P := by
  rw [softCM_iff_condMartingaleAt_all hι]
  exact ⟨eq_ofPartition_of_condMartingaleAt_all hpos,
    fun hEq w => condMartingaleAt_of_P_eq hEq w (condMartingaleAt_all_ofPartition hpos F.P w)⟩

end

end Cleanroom.Trust.TtFiniteFrames
