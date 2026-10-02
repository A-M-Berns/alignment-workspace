import Cleanroom.Trust.TtFiniteFrames

/-!
# Audit round 3 (adversarial) — probe: the inhabitants of I2's hypothesis package

The ledger (row `softCM_immodest`, Witness cell), the `SoftCollapse.lean` module docstring and
the report all *assert* that "for a full-support prior the inhabitants of `hsoft` are exactly
T1's partition experts" — a claim made in prose, backed by `softCM_iff_condMartingaleAt_all`
(soft ⟺ hard at every world) and `ofPartition_soft_identity` (partition experts are inhabitants),
but with the missing half — hard at every world ⟹ the frame *is* its prior's own partition expert
on its own cells — nowhere stated. This probe proves that half and the full characterisation:

* `condMartingaleAt_all_iff_ofPartition_self`: under `hpos`,
  `(∀ w, CondMartingaleAt π F w) ↔ F.P = (Frame.ofPartition π hpos F.P).P`;
* `softCM_hyp_iff_ofPartition_self`: hence, for any ramp family, `softCM_immodest`'s `hsoft` holds
  iff `F` is `π`'s partition expert on the partition `w ↦ F.P w` (its own DDB cells).

Not imported by the library. Mathlib-only (imports the package root).
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The DDB cell of `w` is the fibre of the map `F.P` through `w`. -/
theorem cell_eq_ofMap_P [DecidableEq (W → ℝ)] (F : Frame W) (w : W) :
    F.cell (F.P w) = Corr.ofMap F.P w := by
  ext u
  simp [Frame.cell, Corr.ofMap]

/-- `CondMartingaleAt` depends on the frame only through its rows. -/
theorem condMartingaleAt_congr {π : W → ℝ} {F G : Frame W} (h : F.P = G.P) (w : W)
    (hG : CondMartingaleAt π G w) : CondMartingaleAt π F w := by
  intro X
  have := hG X
  unfold Frame.cell at this ⊢
  rw [h]
  exact this

/-- **The hard identity at every world characterises the prior's own partition expert.** Under
full support, `∀ w, CondMartingaleAt π F w` holds iff every row of `F` is `π` conditioned on
`F`'s own DDB cell at that world, i.e. `F.P = (Frame.ofPartition π hpos F.P).P`. -/
theorem condMartingaleAt_all_iff_ofPartition_self [DecidableEq (W → ℝ)] {π : W → ℝ}
    (hpos : ∀ w, 0 < π w) (F : Frame W) :
    (∀ w, CondMartingaleAt π F w) ↔ F.P = (Frame.ofPartition π hpos F.P).P := by
  constructor
  · intro hCM
    funext w v
    rw [Frame.ofPartition_P_apply, ← cell_eq_ofMap_P]
    have hm : 0 < mass π (F.cell (F.P w)) := by
      unfold mass
      exact Finset.sum_pos (fun u _ => hpos u) ⟨w, F.mem_cell_self w⟩
    rw [eq_div_iff hm.ne']
    have h := (hCM w).apply_single v
    rw [h]
    simp [Frame.mem_cell]
  · intro hP w
    have hG : ∀ w, CondMartingaleAt π (Frame.ofPartition π hpos F.P) w :=
      (softCM_iff_condMartingaleAt_all isRamp_hardIndicator).1
        (fun X t δ _ _ => ofPartition_soft_identity hpos F.P
          (fun _ t x => if t < x then (1 : ℝ) else 0) X t δ)
    exact condMartingaleAt_congr hP w (hG w)

/-- **The inhabitants of I2's hypothesis package, under full support, are exactly the partition
experts**: for any ramp family, `softCM_immodest`'s `hsoft` holds iff `F` is `π`'s partition
expert on its own cells. (The ledger's prose claim, as a theorem.) -/
theorem softCM_hyp_iff_ofPartition_self [DecidableEq (W → ℝ)] {π : W → ℝ}
    (hpos : ∀ w, 0 < π w) (F : Frame W) {ι : ℝ → ℝ → ℝ → ℝ} (hι : IsRamp ι) :
    (∀ (X : W → ℝ) (t δ : ℝ), 0 < δ → δ < Frame.gap F X →
      ∑ w, π w * X w * ι δ t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * ι δ t (E (F.P w) X)) ↔
    F.P = (Frame.ofPartition π hpos F.P).P :=
  (softCM_iff_condMartingaleAt_all hι).trans (condMartingaleAt_all_iff_ofPartition_self hpos F)

end

end Cleanroom.Trust.TtFiniteFrames
