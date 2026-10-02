import Cleanroom.Trust.LegitFiniteDefect.Settlement
import Cleanroom.Trust.LegitFiniteDefect.Trace

/-!
# Audit round 2 (lens: fidelity) — probes for `legit-finite-defect`

Evidence for two claims in `legit-finite-defect-audit-r2-fidelity.md`. Not imported by the
library.

* **P1** — the corrected three-term crossing theorem (`Settlement.Crossing.isGLB_settleGap_crossing`)
  is inhabited by a settlement that is *not* a step function, on which the right-limit term
  `c − s(c⁺)` wins strictly against both the gap at the crossing and the left-limit term, and the
  infimum is **not attained** by any quote. Both shipped witnesses are step functions; on the
  anti-indicator the middle term equals the left one, on `jump` the two one-sided terms coincide.
  This instance shows all three terms doing different work, so the three-term statement is not a
  coincidence of the shipped examples.
* **P3** — the identified-set theorems (`Trace.IdentifiedSet.*`) instantiated on the source's own
  steered system `S2`: its terminal quote equals its terminal opinion (`3/4`), so `D S2 = 3/4`, the
  trace of `S2` is consistent with every defect in `[0, 3/4]` and with none outside — the source's
  computed `d S2 = 1/2` is one interior point of that interval.
-/

namespace Cleanroom.Trust.LegitFiniteDefect.AuditR2Fidelity

open Set Cleanroom.Trust.LegitFiniteDefect.Settlement Cleanroom.Trust.LegitFiniteDefect.Settlement.Crossing

noncomputable section

/-! ## P1: a non-step settlement where the right-limit term wins and nothing attains the GLB -/

/-- `s a = 1 − a/4` for `a < 1/2` (values in `(7/8, 1]`), `s (1/2) = 7/8`, `s a = 1/2 − a/4` for
`a > 1/2` (values in `[1/4, 3/8)`). Antitone, self-mapping, fixed-point-free; crossing `1/2`;
`s(c⁻) = 7/8`, `s(c⁺) = 3/8`; gap at the crossing `3/8`. -/
def ramp : ℝ → ℝ := fun a =>
  if a < 1 / 2 then 1 - a / 4 else if 1 / 2 < a then 1 / 2 - a / 4 else 7 / 8

theorem ramp_antitone : AntitoneOn ramp (Icc 0 1) := by
  intro a _ b _ hab
  unfold ramp
  split_ifs <;> (try simp only [not_lt] at *) <;> linarith

theorem ramp_mapsTo : MapsTo ramp (Icc 0 1) (Icc 0 1) := by
  intro a ha
  unfold ramp
  split_ifs <;> constructor <;> linarith [ha.1, ha.2]

theorem ramp_noFixed : ∀ a ∈ Icc (0 : ℝ) 1, ramp a ≠ a := by
  intro a _ h
  unfold ramp at h
  split_ifs at h with h1 h2
  · linarith
  · linarith
  · simp only [not_lt] at h1 h2
    linarith

theorem ramp_below : below ramp = Icc 0 (1 / 2) := by
  ext a
  simp only [below, ramp, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h0, _⟩, hlt⟩
    split_ifs at hlt with h1 h2
    · exact ⟨h0, h1.le⟩
    · linarith
    · simp only [not_lt] at h1 h2
      exact ⟨h0, h2⟩
  · rintro ⟨h0, hc⟩
    refine ⟨⟨h0, by linarith⟩, ?_⟩
    split_ifs with h1 h2 <;> linarith

theorem ramp_crossing : crossing ramp = 1 / 2 := by
  unfold crossing
  rw [ramp_below]
  exact csSup_Icc (by norm_num)

theorem ramp_image_left : ramp '' Ico 0 (1 / 2) = Ioc (7 / 8) 1 := by
  ext y
  simp only [Set.mem_image, Set.mem_Ico, Set.mem_Ioc]
  constructor
  · rintro ⟨a, ⟨ha0, ha1⟩, rfl⟩
    unfold ramp
    rw [if_pos ha1]
    constructor <;> linarith
  · rintro ⟨hy0, hy1⟩
    refine ⟨4 * (1 - y), ⟨by linarith, by linarith⟩, ?_⟩
    unfold ramp
    rw [if_pos (by linarith)]
    ring

theorem ramp_image_right : ramp '' Ioc (1 / 2) 1 = Ico (1 / 4) (3 / 8) := by
  ext y
  simp only [Set.mem_image, Set.mem_Ioc, Set.mem_Ico]
  constructor
  · rintro ⟨a, ⟨ha0, ha1⟩, rfl⟩
    unfold ramp
    rw [if_neg (not_lt.2 ha0.le), if_pos ha0]
    constructor <;> linarith
  · rintro ⟨hy0, hy1⟩
    refine ⟨2 - 4 * y, ⟨by linarith, by linarith⟩, ?_⟩
    unfold ramp
    rw [if_neg (by linarith), if_pos (by linarith)]
    ring

theorem ramp_leftVal : leftVal ramp = 7 / 8 := by
  unfold leftVal
  rw [ramp_crossing, ramp_image_left]
  exact csInf_Ioc (by norm_num)

theorem ramp_rightVal : rightVal ramp = 3 / 8 := by
  unfold rightVal
  rw [ramp_crossing, ramp_image_right]
  exact csSup_Ico (by norm_num)

theorem ramp_gap_at_crossing : settleGap ramp (1 / 2) = 3 / 8 := by
  unfold settleGap ramp
  norm_num

/-- **P1.** The three terms are `3/8` (gap at the crossing), `3/8` (left) and `1/8` (right); the
GLB is `1/8`; and no quote in `[0, 1]` attains it. -/
theorem ramp_glb_not_attained :
    IsGLB (settleGap ramp '' Icc 0 1) (1 / 8) ∧
      (1 / 8 : ℝ) < settleGap ramp (crossing ramp) ∧
      (1 / 8 : ℝ) < leftVal ramp - crossing ramp ∧
      (1 / 8 : ℝ) = crossing ramp - rightVal ramp ∧
      ∀ a ∈ Icc (0 : ℝ) 1, 1 / 8 < settleGap ramp a := by
  have h := isGLB_settleGap_crossing ramp_antitone ramp_mapsTo ramp_noFixed
    (by rw [ramp_crossing]; norm_num) (by rw [ramp_crossing]; norm_num)
  rw [ramp_crossing, ramp_leftVal, ramp_rightVal, ramp_gap_at_crossing] at h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rwa [show min (3 / 8 : ℝ) (min (7 / 8 - 1 / 2) (1 / 2 - 3 / 8)) = 1 / 8 by norm_num] at h
  · rw [ramp_crossing, ramp_gap_at_crossing]; norm_num
  · rw [ramp_crossing, ramp_leftVal]; norm_num
  · rw [ramp_crossing, ramp_rightVal]; norm_num
  · intro a ha
    unfold settleGap ramp
    split_ifs with h1 h2
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith
    · simp only [not_lt] at h1 h2
      have : a = 1 / 2 := le_antisymm h2 h1
      rw [this]; norm_num

/-! ## P3: the identified set on the source's own steered system -/

open Cleanroom.Trust.LegitFiniteDefect.Trace Cleanroom.Trust.LegitFiniteDefect.Trace.IdentifiedSet

theorem S2_run3 : run S2 3 = 3 / 4 := by norm_num [run, S2, hSteer, quote]

theorem S2_D : D S2 = 3 / 4 := by
  unfold D
  rw [if_pos S2_tracking, S2_run3]
  norm_num

/-- **P3.** The trace of the source's steered system is consistent with every defect in
`[0, 3/4]` and with none outside; the source's `d S2 = 1/2` is an interior point, and the
maximal trace-consistent defect `3/4` is attained by a valid system. -/
theorem S2_identified_set :
    (∀ δ, (∃ S', Valid S' ∧ trace S' = trace S2 ∧ d S' = δ) ↔ 0 ≤ δ ∧ δ ≤ 3 / 4) ∧
      (∃ S', Valid S' ∧ trace S' = trace S2 ∧ d S' = 3 / 4) ∧
      (0 : ℚ) ≤ d S2 ∧ d S2 ≤ 3 / 4 ∧ d S2 = 1 / 2 := by
  have hV : Valid S2 := valid_and_differ.2.1
  refine ⟨fun δ => ?_, ?_, ?_, ?_, d_pair.2⟩
  · rw [defect_consistent_iff hV, S2_D]
  · exact exists_defect_eq hV (by norm_num) (by rw [S2_D])
  · rw [d_pair.2]; norm_num
  · rw [d_pair.2]; norm_num

end

end Cleanroom.Trust.LegitFiniteDefect.AuditR2Fidelity
