import Cleanroom.Trust.LegitFiniteDefect

/-!
# Audit round 2 (adversarial) — probes for `legit-finite-defect`

Not imported by the library. Elaborated with `scripts/lean-check`. Each probe is evidence for a
line of the audit `legit-finite-defect-audit-r2-adversarial.md`; none is a counterexample to a
package theorem.

* P1 — the crossing theorem's one-sided terms are genuine distances: under its hypotheses
  `crossing s ≤ leftVal s` and `rightVal s ≤ crossing s`, so no negative junk term can win the
  three-way `min`.
* P2 — the mandate's two-term formula is *recovered* under the extra hypothesis
  `s c = s(c⁻)` (left-continuity at the crossing): F15 is a missing-hypothesis error, and the
  anti-indicator (where `s c = 1 = s(c⁻)`) is exactly the case where it went unnoticed.
* P3 — the interiority hypothesis of `IdentifiedSet.exists_steered` is load-bearing: a valid
  trace with terminal opinion `0` and a positive terminal quote *does* identify legitimacy
  (`D = 0`, every trace-consistent valid system has defect `0`).
* P4 — `Mechanism.totalTrust_clean` is not automatic for clean-supported priors: the
  clean-supported distribution `(1/2, 0, 0, 1/2)` (all mass on `(lo, 0)` and `(hi, 1)`) fails
  Total Trust at `X = 𝟙{world 1}`, `s = 1/4`, so the hull weights `½ρlo + ½ρhi` are doing work.
* P5 — `Residue.regime_iff`'s `0 < B` is load-bearing (at `A = B = 0` the iff is false).
-/

namespace LegitFiniteDefectAuditR2

open Set Finset Cleanroom.Found.LitDdbFrames Cleanroom.Trust.LegitFiniteDefect

noncomputable section

/-! ## P1 / P2: the crossing theorem -/

namespace SettlementProbe

open Cleanroom.Trust.LegitFiniteDefect.Settlement
open Cleanroom.Trust.LegitFiniteDefect.Settlement.Crossing

/-- P1a. Left of the crossing the settlement is at least the crossing, so `leftVal ≥ crossing`. -/
theorem crossing_le_leftVal {s : ℝ → ℝ} (hanti : AntitoneOn s (Icc 0 1))
    (hm : MapsTo s (Icc 0 1) (Icc 0 1)) (hnf : ∀ a ∈ Icc (0 : ℝ) 1, s a ≠ a)
    (hc0 : 0 < crossing s) : crossing s ≤ leftVal s := by
  have hcmem : crossing s ∈ Icc (0 : ℝ) 1 := crossing_mem hm hnf
  have hne : (s '' Ico 0 (crossing s)).Nonempty := ⟨s 0, 0, ⟨le_rfl, hc0⟩, rfl⟩
  unfold leftVal
  apply le_csInf hne
  rintro _ ⟨a, ha, rfl⟩
  by_contra h
  rw [not_le] at h
  set a' := max a ((s a + crossing s) / 2) with ha'
  have ha'lt : a' < crossing s := max_lt ha.2 (by linarith)
  have ha'mem : a' ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans (le_max_left _ _), ha'lt.le.trans hcmem.2⟩
  have hs : s a' ≤ s a := hanti ⟨ha.1, ha.2.le.trans hcmem.2⟩ ha'mem (le_max_left _ _)
  have hup := lt_of_lt_crossing hanti hm hnf ha'mem ha'lt
  have := le_max_right a ((s a + crossing s) / 2)
  linarith

/-- P1b. Right of the crossing the settlement is at most the crossing, so `rightVal ≤ crossing`. -/
theorem rightVal_le_crossing {s : ℝ → ℝ} (hanti : AntitoneOn s (Icc 0 1))
    (hm : MapsTo s (Icc 0 1) (Icc 0 1)) (hnf : ∀ a ∈ Icc (0 : ℝ) 1, s a ≠ a)
    (hc1 : crossing s < 1) : rightVal s ≤ crossing s := by
  have hcmem : crossing s ∈ Icc (0 : ℝ) 1 := crossing_mem hm hnf
  have hne : (s '' Ioc (crossing s) 1).Nonempty := ⟨s 1, 1, ⟨hc1, le_rfl⟩, rfl⟩
  unfold rightVal
  apply csSup_le hne
  rintro _ ⟨a, ha, rfl⟩
  by_contra h
  rw [not_le] at h
  set a' := min a ((s a + crossing s) / 2) with ha'
  have hlt : crossing s < a' := lt_min ha.1 (by linarith)
  have ha'mem : a' ∈ Icc (0 : ℝ) 1 := ⟨hcmem.1.trans hlt.le, (min_le_left _ _).trans ha.2⟩
  have hs : s a ≤ s a' := hanti ha'mem ⟨hcmem.1.trans ha.1.le, ha.2⟩ (min_le_left _ _)
  have hdown := lt_of_crossing_lt hnf ha'mem hlt
  have := min_le_right a ((s a + crossing s) / 2)
  linarith

/-- P2. The mandate's two-term formula holds when the settlement's value at the crossing is its
left limit (`s c = s(c⁻)`): F15 is a missing hypothesis, and the anti-indicator satisfies it. -/
theorem two_term_of_left_value {s : ℝ → ℝ} (hanti : AntitoneOn s (Icc 0 1))
    (hm : MapsTo s (Icc 0 1) (Icc 0 1)) (hnf : ∀ a ∈ Icc (0 : ℝ) 1, s a ≠ a)
    (hc0 : 0 < crossing s) (hc1 : crossing s < 1) (hL : s (crossing s) = leftVal s) :
    IsGLB (settleGap s '' Icc 0 1) (min (leftVal s - crossing s) (crossing s - rightVal s)) := by
  have h := isGLB_settleGap_crossing hanti hm hnf hc0 hc1
  have hle := crossing_le_leftVal hanti hm hnf hc0
  have hgap : settleGap s (crossing s) = leftVal s - crossing s := by
    unfold settleGap; rw [hL, abs_of_nonneg (by linarith)]
  rw [hgap] at h
  rwa [← min_assoc, min_self] at h

/-- P2 applied: the anti-indicator at level `c ∈ (0, 1)` satisfies the left-value hypothesis. -/
theorem antiIndAt_left_value {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    antiIndAt c (crossing (antiIndAt c)) = leftVal (antiIndAt c) := by
  obtain ⟨hcr, hL, _, _⟩ := antiIndAt_via_crossing hc0 hc1
  rw [hcr, hL]
  simp [antiIndAt]

end SettlementProbe

/-! ## P3: a boundary trace identifies legitimacy -/

namespace TraceProbe

open Cleanroom.Trust.LegitFiniteDefect.Trace
open Cleanroom.Trust.LegitFiniteDefect.Trace.IdentifiedSet

/-- P3. Terminal opinion `0` with a positive terminal quote: `D = 0`, and every valid system with
the same trace has defect `0`. So `exists_steered`'s interiority hypothesis is load-bearing. -/
theorem boundary_identifies {S : Sys} (hS : Valid S) (hY : run S 3 = 0) (ha : 0 < S.a 3) :
    D S = 0 ∧ ∀ S' : Sys, Valid S' → trace S' = trace S → d S' = 0 := by
  have hD : D S = 0 := by
    unfold D
    rw [hY, if_neg ha.ne', if_pos ha]
  refine ⟨hD, fun S' hS' htr => ?_⟩
  have := d_le_D hS hS' htr
  rw [hD] at this
  exact le_antisymm this (by unfold d; exact abs_nonneg _)

end TraceProbe

/-! ## P4: the hull weights in `totalTrust_clean` do work -/

namespace MechanismProbe

open Cleanroom.Trust.LegitFiniteDefect.Mechanism

/-- A clean-supported distribution that is *not* the even mixture of the rows: all mass on
`(lo, 0)` (world `0`) and `(hi, 1)` (world `3`). -/
def πbad : Fin 8 → ℝ := ![1 / 2, 0, 0, 1 / 2, 0, 0, 0, 0]

theorem πbad_mem : πbad ∈ stdSimplex ℝ (Fin 8) := by
  refine ⟨fun x => by fin_cases x <;> norm_num [πbad], ?_⟩
  simp [Fin.sum_univ_eight, πbad, vec8_two, vec8_three, vec8_four, vec8_five, vec8_six, vec8_seven]
  norm_num

theorem πbad_clean_supported : ∀ w, 0 < πbad w → mech w = 0 := by
  intro w hw
  fin_cases w <;>
    simp [πbad, mech, vec8_two, vec8_three, vec8_four, vec8_five, vec8_six, vec8_seven] at hw ⊢

theorem ind_one : ind ({1} : Finset (Fin 8)) = ![0, 1, 0, 0, 0, 0, 0, 0] := by
  funext w
  fin_cases w <;> simp [ind, vec8_two, vec8_three, vec8_four, vec8_five, vec8_six, vec8_seven]

theorem E_rows_ind_one :
    E ρlo ![0, 1, 0, 0, 0, 0, 0, 0] = 1 / 4 ∧ E ρhi ![0, 1, 0, 0, 0, 0, 0, 0] = 0 := by
  constructor <;>
    simp only [E, Fin.sum_univ_eight, ρlo, ρhi, vec8_two, vec8_three, vec8_four, vec8_five,
      vec8_six, vec8_seven, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    norm_num

/-- P4. `πbad` is a clean-supported prior, yet Total Trust fails at `X = 𝟙{world 1}`, `s = 1/4`
(the product sum is `−1/8`): the expert's `lo` row says `θ = 1` with probability `1/4`, but under
`πbad` a `lo` report means `θ = 0` surely. `totalTrust_clean` rests on `πclean = ½ρlo + ½ρhi`. -/
theorem not_totalTrust_πbad : ¬ TotalTrust πbad F := by
  intro h
  have := h (ind {1}) (1 / 4)
  rw [ind_one] at this
  obtain ⟨elo, ehi⟩ := E_rows_ind_one
  simp only [Fin.sum_univ_eight, F_P, vec8_two, vec8_three, vec8_four, vec8_five, vec8_six,
    vec8_seven, Matrix.cons_val_zero, Matrix.cons_val_one, elo, ehi] at this
  simp only [πbad, vec8_two, vec8_three, vec8_four, vec8_five, vec8_six, vec8_seven,
    Matrix.cons_val_zero, Matrix.cons_val_one] at this
  norm_num at this

end MechanismProbe

/-! ## P5: `regime_iff` needs `0 < B` -/

/-- P5. At `A = B = 0` the biconditional of `regime_iff` is false, so its `0 < B` hypothesis is
load-bearing (the shipped instances have `B = 5/16`, `1/10`, `73/256`). -/
theorem regime_iff_needs_B_pos :
    ¬ ((∀ σ : ℚ, 0 < σ → σ ≤ 1 → 0 < σ * ((0 : ℚ) + σ * 0)) ↔ (0 : ℚ) ≤ 0) := by
  intro h
  have := h.2 le_rfl 1 one_pos le_rfl
  norm_num at this

end

end LegitFiniteDefectAuditR2

#print axioms LegitFiniteDefectAuditR2.SettlementProbe.two_term_of_left_value
#print axioms LegitFiniteDefectAuditR2.MechanismProbe.not_totalTrust_πbad
#print axioms LegitFiniteDefectAuditR2.TraceProbe.boundary_identifies
