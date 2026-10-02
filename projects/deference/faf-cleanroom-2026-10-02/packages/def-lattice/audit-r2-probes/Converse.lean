import Cleanroom.Found.DefLattice.TwoOptionLUV

/-!
# Audit round 2 (fidelity) probe: the T6d above face is one direction of an `iff` the source states

[[two-option-value-iff-total-trust]] §Statement: "Value against the constant option … holds **iff**
the boxed right side is ≥ 0". `value_twoOption_hardAbove` ships `→` only (the mandate asked for
that direction). This probe shows the converse is free from the same two `thm:expprovind` facts,
so the theorem renders the source's per-menu equivalence at no extra cost. Not imported by the
library; evidence for a non-blocking recommendation.
-/

namespace Cleanroom.Found.DefLattice.AuditR2

open LogicalInduction Filter Topology

theorem value_twoOption_hardAbove_iff (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] {E : Expert DP}
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {X C S W XW : ℕ → LUV} {s : ℚ} (d : HardTwoOptionData DP E X C S W XW s) :
    (fun n => (S n).expect P n) ≳ₙ (fun n => (C n).expect P n) ↔
      (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ)) := by
  refine ⟨value_twoOption_hardAbove P DP hworld d, fun hTT => ?_⟩
  have hlin := d.expect_followed_asympEq P hworld
  have hconst := d.expect_const_asympEq P hworld
  -- `E(C) ≈ₙ s ≲ₙ E(XW) + s − s·E(W) ≈ₙ E(S)`
  have h1 : (fun _ => (s : ℝ)) ≲ₙ
      (fun n => (XW n).expect P n + (s : ℝ) - (s : ℝ) * (W n).expect P n) := by
    unfold AsympGE at hTT
    unfold AsympLE at hTT ⊢
    intro ε hε
    filter_upwards [hTT ε hε] with n hn
    linarith
  have h2 : (fun n => (C n).expect P n) ≲ₙ
      (fun n => (XW n).expect P n + (s : ℝ) - (s : ℝ) * (W n).expect P n) :=
    AsympEq.trans_asympLE hconst h1
  unfold AsympGE
  exact AsympLE.trans_asympEq h2 hlin.symm

/-- The below face likewise. -/
theorem value_twoOption_hardBelow_iff (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] {E : Expert DP}
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {X C S W XW : ℕ → LUV} {s : ℚ} (d : HardTwoOptionData DP E X C S W XW s) :
    (fun n => (S n).expect P n) ≳ₙ (fun n => (X n).expect P n) ↔
      (fun n => (s : ℝ) * (1 - (W n).expect P n) - ((X n).expect P n - (XW n).expect P n)) ≳ₙ
        (fun _ => (0 : ℝ)) := by
  refine ⟨value_twoOption_hardBelow P DP hworld d, fun hTT => ?_⟩
  have hlin := d.expect_followed_asympEq P hworld
  have h1 : (fun n => (X n).expect P n) ≲ₙ
      (fun n => (XW n).expect P n + (s : ℝ) - (s : ℝ) * (W n).expect P n) := by
    unfold AsympGE at hTT
    unfold AsympLE at hTT ⊢
    intro ε hε
    filter_upwards [hTT ε hε] with n hn
    linarith
  unfold AsympGE
  exact AsympLE.trans_asympEq h1 hlin.symm

end Cleanroom.Found.DefLattice.AuditR2
