import Cleanroom.Decision.DpDevicesCatalog.GridMore

set_option autoImplicit false

/-!
# `dp-devices-catalog` · audit round 2 (adversarial) · probe I: the `tysObsAlt` witness

Evidence file for `dp-devices-catalog-audit-r2-adversarial.md`. **Not imported by the library.**

* Q1 — the repair's `N+` for the vacuity criterion with non-empty action events
  (`tysObsAlt_d2Vacuous_ten`) is vacuity of the *observation itself*: `O'₁₀ = {(5,10)}` has
  `ν_{C'}(O'₁₀) = 0` for every procedure `C'` (so for every tremble) and `nuPoly = 0`, so D2's
  domain guard `nuPoly C B (obs d) ≠ 0` already discharges `d₁₀` and the escape clause does no
  work the guard does not. The witness is what audit round 1 literally asked for (one point
  unconstrained, the other substantive) but it does not exhibit the ZO-19 shape "`O_d` realized,
  no action event realized within it".
* Q2 — on the AMD carrier `AmdW = {sa, sba, sbb}` every world is a leaf-world, so a non-empty
  event disjoint from the leaf-worlds does not exist: the package's empty rendering
  `amdActEvUnrec = ∅` is the *only* unrecorded encoding available on this carrier (a positive
  check of the `N−` cell's disclosure, and the reason the sharper `N+` cannot be built on the AMD
  without enlarging `AmdW`).
-/

namespace Cleanroom.Decision.DpDevicesCatalog.AuditR2

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpDevicesCatalog

/-- Q1(a): `O'₁₀` is null under every procedure (hence under every tremble of every procedure). -/
theorem Q1_tysObsAlt_ten_null (C : Proc Five10 (fun _ => Five10) ℚ) :
    nu C toldYouSo (tysObsAlt .ten) = 0 := by
  rw [tys_nu]; simp [tysObsAlt]

/-- Q1(b): `O'₁₀` is not even tremble-realizable: `nuPoly C B_P O'₁₀ = 0`, so D2's domain guard
`nuPoly C B (obs d) ≠ 0 →` discharges `d₁₀` before the escape clause is reached. -/
theorem Q1_tysObsAlt_ten_nuPoly_zero (C : Proc Five10 (fun _ => Five10) ℚ) :
    nuPoly C toldYouSo (tysObsAlt .ten) = 0 := by
  rw [tys_nuPoly]; simp [tysObsAlt]

/-- Q1(c): consequently the D2 body at `d₁₀` holds for every procedure and tremble through the
domain guard alone (no appeal to `D2VacuousAt`). -/
theorem Q1_d2Body_ten_by_guard (C : Proc Five10 (fun _ => Five10) ℚ) (ε : ℚ) (h0 : 0 < ε)
    (h1 : ε ≤ 1) : D2BodyAt tysObsAlt tysActEv toldYouSo C ε h0 h1 .ten := by
  intro hne
  exact absurd (Q1_tysObsAlt_ten_nuPoly_zero C) hne

/-- Q2: every non-empty event on the AMD carrier contains a leaf-world of `amd`. -/
theorem Q2_amd_every_world_is_leaf (Y : Finset AmdW) (hY : Y.Nonempty) :
    ∃ ℓ : amd.Leaves, world amd ℓ ∈ Y := by
  obtain ⟨w, hw⟩ := hY
  cases w
  · exact ⟨⟨.a, ()⟩, hw⟩
  · exact ⟨⟨.b, .a, ()⟩, hw⟩
  · exact ⟨⟨.b, .b, ()⟩, hw⟩

/-- Q2 (consequence): on the AMD a non-empty action event is always realized by some chance-positive
leaf, so the vacuity criterion's condition (`d2VacuousAt_iff`) fails for every non-empty
encoding: only the empty rendering is vacuous there. -/
theorem Q2_amd_nonempty_event_realised (Y : Finset AmdW) (hY : Y.Nonempty) :
    ¬ ∀ ℓ, Positive amd ℓ → world amd ℓ ∉ Y ∩ amdObs () := by
  intro h
  obtain ⟨ℓ, hℓ⟩ := Q2_amd_every_world_is_leaf Y hY
  apply h ℓ _ (by simp [amdObs, hℓ])
  rcases ℓ with ⟨a, ℓ⟩
  · cases a
    · show (0 : ℚ) < chanceWeight amd ⟨.a, ()⟩
      simp [amd, chanceWeight]
    · rcases ℓ with ⟨b, ℓ⟩
      cases b
      · show (0 : ℚ) < chanceWeight amd ⟨.b, .a, ()⟩
        simp [amd, chanceWeight]
      · show (0 : ℚ) < chanceWeight amd ⟨.b, .b, ()⟩
        simp [amd, chanceWeight]

end Cleanroom.Decision.DpDevicesCatalog.AuditR2
