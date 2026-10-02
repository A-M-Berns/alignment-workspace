import Cleanroom.Decision.DpReferentsCdt.Rows2

/-!
# `dp-referents-cdt` · audit r1 (adversarial) probe: completing findings F2's witness

Not imported by the library.

Findings F2 says the mandate's hypothesis `nuPoly C B (obs d) ≠ 0` (in place of `0 < ν_C(O_d)`) is
not enough for Lemma C2-L3 / FA-20′(i), with Told-You-So `d₁₀` under `C₀` as the witness:
`tys_refR3_ten_C0` (`refR3 = (5, 10)`) and `tys_realReach_ten_C0` (`realReach = 0`,
`refR2Real = 0`, `nuPoly O₁₀ ≠ 0`). For that to refute the mandate's *stated* hypothesis package
the point must also be F3′-structural with disjoint action events — which the package never
proves at `d₁₀`. This probe supplies the two missing conjuncts, so the witness inhabits the full
mandate package (F3′ structural + disjointness + `nuPoly ≠ 0`) and the identity fails there
(`5 ≠ 0`). F2's claim is right; its Lean evidence was incomplete.
-/

namespace Cleanroom.Decision.DpReferentsCdt.AuditR1Adversarial

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpReferentsCdt
open Finset

/-- The `d₁₀`-node of Told-You-So is node-action-veridical. -/
theorem tys_ten_nav : NodeActionVeridical tysActEv toldYouSo (some ⟨.ten, none⟩) := by
  intro ℓ a ha
  rcases ℓ with ⟨k, ℓ⟩
  cases k
  · simp [toldYouSo, edgeOf_decision_some] at ha
  · rcases ℓ with ⟨v, _⟩
    simp only [toldYouSo, edgeOf_decision_some, dite_true, edgeOf_decision_none,
      Option.some.injEq] at ha
    subst ha
    cases v <;> simp [tysActEv, toldYouSo, world]

/-- Told-You-So is F3′-structural at `d₁₀`: the only `d₁₀`-node is subtree-veridical for `O₁₀`
and every positive `O₁₀`-run passes it once. -/
theorem tys_ten_actRecordingStructural : ActRecordingStructural tysObs tysActEv toldYouSo .ten := by
  intro C _
  refine ⟨?_, ?_⟩
  · rintro (_ | ⟨k, q⟩) hpt _ ℓ hℓ
    · exact absurd hpt (by decide)
    · cases k
      · exact q.elim
      · rcases q with _ | ⟨v', e⟩
        · rcases ℓ with ⟨k', ℓ'⟩
          cases k'
          · rw [mem_leavesBelow] at hℓ
            simp [toldYouSo, edgeOf_decision_some] at hℓ
          · rcases ℓ' with ⟨v, _⟩
            cases v <;> simp [tysObs, toldYouSo, world]
        · cases v' <;> exact e.elim
  · intro ℓ _ hobs
    rcases ℓ with ⟨k, ℓ⟩
    cases k
    · simp [tysObs, toldYouSo, world] at hobs
    · rcases ℓ with ⟨v, _⟩
      refine ⟨some ⟨.ten, none⟩, ⟨?_, tys_ten_nav⟩, ?_⟩
      · rw [mem_dNodesOn]
        refine ⟨rfl, ?_⟩
        simp [toldYouSo, edgeOf_decision_some, edgeOf_decision_none]
      · rintro (_ | ⟨k', q⟩) ⟨hmem, -⟩
        · rw [mem_dNodesOn] at hmem
          exact absurd hmem.1 (by decide)
        · cases k'
          · exact q.elim
          · rcases q with _ | ⟨v', e⟩
            · rfl
            · cases v' <;> exact e.elim

/-- The action events of Told-You-So are disjoint at `d₁₀`. -/
theorem tys_ten_actEvDisjoint : ActEvDisjoint tysActEv .ten := by
  intro a b hab
  rw [Finset.disjoint_left]
  intro w hw hw'
  simp only [tysActEv, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
  exact hab (hw.symm.trans hw')

/-- **F2's witness, complete**: F3′ structural + disjointness + `nuPoly O₁₀ ≠ 0` all hold at
`d₁₀` under `C₀`, yet `refR3 .five = 5 ≠ 0 = refR2Real .five` (the latter junk: `realReach = 0`).
The mandate's T3/T5(i) hypothesis package is therefore insufficient, as F2 says. -/
theorem f2_witness_complete :
    ActRecordingStructural tysObs tysActEv toldYouSo .ten ∧
    ActEvDisjoint tysActEv .ten ∧
    nuPoly procFiveTen toldYouSo (tysObs .ten) ≠ 0 ∧
    refR3 tysObs tysActEv procFiveTen toldYouSo .ten .five = 5 ∧
    refR2Real tysActEv procFiveTen toldYouSo .ten .five = 0 :=
  ⟨tys_ten_actRecordingStructural, tys_ten_actEvDisjoint, tys_realReach_ten_C0.2.2,
    tys_refR3_ten_C0.1, tys_realReach_ten_C0.2.1⟩

end Cleanroom.Decision.DpReferentsCdt.AuditR1Adversarial
