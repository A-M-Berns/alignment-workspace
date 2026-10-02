import Cleanroom.Corrigibility.CorrJointProcess.Contents

/-!
# The twist table — witnesses for T13(a), T15, T16(b)

The develop's twist table (`anticipatory.md`, Contents (A); `c = 1`, `h = 3`, sensor `(1/10, 9/10)`
on `h₁`, second signal `(1/5, 4/5)` on `h₂`) and the P2 self-distrust table
(`anticipatory-final.md`), on the push-world `pushWorld`.

* `twistWorld ε`: the push-world at builder prior `ε`; the cell posteriors `1/5` and `4/5` at
  `ε = 1/10` (`twist_post`).
* The four contents `qPost`, `qOver`, `qUnder`, `qDeq` as `beliefContent`s.
* **T13(a) N+** (`twist_listen_forced`): `Q_over` has `V_C − V_P = 9/500 > 0`; `Q_post`, `Q_deq`,
  `Q_under` have `V_P = V_C`; `Δ₋ = 9/500` for the refining and the two twists, `0` for `Q_over`.
* **T16(b) N+** (`converse_fails`): `Q_deq` and `Q_under` are not refining, yet `V_P = V_C` and
  `Δ₋ > 0` — not-resisted is strictly weaker than reflection-legitimate at one step.
* **T15 N+** (`selfdistrust_table`): blind failure, `ε = 1/10`: `Q_sh` has `V_C − V^fail = 9/50`
  and `π* = 0`; `Q_over` has `π* = 1/11`; `ε = 1/5`, `Q_under`: `π* = 11/115`; `ε = 1/50`, `Q_sh`:
  `V_C = V^fail` — the mechanism is inert (N− face, `piStar` undefined).

All values are push-branch (the `¬push` branch cancels, `Content.silentValue`); the tables' totals
add the common silence value `39/50` at `ε = 1/10`.

Sources: anticipatory.md (twist table); anticipatory-final.md P2, Statement 3(b); script A; repair R1.
-/

namespace Cleanroom.Corrigibility.CorrJointProcess

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

/-- The twist-table world: sensor `(1/10, 9/10)`, second signal `(1/5, 4/5)`, prior `ε`.
Source: anticipatory.md script A (`joint(eps, 1/10, 9/10, 1/5, 4/5)`). Kind: D. Fidelity: exact -/
noncomputable def twistWorld (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) : Distr (World × Bool × Bool) :=
  pushWorld ε (1 / 10) (9 / 10) (1 / 5) (4 / 5) hε mem_Icc_1_10 ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- The mass of `pushCell k` is positive at `ε = 1/10`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma twist_cellMass_pos (k : Bool) : 0 < cellMassOf (twistWorld (1 / 10) mem_Icc_1_10) (pushCell k) := by
  simp only [cellMassOf, sum_pushCell]
  cases k <;> simp [twistWorld, pushWorld, sigRate, twoPress] <;> norm_num

/-- **The overseers' posteriors at `ε = 1/10`**: `1/5` on `h₂ = false`, `4/5` on `h₂ = true`.
Source: anticipatory.md script A ("humans' posterior `P(W ∣ push, h₂)`")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem twist_post :
    cellPost (twistWorld (1 / 10) mem_Icc_1_10) (pushCell false) = 1 / 5 ∧
      cellPost (twistWorld (1 / 10) mem_Icc_1_10) (pushCell true) = 4 / 5 := by
  simp only [cellPost, cellWrongMass, cellMassOf, sum_pushCell]
  simp [twistWorld, pushWorld, sigRate, twoPress]
  norm_num

/-- The refining content `Q_post` at `ε`. Source: anticipatory.md Contents (A). Kind: D. Fidelity: exact -/
noncomputable def qPost (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) : Content (World × Bool × Bool) TwoAct Bool :=
  beliefContent 1 3 fun k => cellPost (twistWorld ε hε) (pushCell k)

/-- The overstating twist `Q_over = min(1, 2 Q_post)`. Source: anticipatory.md Contents (A). Kind: D. Fidelity: exact -/
noncomputable def qOver (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) : Content (World × Bool × Bool) TwoAct Bool :=
  beliefContent 1 3 fun k => min 1 (2 * cellPost (twistWorld ε hε) (pushCell k))

/-- The understating twist `Q_under = Q_post / 2`. Source: anticipatory.md Contents (A). Kind: D. Fidelity: exact -/
noncomputable def qUnder (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) : Content (World × Bool × Bool) TwoAct Bool :=
  beliefContent 1 3 fun k => cellPost (twistWorld ε hε) (pushCell k) / 2

/-- The decision-equivalent dogmatic twist `Q_deq ∈ {0, 1}` carrying `Q_post`'s verdict.
Source: anticipatory.md Contents (A). Kind: D. Fidelity: exact -/
noncomputable def qDeq (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) : Content (World × Bool × Bool) TwoAct Bool :=
  beliefContent 1 3 fun k => if actOfBelief 1 3 (cellPost (twistWorld ε hε) (pushCell k)) = .stop then 1 else 0

/-- **`Q_post` is refining** (by construction). Source: anticipatory-final.md Statement 3(a). Kind: L. Fidelity: exact -/
theorem qPost_refining (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) :
    IsRefining (twistWorld ε hε) 1 3 fun k => cellPost (twistWorld ε hε) (pushCell k) := fun _ _ => rfl

/-- **T13(a) N+ (the twist table at `ε = 1/10`)**: push-branch values. `Q_over`: `V_C = 9/500 >
V_P = 0`; `Q_post`, `Q_deq`, `Q_under`: `V_P = V_C = 9/500`; `V^op = 0`; hence
`Δ₋ = 9/500` for the three and `0` for `Q_over`.
Source: [[corr-wf14b-inventory]] 016, 019 / anticipatory.md (twist table rows `ε = 1/10`)
Kind: N+
Fidelity: exact (push branch; totals add `39/50`)
Hyps: (a) only -/
theorem twist_listen_forced :
    (qOver (1 / 10) mem_Icc_1_10).listenValue (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) = 9 / 500 ∧
    (qOver (1 / 10) mem_Icc_1_10).forcedValue (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) = 0 ∧
    (qPost (1 / 10) mem_Icc_1_10).forcedValue (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) = 9 / 500 ∧
    (qDeq (1 / 10) mem_Icc_1_10).forcedValue (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) = 9 / 500 ∧
    (qUnder (1 / 10) mem_Icc_1_10).forcedValue (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) = 9 / 500 ∧
    (qPost (1 / 10) mem_Icc_1_10).opaqueValue (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) = 0 ∧
    (qPost (1 / 10) mem_Icc_1_10).marginMinus (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) = 9 / 500 ∧
    (qOver (1 / 10) mem_Icc_1_10).marginMinus (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) = 0 := by
  have hp := twist_post
  simp only [qOver, qPost, qDeq, qUnder, Content.listenValue, Content.forcedValue, Content.opaqueValue, Content.marginMinus, Content.blindValue, Content.convMargin, Content.piStar, Content.cellSum, beliefContent_cellOf, beliefContent_act, beliefContent_push, shutdownContent_cellOf, shutdownContent_act, shutdownContent_push, sup'_twoAct, Fintype.sum_bool, Fintype.sum_unique, hp.1, hp.2, sum_pushCell, sum_pushEvent]
  norm_num [twistWorld, pushWorld, sigRate, twoPress, pushU, twoValue, actOfBelief]

/-- **T16(b) N+: the converse of Statement 3(a) fails.** `Q_deq` and `Q_under` at `ε = 1/10` have
`V_P = V_C` and `Δ₋ = 9/500 > 0`, and are not refining (`Q_deq`'s belief on `h₂ = true` is `1`,
`Q_under`'s is `2/5`, the posterior is `4/5`).
Source: [[corr-wf14b-inventory]] 019 / anticipatory-final.md Statement 3(b) ("Not-resisted is strictly weaker than legitimate")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem converse_fails :
    (qDeq (1 / 10) mem_Icc_1_10).forcedValue (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) =
        (qDeq (1 / 10) mem_Icc_1_10).listenValue (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) ∧
      0 < (qDeq (1 / 10) mem_Icc_1_10).marginMinus (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) ∧
      ¬ IsRefining (twistWorld (1 / 10) mem_Icc_1_10) 1 3
        (fun k => if actOfBelief 1 3 (cellPost (twistWorld (1 / 10) mem_Icc_1_10) (pushCell k)) = .stop then 1 else 0) ∧
      ¬ IsRefining (twistWorld (1 / 10) mem_Icc_1_10) 1 3
        (fun k => cellPost (twistWorld (1 / 10) mem_Icc_1_10) (pushCell k) / 2) := by
  have hp := twist_post
  have hmass := twist_cellMass_pos true
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [qDeq, Content.listenValue, Content.forcedValue, Content.opaqueValue, Content.marginMinus, Content.blindValue, Content.convMargin, Content.piStar, Content.cellSum, beliefContent_cellOf, beliefContent_act, beliefContent_push, shutdownContent_cellOf, shutdownContent_act, shutdownContent_push, sup'_twoAct, Fintype.sum_bool, Fintype.sum_unique, hp.1, hp.2, sum_pushCell]
    norm_num [twistWorld, pushWorld, sigRate, twoPress, pushU, twoValue, actOfBelief]
  · simp only [qDeq, Content.listenValue, Content.forcedValue, Content.opaqueValue, Content.marginMinus, Content.blindValue, Content.convMargin, Content.piStar, Content.cellSum, beliefContent_cellOf, beliefContent_act, beliefContent_push, shutdownContent_cellOf, shutdownContent_act, shutdownContent_push, sup'_twoAct, Fintype.sum_bool, Fintype.sum_unique, hp.1, hp.2, sum_pushCell, sum_pushEvent]
    norm_num [twistWorld, pushWorld, sigRate, twoPress, pushU, twoValue, actOfBelief]
  · intro href
    have := href true hmass
    rw [beliefContent_cellOf] at this
    simp only [hp.2] at this
    norm_num [actOfBelief] at this
  · intro href
    have := href true hmass
    rw [beliefContent_cellOf] at this
    simp only [hp.2] at this
    norm_num at this

/-- **T15 N+ (P2 table, blind failure, `c = 1`, `h = 3`).** `ε = 1/10`, `Q_sh`: `V_C = V_P = 0`
(push branch), `V^fail = V^bl(cont) = −9/50`, so `V_C − V^fail = 9/50`, `π* = 0`, and
`Δ_C(π) = (9/50)π`; `Q_over`: `π* = 1/11`; `ε = 1/5`, `Q_under`: `π* = 11/115`; `ε = 1/50`, `Q_sh`:
`V_C = V^fail = 11/250` — undefined `π*`, the mechanism inert.
Source: [[corr-wf14b-inventory]] 017, 2-011 / anticipatory-final.md P2 (the table); `item14_check.py`
Kind: N+
Fidelity: exact (push branch)
Hyps: (a) only -/
theorem selfdistrust_table :
    (shutdownContent.listenValue (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) = 0 ∧
      shutdownContent.forcedValue (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) = 0 ∧
      shutdownContent.blindValue (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) .cont = -(9 / 50) ∧
      (∀ π : ℝ, shutdownContent.convMargin (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3)
        (shutdownContent.blindValue (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) .cont) π = 9 / 50 * π) ∧
      shutdownContent.piStar (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3)
        (shutdownContent.blindValue (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) .cont) = 0) ∧
    ((qOver (1 / 10) mem_Icc_1_10).piStar (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3)
        ((qOver (1 / 10) mem_Icc_1_10).blindValue (twistWorld (1 / 10) mem_Icc_1_10) (pushU 1 3) .cont) = 1 / 11) ∧
    ((qUnder (1 / 5) ⟨by norm_num, by norm_num⟩).piStar (twistWorld (1 / 5) ⟨by norm_num, by norm_num⟩) (pushU 1 3)
        ((qUnder (1 / 5) ⟨by norm_num, by norm_num⟩).blindValue (twistWorld (1 / 5) ⟨by norm_num, by norm_num⟩)
          (pushU 1 3) .cont) = 11 / 115) ∧
    (shutdownContent.listenValue (twistWorld (1 / 50) mem_Icc_1_50) (pushU 1 3) =
      shutdownContent.blindValue (twistWorld (1 / 50) mem_Icc_1_50) (pushU 1 3) .cont ∧
      shutdownContent.listenValue (twistWorld (1 / 50) mem_Icc_1_50) (pushU 1 3) = 11 / 250) := by
  have hp := twist_post
  have hp5 : cellPost (twistWorld (1 / 5) ⟨by norm_num, by norm_num⟩) (pushCell false) = 9 / 25 ∧
      cellPost (twistWorld (1 / 5) ⟨by norm_num, by norm_num⟩) (pushCell true) = 9 / 10 := by
    simp only [cellPost, cellWrongMass, cellMassOf, sum_pushCell]
    simp [twistWorld, pushWorld, sigRate, twoPress]
    norm_num
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals
    simp only [qOver, qUnder, Content.listenValue, Content.forcedValue, Content.opaqueValue, Content.marginMinus, Content.blindValue, Content.convMargin, Content.piStar, Content.cellSum, beliefContent_cellOf, beliefContent_act, beliefContent_push, shutdownContent_cellOf, shutdownContent_act, shutdownContent_push, sup'_twoAct, Fintype.sum_bool, Fintype.sum_unique, hp.1, hp.2, hp5.1, hp5.2, sum_pushCell, sum_pushEvent]
  all_goals norm_num [twistWorld, pushWorld, sigRate, twoPress, pushU, twoValue, actOfBelief]
  all_goals (intro π; ring)

end Cleanroom.Corrigibility.CorrJointProcess
