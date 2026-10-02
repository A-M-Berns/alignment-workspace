import Cleanroom.Decision.DpCalibration.Corollaries
import Cleanroom.Decision.DpCalibration.HypWitnesses

/-!
# The tie tree: CA-12′'s consequences inhabited (repair round 2)

Audit round 2 (fidelity B1 = adversarial B1) found that the three CA-12′ consequence theorems of
`Corollaries.lean` (`V_actEv_eq_of_recordsForAll`, `tie_of_mixed_approved`,
`tEdtAt_of_support_subset_of_recordsForAll`) shipped no witness inhabiting their hypothesis
package: the ledger had named the miniature, which is nested and recorded by **no** procedure
(`miniature_not_recordsFor`). This file ships the witness (the adversarial auditor's probe
`TieTree`, adopted; `coinQuery_tie_instance` is the fidelity auditor's N− one):

* **The tie tree** — one point `d`, `a → w1` (payoff `5`), `b →` a fair coin choosing `w2`
  (payoff `0`) or `w3` (payoff `10`); `O = ⊤`; action events `{w1}` / `{w2, w3}`. Recorded for
  every procedure (`tieTree_recordsFor`, `tieTree_recordsForAll`). The strict state of a
  properly mixed `C` has `A^+ = {a, b}` and a **genuine tie** `V(a) = 5 = V(b)` between two
  *different* act-conditional world laws (`tieState_V`), so `T_EDT` approves the mixed
  `procQ ½` (`tieProc_tEdtAt`).
* `tie_of_mixed_approved_instance` (N+) — every hypothesis of `tie_of_mixed_approved`
  discharged on `procQ ½`, conclusion `V(a) = V(b)`.
* `tEdtAt_transfer_instance` (N+) — every hypothesis of
  `tEdtAt_of_support_subset_of_recordsForAll` discharged, approval moved from `procQ ½` to the
  pure sub-mixture `δ_a = procQ 1`.
* `tieTree_every_label_approved` — **CA-12′'s "never forced" in full on one tree**: every label
  `procQ q`, `q ∈ [0, 1]`, is strictly calibrated and `T_EDT`-approved with its own strict state
  (pure or mixed alike), by the transfer theorem from `procQ ½`. Contrast the miniature, where
  the interior approved label is pinned at `2/3` (`miniature_tEdt_interior_iff`): the difference
  is recording.
* `coinQuery_tie_instance` (N−) — the same package on `coinQuery` (zero payoffs: the tie is
  `0 = 0`).
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

section tieTree

/-- Tie-tree worlds. Source: none: infrastructure (audit round 2 probe `TieTree`). Kind: D -/
inductive TieW : Type
  | w1
  | w2
  | w3
  deriving DecidableEq, Fintype

/-- **The tie tree**: `a → w1` with payoff `5`; `b →` a fair coin choosing `w2` (payoff `0`) or
`w3` (payoff `10`). A recorded one-point tree with two acts of equal but non-trivial
continuation value.
Source: `calibration.md` CA-12′ (the recorded case); audit round 2 B1 (probe adopted)
Kind: D -/
def tieTree : Tree TieW Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf .w1 5
    | .b => .chance 2 FinDistr.fair fun j =>
        .leaf (if j = 1 then .w3 else .w2) (if j = 1 then 10 else 0)

/-- `O = ⊤`. Source: none: infrastructure. Kind: D -/
def tieObs : Unit → Finset TieW := fun _ => Finset.univ

/-- Action events: `a ↦ {w1}`, `b ↦ {w2, w3}`. Source: none: infrastructure. Kind: D -/
def tieActEv (_ : Unit) (act : Act2) : Finset TieW :=
  match act with
  | .a => {.w1}
  | .b => {.w2, .w3}

/-- A sum over the leaves of the tie tree as three terms. Source: none: infrastructure. Kind: L -/
theorem tieTree_sum (f : tieTree.Leaves → ℚ) :
    ∑ ℓ, f ℓ = f ⟨.a, ()⟩ + f ⟨.b, 0, ()⟩ + f ⟨.b, 1, ()⟩ := by
  unfold tieTree at f ⊢
  rw [sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf, sum_leaves_chance, Fin.sum_univ_two]
  ring

/-- `ν` on the tie tree. Source: none: infrastructure. Kind: L -/
theorem tieTree_nu (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset TieW) :
    nu C tieTree X =
      (if TieW.w1 ∈ X then (C ()).w .a else 0) +
      (if TieW.w2 ∈ X then (C ()).w .b * (1 / 2) else 0) +
      (if TieW.w3 ∈ X then (C ()).w .b * (1 / 2) else 0) := by
  rw [nu_eq_sum, tieTree_sum]
  unfold tieTree
  simp [leafLaw_decision, leafLaw_chance, leafLaw_leaf, world_decision, world_chance, world_leaf,
    FinDistr.fair, FinDistr.coin]
  norm_num

/-- The payoff mass on the tie tree. Source: none: infrastructure. Kind: L -/
theorem tieTree_paySum (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset TieW) :
    paySum C tieTree X =
      (if TieW.w1 ∈ X then (C ()).w .a * 5 else 0) +
      (if TieW.w3 ∈ X then (C ()).w .b * (1 / 2) * 10 else 0) := by
  rw [paySum_eq_sum_ite, tieTree_sum]
  unfold tieTree
  simp [leafLaw_decision, leafLaw_chance, leafLaw_leaf, world_decision, world_chance, world_leaf,
    payoff_decision, payoff_chance, payoff_leaf, FinDistr.fair, FinDistr.coin]
  norm_num

/-- **The tie tree is recorded at `d` for every procedure**: one `d`-node on every path,
subtree-veridical (`O = ⊤`), action-veridical, and each leaf-world satisfies exactly the drawn
act's event.
Source: `dp-core-tree` Definition 7; audit round 2 B1
Kind: L -/
theorem tieTree_recordsFor (C : Proc Unit (fun _ => Act2) ℚ) :
    RecordsFor tieObs tieActEv C tieTree () := by
  intro ℓ _ _
  unfold tieTree at ℓ ⊢
  rcases ℓ with ⟨act, ℓ⟩
  refine ⟨?_, ?_⟩
  · cases act
    · rfl
    · rcases ℓ with ⟨j, _⟩; rfl
  · rintro (_ | ⟨b, q⟩) hq a ha
    · simp only [edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      refine ⟨fun ℓ' _ => by simp [tieObs], ?_, ?_⟩
      · cases act
        · simp [tieActEv]
        · rcases ℓ with ⟨j, _⟩
          fin_cases j <;> simp [tieActEv]
      · intro a' ha'
        cases act
        · cases a'
          · rfl
          · simp [tieActEv] at ha'
        · rcases ℓ with ⟨j, _⟩
          cases a'
          · fin_cases j <;> simp [tieActEv] at ha'
          · rfl
    · cases b
      · exact Empty.elim q
      · rcases q with ⟨j, q'⟩
        exact Empty.elim q'

/-- `RecordsForAll` on the tie tree. Source: audit round 2 B1. Kind: L -/
theorem tieTree_recordsForAll : RecordsForAll tieObs tieActEv tieTree () :=
  fun C => tieTree_recordsFor C

/-- The strict state of `C` on the tie tree (`O = ⊤`, always realized).
Source: none: infrastructure. Kind: D -/
noncomputable def tieState (C : Proc Unit (fun _ => Act2) ℚ) : State TieW ℚ :=
  calibratedState C tieTree Finset.univ (nu_univ_pos _ _)

/-- Beliefs of the strict state: `P(a) = C(a)`, `P(b) = C(b)` (self-transparency, computed).
Source: none: infrastructure. Kind: L -/
theorem tieState_pr (C : Proc Unit (fun _ => Act2) ℚ) :
    (tieState C).pr (tieActEv () .a) = (C ()).w .a ∧
    (tieState C).pr (tieActEv () .b) = (C ()).w .b := by
  constructor <;> rw [tieState, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, tieTree_nu] <;>
    simp [tieActEv]; ring

/-- **The tie**: for a properly mixed `C`, `V(a) = 5 = V(b)` — a genuine tie between a point mass
on `w1` and a fair coin on `w2/w3`, and (CA-12′) `C(d)`-free.
Source: `calibration.md` CA-12′; audit round 2 B1
Kind: P
Fidelity: exact -/
theorem tieState_V (C : Proc Unit (fun _ => Act2) ℚ) (ha : 0 < (C ()).w .a) (hb : 0 < (C ()).w .b) :
    (tieState C).V (tieActEv () .a) = 5 ∧ (tieState C).V (tieActEv () .b) = 5 := by
  simp only [tieState, calibratedState_V, Finset.inter_univ, tieTree_nu, tieTree_paySum, tieActEv]
  have ha' : (C ()).w .a ≠ 0 := ha.ne'
  have hb' : (C ()).w .b ≠ 0 := hb.ne'
  constructor <;> simp <;> field_simp; ring

/-- The properly mixed procedure `procQ ½`. Source: none: infrastructure. Kind: D -/
def tieProc : Proc Unit (fun _ => Act2) ℚ := procQ (1/2) (by norm_num) (by norm_num)

/-- `A^+ = {a, b}` for the strict state of `procQ ½`. Source: none: infrastructure. Kind: L -/
theorem tieProc_aPlus : APlus (fun _ => tieState tieProc) tieActEv () = Finset.univ := by
  ext a
  simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  obtain ⟨hpa, hpb⟩ := tieState_pr tieProc
  cases a
  · rw [hpa]; norm_num [tieProc, procQ]
  · rw [hpb]; norm_num [tieProc, procQ]

/-- **`T_EDT` approves the mixed label `procQ ½`** at its strict state (both acts possible, tied).
Source: [[decision-problems-v2]] Definition 18; audit round 2 B1
Kind: N+
Fidelity: exact -/
theorem tieProc_tEdtAt : TEdtAt (fun _ => tieState tieProc) tieActEv tieProc () := by
  intro _ a _
  rw [mem_argmaxPlus, tieProc_aPlus]
  obtain ⟨hva, hvb⟩ := tieState_V tieProc (by norm_num [tieProc, procQ]) (by norm_num [tieProc, procQ])
  refine ⟨Finset.mem_univ _, fun b _ => ?_⟩
  cases a <;> cases b <;> simp only [hva, hvb, le_refl]

/-- **`tie_of_mixed_approved` instantiated, N+**: every hypothesis discharged on the tie tree for
the properly mixed `procQ ½` (recording, `ν(O) = 1 > 0`, strict OC with the calibrated state,
`T_EDT` approval, both acts supported), conclusion `V(a) = V(b)` — here `5 = 5`, a tie of two
different act-conditional laws, not `0 = 0`.
Source: `calibration.md` CA-12′ (consequence); audit round 2 B1 (probe adopted)
Kind: N+
Fidelity: exact -/
theorem tie_of_mixed_approved_instance :
    RecordsFor tieObs tieActEv tieProc tieTree () ∧
    0 < nu tieProc tieTree (tieObs ()) ∧
    StrictOCAt (fun _ => tieState tieProc) tieObs tieProc tieTree () ∧
    TEdtAt (fun _ => tieState tieProc) tieActEv tieProc () ∧
    0 < (tieProc ()).w .a ∧ 0 < (tieProc ()).w .b ∧
    (tieState tieProc).V (tieActEv () .a) = (tieState tieProc).V (tieActEv () .b) := by
  have hrec := tieTree_recordsFor tieProc
  have hpos : 0 < nu tieProc tieTree (tieObs ()) := by
    unfold tieObs; exact nu_univ_pos _ _
  have hs : StrictOCAt (fun _ => tieState tieProc) tieObs tieProc tieTree () :=
    strictOCAt_calibratedState tieObs tieProc tieTree _ () _ rfl
  have ha : 0 < (tieProc ()).w .a := by norm_num [tieProc, procQ]
  have hb : 0 < (tieProc ()).w .b := by norm_num [tieProc, procQ]
  exact ⟨hrec, hpos, hs, tieProc_tEdtAt, ha, hb,
    tie_of_mixed_approved tieObs tieActEv tieTree hrec hpos hs tieProc_tEdtAt .a .b ha hb⟩

/-- The pure sub-mixture `δ_a = procQ 1`. Source: none: infrastructure. Kind: D -/
def tieProcA : Proc Unit (fun _ => Act2) ℚ := procQ 1 (by norm_num) le_rfl

/-- **`tEdtAt_of_support_subset_of_recordsForAll` instantiated, N+**: approval of the mixed
`procQ ½` transfers to the pure sub-mixture `δ_a` under its own strict state (where `A^+ = {a}`),
every hypothesis discharged (the sub-mixture's positivity is no longer a hypothesis; it is
derived inside the theorem).
Source: `calibration.md` CA-12′ ("never forced"); audit round 2 B1 (probe adopted)
Kind: N+
Fidelity: exact -/
theorem tEdtAt_transfer_instance :
    RecordsForAll tieObs tieActEv tieTree () ∧
    (∀ a, 0 < (tieProcA ()).w a → 0 < (tieProc ()).w a) ∧
    0 < nu tieProc tieTree (tieObs ()) ∧
    StrictOCAt (fun _ => tieState tieProc) tieObs tieProc tieTree () ∧
    StrictOCAt (fun _ => tieState tieProcA) tieObs tieProcA tieTree () ∧
    TEdtAt (fun _ => tieState tieProc) tieActEv tieProc () ∧
    TEdtAt (fun _ => tieState tieProcA) tieActEv tieProcA () := by
  have hsupp : ∀ a, 0 < (tieProcA ()).w a → 0 < (tieProc ()).w a := by
    intro a ha
    cases a
    · norm_num [tieProc, procQ]
    · simp [tieProcA, procQ] at ha
  have hpos : 0 < nu tieProc tieTree (tieObs ()) := by
    unfold tieObs; exact nu_univ_pos _ _
  have hs : StrictOCAt (fun _ => tieState tieProc) tieObs tieProc tieTree () :=
    strictOCAt_calibratedState tieObs tieProc tieTree _ () _ rfl
  have hs' : StrictOCAt (fun _ => tieState tieProcA) tieObs tieProcA tieTree () :=
    strictOCAt_calibratedState tieObs tieProcA tieTree _ () _ rfl
  have hoff : ∀ d', d' ≠ () → tieProc d' = tieProcA d' := fun d' h => absurd rfl h
  exact ⟨tieTree_recordsForAll, hsupp, hpos, hs, hs', tieProc_tEdtAt,
    tEdtAt_of_support_subset_of_recordsForAll tieObs tieActEv tieTree tieTree_recordsForAll hoff
      hsupp hpos hs hs' tieProc_tEdtAt⟩

/-- **CA-12′'s "never forced", in full, on the tie tree**: every label `procQ q`, `q ∈ [0, 1]` —
pure or properly mixed — is strictly calibrated (with its own strict state `tieState (procQ q)`)
and `T_EDT`-approved at `d`. Transferred from `procQ ½` by
`tEdtAt_of_support_subset_of_recordsForAll` (every support is inside `{a, b}`). On the nested,
unrecorded miniature the interior approved label is instead pinned at `2/3`
(`miniature_tEdt_interior_iff`); recording is the difference.
Source: `calibration.md` CA-12′ ("never forced"); repair round 2 (pushed further)
Kind: N+
Fidelity: exact -/
theorem tieTree_every_label_approved (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    StrictOCAt (fun _ => tieState (procQ q h0 h1)) tieObs (procQ q h0 h1) tieTree () ∧
    TEdtAt (fun _ => tieState (procQ q h0 h1)) tieActEv (procQ q h0 h1) () := by
  have hsupp : ∀ a, 0 < (procQ q h0 h1 ()).w a → 0 < (tieProc ()).w a := by
    intro a _
    cases a <;> norm_num [tieProc, procQ]
  have hpos : 0 < nu tieProc tieTree (tieObs ()) := by
    unfold tieObs; exact nu_univ_pos _ _
  have hs : StrictOCAt (fun _ => tieState tieProc) tieObs tieProc tieTree () :=
    strictOCAt_calibratedState tieObs tieProc tieTree _ () _ rfl
  have hs' : StrictOCAt (fun _ => tieState (procQ q h0 h1)) tieObs (procQ q h0 h1) tieTree () :=
    strictOCAt_calibratedState tieObs (procQ q h0 h1) tieTree _ () _ rfl
  have hoff : ∀ d', d' ≠ () → tieProc d' = procQ q h0 h1 d' := fun d' h => absurd rfl h
  exact ⟨hs', tEdtAt_of_support_subset_of_recordsForAll tieObs tieActEv tieTree
    tieTree_recordsForAll hoff hsupp hpos hs hs' tieProc_tEdtAt⟩

end tieTree

section coinQueryTie

/-- **Instance of `tie_of_mixed_approved`** on `coinQuery` with `procQ ½`: recording,
positivity, strict OC, `T_EDT` at `d`, both acts supported, and the conclusion `V(a) = V(b)`.
N−: `coinQuery`'s payoffs are all `0`, so the tie is `0 = 0`; the N+ instance is
`tie_of_mixed_approved_instance` on the tie tree.
Source: `calibration.md` CA-12′ (consequence); audit round 2 fidelity B1 (probe adopted)
Kind: N−
Fidelity: exact -/
theorem coinQuery_tie_instance :
    RecordsFor cqObs cqActEv (procQ (1/2) (by norm_num) (by norm_num)) coinQuery () ∧
    0 < nu (procQ (1/2) (by norm_num) (by norm_num)) coinQuery (cqObs ()) ∧
    StrictOCAt (fun _ => cqStrictState (1/2) (by norm_num) (by norm_num)) cqObs
      (procQ (1/2) (by norm_num) (by norm_num)) coinQuery () ∧
    TEdtAt (fun _ => cqStrictState (1/2) (by norm_num) (by norm_num)) cqActEv
      (procQ (1/2) (by norm_num) (by norm_num)) () ∧
    0 < (procQ (1/2) (by norm_num) (by norm_num) ()).w .a ∧
    0 < (procQ (1/2) (by norm_num) (by norm_num) ()).w .b ∧
    (cqStrictState (1/2) (by norm_num) (by norm_num)).V (cqActEv () .a) =
      (cqStrictState (1/2) (by norm_num) (by norm_num)).V (cqActEv () .b) := by
  obtain ⟨hr, hpos, hs⟩ := coinQuery_prop7_instance (1/2) (by norm_num) (by norm_num)
  have happ := cqStrictState_tEdtAt (1/2) (by norm_num) (by norm_num)
  have ha : 0 < (procQ (1/2) (by norm_num) (by norm_num) ()).w .a := by norm_num [procQ]
  have hb : 0 < (procQ (1/2) (by norm_num) (by norm_num) ()).w .b := by norm_num [procQ]
  exact ⟨hr, hpos, hs, happ, ha, hb,
    tie_of_mixed_approved cqObs cqActEv coinQuery hr hpos hs happ .a .b ha hb⟩

end coinQueryTie

end Cleanroom.Decision.DpCalibration
