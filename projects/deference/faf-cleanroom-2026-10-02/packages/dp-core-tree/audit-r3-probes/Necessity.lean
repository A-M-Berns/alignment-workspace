import Cleanroom.Found.DpCoreTree

/-!
# dp-core-tree — audit round 3, fidelity lens: probe

Not imported by the library. Elaborated with `scripts/lean-check`.

Two checks the package states in prose but does not ship as declarations.

1. **Lemma 3′'s recording hypothesis is load-bearing.** `screening_recorded` derives the draw's
   independence from Definition 6 (`mass_edge`) and takes `RecordsFor` as its only substantive
   hypothesis. On the overwrite tree (`Overwrite.lean`) `O_d = ⊤`, `{ℓ = 1}` is pre-query
   (`overwrite_preQuery_lesion`), the tree is not recorded (`overwrite_not_recordsFor`), and
   Lemma 3′'s conclusion **fails** with `X = {ℓ = 1}`, `a = {m = 1}`: `3/8 · 1 ≠ 1/2 · 5/8`
   (`screening_recorded_fails_without_recording`). So the recording hypothesis is necessary, not
   decorative; the package's `overwrite_m_not_indep_lesion` is this fact in a different shape
   (findings F1 say "the world-level clause needs recording" but no declaration says so about
   `screening_recorded` itself).
2. **`screening_draw`'s hypotheses are `PreQuery` at `O_d = ⊤`**, as its docstring says
   (`preQuery_top_iff`): the run-level Lemma 3 is Lemma 3′'s hypothesis package with recording
   dropped and `O_d = ⊤`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree.AuditR3

open Finset Catalogue Tree

/-- `{ℓ = 1}` is pre-query for `d` on the overwrite tree under `owProc` (every `d`-node decides
it: `overwrite_decided_lesion`). -/
theorem overwrite_preQuery_lesion : PreQuery owObs owProc overwrite () owL1 := by
  intro ℓ _ _ q _ _
  exact overwrite_decided_lesion q

/-- The action event `{m = 1}` of the overwrite tree is the event `owM1`. -/
theorem owActEv_true : owActEv () true = owM1 := rfl

/-- **Lemma 3′'s conclusion fails on the overwrite tree**, whose only missing hypothesis is
recording: `X = {ℓ = 1}` is pre-query, `RecordsFor` fails, and
`ν(X ∩ a ∩ O_d) · ν(O_d) = 3/8 · 1 ≠ 1/2 · 5/8 = ν(X ∩ O_d) · ν(a ∩ O_d)` with `O_d = ⊤`,
`a = {m = 1}`. So `screening_recorded`'s recording hypothesis is necessary. -/
theorem screening_recorded_fails_without_recording :
    PreQuery owObs owProc overwrite () owL1 ∧
    ¬ RecordsFor owObs owActEv owProc overwrite () ∧
    nu owProc overwrite (owL1 ∩ owActEv () true ∩ owObs ()) * nu owProc overwrite (owObs ()) ≠
      nu owProc overwrite (owL1 ∩ owObs ()) *
        nu owProc overwrite (owActEv () true ∩ owObs ()) := by
  refine ⟨overwrite_preQuery_lesion, overwrite_not_recordsFor, ?_⟩
  obtain ⟨v1, v2, v3, v4⟩ := overwrite_nu_values
  have e1 : owL1 ∩ owActEv () true ∩ owObs () = owM1 ∩ owL1 := by
    rw [owActEv_true]
    show owL1 ∩ owM1 ∩ Finset.univ = owM1 ∩ owL1
    rw [Finset.inter_univ, Finset.inter_comm]
  have e2 : owObs () = Finset.univ := rfl
  have e3 : owL1 ∩ owObs () = owL1 := Finset.inter_univ _
  have e4 : owActEv () true ∩ owObs () = owM1 := by
    rw [owActEv_true]; exact Finset.inter_univ _
  rw [e1, e3, e4, e2, v1, v2, v3, v4]
  norm_num

/-- `screening_draw`'s two hypotheses are exactly `PreQuery` with `O_d = ⊤` (its docstring's
claim), so the run-level Lemma 3 is Lemma 3′'s package minus recording. -/
theorem preQuery_top_iff {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [DecidableEq ι]
    [Fintype Ω] (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (X : Finset Ω) :
    PreQuery (fun _ => (Finset.univ : Finset Ω)) C B d X ↔
      ∀ ℓ, 0 < leafLaw C B ℓ → ∀ q, pt B q = d → (edgeOf B q ℓ).isSome → DecidedAt B q X := by
  constructor
  · intro h ℓ hpos q hq he
    exact h ℓ hpos (Finset.mem_univ _) q hq he
  · intro h ℓ hpos _ q hq he
    exact h ℓ hpos q hq he

end Cleanroom.Found.DpCoreTree.AuditR3
