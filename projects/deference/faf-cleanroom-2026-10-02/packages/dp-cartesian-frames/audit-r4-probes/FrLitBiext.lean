import Cleanroom.Decision.DpCartesianFrames.DiagStruct

/-!
# Audit r4 (adversarial) probe: `FrLit U B ≃ᵇ Fr B` for every `U`, `B`

The report ("Repair round 3") asks a fresh auditor to check that `FrLit`'s `commit`/`assume`
restriction is the source's "row bijection and column identity" and not a squeeze — that
restricting the lazy relocated frame to the lifted rows and the structural-diagonal columns
does not smuggle content into `frLitIsoFr_of_injective`.

The check: `FrLit U B` is biextensionally equivalent to `Fr B` for **every** tree and every
`U`, nested fibers included, by the same two maps as `mapWorlds_frIdentS_biextEquiv_fr`
(`toPolicy`/`liftFun` on rows, `diagStruct`/a chosen preimage on columns) — and both
homotopies are the row-side identity `toPolicy_liftFun`, since `FrLit`'s rows are already in
bijection with `Fr B`'s. So the restriction loses nothing at the `≃ᵇ` grade (UN-7 holds for
`FrLit` as it does for `FrIdent` and `FrIdentS`), and what the injectivity hypothesis of
`frLitIsoFr_of_injective` buys is exactly the upgrade from `≃ᵇ` to `≅`: a bijection of
columns. That is the content of ZO-5(b) as the source states it, and nothing in the
definition of `FrLit` pre-decides it.

Not imported by the library.
-/

namespace Cleanroom.Decision.DpCartesianFrames.AuditR4

open CartesianFrames CategoryTheory
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpCartesianFrames

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [DecidableEq ι] [∀ d, Fintype (acts d)] (U : Finset ι)

/-- **`FrLit U B ≃ᵇ Fr B` for every `B`, `U`** — the literal identified frame's row and column
restrictions are biextensionally invisible; injectivity of `diagStruct` is needed only for
`≅`. -/
theorem frLit_biextEquiv_fr (B : Tree Ω ι acts K) : FrLit U B ≃ᵇ Fr B := by
  refine Frame.biextEquiv_iff_homotopyEquiv.mpr ⟨?_, ?_, ?_, ?_⟩
  · exact
      { agent := fun ρ => toPolicy U (ρ.val (.inr ())) ρ.val
        env := fun ε => ⟨diagStruct U B ε, ⟨ε, rfl⟩⟩
        adjoint := fun ρ ε => by
          show Prod.map Prod.fst id ((Fr (relocRoot U B)).outcome ρ.val (diagStruct U B ε)) =
            (Fr B).outcome (toPolicy U (ρ.val (.inr ())) ρ.val) ε
          rw [fr_relocRoot_outcome_diagStruct]
          rfl }
  · exact
      { agent := fun π => ⟨liftFun U π, ⟨π, rfl⟩⟩
        env := fun y => Classical.choose y.property
        adjoint := fun π y => by
          show (Fr B).outcome π (Classical.choose y.property) =
            Prod.map Prod.fst id ((Fr (relocRoot U B)).outcome (liftFun U π) y.val)
          conv_rhs => rw [← Classical.choose_spec y.property]
          rw [fr_relocRoot_outcome_diagStruct, toPolicy_liftFun]
          rfl }
  · rintro ⟨_, π, rfl⟩ y
    simp only [Frame.id_env, Frame.comp_agent, Function.comp, id]
    show (FrLit U B).outcome ⟨liftFun U π, ⟨π, rfl⟩⟩ y =
      (FrLit U B).outcome ⟨liftFun U (toPolicy U (liftFun U π (.inr ())) (liftFun U π)),
        ⟨_, rfl⟩⟩ y
    rw [toPolicy_liftFun]
  · intro π ε
    simp only [Frame.id_env, Frame.comp_agent, Function.comp, id]
    show (Fr B).outcome π ε =
      (Fr B).outcome (toPolicy U (liftFun U π (.inr ())) (liftFun U π)) ε
    rw [toPolicy_liftFun]

end Cleanroom.Decision.DpCartesianFrames.AuditR4
