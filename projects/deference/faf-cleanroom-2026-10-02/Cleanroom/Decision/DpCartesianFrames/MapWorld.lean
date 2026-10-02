import Cleanroom.Decision.DpCartesianFrames.Profiles
import Cleanroom.Decision.DpFairnessReloc.Iso

/-!
# World relabelling and the frame functor

Package `dp-cartesian-frames`, file 7 (infrastructure). `dp-fairness-reloc` states the strong
fairness of a relocation output on the *coarsened* tree `mapWorld Prod.fst (relocRoot U B)`
(the `pol` stamps projected away), while the identified frame lives on the stamped tree. The
bridge: the frame of a relabelled tree is the relabelled frame, up to biextensional
equivalence — `Fr (mapWorld f B) ≃ᵇ (mapWorlds (Prod.map f id)).obj (Fr B)` — since chance
profiles and runs ignore world labels (`profileOfMapWorld`, `readout_mapWorld_runLeaf`).
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames CategoryTheory
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc

variable {Ω Ω' ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-- A chance profile of the relabelled tree read as one of the original (the shape is the same).
Source: none: infrastructure
Kind: D -/
def profileOfMapWorld (f : Ω → Ω') :
    (B : Tree Ω ι acts K) → ChanceProfile (mapWorld f B) → ChanceProfile B
  | .leaf _ _, _ => ()
  | .chance _ _ child, ε => (ε.1, fun i => profileOfMapWorld f (child i) (ε.2 i))
  | .decision _ child, ε => fun a => profileOfMapWorld f (child a) (ε a)

/-- A chance profile of the original read as one of the relabelled tree.
Source: none: infrastructure
Kind: D -/
def profileToMapWorld (f : Ω → Ω') :
    (B : Tree Ω ι acts K) → ChanceProfile B → ChanceProfile (mapWorld f B)
  | .leaf _ _, _ => ()
  | .chance _ _ child, ε => (ε.1, fun i => profileToMapWorld f (child i) (ε.2 i))
  | .decision _ child, ε => fun a => profileToMapWorld f (child a) (ε a)

theorem profileOfMapWorld_toMapWorld (f : Ω → Ω') :
    (B : Tree Ω ι acts K) → ∀ ε, profileOfMapWorld f B (profileToMapWorld f B ε) = ε
  | .leaf _ _, _ => rfl
  | .chance _ _ child, ε =>
      Prod.ext rfl (funext fun j => profileOfMapWorld_toMapWorld f (child j) (ε.2 j))
  | .decision _ child, ε => funext fun a => profileOfMapWorld_toMapWorld f (child a) (ε a)

/-- The readout of the relabelled tree's run is the relabelled readout of the original's run.
Source: none: infrastructure
Kind: L -/
theorem readout_mapWorld_runLeaf (f : Ω → Ω') (π : (d : ι) → acts d) :
    (B : Tree Ω ι acts K) → ∀ ε : ChanceProfile (mapWorld f B),
      readout (mapWorld f B) (runLeaf π (mapWorld f B) ε) =
        Prod.map f id (readout B (runLeaf π B (profileOfMapWorld f B ε)))
  | .leaf _ _, _ => rfl
  | .chance _ _ child, ε => readout_mapWorld_runLeaf f π (child ε.1) (ε.2 ε.1)
  | .decision d child, ε => readout_mapWorld_runLeaf f π (child (π d)) (ε (π d))

/-- **The frame of a relabelled tree is the relabelled frame** (up to `≃ᵇ`; the carriers are
canonically the same, and the outcomes agree by `readout_mapWorld_runLeaf`).
Source: none: infrastructure (CF-1's functoriality in the world labels; needed to read
`dp-fairness-reloc`'s pre-enrichment fairness on the frame side)
Kind: P
Fidelity: exact
Hyps: none -/
theorem fr_mapWorld_biextEquiv (f : Ω → Ω') (B : Tree Ω ι acts K) :
    Fr (mapWorld f B) ≃ᵇ (Frame.mapWorlds (Prod.map f id)).obj (Fr B) := by
  refine Frame.biextEquiv_iff_homotopyEquiv.mpr ⟨?_, ?_, ?_, ?_⟩
  · exact
      { agent := id
        env := profileToMapWorld f B
        adjoint := fun π ε => by
          show readout (mapWorld f B) (runLeaf π (mapWorld f B) (profileToMapWorld f B ε)) =
            Prod.map f id (readout B (runLeaf π B ε))
          rw [readout_mapWorld_runLeaf, profileOfMapWorld_toMapWorld] }
  · exact
      { agent := id
        env := profileOfMapWorld f B
        adjoint := fun π ε => by
          show Prod.map f id (readout B (runLeaf π B (profileOfMapWorld f B ε))) =
            readout (mapWorld f B) (runLeaf π (mapWorld f B) ε)
          rw [readout_mapWorld_runLeaf] }
  · intro π ε; rfl
  · intro π ε; rfl

/-- Column-determinedness of a relabelled frame is column-determinedness at the preimage.
Source: none: infrastructure
Kind: L -/
theorem columnDetermined_mapWorlds_iff {W V : Type} (p : W → V) (C : CartesianFrames.Frame W)
    (S : Set V) :
    ColumnDetermined ((Frame.mapWorlds p).obj C) S ↔ ColumnDetermined C (p ⁻¹' S) :=
  Iff.rfl

end Cleanroom.Decision.DpCartesianFrames
