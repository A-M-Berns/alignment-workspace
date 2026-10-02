import Cleanroom.Decision.DpCartesianFrames.DiagWitnesses

/-!
# Audit r4 (adversarial) probe: ZO-5(b)'s "only if" at the frame level, on `zmTree`

Repair round 3 proves the "if" half `frLitIsoFr_of_injective : Injective (diagStruct U B) →
FrLit U B ≅ Fr B` and, as the witness that "the hypothesis is needed" (ledger row 96), only
`notInjective_diagStruct_zm : ¬ Injective (diagStruct zmU (zmTree β))`. That shows the
*hypothesis* fails on `zmTree`, not that the *conclusion* fails there — which is what "needed"
means. The gap closes by cardinality: an isomorphism in FAF's Chu category restricts to a
bijection of environments, so `range (diagStruct …) ≃ ChanceProfile (zmTree β)`, and a
surjection between finite types in bijection is injective (`Finite.injective_iff_surjective_of_equiv`),
contradicting `notInjective_diagStruct_zm`. So:

* `envEquiv_of_iso` — any `C ≅ D` in `Chu(W)` gives `D.Env ≃ C.Env` (general; FAF has no such
  lemma under this name, so it is proved here from `hom_inv_id`/`inv_hom_id`);
* `injective_diagStruct_of_frLit_iso` — `FrLit U B ≅ Fr B → Injective (diagStruct U B)`, the
  converse of `frLitIsoFr_of_injective` (so the "if" theorem's hypothesis is *equivalent* to
  its conclusion on finite trees — the matrix statement ZO-5(b) is exactly "columns in
  bijection", as the source says: "only if: the column index sets differ");
* `zm_frLit_not_iso` — `¬ Nonempty (FrLit zmU (zmTree β) ≅ Fr (zmTree β))` for every root coin:
  ZO-5(b)'s "only if" as a statement about the frames, on the package's 2-fold linear mugging.

Not imported by the library.
-/

namespace Cleanroom.Decision.DpCartesianFrames.AuditR4

open CartesianFrames CategoryTheory
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpCartesianFrames

variable {W : Type}

/-- An isomorphism in FAF's Chu category restricts to a bijection of environments
(`hom.env : D.Env → C.Env`, inverse `inv.env`). -/
def envEquiv_of_iso {C D : CartesianFrames.Frame W} (i : C ≅ D) : D.Env ≃ C.Env where
  toFun := i.hom.env
  invFun := i.inv.env
  left_inv := fun e => by
    have h := congrArg Frame.Hom.env i.inv_hom_id
    rw [Frame.comp_env, Frame.id_env] at h
    exact congrFun h e
  right_inv := fun e => by
    have h := congrArg Frame.Hom.env i.hom_inv_id
    rw [Frame.comp_env, Frame.id_env] at h
    exact congrFun h e

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  (U : Finset ι)

/-- **The converse of `frLitIsoFr_of_injective`**: if the literal identified frame is
isomorphic in `Chu(W)` to `Fr B`, the structural diagonal is injective. The iso gives
`ChanceProfile B ≃ range (diagStruct U B)`; `rangeFactorization` is a surjection between
these finite types, hence injective, hence `diagStruct U B` is. -/
theorem injective_diagStruct_of_frLit_iso (B : Tree Ω ι acts K)
    (i : FrLit U B ≅ Fr B) : Function.Injective (diagStruct U B) := by
  have e : ChanceProfile B ≃ Set.range (diagStruct U B) := envEquiv_of_iso i
  have hsurj : Function.Surjective (Set.rangeFactorization (diagStruct U B)) :=
    Set.rangeFactorization_surjective
  have hinj : Function.Injective (Set.rangeFactorization (diagStruct U B)) :=
    (Finite.injective_iff_surjective_of_equiv e).2 hsurj
  exact Set.rangeFactorization_injective.1 hinj

/-- **ZO-5(b) "only if", at the frame level, on the package's 2-fold linear mugging**: for
every root coin, the literal identified frame of the relocation output is *not* isomorphic
to `Fr (zmTree β)` in `Chu(W)` — the conclusion of `frLitIsoFr_of_injective` fails where its
hypothesis fails, so the hypothesis is load-bearing on the conclusion. -/
theorem zm_frLit_not_iso (β : FinDistr ℚ (Fin 2)) :
    ¬ Nonempty (FrLit zmU (zmTree β) ≅ Fr (zmTree β)) :=
  fun ⟨i⟩ => notInjective_diagStruct_zm β (injective_diagStruct_of_frLit_iso zmU (zmTree β) i)

end Cleanroom.Decision.DpCartesianFrames.AuditR4
