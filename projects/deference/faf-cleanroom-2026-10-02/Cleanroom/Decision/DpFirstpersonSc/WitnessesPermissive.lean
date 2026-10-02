import Cleanroom.Decision.DpFirstpersonSc.Dogmatic
import Cleanroom.Decision.DpFirstpersonSc.Lift
import Cleanroom.Decision.DpFirstpersonSc.WitnessesNewcomb
import Cleanroom.Decision.DpFirstpersonSc.WitnessesLift
import Cleanroom.Decision.DpCalibration.ToldYouSo

/-!
# T7's "too permissive" cell on TN-V1 (AN-9)

The occurrence-only refinement **at `d`** admits the atoms `occ(d)` and `occ(d)ᶜ` and nothing
about observations. Whenever `occ(d)ᶜ` is exactly an observation event `λ⁻¹O` of *another* point,
its posterior `μ(· | occ(d)ᶜ)` pushes down to the strict-OC state at `O`
(`occOnly_compl_reaches`, general). On V1 `occ(d_E) = λ⁻¹O_E` exactly (`tnV1_occ_E_eq`), so
`occ(d_E)ᶜ = λ⁻¹O_F` (`tnV1_occ_E_compl`) and the refinement at `d_E` reaches **`d_F`'s** strict
state (`tnV1_half_occOnly_package`): `d_F`'s observation is recovered through `d_E`'s
non-consultation. So Def 6.2's verdict with occurrence atoms alone is "too coarse" on `B₁`
(`occOnly_posteriors`) but, point by point, too permissive. N+: `tnHalf` on V1
(`tnV1_half_occOnly_package`), and (continuation 2) Told-You-So at `d₁₀`: `occ(d₁₀)ᶜ = λ⁻¹O₅`
exactly (`tys_occ_ten_compl`), so the occurrence-only refinement at `d₁₀` reaches **`d₅`'s**
strict state `δ_{(5,5)}` through `d₁₀`'s non-consultation (`tys_occOnly_package`, under every
`C` with `C(d₅)(5) > 0`).

Elaboration note: the SC-level statement is the general `occOnly_compl_reaches` (abstract `Ω ι
acts`); on the concrete `TnPt`/`Box` types, `condOn (runPMF C B) (evAtom (occ .E B) ⁻¹' {false})`
does not elaborate within any heartbeat budget tried (`whnf`/`isDefEq` on the coerced `Finset`
instance terms), even for an abstract `B`, while an event *variable* `A : Set B.Leaves` is fine —
so the TN-V1 cell is stated as the inhabited hypothesis package (`tnV1_half_occOnly_package`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree hiding mass mass_mono mass_union mass_univ mass_nonneg
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Cleanroom.Udt.UdtSupercondition
open Finset

/-- `condOn` depends on the event only up to equality (proof irrelevance of the positivity
guard). Source: none: infrastructure. Kind: L -/
theorem condOn_congr_set {α : Type} (P : PMF α) {S T : Set α} (hST : S = T) (hS : 0 < mass P S)
    (hT : 0 < mass P T) : condOn P S hS = condOn P T hT := by
  subst hST; rfl

/-- `condDistr` depends on the event only up to equality. Source: none: infrastructure. Kind: L -/
theorem condDistr_congr_set {α : Type} [Fintype α] [DecidableEq α] (P : FinDistr ℚ α)
    {S T : Finset α} (hST : S = T) (hS : 0 < probOf P S) (hT : 0 < probOf P T) :
    condDistr P S hS = condDistr P T hT := by
  subst hST; rfl

/-- The `false` atom of `evAtom E` is `Eᶜ`. Source: none: infrastructure. Kind: L -/
theorem evAtom_preimage_false {W : Type} [DecidableEq W] [Fintype W] (E : Finset W) :
    evAtom E ⁻¹' {false} = (↑(Eᶜ) : Set W) := by
  ext w; simp [evAtom]

section general

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]
  (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (d : ι) (O : Finset Ω)

/-- When `occ(d)ᶜ = λ⁻¹O` and `ν(O) > 0`, the `false` atom of `d`'s occurrence anticipation has
positive run mass. Source: none: infrastructure. Kind: L -/
theorem occOnly_compl_pos (hc : (occ d B)ᶜ = worldEv B O) (hO : 0 < nu C B O) :
    0 < mass (runPMF C B) (evAtom (occ d B) ⁻¹' {false}) := by
  rw [evAtom_preimage_false, mass_runPMF_pos_iff, hc]
  exact hO

/-- **AN-9's "too permissive" mechanism, in general**: if `occ(d)ᶜ` is exactly the observation
event `λ⁻¹O` (of any point) with `ν(O) > 0`, the occurrence-only refinement at `d` has the
posterior `μ(· | occ(d)ᶜ)` (an `OccOnlyPosterior` for `d`) whose pushdown to `Ω` is the strict-OC
state at `O`: an observation-conditioned state is reached through `d`'s non-consultation alone.
Source: `anticipation.md` AN-9; mandate T7(b) ("recovers … through another point's
non-consultation")
Kind: C / L (`pushdownDistr_condDistr_worldEv` plus two proof-irrelevance congruences; audit r1
adversarial N2)
Fidelity: exact
Hyps: (a) `occ(d)ᶜ = λ⁻¹O`, (a) `ν(O) > 0` -/
theorem occOnly_compl_reaches (hc : (occ d B)ᶜ = worldEv B O) (hO : 0 < nu C B O)
    (hpos : 0 < mass (runPMF C B) (evAtom (occ d B) ⁻¹' {false})) :
    OccOnlyPosterior C B d (condOn (runPMF C B) (evAtom (occ d B) ⁻¹' {false}) hpos) ∧
    (condOn (runPMF C B) (evAtom (occ d B) ⁻¹' {false}) hpos).map (world B) =
      toPMF (calibratedState C B O hO).P := by
  refine ⟨⟨{false}, hpos, rfl⟩, ?_⟩
  have hpos' : 0 < mass (runPMF C B) (↑((occ d B)ᶜ) : Set B.Leaves) := by
    rw [← evAtom_preimage_false]; exact hpos
  rw [condOn_congr_set _ (evAtom_preimage_false (occ d B)) hpos hpos']
  have hq : 0 < probOf (leafDistr C B) ((occ d B)ᶜ) := by
    rw [probOf_leafDistr, hc]; exact hO
  have hq' : 0 < probOf (leafDistr C B) (worldEv B O) := by
    rw [probOf_leafDistr]; exact hO
  show (condOn (toPMF (leafDistr C B)) _ hpos').map _ = _
  rw [condOn_toPMF' _ _ hq hpos', toPMF_map_world, condDistr_congr_set _ hc hq hq',
    pushdownDistr_condDistr_worldEv C B O hO hq']

/-- **AN-9's "too coarse" half, in general**: when every run consults `d` (`occ(d) = ⊤`), the
occurrence-only refinement at `d` has `μ` itself as its only posterior.
Source: `anticipation.md` AN-9 ("on `B₁` the only posterior is `ν` (one atom)")
Kind: P
Fidelity: exact
Hyps: (a) `occ(d) = ⊤` -/
theorem occOnly_posterior_of_occ_univ (hocc : occ d B = Finset.univ) (P' : PMF B.Leaves)
    (hP : OccOnlyPosterior C B d P') : P' = runPMF C B := by
  obtain ⟨ev, hpos, hP'⟩ := hP
  have hat : ∀ ℓ, evAtom (occ d B) ℓ = true := by intro ℓ; simp [evAtom, hocc]
  by_cases ht : true ∈ ev
  · have hu : evAtom (occ d B) ⁻¹' ev = Set.univ := by
      ext ℓ; simp [hat, ht]
    rw [hP', condOn_congr _ hu hpos]
    exact condOn_univ _ _
  · have hu : evAtom (occ d B) ⁻¹' ev = ∅ := by
      ext ℓ; simp [hat, ht]
    rw [hu, mass_empty] at hpos
    exact absurd hpos (lt_irrefl 0)

end general

section tnv1

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)

/-- **`occ(d_E)ᶜ = λ⁻¹O_F` on V1**: the runs that do not consult `d_E` are exactly the full-box
runs. Source: `anticipation.md` AN-9 (the TN-V1 cell, via `tnV1_occ_E_eq`). Kind: L -/
theorem tnV1_occ_E_compl :
    (occ .E (tnV1 p h0 h1 L S))ᶜ = worldEv (tnV1 p h0 h1 L S) (tnObs .F) := by
  rw [tnV1_occ_E_eq]
  ext ℓ
  simp only [Finset.mem_compl, worldEv, Finset.mem_filter, Finset.mem_univ, true_and, tnObs]
  simp

/-- `ν(O_F) > 0` for `tnHalf` on V1. Source: none: infrastructure. Kind: L -/
theorem tnV1_half_nu_F_pos : 0 < nu tnHalf (tnV1 p h0 h1 L S) (tnObs .F) := by
  rw [tnV1_half_nu_F]; norm_num

/-- **AN-9's "too permissive" cell on TN-V1 (N+)**: the hypothesis package of
`occOnly_compl_reaches` at `d = d_E`, `O = O_F`, `C = tnHalf` is inhabited — `occ(d_E)ᶜ = λ⁻¹O_F`
exactly and `ν(O_F) = ½ > 0` — so the occurrence-only refinement at `d_E` has the posterior
`μ(· | occ(d_E)ᶜ)` whose pushdown is **`d_F`'s** strict-OC state: `d_F`'s observation is recovered
through `d_E`'s non-consultation. The mandate's sentence has the roles swapped — it reads
`occ(d_F)ᶜ = λ⁻¹O_E`, which is false on V1 where `occ(d_F) = ⊤` (`tnV1_occ_F`); the roles here
are as V1's occurrence structure has them, and the cell is AN-9's "at `d_F`, via `d_E`'s
non-consultation" with the point relabelled (same event, same posterior; audit r2 fidelity N1).
The SC-level conclusion is
`occOnly_compl_reaches tnHalf (tnV1 …) .E (tnObs .F) h.1 h.2 _`; it is not restated here because
elaborating `condOn (runPMF C B) (evAtom (occ .E B) ⁻¹' {false})` at the concrete `TnPt`/`Box`
types times out (module docstring).
Source: `anticipation.md` AN-9; mandate T7(b)
Kind: N+
Fidelity: exact -/
theorem tnV1_half_occOnly_package :
    (occ .E (tnV1 p h0 h1 L S))ᶜ = worldEv (tnV1 p h0 h1 L S) (tnObs .F) ∧
      0 < nu tnHalf (tnV1 p h0 h1 L S) (tnObs .F) :=
  ⟨tnV1_occ_E_compl p h0 h1 L S, tnV1_half_nu_F_pos p h0 h1 L S⟩

end tnv1

section tys

/-- **`occ(d₁₀)ᶜ = λ⁻¹O₅` on Told-You-So**: the runs that never consult `d₁₀` are exactly the
`(5,5)` run (the root's `five` branch), which is `O₅ = {n = 5}` as a world event.
Source: `anticipation.md` AN-9 (the Told-You-So cell); mandate T7(b) ("on `toldYouSo` the
`(5,5)` leaf likewise")
Kind: L -/
theorem tys_occ_ten_compl : (occ .ten toldYouSo)ᶜ = worldEv toldYouSo (tysObs .five) := by
  ext ℓ
  unfold toldYouSo at ℓ ⊢
  rcases ℓ with ⟨a, ℓ⟩
  cases a
  · simp [mem_occ, count_decision, worldEv, world_decision, tysObs]
  · rcases ℓ with ⟨b, ℓ⟩
    cases b <;> simp [mem_occ, count_decision, worldEv, world_decision, tysObs]

/-- `ν(O₅) = C(d₅)(5)` on Told-You-So. Source: none: infrastructure. Kind: L -/
theorem tys_nu_obs_five (C : Proc Five10 (fun _ => Five10) ℚ) :
    nu C toldYouSo (tysObs .five) = (C .five).w .five := by
  rw [tys_nu]; simp [tysObs]

/-- **AN-9's "too permissive" cell on Told-You-So (N+)**: the hypothesis package of
`occOnly_compl_reaches` at `d = d₁₀`, `O = O₅`, for every `C` with `C(d₅)(5) > 0` (every
full-support `C`, `procTake5`, `procFiveTen`, the uniform self-model) is inhabited —
`occ(d₁₀)ᶜ = λ⁻¹O₅` exactly and `ν(O₅) = C(d₅)(5) > 0` — so the occurrence-only refinement at
`d₁₀` has the posterior `μ(· | occ(d₁₀)ᶜ)` whose pushdown is **`d₅`'s** strict-OC state
`δ_{(5,5)}` (`tys_five_strictOCAt_of_pos`: that state is `s₅`): the `(5,5)` leaf's observation is
recovered through `d₁₀`'s non-consultation. The SC-level conclusion is
`occOnly_compl_reaches C toldYouSo .ten (tysObs .five) h.1 h.2 _`; it is not restated here for
the reason the module docstring gives for TN-V1 (concrete point/act types do not elaborate
inside `condOn (runPMF …)`).
Source: `anticipation.md` AN-9; mandate T7(b)
Kind: N+
Fidelity: exact
Hyps: (a) `0 < C(d₅)(5)` -/
theorem tys_occOnly_package (C : Proc Five10 (fun _ => Five10) ℚ) (h : 0 < (C .five).w .five) :
    (occ .ten toldYouSo)ᶜ = worldEv toldYouSo (tysObs .five) ∧
      0 < nu C toldYouSo (tysObs .five) :=
  ⟨tys_occ_ten_compl, by rw [tys_nu_obs_five]; exact h⟩

end tys

/-! ## The `B₁` cell: only `μ`, the tails-certain state not reached -/

section mug

variable (x y q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1)

set_option maxHeartbeats 400000 in
/-- **AN-9's `B₁` cell**: the occurrence-only refinement at `d` on `B₁` has only `μ` as a
posterior (`occ(d) = ⊤`), whose pushdown is `ν` — the tails-certain state is not reached: the
pushdown of every occurrence-only posterior differs from `P_{mugState1}` at `(H,⊥,1)`
(`mug1_reverse_ac_fails`).
Source: `anticipation.md` AN-9 ("on `B₁` the only posterior is `ν` (one atom) — the tails-certain
state fails"); audit r1 fidelity N5, adversarial N11
Kind: N+
Fidelity: exact -/
theorem mug1_occOnly_not_tailsCertain (P' : PMF (mug1 x y).Leaves)
    (hP : OccOnlyPosterior (procQ q₀ h0.le h1.le) (mug1 x y) () P') :
    P' = runPMF (procQ q₀ h0.le h1.le) (mug1 x y) ∧
      P'.map (world (mug1 x y)) ≠ toPMF (mugState1 x y q₀ h0.le h1.le).P := by
  have hμ := occOnly_posterior_of_occ_univ (procQ q₀ h0.le h1.le) (mug1 x y) () (mug1_occ x y) P' hP
  refine ⟨hμ, ?_⟩
  rw [hμ, runPMF_map_world, pushdownDistr_leafDistr_eq_priorState_P, Ne, toPMF_eq_iff]
  intro h
  have := congrArg (fun P : FinDistr ℚ MugW => P.w .hOne) h
  rw [(mug1_reverse_ac_fails x y q₀ h0 h1).1] at this
  exact (mug1_reverse_ac_fails x y q₀ h0 h1).2.ne' this

end mug

end Cleanroom.Decision.DpFirstpersonSc
