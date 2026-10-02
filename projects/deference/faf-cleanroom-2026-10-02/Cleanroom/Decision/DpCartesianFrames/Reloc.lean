import Cleanroom.Decision.DpCartesianFrames.Profiles
import Cleanroom.Decision.DpFairnessReloc.Output

/-!
# Relocation and the frame: the identified frame and UN-7

Package `dp-cartesian-frames`, file 5 (T7, headline 4; T8(a)'s consequence). Over
`dp-fairness-reloc`'s `relocRoot U B = decision (inr ()) (fun σ => resolve U σ B)`.

* `toPolicy U σ ρ`: the policy of `B` induced by a policy `ρ` of the relocated tree whose root
  answer is `σ` — `σ` at the relocated points, `ρ (inl d)` at the survivors.
* **`exists_diag`** (the pointwise form of FR-7(a), the real lemma): every profile `ε` of `B`
  has a *diagonal* profile of `resolve U σ B` — one under which, for **every** policy `ρ`, the
  relocated run lands on the copy (`leafMapW`) of the leaf the original run of `toPolicy U σ ρ`
  reaches under `ε`. Proved by the `resolveAux` induction.
* **`FrIdent U B`** (the *identified* seeding, CFF-A/D.2, defined only on relocation outputs):
  `(Fr (relocRoot U B)).assume (range diag)` — the lazy frame of the relocated tree restricted to
  the diagonal columns `diag ε := fun σ => diagProfile σ ε`. So **CFF-1** (`frIdent_eq_assume_diag`)
  is a definition here (`D`), as the mandate allows; what is a theorem is that the diagonal
  columns exist and read as the original's profiles (`fr_relocRoot_outcome_diag`).
* **UN-7 / ZO-5(a) / CFF-2(a)** (`mapWorlds_frIdent_biextEquiv_fr`, headline 4): after
  coarsening the `pol` stamps away, `FrIdent U B ≃ᵇ Fr B` for **every** tree `B` and every
  `U` (nested fibers allowed), through the homotopy equivalence `ρ ↦ toPolicy`, `π ↦ liftFun π`
  on rows (surjective, not injective — survivors in `U` carry inert coordinates — so `≃ᵇ`, not
  `≅`) and the diagonal on columns.
* The general Chu morphism `(mapWorlds fst).obj (Fr (relocRoot U B)) ⟶ Fr B` (the "counit",
  UN-6's backward morphism, for every `B`, `U`), and T8(a)'s consequence: identification only
  adds observability (`observable2_frIdent_of_fr_relocRoot`).

Seeding disclosure: `Fr (relocRoot U B)` is lazy (one coordinate per chance node *of the
relocated tree*, copies independent); `FrIdent U B` identifies the copies of each original
chance node.
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames CategoryTheory
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

section reloc

variable [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] (U : Finset ι)

/-- The policy of `B` induced by a policy `ρ` of the relocated tree whose root answer is `σ`:
`σ` at the relocated points, `ρ (inl d)` at the survivors.
Source: universal UN-7 proof (line 71: "`∏_{d∈U} A_d × ∏_{e∉U} A_e` is canonically `Fr(B)`'s
agent set")
Kind: D -/
def toPolicy (σ : (d : ↥U) → acts d) (ρ : (p : ι ⊕ Unit) → actsR acts U p) : (d : ι) → acts d :=
  fun d => if h : d ∈ U then σ ⟨d, h⟩ else ρ (.inl d)

omit [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] in
/-- `toPolicy` is a left inverse of `dp-fairness-reloc`'s `liftFun`.
Source: none: infrastructure
Kind: L -/
theorem toPolicy_liftFun (π : (d : ι) → acts d) :
    toPolicy U (liftFun U π (.inr ())) (liftFun U π) = π := by
  funext e
  unfold toPolicy
  split <;> rfl

omit [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] in
/-- **Existence of the diagonal profile** (FR-7(a), pointwise): every profile `ε` of `B` has a
profile `ε'` of `resolve U σ B` (worlds mapped by any `g`) under which, for every policy `ρ`
of the relocated tree, the relocated run's leaf maps to the leaf of the original run of
`toPolicy U σ ρ` under `ε`: a copied chance node reads its original's coordinate, and a
relocated decision node is resolved to `σ`, which is what `toPolicy` answers there.
Source: fair-repair FR-7(a) via universal UN-7 (line 71: "copies read the original coordinate
(FR-7(a) pointwise)"); zoo ZO-5(a) (line 69)
Kind: P
Fidelity: exact
Hyps: none -/
theorem exists_diag {Ω' : Type} (g : Ω → Ω') (σ : (d : ↥U) → acts d) :
    (B : Tree Ω ι acts K) → ∀ ε : ChanceProfile B, ∃ ε' : ChanceProfile (resolveW U g σ B),
      ∀ ρ : (p : ι ⊕ Unit) → actsR acts U p,
        leafMapW U g σ B (runLeaf ρ (resolveW U g σ B) ε') = runLeaf (toPolicy U σ ρ) B ε
  | .leaf _ _, _ => ⟨(), fun _ => rfl⟩
  | .chance n β child, ε => by
      unfold resolveW leafMapW; rw [resolveAux_chance]; dsimp only
      choose ε' hε' using fun i => exists_diag g σ (child i) (ε.2 i)
      refine ⟨(ε.1, ε'), fun ρ => ?_⟩
      exact congrArg (Sigma.mk ε.1) (hε' ε.1 ρ)
  | .decision d child, ε => by
      unfold resolveW leafMapW; rw [resolveAux_decision]
      by_cases h : d ∈ U
      · rw [dif_pos h]; dsimp only
        obtain ⟨ε', hε'⟩ := exists_diag g σ (child (σ ⟨d, h⟩)) (ε (σ ⟨d, h⟩))
        refine ⟨ε', fun ρ => ?_⟩
        have hd : toPolicy U σ ρ d = σ ⟨d, h⟩ := by simp [toPolicy, h]
        rw [runLeaf_decision, hd]
        exact congrArg (Sigma.mk _) (hε' ρ)
      · rw [dif_neg h]; dsimp only
        choose ε' hε' using fun a => exists_diag g σ (child a) (ε a)
        refine ⟨ε', fun ρ => ?_⟩
        have hd : toPolicy U σ ρ d = ρ (.inl d) := by simp [toPolicy, h]
        rw [runLeaf_decision, runLeaf_decision, hd]
        exact congrArg (Sigma.mk _) (hε' (ρ (.inl d)) ρ)

/-- A chosen diagonal profile of `resolve U σ B` for `ε` (any choice gives the same outcomes,
by `diagProfile_spec`).
Source: adversary-repair D.2 / cf-frontier CFF-A (line 46: "copies inherit their original's
variable")
Kind: D -/
noncomputable def diagProfile (σ : (d : ↥U) → acts d) (B : Tree Ω ι acts K)
    (ε : ChanceProfile B) : ChanceProfile (resolve U σ B) :=
  Classical.choose (exists_diag U (fun ω => (ω, σ)) σ B ε)

omit [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] in
theorem diagProfile_spec (σ : (d : ↥U) → acts d) (B : Tree Ω ι acts K) (ε : ChanceProfile B)
    (ρ : (p : ι ⊕ Unit) → actsR acts U p) :
    leafMapW U (fun ω => (ω, σ)) σ B
        (runLeaf ρ (resolveW U (fun ω => (ω, σ)) σ B) (diagProfile U σ B ε)) =
      runLeaf (toPolicy U σ ρ) B ε :=
  Classical.choose_spec (exists_diag U (fun ω => (ω, σ)) σ B ε) ρ

/-- The diagonal map on profiles of the relocated tree: every copy of a chance node of `B`
that some run reads, reads the original's coordinate (`diagProfile_spec`); the coordinates of
the copies no run reads are a choice (`Classical.choose`), so `diag U B ε = diag U B ε'`
exactly when `ε` and `ε'` give the same leaf under every pure policy (`diag_eq_iff`,
`Diag.lean`) — the map is not injective, for any `U`, as soon as some chance node sits below
an unchosen chance branch (`not_injective_diag_twoCoins`).
Source: cf-frontier CFF-1 (line 60: "`Δ_κ` = lazy profiles constant on each class")
Kind: D -/
noncomputable def diag (B : Tree Ω ι acts K) (ε : ChanceProfile B) :
    ChanceProfile (relocRoot U B) :=
  fun σ => diagProfile U σ B ε

/-- **The identified frame of a relocation output**: the lazy frame of `relocRoot U B`
restricted to the diagonal columns (one per original profile). Agent: the relocated tree's own
policies (`(p : ι ⊕ Unit) → actsR acts U p`); worlds `RW Ω acts U × K` carry the `pol` stamps.
Defined as the diagonal `assume`, so **CFF-1 is definitional here** (`frIdent_eq_assume_diag`,
Kind `D`); the theorem content is `exists_diag`/`fr_relocRoot_outcome_diag`.
Source: adversary-repair D.2; cf-frontier CFF-A (line 46), CFF-1 (line 60); mandate §3
Kind: D
Fidelity: variant: the identified seeding as a sub-environment of the lazy relocated frame
(the composite option of mandate §3), columns indexed by a chosen diagonal profile per
original profile -/
noncomputable def FrIdent (B : Tree Ω ι acts K) : CartesianFrames.Frame (RW Ω acts U × K) :=
  (Fr (relocRoot U B)).assume (Set.range (diag U B))

omit [∀ d, DecidableEq (acts d)] in
/-- **CFF-1**: the identified frame is the diagonal `assume` of the lazy one — by definition
in this package (disclosed: `D`, not `P`).
Source: cf-frontier CFF-1 (line 60)
Kind: D
Fidelity: exact (definitional) -/
theorem frIdent_eq_assume_diag (B : Tree Ω ι acts K) :
    FrIdent U B = (Fr (relocRoot U B)).assume (Set.range (diag U B)) := rfl

omit [∀ d, DecidableEq (acts d)] in
/-- **The outcome of the relocated tree on a diagonal column**: the original run's world stamped
with the root answer, and its payoff.
Source: fair-repair FR-7(a) (via `dp-fairness-reloc`'s `world_resolveW`, `payoff_resolveW`);
universal UN-7 (line 71)
Kind: P
Fidelity: exact
Hyps: none -/
theorem fr_relocRoot_outcome_diag (B : Tree Ω ι acts K) (ρ : (p : ι ⊕ Unit) → actsR acts U p)
    (ε : ChanceProfile B) :
    (Fr (relocRoot U B)).outcome ρ (diag U B ε) =
      ((world B (runLeaf (toPolicy U (ρ (.inr ())) ρ) B ε), ρ (.inr ())),
        payoff B (runLeaf (toPolicy U (ρ (.inr ())) ρ) B ε)) := by
  show (world (resolveW U (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) B)
      (runLeaf ρ (resolveW U (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) B)
        (diagProfile U (ρ (.inr ())) B ε)),
    payoff (resolveW U (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) B)
      (runLeaf ρ (resolveW U (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) B)
        (diagProfile U (ρ (.inr ())) B ε))) = _
  rw [world_resolveW, payoff_resolveW, diagProfile_spec]

omit [∀ d, DecidableEq (acts d)] in
/-- **UN-7 / ZO-5(a) / CFF-2(a)** (headline 4): for every tree `B` and every `U` (nested fibers
allowed), the identified frame of the relocation output, with the `pol` stamps coarsened away,
is biextensionally equivalent to the lazy frame of `B`. Rows: `ρ ↦ toPolicy` (surjective — a
full profile on the output determines one on `B` — not injective, since survivors in `U`
carry inert coordinates; the collapse handles the duplicates); columns: the diagonal;
outcomes: `fr_relocRoot_outcome_diag`. A `≃ᵇ`, not an `≅` (CFF-2 "literally for every `U`" is
dead, ZO-5(b)).
Source: universal UN-7 (line 71); zoo ZO-5(a) (line 69); cf-frontier CFF-2(a) (line 62);
mandate T7(b)
Kind: P
Fidelity: exact
Hyps: none -/
theorem mapWorlds_frIdent_biextEquiv_fr (B : Tree Ω ι acts K) :
    (Frame.mapWorlds (Prod.map Prod.fst id)).obj (FrIdent U B) ≃ᵇ Fr B := by
  refine Frame.biextEquiv_iff_homotopyEquiv.mpr ⟨?_, ?_, ?_, ?_⟩
  · exact
      { agent := fun ρ => toPolicy U (ρ (.inr ())) ρ
        env := fun ε => ⟨diag U B ε, ⟨ε, rfl⟩⟩
        adjoint := fun ρ ε => by
          show Prod.map Prod.fst id ((Fr (relocRoot U B)).outcome ρ (diag U B ε)) =
            (Fr B).outcome (toPolicy U (ρ (.inr ())) ρ) ε
          rw [fr_relocRoot_outcome_diag]
          rfl }
  · exact
      { agent := fun π => liftFun U π
        env := fun y => Classical.choose y.property
        adjoint := fun π y => by
          obtain ⟨ε', ε, hε⟩ := y
          subst hε
          have hy := Classical.choose_spec (⟨ε, rfl⟩ : diag U B ε ∈ Set.range (diag U B))
          show (Fr B).outcome π
              (Classical.choose (⟨ε, rfl⟩ : diag U B ε ∈ Set.range (diag U B))) =
            Prod.map Prod.fst id ((Fr (relocRoot U B)).outcome (liftFun U π) (diag U B ε))
          rw [← congrArg ((Fr (relocRoot U B)).outcome (liftFun U π)) hy,
            fr_relocRoot_outcome_diag, toPolicy_liftFun]
          rfl }
  · rintro ρ ⟨ε', ε, hε⟩
    subst hε
    simp only [Frame.id_env, Frame.comp_agent, Function.comp, id]
    show Prod.map Prod.fst id ((Fr (relocRoot U B)).outcome ρ (diag U B ε)) =
      Prod.map Prod.fst id
        ((Fr (relocRoot U B)).outcome (liftFun U (toPolicy U (ρ (.inr ())) ρ)) (diag U B ε))
    rw [fr_relocRoot_outcome_diag, fr_relocRoot_outcome_diag, toPolicy_liftFun]
    rfl
  · intro π ε
    simp only [Frame.id_env, Frame.comp_agent, Function.comp, id]
    show (Fr B).outcome π ε =
      (Fr B).outcome (toPolicy U (liftFun U π (.inr ())) (liftFun U π)) ε
    rw [toPolicy_liftFun]

/-- **The counit** (UN-6's backward morphism, in general): for every `B` and `U` there is a Chu
morphism from the coarsened lazy relocated frame to `Fr B` — `toPolicy` on rows, the diagonal
on columns (CF-24's "diagonal Assume" followed by coarsening).
Source: universal UN-6 (line 69: "the counit is CF's own morphism `C → Assume^F(C)` (id,
inclusion) at `F = Δ` followed by coarsening")
Kind: D
Fidelity: exact -/
noncomputable def counitHom (B : Tree Ω ι acts K) :
    (Frame.mapWorlds (Prod.map Prod.fst id)).obj (Fr (relocRoot U B)) ⟶ Fr B where
  agent := fun ρ => toPolicy U (ρ (.inr ())) ρ
  env := fun ε => diag U B ε
  adjoint := fun ρ ε => by
    show Prod.map Prod.fst id ((Fr (relocRoot U B)).outcome ρ (diag U B ε)) =
      (Fr B).outcome (toPolicy U (ρ (.inr ())) ρ) ε
    rw [fr_relocRoot_outcome_diag]
    rfl

omit [∀ d, DecidableEq (acts d)] in
/-- **Identification only adds observability** (CFF-1's takeaway, T8(a) at the relocation
output): a partition observable in the lazy relocated frame is observable in the identified
one, since the latter is an `assume` of the former.
Source: cf-frontier CFF-1 (line 60: "identification can only add observability, never remove it")
Kind: C
Fidelity: exact
Hyps: none -/
theorem observable2_frIdent_of_fr_relocRoot (B : Tree Ω ι acts K) (S : Set (RW Ω acts U × K))
    (h : Observable2 (Fr (relocRoot U B)) S) : Observable2 (FrIdent U B) S :=
  Observable2.assume h _

/-- The claimed observation of `d` on the stamped worlds of a relocation output:
`{((ω, σ), r) | ω ∈ O_d}`.
Source: cf-correspondence CF-2 (line 19), on `RW` worlds
Kind: D -/
def SOR (obs : ι → Finset Ω) (d : ι) : Set (RW Ω acts U × K) := {w | w.1.1 ∈ obs d}

end reloc

end Cleanroom.Decision.DpCartesianFrames
