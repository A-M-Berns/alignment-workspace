import Cleanroom.Decision.DpCartesianFrames.RelocWitnesses
import Cleanroom.Decision.DpCartesianFrames.Witnesses

/-!
# UN-6: relocation is not a Chu morphism lazily

Package `dp-cartesian-frames`, file 11 (T7(d)). Over the frames *derived from the catalogue
tree*: `Fr (mug1 x y)` (2 rows × 2 columns) and the coarsened lazy frame of the relocated
mugging `(mapWorlds fst).obj (Fr (relocRoot {()} (mug1 x y)))` (rows = the relocated tree's
policies, columns = one lazy coin per branch copy).

* `fr_relocRoot_outcome_slice`: the outcome of the lazy relocated frame at `(ρ, ε')` depends on
  `ε'` only through its slice at `ρ`'s root answer; on a diagonal slice it is the original
  run's world (generalizes `fr_relocRoot_outcome_diag`).
* `leafMapW_decision_mem`, `leafMapW_twoBranch`: the leaf map of a resolved leaf takes edge `σ`
  at a relocated node; on a two-branch tree it is `⟨coin, ⟨σ, ()⟩⟩`. Hence the world at
  `(ρ, ε')` is `mugWorld1 (coin of ε' at σ_ρ) (σ_ρ)` for **every** lazy column
  (`relocMug_world`).
* **UN-6, no unit** (`isEmpty_hom_fr_mug1_to_lazyReloc`): there is no Chu morphism
  `Fr B₁ ⟶ (mapWorlds fst).obj (Fr (Rel_d B₁))` — if the images of pay and refuse choose
  different branch copies, the column with tails in the first and heads in the second
  contradicts adjointness; if the same copy, both rows record one choice while pay and refuse
  record different ones. A case analysis, not an enumeration (rule 8).
* **UN-6, counit** (`hom_lazyReloc_to_fr_mug1_eq_counit`): every Chu morphism backward is the
  diagonal `counitHom` (both coin copies must read the original coin; the row map is forced).
* **UN-19** (`un19_square_mug1`, repair round 1): the square commutes under identification
  (UN-7's instance), lazily the frames are not even `≃ᵇ` (`not_biextEquiv_fr_mug1_lazyReloc`),
  and the backward morphism is unique — the composition T7(e) asks for.

Scope (from the source): a **lazy**-convention fact about the mugging; under identification
UN-7 makes the frames equivalent and the no-unit statement is false there.
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames CategoryTheory
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc

section general

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  (U : Finset ι)

omit [∀ d, DecidableEq (acts d)] in
/-- The outcome of the lazy relocated frame at `(ρ, ε')` reads only the slice of `ε'` at the
root answer `ρ (inr ())`; on a diagonal slice it is the original run's stamped world.
Source: fair-repair FR-7(a); universal UN-6 (line 69: "the pay row reads the first copy, the
refuse row the second")
Kind: P
Fidelity: exact
Hyps: none -/
theorem fr_relocRoot_outcome_slice (B : Tree Ω ι acts K) (ρ : (p : ι ⊕ Unit) → actsR acts U p)
    (ε' : ChanceProfile (relocRoot U B)) (ε₀ : ChanceProfile B)
    (h : ε' (ρ (.inr ())) = diagProfile U (ρ (.inr ())) B ε₀) :
    (Fr (relocRoot U B)).outcome ρ ε' =
      ((world B (runLeaf (toPolicy U (ρ (.inr ())) ρ) B ε₀), ρ (.inr ())),
        payoff B (runLeaf (toPolicy U (ρ (.inr ())) ρ) B ε₀)) := by
  show (world (resolveW U (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) B)
      (runLeaf ρ (resolveW U (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) B) (ε' (ρ (.inr ())))),
    payoff (resolveW U (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) B)
      (runLeaf ρ (resolveW U (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) B) (ε' (ρ (.inr ()))))) = _
  rw [h, world_resolveW, payoff_resolveW, diagProfile_spec]

omit [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] in
/-- The leaf map of a resolved leaf takes the edge `σ` at a relocated decision node.
Source: fair-repair FR-6 ("leaf of branch `(a_d)_d` below a resolved `U`-node ↦ the `B`-leaf
below that node's chosen edges")
Kind: L -/
theorem leafMapW_decision_mem {Ω' : Type} (g : Ω → Ω') (σ : (d : ↥U) → acts d) {d : ι}
    (h : d ∈ U) (child : acts d → Tree Ω ι acts K) :
    ∀ ℓ' : (resolveW U g σ (.decision d child)).Leaves,
      ∃ ℓ'' : (child (σ ⟨d, h⟩)).Leaves,
        leafMapW U g σ (.decision d child) ℓ' = ⟨σ ⟨d, h⟩, ℓ''⟩ := by
  unfold resolveW leafMapW
  rw [resolveAux_decision, dif_pos h]
  dsimp only
  intro ℓ'
  exact ⟨_, rfl⟩

end general

section mug

/-- The relocated point of a one-point tree, as an element of `↥U1`.
Source: none: infrastructure
Kind: D -/
def u1 : ↥U1 := ⟨(), Finset.mem_singleton.mpr rfl⟩

/-- On a two-branch tree resolved at its single point, the leaf map sends every resolved leaf to
`⟨coin, ⟨σ, ()⟩⟩`.
Source: none: infrastructure
Kind: L -/
theorem leafMapW_twoBranch {Ω A : Type} [Fintype A] [DecidableEq A] {Ω' : Type} (g : Ω → Ω')
    (σ : (d : ↥U1) → A) (β : FinDistr ℚ (Fin 2)) (φ : Fin 2 → A → Ω × ℚ) :
    ∀ ℓ' : (resolveW U1 g σ (twoBranch β φ)).Leaves,
      leafMapW U1 g σ (twoBranch β φ) ℓ' = ⟨ℓ'.1, ⟨σ u1, ()⟩⟩ := by
  rintro ⟨i, ℓ₂⟩
  obtain ⟨ℓ₃, h₃⟩ := leafMapW_decision_mem (acts := fun _ : Unit => A) U1 g σ
    (Finset.mem_singleton.mpr rfl) (fun a => Tree.leaf (φ i a).1 (φ i a).2) ℓ₂
  show (⟨i, leafMapW (acts := fun _ : Unit => A) U1 g σ
    (Tree.decision (acts := fun _ : Unit => A) () fun a => Tree.leaf (φ i a).1 (φ i a).2) ℓ₂⟩ :
    (twoBranch β φ).Leaves) = ⟨i, ⟨σ u1, ()⟩⟩
  rw [h₃]
  obtain ⟨⟩ := ℓ₃
  rfl

/-- The coin coordinate of a profile of the resolved mugging (the slice's first component).
Source: none: infrastructure
Kind: D -/
def sliceCoin (x y : ℚ) (σ : (d : ↥U1) → Act2) (ε : ChanceProfile (resolve U1 σ (mug1 x y))) :
    Fin 2 :=
  Prod.fst (ε : Fin 2 × _)

/-- **The world of the lazy relocated mugging at any column**: the run of `ρ` reads the copy
in branch `σ_ρ := ρ (inr ())`, whose coin is the slice's coin, and records `σ_ρ`'s choice.
Source: universal UN-6 (line 69)
Kind: P
Fidelity: exact
Hyps: none -/
theorem relocMug_world (x y : ℚ) (ρ : (p : Unit ⊕ Unit) → actsR (fun _ => Act2) U1 p)
    (ε' : ChanceProfile (relocRoot U1 (mug1 x y))) :
    ((Fr (relocRoot U1 (mug1 x y))).outcome ρ ε').1.1 =
      mugWorld1 (sliceCoin x y (ρ (.inr ())) (ε' (ρ (.inr ())))) (ρ (.inr ()) u1) := by
  show (world (resolveW U1 (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ()))
      (twoBranch FinDistr.fair (mugφ x y)))
    (runLeaf ρ (resolveW U1 (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ()))
      (twoBranch FinDistr.fair (mugφ x y))) (ε' (ρ (.inr ()))))).1 = _
  rw [world_resolveW, leafMapW_twoBranch]
  rfl

/-- The world of `Fr (mug1 x y)` at `(π, ε)`.
Source: none: infrastructure
Kind: L -/
theorem fr_mug1_world (x y : ℚ) (π : Unit → Act2) (ε : ChanceProfile (mug1 x y)) :
    ((Fr (mug1 x y)).outcome π ε).1 = mugWorld1 ε.1 (π ()) := rfl

theorem sliceCoin_diagProfile (x y : ℚ) (σ : (d : ↥U1) → Act2) (ε₀ : ChanceProfile (mug1 x y)) :
    sliceCoin x y σ (diagProfile U1 σ (mug1 x y) ε₀) = ε₀.1 := by
  have h := diagProfile_spec U1 σ (mug1 x y) ε₀ (liftFun U1 fun _ => Act2.a)
  have h2 := leafMapW_twoBranch (fun ω => (ω, σ)) σ FinDistr.fair (mugφ x y)
    (runLeaf (liftFun U1 fun _ => Act2.a)
      (resolveW U1 (fun ω => (ω, σ)) σ (twoBranch FinDistr.fair (mugφ x y)))
      (diagProfile U1 σ (mug1 x y) ε₀))
  exact congrArg Sigma.fst (h2.symm.trans h)

/-- **UN-6, no unit**: there is no Chu morphism from `Fr B₁` to the coarsened lazy frame of the
relocated mugging, for every `x`, `y`.
Source: universal UN-6 (line 69: "0 Chu morphisms `Fr(B₁) → Fr(Rel_d B₁)`"); mandate T7(d)
Kind: N+
Fidelity: exact (lazy convention; every `x`, `y`; a case analysis rather than the source's
64-table enumeration) -/
theorem isEmpty_hom_fr_mug1_to_lazyReloc (x y : ℚ) :
    IsEmpty (Fr (mug1 x y) ⟶
      (Frame.mapWorlds (Prod.map Prod.fst id)).obj (Fr (relocRoot U1 (mug1 x y)))) := by
  classical
  constructor
  intro φ
  let σa := φ.agent (fun _ => Act2.a) (.inr ())
  let σb := φ.agent (fun _ => Act2.b) (.inr ())
  -- a profile of the relocated tree whose slice at σa is tails and elsewhere heads
  let ε' : ChanceProfile (relocRoot U1 (mug1 x y)) := fun σ =>
    if σ = σa then diagProfile U1 σ (mug1 x y) (mugεT x y)
    else diagProfile U1 σ (mug1 x y) (mugεH x y)
  have ha := congrArg (fun w => w.1) (φ.adjoint (fun _ => Act2.a) ε')
  have hb := congrArg (fun w => w.1) (φ.adjoint (fun _ => Act2.b) ε')
  change ((Fr (mug1 x y)).outcome (fun _ => Act2.a) (φ.env ε')).1 =
    ((Fr (relocRoot U1 (mug1 x y))).outcome (φ.agent fun _ => Act2.a) ε').1.1 at ha
  change ((Fr (mug1 x y)).outcome (fun _ => Act2.b) (φ.env ε')).1 =
    ((Fr (relocRoot U1 (mug1 x y))).outcome (φ.agent fun _ => Act2.b) ε').1.1 at hb
  rw [fr_mug1_world, relocMug_world] at ha hb
  have hεa : ε' σa = diagProfile U1 σa (mug1 x y) (mugεT x y) := by
    show (if σa = σa then _ else _) = _
    rw [if_pos rfl]
  rw [hεa, sliceCoin_diagProfile] at ha
  dsimp only [mugεT] at ha
  by_cases hs : φ.agent (fun _ => Act2.b) (.inr ()) = φ.agent (fun _ => Act2.a) (.inr ())
  · have hεb : ε' σb = diagProfile U1 σb (mug1 x y) (mugεT x y) := by
      show (if σb = σa then _ else _) = _
      rw [if_pos hs]
    rw [hεb, sliceCoin_diagProfile] at hb
    dsimp only [mugεT] at hb
    rw [hs] at hb
    revert ha hb
    generalize (φ.env ε').1 = c
    generalize φ.agent (fun _ => Act2.a) (.inr ()) u1 = s
    fin_cases c <;> cases s <;> decide
  · have hεb : ε' σb = diagProfile U1 σb (mug1 x y) (mugεH x y) := by
      show (if σb = σa then _ else _) = _
      rw [if_neg hs]
    rw [hεb, sliceCoin_diagProfile] at hb
    dsimp only [mugεH] at hb
    revert ha hb
    generalize (φ.env ε').1 = c
    generalize φ.agent (fun _ => Act2.a) (.inr ()) u1 = s₁
    generalize φ.agent (fun _ => Act2.b) (.inr ()) u1 = s₂
    fin_cases c <;> cases s₁ <;> cases s₂ <;> decide

/-- Two profiles of the resolved mugging with the same coin are equal (the rest of a profile
is a function into `Unit`).
Source: none: infrastructure
Kind: L -/
theorem resolveMug_profile_ext (x y : ℚ) (σ : (d : ↥U1) → Act2)
    (ε₁ ε₂ : ChanceProfile (resolve U1 σ (mug1 x y)))
    (h : sliceCoin x y σ ε₁ = sliceCoin x y σ ε₂) : ε₁ = ε₂ := by
  have hsub : ∀ i : Fin 2, Subsingleton (ChanceProfile (resolveW U1 (fun ω => (ω, σ)) σ
      (Tree.decision (acts := fun _ : Unit => Act2) () fun act =>
        Tree.leaf (mugWorld1 i act) (mugPay x y (mugWorld1 i act))))) := by
    intro i
    unfold resolveW
    rw [resolveAux_decision, dif_pos (Finset.mem_singleton.mpr rfl)]
    dsimp only
    show Subsingleton Unit
    infer_instance
  exact Prod.ext h (funext fun i => (hsub i).elim _ _)

/-- **UN-6, the counit is the only morphism backward**: every Chu morphism from the coarsened
lazy relocated frame to `Fr B₁` is `counitHom` — the row map is forced by the recorded choice
and both coin copies must read the original coin.
Source: universal UN-6 (line 69: "exactly 1 back (`g = id`, `h(c) = (c, c)` — CF-24's diagonal
Assume)"); mandate T7(d)
Kind: N+
Fidelity: exact (uniqueness as equality of `Hom` structures; existence is `counitHom`) -/
theorem hom_lazyReloc_to_fr_mug1_eq_counit (x y : ℚ)
    (ψ : (Frame.mapWorlds (Prod.map Prod.fst id)).obj (Fr (relocRoot U1 (mug1 x y))) ⟶
      Fr (mug1 x y)) : ψ = counitHom U1 (mug1 x y) := by
  -- the coin of ψ.env ε at every slice is ε's coin, and the row map records σ_ρ's choice
  have key : ∀ (ρ : (p : Unit ⊕ Unit) → actsR (fun _ => Act2) U1 p) (ε : ChanceProfile (mug1 x y)),
      mugWorld1 (sliceCoin x y (ρ (.inr ())) (ψ.env ε (ρ (.inr ())))) (ρ (.inr ()) u1) =
        mugWorld1 ε.1 (ψ.agent ρ ()) := by
    intro ρ ε
    have h := congrArg (fun w => w.1) (ψ.adjoint ρ ε)
    change ((Fr (relocRoot U1 (mug1 x y))).outcome ρ (ψ.env ε)).1.1 =
      ((Fr (mug1 x y)).outcome (ψ.agent ρ) ε).1 at h
    rw [relocMug_world, fr_mug1_world] at h
    exact h
  have hcoin : ∀ (σ : (d : ↥U1) → Act2) (ε : ChanceProfile (mug1 x y)),
      sliceCoin x y σ (ψ.env ε σ) = ε.1 := by
    intro σ ε
    have h := key (liftFun U1 fun _ => σ u1) ε
    have hσ : (liftFun U1 fun _ => σ u1) (.inr ()) = σ := funext fun d => by
      show σ u1 = σ d
      exact congrArg σ (Subtype.ext rfl)
    rw [hσ] at h
    revert h
    generalize sliceCoin x y σ (ψ.env ε σ) = c
    generalize ε.1 = c'
    generalize ψ.agent (liftFun U1 fun _ => σ u1) () = s'
    generalize σ u1 = s
    fin_cases c <;> fin_cases c' <;> cases s <;> cases s' <;> decide
  have hagent : ∀ ρ, ψ.agent ρ () = ρ (.inr ()) u1 := by
    intro ρ
    have h := key ρ (mugεT x y)
    rw [hcoin] at h
    dsimp only [mugεT] at h
    revert h
    generalize ρ (.inr ()) u1 = s
    generalize ψ.agent ρ () = s'
    cases s <;> cases s' <;> decide
  apply Frame.Hom.ext
  · funext ρ
    funext u
    cases u
    rw [hagent]
    show ρ (.inr ()) u1 = toPolicy U1 (ρ (.inr ())) ρ ()
    simp [toPolicy, u1]
  · funext ε
    funext σ
    exact resolveMug_profile_ext x y σ _ _ ((hcoin σ ε).trans (sliceCoin_diagProfile x y σ ε).symm)

/-- **Lazily the frames are not even biextensionally equivalent** (a homotopy equivalence would
contain a Chu morphism `Fr B₁ ⟶ (mapWorlds fst).obj (Fr (Rel_d B₁))`, and there is none).
Source: universal UN-19 (line 95: "Exact gap without the convention: … an inclusion of
environments (the unique morphism, UN-6), not an isomorphism")
Kind: C
Fidelity: exact
Hyps: none -/
theorem not_biextEquiv_fr_mug1_lazyReloc (x y : ℚ) :
    ¬ (Fr (mug1 x y) ≃ᵇ
      (Frame.mapWorlds (Prod.map Prod.fst id)).obj (Fr (relocRoot U1 (mug1 x y)))) :=
  fun h => (isEmpty_hom_fr_mug1_to_lazyReloc x y).false
    (Frame.biextEquiv_iff_homotopyEquiv.mp h).choose

/-- **UN-19, the commuting square and its exact gap** (T7(e), the composition of UN-7 and
UN-6 on the mugging): under chance identification plus stamp coarsening `Fr ∘ Rel_U ≃ᵇ Fr`
(here the instance on `B₁`; `mapWorlds_frIdent_biextEquiv_fr` is the general statement for
every `B`, `U`); without the convention the lazy relocated frame is not `≃ᵇ Fr B₁`, and
`Fr B₁` is recovered only through the unique backward morphism, the diagonal counit.
Source: universal UN-19 (line 95); mandate T7(e) ("UN-19 is (b) plus (d): record as `C`")
Kind: C
Fidelity: exact (on the mugging; the identified half holds for every tree by UN-7)
Hyps: none -/
theorem un19_square_mug1 (x y : ℚ) :
    ((Frame.mapWorlds (Prod.map Prod.fst id)).obj (FrIdent U1 (mug1 x y)) ≃ᵇ Fr (mug1 x y)) ∧
    ¬ (Fr (mug1 x y) ≃ᵇ
      (Frame.mapWorlds (Prod.map Prod.fst id)).obj (Fr (relocRoot U1 (mug1 x y)))) ∧
    ∀ ψ : (Frame.mapWorlds (Prod.map Prod.fst id)).obj (Fr (relocRoot U1 (mug1 x y))) ⟶
      Fr (mug1 x y), ψ = counitHom U1 (mug1 x y) :=
  ⟨mapWorlds_frIdent_biextEquiv_fr U1 (mug1 x y), not_biextEquiv_fr_mug1_lazyReloc x y,
    hom_lazyReloc_to_fr_mug1_eq_counit x y⟩

end mug

end Cleanroom.Decision.DpCartesianFrames
