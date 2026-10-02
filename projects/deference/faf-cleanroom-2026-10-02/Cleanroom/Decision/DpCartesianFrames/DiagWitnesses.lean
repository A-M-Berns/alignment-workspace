import Cleanroom.Decision.DpCartesianFrames.DiagStruct

/-!
# Witnesses for ZO-5(b): the 2-fold linear mugging, and the zero-mass variant (F20)

Package `dp-cartesian-frames`, file 22 (repair round 3, T7(c)).

* **UN-7 for the structural frame** (`mapWorlds_frIdentS_biextEquiv_fr`): the structural
  identified frame `FrIdentS U B` is biextensionally equivalent to `Fr B` for every `B`, `U`
  — the same proof as `mapWorlds_frIdent_biextEquiv_fr` with the structural diagonal in
  place of the chosen one. So `FrIdentS` carries UN-7 (headline 4) *and* ZO-5(b)/(c); it is
  the package's rendering of CFF-A's `Fr_κ(Rel_U B)`.
* **The 2-fold linear mugging** `zmTree β` (zoo ZO-5 "Numbers", line 72): a root coin `β`;
  tails → a leaf; heads → a `d`-node whose `a`-edge leads to a second `d`-node whose `b`-edge
  leads to a fair coin (the "transfer coin under the inconsistent sim path"), every other
  edge to a leaf. With `U = {d}`, the transfer coin sits below the inconsistently answered
  path `d:a, d:b`, so no `σ`-copy contains it and the structural diagonal forgets its
  coordinate: `diagStruct` is **not injective** (`zm_diagStruct_eq`, `notInjective_diagStruct_zm`,
  for every root coin `β`). This is ZO-5(b)'s "only if" on the source's own example
  (`Fr(B)` is `2 × 8`, the identified relocated frame `2 × 2`).
* **Which "nested" (findings F20).** With a *fair* root coin the tree is `Nested` in
  `dp-core-tree`'s positive-mass sense (`zm_fair_nested`) — the source's instance. With the
  root coin that puts **all its mass on tails** (`FinDistr.coin 1`), the heads branch has mass
  `0`, so `¬ Nested (zmTree (coin 1)) d` (`zm_zeroMass_not_nested`) while the fiber is still
  nested (`zm_nestedFiber`, any `β`) and `diagStruct` is still not injective. So the mandate's
  hypothesis `∀ d ∈ U, ¬ Nested B d` does **not** give ZO-5(c) on unpruned trees
  (`not_nested_insufficient`); the possibilistic `¬ NestedFiber` of
  `diagStruct_injective_of_not_nestedFiber` does.
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames CategoryTheory
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

section un7

variable [DecidableEq ι] [∀ d, Fintype (acts d)] (U : Finset ι)

/-- **UN-7 for the structural identified frame**: with the `pol` stamps coarsened away,
`FrIdentS U B ≃ᵇ Fr B` for every tree `B` and every `U` (nested fibers allowed) — the
structural counterpart of `mapWorlds_frIdent_biextEquiv_fr`, with the same maps.
Source: universal UN-7 (line 71); zoo ZO-5(a) (line 69); cf-frontier CFF-2(a) (line 62)
Kind: P
Fidelity: exact
Hyps: none -/
theorem mapWorlds_frIdentS_biextEquiv_fr (B : Tree Ω ι acts K) :
    (Frame.mapWorlds (Prod.map Prod.fst id)).obj (FrIdentS U B) ≃ᵇ Fr B := by
  refine Frame.biextEquiv_iff_homotopyEquiv.mpr ⟨?_, ?_, ?_, ?_⟩
  · exact
      { agent := fun ρ => toPolicy U (ρ (.inr ())) ρ
        env := fun ε => ⟨diagStruct U B ε, ⟨ε, rfl⟩⟩
        adjoint := fun ρ ε => by
          show Prod.map Prod.fst id ((Fr (relocRoot U B)).outcome ρ (diagStruct U B ε)) =
            (Fr B).outcome (toPolicy U (ρ (.inr ())) ρ) ε
          rw [fr_relocRoot_outcome_diagStruct]
          rfl }
  · exact
      { agent := fun π => liftFun U π
        env := fun y => Classical.choose y.property
        adjoint := fun π y => by
          obtain ⟨ε', ε, hε⟩ := y
          subst hε
          have hy := Classical.choose_spec
            (⟨ε, rfl⟩ : diagStruct U B ε ∈ Set.range (diagStruct U B))
          show (Fr B).outcome π
              (Classical.choose (⟨ε, rfl⟩ : diagStruct U B ε ∈ Set.range (diagStruct U B))) =
            Prod.map Prod.fst id
              ((Fr (relocRoot U B)).outcome (liftFun U π) (diagStruct U B ε))
          rw [← congrArg ((Fr (relocRoot U B)).outcome (liftFun U π)) hy,
            fr_relocRoot_outcome_diagStruct, toPolicy_liftFun]
          rfl }
  · rintro ρ ⟨ε', ε, hε⟩
    subst hε
    simp only [Frame.id_env, Frame.comp_agent, Function.comp, id]
    show Prod.map Prod.fst id ((Fr (relocRoot U B)).outcome ρ (diagStruct U B ε)) =
      Prod.map Prod.fst id
        ((Fr (relocRoot U B)).outcome (liftFun U (toPolicy U (ρ (.inr ())) ρ))
          (diagStruct U B ε))
    rw [fr_relocRoot_outcome_diagStruct, fr_relocRoot_outcome_diagStruct, toPolicy_liftFun]
    rfl
  · intro π ε
    simp only [Frame.id_env, Frame.comp_agent, Function.comp, id]
    show (Fr B).outcome π ε =
      (Fr B).outcome (toPolicy U (liftFun U π (.inr ())) (liftFun U π)) ε
    rw [toPolicy_liftFun]

end un7

/-! ### The 2-fold linear mugging -/

/-- The single relocated point.
Source: zoo ZO-5 "Numbers" (line 72: "2-fold linear mugging, `U = {d}`")
Kind: D -/
def zmU : Finset Unit := {()}

/-- `() ∈ zmU`.
Source: none: infrastructure
Kind: L -/
theorem mem_zmU : () ∈ zmU := Finset.mem_singleton_self ()

/-- The children of the inner `d`-node: `a` → a leaf; `b` → the transfer coin (a fair coin
over two leaves recording different worlds).
Source: zoo ZO-5 "Numbers" (line 72: "two transfer coins under the inconsistent sim paths")
Kind: D -/
def zmInnerChild : Act2 → Tree Bool Unit (fun _ => Act2) ℚ
  | .a => .leaf true 0
  | .b => .chance 2 FinDistr.fair ![.leaf true 0, .leaf false 0]

/-- The inner `d`-node.
Source: zoo ZO-5 "Numbers" (line 72)
Kind: D -/
def zmInner : Tree Bool Unit (fun _ => Act2) ℚ := .decision () zmInnerChild

/-- The children of the outer `d`-node: `a` → the inner `d`-node; `b` → a leaf.
Source: zoo ZO-5 "Numbers" (line 72)
Kind: D -/
def zmOuterChild : Act2 → Tree Bool Unit (fun _ => Act2) ℚ
  | .a => zmInner
  | .b => .leaf true 0

/-- The outer `d`-node.
Source: zoo ZO-5 "Numbers" (line 72)
Kind: D -/
def zmOuter : Tree Bool Unit (fun _ => Act2) ℚ := .decision () zmOuterChild

/-- **The 2-fold linear mugging with root coin `β`**: index `0` → a leaf; index `1` → the
outer `d`-node. The transfer coin lies below the path `d:a, d:b`, which no pure policy and no
`σ` answers consistently.
Source: zoo ZO-5 "Numbers" (line 72: "2-fold linear mugging, `U = {d}`: `Fr(B)` `2 × 8`
… relocated identified projected frame `2 × 2`; same-matrix False, biext True")
Kind: D
Fidelity: exact (the root coin is a parameter so that the fair and the zero-mass variants
are one tree) -/
def zmTree (β : FinDistr ℚ (Fin 2)) : Tree Bool Unit (fun _ => Act2) ℚ :=
  .chance 2 β ![.leaf true 0, zmOuter]

/-- A profile of the inner `d`-node whose transfer coin shows `j`.
Source: none: infrastructure
Kind: D -/
noncomputable def zmInnerProf (j : Fin 2) : ChanceProfile zmInner
  | .a => ()
  | .b => (j, fun _ => Classical.arbitrary _)

/-- A profile of the outer `d`-node whose transfer coin shows `j`.
Source: none: infrastructure
Kind: D -/
noncomputable def zmOuterProf (j : Fin 2) : ChanceProfile zmOuter
  | .a => zmInnerProf j
  | .b => ()

/-- A heads column of the 2-fold linear mugging whose transfer coin shows `j`.
Source: none: infrastructure
Kind: D -/
noncomputable def zmProf (β : FinDistr ℚ (Fin 2)) (j : Fin 2) : ChanceProfile (zmTree β) :=
  (1, Fin.cons (α := fun i : Fin 2 =>
      ChanceProfile (![(Tree.leaf true 0 : Tree Bool Unit (fun _ => Act2) ℚ), zmOuter] i))
    ()
    (Fin.cons (α := fun i : Fin 1 =>
        ChanceProfile (![(Tree.leaf true 0 : Tree Bool Unit (fun _ => Act2) ℚ), zmOuter] i.succ))
      (zmOuterProf j) (fun i => i.elim0)))

/-- The two heads columns differ as profiles: their transfer coins differ.
Source: none: infrastructure
Kind: L -/
theorem zmProf_ne (β : FinDistr ℚ (Fin 2)) : zmProf β 0 ≠ zmProf β 1 := by
  intro h
  have h' := congrArg (fun ε : ChanceProfile (zmTree β) => (ε.2 1 Act2.a Act2.b).1) h
  change (0 : Fin 2) = 1 at h'
  exact absurd h' (by decide)

/-- **The structural diagonal forgets the transfer coin**: the two heads columns have the same
structural diagonal column, for every `σ` — on the `σ = a` branch the inner node is resolved
to `a`, on `σ = b` the outer one is, and the transfer coin is copied by neither.
Source: zoo ZO-5(b) (line 70: "only if": the column index sets differ"), "Numbers" (line 72)
Kind: P
Fidelity: exact
Hyps: none -/
theorem zm_diagStruct_eq (β : FinDistr ℚ (Fin 2)) :
    diagStruct zmU (zmTree β) (zmProf β 0) = diagStruct zmU (zmTree β) (zmProf β 1) := by
  funext σ
  show diagS zmU (fun ω => (ω, σ)) σ (zmTree β) (zmProf β 0) =
    diagS zmU (fun ω => (ω, σ)) σ (zmTree β) (zmProf β 1)
  refine Prod.ext rfl (funext fun i => ?_)
  fin_cases i
  · rfl
  · show diagS zmU (fun ω => (ω, σ)) σ zmOuter (zmOuterProf 0) =
      diagS zmU (fun ω => (ω, σ)) σ zmOuter (zmOuterProf 1)
    have key : ∀ j, diagS zmU (fun ω => (ω, σ)) σ zmOuter (zmOuterProf j) =
        cast (congrArg ChanceProfile
          (resolveW_decision_mem (acts := fun _ : Unit => Act2) zmU (fun ω => (ω, σ)) σ mem_zmU
            zmOuterChild).symm)
          (diagS zmU (fun ω => (ω, σ)) σ (zmOuterChild (σ ⟨(), mem_zmU⟩))
            (zmOuterProf j (σ ⟨(), mem_zmU⟩))) :=
      fun j => diagS_decision_mem (acts := fun _ : Unit => Act2) zmU _ σ mem_zmU zmOuterChild
        (zmOuterProf j)
    rw [key 0, key 1]
    refine congrArg (cast _) ?_
    generalize hs : σ ⟨(), mem_zmU⟩ = s
    cases s
    · show diagS zmU (fun ω => (ω, σ)) σ zmInner (zmInnerProf 0) =
        diagS zmU (fun ω => (ω, σ)) σ zmInner (zmInnerProf 1)
      have key' : ∀ j, diagS zmU (fun ω => (ω, σ)) σ zmInner (zmInnerProf j) =
          cast (congrArg ChanceProfile
            (resolveW_decision_mem (acts := fun _ : Unit => Act2) zmU (fun ω => (ω, σ)) σ mem_zmU
              zmInnerChild).symm)
            (diagS zmU (fun ω => (ω, σ)) σ (zmInnerChild (σ ⟨(), mem_zmU⟩))
              (zmInnerProf j (σ ⟨(), mem_zmU⟩))) :=
        fun j => diagS_decision_mem (acts := fun _ : Unit => Act2) zmU _ σ mem_zmU zmInnerChild
          (zmInnerProf j)
      rw [key' 0, key' 1]
      refine congrArg (cast _) ?_
      rw [hs]
      rfl
    · rfl

/-- **ZO-5(b), "only if", on the source's example**: on the 2-fold linear mugging (any root
coin) the structural diagonal is not injective — the identified relocated frame has fewer
columns than `Fr B`, so the two are not equal as matrices under the column identity.
Source: zoo ZO-5(b) (line 70), "Numbers" (line 72: "same-matrix False, biext True")
Kind: N+
Fidelity: exact (the source's tree, up to the root coin's weight) -/
theorem notInjective_diagStruct_zm (β : FinDistr ℚ (Fin 2)) :
    ¬ Function.Injective (diagStruct zmU (zmTree β)) :=
  fun hinj => zmProf_ne β (hinj (zm_diagStruct_eq β))

/-- The 2-fold linear mugging has a nested `d`-fiber (the inner `d`-node lies below the outer
one), whatever the root coin.
Source: zoo ZO-5 "Numbers" (line 72); fair-repair §0
Kind: L -/
theorem zm_nestedFiber (β : FinDistr ℚ (Fin 2)) : NestedFiber (zmTree β) () :=
  ⟨⟨1, some ⟨.a, none⟩⟩, (mem_fiber _ _ _).2 rfl,
    fun h => h (by show () ∈ [()]; simp)⟩

/-- With a fair root coin the 2-fold linear mugging is `Nested` in `dp-core-tree`'s
positive-mass sense: the leaf below `d:a, d:b, coin:0` has mass `¼` and meets two `d`-nodes.
Source: zoo ZO-5 "Numbers" (line 72); `seeds.md` SE-2
Kind: N+
Fidelity: exact -/
theorem zm_fair_nested : Nested (zmTree FinDistr.fair) () := by
  refine ⟨by decide, ⟨1, ⟨.a, ⟨.b, ⟨0, ()⟩⟩⟩⟩, ?_, by decide⟩
  show 0 < FinDistr.fair.w 1 * (FinDistr.fair.w 0 * 1)
  norm_num [FinDistr.fair, FinDistr.coin]

/-- The root coin that puts all its mass on tails.
Source: none: infrastructure (findings F20)
Kind: D -/
def coinTails : FinDistr ℚ (Fin 2) := FinDistr.coin 1 (by norm_num) (by norm_num)

/-- **With the zero-mass heads branch the tree is not `Nested`** (no positive-mass path meets
two `d`-nodes), although its `d`-fiber is nested and its structural diagonal is not
injective.
Source: findings F20; `seeds.md` SE-2 (the positive-path clause of `Nested`)
Kind: N+
Fidelity: exact -/
theorem zm_zeroMass_not_nested : ∀ d ∈ zmU, ¬ Nested (zmTree coinTails) d := by
  rintro ⟨⟩ - ⟨-, ⟨i, ℓ⟩, hpos, hcnt⟩
  fin_cases i
  · exact absurd hcnt (by show ¬ 2 ≤ 0; decide)
  · revert hpos
    show ¬ 0 < coinTails.w 1 * chanceWeight zmOuter ℓ
    norm_num [coinTails, FinDistr.coin]

/-- **The mandate's hypothesis is not enough** (findings F20): `∀ d ∈ U, ¬ Nested B d` (the
positive-mass notion) does not make the structural diagonal injective — the zero-mass 2-fold
linear mugging satisfies it, has a nested fiber, and loses its transfer coin. ZO-5(c)'s
"automatic" needs the possibilistic `¬ NestedFiber` (`diagStruct_injective_of_not_nestedFiber`),
or pruning (`NestedFiber.nested_of_pruned`).
Source: mandate T7(c) ("under `∀ d ∈ U, ¬ Nested B d`"); zoo ZO-5(c) (line 71); findings F20
Kind: N+
Fidelity: exact (refutation of the mandate's phrasing; the source's phrasing is the
possibilistic one) -/
theorem not_nested_insufficient :
    (∀ d ∈ zmU, ¬ Nested (zmTree coinTails) d) ∧ NestedFiber (zmTree coinTails) () ∧
    ¬ Function.Injective (diagStruct zmU (zmTree coinTails)) :=
  ⟨zm_zeroMass_not_nested, zm_nestedFiber _, notInjective_diagStruct_zm _⟩

end Cleanroom.Decision.DpCartesianFrames
