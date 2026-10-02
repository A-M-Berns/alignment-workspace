import Cleanroom.Decision.DpCartesianFrames.Diag

/-!
# The structural diagonal and ZO-5(b)/(c): literal matrix equality under non-nestedness

Package `dp-cartesian-frames`, file 21 (repair round 3, T7(c) — the mandate's one remaining
`core` item; audit r1 B4 / r2 fidelity 4 / r3 fidelity 1, adversarial N1).

The source (zoo ZO-5(b),(c) lines 70–71; cf-frontier CFF-2(b) line 62) says: with copies of
each original chance node identified, the relocated frame and `Fr B` are **equal as
matrices** — under FR-6's row bijection and the column identity — **iff every chance node of
`B` lies on a root path that answers each relocated point consistently** (`E' = E_B`), which
is automatic when no `U`-fiber is nested. `Diag.lean` shows the package's choice-based `diag`
cannot carry this (its kernel is `U`-independent). This file defines the object the source
talks about and proves the "if" half at the possibilistic grade.

* **`diagS U g σ B ε`** — the *structural* diagonal profile of `resolveW U g σ B`: every copy of
  a chance node of `B` reads the original's coordinate, consulted or not (the construction
  inside `exists_diag`, made into a definition; at a relocated node the profile is
  transported along `resolveW_decision_mem`, at a survivor along
  `resolveW_decision_not_mem`). **`diagS_spec`** is `exists_diag`'s property for it.
* **`diagStruct U B ε := fun σ => diagS U (fun ω => (ω, σ)) σ B ε`** — the structural diagonal
  column of `relocRoot U B`; **`FrIdentS U B`** — the identified frame with these columns (CFF-A's
  `Fr_κ(Rel_U B)` as a sub-environment of the lazy relocated frame, now with the *structural*
  diagonal, no choice); `fr_relocRoot_outcome_diagStruct` reads its outcomes.
* **ZO-5(c)** (`diagStruct_injective_of_not_nestedFiber`): if no `U`-fiber is nested — in
  `dp-fairness-reloc`'s possibilistic sense `¬ NestedFiber B d`, no `d`-node strictly below a
  `d`-node — then `diagStruct U B` is injective: no coordinate of `B` is lost. Proof: through
  the recursive `NoRepeatIn U B` (no root path meets two nodes carrying one point of `U`),
  equivalent to the `IsMinimal` form (`noRepeatIn_iff`), by an induction that carries the
  partial constraint on `σ` fixed by the relocated points already passed (`diagS_inj_aux`).
* **ZO-5(b), "if"** (`frIdentS_iso_fr_of_injective`): when `diagStruct U B` is injective, the
  coarsened structural identified frame, restricted to the lifted rows, is **isomorphic in
  `Chu(W)`** to `Fr B` under the row bijection `liftFun`/`toPolicy` and the column identity
  `diagStruct` — the source's "equal as matrices up to row renaming". Composed with ZO-5(c):
  `frIdentS_iso_fr_of_not_nestedFiber`, the mandate's T7(c) core half.

**Hypothesis disclosure (findings F20).** The mandate words T7(c) with `dp-core-tree`'s
`¬ Nested B d`, which carries a positive-mass clause; the source's argument ("a path meets
each `U`-point at most once") is possibilistic, and `¬ NestedFiber B d` is the hypothesis
that makes it go through (`NestedFiber.of_nested` gives `¬ NestedFiber → ¬ Nested`, so the
theorem here has the *stronger* hypothesis). With `¬ Nested` alone the claim is false on an
unpruned tree: a zero-mass chance branch leading to two inconsistently answered `d`-nodes
with a coin below is not `Nested` (no positive path) yet loses that coin
(`notInjective_diagStruct_zeroMass`, the "only if" witness, and the positive-mass reading's
counterexample).
-/

universe u v

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames CategoryTheory
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

section structural

variable [DecidableEq ι] (U : Finset ι) {Ω' : Type} (g : Ω → Ω') (σ : (d : ↥U) → acts d)

/-- **The structural diagonal profile** of `resolveW U g σ B` for a profile `ε` of `B`: every
copy of a chance node of `B` reads the original's coordinate, whether or not any run consults
it (the construction inside `exists_diag`, as a definition — no `Classical.choose`). At a
relocated node the profile of the `σ`-child is transported along `resolveW_decision_mem`; at
a survivor the children's profiles are assembled along `resolveW_decision_not_mem`.
Source: cf-frontier CFF-A (line 46: "copies inherit their original's variable"); universal
UN-7 (line 71: "copies read the original coordinate (FR-7(a) pointwise)")
Kind: D
Fidelity: exact (the source's identification of copies, coordinate by coordinate) -/
def diagS : (B : Tree Ω ι acts K) → ChanceProfile B → ChanceProfile (resolveW U g σ B)
  | .leaf _ _, _ => ()
  | .chance _ _ child, ε => (ε.1, fun i => diagS (child i) (ε.2 i))
  | .decision d child, ε =>
      if h : d ∈ U then
        cast (congrArg ChanceProfile (resolveW_decision_mem U g σ h child).symm)
          (diagS (child (σ ⟨d, h⟩)) (ε (σ ⟨d, h⟩)))
      else
        cast (congrArg ChanceProfile (resolveW_decision_not_mem U g σ h child).symm)
          (fun a => diagS (child a) (ε a))

/-- Equation lemma at a chance node.
Source: none: infrastructure
Kind: L -/
theorem diagS_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (ε : ChanceProfile (.chance n β child)) :
    diagS U g σ (.chance n β child) ε = (ε.1, fun i => diagS U g σ (child i) (ε.2 i)) := rfl

/-- Equation lemma at a relocated decision node (with the transport made explicit).
Source: none: infrastructure
Kind: L -/
theorem diagS_decision_mem {d : ι} (h : d ∈ U) (child : acts d → Tree Ω ι acts K)
    (ε : ChanceProfile (.decision d child)) :
    diagS U g σ (.decision d child) ε =
      cast (congrArg ChanceProfile (resolveW_decision_mem U g σ h child).symm)
        (diagS U g σ (child (σ ⟨d, h⟩)) (ε (σ ⟨d, h⟩))) := by
  conv_lhs => unfold diagS
  rw [dif_pos h]

/-- Equation lemma at a surviving decision node.
Source: none: infrastructure
Kind: L -/
theorem diagS_decision_not_mem {d : ι} (h : d ∉ U) (child : acts d → Tree Ω ι acts K)
    (ε : ChanceProfile (.decision d child)) :
    diagS U g σ (.decision d child) ε =
      cast (congrArg ChanceProfile (resolveW_decision_not_mem U g σ h child).symm)
        (fun a => diagS U g σ (child a) (ε a)) := by
  conv_lhs => unfold diagS
  rw [dif_neg h]

/-- The structural diagonal at a relocated node is the `σ`-child's, up to the type transport.
Source: none: infrastructure
Kind: L -/
theorem diagS_decision_mem_heq {d : ι} (h : d ∈ U) (child : acts d → Tree Ω ι acts K)
    (ε : ChanceProfile (.decision d child)) :
    HEq (diagS U g σ (.decision d child) ε) (diagS U g σ (child (σ ⟨d, h⟩)) (ε (σ ⟨d, h⟩))) := by
  rw [diagS_decision_mem U g σ h]; exact cast_heq _ _

/-- The structural diagonal at a survivor is the children's, up to the type transport.
Source: none: infrastructure
Kind: L -/
theorem diagS_decision_not_mem_heq {d : ι} (h : d ∉ U) (child : acts d → Tree Ω ι acts K)
    (ε : ChanceProfile (.decision d child)) :
    HEq (diagS U g σ (.decision d child) ε)
      ((fun a => diagS U g σ (child a) (ε a)) :
        ChanceProfile (Tree.decision (.inl d) fun a => resolveW U g σ (child a))) := by
  rw [diagS_decision_not_mem U g σ h]; exact cast_heq _ _

/-- The leaf map at a relocated node takes the edge `σ` and continues in the `σ`-child.
Source: fair-repair FR-6 (the canonical leaf map); `dp-fairness-reloc`'s `resolveAux`
Kind: L -/
theorem leafMapW_decision_mem_heq {d : ι} (h : d ∈ U) (child : acts d → Tree Ω ι acts K) :
    HEq (leafMapW U g σ (.decision d child))
      (fun ℓ : (resolveW U g σ (child (σ ⟨d, h⟩))).Leaves =>
        (⟨σ ⟨d, h⟩, leafMapW U g σ (child (σ ⟨d, h⟩)) ℓ⟩ : (Tree.decision d child).Leaves)) := by
  unfold leafMapW resolveW
  rw [resolveAux_decision, dif_pos h]
  exact HEq.rfl

/-- The leaf map at a survivor keeps the edge and continues in that child.
Source: fair-repair FR-6; `dp-fairness-reloc`'s `resolveAux`
Kind: L -/
theorem leafMapW_decision_not_mem_heq {d : ι} (h : d ∉ U) (child : acts d → Tree Ω ι acts K) :
    HEq (leafMapW U g σ (.decision d child))
      (fun ℓ : (Tree.decision (.inl d) fun a => resolveW U g σ (child a)).Leaves =>
        (⟨ℓ.1, leafMapW U g σ (child ℓ.1) ℓ.2⟩ : (Tree.decision d child).Leaves)) := by
  unfold leafMapW resolveW
  rw [resolveAux_decision, dif_neg h]
  exact HEq.rfl

/-- Applying heterogeneously equal functions to heterogeneously equal arguments.
Source: none: infrastructure
Kind: L -/
theorem heq_app_eq {A A' : Sort u} {B : Sort v} (e : A = A') {f : A → B} {f' : A' → B}
    (hf : HEq f f') {a : A} {a' : A'} (ha : HEq a a') : f a = f' a' := by
  subst e; rw [eq_of_heq hf, eq_of_heq ha]

/-- The run respects a transport of the tree.
Source: none: infrastructure
Kind: L -/
theorem runLeaf_heq {ι' : Type} {acts' : ι' → Type} {T T' : Tree Ω' ι' acts' K} (e : T = T')
    (ρ : (p : ι') → acts' p) {ε₁ : ChanceProfile T} {ε₂ : ChanceProfile T'} (h : HEq ε₁ ε₂) :
    HEq (runLeaf ρ T ε₁) (runLeaf ρ T' ε₂) := by
  subst e; rw [eq_of_heq h]

/-- **The structural diagonal is diagonal** (FR-7(a) pointwise, for `diagS`): under it, every
policy's relocated run lands on the copy of the leaf the original run of `toPolicy U σ ρ`
reaches under `ε`.
Source: fair-repair FR-7(a) via universal UN-7 (line 71); zoo ZO-5(a) (line 69)
Kind: P
Fidelity: exact
Hyps: none -/
theorem diagS_spec : (B : Tree Ω ι acts K) → ∀ (ε : ChanceProfile B)
    (ρ : (p : ι ⊕ Unit) → actsR acts U p),
    leafMapW U g σ B (runLeaf ρ (resolveW U g σ B) (diagS U g σ B ε)) =
      runLeaf (toPolicy U σ ρ) B ε
  | .leaf _ _, _, _ => rfl
  | .chance _ _ child, ε, ρ => congrArg (Sigma.mk ε.1) (diagS_spec (child ε.1) (ε.2 ε.1) ρ)
  | .decision d child, ε, ρ => by
      by_cases h : d ∈ U
      · have hd : toPolicy U σ ρ d = σ ⟨d, h⟩ := by simp [toPolicy, h]
        rw [runLeaf_decision, hd]
        exact (heq_app_eq (congrArg Tree.Leaves (resolveW_decision_mem U g σ h child))
          (leafMapW_decision_mem_heq U g σ h child)
          (runLeaf_heq (resolveW_decision_mem U g σ h child) ρ
            (diagS_decision_mem_heq U g σ h child ε))).trans
          (congrArg (Sigma.mk (σ ⟨d, h⟩)) (diagS_spec (child (σ ⟨d, h⟩)) (ε (σ ⟨d, h⟩)) ρ))
      · have hd : toPolicy U σ ρ d = ρ (.inl d) := by simp [toPolicy, h]
        rw [runLeaf_decision, hd]
        exact (heq_app_eq (congrArg Tree.Leaves (resolveW_decision_not_mem U g σ h child))
          (leafMapW_decision_not_mem_heq U g σ h child)
          (runLeaf_heq (resolveW_decision_not_mem U g σ h child) ρ
            (diagS_decision_not_mem_heq U g σ h child ε))).trans
          (congrArg (Sigma.mk (ρ (.inl d))) (diagS_spec (child (ρ (.inl d))) (ε (ρ (.inl d))) ρ))

end structural

section identified

variable [DecidableEq ι] [∀ d, Fintype (acts d)] (U : Finset ι)

/-- **The structural diagonal column** of `relocRoot U B` for a profile `ε` of `B`: on the
`σ`-branch, the structural diagonal of `resolve U σ B`. Computable; no choice.
Source: cf-frontier CFF-1 (line 60: "`Δ_κ` = lazy profiles constant on each class"), CFF-A
(line 46)
Kind: D
Fidelity: exact -/
def diagStruct (B : Tree Ω ι acts K) (ε : ChanceProfile B) : ChanceProfile (relocRoot U B) :=
  fun σ => diagS U (fun ω => (ω, σ)) σ B ε

/-- **The structural identified frame** of a relocation output: the lazy frame of
`relocRoot U B` restricted to the structural diagonal columns — CFF-A's `Fr_κ(Rel_U B)`,
with stamps, as a sub-environment of the lazy relocated frame (the composite option of
mandate §3, now with no choice in the column map).
Source: cf-frontier CFF-A (line 46), CFF-1 (line 60); zoo ZO-5 setting (line 68: "`E`
indexed by original chance nodes (copies identified)")
Kind: D
Fidelity: exact (columns = the image of the structural diagonal) -/
def FrIdentS (B : Tree Ω ι acts K) : CartesianFrames.Frame (RW Ω acts U × K) :=
  (Fr (relocRoot U B)).assume (Set.range (diagStruct U B))

/-- The outcome of the relocated tree on a structural diagonal column: the original run's
world stamped with the root answer, and its payoff.
Source: fair-repair FR-7(a); universal UN-7 (line 71)
Kind: P
Fidelity: exact
Hyps: none -/
theorem fr_relocRoot_outcome_diagStruct (B : Tree Ω ι acts K)
    (ρ : (p : ι ⊕ Unit) → actsR acts U p) (ε : ChanceProfile B) :
    (Fr (relocRoot U B)).outcome ρ (diagStruct U B ε) =
      ((world B (runLeaf (toPolicy U (ρ (.inr ())) ρ) B ε), ρ (.inr ())),
        payoff B (runLeaf (toPolicy U (ρ (.inr ())) ρ) B ε)) := by
  show (world (resolveW U (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) B)
      (runLeaf ρ (resolveW U (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) B)
        (diagS U (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) B ε)),
    payoff (resolveW U (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) B)
      (runLeaf ρ (resolveW U (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) B)
        (diagS U (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) B ε))) = _
  rw [world_resolveW, payoff_resolveW, diagS_spec]

end identified

/-! ### Non-nestedness, recursively, and its bridge to `NestedFiber` -/

section nonNested

variable [DecidableEq ι] (U : Finset ι)

/-- No decision node of `B` carries a point of `c`.
Source: none: infrastructure (the induction invariant of `diagS_inj_aux`)
Kind: D -/
def Avoids (c : Finset ι) : Tree Ω ι acts K → Prop
  | .leaf _ _ => True
  | .chance _ _ child => ∀ i, Avoids c (child i)
  | .decision d child => d ∉ c ∧ ∀ a, Avoids c (child a)

/-- No root path of `B` meets two decision nodes carrying one point of `U`: below a `d`-node
with `d ∈ U` there is no `d`-node. The recursive form of "no `U`-fiber is nested".
Source: zoo ZO-5(c) (line 71: "a path meets each `U`-point at most once"); fair-repair §0
("`F_d` is nested (self-succession) if some member is a proper ancestor of another")
Kind: D
Fidelity: exact (equivalent to `∀ d ∈ U, ¬ NestedFiber B d`, `noRepeatIn_iff` and
`noRepeatIn_of_not_nestedFiber`) -/
def NoRepeatIn : Tree Ω ι acts K → Prop
  | .leaf _ _ => True
  | .chance _ _ child => ∀ i, NoRepeatIn (child i)
  | .decision d child => (d ∈ U → ∀ a, Avoids {d} (child a)) ∧ ∀ a, NoRepeatIn (child a)

/-- `Avoids c B` says exactly that no node of `B` carries a point of `c`.
Source: none: infrastructure
Kind: L -/
theorem avoids_iff (c : Finset ι) :
    (B : Tree Ω ι acts K) → (Avoids c B ↔ ∀ q : B.DecNode, pt B q ∉ c)
  | .leaf _ _ => ⟨fun _ q => q.elim, fun _ => trivial⟩
  | .chance _ _ child =>
      ⟨fun h ⟨i, q⟩ => (avoids_iff c (child i)).1 (h i) q,
        fun h i => (avoids_iff c (child i)).2 fun q => h ⟨i, q⟩⟩
  | .decision d child =>
      ⟨fun h q => by
          rcases q with _ | ⟨a, q⟩
          · exact h.1
          · exact (avoids_iff c (child a)).1 (h.2 a) q,
        fun h => ⟨h none, fun a => (avoids_iff c (child a)).2 fun q => h (some ⟨a, q⟩)⟩⟩

/-- `NoRepeatIn U B` says exactly that every node carrying a point of `U` is minimal (no node
strictly above it carries the same point) — `dp-fairness-reloc`'s `IsMinimal`.
Source: none: infrastructure
Kind: L -/
theorem noRepeatIn_iff : (B : Tree Ω ι acts K) →
    (NoRepeatIn U B ↔ ∀ q : B.DecNode, pt B q ∈ U → IsMinimal B q)
  | .leaf _ _ => ⟨fun _ q => q.elim, fun _ => trivial⟩
  | .chance _ _ child =>
      ⟨fun h ⟨i, q⟩ hq => (noRepeatIn_iff (child i)).1 (h i) q hq,
        fun h i => (noRepeatIn_iff (child i)).2 fun q hq => h ⟨i, q⟩ hq⟩
  | .decision d child => by
      constructor
      · rintro ⟨h1, h2⟩ q hq
        rcases q with _ | ⟨a, q⟩
        · simp [IsMinimal]
        · show pt (child a) q ∉ d :: ancestorPts (child a) q
          rw [List.mem_cons, not_or]
          refine ⟨fun hd => ?_, (noRepeatIn_iff (child a)).1 (h2 a) q hq⟩
          exact (avoids_iff {d} (child a)).1 (h1 (hd ▸ hq) a) q (Finset.mem_singleton.2 hd)
      · intro h
        refine ⟨fun hdU a => ?_, fun a => ?_⟩
        · rw [avoids_iff]
          intro q hq
          rw [Finset.mem_singleton] at hq
          have := h (some ⟨a, q⟩) (by show pt (child a) q ∈ U; rw [hq]; exact hdU)
          change pt (child a) q ∉ d :: ancestorPts (child a) q at this
          rw [List.mem_cons, not_or] at this
          exact this.1 hq
        · rw [noRepeatIn_iff]
          intro q hq
          have := h (some ⟨a, q⟩) hq
          change pt (child a) q ∉ d :: ancestorPts (child a) q at this
          rw [List.mem_cons, not_or] at this
          exact this.2

/-- **No nested `U`-fiber ⟹ `NoRepeatIn U B`**: the bridge from `dp-fairness-reloc`'s
definition of record to the recursive form the induction uses.
Source: fair-repair §0; zoo ZO-5(c) (line 71)
Kind: L -/
theorem noRepeatIn_of_not_nestedFiber [∀ d, Fintype (acts d)] (B : Tree Ω ι acts K)
    (h : ∀ d ∈ U, ¬ NestedFiber B d) : NoRepeatIn U B := by
  rw [noRepeatIn_iff]
  intro q hq
  by_contra hmin
  exact h _ hq ⟨q, (mem_fiber B _ q).2 rfl, hmin⟩

/-- Nothing avoids the empty set's points: `Avoids ∅ B`.
Source: none: infrastructure
Kind: L -/
theorem avoids_empty : (B : Tree Ω ι acts K) → Avoids ∅ B
  | .leaf _ _ => trivial
  | .chance _ _ child => fun i => avoids_empty (child i)
  | .decision _ child => ⟨Finset.notMem_empty _, fun a => avoids_empty (child a)⟩

/-- `Avoids` is closed under unions of the avoided sets.
Source: none: infrastructure
Kind: L -/
theorem Avoids.union {c c' : Finset ι} :
    (B : Tree Ω ι acts K) → Avoids c B → Avoids c' B → Avoids (c ∪ c') B
  | .leaf _ _, _, _ => trivial
  | .chance _ _ child, h, h' => fun i => Avoids.union (child i) (h i) (h' i)
  | .decision _ child, h, h' =>
      ⟨fun hm => (Finset.mem_union.1 hm).elim h.1 h'.1,
        fun a => Avoids.union (child a) (h.2 a) (h'.2 a)⟩

end nonNested

/-! ### ZO-5(c): the structural diagonal is injective when no `U`-fiber is nested -/

section injective

variable [DecidableEq ι] (U : Finset ι) {Ω' : Type}

/-- **The induction behind ZO-5(c).** For a subtree `B` reached through relocated points
whose answers are already fixed on the set `c` (the constraint `σ|_c = σ₀|_c`), with `B`
avoiding `c` and no point of `U` repeating on a path of `B`: two profiles of `B` whose
structural diagonals agree on every `σ` satisfying the constraint are equal. At a relocated
node `d` the constraint grows by `d ↦ a` for each child `a` — legitimate because no `d`-node
sits below (`NoRepeatIn`), so the children never read the `d`-coordinate of `σ` again.
Source: zoo ZO-5(c) (line 71: "a path meets each `U`-point at most once, so `E' = E_B`")
Kind: P
Fidelity: exact
Hyps: none -/
theorem diagS_inj_aux (g : ((d : ↥U) → acts d) → Ω → Ω') :
    (B : Tree Ω ι acts K) → ∀ (c : Finset ι), Avoids c B → NoRepeatIn U B →
      ∀ (σ₀ : (d : ↥U) → acts d) (ε ε' : ChanceProfile B),
        (∀ σ : (d : ↥U) → acts d, (∀ d : ↥U, ↑d ∈ c → σ d = σ₀ d) →
          diagS U (g σ) σ B ε = diagS U (g σ) σ B ε') → ε = ε'
  | .leaf _ _, _, _, _, _, ε, ε', _ => Subsingleton.elim (α := Unit) ε ε'
  | .chance _ _ child, c, hc, hB, σ₀, ε, ε', H => by
      have key : ∀ σ, (∀ d : ↥U, ↑d ∈ c → σ d = σ₀ d) →
          ε.1 = ε'.1 ∧ ∀ i, diagS U (g σ) σ (child i) (ε.2 i) =
            diagS U (g σ) σ (child i) (ε'.2 i) := by
        intro σ hσ
        have h := H σ hσ
        rw [diagS_chance, diagS_chance] at h
        exact ⟨(Prod.mk.inj h).1, fun i => congrFun (Prod.mk.inj h).2 i⟩
      refine Prod.ext (key σ₀ fun _ _ => rfl).1 (funext fun i => ?_)
      exact diagS_inj_aux g (child i) c (hc i) (hB i) σ₀ (ε.2 i) (ε'.2 i)
        fun σ hσ => (key σ hσ).2 i
  | .decision d child, c, hc, hB, σ₀, ε, ε', H => by
      obtain ⟨hdc, hc'⟩ := hc
      obtain ⟨hrep, hB'⟩ := hB
      by_cases h : d ∈ U
      · funext a
        refine diagS_inj_aux g (child a) ({d} ∪ c) (Avoids.union (child a) (hrep h a) (hc' a))
          (hB' a) (Function.update σ₀ ⟨d, h⟩ a) (ε a) (ε' a) fun σ hσ => ?_
        have hσd : σ ⟨d, h⟩ = a := by
          rw [hσ ⟨d, h⟩ (Finset.mem_union_left _ (Finset.mem_singleton_self d)),
            Function.update_self]
        have hσc : ∀ d' : ↥U, ↑d' ∈ c → σ d' = σ₀ d' := fun d' hd' => by
          rw [hσ d' (Finset.mem_union_right _ hd'), Function.update_of_ne]
          intro hdd'
          subst hdd'
          exact hdc hd'
        have := H σ hσc
        rw [diagS_decision_mem U (g σ) σ h, diagS_decision_mem U (g σ) σ h] at this
        have := (cast_inj _).mp this
        subst hσd
        exact this
      · funext a
        refine diagS_inj_aux g (child a) c (hc' a) (hB' a) σ₀ (ε a) (ε' a) fun σ hσ => ?_
        have := H σ hσ
        rw [diagS_decision_not_mem U (g σ) σ h, diagS_decision_not_mem U (g σ) σ h] at this
        exact congrFun ((cast_inj _).mp this) a

variable [∀ d, Fintype (acts d)]

/-- **ZO-5(c), recursive form**: if no point of `U` repeats on a root path, the structural
diagonal column map `diagStruct U B` is injective — every coordinate of `B` survives in some
`σ`-copy.
Source: zoo ZO-5(c) (line 71); cf-frontier CFF-2(b) (line 62: "automatic when no fiber in
`U` is nested")
Kind: P
Fidelity: exact
Hyps: none -/
theorem diagStruct_injective_of_noRepeatIn [Nonempty ((d : ↥U) → acts d)]
    (B : Tree Ω ι acts K) (hB : NoRepeatIn U B) : Function.Injective (diagStruct U B) :=
  fun ε ε' h => diagS_inj_aux U (fun σ ω => (ω, σ)) B ∅ (avoids_empty B) hB
    (Classical.arbitrary _) ε ε' fun σ _ => congrFun h σ

/-- **ZO-5(c) / CFF-2(b)'s automatic case** (T7(c), core half, the hypothesis side): if no
`U`-fiber is nested (`dp-fairness-reloc`'s `NestedFiber`, the possibilistic notion the
source's argument uses), the structural diagonal `diagStruct U B` is injective, i.e. the
identified relocated frame's column index set is `B`'s own (`E' = E_B`). The hypothesis is
*stronger* than the mandate's `∀ d ∈ U, ¬ Nested B d` (`NestedFiber.of_nested`); with the
mandate's positive-mass notion the claim fails on unpruned trees (findings F20).
Source: zoo ZO-5(c) (line 71); cf-frontier CFF-2(b) (line 62); mandate T7(c)
Kind: C
Fidelity: variant: `¬ NestedFiber` (possibilistic, the source's "a path meets each `U`-point
at most once") in place of the mandate's `¬ Nested` (positive-mass); `[∀ d, Nonempty (acts
d)]` so that some `σ` exists
Hyps: none -/
theorem diagStruct_injective_of_not_nestedFiber [∀ d, Nonempty (acts d)]
    (B : Tree Ω ι acts K) (h : ∀ d ∈ U, ¬ NestedFiber B d) :
    Function.Injective (diagStruct U B) :=
  diagStruct_injective_of_noRepeatIn U B (noRepeatIn_of_not_nestedFiber U B h)

end injective

/-! ### ZO-5(b), "if": equal as matrices under the row bijection and the column identity -/

section matrix

variable [DecidableEq ι] [∀ d, Fintype (acts d)] (U : Finset ι)

/-- **The literal identified frame** of a relocation output: the lazy frame of `relocRoot U B`
with rows restricted to the lifted policies `liftFun U π` (FR-6's row bijection
`∏_{d∈U} A_d × ∏_{e∉U} A_e ≅ ∏_d A_d`, realized as the sub-agent of rows whose inert
`U`-coordinates agree with the root tuple), columns restricted to the structural diagonal
(the column identity `ε ↦ diagStruct U B ε`), and the `pol` stamps coarsened away.
Source: cf-frontier CFF-2(b) (line 62: "equal as matrices under FR-6's row bijection and the
column identity"); zoo ZO-5(b) (line 70: "matrix equality up to row renaming")
Kind: D
Fidelity: exact (the row bijection and the column identity are the source's) -/
def FrLit (B : Tree Ω ι acts K) : CartesianFrames.Frame (Ω × K) :=
  (Frame.mapWorlds (Prod.map Prod.fst id)).obj
    (((Fr (relocRoot U B)).commit (Set.range (liftFun U))).assume (Set.range (diagStruct U B)))

/-- **ZO-5(b), "if"**: when the structural diagonal is injective (`E' = E_B`), the literal
identified frame of the relocation output is **isomorphic in `Chu(W)`** to `Fr B`, through
the row bijection `liftFun U` / `toPolicy` and the column identity `diagStruct U B` (with its
inverse on the range): the two matrices are equal up to renaming rows and columns, entry by
entry (`fr_relocRoot_outcome_diagStruct`).
Source: zoo ZO-5(b) (line 70, "if"); cf-frontier CFF-2(b) (line 62, "if"); mandate T7(c)
Kind: P
Fidelity: exact (an isomorphism in `Chu(W)` with the source's row and column maps; the
inverse column map is the inverse of an injection onto its range)
Hyps: none -/
noncomputable def frLitIsoFr_of_injective (B : Tree Ω ι acts K)
    (hinj : Function.Injective (diagStruct U B)) : FrLit U B ≅ Fr B where
  hom :=
    { agent := fun ρ => toPolicy U (ρ.val (.inr ())) ρ.val
      env := fun ε => ⟨diagStruct U B ε, ⟨ε, rfl⟩⟩
      adjoint := fun ρ ε => by
        show Prod.map Prod.fst id ((Fr (relocRoot U B)).outcome ρ.val (diagStruct U B ε)) =
          (Fr B).outcome (toPolicy U (ρ.val (.inr ())) ρ.val) ε
        rw [fr_relocRoot_outcome_diagStruct]
        rfl }
  inv :=
    { agent := fun π => ⟨liftFun U π, ⟨π, rfl⟩⟩
      env := fun y => Classical.choose y.property
      adjoint := fun π y => by
        show (Fr B).outcome π (Classical.choose y.property) =
          Prod.map Prod.fst id ((Fr (relocRoot U B)).outcome (liftFun U π) y.val)
        conv_rhs => rw [← Classical.choose_spec y.property]
        rw [fr_relocRoot_outcome_diagStruct, toPolicy_liftFun]
        rfl }
  hom_inv_id := by
    apply Frame.Hom.ext
    · funext ρ
      obtain ⟨_, π, rfl⟩ := ρ
      apply Subtype.ext
      show liftFun U (toPolicy U (liftFun U π (.inr ())) (liftFun U π)) = liftFun U π
      rw [toPolicy_liftFun]
    · funext y
      exact Subtype.ext (Classical.choose_spec y.property)
  inv_hom_id := by
    apply Frame.Hom.ext
    · funext π
      exact toPolicy_liftFun U π
    · funext ε
      exact hinj (Classical.choose_spec
        (⟨ε, rfl⟩ : diagStruct U B ε ∈ Set.range (diagStruct U B)))

/-- **T7(c), the core half** (ZO-5(b) "if" + ZO-5(c)): when no `U`-fiber is nested, the
literal identified frame of the relocation output is isomorphic in `Chu(W)` to `Fr B` under
the row bijection and the column identity — "relocation cannot change the frame", as a
matrix, on the non-nested class.
Source: zoo ZO-5(b),(c) (lines 70–71); cf-frontier CFF-2(b) (line 62); mandate T7(c)
Kind: C
Fidelity: variant: `¬ NestedFiber` (possibilistic) for the mandate's `¬ Nested`; see
`diagStruct_injective_of_not_nestedFiber`
Hyps: none -/
theorem frLit_iso_fr_of_not_nestedFiber [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K)
    (h : ∀ d ∈ U, ¬ NestedFiber B d) : Nonempty (FrLit U B ≅ Fr B) :=
  ⟨frLitIsoFr_of_injective U B (diagStruct_injective_of_not_nestedFiber U B h)⟩

end matrix

end Cleanroom.Decision.DpCartesianFrames
