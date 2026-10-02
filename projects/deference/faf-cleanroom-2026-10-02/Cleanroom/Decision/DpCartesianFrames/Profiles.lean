import Cleanroom.Found.DpCoreTree.Occurrence
import Cleanroom.Decision.DpCartesianFrames.Observe

/-!
# Chance profiles, the frame functor, the node frame and the local frame

Package `dp-cartesian-frames`, file 2: the representation of record (mandate §3), over
`dp-core-tree`'s `Tree` and FAF's `Frame`.

* `ChanceProfile B`: one coordinate per chance node of `B`, reachable or not — CF-1's *lazy*
  seeding — defined structurally (no chance-node addresses). It depends only on the tree's
  shape (arities and action sets), never on chance weights, worlds or payoffs; this is what makes
  the β-pair's `Fr P = Fr P'` hold by `rfl` (T5).
* `runLeaf π B ε`: the deterministic run of the pure policy `π` (one answer per *point*) under
  the profile `ε`; `readout B ℓ := (λ(ℓ), r(ℓ))`, CF-1's extensional readout.
* **`Fr B : Frame (Ω × K)`** (agent: pure policies; environment: chance profiles), the fine
  frame `FrFine B : Frame B.Leaves`, the node frame `FrNode B` (agent: one answer per decision
  *node*), and the **local frame `Loc d B`** (agent `A_d`; environment: the other points'
  answers × the profile), CF-5's rendering of the point-deviation `C[d ↦ a]`.
* `SO obs d := {w | w.1 ∈ O_d}`, the claimed observation of `d` as an event of `Ω × K`.
* **T1(b)**: `Loc d B ◁ₓ Fr B` on the nose over FAF's `MultSubagent` (`loc_multSubagent_fr`).
* **T1(c)** (CF-4): `Fr B ≃ᵇ (FrNode B).commit Δ` with `Δ` the diagonal "one answer per
  point" assignments, hence `Fr B ◁₊ FrNode B` (`fr_addSubagent_frNode`). The AMD's commit is
  proper: see `Witnesses.lean`.

**Seeding disclosure** (mandate §6 item 2): every frame here is *lazy* — `Env` has one coordinate
per chance node of the tree. The identified frame of a relocation output is `Reloc.lean`'s
`FrIdent`. No frame-side statement is a theorem about *problems* until the seeding is named;
every docstring in this package names it.
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames CategoryTheory
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-! ### Chance profiles (lazy seeding) -/

/-- **Chance profiles** of a tree, structurally: a leaf has the trivial profile; a chance node's
profile picks its own child and a profile of *every* child (one coordinate per chance node,
reachable or not — the lazy coin convention); a decision node's profile is a profile of every
child. The type depends only on the shape of `B` (arities, action sets): not on `β`, worlds or
payoffs.
Source: cf-correspondence CF-1 (line 11: `𝐄_B := ∏_{n ∈ Ch(B)} children(n)`, "the lazy coin
convention"); mandate §3
Kind: D
Fidelity: exact (structural rather than address-indexed; canonically the same product) -/
def ChanceProfile : Tree Ω ι acts K → Type
  | .leaf _ _ => Unit
  | .chance n _ child => Fin n × ((i : Fin n) → ChanceProfile (child i))
  | .decision d child => (a : acts d) → ChanceProfile (child a)

/-- `Fintype` structure on chance profiles, by recursion (finite because the tree is).
Source: none: infrastructure
Kind: D -/
@[reducible] def fintypeChanceProfile [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] :
    (B : Tree Ω ι acts K) → Fintype (ChanceProfile B)
  | .leaf _ _ => inferInstanceAs (Fintype Unit)
  | .chance n _ child =>
      haveI : ∀ i, Fintype (ChanceProfile (child i)) := fun i => fintypeChanceProfile (child i)
      inferInstanceAs (Fintype (Fin n × ((i : Fin n) → ChanceProfile (child i))))
  | .decision d child =>
      haveI : ∀ a, Fintype (ChanceProfile (child a)) := fun a => fintypeChanceProfile (child a)
      inferInstanceAs (Fintype ((a : acts d) → ChanceProfile (child a)))

instance [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] (B : Tree Ω ι acts K) :
    Fintype (ChanceProfile B) := fintypeChanceProfile B

/-- Decidable equality of chance profiles, by recursion.
Source: none: infrastructure
Kind: D -/
@[reducible] def decEqChanceProfile [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] :
    (B : Tree Ω ι acts K) → DecidableEq (ChanceProfile B)
  | .leaf _ _ => inferInstanceAs (DecidableEq Unit)
  | .chance n _ child =>
      haveI : ∀ i, DecidableEq (ChanceProfile (child i)) := fun i => decEqChanceProfile (child i)
      inferInstanceAs (DecidableEq (Fin n × ((i : Fin n) → ChanceProfile (child i))))
  | .decision d child =>
      haveI : ∀ a, DecidableEq (ChanceProfile (child a)) := fun a => decEqChanceProfile (child a)
      inferInstanceAs (DecidableEq ((a : acts d) → ChanceProfile (child a)))

instance [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] (B : Tree Ω ι acts K) :
    DecidableEq (ChanceProfile B) := decEqChanceProfile B

/-- Every chance node has at least one child (`FinDistr` sums to `1`), so a chance profile
exists: the environment of a tree frame is never empty (T2's vacuity trap does not arise).
Source: mandate §7 ("empty `Env` … impossible for tree frames — `FinDistr` forces `n ≥ 1`")
Kind: L -/
theorem chanceProfileNonempty : (B : Tree Ω ι acts K) → Nonempty (ChanceProfile B)
  | .leaf _ _ => ⟨()⟩
  | .chance _ β child => by
      obtain ⟨i⟩ := FinDistr.nonempty_of_finDistr β
      exact ⟨(i, fun j => (chanceProfileNonempty (child j)).some)⟩
  | .decision _ child => ⟨fun a => (chanceProfileNonempty (child a)).some⟩

instance (B : Tree Ω ι acts K) : Nonempty (ChanceProfile B) := chanceProfileNonempty B

/-! ### The run and the readout -/

/-- **The run** of a pure policy `π` (one answer per point) under a chance profile `ε`: follow
`ε` at chance nodes and `π d` at every `d`-node — every occurrence of `d` gets the same answer
(the frame's agent is CF-1's policies, not v2 Prop 5's node assignments).
Source: cf-correspondence CF-1 (line 11: "at a chance node `n` follow `ε(n)`, at a decision
node `q` follow `π(d_q)`")
Kind: D
Fidelity: exact -/
def runLeaf (π : (d : ι) → acts d) : (B : Tree Ω ι acts K) → ChanceProfile B → B.Leaves
  | .leaf _ _, _ => ()
  | .chance _ _ child, ε => ⟨ε.1, runLeaf π (child ε.1) (ε.2 ε.1)⟩
  | .decision d child, ε => ⟨π d, runLeaf π (child (π d)) (ε (π d))⟩

/-- The extensional readout `φ(ℓ) := (λ(ℓ), r(ℓ))`.
Source: cf-correspondence CF-1 (line 11: "`φ(ℓ) := (λ(ℓ), r(ℓ))`")
Kind: D -/
def readout (B : Tree Ω ι acts K) (ℓ : B.Leaves) : Ω × K := (world B ℓ, payoff B ℓ)

@[simp] theorem runLeaf_leaf (π : (d : ι) → acts d) (ω : Ω) (r : K) (ε : ChanceProfile (.leaf ω r)) :
    runLeaf π (.leaf ω r : Tree Ω ι acts K) ε = () := rfl

@[simp] theorem runLeaf_chance (π : (d : ι) → acts d) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (ε : ChanceProfile (.chance n β child)) :
    runLeaf π (.chance n β child) ε = ⟨ε.1, runLeaf π (child ε.1) (ε.2 ε.1)⟩ := rfl

@[simp] theorem runLeaf_decision (π : (d : ι) → acts d) (d : ι) (child : acts d → Tree Ω ι acts K)
    (ε : ChanceProfile (.decision d child)) :
    runLeaf π (.decision d child) ε = ⟨π d, runLeaf π (child (π d)) (ε (π d))⟩ := rfl

/-! ### The frames -/

/-- **The (extensional) policy frame `Fr B`**: agent = pure policies `∏_d A_d` (over *all*
points of `ι`; a point not queried in `B` is an inert coordinate), environment = chance profiles
(lazy seeding), outcome = the readout of the run. Worlds are `Ω × K`, not restricted to the
image (the mandate's §3 convention; CF-2 takes `W = Image`).
Source: cf-correspondence CF-1 (line 11: "the (extensional) policy frame `Fr(B)`"); mandate §3
Kind: D
Fidelity: variant: worlds `Ω × K` rather than the image (unreachable cells add no constraint
to any predicate of `Observe.lean`, all of which quantify over `Env`) -/
def Fr (B : Tree Ω ι acts K) : CartesianFrames.Frame (Ω × K) where
  Agent := (d : ι) → acts d
  Env := ChanceProfile B
  outcome π ε := readout B (runLeaf π B ε)

@[simp] theorem Fr_outcome (B : Tree Ω ι acts K) (π : (d : ι) → acts d) (ε : ChanceProfile B) :
    (Fr B).outcome π ε = readout B (runLeaf π B ε) := rfl

/-- **The fine frame** `Fr°(B)` over the leaves: the run itself as the outcome.
Source: cf-correspondence CF-1 (line 11: "the fine frame `Fr°(B)`")
Kind: D
Fidelity: exact -/
def FrFine (B : Tree Ω ι acts K) : CartesianFrames.Frame B.Leaves where
  Agent := (d : ι) → acts d
  Env := ChanceProfile B
  outcome π ε := runLeaf π B ε

/-- `Fr B` is the fine frame pushed along the readout (CF-2's fine-to-coarse transfer is then
FAF's `mapWorlds`).
Source: cf-correspondence CF-2 (line 19)
Kind: L -/
theorem fr_eq_mapWorlds_frFine (B : Tree Ω ι acts K) :
    Fr B = (Frame.mapWorlds (readout B)).obj (FrFine B) := rfl

/-- **CF-2's transfer lemma**: a partition observable in the fine frame after pulling back along
the readout is observable in `Fr B` (the same conditional policy works, since leafwise equality
implies readout equality).
Source: cf-correspondence CF-2 (line 19)
Kind: P
Fidelity: exact
Hyps: none -/
theorem observable_fr_of_frFine {V : Sort*} (B : Tree Ω ι acts K) (v : Ω × K → V)
    (h : Observable (FrFine B) (v ∘ readout B)) : Observable (Fr B) v := by
  intro f
  obtain ⟨a, ha⟩ := h f
  exact ⟨a, fun e => congrArg (readout B) (ha e)⟩

/-- Node assignments: one answer per decision *node* (v2 Prop 5's assignments).
Source: cf-correspondence CF-1 (line 11: "the node frame … agent set `∏_q A_{d_q}`")
Kind: D -/
abbrev NodeAssign (B : Tree Ω ι acts K) : Type := (q : B.DecNode) → acts (pt B q)

/-- The run of a node assignment: at a decision node follow the assignment's answer at that
node, then continue with the assignment restricted to the chosen child.
Source: cf-correspondence CF-1 (line 11: "the run following `σ(q)` at `q`")
Kind: D -/
def runLeafNode : (B : Tree Ω ι acts K) → NodeAssign B → ChanceProfile B → B.Leaves
  | .leaf _ _, _, _ => ()
  | .chance _ _ child, σ, ε =>
      ⟨ε.1, runLeafNode (child ε.1) (fun q => σ ⟨ε.1, q⟩) (ε.2 ε.1)⟩
  | .decision _ child, σ, ε =>
      ⟨σ none, runLeafNode (child (σ none)) (fun q => σ (some ⟨σ none, q⟩)) (ε (σ none))⟩

/-- **The node frame `Fr^nd(B)`**: agent = node assignments, environment = chance profiles,
outcome = the readout of the assignment's run.
Source: cf-correspondence CF-1 (line 11)
Kind: D
Fidelity: exact -/
def FrNode (B : Tree Ω ι acts K) : CartesianFrames.Frame (Ω × K) where
  Agent := NodeAssign B
  Env := ChanceProfile B
  outcome σ ε := readout B (runLeafNode B σ ε)

/-- The diagonal: a policy read as a node assignment (`q ↦ π(d_q)`).
Source: cf-correspondence CF-4 (line 19: "`Δ := {(π(d_q))_q : π ∈ 𝐀_B}`")
Kind: D -/
def diagAssign (B : Tree Ω ι acts K) (π : (d : ι) → acts d) : NodeAssign B :=
  fun q => π (pt B q)

/-- The diagonal assignment runs as the policy does.
Source: cf-correspondence CF-4 (line 19)
Kind: P
Fidelity: exact
Hyps: none -/
theorem runLeafNode_diagAssign (π : (d : ι) → acts d) :
    (B : Tree Ω ι acts K) → ∀ ε, runLeafNode B (diagAssign B π) ε = runLeaf π B ε
  | .leaf _ _, _ => rfl
  | .chance _ _ child, ε => congrArg (Sigma.mk ε.1) (runLeafNode_diagAssign π (child ε.1) (ε.2 ε.1))
  | .decision d child, ε =>
      congrArg (Sigma.mk (π d)) (runLeafNode_diagAssign π (child (π d)) (ε (π d)))

/-! ### The local frame -/

section local_frame

variable [DecidableEq ι]

/-- Extend an answer `a` at `d` and answers `p` at the other points to a full policy.
Source: cf-correspondence CF-5 (line 21: `π_{-d}[d ↦ a]`)
Kind: D -/
def extend (d : ι) (a : acts d) (p : (e : {e : ι // e ≠ d}) → acts e.val) : (e : ι) → acts e :=
  fun e => if h : e = d then cast (congrArg acts h.symm) a else p ⟨e, h⟩

@[simp] theorem extend_self (d : ι) (a : acts d) (p : (e : {e : ι // e ≠ d}) → acts e.val) :
    extend d a p d = a := by
  simp [extend]

theorem extend_ne (d : ι) (a : acts d) (p : (e : {e : ι // e ≠ d}) → acts e.val) {e : ι}
    (h : e ≠ d) : extend d a p e = p ⟨e, h⟩ := by
  simp [extend, h]

/-- Splitting a policy at `d` and extending again is the identity.
Source: none: infrastructure
Kind: L -/
theorem extend_split (d : ι) (π : (e : ι) → acts e) :
    extend d (π d) (fun e => π e.val) = π := by
  funext e
  by_cases h : e = d
  · subst h; simp
  · rw [extend_ne d _ _ h]

/-- **The local frame `Loc_d(B)`**: agent `A_d`, environment = the other points' answers × a
chance profile, outcome = the readout of the run of `π_{-d}[d ↦ a]` under the profile — CF-5's
rendering of the point-deviation, with the rest of the policy externalized. Its environment is
literally the product `Y × Z` of FAF's Definition 19, so `loc_multSubagent_fr` is on the nose.
Lazy seeding.
Source: cf-correspondence CF-5 (line 21); mandate §3
Kind: D
Fidelity: exact -/
def Loc (d : ι) (B : Tree Ω ι acts K) : CartesianFrames.Frame (Ω × K) where
  Agent := acts d
  Env := ((e : {e : ι // e ≠ d}) → acts e.val) × ChanceProfile B
  outcome a p := readout B (runLeaf (extend d a p.1) B p.2)

@[simp] theorem Loc_outcome (d : ι) (B : Tree Ω ι acts K) (a : acts d)
    (p : ((e : {e : ι // e ≠ d}) → acts e.val) × ChanceProfile B) :
    (Loc d B).outcome a p = readout B (runLeaf (extend d a p.1) B p.2) := rfl

/-- **T1(b) — `Loc_d(B) ◁ₓ Fr(B)` on the nose** (headline 1): FAF's externalizing Definition 19
with `X := A_d`, `Y := ∏_{e ≠ d} A_e`, `Z := 𝐄_B`, `f a p ε :=` the readout of the run of
`p[d ↦ a]`: the first frame *is* `Loc d B` (`BiextEquiv.refl`), the second is isomorphic to
`Fr B` in `Chu(W)` through the agent bijection `π ↦ (π d, π|_{≠ d})`. Lazy seeding; `d` need
not be queried (an unqueried `d` gives an inert agent, still a multiplicative subagent).
Source: cf-correspondence CF-5 (line 21); mandate T1(b)
Kind: P
Fidelity: exact
Hyps: none -/
theorem loc_multSubagent_fr (d : ι) (B : Tree Ω ι acts K) : Loc d B ◁ₓ Fr B := by
  refine ⟨acts d, (e : {e : ι // e ≠ d}) → acts e.val, ChanceProfile B,
    fun a p ε => readout B (runLeaf (extend d a p) B ε),
    Frame.BiextEquiv.refl _, Frame.biextEquiv_of_nonempty_iso ⟨?_⟩⟩
  exact
    { hom :=
        { agent := fun π => (π d, fun e => π e.val)
          env := id
          adjoint := fun π ε => by
            change readout B (runLeaf π B ε) =
              readout B (runLeaf (extend d (π d) (fun e => π e.val)) B ε)
            rw [extend_split] }
      inv :=
        { agent := fun q => extend d q.1 q.2
          env := id
          adjoint := fun _ _ => rfl }
      hom_inv_id := by
        apply Frame.Hom.ext
        · funext π; exact extend_split d π
        · rfl
      inv_hom_id := by
        apply Frame.Hom.ext
        · funext q
          obtain ⟨a, p⟩ := q
          exact Prod.ext (extend_self d a p) (funext fun e => extend_ne d a p e.property)
        · rfl }

end local_frame

/-! ### T1(c): `Fr B` is the diagonal commitment of the node frame -/

/-- **CF-4: `Fr(B) ≃ᵇ Commit^Δ(Fr^nd(B))`** with `Δ = range diagAssign`. A biextensional
equivalence, not an isomorphism: two policies differing only at points `B` never queries have
the same diagonal assignment (duplicate rows of `Fr B`), and the collapse identifies them. The
homotopy equivalence is `π ↦ diag π` forward and "choose a policy with this diagonal" backward.
Source: cf-correspondence CF-4 (line 19) ("`Fr(B) ≅ Commit^Δ(Fr^nd(B))`" — for the source's
agent set `∏_{d ∈ D_B}` over queried points only; over all of `ι` it is `≃ᵇ`)
Kind: P
Fidelity: variant: `≃ᵇ` in place of `≅` (the agent ranges over all points of `ι`)
Hyps: none -/
theorem fr_biextEquiv_commit_diag (B : Tree Ω ι acts K) :
    Fr B ≃ᵇ (FrNode B).commit (Set.range (diagAssign B)) := by
  classical
  refine Frame.biextEquiv_iff_homotopyEquiv.mpr ⟨?_, ?_, ?_, ?_⟩
  · exact
      { agent := fun π => ⟨diagAssign B π, ⟨π, rfl⟩⟩
        env := id
        adjoint := fun π ε => by
          change readout B (runLeaf π B ε) = readout B (runLeafNode B (diagAssign B π) ε)
          rw [runLeafNode_diagAssign] }
  · exact
      { agent := fun x => Classical.choose x.property
        env := id
        adjoint := fun x ε => by
          change readout B (runLeafNode B x.val ε) =
            readout B (runLeaf (Classical.choose x.property) B ε)
          rw [← runLeafNode_diagAssign, Classical.choose_spec x.property] }
  · intro π ε
    simp only [Frame.id_env, Frame.comp_agent, Function.comp, id]
    change readout B (runLeaf π B ε) =
      readout B (runLeaf (Classical.choose (⟨π, rfl⟩ : diagAssign B π ∈ Set.range (diagAssign B))) B ε)
    rw [← runLeafNode_diagAssign, ← runLeafNode_diagAssign,
      Classical.choose_spec (⟨π, rfl⟩ : diagAssign B π ∈ Set.range (diagAssign B))]
  · intro x ε
    simp only [Frame.id_env, Frame.comp_agent, Function.comp, id]
    change readout B (runLeafNode B x.val ε) =
      readout B (runLeafNode B (diagAssign B (Classical.choose x.property)) ε)
    rw [Classical.choose_spec x.property]

/-- **CF-4's consequence: `Fr B ◁₊ Fr^nd(B)`** by FAF's `commit_addSubagent` and
`AddSubagent.congr`.
Source: cf-correspondence CF-4 (line 19) ("hence `Fr(B) ◁₊ Fr^nd(B)`, CF-paper Claim 30(1)")
Kind: C
Fidelity: exact
Hyps: none -/
theorem fr_addSubagent_frNode (B : Tree Ω ι acts K) : Fr B ◁₊ FrNode B :=
  (Frame.commit_addSubagent (FrNode B) (Set.range (diagAssign B))).congr
    (fr_biextEquiv_commit_diag B).symm (Frame.BiextEquiv.refl _)

/-! ### The claimed observation -/

/-- **The claimed observation of `d`** as an event of `Ω × K`: `S_{O_d} := {(ω, r) | ω ∈ O_d}`,
for the package's observation labels `obs : ι → Finset Ω` (the same `obs` `dp-core-tree`'s
`SubtreeVeridical` reads).
Source: cf-correspondence CF-2 (line 19: `S_X := {(ω, r) ∈ W : ω ⊨ X}`)
Kind: D
Fidelity: exact -/
def SO (obs : ι → Finset Ω) (d : ι) : Set (Ω × K) := {w | w.1 ∈ obs d}

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem mem_SO (obs : ι → Finset Ω) (d : ι) (w : Ω × K) : w ∈ SO obs d ↔ w.1 ∈ obs d :=
  Iff.rfl

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
/-- Membership in `S_{O_d}` is decidable when `Ω` has decidable equality.
Source: none: infrastructure
Kind: D -/
instance [DecidableEq Ω] (obs : ι → Finset Ω) (d : ι) :
    DecidablePred (· ∈ (SO obs d : Set (Ω × K))) :=
  fun (w : Ω × K) => inferInstanceAs (Decidable (w.1 ∈ obs d))

end Cleanroom.Decision.DpCartesianFrames
