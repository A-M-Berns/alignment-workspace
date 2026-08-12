import Mathlib.Data.Set.Basic

/-
# Cartesian frames as a control representation for the deference line

The static-view result says a valuation factoring only through price and realization
cannot see a difference the architectures hide behind that projection
(`StaticViewFactorization.value_eq_of_price_realization_eq`). Its worked case carries the
hidden difference as a dedicated `jurisdiction` field, so the result establishes the
factorization boundary without saying what real structure lives behind it. This file
supplies a candidate: the agent-side counterfactual structure of a Cartesian frame.

Two frames over one world type can agree, on the nose, after the agent coordinate is
restricted to the choice actually taken, and still fail to be biextensionally equivalent.
The separating property is `AgentInert` — whether the outcome varies with the agent
coordinate at all. It is a function of `outcome`, so unlike a `jurisdiction` field it is
not a payload no formula reads; §3's negative-control block shows what that does and does
not buy, and constructs the adversary that a weaker reading of it would admit.

## Status of the Cartesian-frame definitions below

The authoritative formalization of Garrabrant, Herrmann and Lopez-Wild, *Cartesian
Frames* (arXiv:2109.10996) is `CartesianFrames/` in Formalized-Agent-Foundations, verified
at commit `e13dc5bd0117486b1947fbb5643045e14743e98d`. That is not the commit this
repository pins (`lean/lakefile.toml`), and moving the pin is a trust-chain change and so a
maintainer decision, not a round's. §1 therefore
**mirrors** the fragment of that library these constructions need, in a self-contained
form that carries no dependency on Mathlib's category theory. Correspondence, mirrored
name to authoritative name:

| here | `CartesianFrames.Frame.…` | paper node |
|---|---|---|
| `Frame`, `Hom` | `Frame`, `Hom` | Definitions 1, 2 |
| `Hom.comp f g` | `f ≫ g` | Definition 2 |
| `Iso` | `_ ≅ _` in `Chu W` | Definition 3 |
| `Homotopic`, `HomotopyEquiv` | `Homotopic`, `HomotopyEquiv` | Definitions 36, 37 |
| `agentSetoid`, `envSetoid`, `collapse` | same | Definitions 5, 6 |
| `BiextEquiv` | `BiextEquiv` (`≃ᵇ`) | Definition 7 |
| `image` | `image` | Definition 1 |
| `commit` | `commit` | Definition 28 |
| `mapWorlds` | `mapWorlds` | Definition 10 |
| `partitionSections`, `externalQuot` | same | Definitions 31, 32 |
| `AddSubagent`, `MultSubagent` | `AddSubagent` (`◁₊`), `MultSubagent` (`◁ₓ`) | Definitions 18, 19 |

Two renderings differ from the authoritative ones, and both differences are recorded here
rather than left for a reader to find.

*Composition order.* `Hom.comp` is diagrammatic, matching the authoritative `≫` and
reversing the authoritative `Hom.comp`.

*`Iso` is weaker than a categorical isomorphism.* It requires the two **agent** components
to invert each other and says nothing about the environment components, where a
`CategoryTheory.Iso` in `Chu W` requires both. `BiextEquiv` as mirrored is therefore
*weaker* than the authoritative `≃ᵇ` — easier to satisfy — which makes every
`¬ BiextEquiv` proved below **stronger** than its authoritative counterpart, not weaker.
That is the safe direction, and the cross-check proves the authoritative form outright.

The mirror proves one direction of the paper's Claim 39, `HomotopyEquiv.of_biextEquiv`,
which is all the separations here need: a `¬ HomotopyEquiv` yields a `¬ BiextEquiv`. The
converse direction (Claim 38, hence the full Claim 39) is not mirrored, so the positive
equivalences below are stated as `HomotopyEquiv`. Under Claim 39 they read as
biextensional equivalences, and that reading is a citation, not a result of this file.

All names are provisional (`AGENTS.md` standard 6).
-/

namespace Workspace.Deference.Contrib.CartesianFrameBridge

universe u v w

/-! ## 1. Mirrored Cartesian-frame machinery -/

/-- A Cartesian frame over possible worlds `W`. Mirrors `CartesianFrames.Frame`. -/
@[ext]
structure Frame (W : Type u) where
  Agent : Type u
  Env : Type u
  outcome : Agent → Env → W

namespace Frame

variable {W V : Type u}

/-- The worlds some agent choice and environment state jointly select. -/
def image (C : Frame W) : Set W := {w | ∃ a e, C.outcome a e = w}

/-- A frame morphism: covariant on agents, contravariant on environments. -/
structure Hom (C D : Frame W) where
  agent : C.Agent → D.Agent
  env : D.Env → C.Env
  adjoint : ∀ a e, C.outcome a (env e) = D.outcome (agent a) e

/-- The identity morphism. -/
def Hom.id (C : Frame W) : Hom C C where
  agent := fun a => a
  env := fun e => e
  adjoint := fun _ _ => rfl

/-- Composition in diagrammatic order: `f.comp g` is the authoritative `f ≫ g`. -/
def Hom.comp {C D E : Frame W} (f : Hom C D) (g : Hom D E) : Hom C E where
  agent := fun a => g.agent (f.agent a)
  env := fun e => f.env (g.env e)
  adjoint := fun a e => (f.adjoint a (g.env e)).trans (g.adjoint (f.agent a) e)

/-- An isomorphism of frames, componentwise. -/
structure Iso (C D : Frame W) where
  hom : Hom C D
  inv : Hom D C
  agent_left : ∀ a, inv.agent (hom.agent a) = a
  agent_right : ∀ b, hom.agent (inv.agent b) = b

/-- Two parallel morphisms are homotopic when the mixed pair is again a morphism. -/
def Homotopic {C D : Frame W} (f g : Hom C D) : Prop :=
  ∀ a e, C.outcome a (g.env e) = D.outcome (f.agent a) e

/-- Morphisms both ways whose composites are homotopic to the identities. -/
def HomotopyEquiv (C D : Frame W) : Prop :=
  ∃ (φ : Hom C D) (ψ : Hom D C),
    Homotopic (φ.comp ψ) (Hom.id C) ∧ Homotopic (ψ.comp φ) (Hom.id D)

theorem HomotopyEquiv.refl (C : Frame W) : HomotopyEquiv C C :=
  ⟨Hom.id C, Hom.id C, fun _ _ => rfl, fun _ _ => rfl⟩

theorem HomotopyEquiv.symm {C D : Frame W} (h : HomotopyEquiv C D) : HomotopyEquiv D C :=
  let ⟨φ, ψ, hc, hd⟩ := h
  ⟨ψ, φ, hd, hc⟩

theorem HomotopyEquiv.trans {C D E : Frame W}
    (h₀ : HomotopyEquiv C D) (h₁ : HomotopyEquiv D E) : HomotopyEquiv C E := by
  obtain ⟨φ₀, ψ₀, hc₀, hd₀⟩ := h₀
  obtain ⟨φ₁, ψ₁, hc₁, hd₁⟩ := h₁
  refine ⟨φ₀.comp φ₁, ψ₁.comp ψ₀, ?_, ?_⟩
  · intro a e
    have step : ∀ b : D.Agent,
        C.outcome (ψ₀.agent b) e = C.outcome (ψ₀.agent (ψ₁.agent (φ₁.agent b))) e := by
      intro b
      calc C.outcome (ψ₀.agent b) e = D.outcome b (ψ₀.env e) := (ψ₀.adjoint b e).symm
        _ = D.outcome (ψ₁.agent (φ₁.agent b)) (ψ₀.env e) := hc₁ b (ψ₀.env e)
        _ = C.outcome (ψ₀.agent (ψ₁.agent (φ₁.agent b))) e := ψ₀.adjoint _ e
    exact (hc₀ a e).trans (step (φ₀.agent a))
  · intro c e
    have step : ∀ b : D.Agent,
        E.outcome (φ₁.agent b) e = E.outcome (φ₁.agent (φ₀.agent (ψ₀.agent b))) e := by
      intro b
      calc E.outcome (φ₁.agent b) e = D.outcome b (φ₁.env e) := (φ₁.adjoint b e).symm
        _ = D.outcome (φ₀.agent (ψ₀.agent b)) (φ₁.env e) := hd₀ b (φ₁.env e)
        _ = E.outcome (φ₁.agent (φ₀.agent (ψ₀.agent b))) e := φ₁.adjoint _ e
    exact (hd₁ c e).trans (step (ψ₁.agent c))

theorem HomotopyEquiv.ofIso {C D : Frame W} (i : Iso C D) : HomotopyEquiv C D := by
  refine ⟨i.hom, i.inv, fun a e => ?_, fun b e => ?_⟩
  · exact congrArg (fun x => C.outcome x e) (i.agent_left a).symm
  · exact congrArg (fun x => D.outcome x e) (i.agent_right b).symm

/-- Definition 5's relation on agent choices: identical outcome rows. -/
def agentSetoid (C : Frame W) : Setoid C.Agent where
  r a₀ a₁ := ∀ e, C.outcome a₀ e = C.outcome a₁ e
  iseqv := ⟨fun _ _ => rfl, fun h e => (h e).symm, fun h₀ h₁ e => (h₀ e).trans (h₁ e)⟩

/-- Definition 5's relation on environment states: identical outcome columns. -/
def envSetoid (C : Frame W) : Setoid C.Env where
  r e₀ e₁ := ∀ a, C.outcome a e₀ = C.outcome a e₁
  iseqv := ⟨fun _ _ => rfl, fun h a => (h a).symm, fun h₀ h₁ a => (h₀ a).trans (h₁ a)⟩

/-- The biextensional collapse: delete duplicate rows and columns. -/
def collapse (C : Frame W) : Frame W where
  Agent := Quotient C.agentSetoid
  Env := Quotient C.envSetoid
  outcome := Quotient.lift₂ C.outcome fun _ e₀ a₁ _ ha he => (ha e₀).trans (he a₁)

/-- Definition 7's biextensional equivalence: the collapses are isomorphic. -/
def BiextEquiv (C D : Frame W) : Prop := Nonempty (Iso C.collapse D.collapse)

/-- Every frame is homotopy equivalent to its collapse — the representative-selection
argument inside the paper's proof of Claim 39. -/
theorem homotopyEquiv_collapse (C : Frame W) : HomotopyEquiv C C.collapse := by
  refine ⟨⟨fun a => Quotient.mk C.agentSetoid a, fun ê => ê.out, ?_⟩,
    ⟨fun â => â.out, fun e => Quotient.mk C.envSetoid e, ?_⟩, ?_, ?_⟩
  · refine fun a ê => Quotient.inductionOn ê fun e => ?_
    exact Quotient.exact ((Quotient.mk C.envSetoid e).out_eq) a
  · refine fun â e => Quotient.inductionOn â fun a => ?_
    exact (Quotient.exact ((Quotient.mk C.agentSetoid a).out_eq) e).symm
  · intro a e
    exact (Quotient.exact ((Quotient.mk C.agentSetoid a).out_eq) e).symm
  · intro â ê
    show C.collapse.outcome â ê =
      C.collapse.outcome (Quotient.mk C.agentSetoid â.out) ê
    rw [Quotient.out_eq]

/-- The direction of Claim 39 the separations below use. -/
theorem HomotopyEquiv.of_biextEquiv {C D : Frame W} (h : BiextEquiv C D) :
    HomotopyEquiv C D :=
  ((homotopyEquiv_collapse C).trans (HomotopyEquiv.ofIso h.some)).trans
    (homotopyEquiv_collapse D).symm

/-- `image` is a homotopy-equivalence invariant. -/
theorem image_eq_of_homotopyEquiv {C D : Frame W} (h : HomotopyEquiv C D) :
    C.image = D.image := by
  have key : ∀ {C₀ D₀ : Frame W}, HomotopyEquiv C₀ D₀ → D₀.image ⊆ C₀.image := by
    rintro C₀ D₀ ⟨φ, ψ, -, hd⟩ w ⟨b, e, rfl⟩
    exact ⟨ψ.agent b, φ.env e, (φ.adjoint (ψ.agent b) e).trans (hd b e).symm⟩
  exact Set.ext fun _ => ⟨fun hw => key h.symm hw, fun hw => key h hw⟩

/-- Definition 10's world map `p°`: push outcomes through `p`, keeping both carriers. -/
def mapWorlds (p : W → V) (C : Frame W) : Frame V where
  Agent := C.Agent
  Env := C.Env
  outcome := fun a e => p (C.outcome a e)

/-- Definition 28's `Commit^B`: restrict the agent to `B`. -/
def commit (C : Frame W) (B : Set C.Agent) : Frame W where
  Agent := B
  Env := C.Env
  outcome := fun b e => C.outcome b.val e

/-- Definition 31's `Y/X`: the choice functions selecting one element of each cell. -/
def partitionSections {α : Type u} (s : Setoid α) : Type u :=
  {q : Quotient s → α // ∀ c, Quotient.mk s (q c) = c}

/-- Definition 32's `External^{/B}`: the agent becomes the cells, the environment gains
the choice-function coordinate. -/
def externalQuot (C : Frame W) (s : Setoid C.Agent) : Frame W where
  Agent := Quotient s
  Env := partitionSections s × C.Env
  outcome := fun c p => C.outcome (p.1.val c) p.2

/-- Definition 18's committing definition of additive subagent. -/
def AddSubagent (C D : Frame W) : Prop :=
  ∃ (Y Z : Type u) (X : Set Y) (f : Y → Z → W),
    HomotopyEquiv C { Agent := X, Env := Z, outcome := fun x z => f x.val z } ∧
    HomotopyEquiv D { Agent := Y, Env := Z, outcome := f }

/-- Definition 19's externalizing definition of multiplicative subagent. -/
def MultSubagent (C D : Frame W) : Prop :=
  ∃ (X Y Z : Type u) (f : X → Y → Z → W),
    HomotopyEquiv C { Agent := X, Env := Y × Z, outcome := fun x p => f x p.1 p.2 } ∧
    HomotopyEquiv D { Agent := X × Y, Env := Z, outcome := fun p z => f p.1 p.2 z }

/-- Claim 30(1): committing produces additive subagents. -/
theorem commit_addSubagent (C : Frame W) (B : Set C.Agent) :
    AddSubagent (C.commit B) C :=
  ⟨C.Agent, C.Env, B, C.outcome, HomotopyEquiv.refl _, HomotopyEquiv.refl _⟩

/-- The one-cell partition of a nonempty carrier. -/
def totalSetoid (α : Type u) : Setoid α where
  r _ _ := True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

instance instSubsingletonTotalQuotient (α : Type u) :
    Subsingleton (Quotient (totalSetoid α)) :=
  ⟨fun x y => Quotient.inductionOn₂ x y fun _ _ => Quotient.sound trivial⟩

/-- Every element of a one-cell partition is the value of a constant section. -/
def constSection {α : Type u} (a : α) : partitionSections (totalSetoid α) :=
  ⟨fun _ => a, fun c => Subsingleton.elim _ c⟩

/-- Claim 34/45(1) at the one-cell partition: externalizing produces multiplicative
subagents. The whole agent choice moves to the environment side. -/
theorem externalQuot_multSubagent_total (C : Frame W) :
    MultSubagent (C.externalQuot (totalSetoid C.Agent)) C := by
  refine ⟨Quotient (totalSetoid C.Agent), partitionSections (totalSetoid C.Agent), C.Env,
    fun c q e => C.outcome (q.val c) e, HomotopyEquiv.refl _, ?_⟩
  refine ⟨⟨fun a => (Quotient.mk _ a, constSection a), fun e => e, fun a e => rfl⟩,
    ⟨fun p => p.2.val p.1, fun e => e, fun p e => rfl⟩, ?_, ?_⟩
  · exact fun a e => rfl
  · rintro ⟨c, q⟩ e
    exact congrArg (fun x => C.outcome (q.val x) e) (Subsingleton.elim _ c)

/-! ## 2. Effective agency, and why it is not a label

`AgentInert C` says the agent coordinate does no work: the world is the same whatever the
agent chooses. It is the degenerate case of practical control, and — unlike a field
recording who is in charge — it is preserved by the coarsest equivalence Cartesian frames
carry. That is the formal content of the claim that the separations in §3 and §4 do not
smuggle jurisdiction into the world type. -/

/-- The agent coordinate does no work. Provisional name. -/
def AgentInert (C : Frame W) : Prop :=
  ∀ (a₀ a₁ : C.Agent) (e : C.Env), C.outcome a₀ e = C.outcome a₁ e

/-- `AgentInert` transfers backwards along a homotopy equivalence. -/
theorem AgentInert.of_homotopyEquiv {C D : Frame W} (h : HomotopyEquiv C D)
    (hD : AgentInert D) : AgentInert C := by
  obtain ⟨φ, ψ, hc, -⟩ := h
  intro a₀ a₁ e
  calc C.outcome a₀ e = C.outcome (ψ.agent (φ.agent a₀)) e := hc a₀ e
    _ = D.outcome (φ.agent a₀) (ψ.env e) := (ψ.adjoint (φ.agent a₀) e).symm
    _ = D.outcome (φ.agent a₁) (ψ.env e) := hD _ _ _
    _ = C.outcome (ψ.agent (φ.agent a₁)) e := ψ.adjoint _ e
    _ = C.outcome a₁ e := (hc a₁ e).symm

/-- `AgentInert` is a homotopy-equivalence invariant. -/
theorem AgentInert.iff_of_homotopyEquiv {C D : Frame W} (h : HomotopyEquiv C D) :
    AgentInert C ↔ AgentInert D :=
  ⟨fun hC => AgentInert.of_homotopyEquiv h.symm hC, AgentInert.of_homotopyEquiv h⟩

/-- `AgentInert` is a biextensional-equivalence invariant: it survives the collapse that
deletes duplicate rows and columns, so a frame cannot acquire or lose it by adding
behaviourally redundant agent choices. -/
theorem AgentInert.iff_of_biextEquiv {C D : Frame W} (h : BiextEquiv C D) :
    AgentInert C ↔ AgentInert D :=
  AgentInert.iff_of_homotopyEquiv (HomotopyEquiv.of_biextEquiv h)

/-- The separation tool: frames differing in `AgentInert` are not biextensionally
equivalent. -/
theorem not_biextEquiv_of_agentInert_ne {C D : Frame W}
    (hC : ¬ AgentInert C) (hD : AgentInert D) : ¬ BiextEquiv C D :=
  fun h => hC ((AgentInert.iff_of_biextEquiv h).mpr hD)

end Frame

open Frame

/-! ## 3. Delegation and simulation over one world type

The world records what was executed and an exogenous coordinate. It carries no field
naming a controller; the two architectures below differ only in `outcome`, over identical
agent and environment carriers. -/

/-- Provisional. The executed action and one exogenous coordinate. -/
@[ext]
structure World where
  executed : Bool
  disturbance : Bool
  deriving DecidableEq

/-- The principal's frame under delegation: execution tracks the principal's disposition.
Provisional name. -/
abbrev delegated : Frame World where
  Agent := Bool
  Env := Bool
  outcome := fun h s => ⟨h, s⟩

/-- The principal's frame under simulation: the executed action is supplied by another
process at the value `h₀`, and does not vary with the principal's disposition. Provisional
name. -/
abbrev simulated (h₀ : Bool) : Frame World where
  Agent := Bool
  Env := Bool
  outcome := fun _ s => ⟨h₀, s⟩

/-- Restriction of the agent coordinate to a single choice. This is the shape of the
current deference view's input: once the realization map is taken, the agent's
counterfactual coordinate has already been quotiented away. Provisional name. -/
def pin (C : Frame W) (a : C.Agent) : Frame W where
  Agent := PUnit
  Env := C.Env
  outcome := fun _ e => C.outcome a e

/-- `pin` is `Commit` to a singleton, up to homotopy equivalence — it is not a new
operation. -/
theorem pin_homotopyEquiv_commit {W : Type u} (C : Frame W) (a : C.Agent) :
    HomotopyEquiv (pin C a) (C.commit {a}) := by
  refine ⟨⟨fun _ => ⟨a, rfl⟩, fun e => e, fun _ _ => rfl⟩,
    ⟨fun _ => PUnit.unit, fun e => e, fun b e => ?_⟩, fun _ _ => rfl, fun b e => ?_⟩
  · exact congrArg (fun x => C.outcome x e) b.property
  · exact congrArg (fun x => C.outcome x e) b.property

/-- **The premise.** At the disposition actually held, delegation and simulation are the
same object: the perfect simulator agrees with the principal on the realized play, for
every environment state. Negative control N3. -/
theorem pin_delegated_eq_pin_simulated (h₀ : Bool) :
    pin delegated h₀ = pin (simulated h₀) h₀ := rfl

/-- Simulation leaves the principal's agent coordinate inert. -/
theorem simulated_agentInert (h₀ : Bool) : AgentInert (simulated h₀) :=
  fun _ _ _ => rfl

/-- Delegation does not. -/
theorem delegated_not_agentInert : ¬ AgentInert delegated := by
  intro h
  exact absurd (h false true false) (by decide)

/-- **The separation.** The two architectures are not biextensionally equivalent, so the
distinction is not an artifact of duplicate agent choices. Negative control N2. -/
theorem delegated_not_biextEquiv_simulated (h₀ : Bool) :
    ¬ BiextEquiv delegated (simulated h₀) :=
  not_biextEquiv_of_agentInert_ne delegated_not_agentInert (simulated_agentInert h₀)

/-- **The blindness.** Any functional of the pinned frame pushed through any world map
assigns the two architectures the same value. This is the Cartesian-frame form of
`StaticViewFactorization.value_eq_of_price_realization_eq`, with the difference the
valuation cannot see identified as agent-side counterfactual structure rather than as a
dedicated field. -/
theorem commitment_view_blind {V : Type} {Value : Type v} (p : World → V)
    (valuation : Frame V → Value) (h₀ : Bool) :
    valuation (mapWorlds p (pin delegated h₀))
      = valuation (mapWorlds p (pin (simulated h₀) h₀)) := rfl

theorem agentInert_is_invariant {C D : Frame World} (h : BiextEquiv C D) :
    AgentInert C ↔ AgentInert D :=
  AgentInert.iff_of_biextEquiv h

/-! ### Negative control N1: what invariance does and does not certify

Being separated by a biextensional-equivalence invariant does **not** certify that a
separation is structural rather than a relabelling. `image` is such an invariant, so any
property reading a world coordinate through `image` is one too, and a controller label
moved from the architecture record into the world type passes that test.

The construction below is the adversary. `labelledHuman` and `labelledAgent` differ only
in the value of a `controller` coordinate their outcomes write; both are agent-active, so
`AgentInert` does no work; and they are separated at biextensional equivalence by their
images alone.

What separates the adversary from §3 is robustness under world maps. The label separation
is destroyed by the world map that forgets the label while keeping the executed action.
The §3 separation is destroyed by no world map that distinguishes the executed action at
any environment state. **That is a structural argument, not a proof that no label can
pass it.** -/

/-- A world type carrying a controller label, for the adversarial construction. Provisional
name. -/
@[ext]
structure LabelledWorld where
  executed : Bool
  controller : Bool
  deriving DecidableEq

abbrev labelledHuman : Frame LabelledWorld where
  Agent := Bool
  Env := Bool
  outcome := fun h _ => ⟨h, true⟩

abbrev labelledAgent : Frame LabelledWorld where
  Agent := Bool
  Env := Bool
  outcome := fun h _ => ⟨h, false⟩

theorem labelledHuman_not_agentInert : ¬ AgentInert labelledHuman := by
  intro h
  exact absurd (h false true false) (by decide)

theorem labelledAgent_not_agentInert : ¬ AgentInert labelledAgent := by
  intro h
  exact absurd (h false true false) (by decide)

theorem labelledHuman_image :
    labelledHuman.image = {w : LabelledWorld | w.controller = true} := by
  refine Set.ext fun w => ⟨?_, fun hw => ⟨w.executed, false, LabelledWorld.ext rfl hw.symm⟩⟩
  rintro ⟨a, -, rfl⟩
  rfl

theorem labelledAgent_image :
    labelledAgent.image = {w : LabelledWorld | w.controller = false} := by
  refine Set.ext fun w => ⟨?_, fun hw => ⟨w.executed, false, LabelledWorld.ext rfl hw.symm⟩⟩
  rintro ⟨a, -, rfl⟩
  rfl

/-- The adversary passes the test: a pure controller label separates two agent-active
frames at biextensional equivalence. -/
theorem labelledHuman_not_biextEquiv_labelledAgent :
    ¬ BiextEquiv labelledHuman labelledAgent := by
  intro h
  have himg := image_eq_of_homotopyEquiv (HomotopyEquiv.of_biextEquiv h)
  rw [labelledHuman_image, labelledAgent_image] at himg
  have hmem : (⟨true, true⟩ : LabelledWorld) ∈ {w : LabelledWorld | w.controller = false} := by
    rw [← himg]; rfl
  exact absurd hmem (by decide)

/-- …and it fails the world-map test: forgetting the label, and keeping the executed
action, makes the two frames the same object. -/
theorem mapWorlds_forgetLabel :
    mapWorlds LabelledWorld.executed labelledHuman
      = mapWorlds LabelledWorld.executed labelledAgent := rfl

/-- `AgentInert` is carried by every world map. -/
theorem agentInert_mapWorlds {W V : Type} {C : Frame W} (p : W → V) (h : AgentInert C) :
    AgentInert (mapWorlds p C) :=
  fun a₀ a₁ e => congrArg p (h a₀ a₁ e)

/-- The §3 separation survives every world map that distinguishes the executed action at
even one environment state. No world map plays the role `forgetLabel` plays above. -/
theorem mapWorlds_delegated_not_biextEquiv_simulated {V : Type} (p : World → V)
    (h₀ s : Bool) (hp : p ⟨true, s⟩ ≠ p ⟨false, s⟩) :
    ¬ BiextEquiv (mapWorlds p delegated) (mapWorlds p (simulated h₀)) :=
  not_biextEquiv_of_agentInert_ne (fun h => hp (h true false s)) (fun _ _ _ => rfl)

/-! ### What the separation does and does not see: dependence, not agreement

`simRead f` executes `f` of the principal's disposition. `f = id` is `delegated` and
`f = fun _ => h₀` is `simulated h₀`, both definitionally, so the family contains both arms
of §3. The invariant reads whether execution *varies with* the principal's coordinate, and
that is strictly weaker than tracking it: a process executing the principal's disposition
**negated** is biextensionally equivalent to delegation.

This is the round's central negative finding about delegation versus simulation. A process
that accurately predicts the principal is, by construction, one whose output varies with
the principal's disposition — so Cartesian frames identify it with delegation, and the
case the deference line asked about is not separated. What is separated is a process
supplying a fixed value that happens to coincide. -/

/-- A process executing `f` of the principal's disposition. Provisional name. -/
abbrev simRead (f : Bool → Bool) : Frame World where
  Agent := Bool
  Env := Bool
  outcome := fun h s => ⟨f h, s⟩

theorem simRead_id_eq_delegated : simRead id = delegated := rfl

theorem simRead_const_eq_simulated (h₀ : Bool) : simRead (fun _ => h₀) = simulated h₀ := rfl

/-- A process executing the **opposite** of the principal's disposition is homotopy
equivalent — hence, by Claim 39, biextensionally equivalent — to delegation. No invariant
in this file separates them. -/
theorem simRead_not_homotopyEquiv_delegated : HomotopyEquiv (simRead not) delegated := by
  refine ⟨⟨fun h => !h, fun e => e, fun a e => rfl⟩,
    ⟨fun h => !h, fun e => e, fun a e => by cases a <;> rfl⟩, ?_, ?_⟩
  · intro a e; cases a <;> rfl
  · intro a e; cases a <;> rfl

/-! ## 4. Preservation, foreclosure and transfer of future corrective agency

The same three frames read at a later index: the future principal's corrective frame under
a present action that preserves correction, one that forecloses it, and one that moves it
to another process. The present actions have the same immediate effect; they differ only in
the future frame they induce. -/

/-- The future principal's corrective frame when correction is preserved. Provisional
name. -/
abbrev preserve : Frame World where
  Agent := Bool
  Env := Bool
  outcome := fun c s => ⟨c, s⟩

/-- The future principal's corrective frame when the present action forecloses correction:
the outcome is fixed at `d₀` whatever the principal does. Provisional name. -/
abbrev foreclose (d₀ : Bool) : Frame World where
  Agent := Bool
  Env := Bool
  outcome := fun _ s => ⟨d₀, s⟩

/-- The future principal's corrective frame when the corrective degree of freedom is
transferred: it is still exercised, but from the environment side. Provisional name. -/
abbrev transfer : Frame World where
  Agent := Bool
  Env := Bool × Bool
  outcome := fun _ p => ⟨p.1, p.2⟩

/-- Preservation is not a matter of counting syntactic actions: the preserved frame has
agent choices that actually move the world. Negative control N4. -/
theorem preserve_not_agentInert : ¬ AgentInert preserve := by
  intro h
  exact absurd (h false true false) (by decide)

theorem foreclose_agentInert (d₀ : Bool) : AgentInert (foreclose d₀) := fun _ _ _ => rfl

theorem transfer_agentInert : AgentInert transfer := fun _ _ _ => rfl

/-- Foreclosure is a proper restriction: the foreclosed frame is not biextensionally
equivalent to the preserved one. Negative control N5. -/
theorem foreclose_not_biextEquiv_preserve (d₀ : Bool) :
    ¬ BiextEquiv preserve (foreclose d₀) :=
  not_biextEquiv_of_agentInert_ne preserve_not_agentInert (foreclose_agentInert d₀)

/-- Transfer is likewise a proper loss of the principal's control. -/
theorem transfer_not_biextEquiv_preserve : ¬ BiextEquiv preserve transfer :=
  not_biextEquiv_of_agentInert_ne preserve_not_agentInert transfer_agentInert

/-- **Foreclosure as commitment.** The foreclosed future frame is the preserved one with
the agent restricted to the single choice the present action leaves available. -/
theorem foreclose_homotopyEquiv_commit (d₀ : Bool) :
    HomotopyEquiv (foreclose d₀) (preserve.commit {d₀}) := by
  refine HomotopyEquiv.trans ?_ (pin_homotopyEquiv_commit preserve d₀)
  exact ⟨⟨fun _ => PUnit.unit, fun e => e, fun _ _ => rfl⟩,
    ⟨fun _ => false, fun e => e, fun _ _ => rfl⟩, fun _ _ => rfl, fun _ _ => rfl⟩

/-- The restricted frame is an additive subagent of the preserved one, by Claim 30. -/
theorem commit_preserve_addSubagent (d₀ : Bool) :
    AddSubagent (preserve.commit {d₀}) preserve :=
  Frame.commit_addSubagent preserve {d₀}

/-- **Transfer as externalization.** The transferred future frame is the preserved one
with the corrective coordinate moved from the agent side to the environment side. -/
theorem transfer_homotopyEquiv_externalQuot :
    HomotopyEquiv transfer (preserve.externalQuot (totalSetoid preserve.Agent)) := by
  refine ⟨⟨fun _ => Quotient.mk _ true, fun p => (p.1.val (Quotient.mk _ true), p.2),
      fun _ _ => rfl⟩,
    ⟨fun _ => true, fun p => (constSection p.1, p.2), fun _ _ => rfl⟩,
    fun _ _ => rfl, ?_⟩
  rintro c ⟨q, s⟩
  have hc : c = Quotient.mk (totalSetoid preserve.Agent) true :=
    Subsingleton.elim (α := Quotient (totalSetoid preserve.Agent)) c _
  exact congrArg (fun x => preserve.outcome (q.val x) s) hc

/-- The externalized frame is a multiplicative subagent of the preserved one, by
Claim 34/45. -/
theorem externalQuot_preserve_multSubagent :
    MultSubagent (preserve.externalQuot (totalSetoid preserve.Agent)) preserve :=
  Frame.externalQuot_multSubagent_total preserve

/-! ### The invariant that separates restriction from externalization

Both foreclosure and transfer leave the future principal's agent coordinate inert. They
differ in whether the worlds the corrective coordinate used to reach are still reached:
commitment shrinks the image, externalization preserves it. -/

theorem preserve_image : preserve.image = Set.univ :=
  Set.eq_univ_of_forall fun w => ⟨w.executed, w.disturbance, rfl⟩

theorem foreclose_image (d₀ : Bool) :
    (foreclose d₀).image = {w : World | w.executed = d₀} := by
  refine Set.ext fun w => ⟨?_, fun hw => ⟨true, w.disturbance, ?_⟩⟩
  · rintro ⟨-, s, rfl⟩
    rfl
  · exact World.ext hw.symm rfl

/-- Commitment shrinks the reachable worlds. -/
theorem foreclose_image_ne_preserve (d₀ : Bool) :
    (foreclose d₀).image ≠ preserve.image := by
  rw [foreclose_image, preserve_image]
  intro h
  have hmem : (⟨!d₀, false⟩ : World) ∈ {w : World | w.executed = d₀} := by
    rw [h]; trivial
  exact absurd hmem (by cases d₀ <;> decide)

/-- Externalization does not: the same worlds remain reachable, from the environment
side. -/
theorem transfer_image : transfer.image = preserve.image := by
  rw [preserve_image]
  exact Set.eq_univ_of_forall fun w => ⟨true, (w.executed, w.disturbance), rfl⟩

/-- **Negative control on the externalization reading.** `transfer` is equivalent to a
frame whose agent carrier is a single point and whose executed coordinate is simply part
of the environment. Nothing in the representation distinguishes "another process exercises
the correction" from "the corrective coordinate is exogenous": a frame has no notion of
*whose* environment state a coordinate is. -/
theorem transfer_homotopyEquiv_exogenous :
    HomotopyEquiv transfer
      { Agent := PUnit, Env := Bool × Bool, outcome := fun _ p => ⟨p.1, p.2⟩ } :=
  ⟨⟨fun _ => PUnit.unit, fun e => e, fun _ _ => rfl⟩,
    ⟨fun _ => true, fun e => e, fun _ _ => rfl⟩, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Consequently foreclosure and transfer are themselves distinguishable, and the two
CF-native operations are not interchangeable models of losing corrective agency. -/
theorem foreclose_not_biextEquiv_transfer (d₀ : Bool) :
    ¬ BiextEquiv (foreclose d₀) transfer := by
  intro h
  refine foreclose_image_ne_preserve d₀ ?_
  rw [image_eq_of_homotopyEquiv (HomotopyEquiv.of_biextEquiv h), transfer_image]

/-- The preserve/foreclose pair reproduces §3's blindness at the later index: the
immediate realized play is identical and every functional of it agrees. -/
theorem later_commitment_view_blind {V : Type} {Value : Type v} (p : World → V)
    (valuation : Frame V → Value) (d₀ : Bool) :
    valuation (mapWorlds p (pin preserve d₀))
      = valuation (mapWorlds p (pin (foreclose d₀) d₀)) := rfl

/-! ### The two-stage statement

The present index and the later index in one object: a present action is chosen, its
immediate effect is the same whichever is chosen, and the corrective frame it leaves the
future principal is not. -/

/-- The present action available to the acting process. Provisional name. -/
inductive PresentAction where
  | preserveCorrection
  | forecloseCorrection
  | transferCorrection
  deriving DecidableEq

/-- The present stage as a frame: the acting process chooses, the environment supplies the
disturbance, and the immediately executed action is `false` whatever is chosen. Provisional
name. -/
abbrev presentStage : Frame World where
  Agent := PresentAction
  Env := Bool
  outcome := fun _ s => ⟨false, s⟩

/-- The corrective frame each present action leaves the future principal. Provisional
name. -/
def futureFrame : PresentAction → Frame World
  | .preserveCorrection => preserve
  | .forecloseCorrection => foreclose false
  | .transferCorrection => transfer

/-- At the present index the three actions are indistinguishable — not merely equal in
their executed action, but inert in the present frame. -/
theorem presentStage_agentInert : AgentInert presentStage := fun _ _ _ => rfl

/-- **The two-stage separation.** Three present actions with an inert present frame induce
pairwise non-equivalent future corrective frames. -/
theorem futureFrame_separates :
    ¬ BiextEquiv (futureFrame .preserveCorrection) (futureFrame .forecloseCorrection) ∧
      ¬ BiextEquiv (futureFrame .preserveCorrection) (futureFrame .transferCorrection) ∧
      ¬ BiextEquiv (futureFrame .forecloseCorrection) (futureFrame .transferCorrection) :=
  ⟨foreclose_not_biextEquiv_preserve false, transfer_not_biextEquiv_preserve,
    foreclose_not_biextEquiv_transfer false⟩

#print axioms Frame.HomotopyEquiv.trans
#print axioms Frame.HomotopyEquiv.ofIso
#print axioms Frame.homotopyEquiv_collapse
#print axioms Frame.HomotopyEquiv.of_biextEquiv
#print axioms Frame.image_eq_of_homotopyEquiv
#print axioms Frame.commit_addSubagent
#print axioms Frame.externalQuot_multSubagent_total
#print axioms Frame.AgentInert.of_homotopyEquiv
#print axioms Frame.AgentInert.iff_of_biextEquiv
#print axioms Frame.not_biextEquiv_of_agentInert_ne
#print axioms pin_homotopyEquiv_commit
#print axioms pin_delegated_eq_pin_simulated
#print axioms simulated_agentInert
#print axioms delegated_not_agentInert
#print axioms delegated_not_biextEquiv_simulated
#print axioms commitment_view_blind
#print axioms agentInert_is_invariant
#print axioms labelledHuman_not_agentInert
#print axioms labelledAgent_not_agentInert
#print axioms labelledHuman_image
#print axioms labelledAgent_image
#print axioms labelledHuman_not_biextEquiv_labelledAgent
#print axioms mapWorlds_forgetLabel
#print axioms agentInert_mapWorlds
#print axioms mapWorlds_delegated_not_biextEquiv_simulated
#print axioms simRead_id_eq_delegated
#print axioms simRead_const_eq_simulated
#print axioms simRead_not_homotopyEquiv_delegated
#print axioms preserve_not_agentInert
#print axioms foreclose_agentInert
#print axioms transfer_agentInert
#print axioms foreclose_not_biextEquiv_preserve
#print axioms transfer_not_biextEquiv_preserve
#print axioms foreclose_homotopyEquiv_commit
#print axioms commit_preserve_addSubagent
#print axioms transfer_homotopyEquiv_externalQuot
#print axioms externalQuot_preserve_multSubagent
#print axioms preserve_image
#print axioms foreclose_image
#print axioms foreclose_image_ne_preserve
#print axioms transfer_image
#print axioms transfer_homotopyEquiv_exogenous
#print axioms foreclose_not_biextEquiv_transfer
#print axioms later_commitment_view_blind
#print axioms presentStage_agentInert
#print axioms futureFrame_separates

end Workspace.Deference.Contrib.CartesianFrameBridge
