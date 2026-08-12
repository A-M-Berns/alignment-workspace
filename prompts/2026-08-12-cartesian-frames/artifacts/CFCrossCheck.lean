import CartesianFrames

/-
# Cross-check: the deference bridge statements against the authoritative Cartesian Frames

Every statement here is the authoritative-library counterpart of a declaration in
`Workspace/Deference/Contrib/CartesianFrameBridge.lean` (alignment-workspace). It uses
`CartesianFrames.Frame`, its real `≃ᵇ`, `◁₊`, `◁ₓ`, `commit`, `externalQuot` and
`image` — no mirrored definitions. Because Claim 39 is available in both directions here,
the positive results are stated as genuine biextensional equivalences rather than as
homotopy equivalences.

This file is evidence, not a contribution to this repository: it is committed under the
alignment-workspace round directory and compiled against Formalized-Agent-Foundations.

**Verified at `e13dc5bd0117486b1947fbb5643045e14743e98d`**, which is the head of both
`main` and `cartesian-frames-formalization` there. To re-verify: copy this file to the
root of such a checkout and run `lake env lean CFCrossCheck.lean`. Every declaration must
report axioms within `[propext, Classical.choice, Quot.sound]`.
-/

open CartesianFrames
open scoped CartesianFrames.Frame

namespace CFDeferenceCrossCheck

@[ext]
structure World where
  executed : Bool
  disturbance : Bool
  deriving DecidableEq

/-! ## The frames -/

abbrev delegated : CartesianFrames.Frame World where
  Agent := Bool
  Env := Bool
  outcome := fun h s => ⟨h, s⟩

abbrev simulated (h₀ : Bool) : CartesianFrames.Frame World where
  Agent := Bool
  Env := Bool
  outcome := fun _ s => ⟨h₀, s⟩

abbrev preserve : CartesianFrames.Frame World where
  Agent := Bool
  Env := Bool
  outcome := fun c s => ⟨c, s⟩

abbrev foreclose (d₀ : Bool) : CartesianFrames.Frame World where
  Agent := Bool
  Env := Bool
  outcome := fun _ s => ⟨d₀, s⟩

abbrev transfer : CartesianFrames.Frame World where
  Agent := Bool
  Env := Bool × Bool
  outcome := fun _ p => ⟨p.1, p.2⟩

/-! ## Effective agency is a `≃ᵇ`-invariant -/

def AgentInert {W : Type} (C : CartesianFrames.Frame W) : Prop :=
  ∀ (a₀ a₁ : C.Agent) (e : C.Env), C.outcome a₀ e = C.outcome a₁ e

theorem AgentInert.of_biextEquiv {W : Type} {C D : CartesianFrames.Frame W}
    (h : C ≃ᵇ D) (hD : AgentInert D) : AgentInert C := by
  obtain ⟨φ, ψ, hc, -⟩ := Frame.biextEquiv_iff_homotopyEquiv.mp h
  intro a₀ a₁ e
  calc C.outcome a₀ e = C.outcome (ψ.agent (φ.agent a₀)) e := hc a₀ e
    _ = D.outcome (φ.agent a₀) (ψ.env e) := (ψ.adjoint (φ.agent a₀) e).symm
    _ = D.outcome (φ.agent a₁) (ψ.env e) := hD _ _ _
    _ = C.outcome (ψ.agent (φ.agent a₁)) e := ψ.adjoint _ e
    _ = C.outcome a₁ e := (hc a₁ e).symm

theorem not_biextEquiv_of_agentInert_ne {W : Type} {C D : CartesianFrames.Frame W}
    (hC : ¬ AgentInert C) (hD : AgentInert D) : ¬ (C ≃ᵇ D) :=
  fun h => hC (AgentInert.of_biextEquiv h hD)

/-! ## Delegation versus simulation -/

def pin {W : Type} (C : CartesianFrames.Frame W) (a : C.Agent) : CartesianFrames.Frame W where
  Agent := PUnit
  Env := C.Env
  outcome := fun _ e => C.outcome a e

theorem pin_biextEquiv_commit {W : Type} (C : CartesianFrames.Frame W) (a : C.Agent) :
    pin C a ≃ᵇ C.commit {a} :=
  Frame.biextEquiv_iff_homotopyEquiv.mpr
    ⟨{ agent := fun _ => ⟨a, rfl⟩, env := fun e => e, adjoint := fun _ _ => rfl },
     { agent := fun _ => PUnit.unit, env := fun e => e,
       adjoint := fun b e => congrArg (fun x => C.outcome x e) b.property },
     fun _ _ => rfl,
     fun b e => congrArg (fun x => C.outcome x e) b.property⟩

theorem pin_delegated_eq_pin_simulated (h₀ : Bool) :
    pin delegated h₀ = pin (simulated h₀) h₀ := rfl

theorem simulated_agentInert (h₀ : Bool) : AgentInert (simulated h₀) := fun _ _ _ => rfl

theorem delegated_not_agentInert : ¬ AgentInert delegated := by
  intro h
  exact absurd (h false true false) (by decide)

theorem delegated_not_biextEquiv_simulated (h₀ : Bool) :
    ¬ (delegated ≃ᵇ simulated h₀) :=
  not_biextEquiv_of_agentInert_ne delegated_not_agentInert (simulated_agentInert h₀)

theorem commitment_view_blind {V : Type} {Value : Type} (p : World → V)
    (valuation : CartesianFrames.Frame V → Value) (h₀ : Bool) :
    valuation ((Frame.mapWorlds p).obj (pin delegated h₀))
      = valuation ((Frame.mapWorlds p).obj (pin (simulated h₀) h₀)) := rfl

/-! ## Negative control N1: a controller label passes the invariance test

`labelledHuman` and `labelledAgent` differ only in a controller coordinate their outcomes
write. Both are agent-active, and they are separated at the real `≃ᵇ` by `image` alone —
so being separated by a `≃ᵇ`-invariant does not certify a separation as structural. The
asymmetry that survives is under world maps: forgetting the label collapses this pair, and
no world map retaining the executed action collapses the pair in the section above. -/

@[ext]
structure LabelledWorld where
  executed : Bool
  controller : Bool
  deriving DecidableEq

abbrev labelledHuman : CartesianFrames.Frame LabelledWorld where
  Agent := Bool
  Env := Bool
  outcome := fun h _ => ⟨h, true⟩

abbrev labelledAgent : CartesianFrames.Frame LabelledWorld where
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

theorem labelledHuman_not_biextEquiv_labelledAgent :
    ¬ (labelledHuman ≃ᵇ labelledAgent) := by
  intro h
  have himg := Frame.image_eq_of_biextEquiv h
  rw [labelledHuman_image, labelledAgent_image] at himg
  have hmem : (⟨true, true⟩ : LabelledWorld) ∈ {w : LabelledWorld | w.controller = false} := by
    rw [← himg]; rfl
  exact absurd hmem (by decide)

theorem mapWorlds_forgetLabel :
    (Frame.mapWorlds LabelledWorld.executed).obj labelledHuman
      = (Frame.mapWorlds LabelledWorld.executed).obj labelledAgent := rfl

theorem mapWorlds_delegated_not_biextEquiv_simulated {V : Type} (p : World → V)
    (h₀ s : Bool) (hp : p ⟨true, s⟩ ≠ p ⟨false, s⟩) :
    ¬ ((Frame.mapWorlds p).obj delegated ≃ᵇ (Frame.mapWorlds p).obj (simulated h₀)) :=
  not_biextEquiv_of_agentInert_ne (fun h => hp (h true false s)) (fun _ _ _ => rfl)

/-! ## Dependence, not agreement -/

abbrev simRead (f : Bool → Bool) : CartesianFrames.Frame World where
  Agent := Bool
  Env := Bool
  outcome := fun h s => ⟨f h, s⟩

theorem simRead_id_eq_delegated : simRead id = delegated := rfl

theorem simRead_const_eq_simulated (h₀ : Bool) : simRead (fun _ => h₀) = simulated h₀ := rfl

/-- A process executing the opposite of the principal's disposition is biextensionally
equivalent to delegation. -/
theorem simRead_not_biextEquiv_delegated : simRead not ≃ᵇ delegated := by
  refine Frame.biextEquiv_iff_homotopyEquiv.mpr
    ⟨{ agent := fun h => !h, env := fun e => e, adjoint := fun _ _ => rfl },
     { agent := fun h => !h, env := fun e => e, adjoint := fun a e => by cases a <;> rfl },
     ?_, ?_⟩
  · intro a e; cases a <;> rfl
  · intro a e; cases a <;> rfl

/-! ## Preservation, foreclosure, transfer -/

theorem preserve_not_agentInert : ¬ AgentInert preserve := by
  intro h
  exact absurd (h false true false) (by decide)

theorem foreclose_agentInert (d₀ : Bool) : AgentInert (foreclose d₀) := fun _ _ _ => rfl

theorem transfer_agentInert : AgentInert transfer := fun _ _ _ => rfl

theorem foreclose_not_biextEquiv_preserve (d₀ : Bool) :
    ¬ (preserve ≃ᵇ foreclose d₀) :=
  not_biextEquiv_of_agentInert_ne preserve_not_agentInert (foreclose_agentInert d₀)

theorem transfer_not_biextEquiv_preserve : ¬ (preserve ≃ᵇ transfer) :=
  not_biextEquiv_of_agentInert_ne preserve_not_agentInert transfer_agentInert

theorem foreclose_biextEquiv_pin (d₀ : Bool) : foreclose d₀ ≃ᵇ pin preserve d₀ :=
  Frame.biextEquiv_iff_homotopyEquiv.mpr
    ⟨{ agent := fun _ => PUnit.unit, env := fun e => e, adjoint := fun _ _ => rfl },
     { agent := fun _ => false, env := fun e => e, adjoint := fun _ _ => rfl },
     fun _ _ => rfl, fun _ _ => rfl⟩

/-- Foreclosure is commitment: the real `Commit^B`, at biextensional-equivalence
strength. -/
theorem foreclose_biextEquiv_commit (d₀ : Bool) :
    foreclose d₀ ≃ᵇ preserve.commit {d₀} :=
  (foreclose_biextEquiv_pin d₀).trans (pin_biextEquiv_commit preserve d₀)

/-- The real Claim 30: the restricted future frame is an additive subagent. -/
theorem commit_preserve_addSubagent (d₀ : Bool) : preserve.commit {d₀} ◁₊ preserve :=
  Frame.commit_addSubagent preserve {d₀}

def totalSetoid (α : Type) : Setoid α where
  r _ _ := True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

instance instSubsingletonTotalQuotient (α : Type) :
    Subsingleton (Quotient (totalSetoid α)) :=
  ⟨fun x y => Quotient.inductionOn₂ x y fun _ _ => Quotient.sound trivial⟩

def constSection {α : Type} (a : α) : Frame.partitionSections (totalSetoid α) :=
  ⟨fun _ => a, fun c => Subsingleton.elim _ c⟩

/-- Transfer is externalization: the real `External^{/B}` at the one-cell partition. -/
theorem transfer_biextEquiv_externalQuot :
    transfer ≃ᵇ preserve.externalQuot (totalSetoid preserve.Agent) := by
  refine Frame.biextEquiv_iff_homotopyEquiv.mpr
    ⟨{ agent := fun _ => Quotient.mk _ true
       env := fun p => (p.1.val (Quotient.mk _ true), p.2)
       adjoint := fun _ _ => rfl },
     { agent := fun _ => true
       env := fun p => (constSection p.1, p.2)
       adjoint := fun _ _ => rfl },
     fun _ _ => rfl, ?_⟩
  rintro c ⟨q, s⟩
  have hc : c = Quotient.mk (totalSetoid preserve.Agent) true :=
    Subsingleton.elim (α := Quotient (totalSetoid preserve.Agent)) c _
  exact congrArg (fun x => preserve.outcome (q.val x) s) hc

/-- The real Claim 34/45: the externalized future frame is a multiplicative subagent. -/
theorem externalQuot_preserve_multSubagent :
    preserve.externalQuot (totalSetoid preserve.Agent) ◁ₓ preserve :=
  Frame.externalQuot_multSubagent preserve (totalSetoid preserve.Agent)

/-! ## The image invariant separating the two -/

theorem preserve_image : preserve.image = Set.univ :=
  Set.eq_univ_of_forall fun w => ⟨w.executed, w.disturbance, rfl⟩

theorem foreclose_image (d₀ : Bool) :
    (foreclose d₀).image = {w : World | w.executed = d₀} := by
  refine Set.ext fun w => ⟨?_, fun hw => ⟨true, w.disturbance, World.ext hw.symm rfl⟩⟩
  rintro ⟨-, s, rfl⟩
  rfl

theorem foreclose_image_ne_preserve (d₀ : Bool) :
    (foreclose d₀).image ≠ preserve.image := by
  rw [foreclose_image, preserve_image]
  intro h
  have hmem : (⟨!d₀, false⟩ : World) ∈ {w : World | w.executed = d₀} := by
    rw [h]; trivial
  exact absurd hmem (by cases d₀ <;> decide)

/-- Nothing distinguishes "another process exercises the correction" from "the corrective
coordinate is exogenous": `transfer` is equivalent to a frame with a one-point agent. -/
theorem transfer_biextEquiv_exogenous :
    transfer ≃ᵇ { Agent := PUnit, Env := Bool × Bool, outcome := fun _ p => ⟨p.1, p.2⟩ } :=
  Frame.biextEquiv_iff_homotopyEquiv.mpr
    ⟨{ agent := fun _ => PUnit.unit, env := fun e => e, adjoint := fun _ _ => rfl },
     { agent := fun _ => true, env := fun e => e, adjoint := fun _ _ => rfl },
     fun _ _ => rfl, fun _ _ => rfl⟩

theorem transfer_image : transfer.image = preserve.image := by
  rw [preserve_image]
  exact Set.eq_univ_of_forall fun w => ⟨true, (w.executed, w.disturbance), rfl⟩

/-- Commitment and externalization are not interchangeable: the real `image` invariant of
biextensional equivalence separates them. -/
theorem foreclose_not_biextEquiv_transfer (d₀ : Bool) :
    ¬ (foreclose d₀ ≃ᵇ transfer) := by
  intro h
  refine foreclose_image_ne_preserve d₀ ?_
  rw [Frame.image_eq_of_biextEquiv h, transfer_image]

/-- The Decomposition Theorem applies to both arms: each is a subagent of the preserved
frame, hence factors as a multiplicative subagency followed by an additive one. -/
theorem foreclose_subagent (d₀ : Bool) : preserve.commit {d₀} ◁ preserve :=
  (Frame.commit_addSubagent preserve {d₀}).subagent

theorem transfer_subagent :
    preserve.externalQuot (totalSetoid preserve.Agent) ◁ preserve :=
  (Frame.externalQuot_multSubagent preserve (totalSetoid preserve.Agent)).subagent

/-! ## The two-stage statement -/

inductive PresentAction where
  | preserveCorrection
  | forecloseCorrection
  | transferCorrection
  deriving DecidableEq

abbrev presentStage : CartesianFrames.Frame World where
  Agent := PresentAction
  Env := Bool
  outcome := fun _ s => ⟨false, s⟩

def futureFrame : PresentAction → CartesianFrames.Frame World
  | .preserveCorrection => preserve
  | .forecloseCorrection => foreclose false
  | .transferCorrection => transfer

theorem presentStage_agentInert : AgentInert presentStage := fun _ _ _ => rfl

/-- Three present actions with an inert present frame induce pairwise non-equivalent
future corrective frames. -/
theorem futureFrame_separates :
    ¬ (futureFrame .preserveCorrection ≃ᵇ futureFrame .forecloseCorrection) ∧
      ¬ (futureFrame .preserveCorrection ≃ᵇ futureFrame .transferCorrection) ∧
      ¬ (futureFrame .forecloseCorrection ≃ᵇ futureFrame .transferCorrection) :=
  ⟨foreclose_not_biextEquiv_preserve false, transfer_not_biextEquiv_preserve,
    foreclose_not_biextEquiv_transfer false⟩

#print axioms AgentInert.of_biextEquiv
#print axioms not_biextEquiv_of_agentInert_ne
#print axioms pin_biextEquiv_commit
#print axioms pin_delegated_eq_pin_simulated
#print axioms delegated_not_agentInert
#print axioms delegated_not_biextEquiv_simulated
#print axioms commitment_view_blind
#print axioms labelledHuman_not_agentInert
#print axioms labelledAgent_not_agentInert
#print axioms labelledHuman_image
#print axioms labelledAgent_image
#print axioms labelledHuman_not_biextEquiv_labelledAgent
#print axioms mapWorlds_forgetLabel
#print axioms mapWorlds_delegated_not_biextEquiv_simulated
#print axioms simRead_id_eq_delegated
#print axioms simRead_const_eq_simulated
#print axioms simRead_not_biextEquiv_delegated
#print axioms transfer_biextEquiv_exogenous
#print axioms preserve_not_agentInert
#print axioms foreclose_not_biextEquiv_preserve
#print axioms transfer_not_biextEquiv_preserve
#print axioms foreclose_biextEquiv_pin
#print axioms foreclose_biextEquiv_commit
#print axioms commit_preserve_addSubagent
#print axioms transfer_biextEquiv_externalQuot
#print axioms externalQuot_preserve_multSubagent
#print axioms preserve_image
#print axioms foreclose_image
#print axioms foreclose_image_ne_preserve
#print axioms transfer_image
#print axioms foreclose_not_biextEquiv_transfer
#print axioms foreclose_subagent
#print axioms transfer_subagent
#print axioms presentStage_agentInert
#print axioms futureFrame_separates

end CFDeferenceCrossCheck
