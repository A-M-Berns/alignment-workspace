/-
# Accounted obligation states, Integrity evolution, and Legitimate Evolution

Round `projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/`.

**The state.**  The qualitative obligation state a consumer reads is
`ObligationState S anchor = (boundary, account)`: the docket and exposure at a prefix
together with the authenticated current account of every exposed occurrence.  The
account is state, not a certificate: it is the status and lineage the export `O_P`
must carry, and two states on one boundary with different accounts are different
states.  `Initial.state` is one way to build a first state; nothing else needs it.

**The relation.**  `Evolution O₀ O₁` is a chain of transitions in which every
intermediate state is explicit and every target account is *the propagation* of its
source account through the transition.  The target account is therefore a function of
the source account and the certificate; there is no freedom to choose it.
`Evolution.trans` composes at a literally shared state.  `Evolution.conservation` is
Answerability Conservation: exposure only grows, every recorded receipt persists,
and the resolution witness each account denotes is transported from the earlier state.

**Openness over time.**  An `OpennessSemantics` gives, for each accounted state and
concern, the actual and counterfactual coverage states — external data, indexed by the
state so that the docket, the ports and the accounts (which carrier holds which
occurrence's load) are available to it.  `LegitimateSegment` requires
`RobustOpenActual` for every concern at *every* state of the evolution.
Because coverage and standing are conditional on liveness and applicability, this is
already the concern-relative form: nothing is demanded of a concern while it is
inapplicable or represented.  `Witness.endpoint_only_insufficient` is the exact
trajectory that endpoint-only openness accepts and this rejects: open, then a live
concern with no route, then restored.

**What this does not establish.**  That any `OpennessSemantics` is causally correct,
that any `Protocol` is authenticated, or that the concerns `Γ` are related to the
docket in any particular way; the last is what the semantics' dependence on the state
is for, and the generic theory does not fix it.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.OccurrenceIntegrity
import Workspace.Normativity.Contrib.NonCaptureCertificate

namespace Workspace.Normativity.Contrib.LegitimateEvolution

open Workspace.Normativity.Contrib.OccurrenceIntegrity
open Workspace.Normativity.Contrib.NonCapture

universe u v w

variable {Occ : Type u} {Req : Type v} (S : Protocol.{u, v, w} Occ Req) (anchor : Occ → Req)

/-! ## 1. The accounted state -/

/-- The qualitative obligation state at a prefix: the boundary and the current account
of every exposed occurrence.  This is `O_P`. -/
structure ObligationState where
  boundary : Boundary Occ Req
  account : Accounted S anchor boundary

/-- A first state, from authenticated initial exposure. -/
def _root_.Workspace.Normativity.Contrib.OccurrenceIntegrity.Initial.state
    {B : Boundary Occ Req} (initial : Initial S anchor B) : ObligationState S anchor :=
  ⟨B, initial.accounted⟩

variable [DecidableEq Occ]

/-! ## 2. Integrity evolution -/

/-- **Integrity evolution.**  Each transition's target account is the propagation of
its source account; every intermediate state is explicit. -/
inductive Evolution : ObligationState S anchor → ObligationState S anchor →
    Type (max u v w)
  | refl (O : ObligationState S anchor) : Evolution O O
  | cons {O₀ O₁ O₂ : ObligationState S anchor}
      (step : Step S anchor O₀.boundary O₁.boundary)
      (propagates : Step.propagate S step O₀.account = O₁.account)
      (tail : Evolution O₁ O₂) : Evolution O₀ O₂

namespace Evolution

variable {S anchor}

/-- Composition at a shared state. -/
def trans {O₀ O₁ O₂ : ObligationState S anchor} (left : Evolution S anchor O₀ O₁)
    (right : Evolution S anchor O₁ O₂) : Evolution S anchor O₀ O₂ :=
  match left with
  | .refl _ => right
  | .cons step propagates tail => .cons step propagates (tail.trans right)

/-- The underlying Integrity certificate. -/
def toSegment {O₀ O₁ : ObligationState S anchor} :
    Evolution S anchor O₀ O₁ → Segment S anchor O₀.boundary O₁.boundary
  | .refl O => .refl O.boundary
  | .cons step _ tail => .cons step tail.toSegment

/-- The target account is the propagation of the source account along the segment. -/
theorem propagate_toSegment {O₀ O₁ : ObligationState S anchor}
    (ev : Evolution S anchor O₀ O₁) :
    ev.toSegment.propagate O₀.account = O₁.account := by
  induction ev with
  | refl O => rfl
  | cons step propagates tail ih =>
      simp only [toSegment, Segment.propagate]
      rw [propagates]
      exact ih

/-- A segment and a source account determine an evolution to the propagated state. -/
def ofSegment {A B : Boundary Occ Req} (segment : Segment S anchor A B)
    (account : Accounted S anchor A) :
    Evolution S anchor ⟨A, account⟩ ⟨B, segment.propagate account⟩ :=
  match segment with
  | .refl _ => .refl _
  | .cons step tail => .cons step rfl (ofSegment tail _)

/-- A predicate holding at every state of the evolution, endpoints included. -/
def AllStates (P : ObligationState S anchor → Prop) :
    {O₀ O₁ : ObligationState S anchor} → Evolution S anchor O₀ O₁ → Prop
  | _, _, .refl O => P O
  | O₀, _, .cons _ _ tail => P O₀ ∧ tail.AllStates P

theorem AllStates.head {P : ObligationState S anchor → Prop}
    {O₀ O₁ : ObligationState S anchor} {ev : Evolution S anchor O₀ O₁}
    (h : ev.AllStates P) : P O₀ := by
  cases ev with
  | refl => exact h
  | cons => exact h.1

theorem AllStates.last {P : ObligationState S anchor → Prop}
    {O₀ O₁ : ObligationState S anchor} {ev : Evolution S anchor O₀ O₁}
    (h : ev.AllStates P) : P O₁ := by
  induction ev with
  | refl => exact h
  | cons _ _ _ ih => exact ih h.2

/-- A state predicate over a composite holds exactly when it holds over both parts. -/
theorem AllStates.trans {P : ObligationState S anchor → Prop}
    {O₀ O₁ O₂ : ObligationState S anchor}
    {left : Evolution S anchor O₀ O₁} {right : Evolution S anchor O₁ O₂}
    (hl : left.AllStates P) (hr : right.AllStates P) :
    (left.trans right).AllStates P := by
  induction left with
  | refl => exact hr
  | cons _ _ _ ih => exact ⟨hl.1, ih hl.2 hr⟩

end Evolution

/-! ## 3. Answerability Conservation -/

/-- **Answerability Conservation** between two accounted states: no occurrence
disappears, every recorded receipt persists, and the resolution witness denoted by each
occurrence's later account is its earlier account's witness under a transport of live
resolutions.  Anchoring is by type: both accounts are `Program _ _ (anchor o)`. -/
structure Conservation (O₀ O₁ : ObligationState S anchor) : Prop where
  exposure : O₀.boundary.exposed ⊆ O₁.boundary.exposed
  receipts : ∀ o (h₀ : o ∈ O₀.boundary.exposed),
    (O₀.account o h₀).terminals ≤ (O₁.account o (exposure h₀)).terminals
  faithful : ∃ transport :
      ((p : Fin O₁.boundary.portCount) → S.Resolution (O₁.boundary.demand p)) →
      ((p : Fin O₀.boundary.portCount) → S.Resolution (O₀.boundary.demand p)),
    ∀ o (h₀ : o ∈ O₀.boundary.exposed) v,
      (O₁.account o (exposure h₀)).evaluate v = (O₀.account o h₀).evaluate (transport v)

namespace Conservation

variable {S anchor}

omit [DecidableEq Occ] in
theorem refl (O : ObligationState S anchor) : Conservation S anchor O O :=
  ⟨fun _ h => h, fun _ _ => le_rfl, ⟨id, fun _ _ _ => rfl⟩⟩

omit [DecidableEq Occ] in
theorem trans {O₀ O₁ O₂ : ObligationState S anchor} (h₁ : Conservation S anchor O₀ O₁)
    (h₂ : Conservation S anchor O₁ O₂) : Conservation S anchor O₀ O₂ where
  exposure := fun _ h => h₂.exposure (h₁.exposure h)
  receipts := fun o h₀ => (h₁.receipts o h₀).trans (h₂.receipts o (h₁.exposure h₀))
  faithful := by
    obtain ⟨t₁, ht₁⟩ := h₁.faithful
    obtain ⟨t₂, ht₂⟩ := h₂.faithful
    exact ⟨fun v => t₁ (t₂ v), fun o h₀ v => by rw [ht₂ o (h₁.exposure h₀) v, ht₁]⟩

/-- One transition conserves. -/
theorem ofStep {O₀ O₁ : ObligationState S anchor}
    (step : Step S anchor O₀.boundary O₁.boundary)
    (propagates : Step.propagate S step O₀.account = O₁.account) :
    Conservation S anchor O₀ O₁ where
  exposure := step.exposures
  receipts := fun o h₀ => by
    rw [← propagates]
    simp only [Step.propagate, dif_pos h₀]
    exact Program.terminals_le_subst _ _ _
  faithful := by
    refine ⟨fun v p => (step.replacement p).evaluate v, fun o h₀ v => ?_⟩
    rw [← propagates]
    simp only [Step.propagate, dif_pos h₀]
    exact Program.evaluate_subst _ _ _ _

end Conservation

/-- **Integrity evolution conserves answerability.** -/
theorem Evolution.conservation {O₀ O₁ : ObligationState S anchor}
    (ev : Evolution S anchor O₀ O₁) : Conservation S anchor O₀ O₁ := by
  induction ev with
  | refl O => exact Conservation.refl O
  | cons step propagates _ ih => exact (Conservation.ofStep step propagates).trans ih

/-! ## 4. Openness over time and Legitimate Evolution -/

/-- An intervention semantics: for every accounted state and declared concern, the
actual and counterfactual coverage states.  External.  It sees the whole state — the
history prefix, the docket and the accounts — so the carrier of a concern's load can
be read off the accounts rather than reconstructed from the history. -/
def OpennessSemantics (Γ J R : Type) := ObligationState S anchor → Γ → Scenario J R

variable {Γ J R : Type}

variable {S anchor} in
/-- Robust Openness for every concern at one state, actual branch included. -/
def OpenAt (sem : OpennessSemantics S anchor Γ J R) (O : ObligationState S anchor) : Prop :=
  ∀ c, (sem O c).RobustOpenActual

variable {S anchor} in
instance [Fintype Γ] [Fintype J] [Fintype R] (sem : OpennessSemantics S anchor Γ J R)
    (O : ObligationState S anchor) : Decidable (OpenAt sem O) := by
  unfold OpenAt; infer_instance

/-- **Legitimate Evolution**, as a certificate: an Integrity evolution every state of
which is robustly open.  Proof-relevant; `Legitimate` below hides it. -/
structure LegitimateSegment (sem : OpennessSemantics S anchor Γ J R)
    (O₀ O₁ : ObligationState S anchor) where
  evolution : Evolution S anchor O₀ O₁
  openAll : evolution.AllStates (OpenAt sem)

namespace LegitimateSegment

variable {S anchor} {sem : OpennessSemantics S anchor Γ J R}

def refl (O : ObligationState S anchor) (h : OpenAt sem O) :
    LegitimateSegment S anchor sem O O :=
  ⟨.refl O, h⟩

/-- Composition at a shared state. -/
def trans {O₀ O₁ O₂ : ObligationState S anchor}
    (left : LegitimateSegment S anchor sem O₀ O₁)
    (right : LegitimateSegment S anchor sem O₁ O₂) :
    LegitimateSegment S anchor sem O₀ O₂ :=
  ⟨left.evolution.trans right.evolution, left.openAll.trans right.openAll⟩

/-- **Diachronic Answerability to the protected party**, decomposed: content and
receipts are conserved by Integrity, and coverage and standing hold at both endpoints
(and, by `openAll`, at every state between). -/
theorem answerable {O₀ O₁ : ObligationState S anchor}
    (leg : LegitimateSegment S anchor sem O₀ O₁) :
    Conservation S anchor O₀ O₁ ∧ OpenAt sem O₀ ∧ OpenAt sem O₁ :=
  ⟨leg.evolution.conservation, leg.openAll.head, leg.openAll.last⟩

end LegitimateSegment

/-- The endpoint relation a consumer may use; the witness stays available for audit. -/
def Legitimate (sem : OpennessSemantics S anchor Γ J R) (O₀ O₁ : ObligationState S anchor) :
    Prop :=
  Nonempty (LegitimateSegment S anchor sem O₀ O₁)

theorem Legitimate.trans {sem : OpennessSemantics S anchor Γ J R}
    {O₀ O₁ O₂ : ObligationState S anchor} (h₁ : Legitimate S anchor sem O₀ O₁)
    (h₂ : Legitimate S anchor sem O₁ O₂) : Legitimate S anchor sem O₀ O₂ :=
  h₁.elim fun l => h₂.elim fun r => ⟨l.trans r⟩

/-! ## 5. Witnesses

Two transitions on the Integrity witness: the first answers one of two equal-anchor
occurrences and carries the other; the second carries again.  Under a semantics that is
open at every prefix the two legitimate segments compose, and the composite's accounts
are `answered` and `live`.  Under a semantics closed only at the middle prefix, both
endpoints are open and the evolution is not legitimate. -/

namespace Witness

open Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness
open Workspace.Normativity.Contrib.NonCapture.Witness (st)

/-- The witness anchoring: every occurrence is anchored at `()`. -/
abbrev wAnchor : Fin 2 → Unit := Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness.anchor

/-- The docket after the second carry. -/
def final : Boundary (Fin 2) Unit := ⟨[0, 1, 2], Finset.univ, 1, fun _ => ()⟩

/-- Carry the one live port. -/
def step₂ : Step protocol wAnchor finish final where
  event := 2
  fresh := by decide
  append := rfl
  exposures := fun _ h => h
  replacement := fun _ => Program.live ⟨0, by decide⟩ rfl trivial
  admitted := fun _ _ h => absurd (Finset.mem_univ _) h
  newPort := fun _ _ h => absurd (Finset.mem_univ _) h
  newAnchor := fun _ _ h => absurd (Finset.mem_univ _) h
  newCredential := fun _ _ h => absurd (Finset.mem_univ _) h

def state₀ : ObligationState protocol wAnchor := initial.state
def state₁ : ObligationState protocol wAnchor := ⟨finish, Step.propagate protocol step state₀.account⟩
def state₂ : ObligationState protocol wAnchor := ⟨final, Step.propagate protocol step₂ state₁.account⟩

def ev₀₁ : Evolution protocol wAnchor state₀ state₁ := .cons (O₁ := state₁) step rfl (.refl _)
def ev₁₂ : Evolution protocol wAnchor state₁ state₂ := .cons (O₁ := state₂) step₂ rfl (.refl _)

/-- One concern, one route: fully open. -/
def openS : Scenario (Fin 1) (Fin 1) :=
  ⟨st true false false true true true true, ![st true false false true true true true]⟩

/-- The concern is live and the actual prefix has no adequate route. -/
def closedS : Scenario (Fin 1) (Fin 1) :=
  ⟨st true false false false false false true, ![st true false false true true true true]⟩

/-- Open everywhere. -/
def semOpen : OpennessSemantics protocol wAnchor Unit (Fin 1) (Fin 1) := fun _ _ => openS

/-- Open except at the middle state, whose history is `[0, 1]`. -/
def semMiddle : OpennessSemantics protocol wAnchor Unit (Fin 1) (Fin 1) :=
  fun O _ => if O.boundary.history = [0, 1] then closedS else openS

def leg₀₁ : LegitimateSegment protocol wAnchor semOpen state₀ state₁ :=
  ⟨ev₀₁, show OpenAt semOpen state₀ ∧ OpenAt semOpen state₁
    by decide⟩

def leg₁₂ : LegitimateSegment protocol wAnchor semOpen state₁ state₂ :=
  ⟨ev₁₂, show OpenAt semOpen state₁ ∧ OpenAt semOpen state₂
    by decide⟩

/-- **Legitimate segments compose nonvacuously**: the composite is legitimate and its
accounts keep the two equal-anchor occurrences apart. -/
theorem composed :
    (leg₀₁.trans leg₁₂).evolution.AllStates (OpenAt semOpen) ∧
    (state₂.account 0 (Finset.mem_univ _)).fates = {Fate.answered} ∧
    (state₂.account 1 (Finset.mem_univ _)).fates = {Fate.live} := by
  refine ⟨(leg₀₁.trans leg₁₂).openAll, ?_, ?_⟩ <;>
  simp [state₂, state₁, state₀, Initial.state, Step.propagate, Initial.accounted, initial,
    step, step₂, start, finish, Program.subst, Program.fates]

/-- **Endpoint-only openness is insufficient.**  Both endpoints of `ev₀₁.trans ev₁₂` are
open under `semMiddle`, the middle state is not, and the evolution is not legitimate. -/
theorem endpoint_only_insufficient :
    OpenAt semMiddle state₀ ∧ OpenAt semMiddle state₂ ∧
    ¬ OpenAt semMiddle state₁ ∧
    ¬ (ev₀₁.trans ev₁₂).AllStates (OpenAt semMiddle) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro h
  have h' : OpenAt semMiddle state₀ ∧
      OpenAt semMiddle state₁ ∧
      OpenAt semMiddle state₂ := h
  exact (by decide : ¬ OpenAt semMiddle state₁) h'.2.1

end Witness

end Workspace.Normativity.Contrib.LegitimateEvolution

#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.Evolution.propagate_toSegment
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.Evolution.ofSegment
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.Evolution.AllStates.trans
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.Conservation.trans
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.Conservation.ofStep
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.Evolution.conservation
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.LegitimateSegment.trans
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.LegitimateSegment.answerable
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.Legitimate.trans
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.Witness.composed
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.Witness.endpoint_only_insufficient
