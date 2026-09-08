/-
# Occurrence-local Integrity: the trace of one account

Round `projects/deference/rounds/2026-09-07-reason-mediated-authorship/`.

`AuthorityActivation.LegitimateForSegment` scopes Robust Openness to the concerns relevant
to one occurrence but still carries a global `Evolution`: every occurrence's account is
propagated through every step.  This module isolates the weakest Integrity object the
evaluation consumer needs — the **local trace** of one occurrence's own account — and
shows it is a projection of the global object.

* `Program.substOn` — substitution given replacements only at the live ports the account
  occupies; `substOn_eq_subst` — it agrees with `subst` when a total replacement is
  restricted.
* `LocalStep`, `LocalTrace` — one transition, and a chain of them, seen from one
  occurrence: a fresh event, the occurrence still exposed, and accounts for its own live
  ports.  Nothing is said about other occurrences.
* `Step.toLocal`, `Evolution.toLocalTrace` — **projection**: a global step or evolution
  restricts to a local step or trace of any occurrence exposed at the start, and the
  local trace's endpoint is the globally propagated account.
* `LocalLegit` — the occurrence-local legitimacy certificate: a local trace whose states
  are explicit snapshots, each robustly open for the declared scope.
  `LegitimateForSegment.toLocalLegit` projects the scoped-openness certificate to it.
* `Witness.unrelated_integrity_failure` — a trajectory on which occurrence `1` disappears
  (no global `Evolution` exists, by conservation of exposure) while occurrence `0`'s
  account propagates and its scope is open: the local certificate is inhabited.

**What this does not establish.**  That a record-keeper who dropped one occurrence should
be trusted about another: receipt authenticity is the protocol's `Authorized` /
`AnswerOK`, external to both the global and the local object.  The local object is the
weakest *propagation* certificate, not an evidentiary policy.  Names are provisional
(`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.AuthorityActivation

universe u v w

namespace Workspace.Normativity.Contrib.OccurrenceIntegrity.Program

variable {Occ : Type u} {Req : Type v} {S : Protocol.{u, v, w} Occ Req}
variable {A B : Boundary Occ Req}

/-- Substitution at exactly the live ports an account occupies. -/
def substOn (hab : A.history <+: B.history) :
    {r : Req} → (t : Program S A r) →
    ((p : Fin A.portCount) → p ∈ t.livePorts → Program S B (A.demand p)) → Program S B r
  | _, .live p hp _, repl => hp ▸ repl p (by simp [livePorts])
  | _, .answer a h, _ => .answer a (h.trans hab)
  | _, .close c h, _ => .close c (h.trans hab)
  | _, .combine law h children, repl =>
      .combine law (h.trans hab) fun i =>
        substOn hab (children i) fun p hp => repl p (by
          simp only [livePorts]
          exact Multiset.mem_sum.mpr ⟨i, Finset.mem_univ i, hp⟩)

/-- A total replacement, restricted, substitutes as `subst` does. -/
theorem substOn_eq_subst (hab : A.history <+: B.history) {r : Req} (t : Program S A r)
    (replacement : (p : Fin A.portCount) → Program S B (A.demand p)) :
    t.substOn hab (fun p _ => replacement p) = t.subst hab replacement := by
  induction t with
  | live p hp _ => rfl
  | answer => rfl
  | close => rfl
  | combine law h children ih =>
      simp only [substOn, subst]
      congr 1
      funext i
      exact ih i

end Workspace.Normativity.Contrib.OccurrenceIntegrity.Program

namespace Workspace.Normativity.Contrib.OccurrenceLocalIntegrity

open Workspace.Normativity.Contrib.OccurrenceIntegrity
open Workspace.Normativity.Contrib.LegitimateEvolution
open Workspace.Normativity.Contrib.AuthorityActivation

variable {Occ : Type u} {Req : Type v} {S : Protocol.{u, v, w} Occ Req}
variable {anchor : Occ → Req} (o : Occ)

/-! ## 1. Local steps and traces -/

/-- **One transition, seen from one occurrence**: a fresh event, the occurrence still
exposed, and an account at the target for each live port its own account occupies. -/
structure LocalStep (A B : Boundary Occ Req) (t : Program S A (anchor o)) where
  event : Nat
  fresh : event ∉ A.history
  append : B.history = A.history ++ [event]
  exposed : o ∈ B.exposed
  repl : (p : Fin A.portCount) → p ∈ t.livePorts → Program S B (A.demand p)

namespace LocalStep

variable {o} {A B : Boundary Occ Req} {t : Program S A (anchor o)}

theorem historyPrefix (ls : LocalStep (S := S) (anchor := anchor) o A B t) :
    A.history <+: B.history := by
  rw [ls.append]; exact List.prefix_append _ _

/-- The locally propagated account. -/
def propagate (ls : LocalStep (S := S) (anchor := anchor) o A B t) : Program S B (anchor o) :=
  t.substOn ls.historyPrefix ls.repl

end LocalStep

/-- **The local trace** of one occurrence's account: a chain of local steps, each target
account the local propagation of its source. -/
inductive LocalTrace :
    (A : Boundary Occ Req) → Program S A (anchor o) →
    (B : Boundary Occ Req) → Program S B (anchor o) → Type (max u v w)
  | refl (A) (t : Program S A (anchor o)) : LocalTrace A t A t
  | cons {A B C} {t : Program S A (anchor o)} {v : Program S C (anchor o)}
      (ls : LocalStep (S := S) (anchor := anchor) o A B t)
      (tail : LocalTrace B ls.propagate C v) : LocalTrace A t C v

namespace LocalTrace

variable {o}

/-- Recast the endpoint accounts along equalities. -/
def cast {A B : Boundary Occ Req} {t t' : Program S A (anchor o)} {u u' : Program S B (anchor o)}
    (ht : t = t') (hu : u = u') (tr : LocalTrace (S := S) (anchor := anchor) o A t B u) :
    LocalTrace (S := S) (anchor := anchor) o A t' B u' := by
  subst ht; subst hu; exact tr

end LocalTrace

/-! ## 2. Projection from the global objects -/

variable [DecidableEq Occ]

/-- A global step restricts to a local step of any occurrence exposed at its source. -/
def _root_.Workspace.Normativity.Contrib.OccurrenceIntegrity.Step.toLocal
    {A B : Boundary Occ Req} (step : Step S anchor A B) (ho : o ∈ A.exposed)
    (t : Program S A (anchor o)) : LocalStep (S := S) (anchor := anchor) o A B t where
  event := step.event
  fresh := step.fresh
  append := step.append
  exposed := step.exposures ho
  repl := fun p _ => step.replacement p

/-- The local propagation of the restricted step is the global propagation. -/
theorem Step.toLocal_propagate {A B : Boundary Occ Req} (step : Step S anchor A B)
    (ho : o ∈ A.exposed) (account : Accounted S anchor A) (hb : o ∈ B.exposed) :
    (step.toLocal o ho (account o ho)).propagate = Step.propagate S step account o hb := by
  unfold LocalStep.propagate Step.propagate
  simp only [dif_pos ho]
  exact Program.substOn_eq_subst _ _ _

/-- **Projection.**  A global evolution restricts to a local trace of any occurrence
exposed at its start, ending at the globally propagated account. -/
def _root_.Workspace.Normativity.Contrib.LegitimateEvolution.Evolution.toLocalTrace :
    {O₀ O₁ : ObligationState S anchor} → (ev : Evolution S anchor O₀ O₁) →
    (h₀ : o ∈ O₀.boundary.exposed) →
    LocalTrace (S := S) (anchor := anchor) o O₀.boundary (O₀.account o h₀) O₁.boundary
      (O₁.account o (ev.conservation.exposure h₀))
  | _, _, .refl O, h₀ => .refl O.boundary (O.account o h₀)
  | O₀, O₂, .cons (O₁ := O₁) step propagates tail, h₀ =>
      let h₁ : o ∈ O₁.boundary.exposed := step.exposures h₀
      .cons (step.toLocal o h₀ (O₀.account o h₀))
        ((tail.toLocalTrace h₁).cast (by
          rw [Step.toLocal_propagate (o := o) step h₀ O₀.account h₁, propagates]) rfl)

/-! ## 3. The occurrence-local legitimacy certificate -/

variable {Γ J R : Type}

/-- **Occurrence-local legitimacy**: explicit state snapshots, each robustly open for the
declared scope, with the occurrence's own account propagated locally between consecutive
snapshots.  Other occurrences' accounts are unconstrained. -/
inductive LocalLegit (scope : Finset Γ) (sem : OpennessSemantics S anchor Γ J R) :
    (O : ObligationState S anchor) → o ∈ O.boundary.exposed →
    (O' : ObligationState S anchor) → o ∈ O'.boundary.exposed → Type (max u v w)
  | refl (O) (h : o ∈ O.boundary.exposed) (open_ : OpenAtFor scope sem O) :
      LocalLegit scope sem O h O h
  | cons {O₁ O₂ O₃ : ObligationState S anchor} {h₁ : o ∈ O₁.boundary.exposed}
      {h₂ : o ∈ O₂.boundary.exposed} {h₃ : o ∈ O₃.boundary.exposed}
      (open_ : OpenAtFor scope sem O₁)
      (ls : LocalStep (S := S) (anchor := anchor) o O₁.boundary O₂.boundary (O₁.account o h₁))
      (hprop : ls.propagate = O₂.account o h₂)
      (tail : LocalLegit scope sem O₂ h₂ O₃ h₃) : LocalLegit scope sem O₁ h₁ O₃ h₃

/-- The recursive projection: an evolution open at every state for the scope gives a local
certificate for any occurrence exposed at its start. -/
def _root_.Workspace.Normativity.Contrib.LegitimateEvolution.Evolution.toLocalLegit
    {scope : Finset Γ} {sem : OpennessSemantics S anchor Γ J R} :
    {O₀ O₁ : ObligationState S anchor} → (ev : Evolution S anchor O₀ O₁) →
    ev.AllStates (OpenAtFor scope sem) → (h₀ : o ∈ O₀.boundary.exposed) →
    LocalLegit (S := S) (anchor := anchor) o scope sem O₀ h₀ O₁
      (ev.conservation.exposure h₀)
  | _, _, .refl O, openAll, h₀ => .refl O h₀ openAll
  | O₀, O₂, .cons (O₁ := O₁) step propagates tail, openAll, h₀ =>
      let h₁ : o ∈ O₁.boundary.exposed := step.exposures h₀
      .cons openAll.1 (step.toLocal o h₀ (O₀.account o h₀))
        (by rw [Step.toLocal_propagate (o := o) step h₀ O₀.account h₁, propagates])
        (tail.toLocalLegit openAll.2 h₁)

/-- **Projection of the scoped-openness certificate.** -/
def _root_.Workspace.Normativity.Contrib.AuthorityActivation.LegitimateForSegment.toLocalLegit
    {scope : Finset Γ} {sem : OpennessSemantics S anchor Γ J R}
    {O₀ O₁ : ObligationState S anchor}
    (leg : LegitimateForSegment scope sem O₀ O₁) (h₀ : o ∈ O₀.boundary.exposed) :
    LocalLegit (S := S) (anchor := anchor) o scope sem O₀ h₀ O₁
      (leg.evolution.conservation.exposure h₀) :=
  leg.evolution.toLocalLegit o leg.openAll h₀

/-! ## 4. Witness: an unrelated Integrity failure -/

namespace Witness

open Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness
open Workspace.Normativity.Contrib.LegitimateEvolution.Witness
open Workspace.Normativity.Contrib.AuthorityActivation.Witness (semTwo)

/-- The boundary after occurrence `1` has vanished from the record: one port, only
occurrence `0` exposed. -/
def dropped : Boundary (Fin 2) Unit := ⟨[0, 1], {0}, 1, fun _ => ()⟩

/-- Occurrence `0` is live on the remaining port; nothing else is exposed. -/
def droppedState : ObligationState protocol wAnchor :=
  ⟨dropped, fun _ _ => Program.live ⟨0, by decide⟩ rfl trivial⟩

/-- **No global evolution reaches the dropped state**: exposure only grows. -/
theorem no_evolution : IsEmpty (Evolution protocol wAnchor state₀ droppedState) := by
  constructor
  intro ev
  have h := ev.conservation.exposure (Finset.mem_univ (1 : Fin 2))
  simp [droppedState, dropped] at h

/-- The local step carrying occurrence `0`'s port. -/
def localStep : LocalStep (S := protocol) (anchor := wAnchor) 0 state₀.boundary dropped
    (state₀.account 0 (Finset.mem_univ _)) where
  event := 1
  fresh := by decide
  append := rfl
  exposed := by simp [dropped]
  repl := fun _ _ => Program.live ⟨0, by decide⟩ rfl trivial

theorem open_start : OpenAtFor {0} semTwo state₀ := by decide

theorem open_dropped : OpenAtFor {0} semTwo droppedState := by decide

/-- **The local certificate is inhabited**: occurrence `0`'s account propagates, and the
scope is open at both snapshots. -/
def localLegit : LocalLegit (S := protocol) (anchor := wAnchor) 0 {0} semTwo
    state₀ (Finset.mem_univ _) droppedState (by simp [droppedState, dropped]) :=
  .cons open_start localStep rfl (.refl _ _ open_dropped)

theorem unrelated_integrity_failure :
    IsEmpty (Evolution protocol wAnchor state₀ droppedState) ∧
    Nonempty (LocalLegit (S := protocol) (anchor := wAnchor) 0 {0} semTwo
      state₀ (Finset.mem_univ _) droppedState (by simp [droppedState, dropped])) :=
  ⟨no_evolution, ⟨localLegit⟩⟩

end Witness

end Workspace.Normativity.Contrib.OccurrenceLocalIntegrity

#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.substOn_eq_subst
#print axioms Workspace.Normativity.Contrib.OccurrenceLocalIntegrity.Step.toLocal_propagate
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.Evolution.toLocalTrace
#print axioms Workspace.Normativity.Contrib.AuthorityActivation.LegitimateForSegment.toLocalLegit
#print axioms Workspace.Normativity.Contrib.OccurrenceLocalIntegrity.Witness.no_evolution
#print axioms Workspace.Normativity.Contrib.OccurrenceLocalIntegrity.Witness.localLegit
#print axioms Workspace.Normativity.Contrib.OccurrenceLocalIntegrity.Witness.unrelated_integrity_failure
