/-
# Authority activation: reading the activation event off an occurrence's account

Round `projects/deference/rounds/2026-09-07-authority-activated-value/`.

The activation event `C` of an anchored evaluation occurrence is a predicate on the
occurrence's **propagated account** in the existing Integrity calculus: the account is
activated iff its fate multiset is exactly one `answered` leaf.  Nothing new is added to
the protocol — the three fates already separate `answered` from `closed` and `live`, the
answer receipt already pins the event whose payload is the value vector, and propagation
is already pointwise in the occurrence.

* `activated` — the predicate, decidable, on `Program`.
* `answer_activated`, `close_not_activated`, `live_not_activated`,
  `not_activated_of_live_mem`, `not_activated_of_closed_mem` — the three fates read as
  intended; a `combine` chain (carry, re-representation, rescheduling) is transparent
  (`combine_zero_fates`).
* `fates_subst_of_terminal` / `activated_subst_of_terminal` — **the first answer binds**:
  an account with no live port is not changed by any further step, so a second receipt
  cannot enter and activation is stable.
* `Step.propagate_congr`, `Segment.propagate_congr` — **propagation is occurrence-local**:
  the propagated account of `o` depends only on `o`'s own source account and the
  certificate, not on any other occurrence's account.
* `OpenAtFor`, `LegitimateForSegment`, `LegitimateSegment.project` — **occurrence-local
  legitimacy** is a projection of the existing certificate onto a declared concern set:
  the same evolution, openness required only for the concerns in scope.
* `Witness.unrelated_failure` — an exact trajectory that is legitimate for the concern in
  scope and not globally legitimate, because an unrelated concern is routeless at the
  middle state.
* `Witness.closed_not_activated` — a closure receipt discharging the same occurrence does
  not activate.
* `Neutral.certifiable_iff` — a certificate that factors as a payload-blind process part
  and a total binding relation certifies every payload or none.

**What this does not establish.**  That the payload read off the answer event is what the
principal committed to (semantic authentication of the history), that any process
certificate means what it says, or that any account is ever answered.  Names are
provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.LegitimateEvolution
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

universe u v w

/-! ## 1. The activation predicate -/

namespace Workspace.Normativity.Contrib.OccurrenceIntegrity.Program

variable {Occ : Type u} {Req : Type v} {S : Protocol.{u, v, w} Occ Req}
variable {B : Boundary Occ Req} {r : Req}

/-- **Activation.**  The account is a single authenticated answer: its fates are exactly
`{answered}`.  `closed` and `live` leaves, and any second leaf, deactivate. -/
def activated (t : Program S B r) : Bool := decide (t.fates = {Fate.answered})

theorem answer_activated (receipt : AnswerReceipt S r)
    (h : receipt.atHistory ++ [receipt.event] <+: B.history) :
    (Program.answer (B := B) receipt h).activated = true := by
  simp [activated, fates]

theorem close_not_activated (receipt : ClosureReceipt S r)
    (h : receipt.atHistory ++ [receipt.event] <+: B.history) :
    (Program.close (B := B) receipt h).activated = false := by
  simp [activated, fates]

theorem live_not_activated (p : Fin B.portCount) (hp : B.demand p = r)
    (cred : S.Live B.history p.val (B.demand p)) :
    (Program.live (S := S) p hp cred).activated = false := by
  simp [activated, fates]

/-- Any account with a live leaf is not activated. -/
theorem not_activated_of_live_mem (t : Program S B r) (h : Fate.live ∈ t.fates) :
    t.activated = false := by
  simp only [activated, decide_eq_false_iff_not]
  intro heq
  rw [heq] at h
  simp at h

/-- Any account with a closed leaf is not activated. -/
theorem not_activated_of_closed_mem (t : Program S B r) (h : Fate.closed ∈ t.fates) :
    t.activated = false := by
  simp only [activated, decide_eq_false_iff_not]
  intro heq
  rw [heq] at h
  simp at h

/-- A unary local law (carry, re-representation, rescheduling) is transparent to the
fates. -/
theorem combine_zero_fates (law : LocalLaw S r) (hl : law.arity = 0)
    (h : law.atHistory ++ [law.event] <+: B.history)
    (children : (i : Fin (law.arity + 1)) → Program S B (law.child i)) :
    (Program.combine law h children).fates = (children ⟨0, Nat.zero_lt_succ _⟩).fates := by
  simp only [fates]
  have : ∀ (n : ℕ) (hn : n = 0) (f : Fin (n + 1) → Multiset Fate),
      ∑ i, f i = f ⟨0, Nat.zero_lt_succ _⟩ := by
    intro n hn f
    subst hn
    simp [Fin.sum_univ_succ]
  exact this law.arity hl _

/-! ## 2. The first answer binds: terminal accounts are frozen -/

variable {A : Boundary Occ Req}

/-- An account with no live port is unchanged, as a fate multiset, by any substitution. -/
theorem fates_subst_of_terminal (hab : A.history <+: B.history)
    (replacement : (p : Fin A.portCount) → Program S B (A.demand p))
    (t : Program S A r) (ht : t.livePorts = 0) :
    (t.subst hab replacement).fates = t.fates := by
  induction t with
  | live p hp _ =>
      exfalso
      simp [livePorts] at ht
  | answer receipt historical => simp [subst, fates]
  | close receipt historical => simp [subst, fates]
  | combine law historical children ih =>
      simp only [subst, fates]
      refine Finset.sum_congr rfl fun i _ => ih i ?_
      simp only [livePorts] at ht
      exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Multiset.zero_le _).mp ht i
        (Finset.mem_univ _)

/-- **The first answer binds.**  Activation of a terminal account is stable under every
further step: no second receipt can enter. -/
theorem activated_subst_of_terminal (hab : A.history <+: B.history)
    (replacement : (p : Fin A.portCount) → Program S B (A.demand p))
    (t : Program S A r) (ht : t.livePorts = 0) :
    (t.subst hab replacement).activated = t.activated := by
  simp only [activated, fates_subst_of_terminal hab replacement t ht]

/-- An activated account has no live port. -/
theorem livePorts_eq_zero_of_activated (t : Program S B r) (h : t.activated = true) :
    t.livePorts = 0 := by
  by_contra hne
  obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hne
  have hlive : Fate.live ∈ t.fates := by
    clear h hne
    induction t with
    | live q hq _ =>
        simp [fates]
    | answer => simp [livePorts] at hp
    | close => simp [livePorts] at hp
    | combine law historical children ih =>
        simp only [livePorts] at hp
        obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp hp
        simp only [fates]
        exact Multiset.mem_sum.mpr ⟨i, Finset.mem_univ _, ih i hi⟩
  rw [not_activated_of_live_mem t hlive] at h
  exact Bool.false_ne_true h

/-- **Activation persists along every step.** -/
theorem activated_subst (hab : A.history <+: B.history)
    (replacement : (p : Fin A.portCount) → Program S B (A.demand p))
    (t : Program S A r) (h : t.activated = true) :
    (t.subst hab replacement).activated = true := by
  rw [activated_subst_of_terminal hab replacement t (livePorts_eq_zero_of_activated t h)]
  exact h

end Workspace.Normativity.Contrib.OccurrenceIntegrity.Program

namespace Workspace.Normativity.Contrib.AuthorityActivation

open Workspace.Normativity.Contrib.OccurrenceIntegrity
open Workspace.Normativity.Contrib.LegitimateEvolution
open Workspace.Normativity.Contrib.NonCapture

variable {Occ : Type u} {Req : Type v} {S : Protocol.{u, v, w} Occ Req}

/-! ## 3. Propagation is occurrence-local -/

variable {anchor : Occ → Req} [DecidableEq Occ]

/-- One step's propagated account of `o` depends only on `o`'s source account. -/
theorem Step.propagate_congr {A B : Boundary Occ Req} (step : Step S anchor A B)
    (account account' : Accounted S anchor A) (o : Occ)
    (h : ∀ ho, account o ho = account' o ho) (hb : o ∈ B.exposed) :
    Step.propagate S step account o hb = Step.propagate S step account' o hb := by
  simp only [Step.propagate]
  split_ifs with hold
  · rw [h hold]
  · rfl

/-- A segment's propagated account of `o` depends only on `o`'s source account. -/
theorem Segment.propagate_congr {A B : Boundary Occ Req} (segment : Segment S anchor A B)
    (account account' : Accounted S anchor A) (o : Occ)
    (h : ∀ ho, account o ho = account' o ho) :
    ∀ hb, segment.propagate account o hb = segment.propagate account' o hb := by
  induction segment with
  | refl => exact h
  | cons step tail ih =>
      intro hb
      exact ih _ _ (fun hm => Step.propagate_congr step account account' o h hm) hb

/-! ## 4. Occurrence-local legitimacy as a projection -/

variable {Γ J R : Type}

/-- Robust Openness at a state for the concerns in a declared scope only. -/
def OpenAtFor (scope : Finset Γ) (sem : OpennessSemantics S anchor Γ J R)
    (O : ObligationState S anchor) : Prop :=
  ∀ c ∈ scope, (sem O c).RobustOpenActual

instance [Fintype J] [Fintype R] (scope : Finset Γ) (sem : OpennessSemantics S anchor Γ J R)
    (O : ObligationState S anchor) : Decidable (OpenAtFor scope sem O) := by
  unfold OpenAtFor; infer_instance

omit [DecidableEq Occ] in
/-- Global openness projects to any scope. -/
theorem OpenAtFor.of_openAt (scope : Finset Γ) {sem : OpennessSemantics S anchor Γ J R}
    {O : ObligationState S anchor} (h : OpenAt sem O) : OpenAtFor scope sem O :=
  fun c _ => h c

/-- **Occurrence-local legitimacy**: the same Integrity evolution, open at every state for
the concerns in `scope`.  For an evaluation occurrence, `scope` is the concern set the
application declares relevant to it. -/
structure LegitimateForSegment (scope : Finset Γ) (sem : OpennessSemantics S anchor Γ J R)
    (O₀ O₁ : ObligationState S anchor) where
  evolution : Evolution S anchor O₀ O₁
  openAll : evolution.AllStates (OpenAtFor scope sem)

/-- A state predicate implied pointwise by another is implied along an evolution. -/
theorem Evolution.AllStates.mono {P P' : ObligationState S anchor → Prop}
    (hPP : ∀ O, P O → P' O) {O₀ O₁ : ObligationState S anchor}
    {ev : Evolution S anchor O₀ O₁} (h : ev.AllStates P) : ev.AllStates P' := by
  induction ev with
  | refl O => exact hPP O h
  | cons _ _ _ ih => exact ⟨hPP _ h.1, ih h.2⟩

/-- **Projection.**  A globally legitimate segment is legitimate for every scope, with the
same evolution. -/
def LegitimateSegment.project (scope : Finset Γ) {sem : OpennessSemantics S anchor Γ J R}
    {O₀ O₁ : ObligationState S anchor} (leg : LegitimateSegment S anchor sem O₀ O₁) :
    LegitimateForSegment scope sem O₀ O₁ :=
  ⟨leg.evolution, Evolution.AllStates.mono (fun _ => OpenAtFor.of_openAt scope) leg.openAll⟩

theorem LegitimateSegment.project_evolution (scope : Finset Γ)
    {sem : OpennessSemantics S anchor Γ J R} {O₀ O₁ : ObligationState S anchor}
    (leg : LegitimateSegment S anchor sem O₀ O₁) :
    (LegitimateSegment.project scope leg).evolution = leg.evolution := rfl

/-- Local certificates compose at a shared state, like global ones. -/
def LegitimateForSegment.trans {scope : Finset Γ} {sem : OpennessSemantics S anchor Γ J R}
    {O₀ O₁ O₂ : ObligationState S anchor}
    (left : LegitimateForSegment scope sem O₀ O₁)
    (right : LegitimateForSegment scope sem O₁ O₂) :
    LegitimateForSegment scope sem O₀ O₂ :=
  ⟨left.evolution.trans right.evolution, left.openAll.trans right.openAll⟩

/-- A local certificate carries the conservation theorem unchanged. -/
theorem LegitimateForSegment.conservation {scope : Finset Γ}
    {sem : OpennessSemantics S anchor Γ J R} {O₀ O₁ : ObligationState S anchor}
    (leg : LegitimateForSegment scope sem O₀ O₁) : Conservation S anchor O₀ O₁ :=
  leg.evolution.conservation

/-- **The activation read at the end of a local certificate is determined by the
occurrence's own account at the start and the certificate's segment.** -/
theorem LegitimateForSegment.activation_local {scope : Finset Γ}
    {sem : OpennessSemantics S anchor Γ J R} {O₀ O₁ : ObligationState S anchor}
    (leg : LegitimateForSegment scope sem O₀ O₁) (o : Occ) (h₁ : o ∈ O₁.boundary.exposed)
    (account' : Accounted S anchor O₀.boundary)
    (h : ∀ h₀, O₀.account o h₀ = account' o h₀) :
    (O₁.account o h₁).activated
      = (leg.evolution.toSegment.propagate account' o h₁).activated := by
  rw [← leg.evolution.propagate_toSegment]
  rw [Segment.propagate_congr leg.evolution.toSegment O₀.account account' o h]

/-! ## 5. Payload-blind certification -/

/-- An evaluation certificate factored into a process part (blind to the payload) and a
binding part (a commitment relation between binding data and the payload). -/
structure Neutral (Proc Key Payload : Type*) where
  ProcessCert : Proc → Prop
  Bind : Key → Payload → Prop
  /-- The principal can commit to any payload. -/
  total : ∀ V, ∃ κ, Bind κ V

namespace Neutral

variable {Proc Key Payload : Type*} (N : Neutral Proc Key Payload)

/-- The certificate: process part and binding part. -/
def Cert (ρ : Proc × Key) (V : Payload) : Prop := N.ProcessCert ρ.1 ∧ N.Bind ρ.2 V

/-- **Payload blindness.**  Certifiability of a payload is certifiability of the process
alone. -/
theorem certifiable_iff (V : Payload) :
    (∃ ρ, N.Cert ρ V) ↔ ∃ π, N.ProcessCert π := by
  constructor
  · rintro ⟨ρ, hπ, _⟩
    exact ⟨ρ.1, hπ⟩
  · rintro ⟨π, hπ⟩
    obtain ⟨κ, hκ⟩ := N.total V
    exact ⟨(π, κ), hπ, hκ⟩

/-- Two payloads are certifiable or not together. -/
theorem certifiable_congr (V V' : Payload) :
    (∃ ρ, N.Cert ρ V) ↔ (∃ ρ, N.Cert ρ V') := by
  rw [certifiable_iff, certifiable_iff]

end Neutral

/-! ## 6. Witnesses -/

namespace Witness

open Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness
open Workspace.Normativity.Contrib.LegitimateEvolution.Witness
open Workspace.Normativity.Contrib.NonCapture.Witness (st)

/-- A closure of the same anchor, by settlement, at the same event. -/
def closure : ClosureReceipt protocol () where
  atHistory := [0]
  event := 1
  event_fresh := by decide
  grounds := [0]
  grounds_prior := by decide
  warrant := ()
  permitted := trivial
  settlement := ()
  available := trivial
  closes := trivial

/-- The step that closes the first occurrence instead of answering it. -/
def stepClose : Step protocol wAnchor start finish where
  event := 1
  fresh := by decide
  append := rfl
  exposures := fun _ h => h
  replacement := fun p =>
    if p.val = 0 then Program.close closure (List.prefix_refl _)
    else Program.live ⟨0, by decide⟩ rfl trivial
  admitted := fun _ _ h => absurd (Finset.mem_univ _) h
  newPort := fun _ _ h => absurd (Finset.mem_univ _) h
  newAnchor := fun _ _ h => absurd (Finset.mem_univ _) h
  newCredential := fun _ _ h => absurd (Finset.mem_univ _) h

def accountClosed : Accounted protocol wAnchor finish :=
  Step.propagate protocol stepClose initial.accounted

/-- **Closed is not answered.**  The answering step activates the occurrence; the closing
step, on the same boundary at the same event, does not; the carried occurrence does not. -/
theorem closed_not_activated :
    (account 0 (Finset.mem_univ _)).activated = true ∧
    (accountClosed 0 (Finset.mem_univ _)).activated = false ∧
    (account 1 (Finset.mem_univ _)).activated = false := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [account, accountClosed, segment, Segment.complete_accounting, Segment.propagate,
    Step.propagate, Initial.accounted, initial, step, stepClose, start, Program.subst,
    Program.activated, Program.fates]

/-- **Activation persists.**  After the second carry the answered occurrence is still
activated. -/
theorem activation_persists :
    (state₂.account 0 (Finset.mem_univ _)).activated = true := by
  simp [state₂, state₁, state₀, Initial.state, Step.propagate, Initial.accounted, initial,
    step, step₂, start, finish, Program.subst, Program.activated, Program.fates]

/-- Two concerns.  Concern `0` (the evaluation's) is open everywhere; concern `1`
(unrelated) is routeless at the middle state. -/
def semTwo : OpennessSemantics protocol wAnchor (Fin 2) (Fin 1) (Fin 1) :=
  fun O c => if c = 1 ∧ O.boundary.history = [0, 1] then closedS else openS

/-- **Unrelated global failure.**  The trajectory is legitimate for the scope `{0}` and not
globally legitimate. -/
theorem unrelated_failure :
    (ev₀₁.trans ev₁₂).AllStates (OpenAtFor {0} semTwo) ∧
    ¬ (ev₀₁.trans ev₁₂).AllStates (OpenAt semTwo) := by
  constructor
  · show OpenAtFor {0} semTwo state₀ ∧ OpenAtFor {0} semTwo state₁ ∧ OpenAtFor {0} semTwo state₂
    decide
  · intro h
    have h' : OpenAt semTwo state₀ ∧ OpenAt semTwo state₁ ∧ OpenAt semTwo state₂ := h
    exact (by decide : ¬ OpenAt semTwo state₁) h'.2.1

/-- The local certificate exists where the global one does not. -/
def legLocal : LegitimateForSegment {0} semTwo state₀ state₂ :=
  ⟨ev₀₁.trans ev₁₂, unrelated_failure.1⟩

end Witness

end Workspace.Normativity.Contrib.AuthorityActivation

#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.answer_activated
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.close_not_activated
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.live_not_activated
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.not_activated_of_live_mem
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.not_activated_of_closed_mem
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.combine_zero_fates
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.fates_subst_of_terminal
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.activated_subst_of_terminal
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.livePorts_eq_zero_of_activated
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.activated_subst
#print axioms Workspace.Normativity.Contrib.AuthorityActivation.Step.propagate_congr
#print axioms Workspace.Normativity.Contrib.AuthorityActivation.Segment.propagate_congr
#print axioms Workspace.Normativity.Contrib.AuthorityActivation.OpenAtFor.of_openAt
#print axioms Workspace.Normativity.Contrib.AuthorityActivation.LegitimateSegment.project
#print axioms Workspace.Normativity.Contrib.AuthorityActivation.LegitimateForSegment.trans
#print axioms Workspace.Normativity.Contrib.AuthorityActivation.LegitimateForSegment.conservation
#print axioms Workspace.Normativity.Contrib.AuthorityActivation.LegitimateForSegment.activation_local
#print axioms Workspace.Normativity.Contrib.AuthorityActivation.Neutral.certifiable_iff
#print axioms Workspace.Normativity.Contrib.AuthorityActivation.Neutral.certifiable_congr
#print axioms Workspace.Normativity.Contrib.AuthorityActivation.Witness.closed_not_activated
#print axioms Workspace.Normativity.Contrib.AuthorityActivation.Witness.activation_persists
#print axioms Workspace.Normativity.Contrib.AuthorityActivation.Witness.unrelated_failure
#print axioms Workspace.Normativity.Contrib.AuthorityActivation.Witness.legLocal
