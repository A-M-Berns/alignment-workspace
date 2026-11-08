/-
# Admission by standing: the protocol's admission predicate from the authority allocation

Round `projects/normativity/rounds/2026-11-07-score-side-binding/`.

`Protocol.Admitted : List ℕ → Occ → Req → Prop` is the typed admission predicate
`WarrantInductor.Entitlement` consumes; the fixture's protocol made it `True`.  The authority
module's allocation `AuthorityModule.AuthAlloc` says who holds which matter.  **Admission by
standing** (`admittedByStanding`): an obligation occurrence is admitted at history `h` when
its issuer holds the obligation's matter under the allocation current at `h`; first-person
commitments are matters the reasoner holds itself (issuer `agent`, holder `agent`).  The types
meet without adaptation: `withStanding` replaces one field of a protocol.

The fixture (§2) is the witness's `state₀` rebuilt over the protocol with standing: two
matters, one per exposed obligation, the first the principal's and the second — the origin of
the `Z` warrant — the reasoner's own.  `entitlementS` inhabits `Entitlement` on it for the
witness's grounds at every date, with the admission clause discharged by the allocation
(`admitted_by_allocation`).  The clause has content: under the allocation that moves the first
matter to the agent, the first obligation is not admitted (`reallocated_not_admitted`), and no
entitlement over any obligation state of that protocol may trace an occurrence to it
(`reallocated_entitles_nothing`), the counterpart of the witness's `answered_not_entitled`.
Of entitlement's four conditions, exposure is content-free at the fixture (everything is
exposed), admission and liveness carry content, and `Expresses` remains typed.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.WarrantInductorWitness
import Workspace.Deference.Contrib.AuthorityModule

namespace Workspace.Normativity.Contrib.AdmissionByStanding

open Workspace.Normativity.Contrib.OccurrenceIntegrity
open Workspace.Normativity.Contrib.OpenIntegrityEvolution
open Workspace.Deference.Contrib.AuthorityModule
open Workspace.Normativity.Contrib.WarrantInductor
open Workspace.Normativity.Contrib.WarrantInductorWitness (N grounds)
open Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness (protocol anchor start)
open Workspace.Normativity.Contrib.OpenIntegrityEvolution.Witness (wAnchor)

/-! ## 1. Admission by standing -/

section General

universe u v w

variable {Occ : Type u} {Req : Type v} {M Res Disc : Type*}

/-- **Admission by standing** (provisional name): an obligation occurrence is admitted at
history `h` when its issuer holds its matter under the allocation current at `h`.  A
first-person commitment is a matter the reasoner holds itself: issuer `agent`, holder
`agent`. -/
def admittedByStanding (allocAt : List ℕ → AuthAlloc M Res Disc) (matter : Occ → M)
    (issuer : Occ → Holder) : List ℕ → Occ → Req → Prop :=
  fun h o _ => ((allocAt h).entry (matter o)).holder = issuer o

/-- A protocol with its admission predicate replaced by admission by standing. -/
def withStanding (S : Protocol.{u, v, w} Occ Req) (allocAt : List ℕ → AuthAlloc M Res Disc)
    (matter : Occ → M) (issuer : Occ → Holder) : Protocol.{u, v, w} Occ Req :=
  { S with Admitted := admittedByStanding allocAt matter issuer }

theorem withStanding_admitted (S : Protocol.{u, v, w} Occ Req)
    (allocAt : List ℕ → AuthAlloc M Res Disc) (matter : Occ → M) (issuer : Occ → Holder)
    (h : List ℕ) (o : Occ) (r : Req) :
    (withStanding S allocAt matter issuer).Admitted h o r ↔
      ((allocAt h).entry (matter o)).holder = issuer o := Iff.rfl

/-- **Reallocation withdraws admission**: moving an occurrence's matter to a holder other than
its issuer makes it inadmissible at every history under that allocation. -/
theorem not_admitted_of_withHolder (J : AuthAlloc M Res Disc) (matter : Occ → M)
    (issuer : Occ → Holder) (o : Occ) (hold : Holder) (hne : hold ≠ issuer o) (h : List ℕ)
    (r : Req) :
    ¬ admittedByStanding (fun _ => J.withHolder (matter o) hold) matter issuer h o r := by
  simp [admittedByStanding, AuthAlloc.withHolder, hne]

end General

/-! ## 2. The fixture: `state₀` over the protocol with standing -/

/-- The issuers: the first obligation is the principal's, the second — the origin of the `Z`
warrant — the reasoner's own commitment. -/
def issuer : Fin 2 → Holder := ![.principal, .agent]

/-- The allocation: each obligation is its own matter, held by its issuer; the principal is the
meta-holder; the floor is empty. -/
def J₀ : AuthAlloc (Fin 2) Unit Unit :=
  ⟨fun m => ⟨issuer m, Set.univ, 0, 0, ∅⟩, .principal, ∅⟩

/-- The fixture's protocol with admission by standing under `J₀` at every history. -/
def protocolS : Protocol.{0, 0, 0} (Fin 2) Unit := withStanding protocol (fun _ => J₀) id issuer

/-- Both obligations exposed on their own ports, each admitted by the allocation. -/
def initialS : Initial protocolS anchor start where
  admitted _ _ := rfl
  port o _ := o
  anchored _ _ := rfl
  credential _ _ := trivial

/-- The accounted state over the protocol with standing. -/
def stateS : ObligationState protocolS wAnchor := initialS.state

theorem account_live (e : Fin 2) (h : e ∈ stateS.boundary.exposed) :
    Fate.live ∈ (stateS.account e h).fates := by
  simp [stateS, Initial.state, Initial.accounted, initialS, Program.fates]

/-- **Admission by the allocation**: at every history, each obligation's issuer holds its
matter under `J₀`. -/
theorem admitted_by_allocation (h : List ℕ) (e : Fin 2) : protocolS.Admitted h e () := rfl

/-- **The first-person commitment is admitted**: the reasoner holds the matter it committed
itself on. -/
theorem first_person_admitted (h : List ℕ) :
    protocolS.Admitted h 1 () ∧ (J₀.entry 1).holder = .agent ∧ issuer 1 = .agent :=
  ⟨rfl, rfl, rfl⟩

/-- **The entitlement on the standing fixture**: the witness's origins (the first warrant's
occurrences realize obligation `0`, the `Z` warrant obligation `1`), admission by the
allocation, liveness from the accounts, `Expresses` total. -/
def entitlementS (n : ℕ) : Entitlement stateS (N n).grounds (fun _ _ => True) where
  origin o := if o.id = 4 then 1 else 0
  origin_exposed _ _ := by simp [stateS, Initial.state, start]
  admitted _ _ := rfl
  live _ _ := account_live _ _
  faithful _ _ := trivial

/-- The allocation with the first matter moved to the agent. -/
noncomputable def J₁ : AuthAlloc (Fin 2) Unit Unit := J₀.withHolder 0 .agent

/-- The protocol with standing under `J₁`. -/
noncomputable def protocolS₁ : Protocol.{0, 0, 0} (Fin 2) Unit :=
  withStanding protocol (fun _ => J₁) id issuer

/-- **Reallocation withdraws admission at the fixture**: under `J₁` the principal's obligation
is not admitted at any history. -/
theorem reallocated_not_admitted (h : List ℕ) : ¬ protocolS₁.Admitted h 0 () :=
  not_admitted_of_withHolder J₀ id issuer 0 .agent (by decide) h ()

/-- **A reallocated obligation entitles nothing**: over any obligation state of the protocol
under `J₁`, no entitlement of the witness's grounds, under any `Expresses` relation, may trace
an occurrence to obligation `0`.  The counterpart of `answered_not_entitled`, with the account
replaced by the allocation. -/
theorem reallocated_entitles_nothing (O : ObligationState protocolS₁ wAnchor)
    (Expresses : Unit → SeedStatics.Form 5 → Prop) (E : Entitlement O grounds Expresses)
    (o : WarrantEntitlement.Occurrence 5) (ho : o ∈ grounds) : E.origin o ≠ 0 := by
  intro h
  have := E.admitted o ho
  rw [h] at this
  exact reallocated_not_admitted _ this

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.admittedByStanding
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.withStanding
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.withStanding_admitted
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.not_admitted_of_withHolder
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.issuer
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.J₀
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.protocolS
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.initialS
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.stateS
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.account_live
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.admitted_by_allocation
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.first_person_admitted
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.entitlementS
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.J₁
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.protocolS₁
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.reallocated_not_admitted
#print axioms Workspace.Normativity.Contrib.AdmissionByStanding.reallocated_entitles_nothing

end Workspace.Normativity.Contrib.AdmissionByStanding
