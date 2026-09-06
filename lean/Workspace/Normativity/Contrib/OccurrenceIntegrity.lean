/-
# Occurrence-indexed Integrity and the accounting theorem

Round `projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/`.

The object is a **proof-relevant account** of every obligation occurrence ever
exposed.  Occurrence identity (`Occ`) lives outside the content type (`Req`): two
occurrences with equal anchors have two accounts, and nothing in this module can
identify them.  An account is a finite tree whose leaves are exactly the three fates —
a live port of the current docket, an authenticated answer receipt, or an
authenticated closure receipt — and whose internal nodes are authenticated local
transformations of content (carry, split, merge, re-representation), each carrying
maps of anchored evidence in both directions.

**The theorem.**  A transition (`Step`) is a single fresh event that supplies, for
every live port of the docket it starts from, an account at the docket it produces,
and admits fresh occurrences only with an admission credential.  Then
`Segment.complete_accounting`: authenticated initial exposure plus a segment of such
transitions yields an account for every occurrence exposed at the end.  The two
structural facts behind it: `Program.evaluate_subst` (the anchored evidence an account
denotes is preserved through substitution, so carry is faithful by construction) and
`Program.terminals_subst` / `Program.livePorts_subst` (a step never rewrites a
recorded receipt and replaces exactly the live leaves).

**What this does not establish.**  The protocol's predicates — `Admitted`, `Live`,
`Authorized`, `AnswerOK`, `SetView`, `Closes` — and the evidence maps of a `LocalLaw`
are external semantic and authority inputs.  Nothing here says that an implementation
authenticates them, that any occurrence is ever answered, or that a settlement item is
true.  The closure judgment `Closes` is a stored certificate at a strict prefix, so a
later change of interpretation cannot alter a historical discharge; reconsideration of
a closure is a fresh admitted occurrence, not a mutation.

Names are provisional (`AGENTS.md` standard 6).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Fintype.Basic

namespace Workspace.Normativity.Contrib.OccurrenceIntegrity

universe u v w

/-! ## 1. Boundaries and the protocol -/

/-- The docket at a prefix: the authenticated history, the finite set of occurrences
exposed so far, and the live ports with their demanded content.  Occurrence identity
and port identity are separate: a port is a carrier, an occurrence is a debt. -/
structure Boundary (Occ : Type u) (Req : Type v) where
  history : List Nat
  exposed : Finset Occ
  portCount : Nat
  demand : Fin portCount → Req

/-- The application's fixed interpretation.  Every field is an external verification
relation; the theorems below compose them and do not establish them. -/
structure Protocol (Occ : Type u) (Req : Type v) where
  /-- Anchored answer evidence for a requirement: what adequately answers it. -/
  Evidence : Req → Type w
  /-- Externally supplied settlement items. -/
  Settlement : Type w
  /-- The immutable rule/licence/interpretation bundle an authority acts under. -/
  Warrant : Type w
  /-- Admission of an occurrence with its anchor at a prefix. -/
  Admitted : List Nat → Occ → Req → Prop
  /-- A port is live with the given demand at a prefix. -/
  Live : List Nat → Nat → Req → Prop
  /-- The warrant is in force at the prefix. -/
  Authorized : List Nat → Warrant → Prop
  /-- The answer meets the anchored specification under the warrant. -/
  AnswerOK : List Nat → Req → Warrant → Prop
  /-- The settlement item is available through the boundary at the prefix. -/
  SetView : List Nat → Settlement → Prop
  /-- Internal closure judgment: under the warrant in force at the prefix, the
  settlement item suffices to close the requirement. -/
  Closes : List Nat → Req → Settlement → Warrant → Prop
  answer_sound : ∀ h r w, AnswerOK h r w → Evidence r
  closure_sound : ∀ h r s w, SetView h s → Closes h r s w → Evidence r

variable {Occ : Type u} {Req : Type v} (S : Protocol.{u, v, w} Occ Req)

/-! ## 2. Receipts and local laws: immutable historical data -/

/-- Authority to act: a fresh event at a strict prefix, citing only prior grounds,
under a warrant in force there.  A transition cannot cite itself. -/
structure Authority where
  atHistory : List Nat
  event : Nat
  event_fresh : event ∉ atHistory
  grounds : List Nat
  grounds_prior : ∀ g ∈ grounds, g ∈ atHistory
  warrant : S.Warrant
  permitted : S.Authorized atHistory warrant

/-- An answer receipt: authority plus adequacy against the anchor. -/
structure AnswerReceipt (r : Req) extends Authority S where
  adequate : S.AnswerOK atHistory r warrant

/-- A closure receipt: authority, an externally available settlement item, and the
internal closure judgment made at that prefix.  All three are stored. -/
structure ClosureReceipt (r : Req) extends Authority S where
  settlement : S.Settlement
  available : S.SetView atHistory settlement
  closes : S.Closes atHistory r settlement warrant

/-- An authenticated local transformation of content into `arity + 1` successors.
`ofChildren` is faithful carry (the successors jointly still owe the parent);
`toChildren` is no growth (they jointly owe no more).  Carry, split, merge and
re-representation are all instances; a disposal successor is an identity carry. -/
structure LocalLaw (r : Req) extends Authority S where
  arity : Nat
  child : Fin (arity + 1) → Req
  toChildren : S.Evidence r → (i : Fin (arity + 1)) → S.Evidence (child i)
  ofChildren : ((i : Fin (arity + 1)) → S.Evidence (child i)) → S.Evidence r

/-- A terminal fate, as immutable data. -/
inductive Leaf (S : Protocol.{u, v, w} Occ Req) : Type (max v w)
  | answer (r : Req) (receipt : AnswerReceipt S r)
  | close (r : Req) (receipt : ClosureReceipt S r)

/-- The three fates. -/
inductive Fate
  | answered
  | closed
  | live
  deriving DecidableEq

/-! ## 3. Accounts -/

/-- The account of one requirement at a boundary.  Every leaf is a fate; every internal
node is a local law whose event lies in the boundary's history. -/
inductive Program (B : Boundary Occ Req) : Req → Type (max u v w)
  | live {r} (p : Fin B.portCount) (hp : B.demand p = r)
      (credential : S.Live B.history p.val (B.demand p)) : Program B r
  | answer {r} (receipt : AnswerReceipt S r)
      (historical : receipt.atHistory ++ [receipt.event] <+: B.history) : Program B r
  | close {r} (receipt : ClosureReceipt S r)
      (historical : receipt.atHistory ++ [receipt.event] <+: B.history) : Program B r
  | combine {r} (law : LocalLaw S r)
      (historical : law.atHistory ++ [law.event] <+: B.history)
      (children : (i : Fin (law.arity + 1)) → Program B (law.child i)) : Program B r

namespace Program

variable {S} {A B : Boundary Occ Req} {r : Req}

/-- What the account denotes, given evidence for every live port: answers and closures
supply their own evidence; a local law reassembles its successors' evidence. -/
def evaluate {r : Req} (t : Program S B r)
    (liveEvidence : (p : Fin B.portCount) → S.Evidence (B.demand p)) : S.Evidence r :=
  match t with
  | .live p hp _ => hp ▸ liveEvidence p
  | .answer a _ => S.answer_sound _ _ _ a.adequate
  | .close c _ => S.closure_sound _ _ _ _ c.available c.closes
  | .combine law _ children => law.ofChildren fun i => evaluate (children i) liveEvidence

/-- Simultaneous substitution of an account at `B` for every live port of `A`.  Terminal
receipts and local laws are carried unchanged; only their history witness extends. -/
def subst {r : Req} (hab : A.history <+: B.history)
    (replacement : (p : Fin A.portCount) → Program S B (A.demand p))
    (t : Program S A r) : Program S B r :=
  match t with
  | .live p hp _ => hp ▸ replacement p
  | .answer a h => .answer a (h.trans hab)
  | .close c h => .close c (h.trans hab)
  | .combine law h children =>
      .combine law (h.trans hab) fun i => subst hab replacement (children i)

/-- **Faithful carry.**  The denotation of the substituted account is the denotation of
the original, with each live port read through its replacement. -/
theorem evaluate_subst (hab : A.history <+: B.history)
    (replacement : (p : Fin A.portCount) → Program S B (A.demand p))
    (t : Program S A r)
    (values : (p : Fin B.portCount) → S.Evidence (B.demand p)) :
    (t.subst hab replacement).evaluate values =
      t.evaluate fun p => (replacement p).evaluate values := by
  induction t with
  | live p hp _ => cases hp; rfl
  | answer receipt historical => rfl
  | close receipt historical => rfl
  | combine law historical children ih =>
      simp only [subst, evaluate]
      congr 1
      funext i
      exact ih i

/-- The multiset of terminal receipts recorded in an account. -/
def terminals : {r : Req} → Program S B r → Multiset (Leaf S)
  | _, .live _ _ _ => 0
  | _, .answer a _ => {Leaf.answer _ a}
  | _, .close c _ => {Leaf.close _ c}
  | _, .combine _ _ children => ∑ i, terminals (children i)

/-- The multiset of live ports an account still occupies. -/
def livePorts : {r : Req} → Program S B r → Multiset (Fin B.portCount)
  | _, .live p _ _ => {p}
  | _, .answer _ _ => 0
  | _, .close _ _ => 0
  | _, .combine _ _ children => ∑ i, livePorts (children i)

/-- The fates of an account's leaves. -/
def fates : {r : Req} → Program S B r → Multiset Fate
  | _, .live _ _ _ => {Fate.live}
  | _, .answer _ _ => {Fate.answered}
  | _, .close _ _ => {Fate.closed}
  | _, .combine _ _ children => ∑ i, fates (children i)

/-- Every account has at least one fate. -/
theorem exists_fate (t : Program S B r) : ∃ f, f ∈ t.fates := by
  induction t with
  | live => exact ⟨Fate.live, by simp [fates]⟩
  | answer => exact ⟨Fate.answered, by simp [fates]⟩
  | close => exact ⟨Fate.closed, by simp [fates]⟩
  | combine law historical children ih =>
      obtain ⟨f, hf⟩ := ih ⟨0, Nat.zero_lt_succ _⟩
      refine ⟨f, ?_⟩
      show f ∈ ∑ i, (children i).fates
      exact Multiset.mem_sum.mpr ⟨⟨0, Nat.zero_lt_succ _⟩, Finset.mem_univ _, hf⟩

/-- There is no empty account. -/
theorem fates_ne_zero (t : Program S B r) : t.fates ≠ 0 := by
  obtain ⟨f, hf⟩ := t.exists_fate
  intro h
  exact Multiset.notMem_zero f (h ▸ hf)

/-- `Multiset.map` distributes over a finite sum. -/
theorem map_finset_sum {ι α β : Type*} [Fintype ι] (f : α → β) (m : ι → Multiset α) :
    Multiset.map f (∑ i, m i) = ∑ i, Multiset.map f (m i) :=
  map_sum (Multiset.mapAddMonoidHom f) m Finset.univ

/-- `Multiset.sum` distributes over a finite sum. -/
theorem sum_finset_sum {ι α : Type*} [Fintype ι] [AddCommMonoid α] (m : ι → Multiset α) :
    (∑ i, m i).sum = ∑ i, (m i).sum :=
  map_sum Multiset.sumAddMonoidHom m Finset.univ

/-- **Receipts are immutable.**  A substitution keeps every terminal receipt and adds
only the terminals of the accounts substituted at live ports. -/
theorem terminals_subst (hab : A.history <+: B.history)
    (replacement : (p : Fin A.portCount) → Program S B (A.demand p))
    (t : Program S A r) :
    (t.subst hab replacement).terminals =
      t.terminals + (t.livePorts.map fun p => (replacement p).terminals).sum := by
  induction t with
  | live p hp _ =>
      cases hp
      simp [subst, terminals, livePorts]
  | answer receipt historical => simp [subst, terminals, livePorts]
  | close receipt historical => simp [subst, terminals, livePorts]
  | combine law historical children ih =>
      simp only [subst, terminals, livePorts]
      rw [map_finset_sum, sum_finset_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => ih i

/-- **Only live leaves move.**  The live ports of the substituted account are exactly
the live ports of the replacements at the original live ports. -/
theorem livePorts_subst (hab : A.history <+: B.history)
    (replacement : (p : Fin A.portCount) → Program S B (A.demand p))
    (t : Program S A r) :
    (t.subst hab replacement).livePorts =
      (t.livePorts.map fun p => (replacement p).livePorts).sum := by
  induction t with
  | live p hp _ =>
      cases hp
      simp [subst, livePorts]
  | answer receipt historical => simp [subst, livePorts]
  | close receipt historical => simp [subst, livePorts]
  | combine law historical children ih =>
      simp only [subst, livePorts]
      rw [map_finset_sum, sum_finset_sum]
      exact Finset.sum_congr rfl fun i _ => ih i

/-- No step removes a recorded receipt. -/
theorem terminals_le_subst (hab : A.history <+: B.history)
    (replacement : (p : Fin A.portCount) → Program S B (A.demand p))
    (t : Program S A r) :
    t.terminals ≤ (t.subst hab replacement).terminals := by
  rw [terminals_subst]
  exact Multiset.le_add_right _ _

end Program

/-! ## 4. Initial exposure, steps, segments -/

/-- The complete account of a boundary: one account per exposed occurrence, anchored
at that occurrence's immutable specification.  Equal anchors do not merge entries. -/
def Accounted (anchor : Occ → Req) (B : Boundary Occ Req) :=
  (o : Occ) → o ∈ B.exposed → Program S B (anchor o)

/-- Authenticated initial exposure: every exposed occurrence is admitted with its anchor
and sits on a live port demanding exactly that anchor. -/
structure Initial (anchor : Occ → Req) (B : Boundary Occ Req) where
  admitted : ∀ o ∈ B.exposed, S.Admitted B.history o (anchor o)
  port : ∀ o, o ∈ B.exposed → Fin B.portCount
  anchored : ∀ o h, B.demand (port o h) = anchor o
  credential : ∀ o h, S.Live B.history (port o h).val (B.demand (port o h))

/-- The initial account: every occurrence is live at its port. -/
def Initial.accounted {anchor : Occ → Req} {B : Boundary Occ Req}
    (initial : Initial S anchor B) : Accounted S anchor B :=
  fun o h => Program.live (initial.port o h) (initial.anchored o h) (initial.credential o h)

/-- **One transition.**  A fresh event appended to the history; every live port of the
source docket receives an account at the target; occurrences exposed at the source
remain exposed; every fresh occurrence is admitted with its anchor and placed on a live
port demanding it.  There is no field by which content leaves. -/
structure Step (anchor : Occ → Req) (A B : Boundary Occ Req) where
  event : Nat
  fresh : event ∉ A.history
  append : B.history = A.history ++ [event]
  exposures : A.exposed ⊆ B.exposed
  replacement : (p : Fin A.portCount) → Program S B (A.demand p)
  admitted : ∀ o ∈ B.exposed, o ∉ A.exposed → S.Admitted B.history o (anchor o)
  newPort : ∀ o, o ∈ B.exposed → o ∉ A.exposed → Fin B.portCount
  newAnchor : ∀ o h hn, B.demand (newPort o h hn) = anchor o
  newCredential : ∀ o h hn,
    S.Live B.history (newPort o h hn).val (B.demand (newPort o h hn))

theorem Step.prefix {anchor : Occ → Req} {A B : Boundary Occ Req}
    (step : Step S anchor A B) : A.history <+: B.history := by
  rw [step.append]
  exact List.prefix_append _ _

variable [DecidableEq Occ]

/-- Propagate an account through one step: substitute at live ports for old occurrences,
open a live account for fresh ones. -/
def Step.propagate {anchor : Occ → Req} {A B : Boundary Occ Req}
    (step : Step S anchor A B) (account : Accounted S anchor A) : Accounted S anchor B :=
  fun o ho =>
    if old : o ∈ A.exposed then
      (account o old).subst step.prefix step.replacement
    else
      Program.live (step.newPort o ho old) (step.newAnchor o ho old)
        (step.newCredential o ho old)

/-- **The Integrity certificate of a segment**, indexed by its exact endpoint
boundaries.  Two certificates compose only when the middle boundary is literally
shared. -/
inductive Segment (anchor : Occ → Req) :
    Boundary Occ Req → Boundary Occ Req → Type (max u v w)
  | refl (B) : Segment anchor B B
  | cons {A B C} : Step S anchor A B → Segment anchor B C → Segment anchor A C

namespace Segment

variable {S} {anchor : Occ → Req}

/-- Concatenation at a shared boundary. -/
def trans {A B C : Boundary Occ Req} (left : Segment S anchor A B)
    (right : Segment S anchor B C) : Segment S anchor A C :=
  match left with
  | .refl _ => right
  | .cons step tail => .cons step (tail.trans right)

/-- Propagate an account along a segment. -/
def propagate {A B : Boundary Occ Req} :
    Segment S anchor A B → Accounted S anchor A → Accounted S anchor B
  | .refl _, account => account
  | .cons step tail, account => tail.propagate (Step.propagate S step account)

/-- Propagation respects concatenation: the composed certificate acts as the
composite. -/
theorem propagate_trans {A B C : Boundary Occ Req} (left : Segment S anchor A B)
    (right : Segment S anchor B C)
    (account : Accounted S anchor A) :
    (left.trans right).propagate account = right.propagate (left.propagate account) := by
  induction left with
  | refl => rfl
  | cons step tail ih => exact ih right _

/-- **Complete accounting.**  Authenticated initial exposure and a segment of local
transitions give an account for every occurrence exposed at the end. -/
def complete_accounting {A B : Boundary Occ Req} (segment : Segment S anchor A B)
    (initial : Initial S anchor A) :
    Accounted S anchor B :=
  segment.propagate initial.accounted

omit [DecidableEq Occ] in
/-- Exposure only grows along a segment. -/
theorem exposure_mono {A B : Boundary Occ Req} (segment : Segment S anchor A B) :
    A.exposed ⊆ B.exposed := by
  induction segment with
  | refl => exact fun _ h => h
  | cons step tail ih => exact fun _ h => ih (step.exposures h)

/-- Its account at the end of a segment denotes evidence for an occurrence's own anchor,
given evidence for the live ports at the end.  This is the typed form of "on the terms
the obligation was incurred". -/
def denote {A B : Boundary Occ Req} (segment : Segment S anchor A B)
    (initial : Initial S anchor A)
    (values : (p : Fin B.portCount) → S.Evidence (B.demand p))
    (o : Occ) (ho : o ∈ B.exposed) : S.Evidence (anchor o) :=
  (segment.complete_accounting initial o ho).evaluate values

end Segment

omit [DecidableEq Occ] in
/-- A local law never manufactures an unanswerable successor from an answerable
parent, nor an answerable parent from unanswerable successors. -/
theorem LocalLaw.feasibility {r : Req} (law : LocalLaw S r) :
    (Nonempty (S.Evidence r) → Nonempty ((i : Fin (law.arity + 1)) → S.Evidence (law.child i))) ∧
    (Nonempty ((i : Fin (law.arity + 1)) → S.Evidence (law.child i)) → Nonempty (S.Evidence r)) :=
  ⟨fun h => h.map law.toChildren, fun h => h.map law.ofChildren⟩

/-! ## 5. Nonvacuity: two occurrences, one anchor, two fates

Two occurrences share the anchor `()`.  One step answers the first and carries the
second.  The propagated accounts record `answered` and `live` respectively: equal
content does not collapse the two debts, and the answer receipt discharges exactly the
port the step routed it to. -/

namespace Witness

/-- The trivial protocol: everything is authenticated. -/
def protocol : Protocol.{0, 0, 0} (Fin 2) Unit where
  Evidence _ := Unit
  Settlement := Unit
  Warrant := Unit
  Admitted _ _ _ := True
  Live _ _ _ := True
  Authorized _ _ := True
  AnswerOK _ _ _ := True
  SetView _ _ := True
  Closes _ _ _ _ := True
  answer_sound _ _ _ _ := ()
  closure_sound _ _ _ _ _ _ := ()

def anchor : Fin 2 → Unit := fun _ => ()

/-- Both occurrences live on their own ports. -/
def start : Boundary (Fin 2) Unit :=
  ⟨[0], Finset.univ, 2, fun _ => ()⟩

/-- The first occurrence answered, the second carried onto the single remaining port. -/
def finish : Boundary (Fin 2) Unit :=
  ⟨[0, 1], Finset.univ, 1, fun _ => ()⟩

def initial : Initial protocol anchor start where
  admitted _ _ := trivial
  port o _ := o
  anchored _ _ := rfl
  credential _ _ := trivial

def receipt : AnswerReceipt protocol () where
  atHistory := [0]
  event := 1
  event_fresh := by decide
  grounds := [0]
  grounds_prior := by decide
  warrant := ()
  permitted := trivial
  adequate := trivial

def step : Step protocol anchor start finish where
  event := 1
  fresh := by decide
  append := rfl
  exposures := fun _ h => h
  replacement := fun p =>
    if p.val = 0 then Program.answer receipt (List.prefix_refl _)
    else Program.live ⟨0, by decide⟩ rfl trivial
  admitted := fun _ _ h => absurd (Finset.mem_univ _) h
  newPort := fun _ _ h => absurd (Finset.mem_univ _) h
  newAnchor := fun _ _ h => absurd (Finset.mem_univ _) h
  newCredential := fun _ _ h => absurd (Finset.mem_univ _) h

def segment : Segment protocol anchor start finish := .cons step (.refl _)

/-- The complete account at the end is inhabited for both occurrences. -/
def account : Accounted protocol anchor finish := segment.complete_accounting initial

theorem first_answered : (account 0 (Finset.mem_univ _)).fates = {Fate.answered} := by
  simp [account, segment, Segment.complete_accounting, Segment.propagate, Step.propagate,
    Initial.accounted, initial, step, start, Program.subst, Program.fates]

theorem second_live : (account 1 (Finset.mem_univ _)).fates = {Fate.live} := by
  simp [account, segment, Segment.complete_accounting, Segment.propagate, Step.propagate,
    Initial.accounted, initial, step, start, Program.subst, Program.fates]

/-- Equal anchors, distinct fates: the lattice-collapse attack has no purchase. -/
theorem distinct_fates :
    (account 0 (Finset.mem_univ _)).fates ≠ (account 1 (Finset.mem_univ _)).fates := by
  rw [first_answered, second_live]
  decide

end Witness

end Workspace.Normativity.Contrib.OccurrenceIntegrity

#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.evaluate_subst
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.fates_ne_zero
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.terminals_subst
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.livePorts_subst
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.terminals_le_subst
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Segment.propagate_trans
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Segment.complete_accounting
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Segment.exposure_mono
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Segment.denote
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.LocalLaw.feasibility
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness.first_answered
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness.second_live
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness.distinct_fates
