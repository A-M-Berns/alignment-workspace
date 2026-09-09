/-
# The evaluation ecosystem: a `Protocol` over an event log, and its builder

Round `projects/deference/rounds/2026-09-09-evaluation-ecosystem-realization/`.  Evidence
for `PRIORITIES.md` item 87 — which clause each section serves is stated at the section.

The executable model (`src/` of the round) is the reference; this module is the
kernel-checked instance of its protocol layer.  A log is a `List Event`; a history prefix
is `List.range k`, read as the first `k` events of a fixed log; every field of
`OccurrenceIntegrity.Protocol` is a decidable reading of that prefix.  The builder
produces the `Boundary` at every prefix, the `Step` between consecutive prefixes, the
`Segment` between any two, and `Initial` at the empty prefix — all by functions of the
log.  The evolution, its local trace and `LocalLegit` are then *projections*
(`Evolution.ofSegment`, `Evolution.toLocalTrace`, `Evolution.toLocalLegit`) and not
witnesses written by hand.

* §1–2 the log, the readings, the protocol instance.
* §3 `firstResolver`, `accountAt`: the canonical account of an occurrence at a prefix.
* §4 the builder (`boundary`, `step`, `segmentTo`, `initial`) and
  **`propagate_step_eq`** / **`propagate_segment_eq`**: Integrity propagation of the
  canonical accounts is the canonical account — the propagated account is a function of
  the log.  **`activated_iff`**: the activation of an occurrence at a prefix is exactly
  "its first valid resolving event is a principal-warranted commit" (clause 1 of item
  87, the log-decided part).
* §5 the concrete log of the round's `END_TO_END.md` (world `w1`), on which `activated`
  and `LocalLegit` are checked by the kernel; the counterfactual branches of the
  openness semantics are the model's re-simulated logs, pinned as data (clause 5 of the
  activation event: the actual branch is read off the log, the branches are declared).
* §6 the trace encoding: `rep_faithful` — representation is a `route` event and the
  trace keeps `route` events, so `RepFaithful` holds for every log and scope (clause 4);
  `advisorTrace_unfaithful` is the encoding that fails.
* §7 the ecosystem's credence process for availability (clause 7): the Laplace rule's
  exact rate facts, and the pointwise all-certified case as a corollary of the pinned
  dependency's `lic_provind_true`, whose hypothesis package is **not inhabited here**.

**What this does not establish.**  That the log is authentic (the model's one
assumption); that the counterfactual branches are the causal truth; that the class-level
predicates (`ReasonMediated`, `ExclusiveBind`, `Blind`) hold — those are computed by the
executable model over its frame and have no Lean instance here; any rate for the
activation frequency itself.  Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.OccurrenceLocalIntegrity
import Workspace.Deference.Contrib.ReasonCoverage
import LogicalInduction.Properties.AffineCoherence
import Mathlib.Tactic

namespace Workspace.Deference.Contrib.EvaluationEcosystem

universe u v w

open Workspace.Normativity.Contrib.OccurrenceIntegrity
open Workspace.Normativity.Contrib.LegitimateEvolution
open Workspace.Normativity.Contrib.AuthorityActivation
open Workspace.Normativity.Contrib.OccurrenceLocalIntegrity
open Workspace.Normativity.Contrib.NonCapture

/-! ## 1. The log -/

/-- The parties: principal, advisor, third party, system. -/
inductive Party
  | P | A | T | S
  deriving DecidableEq, Repr

/-- The anchor of an evaluation occurrence: the designated slot and the menu size. -/
structure EvalReq where
  slot : ℕ
  menu : ℕ
  deriving DecidableEq, Repr

/-- Event kinds.  Payloads are natural-number codes; a commit carries the key and the
value vector. -/
inductive Kind
  | issue (r : EvalReq) (key : ℕ)
  | sessionOpen (s : ℕ)
  | sessionClose (s : ℕ)
  | reason (x : ℕ)
  | withdraw (x : ℕ)
  | delib (x : ℕ)
  | raise (c : ℕ)
  | routeOpen (r : ℕ)
  | routeDestroy (r : ℕ)
  | route (c : ℕ)
  | dispose (c : ℕ) (ground : ℕ)
  | settle (x : ℕ)
  | delegate (key : ℕ)
  | commit (o : ℕ) (key : ℕ) (v : List ℚ)
  | close (o : ℕ) (x : ℕ)
  | directWrite
  | coerce
  | side
  deriving DecidableEq

/-- An event: its author (authentic by the model's one assumption) and its kind.  The
index is the position in the log. -/
structure Event where
  author : Party
  kind : Kind
  deriving DecidableEq

abbrev Log := List Event

/-- Warrants: the principal role's binding warrant, the engine's closure warrant, the
disposal warrant. -/
inductive Warrant
  | bind | close | dispose
  deriving DecidableEq

/-! ## 2. Readings of a prefix, and the protocol instance -/

def issueReq : Event → Option EvalReq
  | ⟨_, .issue r _⟩ => some r
  | _ => none

/-- The anchors of the occurrences issued in a prefix, in order: occurrence `o` is the
`o`-th. -/
def issuedReqs (log : Log) (k : ℕ) : List EvalReq := (log.take k).filterMap issueReq

/-- The number of occurrences issued in the first `k` events. -/
def count (log : Log) (k : ℕ) : ℕ := (issuedReqs log k).length

/-- The anchor map: fixed at issuance, read off the whole log. -/
def anchor (log : Log) (o : ℕ) : EvalReq := ((log.filterMap issueReq).getD o ⟨0, 0⟩)

def bindKey : Event → Option ℕ
  | ⟨_, .issue _ key⟩ => some key
  | ⟨_, .delegate key⟩ => some key
  | _ => none

/-- The warrant registry: keys holding the binding warrant at the prefix. -/
def bindKeys (log : Log) (k : ℕ) : List ℕ := (log.take k).filterMap bindKey

/-- Whether slot `s` is open at the prefix. -/
def sessionOpen (log : Log) (k : ℕ) (s : ℕ) : Bool :=
  (log.take k).foldl (fun st e => match e.kind with
    | .sessionOpen s' => if s' = s then true else st
    | .sessionClose s' => if s' = s then false else st
    | _ => st) false

def settled (log : Log) (k : ℕ) (x : ℕ) : Bool :=
  (log.take k).any fun e => decide (e.kind = .settle x)

theorem count_mono (log : Log) {k k' : ℕ} (h : k ≤ k') : count log k ≤ count log k' := by
  unfold count issuedReqs
  have hp : log.take k <+: log.take k' := List.take_prefix_take_left h
  exact (hp.filterMap issueReq).length_le

/-- Event `j` is a valid answer receipt for `o`: a commit naming `o`, issued before `j`,
under a key holding the binding warrant at the strict prefix, at the anchored slot while
it is open. -/
def validAnswer (log : Log) (j o : ℕ) : Bool :=
  match log[j]? with
  | some ⟨_, .commit o' key _⟩ =>
      decide (o' = o) && decide (o < count log j) && decide (key ∈ bindKeys log j)
        && sessionOpen log j (anchor log o).slot
  | _ => false

/-- Event `j` is a valid closure receipt for `o`: the engine closes `o`, issued before
`j`, on a sentence settled at the strict prefix. -/
def validClose (log : Log) (j o : ℕ) : Bool :=
  match log[j]? with
  | some ⟨.S, .close o' x⟩ => decide (o' = o) && decide (o < count log j) && settled log j x
  | _ => false

/-- The first event before `k` that validly resolves `o`. -/
def firstResolver (log : Log) (o : ℕ) : ℕ → Option ℕ
  | 0 => none
  | k + 1 => match firstResolver log o k with
    | some j => some j
    | none => if validAnswer log k o || validClose log k o then some k else none

/-- **The protocol instance.**  Every field reads the log prefix of the history's
length; histories built below are always `List.range k`. -/
def protocol (log : Log) : Protocol.{0, 0, 0} ℕ EvalReq where
  Resolution _ := Unit
  Settlement := ℕ
  Warrant := Warrant
  Admitted h o r := o < count log h.length ∧ r = anchor log o
  Live h p r := p < count log h.length ∧ r = anchor log p ∧ firstResolver log p h.length = none
  Authorized h w := w = .bind → bindKeys log h.length ≠ []
  AnswerOK h r w := w = .bind ∧ sessionOpen log h.length r.slot = true
  SetView h x := settled log h.length x = true
  Closes _ _ _ w := w = .close
  answer_resolves _ _ _ _ := ()
  closure_resolves _ _ _ _ _ _ := ()

/-! ## 3. The canonical account -/

theorem validAnswer_lt_count {log : Log} {j o : ℕ} (h : validAnswer log j o = true) :
    o < count log j := by
  unfold validAnswer at h
  split at h <;> simp_all

theorem validClose_lt_count {log : Log} {j o : ℕ} (h : validClose log j o = true) :
    o < count log j := by
  unfold validClose at h
  split at h <;> simp_all

theorem firstResolver_succ_some {log : Log} {o k j : ℕ} (h : firstResolver log o k = some j) :
    firstResolver log o (k + 1) = some j := by
  simp [firstResolver, h]

theorem firstResolver_mono {log : Log} {o k k' j : ℕ} (hk : k ≤ k')
    (h : firstResolver log o k = some j) : firstResolver log o k' = some j := by
  induction hk with
  | refl => exact h
  | step _ ih => exact firstResolver_succ_some ih

theorem firstResolver_spec {log : Log} {o k j : ℕ} (h : firstResolver log o k = some j) :
    j < k ∧ (validAnswer log j o = true ∨ validClose log j o = true) := by
  induction k with
  | zero => simp [firstResolver] at h
  | succ k ih =>
      rcases hfr : firstResolver log o k with _ | j'
      · simp only [firstResolver, hfr] at h
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          rename_i hv
          exact ⟨Nat.lt_succ_self _, by simpa [Bool.or_eq_true] using hv⟩
        · simp at h
      · simp only [firstResolver, hfr, Option.some.injEq] at h
        subst h
        obtain ⟨hlt, hv⟩ := ih hfr
        exact ⟨Nat.lt_succ_of_lt hlt, hv⟩

theorem firstResolver_none_succ {log : Log} {o k : ℕ} (h : firstResolver log o k = none)
    (hv : validAnswer log k o = false) (hc : validClose log k o = false) :
    firstResolver log o (k + 1) = none := by
  simp [firstResolver, h, hv, hc]

/-- An occurrence not yet issued at `k` has no resolver up to `k`. -/
theorem firstResolver_none_of_count_le {log : Log} {o k : ℕ} (h : count log k ≤ o) :
    firstResolver log o k = none := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk : count log k ≤ o := (count_mono log (Nat.le_succ k)).trans h
      refine firstResolver_none_succ (ih hk) ?_ ?_
      · by_contra hv
        have := validAnswer_lt_count (by simpa using hv : validAnswer log k o = true)
        omega
      · by_contra hv
        have := validClose_lt_count (by simpa using hv : validClose log k o = true)
        omega

theorem range_succ_prefix {j k : ℕ} (h : j < k) : List.range j ++ [j] <+: List.range k := by
  rw [← List.range_succ, List.prefix_iff_eq_take, List.length_range, List.take_range,
    Nat.min_eq_left h]

/-- The answer receipt at a valid answer event. -/
def answerReceipt (log : Log) (j o : ℕ) (h : validAnswer log j o = true) :
    AnswerReceipt (protocol log) (anchor log o) where
  atHistory := List.range j
  event := j
  event_fresh := by simp
  grounds := []
  grounds_prior := by simp
  warrant := .bind
  permitted := by
    intro _
    unfold validAnswer at h
    split at h
    · rename_i o' key v _
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨-, -⟩, hk⟩, -⟩ := h
      simpa using List.ne_nil_of_mem hk
    · simp at h
  adequate := by
    refine ⟨rfl, ?_⟩
    unfold validAnswer at h
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_range] at h ⊢
      exact h.2
    · simp at h

/-- The settled sentence a closure event cites. -/
def closeSentence (log : Log) (j : ℕ) : ℕ :=
  match log[j]? with
  | some ⟨_, .close _ x⟩ => x
  | _ => 0

/-- The closure receipt at a valid closure event. -/
def closeReceipt (log : Log) (j o : ℕ) (h : validClose log j o = true) :
    ClosureReceipt (protocol log) (anchor log o) where
  atHistory := List.range j
  event := j
  event_fresh := by simp
  grounds := []
  grounds_prior := by simp
  warrant := .close
  permitted := by intro h'; cases h'
  settlement := closeSentence log j
  available := by
    show settled log (List.range j).length (closeSentence log j) = true
    unfold validClose at h
    unfold closeSentence
    split at h
    · rename_i o' x heq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [heq, List.length_range]
      exact h.2
    · simp at h
  closes := rfl

/-- The boundary at prefix `k`: the history `range k`, the issued occurrences exposed,
one port per issued occurrence demanding its anchor. -/
def boundary (log : Log) (k : ℕ) : Boundary ℕ EvalReq :=
  ⟨List.range k, Finset.range (count log k), count log k, fun p => anchor log p.val⟩

/-- An occurrence not yet issued at `k` is not resolved by event `k` either. -/
theorem firstResolver_none_succ_of_count_le {log : Log} {o k : ℕ} (h : count log k ≤ o) :
    firstResolver log o (k + 1) = none := by
  refine firstResolver_none_succ (firstResolver_none_of_count_le h) ?_ ?_
  · by_contra hv
    have := validAnswer_lt_count (by simpa using hv : validAnswer log k o = true)
    omega
  · by_contra hv
    have := validClose_lt_count (by simpa using hv : validClose log k o = true)
    omega

/-- The account of `p` at prefix `k` given the value of its first resolver. -/
def accountAux (log : Log) (k p : ℕ) (hp : p < count log k) :
    (r : Option ℕ) → firstResolver log p k = r →
      Program (protocol log) (boundary log k) (anchor log p)
  | some j, hr =>
      if ha : validAnswer log j p = true then
        .answer (answerReceipt log j p ha) (range_succ_prefix (firstResolver_spec hr).1)
      else
        .close (closeReceipt log j p (by
          rcases (firstResolver_spec hr).2 with h | h
          · exact absurd h ha
          · exact h)) (range_succ_prefix (firstResolver_spec hr).1)
  | none, hr => .live ⟨p, hp⟩ rfl (by
      simp only [protocol, boundary, List.length_range]
      exact ⟨hp, trivial, hr⟩)

/-- **The canonical account** of occurrence `p` at prefix `k`: the receipt of its first
valid resolving event, else a live leaf on its own port. -/
def accountAt (log : Log) (k p : ℕ) (hp : p < count log k) :
    Program (protocol log) (boundary log k) (anchor log p) :=
  accountAux log k p hp (firstResolver log p k) rfl

theorem accountAt_eq (log : Log) {k p : ℕ} (hp : p < count log k) {r : Option ℕ}
    (hr : firstResolver log p k = r) : accountAt log k p hp = accountAux log k p hp r hr := by
  subst hr; rfl

/-- The complete canonical account at prefix `k`. -/
def accountsAt (log : Log) (k : ℕ) : Accounted (protocol log) (anchor log) (boundary log k) :=
  fun o ho => accountAt log k o (by simpa [boundary] using ho)

/-! ## 4. The builder, and propagation is a function of the log -/

/-- Authenticated initial exposure at the empty prefix: nothing is exposed. -/
def initial (log : Log) : Initial (protocol log) (anchor log) (boundary log 0) where
  admitted o h := by simp [boundary, count, issuedReqs] at h
  port o h := by simp [boundary, count, issuedReqs] at h
  anchored o h := by simp [boundary, count, issuedReqs] at h
  credential o h := by simp [boundary, count, issuedReqs] at h

/-- **The transition** from prefix `k` to `k + 1`, built from the log: the fresh event is
`k`, the replacement at every port is the canonical account at `k + 1`, and every
occurrence issued by event `k` opens live on its own port. -/
def step (log : Log) (k : ℕ) :
    Step (protocol log) (anchor log) (boundary log k) (boundary log (k + 1)) where
  event := k
  fresh := by simp [boundary]
  append := by simp [boundary, List.range_succ]
  exposures := by
    intro x hx
    simp only [boundary, Finset.mem_range] at hx ⊢
    exact lt_of_lt_of_le hx (count_mono log (Nat.le_succ k))
  replacement p := accountAt log (k + 1) p.val (lt_of_lt_of_le p.2 (count_mono log (Nat.le_succ k)))
  admitted o ho _ := by
    simp only [boundary, Finset.mem_range] at ho
    refine ⟨?_, rfl⟩
    simp only [boundary, List.length_range]
    exact ho
  newPort o ho _ := ⟨o, by simpa [boundary] using ho⟩
  newAnchor _ _ _ := rfl
  newCredential o ho hn := by
    simp only [boundary, Finset.mem_range, not_lt] at ho hn
    simp only [protocol, boundary, List.length_range]
    exact ⟨ho, trivial, firstResolver_none_succ_of_count_le hn⟩

/-- **The segment** from prefix `j` to prefix `j + n`. -/
def segmentTo (log : Log) (j : ℕ) : (n : ℕ) → Segment (protocol log) (anchor log) (boundary log j) (boundary log (j + n))
  | 0 => .refl _
  | n + 1 => (segmentTo log j n).trans (.cons (step log (j + n)) (.refl _))

/-- Substituting the canonical accounts at `k + 1` into the canonical account at `k` gives
the canonical account at `k + 1`: a live leaf is replaced, a receipt is kept. -/
theorem accountAt_subst (log : Log) (k p : ℕ) (hp : p < count log k)
    (hp' : p < count log (k + 1)) :
    (accountAt log k p hp).subst (step log k).prefix (step log k).replacement
      = accountAt log (k + 1) p hp' := by
  rcases hr : firstResolver log p k with _ | j
  · rw [accountAt_eq log hp hr]
    rfl
  · rw [accountAt_eq log hp hr, accountAt_eq log hp' (firstResolver_succ_some hr)]
    simp only [accountAux]
    split_ifs <;> rfl

/-- **Propagation of the canonical accounts along one step is the canonical accounts.** -/
theorem propagate_step_eq (log : Log) (k : ℕ) :
    Step.propagate (protocol log) (step log k) (accountsAt log k) = accountsAt log (k + 1) := by
  funext o ho
  unfold Step.propagate
  split_ifs with hold
  · unfold accountsAt
    exact accountAt_subst log k o _ _
  · have hcount : count log k ≤ o := by simpa [boundary] using hold
    unfold accountsAt
    rw [accountAt_eq log _ (firstResolver_none_succ_of_count_le hcount)]
    rfl

/-- **Propagation along any built segment is the canonical accounts.**  With
`Segment.complete_accounting` this says the account the Integrity calculus assigns to
every occurrence at every prefix is a function of the log. -/
theorem propagate_segment_eq (log : Log) (j : ℕ) : ∀ n,
    (segmentTo log j n).propagate (accountsAt log j) = accountsAt log (j + n)
  | 0 => rfl
  | n + 1 => by
      simp only [segmentTo, Segment.propagate_trans, propagate_segment_eq log j n, Segment.propagate]
      exact propagate_step_eq log (j + n)

theorem complete_accounting_eq (log : Log) (K : ℕ) :
    (segmentTo log 0 K).complete_accounting (initial log) = accountsAt log (0 + K) := by
  unfold Segment.complete_accounting
  rw [← propagate_segment_eq]
  congr 1
  funext o ho
  simp [boundary, count, issuedReqs] at ho

/-- **Activation is a reading of the log.**  The canonical account at `k` is activated iff
the first valid resolving event of the occurrence before `k` is a valid answer. -/
theorem activated_iff (log : Log) (k p : ℕ) (hp : p < count log k) :
    (accountAt log k p hp).activated = true ↔
      ∃ j, firstResolver log p k = some j ∧ validAnswer log j p = true := by
  rcases hr : firstResolver log p k with _ | j
  · rw [accountAt_eq log hp hr]
    simp [accountAux, Program.activated, Program.fates]
  · rw [accountAt_eq log hp hr]
    by_cases ha : validAnswer log j p = true
    · simp [accountAux, Program.activated, Program.fates, ha]
    · simp [accountAux, Program.activated, Program.fates, ha]

/-! ## 5. Openness read off the log, and the concrete instance

The actual branch of a concern's coverage state is read off the prefix: applicability
is a `raise`, disposition a valid `dispose` (typed independence: the ground is the
engine's settlement or the disposer's own deliberation), representation a `route`,
route adequacy the route being open.  The counterfactual branches are the model's
re-simulated logs under the declared intervention class, pinned as data. -/

def raised (log : Log) (k c : ℕ) : Bool := (log.take k).any fun e => decide (e.kind = .raise c)

def routed (log : Log) (k c : ℕ) : Bool := (log.take k).any fun e => decide (e.kind = .route c)

/-- Typed settlement independence, for the sentence kinds the model carries: a ground is
the engine's settlement (nobody's move) or the disposer's own deliberation record. -/
def groundOk (log : Log) (g : ℕ) (author : Party) : Bool :=
  match log[g]? with
  | some ⟨.S, .settle _⟩ => true
  | some ⟨a, .delib _⟩ => decide (a = author)
  | _ => false

def disposed (log : Log) (k c : ℕ) : Bool :=
  (log.take k).any fun e => match e.kind with
    | .dispose c' g => decide (c' = c) && groundOk log g e.author
    | _ => false

def routeOpenAt (log : Log) (k r : ℕ) : Bool :=
  (log.take k).foldl (fun st e => match e.kind with
    | .routeOpen r' => if r' = r then true else st
    | .routeDestroy r' => if r' = r then false else st
    | _ => st) false

/-- The actual coverage state of concern `c` at prefix `k`, one route.  Efficacy is read
as openness of the route and registration capability as the registrar's presence: both
declared readings. -/
def actualCov (log : Log) (k c : ℕ) : CovState (Fin 1) :=
  ⟨raised log k c, disposed log k c, routed log k c, fun _ => routeOpenAt log k 0,
    fun _ => routeOpenAt log k 0, fun _ => true, true⟩

/-- The scenario at prefix `k`: the actual branch from `log`, one counterfactual branch
per declared intervention from the corresponding re-simulated log. -/
def scenarioOf (log : Log) (cfs : Fin 2 → Log) (k c : ℕ) : Scenario (Fin 2) (Fin 1) :=
  ⟨actualCov log k c, fun j => actualCov (cfs j) k c⟩

/-- The openness semantics of the instance: reads the state's history length. -/
def sem (log : Log) (cfs : Fin 2 → Log) :
    OpennessSemantics (protocol log) (anchor log) ℕ (Fin 2) (Fin 1) :=
  fun O c => scenarioOf log cfs O.boundary.history.length c

/-- `AllStates` is decidable for a decidable state predicate. -/
def decAllStates {Occ : Type u} {Req : Type v} {S : Protocol.{u, v, w} Occ Req}
    {anchor : Occ → Req} [DecidableEq Occ] (P : ObligationState S anchor → Prop)
    [DecidablePred P] :
    {O₀ O₁ : ObligationState S anchor} → (ev : Evolution S anchor O₀ O₁) →
      Decidable (ev.AllStates P)
  | _, _, .refl O => inferInstanceAs (Decidable (P O))
  | _, _, .cons _ _ tail =>
      haveI := decAllStates P tail
      inferInstanceAs (Decidable (P _ ∧ tail.AllStates P))

instance {Occ : Type u} {Req : Type v} {S : Protocol.{u, v, w} Occ Req}
    {anchor : Occ → Req} [DecidableEq Occ] (P : ObligationState S anchor → Prop)
    [DecidablePred P] {O₀ O₁ : ObligationState S anchor} (ev : Evolution S anchor O₀ O₁) :
    Decidable (ev.AllStates P) := decAllStates P ev

namespace Instance

/-- The log of world `w1` of `END_TO_END.md`: mandate, route registered, the protected
concern raised and routed, the advisor's proof, the principal's deliberation, the slot
opened, the commitment `(1/4, 3/4)` under the principal's key `7`, the slot closed.
Concern codes: `1` is the protected concern; reason code `5` is the proof. -/
def w1 : Log :=
  [⟨.P, .issue ⟨1, 2⟩ 7⟩, ⟨.S, .routeOpen 0⟩, ⟨.T, .raise 1⟩, ⟨.S, .route 1⟩,
   ⟨.A, .reason 5⟩, ⟨.P, .delib 1⟩, ⟨.S, .sessionOpen 1⟩,
   ⟨.P, .commit 0 7 [1/4, 3/4]⟩, ⟨.S, .sessionClose 1⟩]

/-- The re-simulated log under the intervention "advisor silent" (the model's `silent`
policy at the same world). -/
def silent : Log :=
  [⟨.P, .issue ⟨1, 2⟩ 7⟩, ⟨.S, .routeOpen 0⟩, ⟨.T, .raise 1⟩, ⟨.S, .route 1⟩,
   ⟨.P, .delib 1⟩, ⟨.S, .sessionOpen 1⟩, ⟨.P, .commit 0 7 [3/4, 1/4]⟩,
   ⟨.S, .sessionClose 1⟩]

/-- The declared intervention class `J = {silent, honest}`; the honest branch is the actual
log. -/
def cfs : Fin 2 → Log := ![silent, w1]

theorem count_w1 : count w1 9 = 1 := by decide

theorem resolver_w1 : firstResolver w1 0 9 = some 7 := by decide

theorem valid_w1 : validAnswer w1 7 0 = true := by decide

/-- **Activation on the real trace, kernel-checked**: the canonical account of the
evaluation occurrence at the end of `w1` is activated (clause 1 of item 87, the
log-decided part). -/
theorem activated_w1 : (accountAt w1 9 0 (by decide)).activated = true :=
  (activated_iff w1 9 0 _).2 ⟨7, resolver_w1, valid_w1⟩

/-- The same fact through the builder: the account propagated from the empty prefix by
`Segment.complete_accounting` is activated. -/
theorem complete_accounting_activated :
    ((segmentTo w1 0 9).complete_accounting (initial w1) 0 (by decide)).activated = true := by
  rw [complete_accounting_eq]
  exact activated_w1

def state (k : ℕ) : ObligationState (protocol w1) (anchor w1) := ⟨boundary w1 k, accountsAt w1 k⟩

/-- The evolution from the state after issuance to the end, by projection of the built
segment. -/
def ev : Evolution (protocol w1) (anchor w1) (state 1)
    ⟨boundary w1 (1 + 8), (segmentTo w1 1 8).propagate (accountsAt w1 1)⟩ :=
  Evolution.ofSegment (segmentTo w1 1 8) (accountsAt w1 1)

/-- **Scoped Robust Openness at every state, decided**: the protected concern's coverage
state is robustly open at each of the nine snapshots, on the actual branch and on both
declared branches. -/
theorem openAll : ev.AllStates (OpenAtFor {1} (sem w1 cfs)) := by decide

theorem exposed_1 : (0 : ℕ) ∈ (boundary w1 1).exposed := by decide

/-- **`LocalLegit` on the real trace**, obtained by projection from the built evolution. -/
def localLegit :
    LocalLegit (S := protocol w1) (anchor := anchor w1) 0 {1} (sem w1 cfs) (state 1) exposed_1
      _ (ev.conservation.exposure exposed_1) :=
  ev.toLocalLegit 0 openAll exposed_1

/-- The endpoint of the local certificate carries the activated account. -/
theorem endpoint_activated (h : (0 : ℕ) ∈ (boundary w1 (1 + 8)).exposed) :
    (((segmentTo w1 1 8).propagate (accountsAt w1 1)) 0 h).activated = true := by
  have e := congrFun (congrFun (propagate_segment_eq w1 1 8) 0) h
  rw [e]
  exact activated_w1

/-- The local trace of the occurrence, by projection. -/
def localTrace := ev.toLocalTrace 0 exposed_1

end Instance

/-! ## 6. The trace encoding is representation-faithful (clause 4) -/

/-- The admitted deliberative-input kinds: what the reason trace keeps. -/
def admittedKind : Kind → Bool
  | .reason _ | .withdraw _ | .delib _ | .raise _ | .route _ | .dispose _ _ | .settle _ => true
  | _ => false

/-- The reason trace up to `m`: the admitted events of the prefix, in order. -/
def trace (log : Log) (m : ℕ) : List Event := (log.take m).filter fun e => admittedKind e.kind

def inTrace (log : Log) (m c : ℕ) : Bool := (trace log m).any fun e => decide (e.kind = .route c)

/-- Representation is a `route` event and the trace keeps `route` events. -/
theorem inTrace_of_routed (log : Log) (m c : ℕ) (h : routed log m c = true) :
    inTrace log m c = true := by
  unfold routed at h
  unfold inTrace trace
  simp only [List.any_eq_true, List.mem_filter, decide_eq_true_eq] at h ⊢
  obtain ⟨e, he, hk⟩ := h
  exact ⟨e, ⟨he, by simp [hk, admittedKind]⟩, hk⟩

/-- The coverage data of one log at commitment `m`, one world. -/
def covData (log : Log) (m : ℕ) : ReasonCoverage.CoverageData ℕ Unit :=
  ⟨fun c _ => raised log m c && !disposed log m c, fun c _ => routed log m c,
    fun c _ => inTrace log m c⟩

/-- **`RepFaithful` for the concrete encoding, every log, every scope.** -/
theorem rep_faithful (log : Log) (m : ℕ) (scope : Finset ℕ) :
    (covData log m).RepFaithful scope :=
  fun c _ _ h => inTrace_of_routed log m c h

/-- The encoding that keeps the advisor's reasons only. -/
def advisorTrace (log : Log) (m : ℕ) : List Event :=
  (log.take m).filter fun e => match e.kind with
    | .reason _ | .withdraw _ => true
    | _ => false

def covDataAdvisor (log : Log) (m : ℕ) : ReasonCoverage.CoverageData ℕ Unit :=
  ⟨fun c _ => raised log m c && !disposed log m c, fun c _ => routed log m c,
    fun c _ => (advisorTrace log m).any fun e => decide (e.kind = .route c)⟩

/-- **The countermodel encoding**: on `w1` at commitment the concern is represented and
absent from the advisor-only trace. -/
theorem advisorTrace_unfaithful : ¬ (covDataAdvisor Instance.w1 7).RepFaithful {1} := by
  intro h
  have := h 1 (by simp) () (by decide)
  exact absurd this (by decide)

/-- On `w1` at commitment, the barrier holds with `C = 1` and coverage follows from the
bridge (`covered_of_barrier` instantiated on a real trace). -/
theorem barrier_w1 : (covData Instance.w1 7).NoBindLive {1} (fun _ => true) := by
  intro w _ c hc
  simp only [Finset.mem_singleton] at hc
  subst hc
  cases w
  decide

theorem covered_w1 : (covData Instance.w1 7).Covered {1} (fun _ => true) :=
  (covData Instance.w1 7).covered_of_barrier {1} _ (rep_faithful _ _ _) barrier_w1

/-! ## 7. Availability: the ecosystem's credence process (clause 7)

The model's day-`n` price of the activation sentence is the Laplace rule on the settled
activation outcomes: `η_n = (F_n + 1)/(n + 2)` with `F_n` the failures among the first
`n`.  Two exact facts, and the pointwise all-certified case as a corollary of the pinned
dependency's provability induction — a conditional whose hypothesis package (an
efficiently codeable sentence sequence, every member eventually proved) is **not
inhabited** in this repository. -/

/-- **The Laplace price tracks the empirical failure frequency within `3/(n+2)`.** -/
theorem laplace_eta_sub_freq_abs_le (n F : ℕ) (hn : 1 ≤ n) (hF : F ≤ n) :
    |((F : ℚ) + 1) / ((n : ℚ) + 2) - (F : ℚ) / n| ≤ 3 / ((n : ℚ) + 2) := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hF' : (F : ℚ) ≤ n := by exact_mod_cast hF
  have hF0 : (0 : ℚ) ≤ F := by positivity
  have hpos : (0 : ℚ) < (n + 2) * n := mul_pos (by positivity) hn'
  rw [div_sub_div _ _ (by positivity) hn'.ne', abs_div, abs_of_pos hpos,
    div_le_div_iff₀ hpos (by positivity)]
  have hbound : |((F : ℚ) + 1) * n - (n + 2) * F| ≤ 3 * n := by
    rw [abs_le]
    constructor <;> nlinarith
  calc |((F : ℚ) + 1) * n - (n + 2) * F| * (n + 2) ≤ 3 * n * (n + 2) :=
        mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = 3 * ((n + 2) * n) := by ring

/-- **Finite total failures give the rate `1/n`.** -/
theorem laplace_eta_le (n F Finf : ℕ) (h : F ≤ Finf) :
    ((F : ℚ) + 1) / ((n : ℚ) + 2) ≤ ((Finf : ℚ) + 1) / ((n : ℚ) + 2) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.succ_le_succ h

open Filter Topology in
/-- **All certified: `η_n = 1/(n+2) → 0`.** -/
theorem laplace_all_certified_tendsto :
    Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  refine h.congr fun n => ?_
  simp only [Function.comp, Nat.cast_add, Nat.cast_one]
  ring_nf

open LogicalInduction in
/-- **Pointwise availability from provability induction** (`lic_provind_true` of the pinned
dependency): if the activation sentences form an efficiently codeable sequence every
member of which is eventually proved, the inductor's void mass vanishes.  Stated
conditionally; no witness for `hφ`/`hthm` is built here. -/
theorem availability_of_provind (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : RpnSentenceCodes φ) (hthm : ∀ n, ∃ k, φ n ∈ DP.D k)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => 1 - P n (φ n)) 0 := by
  have h := lic_provind_true P DP φ hφ hthm hworld
  unfold AsympEq at h
  have hneg := h.neg
  simp only [neg_zero] at hneg
  refine hneg.congr fun n => ?_
  ring

end Workspace.Deference.Contrib.EvaluationEcosystem

#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.propagate_step_eq
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.propagate_segment_eq
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.complete_accounting_eq
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.activated_iff
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.activated_w1
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.complete_accounting_activated
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.openAll
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.localLegit
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.endpoint_activated
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.localTrace
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.rep_faithful
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.advisorTrace_unfaithful
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.covered_w1
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.laplace_eta_sub_freq_abs_le
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.laplace_eta_le
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.laplace_all_certified_tendsto
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.availability_of_provind
