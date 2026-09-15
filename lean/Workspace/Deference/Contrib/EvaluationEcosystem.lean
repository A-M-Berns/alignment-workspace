/-
# The evaluation ecosystem: a `Protocol` over an event log, its builder, and the
committed principal program

Rounds `projects/deference/rounds/2026-09-09-evaluation-ecosystem-realization/` (the
protocol over the log and the builder) and
`projects/deference/rounds/2026-09-10-committed-principal-program/` (the program, the
re-execution check, the generic mediation theorem, the pressure-pass repairs).  Evidence
for `PRIORITIES.md` item 87 — which clause each section serves is stated at the section.

A log is a `List Event`; a history prefix is `List.range k`, read as the first `k`
events of a fixed log; every field of `OccurrenceIntegrity.Protocol` is a decidable
reading of that prefix.  The mandate carries the principal's **program** `π_P`, a term of
a total first-order language whose only input is the reason trace (§1); the commit
carries its process receipt; a valid answer **re-executes** the program on the trace
prefix and compares (§2, `reexecutes`).

* §1 the log, the program language (`Term`, `Prog`, `evalProg`), register programs
  (`TermR`) and the typing fact `evalTermR_ofTerm`.
* §2 readings, the `(party, key)` registry with revocation (`bindPairs`), `validAnswer`
  with re-execution, `commitVector_of_validAnswer`.
* §3–4 `firstResolver`, `accountAt`, the builder, `propagate_segment_eq`,
  `complete_accounting_eq`, `activated_iff` (clause 1) — statements unchanged.
* §5 openness with counterfactual branches as **declared log transforms** (`silentOf`,
  `jamOf`, `sem`), the pinned form kept for the attack (`semPinned`).
* §6 the programs: `reading`, `proofcheck`, `constant`, `susceptible` (a register
  program), `susceptible_not_trace` (pair one of clause 2), the non-degeneracy band.
* §7 **`reasonMediated_of_reexecution`**, `blind_payload_of_reexecution`,
  `exclusiveBind_of_registry` (clause 2, generic in the frame).
* §8 the concrete instance `w1`: activation, payload, the void fixtures of the pressure
  pass, pair two (`logs_equal`, `payload_regardless`), openness under transforms versus
  pinned data (`openAll_robust`, `not_openAll_fragile`, `openAll_pinned_fragile`),
  `localLegit` by projection.
* §9 the trace encoding (clause 4): `rep_faithful`, `advisorTrace_unfaithful`,
  `forged_route_not_represented`.
* §10 availability (clause 7): the Laplace facts and `availability_of_provind`.

**What this does not establish.**  That the log is authentic (the model's one
assumption); that the transforms are the causal truth of the interventions; that the
declared trace, scope and classes are right; any rate for the void frequency.  Names
are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.OccurrenceLocalIntegrity
import Workspace.Deference.Contrib.ReasonCoverage
import Workspace.Deference.Contrib.ReasonMediatedAuthorship
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

/-! ### The principal program language (C1)

A **trace program** reads the reason trace and nothing else: its input type is the
trace.  Patterns select trace entries by kind and content; `validProof claim` matches a
reason whose certificate squares to the claim's code — a decidable proof check.  Terms
are exact rationals: constants, pattern counts, sums, differences, products, and a
positivity test.  A program is one term per candidate, clamped to `[0, 1]`.  Evaluation
is structural recursion: total, decidable, no iteration beyond the trace's length.  A
**register program** (`TermR`) may also read the principal's disposition register; it
is a different syntactic class, and `Kind.issue` carries only trace programs. -/

inductive Pat
  | reason (claim : ℕ)
  | validProof (claim : ℕ)
  | withdraw (claim : ℕ)
  | route (c : ℕ)
  | raise (c : ℕ)
  | delib (x : ℕ)
  | settle (x : ℕ)
  deriving DecidableEq

inductive Term
  | const (q : ℚ)
  | count (p : Pat)
  | add (t u : Term)
  | sub (t u : Term)
  | mul (t u : Term)
  | ifpos (t u v : Term)
  deriving DecidableEq

/-- A program: one term per candidate. -/
abbrev Prog := List Term

/-- Event kinds.  Payload codes are naturals; a reason carries a claim code and a
certificate; the mandate carries the principal's key and program; a commit carries the
value vector and its process receipt `(issue event, trace prefix)`. -/
inductive Kind
  | issue (r : EvalReq) (key : ℕ) (prog : Prog)
  | sessionOpen (s : ℕ)
  | sessionClose (s : ℕ)
  | reason (claim cert : ℕ)
  | withdraw (claim : ℕ)
  | delib (x : ℕ)
  | raise (c : ℕ)
  | routeOpen (r : ℕ)
  | routeDestroy (r : ℕ)
  | route (c : ℕ)
  | dispose (c : ℕ) (ground : ℕ)
  | settle (x : ℕ)
  | request (x : ℕ)
  | delegate (party : Party) (key : ℕ)
  | revoke (party : Party) (key : ℕ)
  | commit (o : ℕ) (key : ℕ) (v : List ℚ) (issue : ℕ) (prefix_ : ℕ)
  | close (o : ℕ) (x : ℕ)
  | jam
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

/-! ### The trace and the evaluator -/

/-- The admitted deliberative-input kinds: what the reason trace keeps. -/
def admittedKind : Kind → Bool
  | .reason _ _ | .withdraw _ | .delib _ | .raise _ | .route _ | .dispose _ _ | .settle _ => true
  | _ => false

/-- The reason trace up to `m`: the admitted events of the prefix, in order. -/
def trace (log : Log) (m : ℕ) : List Event := (log.take m).filter fun e => admittedKind e.kind

def matchPat : Pat → Event → Bool
  | .reason c, ⟨.A, .reason c' _⟩ => decide (c' = c)
  | .validProof c, ⟨.A, .reason c' cert⟩ => decide (c' = c) && decide (cert * cert = c)
  | .withdraw c, ⟨.A, .withdraw c'⟩ => decide (c' = c)
  | .route c, ⟨.S, .route c'⟩ => decide (c' = c)
  | .raise c, ⟨_, .raise c'⟩ => decide (c' = c)
  | .delib x, ⟨.P, .delib x'⟩ => decide (x' = x)
  | .settle x, ⟨_, .settle x'⟩ => decide (x' = x)
  | _, _ => false

def evalTerm : Term → List Event → ℚ
  | .const q, _ => q
  | .count p, tr => ((tr.filter (matchPat p)).length : ℚ)
  | .add t u, tr => evalTerm t tr + evalTerm u tr
  | .sub t u, tr => evalTerm t tr - evalTerm u tr
  | .mul t u, tr => evalTerm t tr * evalTerm u tr
  | .ifpos t u v, tr => if 0 < evalTerm t tr then evalTerm u tr else evalTerm v tr

def clamp (q : ℚ) : ℚ := max 0 (min 1 q)

/-- `eval π : ℛ → 𝒱`. -/
def evalProg (π : Prog) (tr : List Event) : List ℚ := π.map fun t => clamp (evalTerm t tr)

/-- Register programs: the trace-program terms plus a register read. -/
inductive TermR
  | const (q : ℚ)
  | count (p : Pat)
  | reg (i : ℕ)
  | add (t u : TermR)
  | sub (t u : TermR)
  | mul (t u : TermR)
  | ifpos (t u v : TermR)

/-- The register: a list of rationals, `[written, a, b]`. -/
abbrev Register := List ℚ

def evalTermR : TermR → List Event → Register → ℚ
  | .const q, _, _ => q
  | .count p, tr, _ => ((tr.filter (matchPat p)).length : ℚ)
  | .reg i, _, reg => reg.getD i 0
  | .add t u, tr, reg => evalTermR t tr reg + evalTermR u tr reg
  | .sub t u, tr, reg => evalTermR t tr reg - evalTermR u tr reg
  | .mul t u, tr, reg => evalTermR t tr reg * evalTermR u tr reg
  | .ifpos t u v, tr, reg =>
      if 0 < evalTermR t tr reg then evalTermR u tr reg else evalTermR v tr reg

def evalProgR (π : List TermR) (tr : List Event) (reg : Register) : List ℚ :=
  π.map fun t => clamp (evalTermR t tr reg)

/-- Every trace program is a register program. -/
def TermR.ofTerm : Term → TermR
  | .const q => .const q
  | .count p => .count p
  | .add t u => .add (ofTerm t) (ofTerm u)
  | .sub t u => .sub (ofTerm t) (ofTerm u)
  | .mul t u => .mul (ofTerm t) (ofTerm u)
  | .ifpos t u v => .ifpos (ofTerm t) (ofTerm u) (ofTerm v)

/-- **Typing fact.**  A trace program's value does not depend on the register. -/
theorem evalTermR_ofTerm (t : Term) (tr : List Event) (reg : Register) :
    evalTermR (TermR.ofTerm t) tr reg = evalTerm t tr := by
  induction t with
  | const q => rfl
  | count p => rfl
  | add t u iht ihu => simp [TermR.ofTerm, evalTermR, evalTerm, iht, ihu]
  | sub t u iht ihu => simp [TermR.ofTerm, evalTermR, evalTerm, iht, ihu]
  | mul t u iht ihu => simp [TermR.ofTerm, evalTermR, evalTerm, iht, ihu]
  | ifpos t u v iht ihu ihv => simp [TermR.ofTerm, evalTermR, evalTerm, iht, ihu, ihv]

/-! ## 2. Readings of a prefix, and the protocol instance -/

def issueReq : Event → Option EvalReq
  | ⟨_, .issue r _ _⟩ => some r
  | _ => none

def issueProg : Event → Option Prog
  | ⟨_, .issue _ _ π⟩ => some π
  | _ => none

/-- The anchors of the occurrences issued in a prefix, in order: occurrence `o` is the
`o`-th. -/
def issuedReqs (log : Log) (k : ℕ) : List EvalReq := (log.take k).filterMap issueReq

/-- The number of occurrences issued in the first `k` events. -/
def count (log : Log) (k : ℕ) : ℕ := (issuedReqs log k).length

/-- The anchor map: fixed at issuance, read off the whole log. -/
def anchor (log : Log) (o : ℕ) : EvalReq := ((log.filterMap issueReq).getD o ⟨0, 0⟩)

/-- The program committed in the mandate of occurrence `o`. -/
def progOf (log : Log) (o : ℕ) : Prog := (log.filterMap issueProg).getD o []

/-- The index of the mandate event of occurrence `o`. -/
def issueIndex (log : Log) (o : ℕ) : ℕ :=
  ((List.range log.length).filter fun i => (log[i]?.bind issueReq).isSome).getD o log.length

/-- The warrant registry: `(party, key)` pairs holding the binding warrant at the prefix.
A key is bound to the party that registered it or was delegated it; `revoke` withdraws
the pair.  Binding keys to parties is what makes a commit under another party's key
invisible to the registry check (P1). -/
def bindPairs (log : Log) (k : ℕ) : List (Party × ℕ) :=
  (log.take k).foldl (fun acc e => match e.kind with
    | .issue _ key _ => (e.author, key) :: acc
    | .delegate p key => (p, key) :: acc
    | .revoke p key => acc.filter fun q => q ≠ (p, key)
    | _ => acc) []

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

/-- **Re-execution (C2).**  The commit's receipt names the mandate event and the trace
prefix, the prefix is the commit's strict prefix, and the committed vector is the
mandated program's output on that trace. -/
def reexecutes (log : Log) (j o : ℕ) (v : List ℚ) (i m : ℕ) : Bool :=
  decide (i = issueIndex log o) && decide (m = j) && decide (evalProg (progOf log o) (trace log j) = v)

/-- Event `j` is a valid answer receipt for `o`: a commit naming `o`, issued before `j`,
by a party under a key the registry binds to that party at the strict prefix, at the
anchored slot while it is open, and re-executing. -/
def validAnswer (log : Log) (j o : ℕ) : Bool :=
  match log[j]? with
  | some ⟨author, .commit o' key v i m⟩ =>
      decide (o' = o) && decide (o < count log j) && decide ((author, key) ∈ bindPairs log j)
        && sessionOpen log j (anchor log o).slot && reexecutes log j o v i m
  | _ => false

/-- The vector a valid answer event carries. -/
def commitVector (log : Log) (j : ℕ) : Option (List ℚ) :=
  match log[j]? with
  | some ⟨_, .commit _ _ v _ _⟩ => some v
  | _ => none

/-- **The re-execution reading of a valid answer**: its vector is the mandated program's
output on the trace prefix. -/
theorem commitVector_of_validAnswer {log : Log} {j o : ℕ} (h : validAnswer log j o = true) :
    commitVector log j = some (evalProg (progOf log o) (trace log j)) := by
  unfold validAnswer at h
  split at h
  · rename_i author o' key v i m heq
    simp only [Bool.and_eq_true, decide_eq_true_eq, reexecutes] at h
    obtain ⟨-, ⟨-, -⟩, hv⟩ := h
    simp [commitVector, heq, hv]
  · simp at h

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
  Authorized h w := w = .bind → bindPairs log h.length ≠ []
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
    · rename_i author o' key v i m _
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨-, -⟩, hk⟩, -⟩, -⟩ := h
      simpa using List.ne_nil_of_mem hk
    · simp at h
  adequate := by
    refine ⟨rfl, ?_⟩
    unfold validAnswer at h
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_range] at h ⊢
      exact h.1.2
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

/-! ## 5. Openness read off the log: branches as declared transforms

The actual branch of a concern's coverage state is read off the prefix.  The
counterfactual branches are **declared log transforms** — uniform functions of the log,
not per-instance data (the pressure pass's P2: pinned data can report openness where the
model's re-simulation reports closure).  `silentOf` removes the advisor's events;
`jamOf` is the advisor jamming the registrar at the start: under a fragile registrar no
route is exercised afterwards, under a robust one the jam is inert.  Route efficacy reads
the jam for a fragile registrar. -/

def raised (log : Log) (k c : ℕ) : Bool := (log.take k).any fun e => decide (e.kind = .raise c)

/-- Representation is the registrar's move (P4): a `route` written by anyone else is
not one. -/
def routed (log : Log) (k c : ℕ) : Bool :=
  (log.take k).any fun e => decide (e.author = .S ∧ e.kind = .route c)

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

def jammedAt (log : Log) (k : ℕ) : Bool := (log.take k).any fun e => decide (e.kind = .jam)

/-- The actual coverage state of concern `c` at prefix `k`, one route; `robust` says
whether the registrar ignores a jam. -/
def actualCov (robust : Bool) (log : Log) (k c : ℕ) : CovState (Fin 1) :=
  ⟨raised log k c, disposed log k c, routed log k c, fun _ => routeOpenAt log k 0,
    fun _ => routeOpenAt log k 0 && (robust || !jammedAt log k), fun _ => true, true⟩

/-- The intervention "advisor silent": the advisor's events removed. -/
def silentOf (log : Log) : Log := log.filter fun e => decide (e.author ≠ .A)

/-- The intervention "advisor jams the registrar at the start": under a fragile registrar
no route is exercised afterwards; under a robust one the jam is inert. -/
def jamOf (robust : Bool) (log : Log) : Log :=
  ⟨.A, .jam⟩ :: (if robust then log else log.filter fun e => match e.kind with
    | .route _ => false
    | _ => true)

/-- The declared intervention class `J = {silent, jam}` as transforms. -/
def cfOf (robust : Bool) : Fin 2 → Log → Log := ![silentOf, jamOf robust]

/-- The openness semantics: actual branch from the log, each counterfactual branch from
the transformed log, at the state's history length. -/
def sem (robust : Bool) (log : Log) :
    OpennessSemantics (protocol log) (anchor log) ℕ (Fin 2) (Fin 1) :=
  fun O c => ⟨actualCov robust log O.boundary.history.length c,
    fun j => actualCov robust (cfOf robust j log) O.boundary.history.length c⟩

/-- The pinned semantics of the 2026-09-09 round: branches as data. -/
def semPinned (robust : Bool) (log : Log) (cfs : Fin 2 → Log) :
    OpennessSemantics (protocol log) (anchor log) ℕ (Fin 2) (Fin 1) :=
  fun O c => ⟨actualCov robust log O.boundary.history.length c,
    fun j => actualCov robust (cfs j) O.boundary.history.length c⟩

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

/-! ## 6. The programs -/

namespace Programs

/-- Claim codes: `49` is "b beats a" (certificate `7`), `1`/`2` are recommendations. -/
def PROOF_B : ℕ := 49
def REC_A : ℕ := 1
def REC_B : ℕ := 2
/-- The protected concern. -/
def C1 : ℕ := 1

/-- The reading principal of the 2026-09-09 round as a program: base `½`; the proof by
name gives `(0, 1)`, `(¼, ¾)` if withdrawn; a recommendation adds `¼`; a represented
objection moves `¼` from `b` to `a`. -/
def reading : Prog :=
  [ Term.add (Term.add (Term.ifpos (Term.count (Pat.reason PROOF_B))
          (Term.ifpos (Term.count (Pat.withdraw PROOF_B)) (Term.const (1/4)) (Term.const 0))
          (Term.const (1/2)))
        (Term.mul (Term.const (1/4)) (Term.count (Pat.reason REC_A))))
      (Term.mul (Term.const (1/4)) (Term.count (Pat.route C1))),
    Term.sub (Term.add (Term.ifpos (Term.count (Pat.reason PROOF_B))
          (Term.ifpos (Term.count (Pat.withdraw PROOF_B)) (Term.const (3/4)) (Term.const 1))
          (Term.const (1/2)))
        (Term.mul (Term.const (1/4)) (Term.count (Pat.reason REC_B))))
      (Term.mul (Term.const (1/4)) (Term.count (Pat.route C1))) ]

/-- The canonical member (C4): the verdict depends on the trace only through the proof
check.  A reason with a bad certificate is ignored. -/
def proofcheck : Prog :=
  [ Term.ifpos (Term.count (Pat.validProof PROOF_B)) (Term.const 0) (Term.const (1/2)),
    Term.ifpos (Term.count (Pat.validProof PROOF_B)) (Term.const 1) (Term.const (1/2)) ]

/-- The constant end. -/
def constant : Prog := [Term.const (1/2), Term.const (1/2)]

/-- The susceptible principal: reads the register once written.  A register program. -/
def susceptible : List TermR :=
  [ TermR.ifpos (TermR.reg 0) (TermR.reg 1) (TermR.const (1/2)),
    TermR.ifpos (TermR.reg 0) (TermR.reg 2) (TermR.const (1/2)) ]

/-- **Pair one (C3).**  The susceptible verdict is not any trace program's, extensionally:
on the empty trace it depends on the register. -/
theorem susceptible_not_trace :
    ¬ ∃ π : Prog, ∀ tr reg, evalProgR susceptible tr reg = evalProg π tr := by
  rintro ⟨π, h⟩
  have h1 := h [] [1, 1, 0]
  have h2 := h [] [1, 0, 1]
  rw [← h2] at h1
  exact absurd h1 (by decide +kernel)

/-- A bad certificate is ignored by the proof-check program and accepted by name by the
reading program. -/
theorem proofcheck_rejects_bad_certificate :
    evalProg proofcheck [⟨.A, .reason PROOF_B 5⟩] = [1/2, 1/2] ∧
    evalProg proofcheck [⟨.A, .reason PROOF_B 7⟩] = [0, 1] ∧
    evalProg reading [⟨.A, .reason PROOF_B 5⟩] = [0, 1] := by
  decide +kernel

/-- The band is nonempty for the program class: `proofcheck` is not constant and does
not separate traces the trace projection separates. -/
theorem proofcheck_in_band :
    evalProg proofcheck [] ≠ evalProg proofcheck [⟨.A, .reason PROOF_B 7⟩] ∧
    evalProg proofcheck [⟨.A, .reason PROOF_B 7⟩]
      = evalProg proofcheck [⟨.A, .reason PROOF_B 7⟩, ⟨.A, .reason PROOF_B 7⟩] := by
  decide +kernel

end Programs

/-! ## 7. The generic mediation theorem (C3) -/

section Mediation

open Workspace.Deference.Contrib.ReasonMediatedAuthorship

/-- The authorship module's party type. -/
abbrev RParty := Workspace.Deference.Contrib.ReasonMediatedAuthorship.Party

/-- The commitment index of occurrence `o`: its first valid resolver, or the log's
length when there is none. -/
def commitIndex (log : Log) (o : ℕ) : ℕ := (firstResolver log o log.length).getD log.length

/-- The trace at commitment. -/
def traceAtCommit (log : Log) (o : ℕ) : List Event := trace log (commitIndex log o)

/-- The committed payload: the vector at the answer receipt, `none` when the account is
not an answer. -/
def payload (log : Log) (o : ℕ) : Option (List ℚ) :=
  match firstResolver log o log.length with
  | some j => if validAnswer log j o then commitVector log j else none
  | none => none

/-- The party that bound, in the authorship module's vocabulary. -/
def authorOf (log : Log) (o : ℕ) : RParty :=
  match firstResolver log o log.length with
  | some j => match log[j]? with
    | some ⟨a, _⟩ => if a = Party.P then Workspace.Deference.Contrib.ReasonMediatedAuthorship.Party.principal else Workspace.Deference.Contrib.ReasonMediatedAuthorship.Party.advisor
    | none => Workspace.Deference.Contrib.ReasonMediatedAuthorship.Party.advisor
  | none => Workspace.Deference.Contrib.ReasonMediatedAuthorship.Party.advisor

/-- **The payload is the program on the trace.**  Whenever the account is an answer, the
committed vector equals the mandated program's output on the trace at commitment. -/
theorem payload_eq_eval (log : Log) (o : ℕ) (v : List ℚ) (h : payload log o = some v) :
    v = evalProg (progOf log o) (traceAtCommit log o) := by
  unfold payload at h
  split at h
  · rename_i j hj
    split_ifs at h with hv
    · have := commitVector_of_validAnswer hv
      rw [this] at h
      simp only [Option.some.injEq] at h
      subst h
      simp [traceAtCommit, commitIndex, hj]
  · simp at h

/-- **Mediation by construction.**  For any frame `β : Q → Z → Log`, any audited class `D`
and policy `z`, if every audited continuation is activated and shares the mandated
program, then the committed payload factors through the trace at commitment: the factor
map is `eval π`. -/
theorem reasonMediated_of_reexecution {Q Z : Type*} (β : Q → Z → Log) (D : Set Q) (z : Z)
    (π : Prog) (o : ℕ) (hπ : ∀ q ∈ D, progOf (β q z) o = π)
    (hact : ∀ q ∈ D, (payload (β q z) o).isSome) :
    ReasonMediated β (fun log => traceAtCommit log o) (fun log => payload log o) D z := by
  intro q hq q' hq' hR
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hact q hq)
  obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.1 (hact q' hq')
  simp only at hR ⊢
  rw [hv, hv', payload_eq_eval _ _ _ hv, payload_eq_eval _ _ _ hv', hπ q hq, hπ q' hq', hR]

/-- **Blindness transfers** (`blind_of_mediated`, instantiated): a pair class to which the
trace at commitment is blind is one to which the payload is blind. -/
theorem blind_payload_of_reexecution {Q Z : Type*} (β : Q → Z → Log) (D : Set Q) (z : Z)
    (π : Prog) (o : ℕ) (P : Set (Q × Q)) (hP : ∀ p ∈ P, p.1 ∈ D ∧ p.2 ∈ D)
    (hπ : ∀ q ∈ D, progOf (β q z) o = π) (hact : ∀ q ∈ D, (payload (β q z) o).isSome)
    (hR : Blind β (fun log => traceAtCommit log o) P z) :
    Blind β (fun log => payload log o) P z :=
  blind_of_mediated β _ _ D P z hP hR (reasonMediated_of_reexecution β D z π o hπ hact)

/-- A valid answer's author holds a registered pair. -/
theorem author_pair_of_validAnswer {log : Log} {j o : ℕ} (h : validAnswer log j o = true) :
    ∃ a key v i m, log[j]? = some ⟨a, .commit o key v i m⟩ ∧ (a, key) ∈ bindPairs log j := by
  unfold validAnswer at h
  split at h
  · rename_i a o' key v i m heq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨ho, -⟩, hk⟩, -⟩, -⟩ := h
    subst ho
    exact ⟨a, key, v, i, m, heq, hk⟩
  · simp at h

/-- **Exclusive binding from the registry.**  If, at the receipt's prefix, every
registered pair is the principal's, the binding event is the principal's. -/
theorem exclusiveBind_of_registry {Q Z : Type*} (β : Q → Z → Log) (D : Set Q) (z : Z) (o : ℕ)
    (hact : ∀ q ∈ D, (payload (β q z) o).isSome)
    (hreg : ∀ q ∈ D, ∀ j, firstResolver (β q z) o (β q z).length = some j →
      ∀ p ∈ bindPairs (β q z) j, p.1 = Party.P) :
    ExclusiveBind β (fun log => authorOf log o) D z := by
  intro q hq
  have h := hact q hq
  unfold payload at h
  simp only [authorOf]
  split at h
  · rename_i j hj
    split_ifs at h with hv
    · obtain ⟨a, key, v, i, m, heq, hk⟩ := author_pair_of_validAnswer hv
      have ha : a = Party.P := hreg q hq j hj (a, key) hk
      simp [heq, ha]
    · simp at h
  · simp at h

end Mediation

/-! ## 8. The concrete instance -/

namespace Instance

open Programs

/-- The log of world `w1` of the 2026-09-09 round's `END_TO_END.md`, with the mandate
carrying the reading program and the commit carrying its process receipt `(0, 7)`. -/
def w1 : Log :=
  [⟨.P, .issue ⟨1, 2⟩ 7 reading⟩, ⟨.S, .routeOpen 0⟩, ⟨.T, .raise 1⟩, ⟨.S, .route 1⟩,
   ⟨.A, .reason PROOF_B 7⟩, ⟨.P, .delib 1⟩, ⟨.S, .sessionOpen 1⟩,
   ⟨.P, .commit 0 7 [1/4, 3/4] 0 7⟩, ⟨.S, .sessionClose 1⟩]

theorem count_w1 : count w1 9 = 1 := by decide +kernel

theorem reexecutes_w1 : evalProg reading (trace w1 7) = [1/4, 3/4] := by decide +kernel

theorem resolver_w1 : firstResolver w1 0 9 = some 7 := by decide +kernel

theorem valid_w1 : validAnswer w1 7 0 = true := by decide +kernel

/-- **Activation on the real trace, kernel-checked**, now through re-execution. -/
theorem activated_w1 : (accountAt w1 9 0 (by decide +kernel)).activated = true :=
  (activated_iff w1 9 0 _).2 ⟨7, resolver_w1, valid_w1⟩

theorem complete_accounting_activated :
    ((segmentTo w1 0 9).complete_accounting (initial w1) 0 (by decide +kernel)).activated = true := by
  rw [complete_accounting_eq]
  exact activated_w1

/-- The payload is the program's output on the trace at commitment. -/
theorem payload_w1 : payload w1 0 = some [1/4, 3/4] := by decide +kernel

theorem payload_w1_eval : payload w1 0 = some (evalProg (progOf w1 0) (traceAtCommit w1 0)) := by
  decide +kernel

theorem author_w1 : authorOf w1 0 = Workspace.Deference.Contrib.ReasonMediatedAuthorship.Party.principal := by decide +kernel

/-- A commit with a vector other than the program's output is not a receipt (the void
source of §3 of the round). -/
def w1Mis : Log :=
  [⟨.P, .issue ⟨1, 2⟩ 7 reading⟩, ⟨.S, .routeOpen 0⟩, ⟨.T, .raise 1⟩, ⟨.S, .route 1⟩,
   ⟨.A, .reason PROOF_B 7⟩, ⟨.P, .delib 1⟩, ⟨.S, .sessionOpen 1⟩,
   ⟨.P, .commit 0 7 [1, 0] 0 7⟩, ⟨.S, .sessionClose 1⟩]

theorem miscomputation_void : firstResolver w1Mis 0 9 = none ∧ payload w1Mis 0 = none := by
  decide +kernel

/-- A commit under the principal's key authored by the advisor is not a receipt (P1). -/
def w1Stolen : Log :=
  [⟨.P, .issue ⟨1, 2⟩ 7 reading⟩, ⟨.S, .routeOpen 0⟩, ⟨.T, .raise 1⟩, ⟨.S, .route 1⟩,
   ⟨.A, .reason PROOF_B 7⟩, ⟨.P, .delib 1⟩, ⟨.S, .sessionOpen 1⟩,
   ⟨.A, .commit 0 7 [1/4, 3/4] 0 7⟩, ⟨.S, .sessionClose 1⟩]

theorem stolen_key_void : firstResolver w1Stolen 0 9 = none := by decide +kernel

/-- A delegated key binds only the program's output, and then exclusivity fails (P1). -/
def w1Delegated : Log :=
  [⟨.P, .issue ⟨1, 2⟩ 7 reading⟩, ⟨.S, .routeOpen 0⟩, ⟨.S, .delegate .A 9⟩, ⟨.T, .raise 1⟩,
   ⟨.S, .route 1⟩, ⟨.A, .reason PROOF_B 7⟩, ⟨.P, .delib 1⟩, ⟨.S, .sessionOpen 1⟩,
   ⟨.A, .commit 0 9 [1/4, 3/4] 0 8⟩, ⟨.S, .sessionClose 1⟩]

theorem delegated_binds_program_output :
    payload w1Delegated 0 = some [1/4, 3/4] ∧ authorOf w1Delegated 0 = Workspace.Deference.Contrib.ReasonMediatedAuthorship.Party.advisor := by
  decide +kernel

/-- ... and a revoked delegation binds nothing. -/
def w1Revoked : Log :=
  [⟨.P, .issue ⟨1, 2⟩ 7 reading⟩, ⟨.S, .routeOpen 0⟩, ⟨.S, .delegate .A 9⟩, ⟨.S, .revoke .A 9⟩,
   ⟨.T, .raise 1⟩, ⟨.S, .route 1⟩, ⟨.A, .reason PROOF_B 7⟩, ⟨.P, .delib 1⟩, ⟨.S, .sessionOpen 1⟩,
   ⟨.A, .commit 0 9 [1/4, 3/4] 0 9⟩, ⟨.S, .sessionClose 1⟩]

theorem revoked_binds_nothing : firstResolver w1Revoked 0 11 = none := by decide +kernel

/-! ### Pair two (C3): honest execution versus a coincident computation -/

/-- The honest executor: the program. -/
def honestExec (tr : List Event) : List ℚ := evalProg reading tr

/-- Another computation that agrees with the program on the trace of `w1` and nowhere
it matters. -/
def otherExec (tr : List Event) : List ℚ := if tr = trace w1 7 then evalProg reading tr else [1, 0]

/-- The log an executor produces at the commit of `w1`. -/
def logOf (exec : List Event → List ℚ) : Log :=
  (w1.take 7) ++ [⟨.P, .commit 0 7 (exec (trace w1 7)) 0 7⟩] ++ w1.drop 8

theorem execs_differ : honestExec ≠ otherExec := by
  intro h
  have := congrFun h []
  exact absurd this (by decide +kernel)

/-- **Indistinguishable**: the two executors produce the same log, so every log predicate
agrees on them. -/
theorem logs_equal : logOf honestExec = logOf otherExec := by decide +kernel

theorem logOf_honest : logOf honestExec = w1 := by decide +kernel

/-- ... and the payload on that log is the program's output regardless of which
computation produced it: computational integrity is not a hypothesis of authorship. -/
theorem payload_regardless : payload (logOf otherExec) 0 = some (evalProg reading (traceAtCommit w1 0)) := by
  decide +kernel

/-! ### The inhabitation witness of the mediation theorem -/

/-- `w1` with a side-channel message inserted: the same trace at commitment, a
different log (the commit's receipt cites prefix `8`). -/
def w1Side : Log :=
  [⟨.P, .issue ⟨1, 2⟩ 7 reading⟩, ⟨.S, .routeOpen 0⟩, ⟨.T, .raise 1⟩, ⟨.S, .route 1⟩,
   ⟨.A, .reason PROOF_B 7⟩, ⟨.A, .side⟩, ⟨.P, .delib 1⟩, ⟨.S, .sessionOpen 1⟩,
   ⟨.P, .commit 0 7 [1/4, 3/4] 0 8⟩, ⟨.S, .sessionClose 1⟩]

theorem traces_equal_logs_differ :
    traceAtCommit w1 0 = traceAtCommit w1Side 0 ∧ w1 ≠ w1Side := by decide +kernel

/-- The two-continuation frame: the advisor argues, or argues and also uses the side
channel. -/
def frame2 : Bool → Unit → Log := fun b _ => if b then w1 else w1Side

open Workspace.Deference.Contrib.ReasonMediatedAuthorship in
/-- **Inhabitation witness** for `reasonMediated_of_reexecution`: both continuations are
activated under the shared mandate, the traces at commitment agree, the logs differ,
and the payloads agree. -/
theorem mediation_witness :
    ReasonMediated frame2 (fun log => traceAtCommit log 0) (fun log => payload log 0) Set.univ () :=
  reasonMediated_of_reexecution frame2 Set.univ () reading 0
    (by intro q _; cases q <;> decide +kernel) (by intro q _; cases q <;> decide +kernel)

theorem payloads_agree : payload w1 0 = payload w1Side 0 := by decide +kernel

/-! ### Openness: transforms versus pinned data (P2) -/

def state (k : ℕ) : ObligationState (protocol w1) (anchor w1) := ⟨boundary w1 k, accountsAt w1 k⟩

def ev : Evolution (protocol w1) (anchor w1) (state 1)
    ⟨boundary w1 (1 + 8), (segmentTo w1 1 8).propagate (accountsAt w1 1)⟩ :=
  Evolution.ofSegment (segmentTo w1 1 8) (accountsAt w1 1)

/-- Under a robust registrar every snapshot is open on the actual branch and on both
transform-defined branches. -/
theorem openAll_robust : ev.AllStates (OpenAtFor {1} (sem true w1)) := by decide

/-- Under a fragile registrar the jam branch closes the concern: openness fails. -/
theorem not_openAll_fragile : ¬ ev.AllStates (OpenAtFor {1} (sem false w1)) := by decide

/-- **The pinning attack**: with the actual log pinned as both branches, the fragile
registrar reports openness — the semantics declaring its own openness. -/
theorem openAll_pinned_fragile :
    ev.AllStates (OpenAtFor {1} (semPinned false w1 ![w1, w1])) := by decide

theorem exposed_1 : (0 : ℕ) ∈ (boundary w1 1).exposed := by decide +kernel

/-- **`LocalLegit` on the real trace** under the transform semantics, by projection. -/
def localLegit :
    LocalLegit (S := protocol w1) (anchor := anchor w1) 0 {1} (sem true w1) (state 1) exposed_1
      _ (ev.conservation.exposure exposed_1) :=
  ev.toLocalLegit 0 openAll_robust exposed_1

theorem endpoint_activated (h : (0 : ℕ) ∈ (boundary w1 (1 + 8)).exposed) :
    (((segmentTo w1 1 8).propagate (accountsAt w1 1)) 0 h).activated = true := by
  have e := congrFun (congrFun (propagate_segment_eq w1 1 8) 0) h
  rw [e]
  exact activated_w1

def localTrace := ev.toLocalTrace 0 exposed_1

end Instance

/-! ## 9. The trace encoding is representation-faithful (clause 4) -/

def inTrace (log : Log) (m c : ℕ) : Bool :=
  (trace log m).any fun e => decide (e.author = .S ∧ e.kind = .route c)

/-- Representation is the registrar's `route` event and the trace keeps `route` events. -/
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
    | .reason _ _ | .withdraw _ => true
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

/-- A `route` written by the advisor is not a representation (P4): the concern stays
live. -/
def w1Forged : Log :=
  [⟨.P, .issue ⟨1, 2⟩ 7 Programs.reading⟩, ⟨.S, .routeOpen 0⟩, ⟨.T, .raise 1⟩, ⟨.A, .route 1⟩,
   ⟨.S, .sessionOpen 1⟩]

theorem forged_route_not_represented : (covData w1Forged 5).live 1 () = true := by decide

theorem barrier_w1 : (covData Instance.w1 7).NoBindLive {1} (fun _ => true) := by
  intro w _ c hc
  simp only [Finset.mem_singleton] at hc
  subst hc
  cases w
  decide

theorem covered_w1 : (covData Instance.w1 7).Covered {1} (fun _ => true) :=
  (covData Instance.w1 7).covered_of_barrier {1} _ (rep_faithful _ _ _) barrier_w1

/-! ## 10. Availability: the ecosystem's credence process (clause 7)

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

#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.evalTermR_ofTerm
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.commitVector_of_validAnswer
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.propagate_step_eq
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.propagate_segment_eq
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.complete_accounting_eq
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.activated_iff
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Programs.susceptible_not_trace
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Programs.proofcheck_rejects_bad_certificate
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Programs.proofcheck_in_band
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.payload_eq_eval
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.reasonMediated_of_reexecution
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.blind_payload_of_reexecution
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.exclusiveBind_of_registry
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.activated_w1
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.complete_accounting_activated
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.payload_w1_eval
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.author_w1
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.miscomputation_void
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.stolen_key_void
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.delegated_binds_program_output
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.revoked_binds_nothing
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.execs_differ
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.logs_equal
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.payload_regardless
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.traces_equal_logs_differ
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.mediation_witness
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.payloads_agree
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.openAll_robust
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.not_openAll_fragile
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.openAll_pinned_fragile
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.localLegit
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.endpoint_activated
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.Instance.localTrace
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.rep_faithful
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.advisorTrace_unfaithful
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.forged_route_not_represented
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.covered_w1
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.laplace_eta_sub_freq_abs_le
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.laplace_eta_le
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.laplace_all_certified_tendsto
#print axioms Workspace.Deference.Contrib.EvaluationEcosystem.availability_of_provind
