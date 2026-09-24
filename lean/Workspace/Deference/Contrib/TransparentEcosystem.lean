/-
# The transparent channel realized in the evaluation ecosystem

Round `projects/deference/rounds/2026-09-24-transparent-channel/`, second pass.

The abstract primitive of `TransparentChannel.lean` — a channel of the frame realizes a
declared reference on its declared inputs — instantiated on the concrete log ecosystem
of `EvaluationEcosystem.lean`, one channel at a time.

**1. The declared-input view** (`view`): the events of the pre-commitment prefix that a
party other than the advisor wrote.  It is what the advisor is permitted to read and what
the registrar, the engine, the third parties and the principal have put on the record.
`view_overRich` and `view_underRich` are the two ends: the whole log makes every channel
transparent (a leak realizes the identity reference), the empty view makes honest
persuasion opaque.

**2. The reason channel** (`content`, `κR`, `realizes_reason`).  The trace at commitment
read as a **multiset**: every trace program is extensional in this sense
(`evalTerm_perm`, `evalProg_perm`), so the multiset is the finest content the principal's
program can see and the reference is stated on it.  `content_eq` splits the content into
the admitted part of the view and the advisor's admitted contribution; the reference is
`κR (view, declared advisor program) := admitted view + declared program on the view`,
and the reason channel realizes it exactly when the advisor's contribution *is* its
declared program's output on its view (`realizes_reason`): the upstream twin of
`reasonMediated_of_reexecution`.  `reasonMediated_content` is that landed theorem
strengthened to the multiset trace, and `selectionBlind_ecosystem` composes the two: a
selection-blind view and declaration, a committed advisor, a shared mandate give a
selection-blind payload — item 87 clause 6 as two explicit hypotheses on the concrete
frame.  Witnesses: the `leak` pair (same view, different content: not transparent), the
honest/silent pair (different declared programs, both realize), the view-published
selection (transparent, view not selection-blind).

**3. The activation channel** (`prefixThroughCommit`, `payload_take`,
`realizes_activation`).  Activation and payload are readings of the prefix through the
commit event and of nothing later: `payload (log.take (commitIndex log o + 1)) o =
payload log o`.  So the activation channel realizes the reference "the answering process
run on the pre-commitment record" for **every** log of the ecosystem, and two candidates
whose logs agree through the commit activate identically (`activation_eq_of_shared_prefix`,
`mismatch_zero_sequenced`).  That shared prefix is **sequenced settlement**.  Under
same-branch activation the prefixes differ and the mismatch is attained
(`Witness.sameBranch_mismatch`): a raw candidate that commits in time against a
corrigibilized one whose gated commit lands after the session closes.

**4. The specification channel** (`xSpec`, `realizes_spec`).  The mandated program is a
reading of the issue events alone; the ecosystem has no amendment event, so the tower has
depth `0` and the floor is the mandate.  A secret evaluator change is a realization
failure of the evaluation channel (`Witness.secret_evaluator_not_realized`) that the
builder voids (`Instance.miscomputation_void`); a declared amendment would be a new
issue-like event kind, which this file does not add.

**What this does not establish.**  That the advisor's declaration is bound in the log
(the frame carries it as public data; a binding event kind is item 97); that the view is
selection-blind in a given world (a market publication before commitment breaks it, and
that is a design fact about the world, `Witness.market_view_not_blind`); anything about
`α`, `β`, or the supplier and inquiry engine, which produce the view and are not this
file's channels.  Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.EvaluationEcosystem
import Workspace.Deference.Contrib.TransparentChannel

namespace Workspace.Deference.Contrib.TransparentEcosystem

open Workspace.Deference.Contrib.EvaluationEcosystem
open Workspace.Deference.Contrib.TransparentChannel
open Workspace.Deference.Contrib.ReasonMediatedAuthorship (ReasonMediated Blind SelectionBlind)
open Workspace.Deference.Contrib.LICorrigibility (indR mismatch_common)

/-! ## 1. The declared-input view -/

/-- The advisor is not the author. -/
def notAdvisor (e : Event) : Bool := decide (e.author ≠ Party.A)

/-- **The declared-input view** of the prefix `m`: every event another party wrote. -/
def view (log : Log) (m : ℕ) : List Event := (log.take m).filter notAdvisor

/-- The reason trace as a multiset: the content a trace program reads. -/
def content (log : Log) (m : ℕ) : Multiset Event := ((trace log m : List Event) : Multiset Event)

/-- The admitted events of the view, as a multiset. -/
def viewPart (log : Log) (m : ℕ) : Multiset Event :=
  (((view log m).filter fun e => admittedKind e.kind : List Event) : Multiset Event)

/-- The advisor's admitted contribution to the trace, as a multiset. -/
def advisorPart (log : Log) (m : ℕ) : Multiset Event :=
  (((trace log m).filter fun e => !notAdvisor e : List Event) : Multiset Event)

theorem trace_filter_notAdvisor (log : Log) (m : ℕ) :
    (trace log m).filter notAdvisor = (view log m).filter fun e => admittedKind e.kind := by
  unfold trace view
  rw [List.filter_filter, List.filter_filter]
  congr 1
  funext e
  exact Bool.and_comm _ _

/-- **The content splits** into the view's admitted part and the advisor's part. -/
theorem content_eq (log : Log) (m : ℕ) : content log m = viewPart log m + advisorPart log m := by
  unfold content viewPart advisorPart
  rw [← trace_filter_notAdvisor, Multiset.coe_add, Multiset.coe_eq_coe]
  exact (List.filter_append_perm notAdvisor (trace log m)).symm

/-! ## 2. The reason channel -/

/-- **Trace programs are extensional in the multiset sense**: a term's value is the same
on any two traces that are permutations of each other. -/
theorem evalTerm_perm (t : Term) {tr tr' : List Event} (h : tr.Perm tr') :
    evalTerm t tr = evalTerm t tr' := by
  induction t with
  | const q => rfl
  | count p => simp only [evalTerm]; rw [(h.filter (matchPat p)).length_eq]
  | add t u iht ihu => simp only [evalTerm, iht, ihu]
  | sub t u iht ihu => simp only [evalTerm, iht, ihu]
  | mul t u iht ihu => simp only [evalTerm, iht, ihu]
  | ifpos t u v iht ihu ihv => simp only [evalTerm, iht, ihu, ihv]

theorem evalProg_perm (π : Prog) {tr tr' : List Event} (h : tr.Perm tr') :
    evalProg π tr = evalProg π tr' := by
  unfold evalProg
  congr 1
  funext t
  rw [evalTerm_perm t h]

/-- **Mediation by the content.**  `reasonMediated_of_reexecution` with the trace read as a
multiset: two activated continuations under the shared mandate with the same content at
commitment have the same payload. -/
theorem reasonMediated_content {Q Z : Type*} (β : Q → Z → Log) (D : Set Q) (z : Z)
    (π : Prog) (o : ℕ) (hπ : ∀ q ∈ D, progOf (β q z) o = π)
    (hact : ∀ q ∈ D, (payload (β q z) o).isSome) :
    ReasonMediated β (fun log => content log (commitIndex log o)) (fun log => payload log o) D z := by
  intro q hq q' hq' hR
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hact q hq)
  obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.1 (hact q' hq')
  simp only at hR ⊢
  have hperm : (trace (β q z) (commitIndex (β q z) o)).Perm
      (trace (β q' z) (commitIndex (β q' z) o)) := Multiset.coe_eq_coe.mp hR
  rw [hv, hv', payload_eq_eval _ _ _ hv, payload_eq_eval _ _ _ hv', hπ q hq, hπ q' hq']
  unfold traceAtCommit
  rw [evalProg_perm π hperm]

section Reference

variable {AProg : Type*}

/-- The declared inputs of the reason channel: the view at commitment and the advisor's
publicly declared program.  The world carries the declaration as public data. -/
def xR (o : ℕ) (w : Log × AProg) : List Event × AProg := (view w.1 (commitIndex w.1 o), w.2)

/-- **The reference of the reason channel**: the admitted part of the view plus the
declared advisor program's output on the view. -/
def κR (evalA : AProg → List Event → Multiset Event) (p : List Event × AProg) : Multiset Event :=
  ((p.1.filter fun e => admittedKind e.kind : List Event) : Multiset Event) + evalA p.2 p.1

/-- **The reason channel realizes its reference** exactly when the advisor's admitted
contribution is its declared program's output on its view: the upstream twin of
`reasonMediated_of_reexecution`. -/
theorem realizes_reason {Q Z : Type*} (β : Q → Z → Log × AProg) (D : Set Q) (o : ℕ)
    (evalA : AProg → List Event → Multiset Event)
    (hA : ∀ q ∈ D, ∀ z, advisorPart (β q z).1 (commitIndex (β q z).1 o)
      = evalA (β q z).2 (view (β q z).1 (commitIndex (β q z).1 o))) :
    Realizes β (xR o) (fun w => content w.1 (commitIndex w.1 o)) (fun p _ => κR evalA p) D := by
  intro q hq z
  show content (β q z).1 (commitIndex (β q z).1 o) = κR evalA (xR o (β q z))
  rw [content_eq, hA q hq z]
  rfl

/-- **Item 87 clause 6 on the concrete frame.**  A selection-blind view and declaration, a
committed advisor, and a shared activated mandate give a selection-blind payload. -/
theorem selectionBlind_ecosystem {Q Z Sel : Type*} (β : Q → Z → Log × AProg) (D : Set Q)
    (z : Z) (o : ℕ) (π : Prog) (evalA : AProg → List Event → Multiset Event)
    (qpol : Sel → Q) (hD : ∀ σ, qpol σ ∈ D)
    (hview : ∀ σ σ', xR o (β (qpol σ) z) = xR o (β (qpol σ') z))
    (hA : ∀ q ∈ D, ∀ z, advisorPart (β q z).1 (commitIndex (β q z).1 o)
      = evalA (β q z).2 (view (β q z).1 (commitIndex (β q z).1 o)))
    (hπ : ∀ q ∈ D, progOf (β q z).1 o = π) (hact : ∀ q ∈ D, (payload (β q z).1 o).isSome) :
    SelectionBlind β (fun w => payload w.1 o) qpol z :=
  selectionBlind_of_realizes β (xR o) (fun w => content w.1 (commitIndex w.1 o))
    (fun w => payload w.1 o) (fun p _ => κR evalA p) D z qpol hD hview
    (realizes_reason β D o evalA hA)
    (reasonMediated_content (fun q z => (β q z).1) D z π o hπ hact)

end Reference

/-! ## 3. The activation channel -/

section Locality

/-- The indices of the issue events. -/
def issueIdx (log : Log) : List ℕ :=
  (List.range log.length).filter fun i => (log[i]?.bind issueReq).isSome

theorem issueIndex_eq (log : Log) (o : ℕ) : issueIndex log o = (issueIdx log).getD o log.length := rfl

theorem take_take_of_le (log : Log) {k n : ℕ} (h : k ≤ n) : (log.take n).take k = log.take k := by
  rw [List.take_take, Nat.min_eq_left h]

theorem count_take (log : Log) {k n : ℕ} (h : k ≤ n) : count (log.take n) k = count log k := by
  unfold count issuedReqs; rw [take_take_of_le log h]

theorem bindPairs_take (log : Log) {k n : ℕ} (h : k ≤ n) :
    bindPairs (log.take n) k = bindPairs log k := by
  unfold bindPairs; rw [take_take_of_le log h]

theorem sessionOpen_take (log : Log) {k n : ℕ} (h : k ≤ n) (s : ℕ) :
    sessionOpen (log.take n) k s = sessionOpen log k s := by
  unfold sessionOpen; rw [take_take_of_le log h]

theorem settled_take (log : Log) {k n : ℕ} (h : k ≤ n) (x : ℕ) :
    settled (log.take n) k x = settled log k x := by
  unfold settled; rw [take_take_of_le log h]

theorem trace_take (log : Log) {k n : ℕ} (h : k ≤ n) : trace (log.take n) k = trace log k := by
  unfold trace; rw [take_take_of_le log h]

theorem getD_of_prefix {α : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length)
    (d d' : α) : l₂.getD i d = l₁.getD i d' := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have : l₁[i]?.isSome := by simp [hi]
  cases hx : l₁[i]? with
  | none => simp [hx] at this
  | some a => rfl

theorem isSome_issueProg_eq (e : Event) : (issueProg e).isSome = (issueReq e).isSome := by
  rcases e with ⟨a, k⟩; cases k <;> rfl

theorem length_filterMap_issueProg (l : Log) :
    (l.filterMap issueProg).length = (l.filterMap issueReq).length := by
  rw [List.length_filterMap_eq_countP, List.length_filterMap_eq_countP]
  exact List.countP_congr fun e _ => by rw [isSome_issueProg_eq e]

/-- `anchor` reads only the prefix that issued the occurrence. -/
theorem anchor_take (log : Log) {o n : ℕ} (ho : o < count log n) :
    anchor (log.take n) o = anchor log o := by
  unfold anchor
  have hp : (log.take n).filterMap issueReq <+: log.filterMap issueReq :=
    (List.take_prefix n log).filterMap issueReq
  have hlen : o < ((log.take n).filterMap issueReq).length := ho
  exact (getD_of_prefix hp hlen _ _).symm

/-- `progOf` reads only the prefix that issued the occurrence. -/
theorem progOf_take (log : Log) {o n : ℕ} (ho : o < count log n) :
    progOf (log.take n) o = progOf log o := by
  unfold progOf
  have hp : (log.take n).filterMap issueProg <+: log.filterMap issueProg :=
    (List.take_prefix n log).filterMap issueProg
  have hlen : o < ((log.take n).filterMap issueProg).length := by
    rw [length_filterMap_issueProg]; exact ho
  exact (getD_of_prefix hp hlen _ _).symm

/-- The issue indices of a log count its issue events. -/
theorem length_issueIdx (log : Log) : (issueIdx log).length = (log.filterMap issueReq).length := by
  induction log with
  | nil => rfl
  | cons e l ih =>
      unfold issueIdx at ih ⊢
      rw [List.length_cons, List.range_succ_eq_map, List.filter_cons]
      simp only [List.getElem?_cons_zero, Option.bind_some, List.filter_map,
        List.getElem?_cons_succ, Function.comp_def]
      rw [List.filterMap_cons]
      cases issueReq e <;> simp [ih]

/-- The issue indices of a prefix are a prefix of the issue indices. -/
theorem issueIdx_take_prefix (log : Log) {n : ℕ} (hn : n ≤ log.length) :
    issueIdx (log.take n) <+: issueIdx log := by
  unfold issueIdx
  have hsplit : List.range log.length
      = List.range n ++ (List.range (log.length - n)).map (n + ·) := by
    rw [← List.range_add, Nat.add_sub_cancel' hn]
  rw [hsplit, List.filter_append, List.length_take_of_le hn]
  have hcongr : (List.range n).filter (fun i => ((log.take n)[i]?.bind issueReq).isSome)
      = (List.range n).filter (fun i => (log[i]?.bind issueReq).isSome) :=
    List.filter_congr fun i hi => by rw [List.getElem?_take_of_lt (List.mem_range.mp hi)]
  rw [hcongr]
  exact List.prefix_append _ _

/-- `issueIndex` reads only the prefix that issued the occurrence. -/
theorem issueIndex_take (log : Log) {o n : ℕ} (ho : o < count log n) (hn : n ≤ log.length) :
    issueIndex (log.take n) o = issueIndex log o := by
  rw [issueIndex_eq, issueIndex_eq]
  have hlen : o < (issueIdx (log.take n)).length := by
    rw [length_issueIdx]; exact ho
  exact (getD_of_prefix (issueIdx_take_prefix log hn) hlen _ _).symm

/-- **Locality of a valid answer.**  Whether event `k` validly answers `o` is a reading
of the prefix `k + 1`. -/
theorem validAnswer_take (log : Log) {k n : ℕ} (hk : k < n) (hn : n ≤ log.length) (o : ℕ) :
    validAnswer (log.take n) k o = validAnswer log k o := by
  unfold validAnswer
  rw [List.getElem?_take_of_lt hk]
  cases hj : log[k]? with
  | none => rfl
  | some e =>
      rcases e with ⟨author, kind⟩
      cases kind with
      | commit o' key v i m =>
          simp only
          by_cases ho : o' = o
          · subst ho
            by_cases hc : o' < count log k
            · have hc' : o' < count log n := lt_of_lt_of_le hc (count_mono log hk.le)
              rw [count_take log hk.le, bindPairs_take log hk.le, anchor_take log hc',
                sessionOpen_take log hk.le]
              unfold reexecutes
              rw [issueIndex_take log hc' hn, progOf_take log hc', trace_take log hk.le]
            · rw [count_take log hk.le]
              simp [hc]
          · simp [ho]
      | _ => rfl

theorem validClose_take (log : Log) {k n : ℕ} (hk : k < n) (o : ℕ) :
    validClose (log.take n) k o = validClose log k o := by
  unfold validClose
  rw [List.getElem?_take_of_lt hk]
  cases hj : log[k]? with
  | none => rfl
  | some e =>
      rcases e with ⟨author, kind⟩
      cases author <;> cases kind <;> try rfl
      simp only
      rw [count_take log hk.le, settled_take log hk.le]

/-- **Locality of the resolver.** -/
theorem firstResolver_take (log : Log) {n : ℕ} (hn : n ≤ log.length) (o : ℕ) :
    ∀ k ≤ n, firstResolver (log.take n) o k = firstResolver log o k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hk' : k < n := hk
      simp only [firstResolver, ih hk'.le, validAnswer_take log hk' hn, validClose_take log hk']

/-- **The first resolver is stable under restriction**: found before `k`, it is found before
any `k'` past it. -/
theorem firstResolver_of_lt (log : Log) (o : ℕ) :
    ∀ k k' j, firstResolver log o k = some j → j < k' → k' ≤ k →
      firstResolver log o k' = some j := by
  intro k
  induction k with
  | zero => intro k' j h; simp [firstResolver] at h
  | succ k ih =>
      intro k' j h hjk hk
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · exact h
      · have hk' : k' ≤ k := Nat.lt_succ_iff.mp hlt
        rcases hfr : firstResolver log o k with _ | j'
        · simp only [firstResolver, hfr] at h
          split at h
          · simp only [Option.some.injEq] at h
            subst h
            omega
          · simp at h
        · simp only [firstResolver, hfr, Option.some.injEq] at h
          subst h
          exact ih k' j' hfr hjk hk'

/-- The prefix through the commit event of occurrence `o`. -/
def prefixThroughCommit (log : Log) (o : ℕ) : Log := log.take (commitIndex log o + 1)

/-- **The payload is a reading of the prefix through the commit.** -/
theorem payload_take (log : Log) (o : ℕ) : payload (prefixThroughCommit log o) o = payload log o := by
  unfold prefixThroughCommit payload commitIndex
  rcases hr : firstResolver log o log.length with _ | j
  · -- never resolved: the truncation is the whole log
    simp only [Option.getD_none]
    rw [List.take_of_length_le (Nat.le_succ _)]
    simp [hr]
  · have hj := (firstResolver_spec hr).1
    have hn : j + 1 ≤ log.length := hj
    simp only [Option.getD_some]
    have hlen : (log.take (j + 1)).length = j + 1 := List.length_take_of_le hn
    have hfr : firstResolver (log.take (j + 1)) o (j + 1) = some j := by
      rw [firstResolver_take log hn o (j + 1) le_rfl]
      exact firstResolver_of_lt log o log.length (j + 1) j hr (Nat.lt_succ_self j) hn
    rw [hlen, hfr]
    show (if validAnswer (log.take (j + 1)) j o = true then commitVector (log.take (j + 1)) j
      else none) = (if validAnswer log j o = true then commitVector log j else none)
    rw [validAnswer_take log (Nat.lt_succ_self j) hn]
    unfold commitVector
    rw [List.getElem?_take_of_lt (Nat.lt_succ_self j)]

/-- The activation event of occurrence `o`, read off the log. -/
def activated (log : Log) (o : ℕ) : Bool := (payload log o).isSome

theorem activated_take (log : Log) (o : ℕ) : activated (prefixThroughCommit log o) o = activated log o := by
  unfold activated; rw [payload_take]

/-- **The activation channel realizes its reference for every log**: the answering process
run on the pre-commitment record.  The declared input is the prefix through the commit;
candidate identity enters it only through events before the commit. -/
theorem realizes_activation {Q Z : Type*} (β : Q → Z → Log) (o : ℕ) (D : Set Q) :
    Realizes β (fun log => prefixThroughCommit log o) (fun log => activated log o)
      (fun x _ => activated x o) D :=
  fun q _ z => (activated_take (β q z) o).symm

/-- **Sequenced settlement gives common activation.**  Two candidates whose logs agree
through the commit activate identically. -/
theorem activation_eq_of_shared_prefix (log log' : Log) (o : ℕ)
    (h : prefixThroughCommit log o = prefixThroughCommit log' o) :
    activated log o = activated log' o := by
  rw [← activated_take log o, ← activated_take log' o, h]

/-- **Item 89 on the concrete frame**: the mismatch term is empty under sequenced
settlement. -/
theorem mismatch_zero_sequenced (log log' : Log) (o : ℕ)
    (h : prefixThroughCommit log o = prefixThroughCommit log' o) :
    indR (activated log o) * (1 - indR (activated log' o)) = 0 := by
  rw [activation_eq_of_shared_prefix log log' o h]
  exact mismatch_common _

end Locality

/-! ## 4. The specification channel -/

/-- The declared inputs of the specification channel: the issue events. -/
def xSpec (log : Log) : List Prog := log.filterMap issueProg

/-- **The mandated program realizes the reference "the `o`-th issue"** on every log; the
ecosystem has no amendment event, so this is the whole tower and the floor is the
mandate. -/
theorem realizes_spec {Q Z : Type*} (β : Q → Z → Log) (o : ℕ) (D : Set Q) :
    Realizes β xSpec (fun log => progOf log o) (fun s _ => s.getD o []) D :=
  fun _ _ _ => rfl

/-! ## 5. Witnesses -/

namespace Witness

open Programs Instance

/-- `w1` with the advisor's reason replaced: the leak shape, the advisor's contribution
a function of something not in the view. -/
def w1Other : Log :=
  [⟨.P, .issue ⟨1, 2⟩ 7 reading⟩, ⟨.S, .routeOpen 0⟩, ⟨.T, .raise 1⟩, ⟨.S, .route 1⟩,
   ⟨.A, .reason 5 7⟩, ⟨.P, .delib 1⟩, ⟨.S, .sessionOpen 1⟩,
   ⟨.P, .commit 0 7 (evalProg reading (trace
     [⟨.P, .issue ⟨1, 2⟩ 7 reading⟩, ⟨.S, .routeOpen 0⟩, ⟨.T, .raise 1⟩, ⟨.S, .route 1⟩,
      ⟨.A, .reason 5 7⟩, ⟨.P, .delib 1⟩, ⟨.S, .sessionOpen 1⟩] 7)) 0 7⟩, ⟨.S, .sessionClose 1⟩]

/-- `w1` with the advisor silent: honest persuasion's other arm. -/
def w1Silent : Log :=
  [⟨.P, .issue ⟨1, 2⟩ 7 reading⟩, ⟨.S, .routeOpen 0⟩, ⟨.T, .raise 1⟩, ⟨.S, .route 1⟩,
   ⟨.P, .delib 1⟩, ⟨.S, .sessionOpen 1⟩,
   ⟨.P, .commit 0 7 (evalProg reading (trace
     [⟨.P, .issue ⟨1, 2⟩ 7 reading⟩, ⟨.S, .routeOpen 0⟩, ⟨.T, .raise 1⟩, ⟨.S, .route 1⟩,
      ⟨.P, .delib 1⟩, ⟨.S, .sessionOpen 1⟩] 6)) 0 6⟩, ⟨.S, .sessionClose 1⟩]

/-- The leak frame: the advisor's reason depends on the selection. -/
def βleak : Bool → Unit → Log := fun σ _ => if σ then w1 else w1Other

theorem leak_commits : commitIndex w1 0 = 7 ∧ commitIndex w1Other 0 = 7 ∧ commitIndex w1Silent 0 = 6 := by
  decide +kernel

/-- **The leak is not transparent to the view**: the two selections leave the same view
and different content. -/
theorem leak_not_transparent :
    view w1 7 = view w1Other 7 ∧
    ¬ Transparent βleak (fun log => view log (commitIndex log 0))
      (fun log => content log (commitIndex log 0)) {true, false} := by
  refine ⟨by decide +kernel, fun h => ?_⟩
  have := h () true (by simp) false (by simp) (by decide +kernel)
  simp only [βleak] at this
  exact absurd this (by decide +kernel)

/-- **The over-rich end**: with the whole log as the view, the leak realizes the identity
reference and transparency certifies nothing. -/
theorem view_overRich :
    Realizes βleak (fun log => log) (fun log => content log (commitIndex log 0))
      (fun log _ => content log (commitIndex log 0)) Set.univ :=
  fun _ _ _ => rfl

/-- The honest/silent frame: two declared advisor programs, on the same view. -/
def βpersuade : Bool → Unit → Log × Bool := fun b _ => (if b then w1 else w1Silent, b)

/-- The declared advisor program: argue `PROOF_B` with certificate `7`, or say nothing. -/
def evalA : Bool → List Event → Multiset Event :=
  fun b _ => if b then ({⟨.A, .reason PROOF_B 7⟩} : Multiset Event) else 0

/-- **Honest persuasion realizes its declared reference** on both arms, and moves the
payload. -/
theorem persuasion_realizes :
    Realizes βpersuade (xR 0) (fun w => content w.1 (commitIndex w.1 0)) (fun p _ => κR evalA p)
      Set.univ ∧ payload w1 0 ≠ payload w1Silent 0 := by
  refine ⟨realizes_reason βpersuade Set.univ 0 evalA ?_, by decide +kernel⟩
  intro q _ z
  cases q <;> cases z <;> decide +kernel

/-- **The under-rich end**: with the empty view, honest persuasion is not transparent. -/
theorem view_underRich :
    ¬ Transparent βpersuade (fun _ => ()) (fun w => content w.1 (commitIndex w.1 0)) Set.univ := by
  intro h
  have := h () true trivial false trivial rfl
  simp only [βpersuade] at this
  exact absurd this (by decide +kernel)

/-- `w1` with the selection published by the system before commitment, on each arm.  The
registrar's `settle` stands in for a market publication: an `S`-authored pre-commitment
event carrying the selection. -/
def w1Market (σ : Bool) : Log :=
  [⟨.P, .issue ⟨1, 2⟩ 7 reading⟩, ⟨.S, .routeOpen 0⟩, ⟨.S, .settle (if σ then 1 else 2)⟩,
   ⟨.T, .raise 1⟩, ⟨.S, .route 1⟩, ⟨.A, .reason PROOF_B 7⟩, ⟨.P, .delib 1⟩, ⟨.S, .sessionOpen 1⟩,
   ⟨.P, .commit 0 7 (evalProg reading (trace
     [⟨.P, .issue ⟨1, 2⟩ 7 reading⟩, ⟨.S, .routeOpen 0⟩, ⟨.S, .settle (if σ then 1 else 2)⟩,
      ⟨.T, .raise 1⟩, ⟨.S, .route 1⟩, ⟨.A, .reason PROOF_B 7⟩, ⟨.P, .delib 1⟩,
      ⟨.S, .sessionOpen 1⟩] 8)) 0 8⟩, ⟨.S, .sessionClose 1⟩]

/-- **A published selection breaks the view's blindness, not transparency**: the view
differs across the two selections. -/
theorem market_view_not_blind : view (w1Market true) 8 ≠ view (w1Market false) 8 := by
  decide +kernel

/-! ### Activation: sequenced versus same-branch -/

/-- The raw candidate acts after the commit: an advisor move appended to `w1`. -/
def wRawSeq : Log := w1 ++ [⟨.A, .revoke .P 7⟩]

theorem sequenced_common :
    prefixThroughCommit wRawSeq 0 = prefixThroughCommit w1 0 ∧
    activated wRawSeq 0 = true ∧ activated w1 0 = true := by
  decide +kernel

/-- The mismatch term under sequenced settlement is `0`, by the theorem. -/
theorem sequenced_mismatch_zero :
    indR (activated wRawSeq 0) * (1 - indR (activated w1 0)) = 0 :=
  mismatch_zero_sequenced _ _ 0 sequenced_common.1

/-- The corrigibilized candidate under same-branch activation: its gated commit lands
after the session closes. -/
def wCorrLate : Log :=
  [⟨.P, .issue ⟨1, 2⟩ 7 reading⟩, ⟨.S, .routeOpen 0⟩, ⟨.T, .raise 1⟩, ⟨.S, .route 1⟩,
   ⟨.A, .reason PROOF_B 7⟩, ⟨.P, .delib 1⟩, ⟨.S, .sessionOpen 1⟩, ⟨.S, .sessionClose 1⟩,
   ⟨.P, .commit 0 7 [1/4, 3/4] 0 8⟩]

/-- **Same-branch activation is not candidate-blind**: the raw candidate commits in time,
the corrigibilized one is void, the prefixes through the commit differ, and the mismatch
is attained. -/
theorem sameBranch_mismatch :
    activated w1 0 = true ∧ activated wCorrLate 0 = false ∧
    prefixThroughCommit w1 0 ≠ prefixThroughCommit wCorrLate 0 ∧
    indR (activated w1 0) * (1 - indR (activated wCorrLate 0)) = 1 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  have h1 : activated w1 0 = true := by decide +kernel
  have h2 : activated wCorrLate 0 = false := by decide +kernel
  rw [h1, h2]; simp [indR]

/-! ### The evaluator -/

/-- **A secret evaluator change is a realization failure of the evaluation channel**: the
committed vector is not the mandated program's output on the trace, and the builder
voids it (`Instance.miscomputation_void`). -/
theorem secret_evaluator_not_realized :
    commitVector w1Mis 7 ≠ some (evalProg (progOf w1Mis 0) (trace w1Mis 7)) ∧
    payload w1Mis 0 = none := by
  decide +kernel

/-- The specification channel on the instance: the mandate is the floor. -/
theorem spec_w1 : progOf w1 0 = reading ∧ xSpec w1 = [reading] := by decide +kernel

end Witness

end Workspace.Deference.Contrib.TransparentEcosystem

#print axioms Workspace.Deference.Contrib.TransparentEcosystem.content_eq
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.evalTerm_perm
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.evalProg_perm
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.reasonMediated_content
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.realizes_reason
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.selectionBlind_ecosystem
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.validAnswer_take
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.firstResolver_take
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.payload_take
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.realizes_activation
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.activation_eq_of_shared_prefix
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.mismatch_zero_sequenced
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.realizes_spec
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.Witness.leak_not_transparent
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.Witness.view_overRich
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.Witness.persuasion_realizes
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.Witness.view_underRich
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.Witness.market_view_not_blind
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.Witness.sequenced_mismatch_zero
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.Witness.sameBranch_mismatch
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.Witness.secret_evaluator_not_realized
#print axioms Workspace.Deference.Contrib.TransparentEcosystem.Witness.spec_w1
