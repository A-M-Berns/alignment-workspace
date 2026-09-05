/-
# Integrity adversary: countermodels on the unified trace

Round `projects/normativity/legitimacy/rounds/2026-09-05-integrity-adversary/`. Imports the
Normative Continuity spine and edits nothing in it. Every structure here is a
`DefeatTrace` in the spine's sense, so every countermodel satisfies the spine's
structural requirements by construction; what each one shows is that those
requirements, together with `Disciplined` and even `AnswerableFor P`, are satisfied by
traces in which a debt is not answered, not settled on its own terms, and not carried.

**General lemmas** (`Lemmas`).

* `not_out_after_res`, `resolved_once` — an issue resolves at most once.
* `parent_resolved_at_birth`, `root_not_resolved_before` — an issue resolved at `k` can
  be neither a parent nor a route root of anything introduced after `k`. Together:
  the record has no ancestry or route channel back to a resolved issue, so a
  defective closure can only be *mentioned* by a later issue, never reconnected to.
* `anc_parentless` — a parentless issue is its own only ancestor, so `grounded_replay`
  is satisfied trivially by any parentless issue born at any position: the
  "authorization tree back to genesis" does not distinguish genesis from a late root.
* `disciplined_empty_licence` — under the empty licence relation `Disciplined` forbids
  every disposal; with `Witness.witness_disciplined` this shows `Disciplined` is a
  property of a trace *and* an evaluator-supplied `Li`, not of the history alone.

**The evasive trace** (`Evasive`). Four issues over two participants `P = true`,
`V = false`, one settlement fact, no prerequisites. `V` disposes `P`'s criticism
citing only the settlement fact; the successor is discharged at the next position by
any discharging kind `k` (`answer` or `settle ()`); an unrelated parentless issue is
born at 2. Parametrized by the opener function `op`, so the same proofs cover the case
in which `V` opened every issue including the licence that gives `P` standing.
`evasive_disciplined`, `evasive_answerable_for_P`, `evasive_crit_dead`,
`evasive_resolver_V`, `evasive_minted_standing`, `evasive_late_root`.

**The gate trace** (`Gate`). Two prerequisites. `t` is answered *with a successor*
`t1`, so `Met d` becomes true while `t1` is live; `e` is dropped from `c`, so `c` is
ready while its root `u` is live and never discharged. Every resolution is an
`answer`, so the trace is `Disciplined` under every licence relation.
`gate_met_d`, `gate_t1_live`, `gate_b_ready`, `gate_c_ready`, `gate_e_never_met`,
`gate_u_live`, `gate_disciplined`.

**What is not claimed.** That any of these traces is legitimate, or that the missing
clauses named in `ATTACKS.md` suffice; only that the listed conditions admit them.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.NormativeContinuity

namespace Workspace.Normativity.Contrib.IntegrityAdversary

open Classical Relation Finset
open Workspace.Normativity.Contrib.NormativeContinuity

noncomputable section

/-! ## 1. General lemmas -/

namespace Lemmas

variable {Q D S A : Type*}

/-- Once resolved, an issue is never outstanding again. -/
theorem not_out_after_res (T : IssueTrace Q D) {q : Q} {k : ℕ} (hres : q ∈ T.Res k) :
    ∀ n, k < n → q ∉ T.O n := by
  obtain ⟨j, hjk, hqj⟩ := T.out_born q k (T.res_subset k hres)
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    intro hmem
    rw [T.resolution_continuity n] at hmem
    rcases Finset.mem_union.1 hmem with h | h
    · rcases Finset.mem_sdiff.1 h with ⟨hO, hnotres⟩
      rcases Nat.lt_or_ge k n with hkn | hkn
      · exact ih hkn hO
      · have : k = n := by omega
        subst this
        exact hnotres hres
    · have := T.born_unique q j n hqj h
      omega

/-- An issue resolves at most once. -/
theorem resolved_once (T : IssueTrace Q D) {q : Q} {k n : ℕ} (hk : q ∈ T.Res k)
    (hn : q ∈ T.Res n) : k = n := by
  rcases lt_trichotomy k n with h | h | h
  · exact absurd (T.res_subset n hn) (not_out_after_res T hk n h)
  · exact h
  · exact absurd (T.res_subset k hk) (not_out_after_res T hn k h)

/-- **Reopening is unrepresentable by ancestry.** A parent of an issue born at `n`
resolved at `n` and at no other position; an issue resolved earlier cannot be a parent
of anything born later. -/
theorem parent_resolved_at_birth (T : IssueTrace Q D) {q p : Q} {n k : ℕ}
    (hq : q ∈ T.Born n) (hp : p ∈ T.par q) (hk : p ∈ T.Res k) : k = n :=
  resolved_once T hk (T.fresh_successors n q hq p hp)

/-- **Nor by route.** A route root of a prerequisite introduced at `n` was not
resolved before `n`. -/
theorem root_not_resolved_before (T : IssueTrace Q D) {n : ℕ} {q t : Q} {d : D}
    (hd : d ∈ T.PreAdd n q) (ht : t ∈ T.roots d) {k : ℕ} (hk : t ∈ T.Res k) : n ≤ k := by
  by_contra hlt
  push_neg at hlt
  rcases Finset.mem_union.1 (T.pre_refs n q d hd ht) with h | h
  · exact not_out_after_res T hk n hlt h
  · obtain ⟨j, hjk, hj⟩ := T.out_born t k (T.res_subset k hk)
    have := T.born_unique t j n hj h
    omega

/-- A parentless issue is its own only ancestor. -/
theorem anc_parentless (T : TraceData Q D) {q r : Q} (hq : T.par q = ∅) (h : T.anc r q) :
    r = q := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨p, -, hpq⟩
  · exact heq.symm
  · exact absurd hpq (by simp [TraceData.succ, hq])

/-- **Grounded replay is vacuous on a parentless issue**, wherever it is born: the only
witness to `∃ r, anc r q ∧ par r = ∅` is `q` itself. Nothing in `IssueTrace` forbids a
parentless birth at a positive position (`Evasive.evasive_late_root`). -/
theorem grounded_replay_trivial_on_parentless (T : DefeatTrace Q D S A) {q : Q}
    (hpar : T.par q = ∅) : ∀ r, (T.anc r q ∧ T.par r = ∅) ↔ r = q := by
  intro r
  constructor
  · rintro ⟨h, -⟩; exact anc_parentless T.toTraceData hpar h
  · rintro rfl; exact ⟨Relation.ReflTransGen.refl, hpar⟩

/-- **`Disciplined` reads the evaluator's licence relation.** Under the empty relation
it forbids every disposal, so the same history is disciplined or not according to a
parameter the history does not record. -/
theorem disciplined_empty_licence (T : DefeatTrace Q D S A) {K Ty X : Type*} (κ : Q → K)
    (τ : Q → Ty) (x : Q → X) (h : T.Disciplined ⟨fun _ _ _ _ _ => False⟩ κ τ x) {n : ℕ}
    {q : Q} (hq : q ∈ T.Res n) (G : Finset (Ground Q S)) : T.kind n q ≠ Kind.dispose G := by
  intro hk
  rcases h n q hq with h1 | ⟨G', q', hk', hA⟩ | ⟨s, hs, -⟩
  · rw [hk] at h1; cases h1
  · obtain ⟨b, -, l, -, hl⟩ := hA.contested
    exact hl
  · rw [hk] at hs; cases hs

/-- The spine's own witness is disciplined under `wlic` and not under the empty licence
relation, although it is one history. -/
theorem witness_disciplined_is_relative :
    Witness.witness.Disciplined Witness.wlic (fun _ => ()) (fun _ => ()) (fun _ => ()) ∧
    ¬ Witness.witness.Disciplined ⟨fun _ _ _ _ _ => False⟩ (fun _ => ()) (fun _ => ())
        (fun _ => ()) := by
  refine ⟨Witness.witness_disciplined, fun h => ?_⟩
  have hres : Witness.WQ.dis ∈ Witness.witness.Res 1 := by
    simp [Witness.resAt, Witness.Resolves]
  exact disciplined_empty_licence Witness.witness _ _ _ h hres Witness.wG rfl

end Lemmas

/-! ## 2. The evasive trace -/

namespace Evasive

/-- A licence issue, `P`'s criticism, its successor, and a late parentless issue. -/
inductive EQ | licP | crit | crit1 | late
  deriving DecidableEq, Fintype

open EQ

/-- `true` is the principal `P`, `false` the assessed process `V`. -/
abbrev EA := Bool

/-- No prerequisites. -/
abbrev ED := Empty

/-- One settlement fact, about nothing in particular. -/
abbrev ES := Unit

def bornAt : EQ → ℕ
  | crit1 => 1
  | late => 2
  | _ => 0

def resAt : EQ → ℕ
  | crit => 1
  | crit1 => 2
  | _ => 9

/-- Only the criticism and its successor resolve. -/
def Resolves (q : EQ) : Prop := q = crit ∨ q = crit1

instance : DecidablePred Resolves := fun q => by unfold Resolves; infer_instance

def eBorn (n : ℕ) : Finset EQ := Finset.univ.filter (fun q => bornAt q = n)
def eRes (n : ℕ) : Finset EQ := Finset.univ.filter (fun q => resAt q = n ∧ Resolves q)
def eO (n : ℕ) : Finset EQ :=
  Finset.univ.filter (fun q => bornAt q < n ∧ ¬ (resAt q < n ∧ Resolves q))

def epar : EQ → Finset EQ
  | crit1 => {crit}
  | _ => ∅

@[simp] lemma mem_eBorn {q : EQ} {n : ℕ} : q ∈ eBorn n ↔ bornAt q = n := by simp [eBorn]
@[simp] lemma mem_eRes {q : EQ} {n : ℕ} : q ∈ eRes n ↔ (resAt q = n ∧ Resolves q) := by
  simp [eRes]
@[simp] lemma mem_eO {q : EQ} {n : ℕ} :
    q ∈ eO n ↔ (bornAt q < n ∧ ¬ (resAt q < n ∧ Resolves q)) := by simp [eO]

lemma epar_of_ne {q : EQ} (h : q ≠ crit1) : epar q = ∅ := by
  cases q <;> simp_all [epar]

def edata : TraceData EQ ED where
  O := eO
  Res := eRes
  Born := eBorn
  par := epar
  Pre := fun _ _ => ∅
  PreAdd := fun _ _ => ∅
  PreDrop := fun _ _ => ∅
  roots := fun e => e.elim
  intro := fun e => e.elim
  Met := fun _ e => e.elim
  M := fun _ => ∅

theorem edata_other : Fixtures.OtherRequirements edata := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q n k hn hk
    simp only [edata, mem_eBorn] at hn hk; omega
  · intro q n hn
    simp only [edata, mem_eBorn] at hn
    simp only [edata, mem_eO]; omega
  · intro q n hn
    simp only [edata, mem_eO] at hn
    exact ⟨bornAt q, hn.1, by simp [edata]⟩
  · intro n q hq
    simp only [edata, mem_eRes] at hq
    simp only [edata, mem_eO]
    obtain ⟨h1, h2⟩ := hq
    refine ⟨?_, by omega⟩
    revert h1 h2; cases q <;> simp [bornAt, resAt, Resolves] <;> omega
  · intro n
    ext q
    simp only [edata, Finset.mem_union, Finset.mem_sdiff, mem_eO, mem_eRes, mem_eBorn]
    cases q <;> simp [bornAt, resAt, Resolves] <;> omega
  · intro n q hq p hp
    rcases eq_or_ne q crit1 with rfl | hne
    · simp only [edata, epar, Finset.mem_singleton] at hp
      subst hp
      simp only [edata, mem_eBorn, bornAt] at hq
      subst hq
      simp [edata, resAt, Resolves]
    · rw [show (edata.par q) = epar q from rfl, epar_of_ne hne] at hp
      simp at hp
  · intro n q _ _; simp [edata]
  · intro n q _; simp [edata]
  · intro n q d hd; simp [edata] at hd
  · intro n q d hd; simp [edata] at hd
  · intro n e; exact e.elim
  · intro n q _ d hd; simp [edata] at hd
  · intro n m hm; simp [edata] at hm
  · intro n m hm; simp [edata] at hm

theorem edata_reach : Fixtures.ReachGate edata := by
  intro n q _ _ hne; simp [edata] at hne

def eIssue : IssueTrace EQ ED := Fixtures.toIssueTrace edata edata_other edata_reach

/-- The grounds of the disposal: the settlement fact and nothing else. -/
def eG : Finset (Ground EQ ES) := {Sum.inr ()}

/-- The criticism is disposed at 1; its successor is resolved at 2 by the parameter `k`. -/
def ekind (k : Kind EQ ES) : ℕ → EQ → Kind EQ ES
  | 1, crit => Kind.dispose eG
  | 2, crit1 => k
  | _, _ => Kind.answer

/-- **The evasive trace**, for any discharging kind `k` at the successor and any
assignment `op` of openers. -/
def evasive (k : Kind EQ ES) (hk : k.Discharges) (op : EQ → EA) : DefeatTrace EQ ED ES EA :=
  { eIssue with
    Settled := fun n _ => 1 ≤ n
    settled_mono := fun n _ h => by omega
    kind := ekind k
    resolver := fun _ _ => false
    opener := op
    dispose_successor := by
      intro n q G hres hkd
      have hq : resAt q = n ∧ Resolves q := by
        simpa [eIssue, Fixtures.toIssueTrace, edata] using hres
      obtain ⟨h1, h2⟩ := hq
      rcases h2 with rfl | rfl
      · rw [show resAt crit = 1 from rfl] at h1; subst h1
        exact ⟨crit1, by simp [eIssue, Fixtures.toIssueTrace, edata, bornAt],
          by simp [eIssue, Fixtures.toIssueTrace, edata, epar]⟩
      · rw [show resAt crit1 = 2 from rfl] at h1; subst h1
        exfalso
        have hkk : k = Kind.dispose G := hkd
        rw [hkk] at hk
        exact hk
    met_def := by intro n e; exact e.elim }

section

variable (k : Kind EQ ES) (hk : k.Discharges) (op : EQ → EA)

@[simp] lemma evasive_Born (n : ℕ) : (evasive k hk op).Born n = eBorn n := rfl
@[simp] lemma evasive_Res (n : ℕ) : (evasive k hk op).Res n = eRes n := rfl
@[simp] lemma evasive_O (n : ℕ) : (evasive k hk op).O n = eO n := rfl
@[simp] lemma evasive_par (q : EQ) : (evasive k hk op).par q = epar q := rfl
@[simp] lemma evasive_kind (n : ℕ) (q : EQ) : (evasive k hk op).kind n q = ekind k n q := rfl
@[simp] lemma evasive_resolver (n : ℕ) (q : EQ) : (evasive k hk op).resolver n q = false := rfl
@[simp] lemma evasive_opener (q : EQ) : (evasive k hk op).opener q = op q := rfl
@[simp] lemma evasive_Settled (n : ℕ) (s : ES) : (evasive k hk op).Settled n s ↔ 1 ≤ n :=
  Iff.rfl

/-- The licence issue licenses `P`, for the one anchor, whoever opened it. -/
def eLi : DefeatTrace.Licence EQ EA Unit Unit Unit where
  lic q b _ _ _ := q = licP ∧ b = true

theorem evasive_stands_P {n : ℕ} (hn : 1 ≤ n) :
    (evasive k hk op).standsFor eLi n true () () () := by
  refine ⟨licP, ?_, rfl, rfl⟩
  simp [bornAt, resAt, Resolves]; omega

/-- **The disposal is answerable *for* `P`.** All six clauses of `Answerable` and the
principal clause of `AnswerableFor`, for every `k` and every opener assignment. -/
theorem evasive_answerable_for_P :
    (evasive k hk op).AnswerableFor eLi (fun _ => ()) (fun _ => ()) (fun _ => ())
      true 1 crit eG crit1 where
  grounded := by
    intro g hg
    rw [eG, Finset.mem_singleton] at hg
    subst hg
    exact le_rfl
  not_self := by simp [eG]
  born := by simp [bornAt]
  inherits := by simp [epar]
  contested := ⟨true, by simp, evasive_stands_P k hk op le_rfl⟩
  foreign_ground := ⟨Sum.inr (), by simp [eG], by rintro p ⟨⟩⟩
  principal_stands := evasive_stands_P k hk op le_rfl

/-- **The trace is defeat-disciplined**, for `k = answer` and for `k = settle ()`. -/
theorem evasive_disciplined :
    (evasive k hk op).Disciplined eLi (fun _ => ()) (fun _ => ()) (fun _ => ()) := by
  intro n q hres
  have hq : resAt q = n ∧ Resolves q := by simpa using hres
  obtain ⟨h1, h2⟩ := hq
  rcases h2 with rfl | rfl
  · rw [show resAt crit = 1 from rfl] at h1; subst h1
    exact Or.inr (Or.inl ⟨eG, crit1, rfl, (evasive_answerable_for_P k hk op).toAnswerable⟩)
  · rw [show resAt crit1 = 2 from rfl] at h1; subst h1
    cases k with
    | answer => exact Or.inl rfl
    | dispose G => exact hk.elim
    | settle s => exact Or.inr (Or.inr ⟨s, rfl, by show (1:ℕ) ≤ 2; omega⟩)

/-- The criticism itself was disposed, not answered and not settled. -/
theorem evasive_crit_disposed : (evasive k hk op).kind 1 crit = Kind.dispose eG := rfl

/-- Every resolution in the trace was made by `V`. -/
theorem evasive_resolver_V : ∀ n q, (evasive k hk op).resolver n q = false := fun _ _ => rfl

/-- **The criticism's matter is dead at 3**: nothing live descends from it. -/
theorem evasive_crit_dead : (evasive k hk op).Live 3 crit = ∅ := by
  apply eq_empty_of_forall_notMem
  intro q hq
  rw [TraceData.Live, Finset.mem_filter] at hq
  obtain ⟨hO, hanc⟩ := hq
  have hO' : bornAt q < 3 ∧ ¬ (resAt q < 3 ∧ Resolves q) := by simpa using hO
  cases q with
  | licP => exact absurd (Lemmas.anc_parentless _ rfl hanc) (by decide)
  | crit => simp [resAt, Resolves] at hO'
  | crit1 => simp [resAt, Resolves] at hO'
  | late => exact absurd (Lemmas.anc_parentless _ rfl hanc) (by decide)

/-- **Minted standing.** With `op ≡ V`, one participant opened every issue — the licence
conferring `P`'s standing included — resolved every issue, and cited only a settlement
fact; the disposal is still answerable for `P` and the trace is still disciplined. -/
theorem evasive_minted_standing :
    (∀ q, (evasive k hk (fun _ => false)).opener q = false) ∧
    (∀ n q, (evasive k hk (fun _ => false)).resolver n q = false) ∧
    (evasive k hk (fun _ => false)).AnswerableFor eLi (fun _ => ()) (fun _ => ())
      (fun _ => ()) true 1 crit eG crit1 ∧
    (evasive k hk (fun _ => false)).Disciplined eLi (fun _ => ()) (fun _ => ()) (fun _ => ()) :=
  ⟨fun _ => rfl, fun _ _ => rfl, evasive_answerable_for_P k hk _, evasive_disciplined k hk _⟩

/-- **A late root.** `late` is born at 2 with no parents, so it is its own
authorization tree (`Lemmas.grounded_replay_trivial_on_parentless`). -/
theorem evasive_late_root :
    late ∈ (evasive k hk op).Born 2 ∧ (evasive k hk op).par late = ∅ ∧
    ∀ r, ((evasive k hk op).anc r late ∧ (evasive k hk op).par r = ∅) ↔ r = late :=
  ⟨by simp [bornAt], rfl, Lemmas.grounded_replay_trivial_on_parentless _ rfl⟩

/-- The two discharging kinds, for instantiating the family. -/
theorem answer_discharges : (Kind.answer : Kind EQ ES).Discharges := trivial
theorem settle_discharges : (Kind.settle () : Kind EQ ES).Discharges := trivial

end

end Evasive

/-! ## 3. The gate trace -/

namespace Gate

/-- A route root `t` and its successor `t1`, a second root `u`, and two waiters `b`, `c`. -/
inductive MQ | t | t1 | u | b | c
  deriving DecidableEq, Fintype

/-- Two prerequisite occurrences: `d` on `b` rooted at `t`, `e` on `c` rooted at `u`. -/
inductive MD | d | e
  deriving DecidableEq, Fintype

open MQ MD

abbrev MA := Bool
abbrev MS := Empty

def bornAt : MQ → ℕ
  | t1 => 1
  | _ => 0

def resAt : MQ → ℕ
  | t => 1
  | b => 2
  | c => 2
  | _ => 9

def Resolves (q : MQ) : Prop := q = t ∨ q = b ∨ q = c

instance : DecidablePred Resolves := fun q => by unfold Resolves; infer_instance

def mBorn (n : ℕ) : Finset MQ := Finset.univ.filter (fun q => bornAt q = n)
def mRes (n : ℕ) : Finset MQ := Finset.univ.filter (fun q => resAt q = n ∧ Resolves q)
def mO (n : ℕ) : Finset MQ :=
  Finset.univ.filter (fun q => bornAt q < n ∧ ¬ (resAt q < n ∧ Resolves q))

def mpar : MQ → Finset MQ
  | t1 => {t}
  | _ => ∅

def mroots : MD → Finset MQ
  | d => {t}
  | e => {u}

/-- `b` waits on `d` from 1 on; `c` waits on `e` at 1 only. -/
def mPre (n : ℕ) (q : MQ) : Finset MD :=
  if q = b ∧ 1 ≤ n then {d} else if q = c ∧ n = 1 then {e} else ∅

def mPreAdd (n : ℕ) (q : MQ) : Finset MD :=
  if n = 0 ∧ q = b then {d} else if n = 0 ∧ q = c then {e} else ∅

/-- `e` is dropped from `c` at 1. -/
def mPreDrop (n : ℕ) (q : MQ) : Finset MD :=
  if n = 1 ∧ q = c then {e} else ∅

/-- `Met`, as `met_def` will force it: `d` from 2 on, `e` never. -/
def mMet (n : ℕ) : MD → Prop
  | d => 1 < n
  | e => False

@[simp] lemma mem_mBorn {q : MQ} {n : ℕ} : q ∈ mBorn n ↔ bornAt q = n := by simp [mBorn]
@[simp] lemma mem_mRes {q : MQ} {n : ℕ} : q ∈ mRes n ↔ (resAt q = n ∧ Resolves q) := by
  simp [mRes]
@[simp] lemma mem_mO {q : MQ} {n : ℕ} :
    q ∈ mO n ↔ (bornAt q < n ∧ ¬ (resAt q < n ∧ Resolves q)) := by simp [mO]

lemma mpar_of_ne {q : MQ} (h : q ≠ t1) : mpar q = ∅ := by
  cases q <;> simp_all [mpar]

def mdata : TraceData MQ MD where
  O := mO
  Res := mRes
  Born := mBorn
  par := mpar
  Pre := mPre
  PreAdd := mPreAdd
  PreDrop := mPreDrop
  roots := mroots
  intro := fun _ => 0
  Met := mMet
  M := fun _ => ∅

theorem mdata_other : Fixtures.OtherRequirements mdata := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q n k hn hk
    simp only [mdata, mem_mBorn] at hn hk; omega
  · intro q n hn
    simp only [mdata, mem_mBorn] at hn
    simp only [mdata, mem_mO]; omega
  · intro q n hn
    simp only [mdata, mem_mO] at hn
    exact ⟨bornAt q, hn.1, by simp [mdata]⟩
  · intro n q hq
    simp only [mdata, mem_mRes] at hq
    simp only [mdata, mem_mO]
    obtain ⟨h1, h2⟩ := hq
    refine ⟨?_, by omega⟩
    revert h1 h2; cases q <;> simp [bornAt, resAt, Resolves] <;> omega
  · intro n
    ext q
    simp only [mdata, Finset.mem_union, Finset.mem_sdiff, mem_mO, mem_mRes, mem_mBorn]
    cases q <;> simp [bornAt, resAt, Resolves] <;> omega
  · intro n q hq p hp
    rcases eq_or_ne q t1 with rfl | hne
    · simp only [mdata, mpar, Finset.mem_singleton] at hp
      subst hp
      simp only [mdata, mem_mBorn, bornAt] at hq
      subst hq
      simp [mdata, resAt, Resolves]
    · rw [show (mdata.par q) = mpar q from rfl, mpar_of_ne hne] at hp
      simp at hp
  · intro n q hO hO'
    simp only [mdata, mem_mO] at hO hO'
    have hn : 1 ≤ n := by cases q <;> simp [bornAt] at hO <;> omega
    simp only [mdata]
    cases q with
    | b => simp [mPre, mPreDrop, mPreAdd, hn, show 1 ≤ n + 1 by omega, show n ≠ 0 by omega]
    | c =>
      rcases eq_or_ne n 1 with rfl | h1
      · ext d'; simp [mPre, mPreDrop, mPreAdd]
      · simp [mPre, mPreDrop, mPreAdd, h1, show n + 1 ≠ 1 by omega, show n ≠ 0 by omega]
    | t => simp [mPre, mPreDrop, mPreAdd, show n ≠ 0 by omega]
    | t1 => simp [mPre, mPreDrop, mPreAdd, show n ≠ 0 by omega]
    | u => simp [mPre, mPreDrop, mPreAdd, show n ≠ 0 by omega]
  · intro n q hq
    simp only [mdata, mem_mBorn] at hq
    show mPre (n + 1) q = mPreAdd n q
    cases q <;> simp [bornAt] at hq <;> subst hq <;> simp [mPre, mPreAdd]
  · intro n q d hd
    show (0 : ℕ) = n
    by_contra h
    simp [mdata, mPreAdd, Ne.symm h] at hd
  · intro n q d hd r hr
    have hn : n = 0 := by
      by_contra h
      simp [mdata, mPreAdd, h] at hd
    subst hn
    simp only [mdata, Finset.mem_union, mem_mO, mem_mBorn]
    right
    have : d = MD.d ∧ q = b ∨ d = MD.e ∧ q = c := by
      revert hd
      cases q <;> cases d <;> simp [mdata, mPreAdd]
    rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp [mdata, mroots] at hr; subst hr; rfl
    · simp [mdata, mroots] at hr; subst hr; rfl
  · intro n d h
    cases d with
    | d => show 1 < n + 1; have : 1 < n := h; omega
    | e => exact h.elim
  · intro n q hq
    simp only [mdata, mem_mRes] at hq
    intro d hd
    obtain ⟨h1, h2⟩ := hq
    rcases h2 with rfl | rfl | rfl
    · rw [show resAt t = 1 from rfl] at h1; subst h1
      simp [mdata, mPre] at hd
    · rw [show resAt b = 2 from rfl] at h1; subst h1
      have : d = MD.d := by simpa [mdata, mPre] using hd
      subst this
      show 1 < 2; omega
    · rw [show resAt c = 2 from rfl] at h1; subst h1
      simp [mdata, mPre] at hd
  · intro n m hm; simp [mdata] at hm
  · intro n m hm; simp [mdata] at hm

theorem mdata_reach : Fixtures.ReachGate mdata := by
  intro n q _ _ _ m hm; simp [mdata] at hm

def mIssue : IssueTrace MQ MD := Fixtures.toIssueTrace mdata mdata_other mdata_reach

/-- **The gate trace.** Every resolution is an `answer`; there is no settlement fact. -/
def gate : DefeatTrace MQ MD MS MA :=
  { mIssue with
    Settled := fun _ s => s.elim
    settled_mono := fun _ s _ => s.elim
    kind := fun _ _ => Kind.answer
    resolver := fun _ _ => false
    opener := fun q => q = t ∨ q = u
    dispose_successor := by
      intro n q G _ h
      cases h
    met_def := by
      intro n d
      cases d with
      | d =>
        show 1 < n ↔ _
        simp only [mIssue, Fixtures.toIssueTrace, mdata, mroots, Finset.mem_singleton,
          forall_eq, mem_mRes, Kind.Discharges, and_true]
        constructor
        · intro h; exact ⟨1, h, rfl, Or.inl rfl⟩
        · rintro ⟨k, hk, hk1, -⟩
          have : k = 1 := by simpa [resAt] using hk1.symm
          omega
      | e =>
        show False ↔ _
        simp [mIssue, Fixtures.toIssueTrace, mdata, mroots, resAt, Resolves] }

@[simp] lemma gate_O (n : ℕ) : gate.O n = mO n := rfl
@[simp] lemma gate_Res (n : ℕ) : gate.Res n = mRes n := rfl
@[simp] lemma gate_par (q : MQ) : gate.par q = mpar q := rfl
@[simp] lemma gate_Pre (n : ℕ) (q : MQ) : gate.Pre n q = mPre n q := rfl
@[simp] lemma gate_Met (n : ℕ) (d : MD) : gate.Met n d = mMet n d := rfl
@[simp] lemma gate_kind (n : ℕ) (q : MQ) : gate.kind n q = Kind.answer := rfl

/-- **The prerequisite is met at 2** — its root was answered at 1. -/
theorem gate_met_d : gate.Met 2 d := by show 1 < 2; omega

/-- **while the root's matter is live**: the successor carries on. -/
theorem gate_t1_live : t1 ∈ gate.Live 2 t := by
  refine Finset.mem_filter.2 ⟨?_, Relation.ReflTransGen.single ?_⟩
  · simp [bornAt, resAt, Resolves]
  · show t ∈ mpar t1; simp [mpar]

/-- So the waiter is ready. -/
theorem gate_b_ready : gate.Ready 2 b := by
  intro d' hd
  have : d' = d := by simpa [mPre] using hd
  subst this
  exact gate_met_d

/-- **The dropped prerequisite**: `c` is ready at 2, -/
theorem gate_c_ready : gate.Ready 2 c := by
  intro d' hd
  simp [mPre] at hd

/-- **its former prerequisite is never met,** -/
theorem gate_e_never_met : ∀ n, ¬ gate.Met n e := fun _ h => h

/-- **and its root is live at every positive position.** -/
theorem gate_u_live : ∀ n, 1 ≤ n → u ∈ gate.O n := by
  intro n hn
  simp [bornAt, resAt, Resolves]; omega

/-- The trace is disciplined under every licence relation and every anchoring. -/
theorem gate_disciplined {K Ty X : Type*} (Li : DefeatTrace.Licence MQ MA K Ty X)
    (κ : MQ → K) (τ : MQ → Ty) (x : MQ → X) : gate.Disciplined Li κ τ x :=
  fun _ _ _ => Or.inl rfl

/-- Contrast: the spine proves a *disposed* root meets nothing (`dispose_not_met`); the
same edge typed `answer` with a successor meets the prerequisite and keeps the
successor live. The kind, not the receipt, decides `Met`. -/
theorem gate_kind_decides_met :
    gate.Met 2 d ∧ (gate.Live 2 t).Nonempty ∧ gate.kind 1 t = Kind.answer :=
  ⟨gate_met_d, ⟨t1, gate_t1_live⟩, rfl⟩

end Gate

end

end Workspace.Normativity.Contrib.IntegrityAdversary

#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Lemmas.not_out_after_res
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Lemmas.resolved_once
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Lemmas.parent_resolved_at_birth
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Lemmas.root_not_resolved_before
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Lemmas.anc_parentless
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Lemmas.grounded_replay_trivial_on_parentless
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Lemmas.disciplined_empty_licence
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Lemmas.witness_disciplined_is_relative
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Evasive.edata_other
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Evasive.edata_reach
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Evasive.evasive_answerable_for_P
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Evasive.evasive_disciplined
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Evasive.evasive_crit_disposed
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Evasive.evasive_resolver_V
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Evasive.evasive_crit_dead
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Evasive.evasive_minted_standing
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Evasive.evasive_late_root
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Evasive.answer_discharges
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Evasive.settle_discharges
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Gate.mdata_other
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Gate.mdata_reach
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Gate.gate_met_d
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Gate.gate_t1_live
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Gate.gate_b_ready
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Gate.gate_c_ready
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Gate.gate_e_never_met
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Gate.gate_u_live
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Gate.gate_disciplined
#print axioms Workspace.Normativity.Contrib.IntegrityAdversary.Gate.gate_kind_decides_met
