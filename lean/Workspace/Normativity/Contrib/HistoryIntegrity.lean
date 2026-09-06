/-
# History Integrity: token fates, the content-conservation clause, and segment composition

Round `2026-09-05-integrity-constructive`
(`projects/normativity/legitimacy/rounds/2026-09-05-integrity-constructive/`). Builds on
the unified defeat trace of `NormativeContinuity.lean` §5 and adds nothing to it.

**What is proved.**

* `not_out_after_res`, `res_unique` — once resolved, an issue is
  never outstanding again, so its resolution position is unique. This is a theorem of the
  spine; `dispose_not_met` carried it as a hypothesis, and `dispose_not_met'` drops it.
* `token_fate` — **the identity-level trichotomy.** At every position after
  its birth an issue is outstanding, or was discharged (answered or settled) at a unique
  earlier position, or was disposed at a unique earlier position with a fresh successor
  born there. There is no fourth token fate, and this uses only the structural fields.
* `SliceLedger.conservation` — **the content-level three-fate law.** Over a trace whose
  every step from `n₀` satisfies the one transition-local clause `LocalConservation`
  (identity frame off the batch, incoming soundness, carry completeness for disposals,
  separately certified internal closure, receipt accumulation for answers and settlements),
  the anchored load of a matter's
  slice equals *answered* ⊔ *settlement-discharged* ⊔ *carried live* at every later
  position. Disposal contributes nothing: the Defeat Principle in the ledger.
* `SliceLedger.integrity_compose`, `integrity_refl` — segment integrity concatenates and
  the empty segment is neutral; `conservation_of_integrity` is the segment form.
* `Witness.faithful_*` — the spine's `Witness.witness` (a disciplined trace) carries a
  ledger satisfying the full hypothesis package: the nonvacuity witness.
* `Witness.hollow_*` — **the countermodel.** The same disciplined trace with the
  disposal's successor carrying `⊥`: every clause of `LocalConservation 1` holds except
  `carry_complete`, and the account changes. Structural Integrity cannot see the
  difference between `faithful` and `hollow`, because they are ledgers over one trace.

**What is not claimed.** Anything about which ledger a realization in fact carries;
that the load functions are computable from representations (that is semantic
authentication, a hypothesis here); anything about `Met`, attention, or service.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.NormativeContinuity

namespace Workspace.Normativity.Contrib.HistoryIntegrity

open Classical Relation Finset
open Workspace.Normativity.Contrib.NormativeContinuity
open Workspace.Normativity.Contrib.NormativeContinuity.TraceData
open Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace

noncomputable section

variable {Q D S A : Type*}

/-! ## 1. Structural facts of the spine that the fate theorem uses -/

section Structural

variable (T : DefeatTrace Q D S A)

/-- Once resolved, never outstanding again. -/
theorem not_out_after_res {q : Q} {k : ℕ} (hres : q ∈ T.Res k) :
    ∀ n, k < n → q ∉ T.O n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hkn hmem
    rw [T.resolution_continuity n] at hmem
    rcases mem_union.1 hmem with h | h
    · obtain ⟨hO, hnres⟩ := mem_sdiff.1 h
      rcases Nat.lt_or_ge k n with hlt | hge
      · exact ih hlt hO
      · have : k = n := by omega
        subst this
        exact hnres hres
    · obtain ⟨j, hj, hqj⟩ := T.out_born q k (T.res_subset k hres)
      have := T.born_unique q j n hqj h
      omega

/-- **Resolution position is unique.** -/
theorem res_unique {q : Q} {k k' : ℕ} (h : q ∈ T.Res k) (h' : q ∈ T.Res k') : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact not_out_after_res T h k' hlt (T.res_subset k' h')
  · exact not_out_after_res T h' k hgt (T.res_subset k h)

/-- `dispose_not_met` with its uniqueness hypothesis discharged by `res_unique`. -/
theorem dispose_not_met' {n k : ℕ} {d : D} {t : Q} {G : Finset (Ground Q S)}
    (ht : t ∈ T.roots d) (hres : t ∈ T.Res k) (hk : T.kind k t = Kind.dispose G)
    (hn : T.Met n d) : False :=
  T.dispose_not_met ht hk (fun _ hj => res_unique T hj hres) hn

/-- Between birth and resolution an issue is outstanding. -/
theorem out_or_res {q : Q} {j : ℕ} (hq : q ∈ T.Born j) :
    ∀ n, j < n → q ∈ T.O n ∨ ∃ k, j < k ∧ k < n ∧ q ∈ T.Res k := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hjn
    rcases Nat.lt_or_ge j n with hlt | hge
    · rcases ih hlt with hO | ⟨k, hk1, hk2, hk⟩
      · by_cases hres : q ∈ T.Res n
        · exact Or.inr ⟨n, hlt, by omega, hres⟩
        · left
          rw [T.resolution_continuity n]
          exact mem_union_left _ (mem_sdiff.2 ⟨hO, hres⟩)
      · exact Or.inr ⟨k, hk1, by omega, hk⟩
    · have : j = n := by omega
      subst this
      left
      rw [T.resolution_continuity j]
      exact mem_union_right _ hq

/-- **Token trichotomy.** After its birth an issue is outstanding, or discharged at a
unique earlier position, or disposed at a unique earlier position with a successor born
there. Uniqueness is `res_unique`; exclusion of the first from the other two is
`not_out_after_res`; the last two exclude each other because a kind is one constructor.
This uses only the structural fields of the trace. -/
theorem token_fate {q : Q} {j n : ℕ} (hq : q ∈ T.Born j) (hjn : j < n) :
    q ∈ T.O n ∨
    (∃ k, j < k ∧ k < n ∧ q ∈ T.Res k ∧ (T.kind k q).Discharges) ∨
    (∃ k G, j < k ∧ k < n ∧ q ∈ T.Res k ∧ T.kind k q = Kind.dispose G ∧
      ∃ q' ∈ T.Born k, q ∈ T.par q') := by
  rcases out_or_res T hq n hjn with hO | ⟨k, hk1, hk2, hres⟩
  · exact Or.inl hO
  · right
    rcases hkind : T.kind k q with _ | G | s
    · exact Or.inl ⟨k, hk1, hk2, hres, by rw [hkind]; trivial⟩
    · exact Or.inr ⟨k, G, hk1, hk2, hres, hkind, T.dispose_successor k q G hres hkind⟩
    · exact Or.inl ⟨k, hk1, hk2, hres, by rw [hkind]; trivial⟩

/-- The three fates exclude one another: an outstanding issue was not resolved earlier,
and a discharged issue was not disposed at any position. -/
theorem fate_exclusive {q : Q} {n : ℕ} :
    (q ∈ T.O n → ¬ ∃ k, k < n ∧ q ∈ T.Res k) ∧
    (∀ k k' G, q ∈ T.Res k → (T.kind k q).Discharges → q ∈ T.Res k' →
      T.kind k' q ≠ Kind.dispose G) := by
  refine ⟨fun hO ⟨k, hk, hres⟩ => not_out_after_res T hres n hk hO, ?_⟩
  intro k k' G hk hdis hk' heq
  have := res_unique T hk hk'
  subst this
  rw [heq] at hdis
  simp [Kind.Discharges] at hdis

/-- A fresh issue's ancestry passes through a parent: `anc m q` with `q ≠ m` means some
parent of `q` descends from `m`. -/
theorem anc_through_parent {m q : Q} (h : T.anc m q) : q = m ∨ ∃ p ∈ T.par q, T.anc m p := by
  rcases ReflTransGen.cases_tail h with h | ⟨c, hmc, hcq⟩
  · exact Or.inl h
  · exact Or.inr ⟨c, hcq, hmc⟩

end Structural

/-! ## 2. Slice ledgers and the transition-local conservation clause -/

/-- The three kinds as predicates, for filtering a resolution batch. -/
def isAnswer (k : Kind Q S) : Prop := k = Kind.answer
def isSettle (k : Kind Q S) : Prop := ∃ s, k = Kind.settle s
def isDispose (k : Kind Q S) : Prop := ∃ G, k = Kind.dispose G

lemma kind_trichotomy (k : Kind Q S) : isAnswer k ∨ isSettle k ∨ isDispose k := by
  cases k with
  | answer => exact Or.inl rfl
  | dispose G => exact Or.inr (Or.inr ⟨G, rfl⟩)
  | settle s => exact Or.inr (Or.inl ⟨s, rfl⟩)

/-- A **slice ledger** for one anchored slice: the load each issue carries at each
prefix, in the slice's anchored domain `L`, and the accumulated receipts. `L` is a
join-semilattice with bottom, which is all the carriers round's algebra used. -/
structure SliceLedger (T : DefeatTrace Q D S A) (L : Type*) [SemilatticeSup L] [OrderBot L]
    where
  lam : ℕ → Q → L
  sat : ℕ → L
  stl : ℕ → L

namespace SliceLedger

variable {L : Type*} [SemilatticeSup L] [OrderBot L]
variable {T : DefeatTrace Q D S A} (Λ : SliceLedger T L)

/-- The fresh issues of batch `n` that inherit from `p`. -/
def children (T : DefeatTrace Q D S A) (n : ℕ) (p : Q) : Finset Q :=
  (T.Born n).filter (fun q' => p ∈ T.par q')

/-- **The transition-local conservation clause** at position `n`. Everything here reads
the pre-state `n` and the post-state `n + 1` and nothing else.

* `identity_frame` — an outstanding issue not resolved in the batch keeps its load.
* `incoming_sound` — a fresh issue carries no more than the join of its parents' loads
  (a genesis issue therefore carries `⊥` of every slice already open: no accretion).
* `carry_complete` — a disposed issue's load is covered by its children's loads.
* `closure_certificate` — settlement availability and the internal judgment that it
  closes this issue are both present; neither is inferred from the other.
* `sat_receipts`, `stl_receipts` — receipts accumulate exactly the loads of answered
  and settled issues.

There is no clause for disposal receipts: disposal carries, it does not discharge. -/
structure LocalConservation (Closes : ℕ → S → Q → Prop) (n : ℕ) : Prop where
  identity_frame : ∀ q ∈ T.O n, q ∉ T.Res n → Λ.lam (n + 1) q = Λ.lam n q
  incoming_sound : ∀ q' ∈ T.Born n, Λ.lam (n + 1) q' ≤ (T.par q').sup (Λ.lam n)
  carry_complete : ∀ p ∈ T.Res n, isDispose (T.kind n p) →
    Λ.lam n p ≤ (children T n p).sup (Λ.lam (n + 1))
  closure_certificate : ∀ p ∈ T.Res n, isSettle (T.kind n p) →
    ∃ s, T.kind n p = Kind.settle s ∧ T.Settled n s ∧ Closes n s p
  sat_receipts : Λ.sat (n + 1) =
    Λ.sat n ⊔ ((T.Res n).filter (fun p => isAnswer (T.kind n p))).sup (Λ.lam n)
  stl_receipts : Λ.stl (n + 1) =
    Λ.stl n ⊔ ((T.Res n).filter (fun p => isSettle (T.kind n p))).sup (Λ.lam n)

/-- The slice's **account** for matter `m` at `n`: answered ⊔ settlement-discharged ⊔
carried live. -/
def account (n : ℕ) (m : Q) : L := Λ.sat n ⊔ Λ.stl n ⊔ (T.Live n m).sup (Λ.lam n)

/-- **Locality**: outstanding issues outside the matter's ancestry carry `⊥`. -/
def Local (n : ℕ) (m : Q) : Prop := ∀ q ∈ T.O n, ¬ T.anc m q → Λ.lam n q = ⊥

/-- Integrity of the segment `[a, b)`: every step in it satisfies the local clause. -/
def Integrity (Closes : ℕ → S → Q → Prop) (a b : ℕ) : Prop :=
  ∀ i, a ≤ i → i < b → Λ.LocalConservation Closes i

theorem integrity_refl (Closes : ℕ → S → Q → Prop) (a : ℕ) : Λ.Integrity Closes a a :=
  fun _ h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

/-- **Segments concatenate.** Trivial, and stated because that is exactly what a local
clause buys: nothing about a segment is checked that is not checked at its steps. -/
theorem integrity_compose {Closes : ℕ → S → Q → Prop} {a b c : ℕ}
    (h1 : Λ.Integrity Closes a b) (h2 : Λ.Integrity Closes b c) :
    Λ.Integrity Closes a c := by
  intro i hai hic
  rcases Nat.lt_or_ge i b with hib | hbi
  · exact h1 i hai hib
  · exact h2 i hbi hic

theorem integrity_mono {Closes : ℕ → S → Q → Prop} {a b a' b' : ℕ}
    (h : Λ.Integrity Closes a b) (ha : a ≤ a') (hb : b' ≤ b) :
    Λ.Integrity Closes a' b' := fun i h1 h2 => h i (ha.trans h1) (lt_of_lt_of_le h2 hb)

/-- A resolved issue of the batch is outstanding, and if it descends from `m` it is live. -/
lemma mem_live_of_res {n : ℕ} {m p : Q} (hp : p ∈ T.Res n) (hanc : T.anc m p) :
    p ∈ T.Live n m :=
  mem_filter.2 ⟨T.res_subset n hp, hanc⟩

/-- Under the local clause a slice's locality persists. -/
theorem local_succ {Closes : ℕ → S → Q → Prop} {n : ℕ} {m : Q}
    (hs : Λ.LocalConservation Closes n) (hl : Λ.Local n m) :
    Λ.Local (n + 1) m := by
  intro q hq hnanc
  rw [T.resolution_continuity n] at hq
  rcases mem_union.1 hq with h | h
  · obtain ⟨hO, hnres⟩ := mem_sdiff.1 h
    rw [hs.identity_frame q hO hnres]
    exact hl q hO hnanc
  · apply le_bot_iff.1
    refine (hs.incoming_sound q h).trans ?_
    apply Finset.sup_le
    intro p hp
    have hpres : p ∈ T.Res n := T.fresh_successors n q h p hp
    have hpanc : ¬ T.anc m p := fun hmp => hnanc (hmp.tail hp)
    rw [hl p (T.res_subset n hpres) hpanc]

/-- **One step of conservation.** -/
theorem account_succ {Closes : ℕ → S → Q → Prop} {n : ℕ} {m : Q}
    (hs : Λ.LocalConservation Closes n) (hl : Λ.Local n m) :
    Λ.account (n + 1) m = Λ.account n m := by
  -- a resolved issue's load is below the live join, or is ⊥
  have hres_le : ∀ p ∈ T.Res n, Λ.lam n p ≤ (T.Live n m).sup (Λ.lam n) := by
    intro p hp
    by_cases hanc : T.anc m p
    · exact Finset.le_sup (mem_live_of_res hp hanc)
    · rw [hl p (T.res_subset n hp) hanc]; exact bot_le
  apply le_antisymm
  · -- ≤ : everything at n+1 is accounted for at n
    unfold account
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [hs.sat_receipts]
      refine sup_le (le_sup_left.trans le_sup_left) ?_
      refine le_sup_right.trans' ?_
      apply Finset.sup_le
      intro p hp
      exact hres_le p (mem_filter.1 hp).1
    · rw [hs.stl_receipts]
      refine sup_le (le_sup_right.trans le_sup_left) ?_
      refine le_sup_right.trans' ?_
      apply Finset.sup_le
      intro p hp
      exact hres_le p (mem_filter.1 hp).1
    · apply Finset.sup_le
      intro q hq
      obtain ⟨hqO, hqanc⟩ := mem_filter.1 hq
      rw [T.resolution_continuity n] at hqO
      rcases mem_union.1 hqO with h | h
      · obtain ⟨hO, hnres⟩ := mem_sdiff.1 h
        rw [hs.identity_frame q hO hnres]
        exact le_sup_right.trans' (Finset.le_sup (mem_filter.2 ⟨hO, hqanc⟩))
      · refine (hs.incoming_sound q h).trans ?_
        refine le_sup_right.trans' ?_
        apply Finset.sup_le
        intro p hp
        exact hres_le p (T.fresh_successors n q h p hp)
  · -- ≥ : everything at n is accounted for at n+1
    unfold account
    have hsat : Λ.sat n ≤ Λ.sat (n + 1) := by rw [hs.sat_receipts]; exact le_sup_left
    have hstl : Λ.stl n ≤ Λ.stl (n + 1) := by rw [hs.stl_receipts]; exact le_sup_left
    refine sup_le (sup_le (le_sup_left.trans' (le_sup_left.trans' hsat))
      (le_sup_left.trans' (le_sup_right.trans' hstl))) ?_
    apply Finset.sup_le
    intro q hq
    obtain ⟨hqO, hqanc⟩ := mem_filter.1 hq
    by_cases hres : q ∈ T.Res n
    · rcases kind_trichotomy (T.kind n q) with hk | hk | hk
      · -- answered: into sat
        have : Λ.lam n q ≤ Λ.sat (n + 1) := by
          rw [hs.sat_receipts]
          exact le_sup_right.trans' (Finset.le_sup (mem_filter.2 ⟨hres, hk⟩))
        exact le_sup_left.trans' (le_sup_left.trans' this)
      · -- settled: into stl
        have : Λ.lam n q ≤ Λ.stl (n + 1) := by
          rw [hs.stl_receipts]
          exact le_sup_right.trans' (Finset.le_sup (mem_filter.2 ⟨hres, hk⟩))
        exact le_sup_left.trans' (le_sup_right.trans' this)
      · -- disposed: carried by children, which are live at n+1
        refine (hs.carry_complete q hres hk).trans ?_
        refine le_sup_right.trans' ?_
        apply Finset.sup_le
        intro q' hq'
        obtain ⟨hborn, hpar⟩ := mem_filter.1 hq'
        have hlive : q' ∈ T.Live (n + 1) m := by
          refine mem_filter.2 ⟨?_, hqanc.tail hpar⟩
          rw [T.resolution_continuity n]
          exact mem_union_right _ hborn
        exact Finset.le_sup hlive
    · -- unresolved: identity frame
      have hlive : q ∈ T.Live (n + 1) m := by
        refine mem_filter.2 ⟨?_, hqanc⟩
        rw [T.resolution_continuity n]
        exact mem_union_left _ (mem_sdiff.2 ⟨hqO, hres⟩)
      refine le_sup_right.trans' ?_
      rw [← hs.identity_frame q hqO hres]
      exact Finset.le_sup hlive

/-- **Three-fate conservation, segment form.** Integrity of `[n₀, n)` together with
locality at `n₀` keeps the account constant across the segment and locality at its end:
what the slice owed at `n₀` is at `n` exactly answered ⊔ settlement-discharged ⊔ carried
live. -/
theorem conservation_segment (Closes : ℕ → S → Q → Prop) (m : Q) {n₀ n : ℕ}
    (hl : Λ.Local n₀ m) (hn : n₀ ≤ n) (hI : Λ.Integrity Closes n₀ n) :
    Λ.account n m = Λ.account n₀ m ∧ Λ.Local n m := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨rfl, hl⟩
  | succ k hk ih =>
    obtain ⟨hacc, hloc⟩ := ih (Λ.integrity_mono hI le_rfl (Nat.le_succ k))
    have hstep := hI k hk (Nat.lt_succ_self k)
    exact ⟨(Λ.account_succ hstep hloc).trans hacc, Λ.local_succ hstep hloc⟩

/-- The unbounded form: the local clause at every step from `n₀` on. -/
theorem conservation (Closes : ℕ → S → Q → Prop) (m : Q) (n₀ : ℕ) (hl : Λ.Local n₀ m)
    (hs : ∀ n, n₀ ≤ n → Λ.LocalConservation Closes n) :
    ∀ n, n₀ ≤ n → Λ.account n m = Λ.account n₀ m :=
  fun _ hn => (Λ.conservation_segment Closes m hl hn (fun i hi _ => hs i hi)).1

end SliceLedger

/-! ## 3. Witnesses over the spine's disciplined trace

`NormativeContinuity.Witness.witness` is a `DefeatTrace` proved `Disciplined`: five issues,
one answered, one settled, one (`dis`) disposed at position 1 into the fresh successor
`dis1`. Two ledgers are placed on it for the matter `dis`, with `Prop` as the anchored
domain (`⊥ = False`, `⊔ = ∨`, `≤ = →`): `dis` carries the slice at position 1, and the
question is what `dis1` carries afterwards. -/

namespace Witness

open Workspace.Normativity.Contrib.NormativeContinuity.Witness
open Workspace.Normativity.Contrib.NormativeContinuity.Witness.WQ

/-- **Faithful carry.** The successor carries the slice from position 2 on. -/
def faithful : SliceLedger witness Prop where
  lam n q := (q = dis ∧ n = 1) ∨ (q = dis1 ∧ 2 ≤ n)
  sat _ := False
  stl _ := False

/-- **Hollow carry.** The successor is born, fresh, routed, answerably grounded — and
carries nothing. -/
def hollow : SliceLedger witness Prop where
  lam n q := q = dis ∧ n = 1
  sat _ := False
  stl _ := False

/-- Both ledgers sit on one trace, and that trace is defeat-disciplined
(`NormativeContinuity.Witness.witness_disciplined`). -/
theorem same_trace_disciplined :
    witness.Disciplined wlic (fun _ => ()) (fun _ => ()) (fun _ => ()) :=
  witness_disciplined

lemma mem_res_iff {q : WQ} {n : ℕ} :
    q ∈ witness.Res n ↔ n = 1 ∧ (q = ans ∨ q = stl ∨ q = dis) := by
  rw [witness_Res, mem_wRes]
  cases q <;> simp [resAt, Resolves] <;> omega

lemma mem_born_iff {q : WQ} {n : ℕ} :
    q ∈ witness.Born n ↔ (n = 0 ∧ q ≠ dis1) ∨ (n = 1 ∧ q = dis1) := by
  rw [witness_Born, mem_wBorn]
  cases q <;> simp [bornAt] <;> omega

lemma mem_O_iff {q : WQ} {n : ℕ} :
    q ∈ witness.O n ↔ (1 ≤ n ∧ (q = lic ∨ ((q = ans ∨ q = stl ∨ q = dis) ∧ n ≤ 1))) ∨
      (2 ≤ n ∧ q = dis1) := by
  rw [witness_O, mem_wO]
  cases q <;> simp [bornAt, resAt, Resolves] <;> omega

/-- Ancestry of `dis` is `{dis, dis1}`. -/
lemma anc_dis {q : WQ} (h : witness.anc dis q) : q = dis ∨ q = dis1 := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b c _ hstep _ =>
    have hb : b ∈ wpar c := hstep
    cases c <;> simp [wpar] at hb
    exact Or.inr rfl

lemma anc_dis_dis1 : witness.anc dis dis1 :=
  ReflTransGen.single (show dis ∈ wpar dis1 by simp [wpar])

lemma children_dis : SliceLedger.children witness 1 dis = {dis1} := by
  ext q
  simp only [SliceLedger.children, mem_filter, mem_born_iff, mem_singleton, witness_par]
  cases q <;> simp [wpar]

/-- The answer filter at position 1 is `{ans}` and the settle filter is `{stl}`; at every
other position both are empty. -/
lemma answer_filter (n : ℕ) :
    (witness.Res n).filter (fun p => isAnswer (witness.kind n p)) =
      if n = 1 then {ans} else ∅ := by
  ext q
  simp only [mem_filter, mem_res_iff, witness_kind, isAnswer]
  split_ifs with h
  · subst h; cases q <;> simp [wkind]
  · simp [h]

lemma settle_filter (n : ℕ) :
    (witness.Res n).filter (fun p => isSettle (witness.kind n p)) =
      if n = 1 then {stl} else ∅ := by
  ext q
  simp only [mem_filter, mem_res_iff, witness_kind, isSettle]
  split_ifs with h
  · subst h; cases q <;> simp [wkind]
  · simp [h]

/-- Receipts stay `False` on either ledger: nothing answered or settled carries the
slice. Stated for any `lam` that is `False` on `ans` and `stl`. -/
lemma receipts_false {lam : ℕ → WQ → Prop} (hans : ∀ n, ¬ lam n ans) (hstl : ∀ n, ¬ lam n stl)
    (n : ℕ) :
    (False = (False ⊔ ((witness.Res n).filter (fun p => isAnswer (witness.kind n p))).sup (lam n)))
    ∧ (False = (False ⊔ ((witness.Res n).filter (fun p => isSettle (witness.kind n p))).sup (lam n))) := by
  rw [answer_filter, settle_filter]
  constructor <;> apply propext <;> refine ⟨False.elim, fun h => ?_⟩ <;>
    rcases h with h | h <;> try exact h
  · split_ifs at h with hn
    · rw [Finset.sup_singleton] at h; exact hans n h
    · rw [Finset.sup_empty] at h; exact h
  · split_ifs at h with hn
    · rw [Finset.sup_singleton] at h; exact hstl n h
    · rw [Finset.sup_empty] at h; exact h

/-! ### The faithful ledger inhabits the full hypothesis package -/

theorem faithful_local : faithful.Local 1 dis := by
  intro q hq hnanc
  apply eq_false
  rintro (⟨rfl, -⟩ | ⟨-, h⟩)
  · exact hnanc ReflTransGen.refl
  · omega

theorem faithful_step (n : ℕ) (hn : 1 ≤ n) :
    faithful.LocalConservation (fun _ _ _ => True) n where
  identity_frame := by
    intro q hq hnres
    rw [mem_O_iff] at hq
    rw [mem_res_iff] at hnres
    show ((q = dis ∧ n + 1 = 1) ∨ (q = dis1 ∧ 2 ≤ n + 1)) = ((q = dis ∧ n = 1) ∨ (q = dis1 ∧ 2 ≤ n))
    apply propext
    cases q <;> simp at hq hnres ⊢ <;> omega
  incoming_sound := by
    intro q' hq'
    rw [mem_born_iff] at hq'
    rcases hq' with ⟨h0, -⟩ | ⟨h1, rfl⟩
    · omega
    · subst h1
      rw [witness_par, show wpar dis1 = {dis} from rfl, Finset.sup_singleton]
      intro _
      exact Or.inl ⟨rfl, rfl⟩
  carry_complete := by
    intro p hp hdis
    rw [mem_res_iff] at hp
    obtain ⟨rfl, hp⟩ := hp
    obtain ⟨G, hG⟩ := hdis
    rw [witness_kind] at hG
    rcases hp with rfl | rfl | rfl
    · simp [wkind] at hG
    · simp [wkind] at hG
    · rw [children_dis, Finset.sup_singleton]
      intro _
      exact Or.inr ⟨rfl, le_refl 2⟩
  closure_certificate := by
    intro p hp hstl
    rw [mem_res_iff] at hp
    obtain ⟨rfl, hp⟩ := hp
    obtain ⟨s, hs⟩ := hstl
    rw [witness_kind] at hs
    rcases hp with rfl | rfl | rfl
    · simp [wkind] at hs
    · rcases s with ⟨⟩
      exact ⟨(), by simpa [wkind] using hs, by change 1 ≤ 1; omega, trivial⟩
    · simp [wkind] at hs
  sat_receipts := (receipts_false (lam := faithful.lam) (by simp [faithful]) (by simp [faithful]) n).1
  stl_receipts := (receipts_false (lam := faithful.lam) (by simp [faithful]) (by simp [faithful]) n).2

/-- **Nonvacuity of `conservation`.** The faithful ledger conserves the account. -/
theorem faithful_conserves : ∀ n, 1 ≤ n → faithful.account n dis = faithful.account 1 dis :=
  faithful.conservation (fun _ _ _ => True) dis 1 faithful_local (fun n hn => faithful_step n hn)

/-! ### The hollow ledger fails by exactly one clause -/

theorem hollow_local : hollow.Local 1 dis := by
  intro q hq hnanc
  apply eq_false
  rintro ⟨rfl, -⟩
  exact hnanc ReflTransGen.refl

/-- Every clause of `LocalConservation 1` except `carry_complete` holds of `hollow`. -/
theorem hollow_other_clauses :
    (∀ q ∈ witness.O 1, q ∉ witness.Res 1 → hollow.lam 2 q = hollow.lam 1 q) ∧
    (∀ q' ∈ witness.Born 1, hollow.lam 2 q' ≤ (witness.par q').sup (hollow.lam 1)) ∧
    (hollow.sat 2 = hollow.sat 1 ⊔
      ((witness.Res 1).filter (fun p => isAnswer (witness.kind 1 p))).sup (hollow.lam 1)) ∧
    (hollow.stl 2 = hollow.stl 1 ⊔
      ((witness.Res 1).filter (fun p => isSettle (witness.kind 1 p))).sup (hollow.lam 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq hnres
    rw [mem_O_iff] at hq
    rw [mem_res_iff] at hnres
    show (q = dis ∧ 2 = 1) = (q = dis ∧ 1 = 1)
    apply propext
    cases q <;> simp at hq hnres ⊢
  · intro q' hq'
    rw [mem_born_iff] at hq'
    rcases hq' with ⟨h0, -⟩ | ⟨-, rfl⟩
    · omega
    · rintro ⟨h, -⟩
      exact absurd h (by simp)
  · exact (receipts_false (lam := hollow.lam) (by simp [hollow]) (by simp [hollow]) 1).1
  · exact (receipts_false (lam := hollow.lam) (by simp [hollow]) (by simp [hollow]) 1).2

/-- **The clause that fails.** The disposed issue's load is not covered by its children. -/
theorem hollow_carry_fails :
    ¬ (hollow.lam 1 dis ≤ (SliceLedger.children witness 1 dis).sup (hollow.lam 2)) := by
  rw [children_dis, Finset.sup_singleton]
  intro h
  have : hollow.lam 2 dis1 := h ⟨rfl, rfl⟩
  obtain ⟨h1, -⟩ := this
  exact absurd h1 (by simp)

theorem hollow_not_step : ¬ hollow.LocalConservation (fun _ _ _ => True) 1 :=
  fun h => hollow_carry_fails (h.carry_complete dis (mem_res_iff.2 ⟨rfl, Or.inr (Or.inr rfl)⟩)
    ⟨wG, rfl⟩)

/-- **The fourth fate for content.** At position 1 the account carries the slice; at
position 2 it does not — nothing was answered, nothing settled, and the live successor
is empty. -/
theorem hollow_account_1 : hollow.account 1 dis := by
  unfold SliceLedger.account
  exact Or.inr (Finset.le_sup (f := hollow.lam 1)
    (mem_filter.2 ⟨mem_O_iff.2 (Or.inl ⟨le_refl 1, Or.inr ⟨Or.inr (Or.inr rfl), le_refl 1⟩⟩),
      ReflTransGen.refl⟩) ⟨rfl, rfl⟩)

theorem hollow_account_2 : ¬ hollow.account 2 dis := by
  unfold SliceLedger.account
  rintro ((h | h) | h)
  · exact h
  · exact h
  · refine (Finset.sup_le (fun q hq => ?_) : (witness.Live 2 dis).sup (hollow.lam 2) ≤ False) h
    obtain ⟨hO, -⟩ := mem_filter.1 hq
    rintro ⟨rfl, h2⟩
    rw [mem_O_iff] at hO
    omega

theorem hollow_account_changes : hollow.account 2 dis ≠ hollow.account 1 dis :=
  fun h => hollow_account_2 (h ▸ hollow_account_1)

end Witness

end

end Workspace.Normativity.Contrib.HistoryIntegrity

#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.not_out_after_res
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.res_unique
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.dispose_not_met'
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.out_or_res
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.token_fate
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.fate_exclusive
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.anc_through_parent
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.kind_trichotomy
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.SliceLedger.integrity_refl
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.SliceLedger.integrity_compose
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.SliceLedger.integrity_mono
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.SliceLedger.mem_live_of_res
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.SliceLedger.local_succ
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.SliceLedger.account_succ
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.SliceLedger.conservation_segment
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.SliceLedger.conservation
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.same_trace_disciplined
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.mem_res_iff
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.mem_born_iff
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.mem_O_iff
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.anc_dis
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.anc_dis_dis1
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.children_dis
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.answer_filter
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.settle_filter
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.receipts_false
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.faithful_local
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.faithful_step
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.faithful_conserves
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.hollow_local
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.hollow_other_clauses
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.hollow_carry_fails
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.hollow_not_step
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.hollow_account_1
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.hollow_account_2
#print axioms Workspace.Normativity.Contrib.HistoryIntegrity.Witness.hollow_account_changes
