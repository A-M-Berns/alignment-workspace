/-
# Normative Continuity: the structural theorem spine

Formalizes the structural half of *Normative Continuity under Self-Revision*
(`projects/normativity/legitimacy/rounds/2026-08-29-normative-continuity-concordance/NORMATIVE_CONTINUITY.tex`,
checkpoint `AGENT-CONSOLIDATED`, 29 August 2026). The semantic judgments (`Met`, and
implicitly `Resolve`, `AddPre`, `DropPre`, `Designate`) enter only through the recorded
sets they produce; `Permit`, `Due`, `Continue` do not appear, because no theorem here
reads them.

**What is proved.**

* `IssueTrace.persistent_wait` — the Persistent-Wait Theorem (paper Theorem 2), from
  Requirements 4, 5, 7, 8, 9, 10, 12 and finite batches, exactly as the proof-pass
  dependency audit claimed. The five paper steps are the lemmas `not_res_of_reach`,
  `live_succ_eq` / `pre_succ_subset` / `routes_succ_eq` / `reach_succ_subset` (Step 2),
  `finset_antitone_stabilizes` (Step 3), `exists_sink` (Step 4), and
  `routes_empty_persistent` (Step 5, the repaired route-extinction lemma).
* `IssueTrace.persistent_opportunity` — paper Theorem 3, parameterized over
  `WaitResponsive`.
* `IssueTrace.no_structural_abandonment` — paper Theorem 4, parameterized over
  `NonStarving`; the unit-budget constraints on attention are not needed for it.
* `StandingTrace.grounded_replay` — paper Theorem 1, from Requirement 1 alone. The
  freshness clause `StandingTrace.Fresh` is stated and not consumed.
* `anchor_grounded` — the one place the standing layer meets the issue layer
  (Requirement 2).
* Fixtures: `Fixtures.fixA_*` is the rotating-prerequisite countermodel — the
  ownership-only gate admits it (`fixA_live_gate_holds`), the Persistent-Wait
  conclusion fails on it (`fixA_persistent_wait_fails`), the reach gate rejects it
  (`fixA_reach_gate_fails`), and every other requirement holds
  (`fixA_other_requirements`). `fixB_routes` shows the unqualified route-extinction
  lemma is false at a prerequisite's introduction position; `fixE_cycle_is_work` shows a
  two-node waiting cycle counts as work.

**What is not claimed.** That the matter construction `M_n` of the paper is the only one
satisfying `matters_mono`/`matters_prior`; that wait responsiveness or non-starvation hold
of anything; anything about `Permit`, `Due`, `Continue`, checkers, Proper Exercise, or
Legitimate Improvement.

Names are provisional (`AGENTS.md` standard 6).
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.DeriveFintype

namespace Workspace.Normativity.Contrib.NormativeContinuity

open Classical Relation Finset

noncomputable section

/-! ## 1. Issue traces -/

/-- Raw data of an issue/prerequisite/matter trace, positions indexed by `ℕ`.
`O n` is the outstanding set at prefix `n`, `Res n` the issues resolved in batch `n`,
`Born n` the issues opened in batch `n`, `par q` the parents of `q` (immutable),
`Pre n q` the active prerequisites of `q` at prefix `n`, `PreAdd n q` / `PreDrop n q`
the prerequisite occurrences added to / withdrawn from `q` in batch `n`, `roots d`
the route roots `T_d`, `intro d` the position of `d`'s introducing record, `Met n d`
the satisfaction judgment at prefix `n`, and `M n` the matters existing at prefix `n`. -/
structure TraceData (Q D : Type*) where
  O : ℕ → Finset Q
  Res : ℕ → Finset Q
  Born : ℕ → Finset Q
  par : Q → Finset Q
  Pre : ℕ → Q → Finset D
  PreAdd : ℕ → Q → Finset D
  PreDrop : ℕ → Q → Finset D
  roots : D → Finset Q
  intro : D → ℕ
  Met : ℕ → D → Prop
  M : ℕ → Finset Q

variable {Q D : Type*}

namespace TraceData

variable (T : TraceData Q D)

/-- `p → q`: `p` resolved into `q`. -/
def succ (p q : Q) : Prop := p ∈ T.par q

/-- `m ⪯ q`: reflexive-transitive successor ancestry. -/
def anc : Q → Q → Prop := ReflTransGen T.succ

/-- `Live_n(m)`. -/
def Live (n : ℕ) (m : Q) : Finset Q := (T.O n).filter (fun q => T.anc m q)

/-- `Routes_n(d)`. -/
def Routes (n : ℕ) (d : D) : Finset Q := (T.O n).filter (fun r => ∃ t ∈ T.roots d, T.anc t r)

/-- `Ready_n(q)`. -/
def Ready (n : ℕ) (q : Q) : Prop := ∀ d ∈ T.Pre n q, T.Met n d

/-- `q ⇝_n r`: `q` waits through `r`. -/
def waits (n : ℕ) (q r : Q) : Prop := ∃ d ∈ T.Pre n q, ¬ T.Met n d ∧ r ∈ T.Routes n d

/-- `Reach_n(m)`: least set containing `Live_n(m)` and closed under `⇝_n`, cut down to
`O n` (which it lies in anyway since routes are outstanding). -/
def Reach (n : ℕ) (m : Q) : Finset Q :=
  (T.O n).filter (fun r => ∃ q ∈ T.Live n m, ReflTransGen (T.waits n) q r)

/-- `q` lies on a `⇝_n`-cycle (self-loops included). -/
def onCycle (n : ℕ) (q : Q) : Prop := TransGen (T.waits n) q q

/-- `Work_n(m)`. -/
def Work (n : ℕ) (m : Q) : Finset Q :=
  (T.Reach n m).filter (fun q => T.Ready n q ∨ T.onCycle n q)

/-- `o_n(m) = 1`. -/
def opp (n : ℕ) (m : Q) : Prop := m ∈ T.M n ∧ (T.Work n m).Nonempty

/-- `Ω_N(m)`. -/
def Omega (N : ℕ) (m : Q) : ℕ := ((range N).filter (fun n => T.opp n m)).card

/-- `d ∈ NoRoute_n(m)`. -/
def NoRouteWait (n : ℕ) (m : Q) (d : D) : Prop :=
  ∃ q ∈ T.Reach n m, d ∈ T.Pre n q ∧ ¬ T.Met n d ∧ T.Routes n d = ∅

lemma live_subset_reach (n : ℕ) (m : Q) : T.Live n m ⊆ T.Reach n m := by
  intro q hq
  have hO : q ∈ T.O n := (mem_filter.1 hq).1
  exact mem_filter.2 ⟨hO, q, hq, ReflTransGen.refl⟩

lemma reach_subset_O (n : ℕ) (m : Q) : T.Reach n m ⊆ T.O n := filter_subset _ _

lemma live_subset_O (n : ℕ) (m : Q) : T.Live n m ⊆ T.O n := filter_subset _ _

lemma routes_subset_O (n : ℕ) (d : D) : T.Routes n d ⊆ T.O n := filter_subset _ _

/-- Routes of an unmet prerequisite of a reachable issue are reachable. -/
lemma mem_reach_of_waits {n : ℕ} {m q r : Q} (hq : q ∈ T.Reach n m) (h : T.waits n q r) :
    r ∈ T.Reach n m := by
  obtain ⟨hO, q0, hq0, hpath⟩ := mem_filter.1 hq
  have h' := h
  obtain ⟨d, _, _, hr⟩ := h
  exact mem_filter.2 ⟨T.routes_subset_O n d hr, q0, hq0, hpath.tail h'⟩

end TraceData

/-- An issue trace satisfying exactly the structural requirements the Persistent-Wait
Theorem uses: resolution continuity (4), fresh successors (5), prerequisite continuity
(7), no future route roots (8), persistent satisfaction (9), only ready issues resolve
(10), the reach-gated no-rewiring rule (12), plus the bookkeeping facts that positions
are a list (issues and prerequisite occurrences are born once, before they are
outstanding) and that matters are prior issues that persist. Standing-at-opening (2),
new-demands-become-issues (3), state continuity (6) and non-starvation (11) are not
here because no theorem in this file about issue traces uses them. -/
structure IssueTrace (Q D : Type*) extends TraceData Q D where
  born_unique : ∀ q n k, q ∈ Born n → q ∈ Born k → n = k
  born_not_out : ∀ q n, q ∈ Born n → q ∉ O n
  out_born : ∀ q n, q ∈ O n → ∃ j < n, q ∈ Born j
  res_subset : ∀ n, Res n ⊆ O n
  /-- Requirement 4. -/
  resolution_continuity : ∀ n, O (n + 1) = (O n \ Res n) ∪ Born n
  /-- Requirement 5: a parent resolves into its child in the child's birth batch. -/
  fresh_successors : ∀ n q, q ∈ Born n → ∀ p ∈ par q, p ∈ Res n
  /-- Requirement 7, continuing issue. -/
  pre_continuity : ∀ n q, q ∈ O n → q ∈ O (n + 1) →
    Pre (n + 1) q = (Pre n q \ PreDrop n q) ∪ PreAdd n q
  /-- Requirement 7, fresh issue. -/
  pre_fresh : ∀ n q, q ∈ Born n → Pre (n + 1) q = PreAdd n q
  /-- A prerequisite occurrence is the record introducing it: added exactly once, at
  its introduction position. -/
  pre_intro : ∀ n q d, d ∈ PreAdd n q → intro d = n
  /-- Requirement 8. -/
  pre_refs : ∀ n q d, d ∈ PreAdd n q → roots d ⊆ O n ∪ Born n
  /-- Requirement 9. -/
  met_persistent : ∀ n d, Met n d → Met (n + 1) d
  /-- Requirement 10. -/
  ready_resolve : ∀ n q, q ∈ Res n → toTraceData.Ready n q
  matters_mono : ∀ n m, m ∈ M n → m ∈ M (n + 1)
  matters_prior : ∀ n m, m ∈ M n → ∃ j < n, m ∈ Born j
  /-- Requirement 12. -/
  no_rewire : ∀ n q, q ∈ O n → q ∈ O (n + 1) → (PreAdd n q).Nonempty →
    ∀ m ∈ M n, q ∈ toTraceData.Reach n m → (toTraceData.Work n m).Nonempty

namespace IssueTrace

variable (T : IssueTrace Q D)

open TraceData

lemma born_lt_of_out {q : Q} {n j : ℕ} (hq : q ∈ T.O n) (hj : q ∈ T.Born j) : j < n := by
  obtain ⟨i, hi, hqi⟩ := T.out_born q n hq
  rwa [T.born_unique q j i hj hqi]

/-- Parents are outstanding, hence born strictly earlier, at the child's birth. -/
lemma parent_out {p q : Q} {n : ℕ} (hq : q ∈ T.Born n) (hp : p ∈ T.par q) : p ∈ T.O n :=
  T.res_subset n (T.fresh_successors n q hq p hp)

/-- If `m ⪯ q`, `q` is born at `n`, and `m` was born before `n`, the ancestry passes
through a parent of `q` (in particular `m ≠ q`). -/
lemma exists_parent_of_anc {m q : Q} {n j : ℕ} (hanc : T.anc m q) (hq : q ∈ T.Born n)
    (hm : m ∈ T.Born j) (hj : j < n) : ∃ p ∈ T.par q, T.anc m p := by
  rcases ReflTransGen.cases_tail hanc with h | ⟨p, hmp, hpq⟩
  · subst h; exact absurd (T.born_unique _ n j hq hm) (by omega)
  · exact ⟨p, hpq, hmp⟩

/-- Every active prerequisite of an outstanding issue was added, to that issue, at its
introduction position, which is strictly earlier. -/
lemma add_of_mem_pre {n : ℕ} {q : Q} {d : D} (hq : q ∈ T.O n) (hd : d ∈ T.Pre n q) :
    d ∈ T.PreAdd (T.intro d) q ∧ T.intro d < n := by
  induction n with
  | zero => obtain ⟨j, hj, _⟩ := T.out_born q 0 hq; omega
  | succ n ih =>
    rw [T.resolution_continuity n] at hq
    rcases mem_union.1 hq with h | h
    · obtain ⟨hO, _⟩ := mem_sdiff.1 h
      have hq' : q ∈ T.O (n + 1) := by rw [T.resolution_continuity n]; exact mem_union_left _ h
      rw [T.pre_continuity n q hO hq'] at hd
      rcases mem_union.1 hd with h1 | h1
      · obtain ⟨h2, h3⟩ := ih hO (mem_sdiff.1 h1).1
        exact ⟨h2, by omega⟩
      · have := T.pre_intro n q d h1
        exact ⟨by rw [this]; exact h1, by omega⟩
    · rw [T.pre_fresh n q h] at hd
      have := T.pre_intro n q d hd
      exact ⟨by rw [this]; exact hd, by omega⟩

lemma root_born_lt {n : ℕ} {q : Q} {d : D} {t : Q} (hq : q ∈ T.O n) (hd : d ∈ T.Pre n q)
    (ht : t ∈ T.roots d) : ∃ i < n, t ∈ T.Born i := by
  obtain ⟨hadd, hlt⟩ := T.add_of_mem_pre hq hd
  rcases mem_union.1 (T.pre_refs _ q d hadd ht) with h | h
  · obtain ⟨i, hi, hti⟩ := T.out_born t _ h
    exact ⟨i, by omega, hti⟩
  · exact ⟨T.intro d, hlt, h⟩

lemma mem_M_of_le {m : Q} {n0 : ℕ} (hm0 : m ∈ T.M n0) : ∀ n, n0 ≤ n → m ∈ T.M n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hm0
  | succ n _ ih => exact T.matters_mono n m ih

/-- Lemma 6: a reachable resolution is available work. -/
lemma mem_work_of_res {n : ℕ} {m q : Q} (hq : q ∈ T.Reach n m) (hr : q ∈ T.Res n) :
    q ∈ T.Work n m :=
  mem_filter.2 ⟨hq, Or.inl (T.ready_resolve n q hr)⟩

/-- Lemma 3 (route loss is permanent), with the introduction-time hypothesis in the form
"`d` is active on some outstanding issue at `n`". -/
lemma routes_empty_persistent {n : ℕ} {q : Q} {d : D} (hq : q ∈ T.O n) (hd : d ∈ T.Pre n q)
    (h : T.Routes n d = ∅) : ∀ k, n ≤ k → T.Routes k d = ∅ := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h
  | succ k hnk ih =>
    apply eq_empty_of_forall_notMem
    intro r hr
    obtain ⟨hrO, t, ht, hanc⟩ := mem_filter.1 hr
    rw [T.resolution_continuity k] at hrO
    rcases mem_union.1 hrO with h1 | h1
    · have : r ∈ T.Routes k d := mem_filter.2 ⟨(mem_sdiff.1 h1).1, t, ht, hanc⟩
      simp [ih] at this
    · obtain ⟨i, hi, hti⟩ := T.root_born_lt hq hd ht
      obtain ⟨p, hp, hanc'⟩ := T.exists_parent_of_anc hanc h1 hti (by omega)
      have : p ∈ T.Routes k d := mem_filter.2 ⟨T.parent_out h1 hp, t, ht, hanc'⟩
      simp [ih] at this

/-- Lemma 2 (matter continuity): once a matter has no live descendant it never has one. -/
lemma live_empty_persistent {n : ℕ} {m : Q} (hm : m ∈ T.M n) (h : T.Live n m = ∅) :
    ∀ k, n ≤ k → T.Live k m = ∅ := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h
  | succ k hnk ih =>
    have hmk : m ∈ T.M k := by
      clear ih h
      induction k, hnk using Nat.le_induction with
      | base => exact hm
      | succ k _ ih => exact T.matters_mono k m ih
    apply eq_empty_of_forall_notMem
    intro q hq
    obtain ⟨hqO, hanc⟩ := mem_filter.1 hq
    rw [T.resolution_continuity k] at hqO
    rcases mem_union.1 hqO with h1 | h1
    · have : q ∈ T.Live k m := mem_filter.2 ⟨(mem_sdiff.1 h1).1, hanc⟩
      simp [ih] at this
    · obtain ⟨j, hj, hmj⟩ := T.matters_prior k m hmk
      obtain ⟨p, hp, hanc'⟩ := T.exists_parent_of_anc hanc h1 hmj hj
      have : p ∈ T.Live k m := mem_filter.2 ⟨T.parent_out h1 hp, hanc'⟩
      simp [ih] at this

/-! ### Step 2 of the Persistent-Wait proof: after the last opportunity the reachable
structure only shrinks. All lemmas are stated at a single position `n` under the
hypotheses `m ∈ M n` and `Work n m = ∅`. -/

section Shrink

variable {T} {n : ℕ} {m : Q} (hm : m ∈ T.M n) (hW : T.Work n m = ∅)
include hW

/-- Step 1: no reachable issue resolves. -/
lemma not_res_of_reach {q : Q} (hq : q ∈ T.Reach n m) : q ∉ T.Res n := fun hr => by
  have := T.mem_work_of_res hq hr; simp [hW] at this

lemma out_succ_of_reach {q : Q} (hq : q ∈ T.Reach n m) : q ∈ T.O (n + 1) := by
  rw [T.resolution_continuity n]
  exact mem_union_left _ (mem_sdiff.2 ⟨T.reach_subset_O n m hq, not_res_of_reach hW hq⟩)

include hm in
/-- The live lineage is frozen. -/
lemma live_succ_eq : T.Live (n + 1) m = T.Live n m := by
  ext q
  constructor
  · intro hq
    obtain ⟨hqO, hanc⟩ := mem_filter.1 hq
    rw [T.resolution_continuity n] at hqO
    rcases mem_union.1 hqO with h1 | h1
    · exact mem_filter.2 ⟨(mem_sdiff.1 h1).1, hanc⟩
    · obtain ⟨j, hj, hmj⟩ := T.matters_prior n m hm
      obtain ⟨p, hp, hanc'⟩ := T.exists_parent_of_anc hanc h1 hmj hj
      have hpl : p ∈ T.Live n m := mem_filter.2 ⟨T.parent_out h1 hp, hanc'⟩
      exact absurd (T.fresh_successors n q h1 p hp)
        (not_res_of_reach hW (T.live_subset_reach n m hpl))
  · intro hq
    exact mem_filter.2 ⟨out_succ_of_reach hW (T.live_subset_reach n m hq), (mem_filter.1 hq).2⟩

include hm in
/-- Requirement 12 bites: no reachable issue gains a prerequisite. -/
lemma pre_succ_subset {q : Q} (hq : q ∈ T.Reach n m) : T.Pre (n + 1) q ⊆ T.Pre n q := by
  have hO := T.reach_subset_O n m hq
  have hO' := out_succ_of_reach hW hq
  have hadd : T.PreAdd n q = ∅ := by
    by_contra h
    have := T.no_rewire n q hO hO' (nonempty_iff_ne_empty.2 h) m hm hq
    simp [hW] at this
  rw [T.pre_continuity n q hO hO', hadd, union_empty]
  exact sdiff_subset

/-- Route sets of unmet reachable prerequisites are frozen (uses Requirement 8). -/
lemma routes_succ_eq {q : Q} {d : D} (hq : q ∈ T.Reach n m) (hd : d ∈ T.Pre n q)
    (hu : ¬ T.Met n d) : T.Routes (n + 1) d = T.Routes n d := by
  have hO := T.reach_subset_O n m hq
  ext r
  constructor
  · intro hr
    obtain ⟨hrO, t, ht, hanc⟩ := mem_filter.1 hr
    rw [T.resolution_continuity n] at hrO
    rcases mem_union.1 hrO with h1 | h1
    · exact mem_filter.2 ⟨(mem_sdiff.1 h1).1, t, ht, hanc⟩
    · obtain ⟨i, hi, hti⟩ := T.root_born_lt hO hd ht
      obtain ⟨p, hp, hanc'⟩ := T.exists_parent_of_anc hanc h1 hti hi
      have hpr : p ∈ T.Routes n d := mem_filter.2 ⟨T.parent_out h1 hp, t, ht, hanc'⟩
      have hpR : p ∈ T.Reach n m := T.mem_reach_of_waits hq ⟨d, hd, hu, hpr⟩
      exact absurd (T.fresh_successors n r h1 p hp) (not_res_of_reach hW hpR)
  · intro hr
    have hrR : r ∈ T.Reach n m := T.mem_reach_of_waits hq ⟨d, hd, hu, hr⟩
    exact mem_filter.2 ⟨out_succ_of_reach hW hrR, (mem_filter.1 hr).2⟩

include hm in
/-- The reachable set only shrinks (uses Requirement 9 for the edges). -/
lemma reach_succ_subset : T.Reach (n + 1) m ⊆ T.Reach n m := by
  intro r hr
  obtain ⟨-, q0, hq0, hpath⟩ := mem_filter.1 hr
  rw [live_succ_eq hm hW] at hq0
  clear hr
  induction hpath with
  | refl => exact T.live_subset_reach n m hq0
  | tail _ hbc ih =>
    obtain ⟨d, hd, hu, hc⟩ := hbc
    have hd' := pre_succ_subset hm hW ih hd
    have hu' : ¬ T.Met n d := fun h => hu (T.met_persistent n d h)
    rw [routes_succ_eq hW ih hd' hu'] at hc
    exact T.mem_reach_of_waits ih ⟨d, hd', hu', hc⟩

end Shrink

/-! ### Stabilization -/

/-- An antitone `ℕ`-valued sequence is eventually constant. -/
lemma nat_antitone_stabilizes (f : ℕ → ℕ) (h : ∀ n, f (n + 1) ≤ f n) :
    ∃ N, ∀ n, N ≤ n → f n = f N := by
  have hmono : ∀ a b, a ≤ b → f b ≤ f a := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b _ ih => exact (h b).trans ih
  have hex : ∃ v, ∃ n, f n = v := ⟨f 0, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hex
  refine ⟨N, fun n hn => le_antisymm (hmono N n hn) ?_⟩
  rw [hN]
  exact Nat.find_min' hex ⟨n, rfl⟩

/-- An eventually antitone sequence of finsets is eventually constant. -/
lemma finset_antitone_stabilizes {X : Type*} (S : ℕ → Finset X) (n1 : ℕ)
    (h : ∀ n, n1 ≤ n → S (n + 1) ⊆ S n) : ∃ N, n1 ≤ N ∧ ∀ n, N ≤ n → S n = S N := by
  obtain ⟨N, hN⟩ := nat_antitone_stabilizes (fun k => (S (n1 + k)).card)
    (fun k => card_le_card (h (n1 + k) (by omega)))
  refine ⟨n1 + N, by omega, fun n hn => ?_⟩
  have hsub : ∀ a b, n1 ≤ a → a ≤ b → S b ⊆ S a := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact subset_rfl
    | succ b hab ih => exact (h b (by omega)).trans ih
  have h1 := hsub (n1 + N) n (by omega) hn
  have h2 : (S n).card = (S (n1 + N)).card := by
    have := hN (n - n1) (by omega)
    simpa [show n1 + (n - n1) = n by omega] using this
  exact eq_of_subset_of_card_le h1 h2.ge

/-- In a finite set closed under a relation and free of cycles, some element has no
successor. -/
lemma exists_sink {X : Type*} (S : Finset X) (R : X → X → Prop) (hne : S.Nonempty)
    (hclosed : ∀ q ∈ S, ∀ r, R q r → r ∈ S) (hacyc : ∀ q ∈ S, ¬ TransGen R q q) :
    ∃ q ∈ S, ∀ r, ¬ R q r := by
  haveI : Finite S := S.finite_toSet.to_subtype
  let R' : S → S → Prop := fun x y => TransGen R (y : X) (x : X)
  haveI : IsTrans S R' := ⟨fun _ _ _ h1 h2 => h2.trans h1⟩
  haveI : Std.Irrefl R' := ⟨fun x h => hacyc x x.2 h⟩
  have hwf : WellFounded R' := Finite.wellFounded_of_trans_of_irrefl R'
  obtain ⟨x, -, hx⟩ := hwf.has_min Set.univ ⟨⟨hne.choose, hne.choose_spec⟩, trivial⟩
  refine ⟨x, x.2, fun r hr => ?_⟩
  exact hx ⟨r, hclosed x x.2 r hr⟩ trivial (TransGen.single hr)

/-- Bounded cumulative opportunity means opportunity stops. -/
lemma eventually_no_opp {m : Q} (hΩ : ∃ B, ∀ N, T.Omega N m ≤ B) :
    ∃ n1, ∀ n, n1 ≤ n → ¬ T.opp n m := by
  by_contra hcon
  push Not at hcon
  obtain ⟨B, hB⟩ := hΩ
  have : ∀ b, ∃ N, b < T.Omega N m := by
    intro b
    induction b with
    | zero =>
      obtain ⟨n, -, hn⟩ := hcon 0
      refine ⟨n + 1, ?_⟩
      unfold TraceData.Omega
      exact card_pos.2 ⟨n, mem_filter.2 ⟨mem_range.2 (by omega), hn⟩⟩
    | succ b ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨n, hn, hopp⟩ := hcon N
      refine ⟨n + 1, ?_⟩
      unfold TraceData.Omega at hN ⊢
      have hsub : insert n ((range N).filter (fun k => T.opp k m)) ⊆
          (range (n + 1)).filter (fun k => T.opp k m) := by
        intro k hk
        rcases mem_insert.1 hk with rfl | hk
        · exact mem_filter.2 ⟨mem_range.2 (by omega), hopp⟩
        · obtain ⟨h1, h2⟩ := mem_filter.1 hk
          exact mem_filter.2 ⟨mem_range.2 (by have := mem_range.1 h1; omega), h2⟩
      have hnot : n ∉ (range N).filter (fun k => T.opp k m) := by
        intro h; have := mem_range.1 (mem_filter.1 h).1; omega
      have := card_le_card hsub
      rw [card_insert_of_notMem hnot] at this
      omega
  obtain ⟨N, hN⟩ := this B
  exact absurd (hB N) (by omega)

/-- **Persistent-Wait Theorem.** If matter `m` exists from `n0` on, stays live forever,
and has available work only finitely often, then one fixed prerequisite is eventually a
permanent no-route wait. -/
theorem persistent_wait (m : Q) (n0 : ℕ) (hm0 : m ∈ T.M n0)
    (hlive : ∀ n, n0 ≤ n → (T.Live n m).Nonempty)
    (hΩ : ∃ B, ∀ N, T.Omega N m ≤ B) :
    ∃ d N0, ∀ n, N0 ≤ n → T.NoRouteWait n m d := by
  have hM : ∀ n, n0 ≤ n → m ∈ T.M n := T.mem_M_of_le hm0
  obtain ⟨n1', hn1'⟩ := T.eventually_no_opp hΩ
  set n1 := max n0 n1' with hn1
  have hW : ∀ n, n1 ≤ n → T.Work n m = ∅ := by
    intro n hn
    by_contra h
    exact hn1' n (by omega) ⟨hM n (by omega), nonempty_iff_ne_empty.2 h⟩
  -- the unmet reachable (issue, prerequisite) pairs
  let U : ℕ → Finset (Q × D) := fun n =>
    (T.Reach n m).biUnion (fun q => ((T.Pre n q).filter (fun d => ¬ T.Met n d)).image (fun d => (q, d)))
  have hU : ∀ n, n1 ≤ n → U (n + 1) ⊆ U n := by
    intro n hn x hx
    obtain ⟨q, hq, hx⟩ := mem_biUnion.1 hx
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
    obtain ⟨hd, hu⟩ := mem_filter.1 hd
    have hq' := reach_succ_subset (hM n (by omega)) (hW n hn) hq
    refine mem_biUnion.2 ⟨q, hq', mem_image.2 ⟨d, mem_filter.2 ⟨pre_succ_subset (hM n (by omega)) (hW n hn) hq' hd,
      fun h => hu (T.met_persistent n d h)⟩, rfl⟩⟩
  obtain ⟨n2, hn2, hstab⟩ := finset_antitone_stabilizes U n1 hU
  -- at n2: a sink of the waiting graph
  have hne : (T.Reach n2 m).Nonempty :=
    (hlive n2 (by omega)).mono (T.live_subset_reach n2 m)
  obtain ⟨q, hqR, hsink⟩ := exists_sink (T.Reach n2 m) (T.waits n2) hne
    (fun q hq r hr => T.mem_reach_of_waits hq hr)
    (fun q hq hc => by
      have : q ∈ T.Work n2 m := mem_filter.2 ⟨hq, Or.inr hc⟩
      simp [hW n2 hn2] at this)
  have hnr : ¬ T.Ready n2 q := fun hr => by
    have : q ∈ T.Work n2 m := mem_filter.2 ⟨hqR, Or.inl hr⟩
    simp [hW n2 hn2] at this
  unfold TraceData.Ready at hnr
  push Not at hnr
  obtain ⟨d, hd, hu⟩ := hnr
  have hroutes : T.Routes n2 d = ∅ := by
    apply eq_empty_of_forall_notMem
    intro r hr
    exact hsink r ⟨d, hd, hu, hr⟩
  refine ⟨d, n2, fun n hn => ?_⟩
  have hx : (q, d) ∈ U n := by
    rw [hstab n hn]
    exact mem_biUnion.2 ⟨q, hqR, mem_image.2 ⟨d, mem_filter.2 ⟨hd, hu⟩, rfl⟩⟩
  obtain ⟨q', hq', hx⟩ := mem_biUnion.1 hx
  obtain ⟨d', hd', hx⟩ := mem_image.1 hx
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
  obtain ⟨hd', hu'⟩ := mem_filter.1 hd'
  exact ⟨q', hq', hd', hu', T.routes_empty_persistent (T.reach_subset_O n2 m hqR) hd hroutes n hn⟩

/-- **Wait responsiveness** (the single liveness assumption of §8). -/
def WaitResponsive (m : Q) : Prop :=
  ∀ d N0, (∀ n, N0 ≤ n → T.NoRouteWait n m d) → ∃ k, N0 ≤ k ∧ T.Met k d

/-- **Persistent Opportunity.** Under wait responsiveness a matter that is live forever
has unbounded cumulative opportunity. -/
theorem persistent_opportunity (m : Q) (n0 : ℕ) (hm0 : m ∈ T.M n0)
    (hlive : ∀ n, n0 ≤ n → (T.Live n m).Nonempty) (hWR : T.WaitResponsive m) :
    ∀ B, ∃ N, B < T.Omega N m := by
  by_contra h
  push Not at h
  obtain ⟨B, hB⟩ := h
  obtain ⟨d, N0, hd⟩ := T.persistent_wait m n0 hm0 hlive ⟨B, hB⟩
  obtain ⟨k, hk, hmet⟩ := hWR d N0 hd
  obtain ⟨_, _, _, hu, _⟩ := hd k hk
  exact hu hmet

/-- Cumulative attention `A_N(m)` for an attention assignment `a`. -/
def Attention (a : ℕ → Q → ℚ) (N : ℕ) (m : Q) : ℚ := ∑ n ∈ range N, a n m


/-- Requirement 11 (non-starvation) for `a` and `m`. -/
def NonStarving (a : ℕ → Q → ℚ) (m : Q) : Prop :=
  (∀ B, ∃ N, B < T.Omega N m) → ∀ C : ℚ, ∃ N, C < Attention a N m

/-- **No Structural Abandonment.** Every matter either eventually has no live
descendant (explicit closure, by resolution continuity) or receives unbounded attention.
The budget constraints on `a` are not needed for this implication. -/
theorem no_structural_abandonment (a : ℕ → Q → ℚ) (m : Q) (n0 : ℕ) (hm0 : m ∈ T.M n0)
    (hWR : T.WaitResponsive m) (hNS : T.NonStarving a m) :
    (∃ N, n0 ≤ N ∧ ∀ n, N ≤ n → T.Live n m = ∅) ∨ (∀ C : ℚ, ∃ N, C < Attention a N m) := by
  by_cases h : ∃ N, n0 ≤ N ∧ T.Live N m = ∅
  · obtain ⟨N, hN, hL⟩ := h
    exact Or.inl ⟨N, hN, T.live_empty_persistent (T.mem_M_of_le hm0 N hN) hL⟩
  · push Not at h
    exact Or.inr (hNS (T.persistent_opportunity m n0 hm0
      (fun n hn => h n hn) hWR))

end IssueTrace

/-! ## 2. Standing traces and Grounded Replay -/

/-- A standing trace: which rules are in force, what each batch adds and removes, the
grounds cited for each addition, and the `Auth` predicate. `grounds n l` is the set of
authorizers cited by the record adding `l` in batch `n`. -/
structure StandingTrace (N : Type*) where
  L : ℕ → Finset N
  Ladd : ℕ → Finset N
  Ldel : ℕ → Finset N
  grounds : ℕ → N → Finset N
  Auth : N → Prop
  /-- Requirement 1: the exact update. -/
  step : ∀ n, L (n + 1) = (L n \ Ldel n) ∪ Ladd n
  /-- Requirement 1: an addition that changes standing cites standing authorizers. -/
  grounds_standing : ∀ n l, l ∈ Ladd n → l ∉ L n → grounds n l ⊆ (L n).filter Auth
  /-- Requirement 1: such grounds are nonempty. -/
  grounds_nonempty : ∀ n l, l ∈ Ladd n → l ∉ L n → (grounds n l).Nonempty

namespace StandingTrace

variable {N : Type*} (S : StandingTrace N)

/-- `Grounded n l`: `l` has a finite authorization tree whose leaves lie in `G = L 0`,
whose internal nodes were added at positions strictly decreasing along every branch,
all below `n`. This inductive predicate *is* the tree. -/
inductive Grounded : ℕ → N → Prop
  | genesis {n l} : l ∈ S.L 0 → Grounded n l
  | node {n k l} : l ∈ S.Ladd k → l ∉ S.L k → k < n →
      (∀ g ∈ S.grounds k l, Grounded k g) → Grounded n l

lemma Grounded.mono {n k : ℕ} {l : N} (h : S.Grounded n l) (hnk : n ≤ k) : S.Grounded k l := by
  cases h with
  | genesis h => exact Grounded.genesis h
  | node hadd hnot hlt hg => exact Grounded.node hadd hnot (by omega) hg

/-- **Grounded Replay.** Every rule in force has an authorization tree back to `G`.
Uses Requirement 1 only; freshness of `Ladd` is not needed for existence of the tree. -/
theorem grounded_replay : ∀ n, ∀ l ∈ S.L n, S.Grounded n l := by
  intro n
  induction n with
  | zero => intro l hl; exact Grounded.genesis hl
  | succ n ih =>
    intro l hl
    rw [S.step n] at hl
    rcases mem_union.1 hl with h | h
    · exact Grounded.mono S (ih l (mem_sdiff.1 h).1) (Nat.le_succ n)
    · by_cases hin : l ∈ S.L n
      · exact Grounded.mono S (ih l hin) (Nat.le_succ n)
      · refine Grounded.node h hin (by omega) (fun g hg => ?_)
        have := S.grounds_standing n l h hin hg
        exact ih g (mem_filter.1 this).1

/-- Every non-genesis node of the tree cites at least one authorizer. -/
theorem grounded_nonempty_grounds {k : ℕ} {l : N} (hadd : l ∈ S.Ladd k) (hnot : l ∉ S.L k) :
    (S.grounds k l).Nonempty := S.grounds_nonempty k l hadd hnot

/-- Freshness of newly admitted standing occurrences (the clause restored by the audit).
Stated as a definition, not a field: `grounded_replay` does not consume it. -/
def Fresh : Prop := ∀ n l, l ∈ S.Ladd n → ∀ k, k ≤ n → l ∉ S.L k

end StandingTrace

/-! ### Standing at opening (Requirement 2) -/

/-- A licensing relation `λ ▷ (κ, τ, x)` on rule content. -/
structure Licensing (N K Ty X : Type*) where
  lic : N → K → Ty → X → Prop

/-- `κ ⊩_n (τ, x)`: some standing rule licenses `κ` for `(τ, x)`. -/
def Licensing.standsFor {N K Ty X : Type*} (Li : Licensing N K Ty X) (S : StandingTrace N)
    (n : ℕ) (κ : K) (τ : Ty) (x : X) : Prop :=
  ∃ l ∈ S.L n, Li.lic l κ τ x

/-- Requirement 2 for an issue trace with anchors `κ`, kinds `τ`, subjects `x`. -/
def AnchorStanding {N K Ty X : Type*} (Li : Licensing N K Ty X) (S : StandingTrace N)
    (T : TraceData Q D) (κ : Q → K) (τ : Q → Ty) (x : Q → X) : Prop :=
  ∀ n q, q ∈ T.Born n → Li.standsFor S n (κ q) (τ q) (x q)

/-- Where the two layers meet: the rule licensing a fresh issue's protocol has an
authorization tree back to `G`. -/
theorem anchor_grounded {N K Ty X : Type*} (Li : Licensing N K Ty X) (S : StandingTrace N)
    (T : TraceData Q D) (κ : Q → K) (τ : Q → Ty) (x : Q → X)
    (h : AnchorStanding Li S T κ τ x) {n : ℕ} {q : Q} (hq : q ∈ T.Born n) :
    ∃ l ∈ S.L n, Li.lic l (κ q) (τ q) (x q) ∧ S.Grounded n l := by
  obtain ⟨l, hl, hlic⟩ := h n q hq
  exact ⟨l, hl, hlic, S.grounded_replay n l hl⟩


/-! ## 3. Regression fixtures

The Python fixtures of the proof pass, replayed in Lean. Fixture A is the necessity
witness for Requirement 12: the ownership-only (`Live`) gate admits a trace on which
the Persistent-Wait conclusion fails, and the reach gate rejects the same trace at the
first rotation, by Requirement 12 alone. -/

namespace Fixtures

/-- The statement of Requirement 12 for a trace data. -/
def ReachGate (T : TraceData Q D) : Prop :=
  ∀ n q, q ∈ T.O n → q ∈ T.O (n + 1) → (T.PreAdd n q).Nonempty →
    ∀ m ∈ T.M n, q ∈ T.Reach n m → (T.Work n m).Nonempty

/-- The weaker ownership-only gate the proof pass refuted. -/
def LiveGate (T : TraceData Q D) : Prop :=
  ∀ n q, q ∈ T.O n → q ∈ T.O (n + 1) → (T.PreAdd n q).Nonempty →
    ∀ m ∈ T.M n, q ∈ T.Live n m → (T.Work n m).Nonempty

/-- Every `IssueTrace` field except Requirement 12, as one proposition on trace data. -/
def OtherRequirements (T : TraceData Q D) : Prop :=
  (∀ q n k, q ∈ T.Born n → q ∈ T.Born k → n = k) ∧
  (∀ q n, q ∈ T.Born n → q ∉ T.O n) ∧
  (∀ q n, q ∈ T.O n → ∃ j < n, q ∈ T.Born j) ∧
  (∀ n, T.Res n ⊆ T.O n) ∧
  (∀ n, T.O (n + 1) = (T.O n \ T.Res n) ∪ T.Born n) ∧
  (∀ n q, q ∈ T.Born n → ∀ p ∈ T.par q, p ∈ T.Res n) ∧
  (∀ n q, q ∈ T.O n → q ∈ T.O (n + 1) →
    T.Pre (n + 1) q = (T.Pre n q \ T.PreDrop n q) ∪ T.PreAdd n q) ∧
  (∀ n q, q ∈ T.Born n → T.Pre (n + 1) q = T.PreAdd n q) ∧
  (∀ n q d, d ∈ T.PreAdd n q → T.intro d = n) ∧
  (∀ n q d, d ∈ T.PreAdd n q → T.roots d ⊆ T.O n ∪ T.Born n) ∧
  (∀ n d, T.Met n d → T.Met (n + 1) d) ∧
  (∀ n q, q ∈ T.Res n → T.Ready n q) ∧
  (∀ n m, m ∈ T.M n → m ∈ T.M (n + 1)) ∧
  (∀ n m, m ∈ T.M n → ∃ j < n, m ∈ T.Born j)

/-- `OtherRequirements` and the reach gate together are exactly an `IssueTrace`. -/
def toIssueTrace (T : TraceData Q D) (h : OtherRequirements T) (hg : ReachGate T) :
    IssueTrace Q D :=
  { T with
    born_unique := h.1, born_not_out := h.2.1, out_born := h.2.2.1, res_subset := h.2.2.2.1,
    resolution_continuity := h.2.2.2.2.1, fresh_successors := h.2.2.2.2.2.1,
    pre_continuity := h.2.2.2.2.2.2.1, pre_fresh := h.2.2.2.2.2.2.2.1,
    pre_intro := h.2.2.2.2.2.2.2.2.1, pre_refs := h.2.2.2.2.2.2.2.2.2.1,
    met_persistent := h.2.2.2.2.2.2.2.2.2.2.1, ready_resolve := h.2.2.2.2.2.2.2.2.2.2.2.1,
    matters_mono := h.2.2.2.2.2.2.2.2.2.2.2.2.1, matters_prior := h.2.2.2.2.2.2.2.2.2.2.2.2.2,
    no_rewire := hg }

/-! ### Fixture A — rotating prerequisite -/

inductive AQ | a | b | b1 | c
  deriving DecidableEq, Fintype

open AQ

/-- Issues `a` (matter `m₁`), `b` (matter `m₂`, resolved at 1 into `b1` and `c`).
Prerequisite `none` is `d₀` on `a` with route root `b1`; `some k` is `e_k` on `b1`,
introduced at `k+1`, withdrawn at `k+2`, with no route. `Met` is never true. -/
def fixA : TraceData AQ (Option ℕ) where
  O n := univ.filter (fun q => (n = 1 ∧ (q = a ∨ q = b)) ∨ (2 ≤ n ∧ (q = a ∨ q = b1 ∨ q = c)))
  Res n := univ.filter (fun q => n = 1 ∧ q = b)
  Born n := univ.filter (fun q => (n = 0 ∧ (q = a ∨ q = b)) ∨ (n = 1 ∧ (q = b1 ∨ q = c)))
  par q := univ.filter (fun p => p = b ∧ (q = b1 ∨ q = c))
  Pre n q := match q with
    | a => if 2 ≤ n then {none} else ∅
    | b1 => if 2 ≤ n then {some (n - 2)} else ∅
    | _ => ∅
  PreAdd n q := match q with
    | a => if n = 1 then {none} else ∅
    | b1 => if 1 ≤ n then {some (n - 1)} else ∅
    | _ => ∅
  PreDrop n q := match q with
    | b1 => if 2 ≤ n then {some (n - 2)} else ∅
    | _ => ∅
  roots d := univ.filter (fun t => d = none ∧ t = b1)
  intro d := match d with | none => 1 | some k => k + 1
  Met _ _ := False
  M n := univ.filter (fun q => 1 ≤ n ∧ (q = a ∨ q = b))

section fixA_lemmas

@[simp] lemma fixA_mem_O {n : ℕ} {q : AQ} :
    q ∈ fixA.O n ↔ (n = 1 ∧ (q = a ∨ q = b)) ∨ (2 ≤ n ∧ (q = a ∨ q = b1 ∨ q = c)) := by
  simp [fixA]
@[simp] lemma fixA_mem_Res {n : ℕ} {q : AQ} : q ∈ fixA.Res n ↔ n = 1 ∧ q = b := by simp [fixA]
@[simp] lemma fixA_mem_Born {n : ℕ} {q : AQ} :
    q ∈ fixA.Born n ↔ (n = 0 ∧ (q = a ∨ q = b)) ∨ (n = 1 ∧ (q = b1 ∨ q = c)) := by simp [fixA]
@[simp] lemma fixA_mem_par {p q : AQ} : p ∈ fixA.par q ↔ p = b ∧ (q = b1 ∨ q = c) := by
  simp [fixA]
@[simp] lemma fixA_succ {p q : AQ} : fixA.succ p q ↔ p = b ∧ (q = b1 ∨ q = c) := by
  simp [TraceData.succ]
@[simp] lemma fixA_mem_roots {d : Option ℕ} {t : AQ} : t ∈ fixA.roots d ↔ d = none ∧ t = b1 := by
  simp [fixA]
@[simp] lemma fixA_mem_M {n : ℕ} {q : AQ} : q ∈ fixA.M n ↔ 1 ≤ n ∧ (q = a ∨ q = b) := by simp [fixA]
@[simp] lemma fixA_Met {n : ℕ} {d : Option ℕ} : ¬ fixA.Met n d := by simp [fixA]
@[simp] lemma fixA_Pre_a {n : ℕ} : fixA.Pre n a = if 2 ≤ n then {none} else ∅ := rfl
@[simp] lemma fixA_Pre_b1 {n : ℕ} : fixA.Pre n b1 = if 2 ≤ n then {some (n - 2)} else ∅ := rfl
@[simp] lemma fixA_Pre_b {n : ℕ} : fixA.Pre n b = ∅ := rfl
@[simp] lemma fixA_Pre_c {n : ℕ} : fixA.Pre n c = ∅ := rfl
@[simp] lemma fixA_PreAdd_a {n : ℕ} : fixA.PreAdd n a = if n = 1 then {none} else ∅ := rfl
@[simp] lemma fixA_PreAdd_b1 {n : ℕ} : fixA.PreAdd n b1 = if 1 ≤ n then {some (n - 1)} else ∅ := rfl
@[simp] lemma fixA_PreAdd_b {n : ℕ} : fixA.PreAdd n b = ∅ := rfl
@[simp] lemma fixA_PreAdd_c {n : ℕ} : fixA.PreAdd n c = ∅ := rfl
@[simp] lemma fixA_PreDrop_b1 {n : ℕ} : fixA.PreDrop n b1 = if 2 ≤ n then {some (n - 2)} else ∅ := rfl
@[simp] lemma fixA_PreDrop_a {n : ℕ} : fixA.PreDrop n a = ∅ := rfl
@[simp] lemma fixA_PreDrop_b {n : ℕ} : fixA.PreDrop n b = ∅ := rfl
@[simp] lemma fixA_PreDrop_c {n : ℕ} : fixA.PreDrop n c = ∅ := rfl
@[simp] lemma fixA_intro_none : fixA.intro none = 1 := rfl
@[simp] lemma fixA_intro_some {k : ℕ} : fixA.intro (some k) = k + 1 := rfl

/-- Ancestry in fixture A: `a` has no descendants but itself. -/
lemma fixA_anc_a {q : AQ} (h : fixA.anc a q) : q = a := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => subst ih; simp at hbc

lemma fixA_anc_b1 {q : AQ} (h : fixA.anc b1 q) : q = b1 := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => subst ih; simp at hbc

lemma fixA_anc_b_c : fixA.anc b c := ReflTransGen.single (by simp)

lemma fixA_not_anc_b_a : ¬ fixA.anc b a := fun h => by
  rcases ReflTransGen.cases_tail h with h | ⟨p, _, hp⟩
  · cases h
  · simp at hp

/-- Routes of `d₀` at any position `n ≥ 2` are exactly `{b1}`. -/
lemma fixA_routes_d0 {n : ℕ} (hn : 2 ≤ n) : fixA.Routes n none = {b1} := by
  ext r
  simp only [TraceData.Routes, mem_filter, mem_singleton]
  constructor
  · rintro ⟨-, t, ht, hanc⟩
    simp at ht; subst ht
    exact fixA_anc_b1 hanc
  · rintro rfl
    exact ⟨by simp [hn], b1, by simp, ReflTransGen.refl⟩

lemma fixA_routes_e {n k : ℕ} : fixA.Routes n (some k) = ∅ := by
  ext r; simp [TraceData.Routes]

/-- The waiting relation at position `n ≥ 2` is exactly `a ⇝ b1`. -/
lemma fixA_waits {n : ℕ} (hn : 2 ≤ n) {q r : AQ} : fixA.waits n q r ↔ q = a ∧ r = b1 := by
  constructor
  · rintro ⟨d, hd, -, hr⟩
    cases q <;> simp [hn] at hd
    · subst hd; rw [fixA_routes_d0 hn] at hr; simp at hr; exact ⟨rfl, hr⟩
    · subst hd; rw [fixA_routes_e] at hr; simp at hr
  · rintro ⟨rfl, rfl⟩
    refine ⟨none, by simp [hn], by simp, ?_⟩
    rw [fixA_routes_d0 hn]; simp

lemma fixA_no_cycle {n : ℕ} (hn : 2 ≤ n) (q : AQ) : ¬ fixA.onCycle n q := by
  intro h
  have key : ∀ x y, TransGen (fixA.waits n) x y → x = a ∧ y = b1 := by
    intro x y hxy
    induction hxy with
    | single h => exact (fixA_waits hn).1 h
    | tail _ h ih => exact ⟨ih.1, ((fixA_waits hn).1 h).2⟩
  obtain ⟨h1, h2⟩ := key q q h
  subst h1; cases h2

lemma fixA_reach_a {n : ℕ} (hn : 2 ≤ n) : fixA.Reach n a = {a, b1} := by
  ext r
  simp only [TraceData.Reach, TraceData.Live, mem_filter]
  constructor
  · rintro ⟨-, q, ⟨-, hq⟩, hpath⟩
    have hq' := fixA_anc_a hq; subst hq'
    rcases ReflTransGen.cases_tail hpath with h | ⟨p, -, hp⟩
    · subst h; simp
    · rw [((fixA_waits hn).1 hp).2]; simp
  · intro hr
    have hO : ∀ x, x ∈ ({a, b1} : Finset AQ) → x ∈ fixA.O n := by
      intro x hx; simp at hx
      rcases hx with rfl | rfl <;> simp [hn]
    refine ⟨hO r hr, a, ⟨hO a (by simp), ReflTransGen.refl⟩, ?_⟩
    simp at hr
    rcases hr with rfl | rfl
    · exact ReflTransGen.refl
    · exact ReflTransGen.single ((fixA_waits hn).2 ⟨rfl, rfl⟩)

/-- Matter `a` has no available work at any position `n ≥ 2`. -/
lemma fixA_work_a {n : ℕ} (hn : 2 ≤ n) : fixA.Work n a = ∅ := by
  apply eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨hR, hw⟩ := mem_filter.1 hq
  rw [fixA_reach_a hn] at hR
  rcases hw with hr | hc
  · simp at hR
    rcases hR with rfl | rfl
    · exact hr none (by simp [hn])
    · exact hr (some (n - 2)) (by simp [hn])
  · exact fixA_no_cycle hn q hc

/-- The reach gate rejects fixture A at position 2, issue `b1`, matter `a`. -/
theorem fixA_reach_gate_fails : ¬ ReachGate fixA := by
  intro h
  have := h 2 b1 (by simp) (by simp) ⟨some 1, by simp⟩ a (by simp)
    (by rw [fixA_reach_a le_rfl]; simp)
  rw [fixA_work_a le_rfl] at this
  exact not_nonempty_empty this

/-- Matter `b` always has work from position 2 on: `c` is ready. -/
lemma fixA_c_work {n : ℕ} (hn : 2 ≤ n) : c ∈ fixA.Work n b := by
  refine mem_filter.2 ⟨?_, Or.inl (by simp [TraceData.Ready])⟩
  refine mem_filter.2 ⟨by simp [hn], c, ?_, ReflTransGen.refl⟩
  exact mem_filter.2 ⟨by simp [hn], fixA_anc_b_c⟩

/-- The ownership-only gate admits fixture A. -/
theorem fixA_live_gate_holds : LiveGate fixA := by
  intro n q hO hO' hadd m hm hL
  obtain ⟨hqO, hanc⟩ := mem_filter.1 hL
  cases q with
  | a =>
    have hn : n = 1 := by
      by_contra hne; simp [hne] at hadd
    subst hn
    have hm2 : m = a ∨ m = b := by simp at hm; tauto
    have hm' : m = a := by
      rcases hm2 with rfl | rfl
      · rfl
      · exact absurd hanc fixA_not_anc_b_a
    subst hm'
    refine ⟨a, mem_filter.2 ⟨mem_filter.2 ⟨by simp, a, mem_filter.2 ⟨by simp, ReflTransGen.refl⟩,
      ReflTransGen.refl⟩, Or.inl (by simp [TraceData.Ready])⟩⟩
  | b => simp at hadd
  | c => simp at hadd
  | b1 =>
    have hn : 2 ≤ n := by simp at hqO; omega
    have hm2 : m = a ∨ m = b := by simp at hm; tauto
    have hm' : m = b := by
      rcases hm2 with rfl | rfl
      · exact absurd (fixA_anc_a hanc) (by decide)
      · rfl
    subst hm'
    exact ⟨c, fixA_c_work hn⟩

/-- Every other structural requirement holds on fixture A, so the reach gate is what
rejects it. -/
theorem fixA_other_requirements : OtherRequirements fixA := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q n k hn hk; cases q <;> simp at hn hk <;> omega
  · intro q n hq; cases q <;> simp at hq ⊢ <;> omega
  · intro q n hq
    cases q <;> simp at hq
    · exact ⟨0, by omega, by simp⟩
    · exact ⟨0, by omega, by simp⟩
    · exact ⟨1, by omega, by simp⟩
    · exact ⟨1, by omega, by simp⟩
  · intro n q hq; simp at hq ⊢; obtain ⟨rfl, rfl⟩ := hq; simp
  · intro n; ext q; cases q <;> simp <;> omega
  · intro n q hq p hp; cases q <;> simp_all
  · intro n q hO hO'
    cases q <;> simp at hO hO'
    · by_cases h : 2 ≤ n
      · simp [h, show 2 ≤ n + 1 by omega, show ¬ n = 1 by omega]
      · have : n = 1 := by omega
        subst this; simp
    · simp
    · have h : 2 ≤ n := by omega
      ext d
      simp [h, show 2 ≤ n + 1 by omega, show 1 ≤ n by omega, show n + 1 - 2 = n - 1 by omega]
    · simp
  · intro n q hq
    cases q <;> simp at hq <;> subst hq <;> simp
  · intro n q d hd
    cases q <;> cases d <;> simp only [fixA_PreAdd_a, fixA_PreAdd_b, fixA_PreAdd_b1, fixA_PreAdd_c] at hd <;>
      (try split_ifs at hd) <;> simp at hd <;> simp <;> omega
  · intro n q d hd t ht
    cases q <;> cases d <;> simp only [fixA_PreAdd_a, fixA_PreAdd_b, fixA_PreAdd_b1, fixA_PreAdd_c] at hd <;>
      (try split_ifs at hd) <;> simp at hd <;> simp at ht <;> simp [ht] <;> omega
  · intro n d h; exact h
  · intro n q hq
    simp at hq; obtain ⟨rfl, rfl⟩ := hq
    simp [TraceData.Ready]
  · intro n m hm; simp at hm ⊢; tauto
  · intro n m hm
    simp at hm
    exact ⟨0, by omega, by rcases hm.2 with rfl | rfl <;> simp⟩

/-- Under the ownership-only gate the Persistent-Wait conclusion fails on fixture A:
matter `a` is live forever, has no work from position 2 on, and no single prerequisite
is a permanent no-route wait — the no-route wait at `n` is `e_{n-2}`, which is withdrawn
at the next position. -/
theorem fixA_persistent_wait_fails :
    (∀ n, 2 ≤ n → (fixA.Live n a).Nonempty) ∧
    (∀ n, 2 ≤ n → fixA.Work n a = ∅) ∧
    ¬ ∃ d N0, ∀ n, N0 ≤ n → fixA.NoRouteWait n a d := by
  refine ⟨fun n hn => ⟨a, mem_filter.2 ⟨by simp [hn], ReflTransGen.refl⟩⟩,
    fun n hn => fixA_work_a hn, ?_⟩
  rintro ⟨d, N0, h⟩
  have hn2 : 2 ≤ max N0 2 := le_max_right _ _
  obtain ⟨q, hq, hd, -, hroutes⟩ := h (max N0 2) (le_max_left _ _)
  obtain ⟨q', hq', hd', -, hroutes'⟩ := h (max N0 2 + 1) ((le_max_left _ _).trans (Nat.le_succ _))
  rw [fixA_reach_a hn2] at hq
  rw [fixA_reach_a (Nat.le_succ_of_le hn2)] at hq'
  simp at hq hq'
  rcases hq with rfl | rfl
  · simp [hn2] at hd; subst hd
    rw [fixA_routes_d0 hn2] at hroutes; simp at hroutes
  · rcases hq' with rfl | rfl
    · simp [Nat.le_succ_of_le hn2] at hd'; subst hd'
      rw [fixA_routes_d0 (Nat.le_succ_of_le hn2)] at hroutes'; simp at hroutes'
    · simp [hn2, Nat.le_succ_of_le hn2] at hd hd'
      subst hd
      have := Option.some.inj hd'
      omega

end fixA_lemmas

/-! ### Fixture B — a co-opened route root: Lemma 3 needs `n > intro d` -/

inductive BQ | a | t
  deriving DecidableEq, Fintype

/-- `a` opens at 0; at batch 1, `t` opens and `d` (root `t`) is added to `a`. -/
def fixB : TraceData BQ Unit where
  O n := univ.filter (fun q => (n = 1 ∧ q = BQ.a) ∨ (2 ≤ n ∧ (q = BQ.a ∨ q = BQ.t)))
  Res _ := ∅
  Born n := univ.filter (fun q => (n = 0 ∧ q = BQ.a) ∨ (n = 1 ∧ q = BQ.t))
  par _ := ∅
  Pre n q := if q = BQ.a ∧ 2 ≤ n then {()} else ∅
  PreAdd n q := if q = BQ.a ∧ n = 1 then {()} else ∅
  PreDrop _ _ := ∅
  roots _ := {BQ.t}
  intro _ := 1
  Met _ _ := False
  M n := univ.filter (fun q => 1 ≤ n ∧ q = BQ.a)

lemma fixB_anc {p q : BQ} (h : fixB.anc p q) : p = q := by
  induction h with
  | refl => rfl
  | tail _ hbc _ => simp [fixB, TraceData.succ] at hbc

/-- `Routes_1(d) = ∅` but `Routes_2(d) = {t}`: the unqualified lemma is false. -/
theorem fixB_routes : fixB.Routes 1 () = ∅ ∧ fixB.Routes 2 () = {BQ.t} := by
  constructor
  · ext r; simp [TraceData.Routes, fixB]
    intro h; subst h; exact fun h => BQ.noConfusion (fixB_anc h)
  · ext r; simp [TraceData.Routes, fixB]
    constructor
    · rintro ⟨-, h⟩; exact (fixB_anc h).symm
    · rintro rfl; exact ⟨Or.inr rfl, ReflTransGen.refl⟩

/-! ### Fixture E — a two-node waiting cycle is work -/

/-- `a` and `t` open at 0; at batch 1 each gets a prerequisite routed to the other:
prerequisite `true` on `a` with root `t`, prerequisite `false` on `t` with root `a`. -/
def fixE : TraceData BQ Bool where
  O n := univ.filter (fun _ => 1 ≤ n)
  Res _ := ∅
  Born n := univ.filter (fun _ => n = 0)
  par _ := ∅
  Pre n q := if 2 ≤ n then {decide (q = BQ.a)} else ∅
  PreAdd n q := if n = 1 then {decide (q = BQ.a)} else ∅
  PreDrop _ _ := ∅
  roots d := if d then {BQ.t} else {BQ.a}
  intro _ := 1
  Met _ _ := False
  M n := univ.filter (fun _ => 1 ≤ n)

lemma fixE_waits {n : ℕ} (hn : 2 ≤ n) : fixE.waits n BQ.a BQ.t ∧ fixE.waits n BQ.t BQ.a := by
  have hO : ∀ q, q ∈ fixE.O n := by intro q; simp only [fixE, mem_filter, mem_univ, true_and]; omega
  constructor
  · exact ⟨true, by simp [fixE, hn], fun h => h,
      mem_filter.2 ⟨hO _, BQ.t, by simp [fixE], ReflTransGen.refl⟩⟩
  · exact ⟨false, by simp [fixE, hn], fun h => h,
      mem_filter.2 ⟨hO _, BQ.a, by simp [fixE], ReflTransGen.refl⟩⟩

/-- Both issues are on a cycle, hence in `Work_n(a)`, at every `n ≥ 2`. -/
theorem fixE_cycle_is_work {n : ℕ} (hn : 2 ≤ n) :
    BQ.a ∈ fixE.Work n BQ.a ∧ BQ.t ∈ fixE.Work n BQ.a := by
  obtain ⟨h1, h2⟩ := fixE_waits hn
  have hO : ∀ q, q ∈ fixE.O n := by intro q; simp only [fixE, mem_filter, mem_univ, true_and]; omega
  have hLa : BQ.a ∈ fixE.Live n BQ.a := mem_filter.2 ⟨hO _, ReflTransGen.refl⟩
  have hRa : BQ.a ∈ fixE.Reach n BQ.a := fixE.live_subset_reach n BQ.a hLa
  have hRt : BQ.t ∈ fixE.Reach n BQ.a := fixE.mem_reach_of_waits hRa h1
  exact ⟨mem_filter.2 ⟨hRa, Or.inr ((TransGen.single h1).tail h2)⟩,
    mem_filter.2 ⟨hRt, Or.inr ((TransGen.single h2).tail h1)⟩⟩

end Fixtures

end

end Workspace.Normativity.Contrib.NormativeContinuity

#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.routes_empty_persistent
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.live_empty_persistent
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.reach_succ_subset
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.exists_sink
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.persistent_wait
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.persistent_opportunity
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.no_structural_abandonment
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.StandingTrace.grounded_replay
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.anchor_grounded
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixA_reach_gate_fails
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixA_live_gate_holds
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixA_other_requirements
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixA_persistent_wait_fails
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixB_routes
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixE_cycle_is_work
