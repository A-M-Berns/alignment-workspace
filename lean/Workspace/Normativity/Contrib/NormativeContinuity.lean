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
* `DefeatTrace.grounded_replay` — paper Theorem 1 on the unified trace (§5): every
  issue in the record descends by `anc` from a parentless issue. The freshness clause
  the standing layer stated and did not consume is now the theorem `DefeatTrace.fresh`.
* `DefeatTrace.anchor_grounded` — Requirement 2. There is no longer a bridge between
  two layers, because there is one trace.
* Fixtures: `Fixtures.fixA_*` is the rotating-prerequisite countermodel — the
  ownership-only gate admits it (`fixA_live_gate_holds`), the Persistent-Wait
  conclusion fails on it (`fixA_persistent_wait_fails`), the reach gate rejects it
  (`fixA_reach_gate_fails`), and every other requirement holds
  (`fixA_other_requirements`). `fixB_routes` shows the unqualified route-extinction
  lemma is false at a prerequisite's introduction position; `fixE_cycle_is_work` shows a
  two-node waiting cycle counts as work.

**Unified grounds and answerable defeat (2026-09-02, §5).** `StandingTrace`,
`Licensing` and the inductive `StandingTrace.Grounded` are **deleted as primitives**.
Standing occurrences are issues of a licence kind on the same trace — Requirement 1's
`step` is literally `resolution_continuity` — and `DefeatTrace` adds resolution kinds
(`answer`, `dispose G`, `settle s`, and deliberately no fourth), a resolver, an opener,
a monotone `Settled`, one new structural requirement (`dispose_successor`) and `Met` as
a definition rather than a judgment. `Ground Q S := Q ⊕ S` is the type a disposal's
grounds live in, which no pre-unification type supplied. The **Defeat Principle** it
rests on is settled: `DECISIONS.md`, 2026-09-03, maintainer ruling.

**Settlement additions (2026-08-30, §4).** `IssueTraceCore.mattersOf` is the paper's
matter construction (roots at birth, designations prospectively) and
`IssueTraceCore.toIssueTrace` realizes the abstract fields from it, so every theorem above
applies to the paper's matters; `IssueTrace.NoPermanentWait` is
the settled primitive form of wait responsiveness, shown equivalent to the `Met` form;
`IssueTrace.shareAttention` is the positive-share attention witness with the unit budget
(`shareAttention_sum_le_one`) and non-starvation (`shareAttention_nonStarving`) for every
matter; `Fixtures.fixE_issueTrace` inhabits the full issue-trace specification.

**What is not claimed.** That wait responsiveness or non-starvation hold of anything;
anything about `Permit`, `Due`, `Continue`, checkers, Proper Exercise, or Legitimate
Improvement.

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
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic

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


/-! ## 4. Settlement additions (2026-08-30)

The concrete matter construction and its realization of the abstract fields, the
admitted-occurrence form of Grounded Replay, the primitive form of wait responsiveness,
the positive-share attention witness, and an inhabitant of `IssueTrace`. -/

/-! ### 4.1 The paper's matter construction realizes the abstract fields -/

/-- An issue trace without matters: every `IssueTrace` field except `M`,
`matters_mono`, `matters_prior`. -/
structure IssueTraceCore (Q D : Type*) extends TraceData Q D where
  born_unique : ∀ q n k, q ∈ Born n → q ∈ Born k → n = k
  born_not_out : ∀ q n, q ∈ Born n → q ∉ O n
  out_born : ∀ q n, q ∈ O n → ∃ j < n, q ∈ Born j
  res_subset : ∀ n, Res n ⊆ O n
  resolution_continuity : ∀ n, O (n + 1) = (O n \ Res n) ∪ Born n
  fresh_successors : ∀ n q, q ∈ Born n → ∀ p ∈ par q, p ∈ Res n
  pre_continuity : ∀ n q, q ∈ O n → q ∈ O (n + 1) →
    Pre (n + 1) q = (Pre n q \ PreDrop n q) ∪ PreAdd n q
  pre_fresh : ∀ n q, q ∈ Born n → Pre (n + 1) q = PreAdd n q
  pre_intro : ∀ n q d, d ∈ PreAdd n q → intro d = n
  pre_refs : ∀ n q d, d ∈ PreAdd n q → roots d ⊆ O n ∪ Born n
  met_persistent : ∀ n d, Met n d → Met (n + 1) d
  ready_resolve : ∀ n q, q ∈ Res n → toTraceData.Ready n q
  no_rewire : ∀ n q, q ∈ O n → q ∈ O (n + 1) → (PreAdd n q).Nonempty →
    ∀ m ∈ M n, q ∈ toTraceData.Reach n m → (toTraceData.Work n m).Nonempty

namespace IssueTraceCore

variable (C : IssueTraceCore Q D)

/-- The paper's `M_n`: `M_0 = ∅`; after batch `e_n`, add every root issue born at `n`
(`Par_n(q) = ∅`, i.e. `par q = ∅`) and every issue designated in `e_n`. `Desig n` is the
set of accepted `Designate_n` records. -/
def mattersOf (Desig : ℕ → Finset Q) : ℕ → Finset Q
  | 0 => ∅
  | n + 1 => mattersOf Desig n ∪ (C.Born n).filter (fun q => C.par q = ∅) ∪ Desig n

@[simp] lemma mattersOf_zero (Desig : ℕ → Finset Q) : C.mattersOf Desig 0 = ∅ := rfl

lemma mattersOf_succ (Desig : ℕ → Finset Q) (n : ℕ) :
    C.mattersOf Desig (n + 1) =
      C.mattersOf Desig n ∪ (C.Born n).filter (fun q => C.par q = ∅) ∪ Desig n := rfl

/-- Matterhood is prospective: `m ∈ M_{n+1}` iff it was already a matter, or became one
in batch `e_n` as a root or by designation. -/
lemma mem_mattersOf_succ (Desig : ℕ → Finset Q) (n : ℕ) (m : Q) :
    m ∈ C.mattersOf Desig (n + 1) ↔
      m ∈ C.mattersOf Desig n ∨ (m ∈ C.Born n ∧ C.par m = ∅) ∨ m ∈ Desig n := by
  simp [mattersOf_succ, mem_union, mem_filter, or_assoc]

lemma mattersOf_mono (Desig : ℕ → Finset Q) : ∀ n m, m ∈ C.mattersOf Desig n →
    m ∈ C.mattersOf Desig (n + 1) := by
  intro n m h; rw [mem_mattersOf_succ]; exact Or.inl h

/-- With designation restricted to issues already open or co-opened (the paper's
`q ∈ O_n ∪ Q⁺_n`), every matter is an issue born strictly before the prefix at which it
exists. -/
lemma mattersOf_prior (Desig : ℕ → Finset Q)
    (hD : ∀ n, Desig n ⊆ C.O n ∪ C.Born n) :
    ∀ n m, m ∈ C.mattersOf Desig n → ∃ j < n, m ∈ C.Born j := by
  intro n
  induction n with
  | zero => intro m h; simp at h
  | succ n ih =>
    intro m h
    rw [mem_mattersOf_succ] at h
    rcases h with h | ⟨h, -⟩ | h
    · obtain ⟨j, hj, hm⟩ := ih m h; exact ⟨j, by omega, hm⟩
    · exact ⟨n, by omega, h⟩
    · rcases mem_union.1 (hD n h) with h | h
      · obtain ⟨j, hj, hm⟩ := C.out_born m n h; exact ⟨j, by omega, hm⟩
      · exact ⟨n, by omega, h⟩

/-- The realization: the concrete construction yields an `IssueTrace`, so every theorem
of §1 applies to the paper's matters. Requirement 12 is transported verbatim (its `M`
is the constructed one). -/
def toIssueTrace (Desig : ℕ → Finset Q) (hD : ∀ n, Desig n ⊆ C.O n ∪ C.Born n)
    (hgate : ∀ n q, q ∈ C.O n → q ∈ C.O (n + 1) → (C.PreAdd n q).Nonempty →
      ∀ m ∈ C.mattersOf Desig n, q ∈ C.Reach n m → (C.Work n m).Nonempty) :
    IssueTrace Q D :=
  { C.toTraceData with
    M := C.mattersOf Desig
    born_unique := C.born_unique, born_not_out := C.born_not_out, out_born := C.out_born,
    res_subset := C.res_subset, resolution_continuity := C.resolution_continuity,
    fresh_successors := C.fresh_successors, pre_continuity := C.pre_continuity,
    pre_fresh := C.pre_fresh, pre_intro := C.pre_intro, pre_refs := C.pre_refs,
    met_persistent := C.met_persistent, ready_resolve := C.ready_resolve,
    matters_mono := C.mattersOf_mono Desig, matters_prior := C.mattersOf_prior Desig hD,
    no_rewire := hgate }

/-- Birth: `β(m)` for the constructed matters is the successor of the batch in which `m`
was born as a root or designated — never earlier (no retroactive matterhood). -/
lemma mattersOf_not_mem_of_lt (Desig : ℕ → Finset Q) (hD : ∀ n, Desig n ⊆ C.O n ∪ C.Born n)
    {m : Q} {j n : ℕ} (hm : m ∈ C.Born j) (hn : n ≤ j) : m ∉ C.mattersOf Desig n := by
  intro h
  obtain ⟨i, hi, hmi⟩ := C.mattersOf_prior Desig hD n m h
  have := C.born_unique m j i hm hmi
  omega

/-- Merge: a joint successor is live for every matter of every parent. -/
lemma anc_of_parent {m p q : Q} (hp : p ∈ C.par q) (h : C.anc m p) : C.anc m q :=
  h.tail hp

/-- Split: each successor of a resolved descendant is live for the same matter. -/
lemma mem_live_succ_of_parent {m p q : Q} {n : ℕ} (hq : q ∈ C.Born n) (hp : p ∈ C.par q)
    (hL : p ∈ C.Live n m) : q ∈ C.Live (n + 1) m := by
  refine mem_filter.2 ⟨?_, C.anc_of_parent hp (mem_filter.1 hL).2⟩
  rw [C.resolution_continuity n]; exact mem_union_right _ hq

end IssueTraceCore

/-! ### 4.3 Wait responsiveness: the primitive form -/

namespace IssueTrace

variable (T : IssueTrace Q D)

/-- The settled primitive: no fixed prerequisite is a permanent no-route wait. -/
def NoPermanentWait (m : Q) : Prop :=
  ∀ d N0, ∃ n, N0 ≤ n ∧ ¬ T.NoRouteWait n m d

/-- The "eventually `Met`" form implies the primitive form. -/
lemma noPermanentWait_of_waitResponsive {m : Q} (h : T.WaitResponsive m) :
    T.NoPermanentWait m := by
  intro d N0
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk, hmet⟩ := h d N0 hcon
  obtain ⟨_, _, _, hu, _⟩ := hcon k hk
  exact hu hmet

/-- And conversely, vacuously: the two are equivalent. -/
lemma waitResponsive_of_noPermanentWait {m : Q} (h : T.NoPermanentWait m) :
    T.WaitResponsive m := by
  intro d N0 hall
  obtain ⟨n, hn, hnot⟩ := h d N0
  exact absurd (hall n hn) hnot

/-- Persistent Opportunity from the primitive form. -/
theorem persistent_opportunity' (m : Q) (n0 : ℕ) (hm0 : m ∈ T.M n0)
    (hlive : ∀ n, n0 ≤ n → (T.Live n m).Nonempty) (h : T.NoPermanentWait m) :
    ∀ B, ∃ N, B < T.Omega N m :=
  T.persistent_opportunity m n0 hm0 hlive (T.waitResponsive_of_noPermanentWait h)

/-! ### 4.4 The positive-share attention witness -/

/-- Share `2^{-(idx m)-1}` for an injective index (e.g. birth order with a fixed
tie-break), charged exactly when the matter has work. -/
def shareAttention (idx : Q → ℕ) (n : ℕ) (m : Q) : ℚ :=
  if T.opp n m then (1 / 2 : ℚ) ^ (idx m + 1) else 0

lemma shareAttention_nonneg (idx : Q → ℕ) (n : ℕ) (m : Q) : 0 ≤ T.shareAttention idx n m := by
  unfold shareAttention; split_ifs <;> positivity

lemma shareAttention_le_opp (idx : Q → ℕ) (n : ℕ) (m : Q) :
    T.shareAttention idx n m ≤ if T.opp n m then 1 else 0 := by
  unfold shareAttention
  split_ifs
  · exact pow_le_one₀ (by norm_num) (by norm_num)
  · exact le_rfl

lemma geom_half_sum_le (N : ℕ) : ∑ k ∈ range N, (1 / 2 : ℚ) ^ (k + 1) ≤ 1 := by
  have : ∀ N, ∑ k ∈ range N, (1 / 2 : ℚ) ^ (k + 1) = 1 - (1 / 2 : ℚ) ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [sum_range_succ, ih]; ring
  rw [this]
  have : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ N := by positivity
  linarith

/-- Unit budget at every position, for any finite set of matters. -/
lemma shareAttention_sum_le_one (idx : Q → ℕ) (hidx : Function.Injective idx) (n : ℕ)
    (S : Finset Q) : ∑ m ∈ S, T.shareAttention idx n m ≤ 1 := by
  calc ∑ m ∈ S, T.shareAttention idx n m
      ≤ ∑ m ∈ S, (1 / 2 : ℚ) ^ (idx m + 1) := by
        apply sum_le_sum; intro m _
        unfold shareAttention; split_ifs
        · exact le_rfl
        · positivity
    _ = ∑ k ∈ S.image idx, (1 / 2 : ℚ) ^ (k + 1) := by
        rw [sum_image (fun a _ b _ h => hidx h)]
    _ ≤ ∑ k ∈ range ((S.image idx).sup id + 1), (1 / 2 : ℚ) ^ (k + 1) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [mem_range]
          have := le_sup (f := id) hk
          simp only [id] at this
          omega
        · intro k _ _; positivity
    _ ≤ 1 := geom_half_sum_le _

/-- `A_N(m) = w_m · Ω_N(m)` exactly. -/
lemma attention_share_eq (idx : Q → ℕ) (N : ℕ) (m : Q) :
    Attention (T.shareAttention idx) N m = (1 / 2 : ℚ) ^ (idx m + 1) * T.Omega N m := by
  unfold Attention shareAttention TraceData.Omega
  rw [← sum_boole, mul_sum]
  apply sum_congr rfl
  intro n _
  split_ifs <;> simp

/-- Hence non-starvation holds for every matter simultaneously. -/
theorem shareAttention_nonStarving (idx : Q → ℕ) (m : Q) :
    T.NonStarving (T.shareAttention idx) m := by
  intro hΩ C
  set w : ℚ := (1 / 2 : ℚ) ^ (idx m + 1) with hw
  have hwpos : 0 < w := by positivity
  obtain ⟨B, hB⟩ : ∃ B : ℕ, C / w < B := exists_nat_gt _
  obtain ⟨N, hN⟩ := hΩ B
  refine ⟨N, ?_⟩
  rw [attention_share_eq]
  have : (C / w) * w < (T.Omega N m : ℚ) * w := by
    apply mul_lt_mul_of_pos_right _ hwpos
    calc C / w < B := hB
      _ < T.Omega N m := by exact_mod_cast hN
  rw [div_mul_cancel₀ _ hwpos.ne'] at this
  linarith [this]

end IssueTrace

/-! ### 4.5 An inhabitant of the full issue-trace specification -/

namespace Fixtures

@[simp] lemma fixE_mem_O {n : ℕ} {q : BQ} : q ∈ fixE.O n ↔ 1 ≤ n := by
  simp only [fixE, mem_filter, mem_univ, true_and]
@[simp] lemma fixE_Res {n : ℕ} : fixE.Res n = ∅ := rfl
@[simp] lemma fixE_mem_Born {n : ℕ} {q : BQ} : q ∈ fixE.Born n ↔ n = 0 := by
  simp only [fixE, mem_filter, mem_univ, true_and]
@[simp] lemma fixE_par {q : BQ} : fixE.par q = ∅ := rfl
@[simp] lemma fixE_Pre {n : ℕ} {q : BQ} :
    fixE.Pre n q = if 2 ≤ n then {decide (q = BQ.a)} else ∅ := rfl
@[simp] lemma fixE_PreAdd {n : ℕ} {q : BQ} :
    fixE.PreAdd n q = if n = 1 then {decide (q = BQ.a)} else ∅ := rfl
@[simp] lemma fixE_PreDrop {n : ℕ} {q : BQ} : fixE.PreDrop n q = ∅ := rfl
@[simp] lemma fixE_intro {d : Bool} : fixE.intro d = 1 := rfl
@[simp] lemma fixE_Met {n : ℕ} {d : Bool} : ¬ fixE.Met n d := by simp [fixE]
@[simp] lemma fixE_mem_M {n : ℕ} {q : BQ} : q ∈ fixE.M n ↔ 1 ≤ n := by
  simp only [fixE, mem_filter, mem_univ, true_and]

/-- Fixture E satisfies every other requirement. -/
theorem fixE_other_requirements : OtherRequirements fixE := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q n k hn hk; rw [fixE_mem_Born] at hn hk; omega
  · intro q n hq; rw [fixE_mem_Born] at hq; rw [fixE_mem_O]; omega
  · intro q n hq; rw [fixE_mem_O] at hq; exact ⟨0, by omega, by rw [fixE_mem_Born]⟩
  · intro n; simp
  · intro n; ext q; simp; omega
  · intro n q _ p hp; simp at hp
  · intro n q hO hO'
    rw [fixE_mem_O] at hO
    by_cases h : 2 ≤ n
    · simp [h, show 2 ≤ n + 1 by omega, show ¬ n = 1 by omega]
    · have : n = 1 := by omega
      subst this; simp
  · intro n q hq; rw [fixE_mem_Born] at hq; subst hq; simp
  · intro n q d hd
    by_cases h : n = 1
    · simp [h]
    · simp [h] at hd
  · intro n q d hd r hr
    by_cases h : n = 1
    · subst h; simp
    · simp [h] at hd
  · intro n d h; exact h
  · intro n q hq; simp at hq
  · intro n m hm; rw [fixE_mem_M] at hm ⊢; omega
  · intro n m hm; rw [fixE_mem_M] at hm; exact ⟨0, by omega, by rw [fixE_mem_Born]⟩

/-- Fixture E satisfies the reach gate: its only prerequisite additions are at position
1, where both matters have work (`a` and `t` are ready). -/
theorem fixE_reach_gate : ReachGate fixE := by
  intro n q hO hO' hadd m hm hR
  have hn : n = 1 := by
    by_contra hne; simp [hne] at hadd
  subst hn
  have hOq : ∀ q, q ∈ fixE.O 1 := by intro q; simp
  refine ⟨m, mem_filter.2 ⟨?_, Or.inl ?_⟩⟩
  · exact mem_filter.2 ⟨hOq m, m, mem_filter.2 ⟨hOq m, ReflTransGen.refl⟩, ReflTransGen.refl⟩
  · intro d hd; simp at hd

/-- The specification is inhabited. -/
def fixE_issueTrace : IssueTrace BQ Bool := toIssueTrace fixE fixE_other_requirements fixE_reach_gate

theorem fixE_issueTrace_nonvacuous : (fixE_issueTrace.Live 1 BQ.a).Nonempty :=
  ⟨BQ.a, mem_filter.2 ⟨by simp [fixE_issueTrace, toIssueTrace], ReflTransGen.refl⟩⟩

end Fixtures

/-! ## 5. Unified grounds and answerable defeat (2026-09-02)

Round `2026-09-02-unified-grounds-answerable-defeat`, answering `PRIORITIES.md`
item 77. Rests on the **Defeat Principle**, adopted by maintainer ruling
(`DECISIONS.md`, 2026-09-03): no participant extinguishes a debt; a participant may pay
it — `answer` — or move it onto the grounds for saying it is not owed — `dispose`; only
`settle` extinguishes. The 2026-09-02 round ran under it as a hypothesis.

`StandingTrace`, `Licensing` and `StandingTrace.Grounded` are gone as primitives.
Standing occurrences are issues of a licence kind on the *same* trace, so that
`Ladd` is birth, `Ldel` is resolution, `grounds` is `par`, and `Fresh` is
`born_unique`. What was Requirement 1's `step` is literally `resolution_continuity`.
Everything the standing layer proved is re-derived here from `anc`, with two
exceptions recorded honestly in `DEFEAT.md` §2: the `Auth` filter on grounds and
the nonemptiness of grounds are *not* consequences of ancestry and are carried as
side conditions on licence-kind issues.

Names are provisional (`AGENTS.md` standard 6). -/

section Unified

/-- A **ground** is a prior issue or a settlement fact. The sum is the point of the
round: a disposal's grounds may mix issues already in the record with facts the world
settled, and no pre-unification type held both. -/
abbrev Ground (Q S : Type*) := Q ⊕ S

/-- The three resolution kinds, and there is deliberately no fourth. `answer` rebuts
the challenge-warrant and discharges content; `dispose G` undercuts the
challenge-warrant on grounds `G` and *moves* the content; `settle s` records that the
world lowered the level of demand. -/
inductive Kind (Q S : Type*) where
  | answer : Kind Q S
  | dispose : Finset (Ground Q S) → Kind Q S
  | settle : S → Kind Q S

namespace Kind

variable {Q S : Type*}

/-- The Defeat Principle, as a predicate on kinds: `answer` and `settle` extinguish
content, `dispose` does not. -/
def Discharges : Kind Q S → Prop
  | answer => True
  | dispose _ => False
  | settle _ => True

/-- `dispose` is the only kind that does not discharge. -/
lemma discharges_iff_not_dispose (k : Kind Q S) :
    k.Discharges ↔ ∀ G, k ≠ dispose G := by
  cases k <;> simp [Discharges]

end Kind

/-- A **defeat trace**: an issue trace whose resolutions carry a kind, a resolver and
an opener, over a type `S` of settlement facts and a type `A` of participants.

`Settled` is monotone. Its independence from any participant's write set is an
explicit hypothesis where it is used, not a field, because §5's fixture tests the
necessity of that independence. -/
structure DefeatTrace (Q D S A : Type*) extends IssueTrace Q D where
  /-- Settlement facts, monotone in the prefix. -/
  Settled : ℕ → S → Prop
  settled_mono : ∀ n s, Settled n s → Settled (n + 1) s
  /-- How each resolution resolved. -/
  kind : ℕ → Q → Kind Q S
  /-- Who resolved it. -/
  resolver : ℕ → Q → A
  /-- Who opened it. -/
  opener : Q → A
  /-- **The one new structural requirement.** A disposal in batch `n` is accompanied
  by a fresh successor carrying the load: this is `fresh_successors` read in reverse,
  and it is the Defeat Principle made structural. -/
  dispose_successor : ∀ n q G, q ∈ Res n → kind n q = Kind.dispose G →
    ∃ q' ∈ Born n, q ∈ par q'
  /-- **`Met` is no longer a primitive judgment.** A prerequisite is met exactly when
  every route root was resolved strictly earlier *by answer or settlement*. A disposed
  root does not meet anything. -/
  met_def : ∀ n d, Met n d ↔
    ∀ t ∈ roots d, ∃ k < n, t ∈ Res k ∧ (kind k t).Discharges

namespace DefeatTrace

variable {Q D S A : Type*} (T : DefeatTrace Q D S A)

open TraceData IssueTrace

/-- `Grounded n g`: the ground is available at prefix `n`. An issue is available when
it is in the record strictly before `n` — outstanding or resolved, it makes no
difference, what matters is that the record already carried it. A settlement fact is
available when it is settled. -/
def Grounded (n : ℕ) : Ground Q S → Prop
  | Sum.inl q => ∃ j < n, q ∈ T.Born j
  | Sum.inr s => T.Settled n s

lemma grounded_mono {n k : ℕ} {g : Ground Q S} (h : T.Grounded n g) (hnk : n ≤ k) :
    T.Grounded k g := by
  cases g with
  | inl q => obtain ⟨j, hj, hq⟩ := h; exact ⟨j, by omega, hq⟩
  | inr s =>
    induction hnk with
    | refl => exact h
    | step _ ih => exact T.settled_mono _ _ ih

/-- Every issue in the record before `n` is grounded, which is the unified reading of
"in force". -/
lemma grounded_of_out {n : ℕ} {q : Q} (hq : q ∈ T.O n) : T.Grounded n (Sum.inl q) :=
  T.out_born q n hq

/-! ### 5.1 What the standing layer proved, re-derived from ancestry -/

/-- **Freshness is `born_unique`.** What `StandingTrace.Fresh` postulated — a newly
admitted occurrence was in force at no earlier prefix — is a *theorem* of the unified
trace, from birth uniqueness and the list discipline alone. -/
theorem fresh : ∀ n q, q ∈ T.Born n → ∀ k, k ≤ n → q ∉ T.O k := by
  intro n q hq k hk hmem
  obtain ⟨j, hj, hqj⟩ := T.out_born q k hmem
  have hnj : n = j := T.born_unique q n j hq hqj
  omega

/-- **Grounded Replay, unified.** Every issue in the record descends by `anc` from a
parentless issue: the authorization tree of paper Theorem 1, with the strictly
decreasing positions now a consequence of `parent_out` rather than a hypothesis.

This replaces `StandingTrace.grounded_replay`. What it does *not* replace is that
theorem's `Auth` filter — see `DEFEAT.md` §2. -/
theorem grounded_replay : ∀ n q, q ∈ T.Born n → ∃ r, T.anc r q ∧ T.par r = ∅ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro q hq
    by_cases hpar : T.par q = ∅
    · exact ⟨q, ReflTransGen.refl, hpar⟩
    · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.2 hpar
      have hpo : p ∈ T.O n := T.parent_out hq hp
      obtain ⟨j, hj, hpj⟩ := T.out_born p n hpo
      obtain ⟨r, hr, hrpar⟩ := ih j hj p hpj
      exact ⟨r, hr.tail hp, hrpar⟩

/-- The live form: every outstanding issue has an authorization tree. -/
theorem grounded_replay_live {n : ℕ} {q : Q} (hq : q ∈ T.O n) :
    ∃ r, T.anc r q ∧ T.par r = ∅ := by
  obtain ⟨j, _, hqj⟩ := T.out_born q n hq
  exact T.grounded_replay j q hqj

/-! ### 5.2 Standing derived from live licence-issues -/

/-- A licensing relation carried by the trace itself: `lic q b κ τ x` says the
licence-kind issue `q` licenses **participant `b`** to hold anchor `κ` for `(τ, x)`.

The participant argument is the 2026-09-03 repair. Without it `standsFor` records
only that *somebody* has standing, and `Answerable.contested` — which binds a `b`
distinct from the resolver and then asks a question not mentioning `b` — is satisfied
by any participant type with two elements. `STANDING_REPAIR.md` §1. -/
structure Licence (Q A K Ty X : Type*) where
  lic : Q → A → K → Ty → X → Prop

/-- `b ⊩_n (κ, τ, x)`: some *live issue* licenses `b` for `κ`. What was
`Licensing.standsFor` reading a separate `StandingTrace.L` is now a filter on `O n`. -/
def standsFor {K Ty X : Type*} (Li : Licence Q A K Ty X) (n : ℕ) (b : A) (κ : K)
    (τ : Ty) (x : X) : Prop :=
  ∃ q ∈ T.O n, Li.lic q b κ τ x

/-- Requirement 2 on the unified trace: a fresh issue's protocol is licensed *for
someone*. -/
def AnchorStanding {K Ty X : Type*} (Li : Licence Q A K Ty X)
    (κ : Q → K) (τ : Q → Ty) (x : Q → X) : Prop :=
  ∀ n q, q ∈ T.Born n → ∃ b, T.standsFor Li n b (κ q) (τ q) (x q)

/-- **`anchor_grounded`, re-derived.** The licence-issue licensing a fresh issue's
protocol is itself in the record and has an authorization tree — and it licenses it
for a named participant. One trace, one theorem; the two-layer bridge is gone. -/
theorem anchor_grounded {K Ty X : Type*} (Li : Licence Q A K Ty X)
    (κ : Q → K) (τ : Q → Ty) (x : Q → X) (h : T.AnchorStanding Li κ τ x)
    {n : ℕ} {q : Q} (hq : q ∈ T.Born n) :
    ∃ b, ∃ l ∈ T.O n, Li.lic l b (κ q) (τ q) (x q) ∧ ∃ r, T.anc r l ∧ T.par r = ∅ := by
  obtain ⟨b, l, hl, hlic⟩ := h n q hq
  exact ⟨b, l, hl, hlic, T.grounded_replay_live hl⟩

/-! ### 5.3 `Met` as a definition, and what a disposal cannot do -/

/-- **Requirement 9 is now a theorem.** Persistent satisfaction follows from `met_def`
by weakening `k < n` to `k < n + 1`; it needed no separate postulate once `Met` reads
the record. -/
theorem met_persistent' : ∀ n d, T.Met n d → T.Met (n + 1) d := by
  intro n d h
  rw [T.met_def] at h ⊢
  intro t ht
  obtain ⟨k, hk, hres, hdis⟩ := h t ht
  exact ⟨k, by omega, hres, hdis⟩

/-- A disposed root never contributes to `Met`. This is the Defeat Principle at the
structural level: disposal moves a debt, it does not discharge one. -/
theorem dispose_not_met {n k : ℕ} {d : D} {t : Q} {G : Finset (Ground Q S)}
    (ht : t ∈ T.roots d) (hk : T.kind k t = Kind.dispose G)
    (huniq : ∀ j, t ∈ T.Res j → j = k) (hn : T.Met n d) : False := by
  rw [T.met_def] at hn
  obtain ⟨j, _, hresj, hdis⟩ := hn t ht
  rw [huniq j hresj, hk] at hdis
  exact hdis

/-- **A prerequisite cannot be disposed away.** If a route root is disposed, the route
is nonempty at the next prefix: the successor the disposal was required to open is
itself a route root's descendant, so `Routes` — being ancestry-closed — picks it up
with no new axiom. This is the strengthening of `persistent_wait` the round set out to
test, and it holds. -/
theorem routes_survive_dispose {n : ℕ} {d : D} {t : Q} {G : Finset (Ground Q S)}
    (ht : t ∈ T.roots d) (hres : t ∈ T.Res n) (hk : T.kind n t = Kind.dispose G) :
    (T.Routes (n + 1) d).Nonempty := by
  obtain ⟨q', hq', hpar⟩ := T.dispose_successor n t G hres hk
  refine ⟨q', mem_filter.2 ⟨?_, ⟨t, ht, ReflTransGen.single hpar⟩⟩⟩
  rw [T.resolution_continuity n]
  exact mem_union_right _ hq'

/-! ### 5.4 Answerable disposal -/

/-- **Answerable disposal** (D1–D3). `q` is disposed at `n` on grounds `G` with
successor `q'`, and:

* **D1 grounded** — every ground is available at `n`, and `q` is not among them.
  The second conjunct is *not* redundant: see `self_grounding_not_excluded_by_priority`.
* **D2 routed** — the successor is fresh in this batch and inherits `q`'s load.
* **D3 separated** — someone other than the resolver has standing on the successor,
  and some ground was opened by someone other than the resolver. -/
structure Answerable {K Ty X : Type*} (Li : Licence Q A K Ty X) (κ : Q → K) (τ : Q → Ty)
    (x : Q → X) (n : ℕ) (q : Q) (G : Finset (Ground Q S)) (q' : Q) : Prop where
  /-- D1. -/
  grounded : ∀ g ∈ G, T.Grounded n g
  /-- D1, the clause ancestry does not supply. -/
  not_self : Sum.inl q ∉ G
  /-- D2. -/
  born : q' ∈ T.Born n
  /-- D2. -/
  inherits : q ∈ T.par q'
  /-- D3, standing side. `b` now occurs in the body, which is the whole of the
  2026-09-03 repair: this says a *named participant other than the resolver* holds
  standing on the successor. -/
  contested : ∃ b, b ≠ T.resolver n q ∧ T.standsFor Li n b (κ q') (τ q') (x q')
  /-- D3, grounds side. -/
  foreign_ground : ∃ g ∈ G, ∀ p : Q, g = Sum.inl p → T.opener p ≠ T.resolver n q

/-- A **defeat-disciplined** trace: every resolution answers, disposes answerably, or
settles a fact that is settled. -/
def Disciplined {K Ty X : Type*} (Li : Licence Q A K Ty X) (κ : Q → K) (τ : Q → Ty)
    (x : Q → X) : Prop :=
  ∀ n q, q ∈ T.Res n →
    T.kind n q = Kind.answer ∨
    (∃ G q', T.kind n q = Kind.dispose G ∧ T.Answerable Li κ τ x n q G q') ∨
    (∃ s, T.kind n q = Kind.settle s ∧ T.Settled n s)

/-! ### 5.5 No self-grounding, and exactly where it comes from -/

/-- **The successor cannot ground the disposal**, and neither can anything else born
in the same batch. This is the transition-certificates round's postulate 5 collapsing
again: priority alone refuses it, with no dedicated clause. -/
theorem no_grounding_in_batch {n : ℕ} {q' : Q} (hq' : q' ∈ T.Born n) :
    ¬ T.Grounded n (Sum.inl q') := by
  rintro ⟨j, hj, hqj⟩
  rw [T.born_unique q' n j hq' hqj] at hj
  omega

/-- **But priority does *not* refuse self-grounding.** A disposed issue is by
construction in the record strictly before its own disposal, so `Grounded` holds of
it. Postulate 5 therefore re-derives on the unified trace for the successor and the
batch, and *fails* for the issue itself — which is why `Answerable.not_self` is a
clause and not a lemma. Reported as a finding in `DEFEAT.md` §2. -/
theorem self_grounding_not_excluded_by_priority {n : ℕ} {q : Q} (hq : q ∈ T.Res n) :
    T.Grounded n (Sum.inl q) :=
  T.grounded_of_out (T.res_subset n hq)

/-- With the clause in place, no answerable disposal is grounded in itself, its
successor, or anything born in its batch. -/
theorem no_self_grounding {K Ty X : Type*} {Li : Licence Q A K Ty X} {κ : Q → K}
    {τ : Q → Ty} {x : Q → X} {n : ℕ} {q q' : Q} {G : Finset (Ground Q S)}
    (hA : T.Answerable Li κ τ x n q G q') :
    Sum.inl q ∉ G ∧ ∀ b ∈ T.Born n, Sum.inl b ∉ G :=
  ⟨hA.not_self, fun _ hb hmem => T.no_grounding_in_batch hb (hA.grounded _ hmem)⟩

/-! ### 5.7 Laundering, both sides (2026-09-03)

Before the standing repair, `Answerable.contested` bound a participant it never
mentioned again, so the standing half of D3 was vacuous and every laundering result
rested on `foreign_ground` alone. With `b` in the body both halves carry weight, and
the standing half independently refuses a single-handed disposal. -/

/-- A disposal edge is **in one hand** for `a` when `a` resolved it, `a` opened every
issue it cites, and only `a` holds standing on its successor.

Note what the middle clause does *not* say: a **settlement** ground constrains nothing,
because no participant opened it. That is deliberate — a fact the world settled is
foreign to everyone — and it is why the standing clause is needed rather than
decorative: an edge citing only settlement facts satisfies `foreign_ground` trivially
and is refused, if at all, by `contested`. -/
structure InOneHand {K Ty X : Type*} (Li : Licence Q A K Ty X) (κ : Q → K) (τ : Q → Ty)
    (x : Q → X) (a : A) (n : ℕ) (q : Q) (G : Finset (Ground Q S)) (q' : Q) : Prop where
  resolved : T.resolver n q = a
  grounds_own : ∀ p : Q, Sum.inl p ∈ G → T.opener p = a
  standing_own : ∀ b, T.standsFor Li n b (κ q') (τ q') (x q') → b = a

/-- **The standing side alone refuses a single-handed edge.** This is the theorem the
pre-repair `contested` could not prove, and the reason the repair matters: it consumes
`contested` and nothing else. -/
theorem not_in_one_hand_of_contested {K Ty X : Type*} {Li : Licence Q A K Ty X}
    {κ : Q → K} {τ : Q → Ty} {x : Q → X} {a : A} {n : ℕ} {q q' : Q}
    {G : Finset (Ground Q S)} (hA : T.Answerable Li κ τ x n q G q') :
    ¬ T.InOneHand Li κ τ x a n q G q' := by
  rintro ⟨hres, -, hstand⟩
  obtain ⟨b, hb, hsb⟩ := hA.contested
  exact hb (by rw [hstand b hsb, hres])

/-- **What the grounds side actually gives**, stated exactly rather than overstated:
the foreign ground is either a settlement fact — foreign to every participant, since
nobody opened it — or an issue opened by somebody other than the resolver. The first
disjunct is why `foreign_ground` cannot carry the laundering argument by itself. -/
theorem foreign_ground_dichotomy {K Ty X : Type*} {Li : Licence Q A K Ty X}
    {κ : Q → K} {τ : Q → Ty} {x : Q → X} {n : ℕ} {q q' : Q}
    {G : Finset (Ground Q S)} (hA : T.Answerable Li κ τ x n q G q') :
    ∃ g ∈ G, (∃ s : S, g = Sum.inr s) ∨
      (∃ p : Q, g = Sum.inl p ∧ T.opener p ≠ T.resolver n q) := by
  obtain ⟨g, hg, hfor⟩ := hA.foreign_ground
  refine ⟨g, hg, ?_⟩
  cases g with
  | inl p => exact Or.inr ⟨p, rfl, hfor p rfl⟩
  | inr s => exact Or.inl ⟨s, rfl⟩

/-- A **laundering walk** for `a`: a nonempty chain of disposal edges every one of
which is in `a`'s hand. -/
def LaunderingWalk {K Ty X : Type*} (Li : Licence Q A K Ty X) (κ : Q → K) (τ : Q → Ty)
    (x : Q → X) (a : A) (w : List (ℕ × Q × Finset (Ground Q S) × Q)) : Prop :=
  w ≠ [] ∧ ∀ e ∈ w, T.InOneHand Li κ τ x a e.1 e.2.1 e.2.2.1 e.2.2.2

/-- **Separation forbids laundering walks.** In a trace whose disposals are answerable,
no walk is in one hand — and after the repair this is proved from the standing side. -/
theorem no_laundering_walk {K Ty X : Type*} {Li : Licence Q A K Ty X} {κ : Q → K}
    {τ : Q → Ty} {x : Q → X} {a : A}
    {w : List (ℕ × Q × Finset (Ground Q S) × Q)}
    (hans : ∀ e ∈ w, T.Answerable Li κ τ x e.1 e.2.1 e.2.2.1 e.2.2.2) :
    ¬ T.LaunderingWalk Li κ τ x a w := by
  rintro ⟨hne, hall⟩
  cases w with
  | nil => exact hne rfl
  | cons e t =>
    exact T.not_in_one_hand_of_contested (hans e (by simp)) (hall e (by simp))

/-! ### 5.8 The principal-relative form (definition and one theorem only)

Stated because the coalition question is the author's and stays in the queue: this is
**not** the general non-capture predicate. It is what one gets by naming a protected
participant, and the theorem is the one-line consequence of naming one. -/

/-- `AnswerableFor P`: answerable, and `P` specifically holds standing on the
successor. -/
structure AnswerableFor {K Ty X : Type*} (Li : Licence Q A K Ty X) (κ : Q → K)
    (τ : Q → Ty) (x : Q → X) (P : A) (n : ℕ) (q : Q) (G : Finset (Ground Q S)) (q' : Q)
    extends T.Answerable Li κ τ x n q G q' : Prop where
  principal_stands : T.standsFor Li n P (κ q') (τ q') (x q')

/-- **No coalition excluding `P` holds all the standing on a `P`-answerable disposal.**
The alternating two-participant walk that defeats plain separation is defeated by this,
because that walk's coalition does not contain `P`. It buys that at the price of naming
a party, which is exactly the reservation left to the author. -/
theorem no_coalition_excluding_principal {K Ty X : Type*} {Li : Licence Q A K Ty X}
    {κ : Q → K} {τ : Q → Ty} {x : Q → X} {P : A} {C : Set A} {n : ℕ} {q q' : Q}
    {G : Finset (Ground Q S)} (hP : P ∉ C)
    (hA : T.AnswerableFor Li κ τ x P n q G q') :
    ¬ (∀ b, T.standsFor Li n b (κ q') (τ q') (x q') → b ∈ C) :=
  fun hall => hP (hall P hA.principal_stands)

/-! ### 5.6 Liveness under defeat -/

/-- **T2's corollary.** A matter whose live issues resolve only by disposal keeps a
live issue at the next prefix: each disposal hands the load to a fresh descendant, and
`Live` is ancestry-filtered, so the frontier cannot empty. -/
theorem live_nonempty_of_dispose_only {m : Q} {n : ℕ} (hlive : (T.Live n m).Nonempty)
    (hdisp : ∀ q ∈ T.Live n m, q ∈ T.Res n → ∃ G, T.kind n q = Kind.dispose G) :
    (T.Live (n + 1) m).Nonempty := by
  obtain ⟨q, hq⟩ := hlive
  obtain ⟨hqO, hanc⟩ := mem_filter.1 hq
  by_cases hres : q ∈ T.Res n
  · obtain ⟨G, hG⟩ := hdisp q hq hres
    obtain ⟨q', hq', hpar⟩ := T.dispose_successor n q G hres hG
    refine ⟨q', mem_filter.2 ⟨?_, hanc.tail hpar⟩⟩
    rw [T.resolution_continuity n]
    exact mem_union_right _ hq'
  · refine ⟨q, mem_filter.2 ⟨?_, hanc⟩⟩
    rw [T.resolution_continuity n]
    exact mem_union_left _ (mem_sdiff.2 ⟨hqO, hres⟩)

end DefeatTrace

/-! ### 5.9 A witness: `Disciplined` is satisfiable (2026-09-03)

PR79 stated `DefeatTrace` and `Disciplined` and exhibited no Lean inhabitant of
either; its own report named "nothing here shows a defeat-disciplined trace exists"
as a gap. This closes it, in the style of `Fixtures.fixE_issueTrace`.

`witness` is a five-issue trace with one **answered** issue, one **settled** issue, and
one **answerable disposal** carrying its successor — the three kinds, each exercised
once. `witnessBad` is the same trace with the disposal grounded in itself, and is
proved to fail `Answerable` by **exactly one clause**: `not_self`. Every other clause
is proved to hold of it, which is the Lean form of the round's first finding that
priority alone does not refuse self-grounding. -/

namespace Witness

/-- Five issues: a licence, an answered issue, a settled issue, a disposed issue and
its successor. -/
inductive WQ | lic | ans | stl | dis | dis1
  deriving DecidableEq, Fintype

open WQ

/-- Two participants: `true` is the principal `P`, `false` the advisor `V`. -/
abbrev WA := Bool

/-- No prerequisites, so `Met` and the wait machinery are vacuous and the witness
isolates the resolution kinds. -/
abbrev WD := Empty

/-- One settlement fact. -/
abbrev WS := Unit

/-- Where each issue is born. -/
def bornAt : WQ → ℕ
  | dis1 => 1
  | _ => 0

/-- Where each issue is resolved. `lic` and `dis1` are never resolved, and are excluded
from `wRes` by name; `2` is a placeholder that keeps `wO` monotone for them. -/
def resAt : WQ → ℕ
  | ans => 1
  | stl => 1
  | dis => 1
  | _ => 2

/-- The issues that actually get resolved. -/
def Resolves (q : WQ) : Prop := q ≠ lic ∧ q ≠ dis1

instance : DecidablePred Resolves := fun q => by unfold Resolves; infer_instance

def wBorn (n : ℕ) : Finset WQ := Finset.univ.filter (fun q => bornAt q = n)
def wRes (n : ℕ) : Finset WQ := Finset.univ.filter (fun q => resAt q = n ∧ Resolves q)
def wO (n : ℕ) : Finset WQ :=
  Finset.univ.filter (fun q => bornAt q < n ∧ ¬ (resAt q < n ∧ Resolves q))

def wpar : WQ → Finset WQ
  | dis1 => {dis}
  | _ => ∅

@[simp] lemma mem_wBorn {q : WQ} {n : ℕ} : q ∈ wBorn n ↔ bornAt q = n := by simp [wBorn]

@[simp] lemma mem_wRes {q : WQ} {n : ℕ} : q ∈ wRes n ↔ (resAt q = n ∧ Resolves q) := by
  simp [wRes]

@[simp] lemma mem_wO {q : WQ} {n : ℕ} :
    q ∈ wO n ↔ (bornAt q < n ∧ ¬ (resAt q < n ∧ Resolves q)) := by simp [wO]

lemma wpar_of_ne {q : WQ} (h : q ≠ dis1) : wpar q = ∅ := by
  cases q <;> simp_all [wpar]

/-- The grounds of the honest disposal: the licence issue, born strictly earlier and
opened by the principal. -/
def wG : Finset (Ground WQ WS) := {Sum.inl lic}

/-- The grounds of the dishonest one: the disposed issue itself. -/
def wGbad : Finset (Ground WQ WS) := {Sum.inl dis}

def wkind : ℕ → WQ → Kind WQ WS
  | 1, ans => Kind.answer
  | 1, stl => Kind.settle ()
  | 1, dis => Kind.dispose wG
  | _, _ => Kind.answer

def wkindBad : ℕ → WQ → Kind WQ WS
  | 1, ans => Kind.answer
  | 1, stl => Kind.settle ()
  | 1, dis => Kind.dispose wGbad
  | _, _ => Kind.answer

/-- `V` resolves; `P` opened everything, so the licence ground is foreign to `V`. -/
def wresolver : ℕ → WQ → WA := fun _ _ => false
def wopener : WQ → WA := fun _ => true

def wdata : TraceData WQ WD where
  O := wO
  Res := wRes
  Born := wBorn
  par := wpar
  Pre := fun _ _ => ∅
  PreAdd := fun _ _ => ∅
  PreDrop := fun _ _ => ∅
  roots := fun e => e.elim
  intro := fun e => e.elim
  Met := fun _ e => e.elim
  M := fun _ => ∅

theorem wdata_other : Fixtures.OtherRequirements wdata := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q n k hn hk
    simp only [wdata, mem_wBorn] at hn hk; omega
  · intro q n hn
    simp only [wdata, mem_wBorn] at hn
    simp only [wdata, mem_wO]; omega
  · intro q n hn
    simp only [wdata, mem_wO] at hn
    exact ⟨bornAt q, hn.1, by simp [wdata]⟩
  · intro n q hq
    simp only [wdata, mem_wRes] at hq
    simp only [wdata, mem_wO]
    obtain ⟨h1, h2⟩ := hq
    refine ⟨?_, by omega⟩
    revert h1 h2; cases q <;> simp [bornAt, resAt, Resolves] <;> omega
  · intro n
    ext q
    simp only [wdata, Finset.mem_union, Finset.mem_sdiff, mem_wO, mem_wRes, mem_wBorn]
    cases q <;> simp [bornAt, resAt, Resolves] <;> omega
  · intro n q hq p hp
    rcases eq_or_ne q dis1 with rfl | hne
    · simp only [wdata, wpar, Finset.mem_singleton] at hp
      subst hp
      simp only [wdata, mem_wBorn, bornAt] at hq
      subst hq
      simp [wdata, resAt, Resolves]
    · rw [show (wdata.par q) = wpar q from rfl, wpar_of_ne hne] at hp
      simp at hp
  · intro n q _ _; simp [wdata]
  · intro n q _; simp [wdata]
  · intro n q d hd; simp [wdata] at hd
  · intro n q d hd; simp [wdata] at hd
  · intro n e; exact e.elim
  · intro n q _ d hd; simp [wdata] at hd
  · intro n m hm; simp [wdata] at hm
  · intro n m hm; simp [wdata] at hm

theorem wdata_reach : Fixtures.ReachGate wdata := by
  intro n q _ _ hne; simp [wdata] at hne

/-- The witness as an `IssueTrace`. -/
def witnessIssue : IssueTrace WQ WD :=
  Fixtures.toIssueTrace wdata wdata_other wdata_reach

/-- **The witness.** A defeat trace with one answer, one settlement and one disposal. -/
def witness : DefeatTrace WQ WD WS WA :=
  { witnessIssue with
    Settled := fun n _ => 1 ≤ n
    settled_mono := fun n _ h => by omega
    kind := wkind
    resolver := wresolver
    opener := wopener
    dispose_successor := by
      intro n q G hres hk
      have hq : resAt q = n ∧ Resolves q := by
        simpa [witnessIssue, Fixtures.toIssueTrace, wdata] using hres
      obtain ⟨h1, h2⟩ := hq
      have hqd : q = dis := by
        cases q with
        | lic => exact absurd rfl h2.1
        | dis1 => exact absurd rfl h2.2
        | ans =>
          rw [show resAt ans = 1 from rfl] at h1; subst h1; simp [wkind] at hk
        | stl =>
          rw [show resAt stl = 1 from rfl] at h1; subst h1; simp [wkind] at hk
        | dis => rfl
      subst hqd
      rw [show resAt dis = 1 from rfl] at h1; subst h1
      exact ⟨dis1, by simp [witnessIssue, Fixtures.toIssueTrace, wdata, bornAt],
        by simp [witnessIssue, Fixtures.toIssueTrace, wdata, wpar]⟩
    met_def := by intro n e; exact e.elim }

@[simp] lemma witness_Born (n : ℕ) : witness.Born n = wBorn n := rfl
@[simp] lemma witness_Res (n : ℕ) : witness.Res n = wRes n := rfl
@[simp] lemma witness_O (n : ℕ) : witness.O n = wO n := rfl
@[simp] lemma witness_par (q : WQ) : witness.par q = wpar q := rfl
@[simp] lemma witness_kind (n : ℕ) (q : WQ) : witness.kind n q = wkind n q := rfl
@[simp] lemma witness_resolver (n : ℕ) (q : WQ) : witness.resolver n q = false := rfl
@[simp] lemma witness_opener (q : WQ) : witness.opener q = true := rfl
@[simp] lemma witness_Settled (n : ℕ) (s : WS) : witness.Settled n s ↔ 1 ≤ n := Iff.rfl

/-- The licence licenses the principal, and nobody else. -/
def wlic : DefeatTrace.Licence WQ WA Unit Unit Unit where
  lic q b _ _ _ := q = lic ∧ b = true

theorem witness_grounded_lic : witness.Grounded 1 (Sum.inl lic) := by
  refine ⟨0, by omega, ?_⟩
  simp [bornAt]

theorem witness_stands_P : witness.standsFor wlic 1 true () () () := by
  refine ⟨lic, ?_, rfl, rfl⟩
  simp [bornAt, resAt, Resolves]

/-- **The disposal is answerable.** All six clauses. -/
theorem witness_answerable :
    witness.Answerable wlic (fun _ => ()) (fun _ => ()) (fun _ => ()) 1 dis wG dis1 where
  grounded := by
    intro g hg
    rw [wG, Finset.mem_singleton] at hg
    subst hg
    exact witness_grounded_lic
  not_self := by simp [wG]
  born := by simp [bornAt]
  inherits := by simp [wpar]
  contested := ⟨true, by simp, witness_stands_P⟩
  foreign_ground := ⟨Sum.inl lic, by simp [wG], by rintro p ⟨rfl⟩; simp⟩

/-- **`Disciplined` is satisfiable.** Every resolution in the witness is an answer, an
answerable disposal, or a settlement of a settled fact. -/
theorem witness_disciplined :
    witness.Disciplined wlic (fun _ => ()) (fun _ => ()) (fun _ => ()) := by
  intro n q hres
  have hq : resAt q = n ∧ Resolves q := by simpa using hres
  obtain ⟨h1, h2⟩ := hq
  cases q with
  | lic => exact absurd rfl h2.1
  | dis1 => exact absurd rfl h2.2
  | ans =>
    rw [show resAt ans = 1 from rfl] at h1; subst h1
    exact Or.inl rfl
  | stl =>
    rw [show resAt stl = 1 from rfl] at h1; subst h1
    exact Or.inr (Or.inr ⟨(), rfl, by simp⟩)
  | dis =>
    rw [show resAt dis = 1 from rfl] at h1; subst h1
    exact Or.inr (Or.inl ⟨wG, dis1, rfl, witness_answerable⟩)

/-! #### The witness that fails by exactly one clause -/

/-- The same trace, with the disposal grounded in itself. -/
def witnessBad : DefeatTrace WQ WD WS WA :=
  { witnessIssue with
    Settled := fun n _ => 1 ≤ n
    settled_mono := fun n _ h => by omega
    kind := wkindBad
    resolver := wresolver
    opener := wopener
    met_def := by intro n e; exact e.elim
    dispose_successor := by
      intro n q G hres hk
      have hq : resAt q = n ∧ Resolves q := by
        simpa [witnessIssue, Fixtures.toIssueTrace, wdata] using hres
      obtain ⟨h1, h2⟩ := hq
      have hqd : q = dis := by
        cases q with
        | lic => exact absurd rfl h2.1
        | dis1 => exact absurd rfl h2.2
        | ans => rw [show resAt ans = 1 from rfl] at h1; subst h1; simp [wkindBad] at hk
        | stl => rw [show resAt stl = 1 from rfl] at h1; subst h1; simp [wkindBad] at hk
        | dis => rfl
      subst hqd
      rw [show resAt dis = 1 from rfl] at h1; subst h1
      exact ⟨dis1, by simp [witnessIssue, Fixtures.toIssueTrace, wdata, bornAt],
        by simp [witnessIssue, Fixtures.toIssueTrace, wdata, wpar]⟩ }

@[simp] lemma witnessBad_Born (n : ℕ) : witnessBad.Born n = wBorn n := rfl
@[simp] lemma witnessBad_par (q : WQ) : witnessBad.par q = wpar q := rfl

/-- **The finding, in Lean.** The self-grounded disposal *is* grounded — priority
refuses it nothing, because the disposed issue is in the record strictly before its own
disposal. Compare `self_grounding_not_excluded_by_priority`. -/
theorem witnessBad_grounded : witnessBad.Grounded 1 (Sum.inl dis) := by
  refine ⟨0, by omega, ?_⟩
  simp [bornAt]

/-- Its birth and inheritance clauses hold too. -/
theorem witnessBad_born : dis1 ∈ witnessBad.Born 1 := by simp [bornAt]

theorem witnessBad_inherits : dis ∈ witnessBad.par dis1 := by simp [wpar]

/-- **So `not_self` is the single clause standing between the system and a
self-grounded disposal.** -/
theorem witnessBad_not_answerable :
    ¬ witnessBad.Answerable wlic (fun _ => ()) (fun _ => ()) (fun _ => ())
        1 dis wGbad dis1 := fun h => h.not_self (by simp [wGbad])

end Witness

end Unified

end

end Workspace.Normativity.Contrib.NormativeContinuity

#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.routes_empty_persistent
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.live_empty_persistent
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.reach_succ_subset
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.exists_sink
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.persistent_wait
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.persistent_opportunity
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.no_structural_abandonment
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixA_reach_gate_fails
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixA_live_gate_holds
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixA_other_requirements
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixA_persistent_wait_fails
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixB_routes
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixE_cycle_is_work
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTraceCore.mattersOf_prior
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTraceCore.mattersOf_not_mem_of_lt
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTraceCore.mem_live_succ_of_parent
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.noPermanentWait_of_waitResponsive
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.waitResponsive_of_noPermanentWait
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.persistent_opportunity'
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.shareAttention_sum_le_one
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.shareAttention_nonStarving
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixE_other_requirements
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixE_reach_gate
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixE_issueTrace_nonvacuous
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.DefeatTrace.fresh
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.DefeatTrace.grounded_replay
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.DefeatTrace.grounded_replay_live
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.DefeatTrace.anchor_grounded
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.DefeatTrace.met_persistent'
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.DefeatTrace.dispose_not_met
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.DefeatTrace.routes_survive_dispose
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.DefeatTrace.no_grounding_in_batch
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.DefeatTrace.self_grounding_not_excluded_by_priority
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.DefeatTrace.no_self_grounding
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.DefeatTrace.live_nonempty_of_dispose_only
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.DefeatTrace.not_in_one_hand_of_contested
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.DefeatTrace.foreign_ground_dichotomy
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.DefeatTrace.no_laundering_walk
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.DefeatTrace.no_coalition_excluding_principal
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Witness.witness_answerable
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Witness.witness_disciplined
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Witness.witnessBad_grounded
#print axioms Workspace.Normativity.Contrib.NormativeContinuity.Witness.witnessBad_not_answerable
