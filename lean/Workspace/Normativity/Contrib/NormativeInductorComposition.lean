/-
# Composition lemmas for the Normative Inductor end-to-end theorem

Round `2026-09-05-ni-gap-audit`.  Each section mechanizes one arrow of the chain

    history -> O_P export -> compiler -> joint region -> affordable service
      -> traderized uptake -> practical response -> service transport -> Progress
      -> preservation of ordinary LI

at the level the landed components already type.  Nothing semantic is asserted: the
practical and uptake certificates enter the conditional theorems of
`NormativeInductionInterface` as named hypotheses, never as axioms.

Sections:

1. **History export.**  On an `IssueTrace`, resolution is unique and an exposure born
   before `n` is outstanding at `n` or was resolved exactly once strictly before `n`
   (`res_unique`, `out_or_res_of_born`).  On a `DefeatTrace` every exposure has a total
   status (`status_total`), a unique fate (`fate_unique`), and — the Defeat Principle
   made quantitative-free — a live or discharged descendant at every later prefix
   (`carry`).  `carry_needs_successor` shows `dispose_successor` is necessary for that.
2. **Compiler over rational rows.**  Rows `a·x ≤ b`, cited bundles, the decidable
   membership check, and a sound Farkas refutation certificate for `Conflict`.
3. **Compiled schedule → projection enforcer.**  A per-date compiled bundle with a
   vertex representation is a `RationalConstraintSchedule`; the registered theorem of
   record applies unchanged (`compiled_end_to_end`).
4. **Predictable-window cheapest-date scheduler.**  Liability ≤ `B`, zero residual,
   claim-to-service factor one.
5. **Practical response, semantic chains, uptake, Progress.**  The packaged `(R)`
   constants, the `n`-step affine transport fold, `χ ≤ Σρ/Σλ`, the Jensen step for the
   quadratic modulus, and the finite three-term Progress bound at its canonical
   endpoint — the transport-weighted edge response loss plus residual
   (`edge_progress_bound`, `edge_progress_bound_quadratic`).  The exposure-headline
   form (`progress_bound`, `progress_bound_quadratic`) is an optional stronger
   corollary for applications wanting one loss per exposure; it needs the headline
   to be dominated on every positive edge, and `edge_headline_separation` shows that
   premise is not free.

The conditional end-to-end theorems live in `NormativeInductionInterface`, typed
against the occurrence-indexed Integrity export.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.NormativeContinuity
import Workspace.Normativity.Contrib.EffectiveRepresentation
import Workspace.Normativity.Contrib.EnforcementPreservation
import Workspace.Normativity.Contrib.NormativeInductor
import Mathlib.Analysis.Real.Sqrt

noncomputable section

namespace Workspace.Normativity.Contrib.NormativeInductorComposition

open Classical Finset Relation
open scoped BigOperators
open Workspace.Normativity.Contrib.NormativeContinuity
open Workspace.Normativity.Contrib.NormativeContinuity.TraceData

/-! ## 1. History export -/

section History

variable {Q D : Type*} (T : IssueTrace Q D)

/-- A fresh issue is outstanding at the next prefix (Requirement 4 read forward). -/
lemma out_succ_of_born {n : ℕ} {q : Q} (hq : q ∈ T.Born n) : q ∈ T.O (n + 1) := by
  rw [T.resolution_continuity n]
  exact mem_union_right _ hq

/-- **Once resolved, never outstanding again.**  Re-entry into `O` is only by birth, and an
issue is born once. -/
theorem not_out_of_res {k : ℕ} {q : Q} (hres : q ∈ T.Res k) :
    ∀ m, k < m → q ∉ T.O m := by
  obtain ⟨j, hjk, hborn⟩ := T.out_born q k (T.res_subset k hres)
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    intro hout
    rw [T.resolution_continuity m] at hout
    rcases mem_union.1 hout with h | h
    · have hqm := (mem_sdiff.1 h).1
      have hnres := (mem_sdiff.1 h).2
      rcases Nat.lt_or_ge k m with hkm | hkm
      · exact ih hkm hqm
      · have : m = k := by omega
        subst this
        exact hnres hres
    · have := T.born_unique q j m hborn h
      omega

/-- **Resolution is unique.**  This discharges the `huniq` hypothesis that
`DefeatTrace.dispose_not_met` carries; it is a theorem of the issue-trace requirements. -/
theorem res_unique {k k' : ℕ} {q : Q} (h : q ∈ T.Res k) (h' : q ∈ T.Res k') : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact not_out_of_res T h k' hlt (T.res_subset k' h')
  · exact not_out_of_res T h' k hgt (T.res_subset k h)

/-- An outstanding issue was not resolved earlier. -/
theorem not_res_of_out {n k : ℕ} {q : Q} (hout : q ∈ T.O n) (hk : k < n) : q ∉ T.Res k :=
  fun h => not_out_of_res T h n hk hout

/-- **Exposure accounting.**  An issue born strictly before `n` is outstanding at `n` or
was resolved at some batch strictly between its birth and `n`. -/
theorem out_or_res_of_born {j n : ℕ} {q : Q} (hq : q ∈ T.Born j) (hjn : j < n) :
    q ∈ T.O n ∨ ∃ k, j < k ∧ k < n ∧ q ∈ T.Res k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge j n with hjn' | hjn'
    · rcases ih hjn' with hout | ⟨k, hjk, hkn, hres⟩
      · by_cases hres : q ∈ T.Res n
        · exact Or.inr ⟨n, hjn', Nat.lt_succ_self n, hres⟩
        · left
          rw [T.resolution_continuity n]
          exact mem_union_left _ (mem_sdiff.2 ⟨hout, hres⟩)
      · exact Or.inr ⟨k, hjk, by omega, hres⟩
    · have : j = n := by omega
      subst this
      exact Or.inl (out_succ_of_born T hq)

/-- **Historical exposure** at prefix `n`: every issue born strictly before `n`, by its
immutable identity, whether or not it is still outstanding. -/
def exposures (n : ℕ) : Finset Q := (range n).biUnion T.Born

@[simp] lemma mem_exposures {n : ℕ} {q : Q} :
    q ∈ exposures T n ↔ ∃ j < n, q ∈ T.Born j := by
  simp [exposures]

/-- The live docket is a subset of historical exposure. -/
theorem live_subset_exposures (n : ℕ) : T.O n ⊆ exposures T n := by
  intro q hq
  rw [mem_exposures]
  exact T.out_born q n hq

/-- Exposure is monotone: a cleared docket is not a cleared record. -/
theorem exposures_mono {n m : ℕ} (h : n ≤ m) : exposures T n ⊆ exposures T m := by
  intro q hq
  rw [mem_exposures] at hq ⊢
  obtain ⟨j, hj, hq⟩ := hq
  exact ⟨j, by omega, hq⟩

end History

section DefeatExport

variable {Q D S A : Type*} (T : DefeatTrace Q D S A)

/-- The certified status of an exposure at a prefix: still owed, paid, moved onto a named
successor, or extinguished by settlement.  The four constructors are the three resolution
kinds plus `live`; there is deliberately no fifth. -/
inductive Status (Q S : Type*) where
  | live : Status Q S
  | answered : Status Q S
  | disposed : Q → Status Q S
  | settled : S → Status Q S

/-- The fate of a status, forgetting the successor and the settlement fact. -/
inductive Fate where
  | live | answered | disposed | settled
  deriving DecidableEq

/-- Forget the payload. -/
def Status.fate {Q S : Type*} : Status Q S → Fate
  | .live => .live
  | .answered => .answered
  | .disposed _ => .disposed
  | .settled _ => .settled

/-- `HasStatus n q st`: the trace certifies status `st` for `q` at prefix `n`. -/
def HasStatus (n : ℕ) (q : Q) : Status Q S → Prop
  | .live => q ∈ T.O n
  | .answered => ∃ k < n, q ∈ T.Res k ∧ T.kind k q = Kind.answer
  | .disposed q' => ∃ k < n, ∃ G, q ∈ T.Res k ∧ T.kind k q = Kind.dispose G ∧
      q' ∈ T.Born k ∧ q ∈ T.par q'
  | .settled s => ∃ k < n, q ∈ T.Res k ∧ T.kind k q = Kind.settle s

/-- **Every exposure has a status.**  Uses `dispose_successor` to name the successor. -/
theorem status_total {j n : ℕ} {q : Q} (hq : q ∈ T.Born j) (hjn : j < n) :
    ∃ st, HasStatus T n q st := by
  rcases out_or_res_of_born T.toIssueTrace hq hjn with hout | ⟨k, _, hkn, hres⟩
  · exact ⟨.live, hout⟩
  · rcases hk : T.kind k q with _ | G | s
    · exact ⟨.answered, k, hkn, hres, hk⟩
    · obtain ⟨q', hq', hpar⟩ := T.dispose_successor k q G hres hk
      exact ⟨.disposed q', k, hkn, G, hres, hk, hq', hpar⟩
    · exact ⟨.settled s, k, hkn, hres, hk⟩

/-- **The fate is unique.**  Two certified statuses of one exposure at one prefix agree
after forgetting payloads; `res_unique` is what makes the resolved kinds agree. -/
theorem fate_unique {n : ℕ} {q : Q} {st st' : Status Q S}
    (h : HasStatus T n q st) (h' : HasStatus T n q st') : st.fate = st'.fate := by
  have key : ∀ {k k' : ℕ}, k < n → k' < n → q ∈ T.Res k → q ∈ T.Res k' →
      T.kind k q = T.kind k' q := by
    intro k k' _ _ hk hk'
    have := res_unique T.toIssueTrace hk hk'
    subst this
    rfl
  cases st with
  | live =>
    cases st' with
    | live => rfl
    | answered =>
      obtain ⟨k, hk, hres, _⟩ := h'
      exact absurd hres (not_res_of_out T.toIssueTrace h hk)
    | disposed q' =>
      obtain ⟨k, hk, _, hres, _⟩ := h'
      exact absurd hres (not_res_of_out T.toIssueTrace h hk)
    | settled s =>
      obtain ⟨k, hk, hres, _⟩ := h'
      exact absurd hres (not_res_of_out T.toIssueTrace h hk)
  | answered =>
    obtain ⟨k, hk, hres, hkind⟩ := h
    cases st' with
    | live => exact absurd hres (not_res_of_out T.toIssueTrace h' hk)
    | answered => rfl
    | disposed q' =>
      obtain ⟨k', hk', G, hres', hkind', _⟩ := h'
      have := key hk hk' hres hres'
      rw [hkind, hkind'] at this
      exact absurd this (by simp)
    | settled s =>
      obtain ⟨k', hk', hres', hkind'⟩ := h'
      have := key hk hk' hres hres'
      rw [hkind, hkind'] at this
      exact absurd this (by simp)
  | disposed q' =>
    obtain ⟨k, hk, G, hres, hkind, _⟩ := h
    cases st' with
    | live => exact absurd hres (not_res_of_out T.toIssueTrace h' hk)
    | answered =>
      obtain ⟨k', hk', hres', hkind'⟩ := h'
      have := key hk hk' hres hres'
      rw [hkind, hkind'] at this
      exact absurd this (by simp)
    | disposed q'' => rfl
    | settled s =>
      obtain ⟨k', hk', hres', hkind'⟩ := h'
      have := key hk hk' hres hres'
      rw [hkind, hkind'] at this
      exact absurd this (by simp)
  | settled s =>
    obtain ⟨k, hk, hres, hkind⟩ := h
    cases st' with
    | live => exact absurd hres (not_res_of_out T.toIssueTrace h' hk)
    | answered =>
      obtain ⟨k', hk', hres', hkind'⟩ := h'
      have := key hk hk' hres hres'
      rw [hkind, hkind'] at this
      exact absurd this (by simp)
    | disposed q'' =>
      obtain ⟨k', hk', G, hres', hkind', _⟩ := h'
      have := key hk hk' hres hres'
      rw [hkind, hkind'] at this
      exact absurd this (by simp)
    | settled s' => rfl

/-- `dispose_not_met` with its uniqueness hypothesis discharged by `res_unique`. -/
theorem dispose_not_met' {n k : ℕ} {d : D} {t : Q} {G : Finset (Ground Q S)}
    (ht : t ∈ T.roots d) (hres : t ∈ T.Res k) (hk : T.kind k t = Kind.dispose G)
    (hn : T.Met n d) : False :=
  T.dispose_not_met ht hk (fun j hj => res_unique T.toIssueTrace hj hres) hn

/-- `CarriedTo T kind n q`: some descendant of `q` is outstanding at `n`, or was
resolved before `n` by a discharging kind.  Stated over an `IssueTrace` and an arbitrary
kind assignment so that the necessity of `dispose_successor` can be exhibited. -/
def CarriedTo (T : IssueTrace Q D) (kind : ℕ → Q → Kind Q S) (n : ℕ) (q : Q) : Prop :=
  ∃ r, T.anc q r ∧ (r ∈ T.O n ∨ ∃ k < n, r ∈ T.Res k ∧ (kind k r).Discharges)

/-- **Carry.**  Under the Defeat Principle no exposure vanishes: at every later prefix
some descendant of it is still owed or was discharged by answer or settlement.  This is
the structural half of the answerability-conservation invariant on the unified trace;
the semantic half (that the descendant carries the *same* load) is not stated here. -/
theorem carry {j n : ℕ} {q : Q} (hq : q ∈ T.Born j) (hjn : j < n) :
    CarriedTo T.toIssueTrace T.kind n q := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge j n with hjn' | hjn'
    · obtain ⟨r, hanc, hr⟩ := ih hjn'
      rcases hr with hout | ⟨k, hk, hres, hdis⟩
      · by_cases hres : r ∈ T.Res n
        · rcases hk : T.kind n r with _ | G | s
          · exact ⟨r, hanc, Or.inr ⟨n, Nat.lt_succ_self n, hres, by rw [hk]; trivial⟩⟩
          · obtain ⟨r', hr'born, hpar⟩ := T.dispose_successor n r G hres hk
            exact ⟨r', ReflTransGen.tail hanc hpar,
              Or.inl (out_succ_of_born T.toIssueTrace hr'born)⟩
          · exact ⟨r, hanc, Or.inr ⟨n, Nat.lt_succ_self n, hres, by rw [hk]; trivial⟩⟩
        · refine ⟨r, hanc, Or.inl ?_⟩
          rw [T.resolution_continuity n]
          exact mem_union_left _ (mem_sdiff.2 ⟨hout, hres⟩)
      · exact ⟨r, hanc, Or.inr ⟨k, by omega, hres, hdis⟩⟩
    · have : j = n := by omega
      subst this
      exact ⟨q, ReflTransGen.refl, Or.inl (out_succ_of_born T.toIssueTrace hq)⟩

/-- **The qualitative obligation export** `O_P = (E, Live, Spec, Status)`.  No weights.
The anchored specification is a function of the immutable identity, supplied by the
anchored-slices layer; the trace does not carry it and this structure does not invent it. -/
structure ObligationExport (Q S Spec : Type*) where
  exposures : Finset Q
  live : Finset Q
  spec : Q → Spec
  status : Q → Status Q S → Prop

variable [DecidableEq Q]

/-- The export adapter from a defeat trace at prefix `n`. -/
def exportObligations (spec : Q → Spec) (n : ℕ) : ObligationExport Q S Spec where
  exposures := exposures T.toIssueTrace n
  live := T.O n
  spec := spec
  status := HasStatus T n

/-- **The export theorem.**  Live ⊆ exposures; every exposure has a status; the fate is
unique; every exposure is carried. -/
theorem export_sound (spec : Q → Spec) (n : ℕ) :
    (exportObligations T spec n).live ⊆ (exportObligations T spec n).exposures ∧
    (∀ q ∈ (exportObligations T spec n).exposures,
      ∃ st, (exportObligations T spec n).status q st) ∧
    (∀ q st st', (exportObligations T spec n).status q st →
      (exportObligations T spec n).status q st' →
      st.fate = st'.fate) ∧
    (∀ q ∈ (exportObligations T spec n).exposures,
      CarriedTo T.toIssueTrace T.kind n q) := by
  refine ⟨live_subset_exposures T.toIssueTrace n, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨j, hj, hq⟩ := (mem_exposures T.toIssueTrace).1 hq
    exact status_total T hq hj
  · intro q st st' h h'
    exact fate_unique T h h'
  · intro q hq
    obtain ⟨j, hj, hq⟩ := (mem_exposures T.toIssueTrace).1 hq
    exact carry T hq hj

end DefeatExport

/-! ### Necessity of `dispose_successor` for carry

On the 2026-09-03 witness trace, reassign the kind of `ans` at batch 1 to a disposal.
`ans` has no successor, so nothing descends from it, it is not outstanding at 2, and its
only resolution does not discharge.  `carry` fails; the field is load-bearing. -/

section CarryNecessity

open Workspace.Normativity.Contrib.NormativeContinuity.Witness

/-- A kind assignment that disposes `ans` with no successor opened. -/
def wkindNoSucc : ℕ → WQ → Kind WQ WS
  | 1, WQ.ans => Kind.dispose ∅
  | _, _ => Kind.answer

lemma witnessIssue_anc_ans {r : WQ} (h : witnessIssue.anc WQ.ans r) : r = WQ.ans := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    have : WQ.ans ∈ wpar _ := hstep
    revert this
    rename_i c _
    cases c <;> simp [wpar]

theorem carry_needs_successor : ¬ CarriedTo witnessIssue wkindNoSucc 2 WQ.ans := by
  rintro ⟨r, hanc, hr⟩
  have hr' := witnessIssue_anc_ans hanc
  subst hr'
  rcases hr with hout | ⟨k, hk, hres, hdis⟩
  · have : WQ.ans ∈ wO 2 := hout
    simp [bornAt, resAt, Resolves] at this
  · have hres' : resAt WQ.ans = k ∧ Resolves WQ.ans := by
      simpa [witnessIssue, Fixtures.toIssueTrace, wdata] using hres
    have hk1 : k = 1 := by
      have := hres'.1
      simp [resAt] at this
      omega
    subst hk1
    simp [wkindNoSucc, Kind.Discharges] at hdis

/-- The carry theorem is inhabited: on the honest witness, `dis` (born at `0`) is carried
to prefix `2`. -/
theorem carry_witness : CarriedTo witnessIssue witness.kind 2 WQ.dis :=
  carry witness (j := 0) (by simp [bornAt]) (by norm_num)

end CarryNecessity

/-! ## 2. The compiler over rational rows -/

section Compiler

variable {Q : Type*} {d : ℕ}

/-- An affine row `∑ i, a i * x i ≤ b` over `d` rational coordinates. -/
structure Row (d : ℕ) where
  a : Fin d → ℚ
  b : ℚ

/-- Satisfaction of a row at a rational point. -/
def Row.Sat (r : Row d) (x : Fin d → ℚ) : Prop := ∑ i, r.a i * x i ≤ r.b

/-- Satisfaction of a row at a real point. -/
def Row.SatR (r : Row d) (x : Fin d → ℝ) : Prop := ∑ i, (r.a i : ℝ) * x i ≤ (r.b : ℝ)

instance (r : Row d) (x : Fin d → ℚ) : Decidable (r.Sat x) := by
  unfold Row.Sat; infer_instance

/-- The unit cube. -/
def InCube (x : Fin d → ℚ) : Prop := ∀ i, 0 ≤ x i ∧ x i ≤ 1

instance (x : Fin d → ℚ) : Decidable (InCube x) := by
  unfold InCube; infer_instance

/-- The cube's upper row `x i ≤ 1`. -/
def cubeUpper (i : Fin d) : Row d := ⟨fun j => if j = i then 1 else 0, 1⟩

/-- The cube's lower row `-x i ≤ 0`. -/
def cubeLower (i : Fin d) : Row d := ⟨fun j => if j = i then -1 else 0, 0⟩

lemma cubeUpper_sat {x : Fin d → ℚ} (hx : InCube x) (i : Fin d) : (cubeUpper i).Sat x := by
  unfold Row.Sat cubeUpper
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact (hx i).2

lemma cubeLower_sat {x : Fin d → ℚ} (hx : InCube x) (i : Fin d) : (cubeLower i).Sat x := by
  unfold Row.Sat cubeLower
  simp only [ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  linarith [(hx i).1]

/-- A row citing the live obligation it realizes. -/
structure CitedRow (Q : Type*) (d : ℕ) where
  cites : Q
  row : Row d

/-- A compiler input bundle: cited rows for one service occurrence. -/
abbrev Bundle (Q : Type*) (d : ℕ) := List (CitedRow Q d)

/-- The obligations a bundle cites. -/
def Bundle.cited (B : Bundle Q d) : List Q := B.map CitedRow.cites

/-- The joint region `K = cube ∩ rows`, at rational points. -/
def Bundle.Region (B : Bundle Q d) (x : Fin d → ℚ) : Prop :=
  InCube x ∧ ∀ c ∈ B, c.row.Sat x

/-- The joint region at real points, for the bridge to the projection stack. -/
def Bundle.RegionR (B : Bundle Q d) (x : Fin d → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∀ c ∈ B, c.row.SatR x

instance (B : Bundle Q d) (x : Fin d → ℚ) : Decidable (B.Region x) := by
  unfold Bundle.Region; infer_instance

/-- **The exact membership check** a `Compiled` certificate is verified by. -/
def checkCompiled (B : Bundle Q d) (w : Fin d → ℚ) : Bool := decide (B.Region w)

theorem checkCompiled_iff (B : Bundle Q d) (w : Fin d → ℚ) :
    checkCompiled B w = true ↔ B.Region w := decide_eq_true_iff

/-- A checked witness makes the joint region nonempty: **joint feasibility**. -/
theorem region_nonempty_of_check {B : Bundle Q d} {w : Fin d → ℚ}
    (h : checkCompiled B w = true) : ∃ x, B.Region x :=
  ⟨w, (checkCompiled_iff B w).1 h⟩

/-- A bundle is **well formed** at prefix `n` when every cited obligation is live. -/
def Bundle.WellFormed {D : Type*} (T : IssueTrace Q D) (n : ℕ) (B : Bundle Q d) : Prop :=
  ∀ c ∈ B, c.cites ∈ T.O n

/-- **A Farkas refutation certificate**: finitely many nonnegative multipliers on rows
whose weighted coefficient sum vanishes while the weighted constant sum is negative. -/
structure FarkasCert (d : ℕ) (m : ℕ) where
  mult : Fin m → ℚ
  row : Fin m → Row d
  mult_nonneg : ∀ i, 0 ≤ mult i
  coeff_sum : ∀ j, ∑ i, mult i * (row i).a j = 0
  const_sum : ∑ i, mult i * (row i).b < 0

/-- **Soundness of the refutation certificate.**  No point satisfies every row the
certificate weights. -/
theorem farkas_sound {m : ℕ} (c : FarkasCert d m) (x : Fin d → ℚ)
    (hx : ∀ i, (c.row i).Sat x) : False := by
  have h1 : ∑ i, c.mult i * ∑ j, (c.row i).a j * x j ≤ ∑ i, c.mult i * (c.row i).b := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hx i) (c.mult_nonneg i)
  have h2 : ∑ i, c.mult i * ∑ j, (c.row i).a j * x j = 0 := by
    calc ∑ i, c.mult i * ∑ j, (c.row i).a j * x j
        = ∑ i, ∑ j, c.mult i * (c.row i).a j * x j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = ∑ j, ∑ i, c.mult i * (c.row i).a j * x j := Finset.sum_comm
      _ = ∑ j, (∑ i, c.mult i * (c.row i).a j) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
      _ = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          rw [c.coeff_sum j, zero_mul]
  have := c.const_sum
  linarith

/-- The rows a certificate may weight against a bundle: the bundle's own rows and the
cube rows. -/
def Bundle.Allowed (B : Bundle Q d) (r : Row d) : Prop :=
  (∃ c ∈ B, c.row = r) ∨ (∃ i, r = cubeUpper i) ∨ (∃ i, r = cubeLower i)

/-- **Accountable conflict is sound.**  A Farkas certificate over allowed rows refutes
joint feasibility of the bundle. -/
theorem conflict_sound {m : ℕ} (B : Bundle Q d) (c : FarkasCert d m)
    (hallowed : ∀ i, B.Allowed (c.row i)) : ¬ ∃ x, B.Region x := by
  rintro ⟨x, hcube, hrows⟩
  refine farkas_sound c x ?_
  intro i
  rcases hallowed i with ⟨cr, hcr, hrow⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [← hrow]; exact hrows cr hcr
  · rw [hj]; exact cubeUpper_sat hcube j
  · rw [hj]; exact cubeLower_sat hcube j

/-- The compiler's three outputs.  `conflict` carries its refutation; `unknown` carries
nothing.  Neither has a field that could name, drop, or reweight an obligation. -/
inductive CompileResult (Q : Type*) (d : ℕ) where
  | compiled (w : Fin d → ℚ)
  | conflict (m : ℕ) (cert : FarkasCert d m)
  | unknown

/-- A result is **valid** for a bundle when its certificate checks. -/
def CompileResult.Valid (B : Bundle Q d) : CompileResult Q d → Prop
  | .compiled w => checkCompiled B w = true
  | .conflict _ cert => ∀ i, B.Allowed (cert.row i)
  | .unknown => True

/-- **Compiler soundness for the declared row schema.**  A valid `compiled` result
exhibits joint feasibility; a valid `conflict` result refutes it. -/
theorem compile_sound (B : Bundle Q d) :
    ∀ res : CompileResult Q d, res.Valid B →
      (∀ w, res = .compiled w → ∃ x, B.Region x) ∧
      (∀ m cert, res = .conflict m cert → ¬ ∃ x, B.Region x) := by
  intro res hv
  refine ⟨?_, ?_⟩
  · rintro w rfl
    exact region_nonempty_of_check hv
  · rintro m cert rfl
    exact conflict_sound B cert hv

/-- **Failure conservation.**  Whatever the compiler returns, every obligation a
well-formed bundle cites is carried at every later prefix.  The result type has no
write authority over the trace; this is the theorem `carry` restricted to cited
obligations. -/
theorem failure_conserves {D S A : Type*} (T : DefeatTrace Q D S A) {n : ℕ}
    (B : Bundle Q d) (hwf : B.WellFormed T.toIssueTrace n) (_res : CompileResult Q d) :
    ∀ c ∈ B, ∀ m, n ≤ m → CarriedTo T.toIssueTrace T.kind m c.cites := by
  intro c hc m hm
  obtain ⟨j, hj, hborn⟩ := T.out_born _ n (hwf c hc)
  exact carry T hborn (by omega)

end Compiler

/-! ## 3. A compiled schedule is a constraint schedule

The projection stack takes a vertex representation.  A compiled day therefore carries,
besides its rows and feasibility witness, a `RationalPolytope` whose carrier is exactly the
real joint region.  That field is **convex representability in the schema the enforcer
consumes** — the rows-to-vertices conversion is not proved in the repository and is the
exact missing statement recorded in `GAP_AUDIT.md`. -/

section CompiledSchedule

open Workspace.Normativity.Contrib.RationalPolytope
open Workspace.Normativity.Contrib.ConstraintSchedule
open Workspace.Normativity.Contrib.ProjectionCompiler
open Workspace.Normativity.Contrib.ProjectionBridge
open Workspace.Normativity.Contrib.EffectiveRepresentation
open LogicalInduction

variable {Q : Type*}

/-- One service occurrence's compiled output, with its representation. -/
structure CompiledDay (Q : Type*) where
  coords : List Sentence
  nodup : coords.Nodup
  tol : ℚ
  tol_pos : 0 < tol
  bundle : Bundle Q coords.length
  witness : Fin coords.length → ℚ
  witness_ok : checkCompiled bundle witness = true
  vertices : RationalPolytope coords.length
  vertices_in_cube : ∀ v ∈ vertices.verts, ∀ i, 0 ≤ v i ∧ v i ≤ 1
  /-- Convex representability: the vertex hull is the real joint region. -/
  represents : ∀ p : Pt coords.length, p ∈ vertices.carrier ↔ bundle.RegionR (fun i => p i)

/-- A compiled schedule: one compiled day per date. -/
abbrev CompiledSchedule (Q : Type*) := ℕ → CompiledDay Q

/-- The constraint schedule a compiled schedule presents to the enforcer. -/
def CompiledSchedule.toSchedule (CS : CompiledSchedule Q) : RationalConstraintSchedule where
  coords n := (CS n).coords
  nodup n := (CS n).nodup
  tol n := (CS n).tol
  tol_pos n := (CS n).tol_pos
  region n := (CS n).vertices
  region_in_cube n := (CS n).vertices_in_cube

/-- Every compiled day's region is nonempty, by its checked witness. -/
theorem CompiledSchedule.region_nonempty (CS : CompiledSchedule Q) (n : ℕ) :
    ∃ x, (CS n).bundle.Region x :=
  region_nonempty_of_check (CS n).witness_ok

/-- **Admissibility in row terms.**  If every plausible world's payout, restricted to the
day's fragment, lies in the cube and satisfies every compiled row, the schedule admits it. -/
theorem CompiledSchedule.regionPred_of_rows (CS : CompiledSchedule Q) (n : ℕ)
    (y : Sentence → ℝ)
    (h : (CS n).bundle.RegionR (fun i => restrict (CS.toSchedule.fragment n) y i)) :
    CS.toSchedule.regionPred n y := by
  unfold RationalConstraintSchedule.regionPred ConstraintSchedule.regionPred
  exact ((CS n).represents _).2 h

/-- **Compiled schedule → theorem of record.**  The registered
`end_to_end_of_constraints_effective` applies to a compiled schedule unchanged: the
augmented market is a logical inductor, conforms within tolerance, and the target lies in
the day's region.  Hypotheses: computability of the schedule's data, computability of the
deductive process, and admissibility of every compiled row by every plausible world. -/
theorem compiled_end_to_end (CS : CompiledSchedule Q) (hC : CS.toSchedule.Computation)
    {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
    (hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      (CS n).bundle.RegionR (fun i => restrict (CS.toSchedule.fragment n) v.payout i)) :
    IsLogicalInductor (CS.toSchedule.market (effectiveRepresentation CS.toSchedule) DP) DP ∧
      (∀ n, ProjectionForce.dist2 (CS.toSchedule.fragment n).toFinset
          (CS.toSchedule.market (effectiveRepresentation CS.toSchedule) DP n)
          (CS.toSchedule.target (effectiveRepresentation CS.toSchedule) DP n)
            ≤ (((CS n).tol : ℚ) : ℝ)) ∧
      ∀ n, CS.toSchedule.regionPred n
          (CS.toSchedule.target (effectiveRepresentation CS.toSchedule) DP n) ∧
        ∀ φ ∈ (CS.toSchedule.fragment n).toFinset,
          |CS.toSchedule.market (effectiveRepresentation CS.toSchedule) DP n φ
            - CS.toSchedule.target (effectiveRepresentation CS.toSchedule) DP n φ|
            ≤ (((CS n).tol : ℚ) : ℝ) :=
  end_to_end_of_constraints_effective CS.toSchedule hC process
    (fun n v hv => CS.regionPred_of_rows n v.payout (hadm n v hv))

end CompiledSchedule

/-! ## 4. The predictable-window cheapest-date scheduler -/

section Scheduler

/-- A **predictable-window linear workload** over `N` arrival dates: claim mass `c t ≥ 0`
arriving at `t`, per-unit liability weight `w s ≥ 0` at each service date `s`, and for each
arrival a finite nonempty window of admissible service dates whose weights are all known at
arrival. -/
structure Workload (N : ℕ) where
  c : Fin N → ℚ
  c_nonneg : ∀ t, 0 ≤ c t
  w : ℕ → ℚ
  w_nonneg : ∀ s, 0 ≤ w s
  window : Fin N → Finset ℕ
  window_nonempty : ∀ t, (window t).Nonempty

namespace Workload

variable {N : ℕ} (W : Workload N)

/-- The cheapest weight in a claim's window. -/
def minWeight (t : Fin N) : ℚ := (W.window t).inf' (W.window_nonempty t) W.w

/-- The cheapest date in a claim's window, with the finset's own tie-break. -/
noncomputable def cheapest (t : Fin N) : ℕ :=
  ((W.window t).exists_mem_eq_inf' (W.window_nonempty t) W.w).choose

lemma cheapest_mem (t : Fin N) : W.cheapest t ∈ W.window t :=
  ((W.window t).exists_mem_eq_inf' (W.window_nonempty t) W.w).choose_spec.1

lemma w_cheapest (t : Fin N) : W.w (W.cheapest t) = W.minWeight t :=
  ((W.window t).exists_mem_eq_inf' (W.window_nonempty t) W.w).choose_spec.2.symm

/-- The **declared budget condition**: `∑ t, c t · min_{s ∈ window t} w s ≤ B`. -/
def Affordable (B : ℚ) : Prop := ∑ t, W.c t * W.minWeight t ≤ B

/-- The cheapest-date plan: all of claim `t`'s mass is served at `cheapest t`. -/
noncomputable def plan (t : Fin N) (s : ℕ) : ℚ := if s = W.cheapest t then W.c t else 0

/-- Total claim mass. -/
def totalClaim : ℚ := ∑ t, W.c t

/-- **Liability.**  The scheduled plan's total liability is at most the budget. -/
theorem liability_le {B : ℚ} (h : W.Affordable B) :
    ∑ t, W.c t * W.w (W.cheapest t) ≤ B := by
  have : ∑ t, W.c t * W.w (W.cheapest t) = ∑ t, W.c t * W.minWeight t := by
    apply Finset.sum_congr rfl
    intro t _
    rw [W.w_cheapest t]
  rw [this]
  exact h

/-- **Adaptedness.**  The chosen date lies in the window known at arrival. -/
theorem adapted (t : Fin N) : W.cheapest t ∈ W.window t := W.cheapest_mem t

/-- **Full transport.**  Each claim's mass is transported in full; the residual is zero. -/
theorem plan_row (t : Fin N) (S : Finset ℕ) (hS : W.cheapest t ∈ S) :
    ∑ s ∈ S, W.plan t s = W.c t := by
  unfold plan
  rw [Finset.sum_ite_eq' S (W.cheapest t) (fun _ => W.c t)]
  simp [hS]

theorem residual_zero (S : Finset ℕ) (hS : ∀ t, W.cheapest t ∈ S) :
    W.totalClaim - ∑ t, ∑ s ∈ S, W.plan t s = 0 := by
  unfold totalClaim
  have : ∑ t, ∑ s ∈ S, W.plan t s = ∑ t, W.c t :=
    Finset.sum_congr rfl fun t _ => W.plan_row t S (hS t)
  rw [this, sub_self]

/-- **Claim-to-service factor one.**  Service capacity spent equals claim mass served,
date by date, so the parsimony constant of the old transport theorem is `K = 1`. -/
theorem column_eq_service (s : ℕ) :
    ∑ t, W.plan t s = ∑ t, if s = W.cheapest t then W.c t else 0 := rfl

theorem total_service_eq_total_claim (S : Finset ℕ) (hS : ∀ t, W.cheapest t ∈ S) :
    ∑ s ∈ S, ∑ t, W.plan t s = W.totalClaim := by
  rw [Finset.sum_comm]
  unfold totalClaim
  exact Finset.sum_congr rfl fun t _ => W.plan_row t S (hS t)

end Workload

/-- A nonvacuous workload: two claims, windows `{0,1}` and `{1,2}`, weights `w s = s + 1`. -/
def sampleWorkload : Workload 2 where
  c := ![1, 2]
  c_nonneg := by intro t; fin_cases t <;> norm_num
  w s := (s : ℚ) + 1
  w_nonneg := by intro s; positivity
  window := ![{0, 1}, {1, 2}]
  window_nonempty := by intro t; fin_cases t <;> simp

theorem sampleWorkload_affordable : sampleWorkload.Affordable 5 := by
  unfold Workload.Affordable Workload.minWeight
  simp [sampleWorkload, Fin.sum_univ_two]
  norm_num

end Scheduler

/-! ## 5. Practical response, semantic chains, uptake, Progress -/

section Response

open Workspace.Normativity.Contrib.NormativeInductor

/-- **Anchored response transport `(R)`, packaged.**  From calibration to an admissible
value (`d`), bounded ambiguity to the authenticated value (`ζ`), an `η`-optimal response
distribution on a finite alphabet, and the response-adequacy certificate `(NI-S)` with
constant `L`, the anchored loss obeys `loss ≤ 2L·d + (L(2ζ+η) + ε_resp)`. -/
theorem anchored_response_transport {Q : Type*} [DecidableEq Q]
    (actions : Finset Q) {p b admissible trueValue : Q → ℝ} {qStar : Q}
    {d ζ η L εresp loss : ℝ}
    (hqStar : qStar ∈ actions)
    (hp : ∀ q ∈ actions, 0 ≤ p q)
    (hprob : ∑ q ∈ actions, p q = 1)
    (hadmissible : ∀ q, |admissible q - b q| ≤ d)
    (hsemantic : ∀ q, |trueValue q - admissible q| ≤ ζ)
    (hchoice : b qStar ≤ (∑ q ∈ actions, p q * b q) + η)
    (hL : 0 ≤ L)
    (hresp : loss ≤ L * (trueValue qStar - ∑ q ∈ actions, p q * trueValue q) + εresp) :
    loss ≤ (2 * L) * d + (L * (2 * ζ + η) + εresp) := by
  have hcal := calibration_through_value_correspondence hadmissible hsemantic
  have hregret := randomized_approximate_argmax_transfer actions hqStar hp hprob
    (fun q _ => hcal q) hchoice
  have := practical_response_compose
    (decisionDefect := trueValue qStar - ∑ q ∈ actions, p q * trueValue q)
    (operativeDefect := d + ζ) (loss := loss) (C := 2) (η := η) (L := L) (ε := εresp) hL
    (by linarith) hresp
  ring_nf at this ⊢
  exact this

/-- An affine transport step `(L, ε)`. -/
abbrev Step := ℝ × ℝ

/-- Fold a chain of steps into one certificate.  `steps = [s₁, …, sₙ]` is applied in
list order: `s₁` first. -/
def chainCert : List Step → Step
  | [] => (1, 0)
  | s :: rest =>
      let c := chainCert rest
      (c.1 * s.1, c.2 + c.1 * s.2)

/-- A chain of quantities `y 0, y 1, …, y n` linked by the steps. -/
def Linked : List Step → (ℕ → ℝ) → ℕ → Prop
  | [], _, _ => True
  | s :: rest, y, i => y (i + 1) ≤ s.1 * y i + s.2 ∧ Linked rest y (i + 1)

lemma chainCert_fst_nonneg : ∀ (steps : List Step),
    (∀ s ∈ steps, 0 ≤ s.1) → 0 ≤ (chainCert steps).1 := by
  intro steps
  induction steps with
  | nil => simp [chainCert]
  | cons s rest ih =>
    intro h
    simp only [chainCert]
    exact mul_nonneg (ih fun t ht => h t (List.mem_cons_of_mem s ht))
      (h s (List.mem_cons_self ..))

/-- **The `n`-step semantic transport fold.**  Nonnegative multipliers along the chain
give `y n ≤ L* · y 0 + ε*` with `(L*, ε*) = chainCert steps`. -/
theorem chain_transport : ∀ (steps : List Step) (y : ℕ → ℝ) (i : ℕ),
    (∀ s ∈ steps, 0 ≤ s.1) → Linked steps y i →
    y (i + steps.length) ≤ (chainCert steps).1 * y i + (chainCert steps).2 := by
  intro steps
  induction steps with
  | nil =>
    intro y i _ _
    simp [chainCert]
  | cons s rest ih =>
    intro y i hnn hlinked
    obtain ⟨hstep, hrest⟩ := hlinked
    have hL : ∀ t ∈ rest, 0 ≤ t.1 := fun t ht => hnn t (List.mem_cons_of_mem s ht)
    have hs : 0 ≤ s.1 := hnn s (List.mem_cons_self ..)
    have htail := ih y (i + 1) hL hrest
    have hcert : 0 ≤ (chainCert rest).1 := chainCert_fst_nonneg rest hL
    have hcomp := affine_transport_compose (L₁ := (chainCert rest).1) (L₂ := s.1)
      (ε₁ := (chainCert rest).2) (ε₂ := s.2) hcert hstep htail
    have hlen : i + (s :: rest).length = (i + 1) + rest.length := by
      simp [List.length_cons]; omega
    rw [hlen]
    simpa [chainCert] using hcomp

/-- A chain of exact-carry steps folds to the identity certificate. -/
theorem chainCert_exact_carry : ∀ n, chainCert (List.replicate n ((1 : ℝ), (0 : ℝ))) = (1, 0)
  | 0 => rfl
  | n + 1 => by
      simp only [List.replicate_succ, chainCert, chainCert_exact_carry n]
      norm_num

end Response

section Uptake

/-- **The work-ratio bound.**  Per-date work bounds `λ_s d_s² ≤ ρ_s` give
`χ = Σ λ d² / Σ λ ≤ Σ ρ / Σ λ`. -/
theorem work_ratio_le {ι : Type*} (S : Finset ι) (lam d ρ : ι → ℝ)
    (hwork : ∀ s ∈ S, lam s * d s ^ 2 ≤ ρ s) (hpos : 0 < ∑ s ∈ S, lam s) :
    (∑ s ∈ S, lam s * d s ^ 2) / (∑ s ∈ S, lam s) ≤ (∑ s ∈ S, ρ s) / (∑ s ∈ S, lam s) :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum hwork) hpos.le

/-- The per-date work bound from the calibrated schedule: `λ = ρ/δ²` and a defect at most
`δ` give `λ d² ≤ ρ`.  Composes with `public_work_le_projection_work` for the sup defect. -/
theorem work_of_calibrated {d δ ρ : ℝ} (hd0 : 0 ≤ d) (hδ : 0 < δ) (hρ : 0 ≤ ρ) (hd : d ≤ δ) :
    (ρ / δ ^ 2) * d ^ 2 ≤ ρ := by
  have hsq : d ^ 2 ≤ δ ^ 2 := by nlinarith
  calc (ρ / δ ^ 2) * d ^ 2 ≤ (ρ / δ ^ 2) * δ ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (div_nonneg hρ (by positivity))
    _ = ρ := by field_simp

/-- **Jensen for the quadratic modulus.**  For a probability vector `ν` and nonnegative
`d`, `Σ ν d ≤ √(Σ ν d²)`; so `Ψ_φ(χ) = √χ` is admissible when `φ(x) = x²`. -/
theorem mean_le_sqrt_mean_sq {ι : Type*} (S : Finset ι) (ν d : ι → ℝ)
    (hν : ∀ s ∈ S, 0 ≤ ν s) (hprob : ∑ s ∈ S, ν s = 1) (hd : ∀ s ∈ S, 0 ≤ d s) :
    ∑ s ∈ S, ν s * d s ≤ Real.sqrt (∑ s ∈ S, ν s * d s ^ 2) := by
  set m := ∑ s ∈ S, ν s * d s with hm
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun s hs => mul_nonneg (hν s hs) (hd s hs)
  have hvar : 0 ≤ ∑ s ∈ S, ν s * (d s - m) ^ 2 :=
    Finset.sum_nonneg fun s hs => mul_nonneg (hν s hs) (sq_nonneg _)
  have hexpand : ∑ s ∈ S, ν s * (d s - m) ^ 2 = (∑ s ∈ S, ν s * d s ^ 2) - m ^ 2 := by
    have h1 : ∑ s ∈ S, ν s * (d s - m) ^ 2 =
        ∑ s ∈ S, (ν s * d s ^ 2 - 2 * m * (ν s * d s) + m ^ 2 * ν s) := by
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hprob, ← hm]
    ring
  apply Real.le_sqrt_of_sq_le
  linarith

end Uptake

section Progress

variable {E S : Type*}

/-- **Finite edge-response Progress.** `Λ e s` is the anchored loss of exposure `e`
against the one response actually realized at service `s`. The matched statistic
weights these edges, allowing several services to contribute to one exposure.
Nonnegative transport and defect, edge-local practical certificates, and the
weighted column bound imply the three-term estimate. Evaluation normalization and
row caps give the residual its interpretation; they are not needed for this algebra. -/
theorem edge_progress_bound (Es : Finset E) (Ss : Finset S)
    (T Λ M ε : E → S → ℝ) (d ν : S → ℝ) (Γ D : ℝ)
    (hT : ∀ e ∈ Es, ∀ s ∈ Ss, 0 ≤ T e s)
    (hd : ∀ s ∈ Ss, 0 ≤ d s)
    (hedge : ∀ e ∈ Es, ∀ s ∈ Ss, 0 < T e s → Λ e s ≤ M e s * d s + ε e s)
    (hΓ : ∀ s ∈ Ss, ∑ e ∈ Es, T e s * M e s ≤ Γ * ν s) :
    (∑ e ∈ Es, ∑ s ∈ Ss, T e s * Λ e s) +
        D * (1 - ∑ e ∈ Es, ∑ s ∈ Ss, T e s) ≤
      Γ * (∑ s ∈ Ss, ν s * d s) + (∑ e ∈ Es, ∑ s ∈ Ss, T e s * ε e s) +
        D * (1 - ∑ e ∈ Es, ∑ s ∈ Ss, T e s) := by
  have hedge' : ∀ e ∈ Es, ∀ s ∈ Ss,
      T e s * Λ e s ≤ T e s * (M e s * d s + ε e s) := by
    intro e he s hs
    rcases (hT e he s hs).lt_or_eq with hpos | hzero
    · exact mul_le_mul_of_nonneg_left (hedge e he s hs hpos) hpos.le
    · rw [← hzero]; simp
  have hmatched : (∑ e ∈ Es, ∑ s ∈ Ss, T e s * Λ e s) ≤
      (∑ s ∈ Ss, (∑ e ∈ Es, T e s * M e s) * d s) +
        ∑ e ∈ Es, ∑ s ∈ Ss, T e s * ε e s := by
    calc
      _ ≤ ∑ e ∈ Es, ∑ s ∈ Ss, T e s * (M e s * d s + ε e s) :=
        Finset.sum_le_sum fun e he => Finset.sum_le_sum fun s hs => hedge' e he s hs
      _ = (∑ e ∈ Es, ∑ s ∈ Ss, (T e s * M e s) * d s) +
          ∑ e ∈ Es, ∑ s ∈ Ss, T e s * ε e s := by
        simp only [mul_add, Finset.sum_add_distrib, mul_assoc]
      _ = _ := by rw [Finset.sum_comm (s := Es) (t := Ss)]; simp only [Finset.sum_mul]
  have hamp : (∑ s ∈ Ss, (∑ e ∈ Es, T e s * M e s) * d s) ≤
      Γ * ∑ s ∈ Ss, ν s * d s := by
    calc
      _ ≤ ∑ s ∈ Ss, (Γ * ν s) * d s :=
        Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_right (hΓ s hs) (hd s hs)
      _ = _ := by simp only [Finset.mul_sum, mul_assoc]
  linarith

/-- **Quadratic finite edge-response Progress.** Intensity-normalized service weights
and the uptake certificate `λ_s d_s² ≤ ρ_s` supply the square-root modulus. -/
theorem edge_progress_bound_quadratic (Es : Finset E) (Ss : Finset S)
    (T Λ M ε : E → S → ℝ) (d lam ρ : S → ℝ) (Γ D : ℝ)
    (hT : ∀ e ∈ Es, ∀ s ∈ Ss, 0 ≤ T e s)
    (hd : ∀ s ∈ Ss, 0 ≤ d s)
    (hedge : ∀ e ∈ Es, ∀ s ∈ Ss, 0 < T e s → Λ e s ≤ M e s * d s + ε e s)
    (hlam : ∀ s ∈ Ss, 0 ≤ lam s) (hlampos : 0 < ∑ s ∈ Ss, lam s)
    (hwork : ∀ s ∈ Ss, lam s * d s ^ 2 ≤ ρ s)
    (hΓ0 : 0 ≤ Γ)
    (hΓ : ∀ s ∈ Ss, ∑ e ∈ Es, T e s * M e s ≤ Γ * (lam s / ∑ s' ∈ Ss, lam s')) :
    (∑ e ∈ Es, ∑ s ∈ Ss, T e s * Λ e s) +
        D * (1 - ∑ e ∈ Es, ∑ s ∈ Ss, T e s) ≤
      Γ * Real.sqrt ((∑ s ∈ Ss, ρ s) / (∑ s ∈ Ss, lam s)) +
        (∑ e ∈ Es, ∑ s ∈ Ss, T e s * ε e s) +
        D * (1 - ∑ e ∈ Es, ∑ s ∈ Ss, T e s) := by
  set A := ∑ s ∈ Ss, lam s with hA
  let ν : S → ℝ := fun s => lam s / A
  have hν : ∀ s ∈ Ss, 0 ≤ ν s := fun s hs => div_nonneg (hlam s hs) hlampos.le
  have hνprob : ∑ s ∈ Ss, ν s = 1 := by
    simp only [ν]
    rw [← Finset.sum_div, ← hA]
    exact div_self hlampos.ne'
  have hmain := edge_progress_bound Es Ss T Λ M ε d ν Γ D hT hd hedge hΓ
  have hjensen := mean_le_sqrt_mean_sq Ss ν d hν hνprob hd
  have hχ : ∑ s ∈ Ss, ν s * d s ^ 2 ≤ (∑ s ∈ Ss, ρ s) / A := by
    have : ∑ s ∈ Ss, ν s * d s ^ 2 = (∑ s ∈ Ss, lam s * d s ^ 2) / A := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      simp only [ν]
      ring
    rw [this]
    exact work_ratio_le Ss lam d ρ hwork hlampos
  have hfirst : Γ * (∑ s ∈ Ss, ν s * d s) ≤
      Γ * Real.sqrt ((∑ s ∈ Ss, ρ s) / A) :=
    mul_le_mul_of_nonneg_left (hjensen.trans (Real.sqrt_le_sqrt hχ)) hΓ0
  linarith

/-- **Optional exposure-headline bound.** Over finite exposures `E` and services `S`:
`μ` a probability vector; `T` a nonnegative partial transport with `Σ_s T e s ≤ μ e`
(`T1`); exposure losses `ℓ e ∈ [0, D]`; each edge with positive mass certified by
`ℓ e ≤ M e s · d s + ε e s` (the `(R)` certificate); `ν` a probability vector of service
weights with `Σ_e T e s · M e s ≤ Γ ν s` (`T3`, amplification).  Then

    Σ_e μ e · ℓ e ≤ Γ · Σ_s ν s · d s + Σ_{e,s} T e s · ε e s + D · (1 - Σ_{e,s} T e s). -/
theorem progress_bound (Es : Finset E) (Ss : Finset S)
    (μ : E → ℝ) (T : E → S → ℝ) (ℓ : E → ℝ) (M ε : E → S → ℝ) (d : S → ℝ) (ν : S → ℝ)
    (Γ D : ℝ)
    (hμ : ∀ e ∈ Es, 0 ≤ μ e) (hμ1 : ∑ e ∈ Es, μ e = 1)
    (hT : ∀ e ∈ Es, ∀ s ∈ Ss, 0 ≤ T e s)
    (hT1 : ∀ e ∈ Es, ∑ s ∈ Ss, T e s ≤ μ e)
    (hℓ0 : ∀ e ∈ Es, 0 ≤ ℓ e) (hℓD : ∀ e ∈ Es, ℓ e ≤ D)
    (hd : ∀ s ∈ Ss, 0 ≤ d s)
    (hedge : ∀ e ∈ Es, ∀ s ∈ Ss, 0 < T e s → ℓ e ≤ M e s * d s + ε e s)
    (hν : ∀ s ∈ Ss, 0 ≤ ν s)
    (hΓ : ∀ s ∈ Ss, ∑ e ∈ Es, T e s * M e s ≤ Γ * ν s) :
    ∑ e ∈ Es, μ e * ℓ e ≤
      Γ * (∑ s ∈ Ss, ν s * d s) + (∑ e ∈ Es, ∑ s ∈ Ss, T e s * ε e s) +
        D * (1 - ∑ e ∈ Es, ∑ s ∈ Ss, T e s) := by
  -- Step 1: split each exposure's mass into transported and residual parts.
  have hsplit : ∀ e ∈ Es, μ e * ℓ e ≤
      (∑ s ∈ Ss, T e s * ℓ e) + D * (μ e - ∑ s ∈ Ss, T e s) := by
    intro e he
    have hres : 0 ≤ μ e - ∑ s ∈ Ss, T e s := sub_nonneg.2 (hT1 e he)
    have : μ e * ℓ e = (∑ s ∈ Ss, T e s) * ℓ e + (μ e - ∑ s ∈ Ss, T e s) * ℓ e := by ring
    rw [this, Finset.sum_mul]
    have := mul_le_mul_of_nonneg_left (hℓD e he) hres
    linarith
  -- Step 2: bound each transported edge by its certificate.
  have hedge' : ∀ e ∈ Es, ∀ s ∈ Ss, T e s * ℓ e ≤ T e s * (M e s * d s + ε e s) := by
    intro e he s hs
    rcases (hT e he s hs).lt_or_eq with hpos | hzero
    · exact mul_le_mul_of_nonneg_left (hedge e he s hs hpos) hpos.le
    · rw [← hzero]; simp
  have h2 : ∑ e ∈ Es, μ e * ℓ e ≤
      (∑ e ∈ Es, ∑ s ∈ Ss, T e s * (M e s * d s + ε e s)) +
        D * (∑ e ∈ Es, (μ e - ∑ s ∈ Ss, T e s)) := by
    calc ∑ e ∈ Es, μ e * ℓ e
        ≤ ∑ e ∈ Es, ((∑ s ∈ Ss, T e s * ℓ e) + D * (μ e - ∑ s ∈ Ss, T e s)) :=
          Finset.sum_le_sum hsplit
      _ = (∑ e ∈ Es, ∑ s ∈ Ss, T e s * ℓ e) + D * (∑ e ∈ Es, (μ e - ∑ s ∈ Ss, T e s)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (∑ e ∈ Es, ∑ s ∈ Ss, T e s * (M e s * d s + ε e s)) +
            D * (∑ e ∈ Es, (μ e - ∑ s ∈ Ss, T e s)) := by
          exact (add_le_add_iff_right _).2
            (Finset.sum_le_sum fun e he =>
              Finset.sum_le_sum fun s hs => hedge' e he s hs)
  -- Step 3: the residual term.
  have hres : ∑ e ∈ Es, (μ e - ∑ s ∈ Ss, T e s) = 1 - ∑ e ∈ Es, ∑ s ∈ Ss, T e s := by
    rw [Finset.sum_sub_distrib, hμ1]
  -- Step 4: exchange sums and apply the amplification bound.
  have hamp : ∑ e ∈ Es, ∑ s ∈ Ss, T e s * (M e s * d s) ≤ Γ * ∑ s ∈ Ss, ν s * d s := by
    calc ∑ e ∈ Es, ∑ s ∈ Ss, T e s * (M e s * d s)
        = ∑ s ∈ Ss, (∑ e ∈ Es, T e s * M e s) * d s := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro e _
          ring
      _ ≤ ∑ s ∈ Ss, (Γ * ν s) * d s := by
          apply Finset.sum_le_sum
          intro s hs
          exact mul_le_mul_of_nonneg_right (hΓ s hs) (hd s hs)
      _ = Γ * ∑ s ∈ Ss, ν s * d s := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
  have hdistrib : ∑ e ∈ Es, ∑ s ∈ Ss, T e s * (M e s * d s + ε e s) =
      (∑ e ∈ Es, ∑ s ∈ Ss, T e s * (M e s * d s)) + ∑ e ∈ Es, ∑ s ∈ Ss, T e s * ε e s := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hres, hdistrib] at h2
  linarith

/-- **Optional exposure-headline quadratic bound.** This controls one loss per
exposure using its comparison to every positively weighted service edge. The public
edge-response statistic is controlled directly by `edge_progress_bound_quadratic`. -/
theorem progress_bound_quadratic (Es : Finset E) (Ss : Finset S)
    (μ : E → ℝ) (T : E → S → ℝ) (ℓ : E → ℝ) (M ε : E → S → ℝ) (d lam ρ : S → ℝ)
    (Γ D : ℝ)
    (hμ : ∀ e ∈ Es, 0 ≤ μ e) (hμ1 : ∑ e ∈ Es, μ e = 1)
    (hT : ∀ e ∈ Es, ∀ s ∈ Ss, 0 ≤ T e s)
    (hT1 : ∀ e ∈ Es, ∑ s ∈ Ss, T e s ≤ μ e)
    (hℓ0 : ∀ e ∈ Es, 0 ≤ ℓ e) (hℓD : ∀ e ∈ Es, ℓ e ≤ D)
    (hd : ∀ s ∈ Ss, 0 ≤ d s)
    (hedge : ∀ e ∈ Es, ∀ s ∈ Ss, 0 < T e s → ℓ e ≤ M e s * d s + ε e s)
    (hlam : ∀ s ∈ Ss, 0 ≤ lam s) (hlampos : 0 < ∑ s ∈ Ss, lam s)
    (hwork : ∀ s ∈ Ss, lam s * d s ^ 2 ≤ ρ s)
    (hΓ0 : 0 ≤ Γ)
    (hΓ : ∀ s ∈ Ss, ∑ e ∈ Es, T e s * M e s ≤ Γ * (lam s / ∑ s' ∈ Ss, lam s')) :
    ∑ e ∈ Es, μ e * ℓ e ≤
      Γ * Real.sqrt ((∑ s ∈ Ss, ρ s) / (∑ s ∈ Ss, lam s)) +
        (∑ e ∈ Es, ∑ s ∈ Ss, T e s * ε e s) +
        D * (1 - ∑ e ∈ Es, ∑ s ∈ Ss, T e s) := by
  set A := ∑ s ∈ Ss, lam s with hA
  let ν : S → ℝ := fun s => lam s / A
  have hν : ∀ s ∈ Ss, 0 ≤ ν s := fun s hs => div_nonneg (hlam s hs) hlampos.le
  have hνprob : ∑ s ∈ Ss, ν s = 1 := by
    simp only [ν]
    rw [← Finset.sum_div, ← hA]
    exact div_self hlampos.ne'
  have hmain := progress_bound Es Ss μ T ℓ M ε d ν Γ D hμ hμ1 hT hT1 hℓ0 hℓD hd hedge hν hΓ
  have hjensen := mean_le_sqrt_mean_sq Ss ν d hν hνprob hd
  have hχ : ∑ s ∈ Ss, ν s * d s ^ 2 ≤ (∑ s ∈ Ss, ρ s) / A := by
    have : ∑ s ∈ Ss, ν s * d s ^ 2 = (∑ s ∈ Ss, lam s * d s ^ 2) / A := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      simp only [ν]
      ring
    rw [this]
    exact work_ratio_le Ss lam d ρ hwork hlampos
  have hsqrt : Real.sqrt (∑ s ∈ Ss, ν s * d s ^ 2) ≤ Real.sqrt ((∑ s ∈ Ss, ρ s) / A) :=
    Real.sqrt_le_sqrt hχ
  have hfirst : Γ * (∑ s ∈ Ss, ν s * d s) ≤ Γ * Real.sqrt ((∑ s ∈ Ss, ρ s) / A) :=
    mul_le_mul_of_nonneg_left (hjensen.trans hsqrt) hΓ0
  linarith

end Progress

/-! ### A finite inhabitant of the Progress hypotheses

One exposure, one service, full transport, `d = 1/2`, `λ = 1`, `ρ = 1/4`, `M = 1`,
`ε = 0`, `ℓ = 1/2`, `D = 1`, `Γ = 1`.  This inhabits every field of
`progress_bound_quadratic`. -/

section ProgressWitness

/-- Every hypothesis of the quadratic edge theorem is inhabited: one exposure,
one service, transport `1/2`, loss `5/8`, defect `1/2`, multiplier `1`, error `1/8`,
intensity `1`, work budget `1/4`, amplification `1/2`, residual bound `1`.
The uptake, semantic-error, and residual terms are all strictly positive. -/
theorem edge_progress_witness :
    (∑ e ∈ ({()} : Finset Unit), ∑ s ∈ ({()} : Finset Unit),
        (1 / 2 : ℝ) * (5 / 8 : ℝ)) +
        (1 : ℝ) * (1 - ∑ e ∈ ({()} : Finset Unit),
          ∑ s ∈ ({()} : Finset Unit), (1 / 2 : ℝ)) ≤
      (1 / 2 : ℝ) * Real.sqrt ((∑ s ∈ ({()} : Finset Unit), (1 / 4 : ℝ)) /
          (∑ s ∈ ({()} : Finset Unit), (1 : ℝ))) +
        (∑ e ∈ ({()} : Finset Unit), ∑ s ∈ ({()} : Finset Unit),
          (1 / 2 : ℝ) * (1 / 8 : ℝ)) +
        (1 : ℝ) * (1 - ∑ e ∈ ({()} : Finset Unit),
          ∑ s ∈ ({()} : Finset Unit), (1 / 2 : ℝ)) :=
  edge_progress_bound_quadratic (E := Unit) (S := Unit) {()} {()}
    (fun _ _ => 1 / 2) (fun _ _ => 5 / 8) (fun _ _ => 1) (fun _ _ => 1 / 8)
    (fun _ => 1 / 2) (fun _ => 1) (fun _ => 1 / 4) (1 / 2) 1
    (by intros; norm_num) (by intros; norm_num) (by intros; norm_num)
    (by intros; norm_num) (by norm_num) (by intros; norm_num) (by norm_num)
    (by intros; norm_num)

/-- One exposure can have distinct losses on two services. Their average does not
control an arbitrarily chosen headline loss. Equal transport, edge losses `0,1`,
and headline loss `1` give the exact separating witness. -/
theorem edge_headline_separation :
    (∑ s : Bool, (1 / 2 : ℝ) * (if s then 1 else 0)) < (1 : ℝ) := by
  norm_num [Fintype.sum_bool]

theorem progress_witness :
    ∑ e ∈ ({()} : Finset Unit), (1 : ℝ) * (1 / 2 : ℝ) ≤
      (1 : ℝ) * Real.sqrt ((∑ s ∈ ({()} : Finset Unit), (1 / 4 : ℝ)) /
          (∑ s ∈ ({()} : Finset Unit), (1 : ℝ))) +
        (∑ e ∈ ({()} : Finset Unit), ∑ s ∈ ({()} : Finset Unit), (1 : ℝ) * (0 : ℝ)) +
        (1 : ℝ) * (1 - ∑ e ∈ ({()} : Finset Unit), ∑ s ∈ ({()} : Finset Unit), (1 : ℝ)) :=
  progress_bound_quadratic (E := Unit) (S := Unit) {()} {()}
    (fun _ => 1) (fun _ _ => 1) (fun _ => 1 / 2) (fun _ _ => 1) (fun _ _ => 0)
    (fun _ => 1 / 2) (fun _ => 1) (fun _ => 1 / 4) 1 1
    (by simp) (by simp) (by simp) (by simp) (by norm_num) (by norm_num) (by norm_num)
    (by intros; norm_num) (by simp) (by simp) (by intros; norm_num) (by norm_num)
    (by intros; simp)

end ProgressWitness

end Workspace.Normativity.Contrib.NormativeInductorComposition

#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.not_out_of_res
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.out_succ_of_born
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.res_unique
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.not_res_of_out
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.out_or_res_of_born
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.live_subset_exposures
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.exposures_mono
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.status_total
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.fate_unique
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.dispose_not_met'
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.carry
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.export_sound
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.carry_needs_successor
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.carry_witness
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.witnessIssue_anc_ans
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.cubeUpper_sat
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.cubeLower_sat
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.checkCompiled_iff
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.region_nonempty_of_check
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.farkas_sound
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.conflict_sound
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.compile_sound
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.failure_conserves
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.CompiledSchedule.regionPred_of_rows
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.CompiledSchedule.region_nonempty
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.compiled_end_to_end
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.Workload.cheapest_mem
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.Workload.w_cheapest
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.Workload.liability_le
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.Workload.adapted
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.Workload.plan_row
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.Workload.residual_zero
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.Workload.column_eq_service
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.Workload.total_service_eq_total_claim
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.sampleWorkload_affordable
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.anchored_response_transport
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.chainCert_fst_nonneg
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.chain_transport
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.chainCert_exact_carry
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.work_ratio_le
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.work_of_calibrated
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.mean_le_sqrt_mean_sq
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.edge_progress_bound
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.edge_progress_bound_quadratic
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.edge_progress_witness
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.edge_headline_separation
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.progress_bound
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.progress_bound_quadratic
#print axioms Workspace.Normativity.Contrib.NormativeInductorComposition.progress_witness
