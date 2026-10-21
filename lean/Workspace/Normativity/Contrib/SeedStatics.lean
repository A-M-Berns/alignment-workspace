/-
# Seed statics: settlement, forms, the forced region, certificates, elimination

Landed on `main` by the round `2026-10-21-rebuttal-and-end-to-end` (ruling M6 of its
dispatch) from the branch `round/2026-09-16-seed-statics` (`SeedStatics.lean`, as carried
by `round/2026-09-17-convergence-measure`), superseding both the branch file and the copy
of its first five sections that `WarrantEntitlement.lean` carried.  Built on the
rational-row compiler of `NormativeInductorComposition` §2 (`Row`, `CitedRow`, `Bundle`,
`Bundle.Region`, `checkCompiled`, `FarkasCert`) and the Fourier–Motzkin elimination of
`FourierMotzkin`.  Nothing is registered by this file alone; every name is provisional
(`AGENTS.md` standard 6).

Sections, numbered as on the branch so the branch round's documents still read:

1. **Settlement and specialization.**  A settled fragment pins coordinates; a row
   specializes by substituting the settled coordinates (`specialize_sat_iff`).
2. **The seed.**  Substantive items are leverage forms (`premise`, `applicability`,
   `strength`) carrying a strength and a docket port; structural items are raw rows with a
   kind and a surface id; the constitutive layer is declared data.  Two withdrawal
   channels (`liveStr_indep_defeat`, `liveSub_indep_withdraw`).
3. **The forced region** is `Bundle.Region` of a computable bundle, decided by
   `checkCompiled` (`forcedRegion_iff_check`, `forcedRegion_iff`).
4. **Monotonicity under settlement** (`forcedRegion_anti`, `IsForcedInterval.mono`) and
   its failure under defeat (`defeat_widens`); `Pins`, `Refuted`, `leverage`.
   These statements are about the unspecialized-row region and remain true; the
   rebuttal rule of the 2026-10-21 round acts on the *settled* region of
   `WarrantEntitlement.lean`, where monotonicity is restated.
5. **Certificates.**  Bound certificates (`BoundCert`, `sound`, `sound_of_pos`,
   `lowerCert_bound`, `upperCert_bound`), sure loss (`SureLoss`, `sureLoss_of_cert`), the
   support of a Farkas certificate (`FarkasCert.support_sound`), `MinimalInfeasible`.
6. **The interval by elimination.**  Rows convert to `LinCon`; eliminating every
   coordinate but `φ` computes the projection (`project_sat_iff`); the endpoints of the
   one-dimensional system are the forced interval, attained over `ℝ`
   (`forcedInterval_spec`, `forcedInterval_bounds`, `forcedInterval_mono`).
8. **Seed-independence.**  Refuted for item-level humility (`c3_refuted`); the strict
   form holds (`seed_independence_strict`, via `point_forced_of_open_layer`).
10. **Stabilization.**  `eventually_const_of_monotone`, `eventually_const_of_finite`,
    `tendsto_of_summable_drops`.

Not landed, by the dispatch: §7 confinement, §9 transport (its negated-form drop is filed,
not fixed), §11 non-dogmatism.  Additions over the branch, all from the
warrant-enforcement-semantics round: `DecidableEq` on `Form`, `SubItem`, `DocketState`,
`Cite`; `Form.applicability_sat_iff`, `Form.strength_sat_iff`; a `Decidable` instance for
`forcedRegion`; `Settlement.empty_pinRowsAt`; `BoundCert.sound_of_pos`.
-/

import Workspace.Normativity.Contrib.NormativeInductorComposition
import Workspace.Normativity.Contrib.FourierMotzkin

namespace Workspace.Normativity.Contrib.SeedStatics

open Workspace.Normativity.Contrib.NormativeInductorComposition
open Finset

variable {d : ℕ}

/-! ## 1. Settlement and specialization -/

/-- The rational truth value of a settled coordinate. -/
def truth (b : Bool) : ℚ := if b then 1 else 0

/-- A **settled fragment** over `d` coordinates: the settled ones carry a truth value. -/
structure Settlement (d : ℕ) where
  val : Fin d → Option Bool

namespace Settlement

/-- A price vector agrees with the settlement on every settled coordinate. -/
def Pinned (F : Settlement d) (x : Fin d → ℚ) : Prop :=
  ∀ i b, F.val i = some b → x i = truth b

/-- `F ⊆ F'` with compatible valuations. -/
def le (F F' : Settlement d) : Prop := ∀ i b, F.val i = some b → F'.val i = some b

/-- The empty settlement. -/
def empty (d : ℕ) : Settlement d := ⟨fun _ => none⟩

theorem empty_pinned (x : Fin d → ℚ) : (empty d).Pinned x := by
  intro i b h; simp [empty] at h

theorem le_refl (F : Settlement d) : F.le F := fun _ _ h => h

theorem Pinned.mono {F F' : Settlement d} (h : F.le F') {x : Fin d → ℚ} (hx : F'.Pinned x) :
    F.Pinned x := fun i b hi => hx i b (h i b hi)

/-- The two pin rows of a settled coordinate: `x i ≤ v` and `-x i ≤ -v`. -/
def pinRowsAt (F : Settlement d) (i : Fin d) : List (Row d) :=
  (F.val i).elim [] fun b =>
    [⟨fun j => if j = i then 1 else 0, truth b⟩, ⟨fun j => if j = i then -1 else 0, -truth b⟩]

/-- All pin rows. -/
def pinRows (F : Settlement d) : List (Row d) := (List.finRange d).flatMap F.pinRowsAt

lemma pinRowsAt_sat_iff (F : Settlement d) (i : Fin d) (x : Fin d → ℚ) :
    (∀ r ∈ F.pinRowsAt i, r.Sat x) ↔ ∀ b, F.val i = some b → x i = truth b := by
  unfold pinRowsAt
  cases h : F.val i with
  | none => simp
  | some b =>
    simp only [Option.elim, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Option.some.injEq, forall_eq']
    unfold Row.Sat
    simp only [ite_mul, one_mul, neg_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    constructor
    · rintro ⟨h1, h2⟩; linarith
    · intro h; constructor <;> linarith

theorem pinRows_sat_iff (F : Settlement d) (x : Fin d → ℚ) :
    (∀ r ∈ F.pinRows, r.Sat x) ↔ F.Pinned x := by
  unfold pinRows Pinned
  simp only [List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · intro h i b hi
    exact (pinRowsAt_sat_iff F i x).1 (fun r hr => h r ⟨i, hr⟩) b hi
  · rintro h r ⟨i, hr⟩
    exact (pinRowsAt_sat_iff F i x).2 (h i) r hr

/-- The empty settlement has no pin rows. -/
@[simp] theorem empty_pinRowsAt (i : Fin d) : (empty d).pinRowsAt i = [] := rfl

end Settlement

/-- The settled contribution of coordinate `i` to a row's left-hand side. -/
def settledTerm (F : Settlement d) (r : Row d) (i : Fin d) : ℚ :=
  (F.val i).elim 0 fun b => r.a i * truth b

/-- **Specialization**: settled coordinates are substituted; the row becomes a row over
the unsettled coordinates (zero coefficient elsewhere) with an adjusted constant. -/
def specialize (F : Settlement d) (r : Row d) : Row d :=
  ⟨fun i => if (F.val i).isSome then 0 else r.a i, r.b - ∑ i, settledTerm F r i⟩

/-- On the pinned slice, the specialized row says exactly what the original row says. -/
theorem specialize_sat_iff (F : Settlement d) (r : Row d) {x : Fin d → ℚ} (hx : F.Pinned x) :
    (specialize F r).Sat x ↔ r.Sat x := by
  unfold Row.Sat specialize
  have key : ∀ i, r.a i * x i =
      (if (F.val i).isSome then 0 else r.a i) * x i + settledTerm F r i := by
    intro i
    unfold settledTerm
    cases h : F.val i with
    | none => simp
    | some b => simp [hx i b h]
  simp only
  rw [show (∑ i, r.a i * x i) =
      ∑ i, ((if (F.val i).isSome then 0 else r.a i) * x i + settledTerm F r i) from
      Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib]
  constructor <;> intro h <;> linarith

/-! ## 2. The seed -/

/-- The three leverage forms of an endorsement, each carrying its strength `c`:
`premise X c` is `P(X) ≥ c`; `applicability X XA c` is `P(X∧A) ≥ c·P(X)`;
`strength XA XAY c` is `P(X∧A∧Y) ≥ c·P(X∧A)`. -/
inductive Form (d : ℕ) where
  | premise (X : Fin d) (c : ℚ)
  | applicability (X XA : Fin d) (c : ℚ)
  | strength (XA XAY : Fin d) (c : ℚ)
  deriving DecidableEq

namespace Form

/-- The strength of a form. -/
def c : Form d → ℚ
  | premise _ c => c
  | applicability _ _ c => c
  | strength _ _ c => c

/-- The row `a · x ≤ b` an endorsement compiles to. -/
def row : Form d → Row d
  | premise X c => ⟨fun j => if j = X then -1 else 0, -c⟩
  | applicability X XA c => ⟨fun j => (if j = X then c else 0) + (if j = XA then -1 else 0), 0⟩
  | strength XA XAY c => ⟨fun j => (if j = XA then c else 0) + (if j = XAY then -1 else 0), 0⟩

theorem premise_sat_iff (X : Fin d) (c : ℚ) (x : Fin d → ℚ) :
    (premise X c).row.Sat x ↔ c ≤ x X := by
  unfold row Row.Sat
  simp only [ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  constructor <;> intro h <;> linarith

theorem applicability_sat_iff (X XA : Fin d) (c : ℚ) (x : Fin d → ℚ) :
    (applicability X XA c).row.Sat x ↔ c * x X ≤ x XA := by
  unfold row Row.Sat
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, neg_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  constructor <;> intro h <;> linarith

theorem strength_sat_iff (XA XAY : Fin d) (c : ℚ) (x : Fin d → ℚ) :
    (strength XA XAY c).row.Sat x ↔ c * x XA ≤ x XAY := by
  unfold row Row.Sat
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, neg_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  constructor <;> intro h <;> linarith

end Form

/-- A **substantive item**: a leverage form with a docket port.  Defeasible: a defeater
landing on the port removes it from the live bundle. -/
structure SubItem (d : ℕ) where
  form : Form d
  port : ℕ
  deriving DecidableEq

/-- The kinds a structural row may declare. -/
inductive StrKind where
  | dominance
  | impartiality
  | coherence
  deriving DecidableEq

/-- A **structural item**: a raw row of strength one with a kind and a surface id.
Not defeasible by the docket; withdrawn only by a surface-change occurrence. -/
structure StrItem (d : ℕ) where
  row : Row d
  kind : StrKind
  id : ℕ

/-- The **constitutive layer** as declared data: the standing set and the protected
class of coordinates.  Nothing in the statics computes from these; they are what a
reasoner may not change unilaterally. -/
structure Constitutive (d : ℕ) (A : Type*) where
  standing : Finset A
  protectedClass : Finset (Fin d)

/-- A **seed**. -/
structure Seed (d : ℕ) (A : Type*) where
  sub : List (SubItem d)
  str : List (StrItem d)
  con : Constitutive d A

/-- **Item-level humility of the substantive layer**: every strength lies in `(0,1)`. -/
def Seed.HumbleItems {A : Type*} (S : Seed d A) : Prop :=
  ∀ it ∈ S.sub, 0 < it.form.c ∧ it.form.c < 1

instance {A : Type*} (S : Seed d A) : Decidable S.HumbleItems := by
  unfold Seed.HumbleItems; infer_instance

/-- The **docket state**: ports with a landed defeater, and structural ids withdrawn by
a surface-change occurrence.  Two channels, deliberately separate. -/
structure DocketState where
  defeated : Finset ℕ
  withdrawn : Finset ℕ
  deriving DecidableEq

/-- The quiet docket. -/
def DocketState.quiet : DocketState := ⟨∅, ∅⟩

/-- Live substantive items: port not defeated. -/
def Seed.liveSub {A : Type*} (S : Seed d A) (st : DocketState) : List (SubItem d) :=
  S.sub.filter fun it => it.port ∉ st.defeated

/-- Live structural items: id not withdrawn. -/
def Seed.liveStr {A : Type*} (S : Seed d A) (st : DocketState) : List (StrItem d) :=
  S.str.filter fun it => it.id ∉ st.withdrawn

/-- A docket defeat never reaches a structural item. -/
theorem Seed.liveStr_indep_defeat {A : Type*} (S : Seed d A) (D D' W : Finset ℕ) :
    S.liveStr ⟨D, W⟩ = S.liveStr ⟨D', W⟩ := rfl

/-- A surface change never reaches a substantive item. -/
theorem Seed.liveSub_indep_withdraw {A : Type*} (S : Seed d A) (D W W' : Finset ℕ) :
    S.liveSub ⟨D, W⟩ = S.liveSub ⟨D, W'⟩ := rfl

/-! ## 3. The forced region -/

/-- What a row of the forced bundle cites. -/
inductive Cite (d : ℕ) where
  | sub (port : ℕ)
  | str (id : ℕ)
  | settled (i : Fin d)
  deriving DecidableEq

/-- The pin rows, cited. -/
def pinCited (F : Settlement d) : Bundle (Cite d) d :=
  (List.finRange d).flatMap fun i => (F.pinRowsAt i).map fun r => ⟨Cite.settled i, r⟩

/-- **The forced bundle** of a seed, a live warrant set `W`, a docket state and a
settlement: every live specialized endorsement, plus the pin rows. -/
def forcedBundle {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) : Bundle (Cite d) d :=
  ((S.liveSub st ++ W).map fun it => ⟨Cite.sub it.port, specialize F it.form.row⟩) ++
  ((S.liveStr st).map fun it => ⟨Cite.str it.id, specialize F it.row⟩) ++
  pinCited F

/-- **The forced region** `K(S ∪ W, F)`, at rational points. -/
def forcedRegion {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) (x : Fin d → ℚ) : Prop :=
  (forcedBundle S W st F).Region x

instance {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) (x : Fin d → ℚ) : Decidable (forcedRegion S W st F x) := by
  unfold forcedRegion; infer_instance

/-- `checkCompiled` decides membership in the forced region. -/
theorem forcedRegion_iff_check {A : Type*} (S : Seed d A) (W : List (SubItem d))
    (st : DocketState) (F : Settlement d) (x : Fin d → ℚ) :
    forcedRegion S W st F x ↔ checkCompiled (forcedBundle S W st F) x = true :=
  (checkCompiled_iff _ _).symm

lemma pinCited_sat_iff (F : Settlement d) (x : Fin d → ℚ) :
    (∀ c ∈ pinCited F, c.row.Sat x) ↔ F.Pinned x := by
  rw [← Settlement.pinRows_sat_iff]
  unfold pinCited Settlement.pinRows
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  constructor
  · rintro h r ⟨i, hr⟩
    exact h ⟨Cite.settled i, r⟩ ⟨i, r, hr, rfl⟩
  · rintro h c ⟨i, r, hr, rfl⟩
    exact h r ⟨i, hr⟩

/-- **The forced region, read on the unspecialized rows.**  A point is in it iff it is in
the cube, pinned by the settlement, and satisfies every live original row. -/
theorem forcedRegion_iff {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) (x : Fin d → ℚ) :
    forcedRegion S W st F x ↔
      InCube x ∧ F.Pinned x ∧
      (∀ it ∈ S.liveSub st ++ W, it.form.row.Sat x) ∧
      (∀ it ∈ S.liveStr st, it.row.Sat x) := by
  unfold forcedRegion Bundle.Region forcedBundle
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro ⟨hcube, hrows⟩
    have hpin : F.Pinned x := (pinCited_sat_iff F x).1 fun c hc => hrows c (Or.inr hc)
    refine ⟨hcube, hpin, ?_, ?_⟩
    · intro it hit
      have := hrows ⟨Cite.sub it.port, specialize F it.form.row⟩ (Or.inl (Or.inl ⟨it, hit, rfl⟩))
      exact (specialize_sat_iff F _ hpin).1 this
    · intro it hit
      have := hrows ⟨Cite.str it.id, specialize F it.row⟩ (Or.inl (Or.inr ⟨it, hit, rfl⟩))
      exact (specialize_sat_iff F _ hpin).1 this
  · rintro ⟨hcube, hpin, hsub, hstr⟩
    refine ⟨hcube, ?_⟩
    rintro c ((⟨it, hit, rfl⟩ | ⟨it, hit, rfl⟩) | hc)
    · exact (specialize_sat_iff F _ hpin).2 (hsub it hit)
    · exact (specialize_sat_iff F _ hpin).2 (hstr it hit)
    · exact (pinCited_sat_iff F x).2 hpin c hc

/-! ## 4. Monotonicity under settlement, and its failure under defeat -/

/-- **Monotonicity under settlement.**  More settlement, smaller region. -/
theorem forcedRegion_anti {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    {F F' : Settlement d} (h : F.le F') {x : Fin d → ℚ} (hx : forcedRegion S W st F' x) :
    forcedRegion S W st F x := by
  rw [forcedRegion_iff] at hx ⊢
  exact ⟨hx.1, hx.2.1.mono h, hx.2.2.1, hx.2.2.2⟩

/-- `c` is a valid lower bound on `P(φ)` over the forced region. -/
def LowerBound {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) (φ : Fin d) (c : ℚ) : Prop :=
  ∀ x, forcedRegion S W st F x → c ≤ x φ

/-- `c` is a valid upper bound on `P(φ)` over the forced region. -/
def UpperBound {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) (φ : Fin d) (c : ℚ) : Prop :=
  ∀ x, forcedRegion S W st F x → x φ ≤ c

/-- **The forced interval** `[lo, hi]` of `φ`: valid bounds, both attained. -/
structure IsForcedInterval {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) (φ : Fin d) (lo hi : ℚ) : Prop where
  lower : LowerBound S W st F φ lo
  upper : UpperBound S W st F φ hi
  lo_mem : ∃ x, forcedRegion S W st F x ∧ x φ = lo
  hi_mem : ∃ x, forcedRegion S W st F x ∧ x φ = hi

namespace IsForcedInterval

variable {A : Type*} {S : Seed d A} {W : List (SubItem d)} {st : DocketState} {F : Settlement d}
  {φ : Fin d}

theorem le {lo hi : ℚ} (I : IsForcedInterval S W st F φ lo hi) : lo ≤ hi := by
  obtain ⟨x, hx, rfl⟩ := I.lo_mem
  exact I.upper x hx

theorem unique {lo hi lo' hi' : ℚ} (I : IsForcedInterval S W st F φ lo hi)
    (I' : IsForcedInterval S W st F φ lo' hi') : lo = lo' ∧ hi = hi' := by
  obtain ⟨x, hx, rfl⟩ := I.lo_mem
  obtain ⟨x', hx', rfl⟩ := I'.lo_mem
  obtain ⟨y, hy, rfl⟩ := I.hi_mem
  obtain ⟨y', hy', rfl⟩ := I'.hi_mem
  exact ⟨le_antisymm (I.lower x' hx') (I'.lower x hx),
    le_antisymm (I'.upper y hy) (I.upper y' hy')⟩

/-- **Monotonicity of forced intervals under settlement**: `I_φ(S, F') ⊆ I_φ(S, F)`. -/
theorem mono {F' : Settlement d} (h : F.le F') {lo hi lo' hi' : ℚ}
    (I : IsForcedInterval S W st F φ lo hi) (I' : IsForcedInterval S W st F' φ lo' hi') :
    lo ≤ lo' ∧ hi' ≤ hi := by
  obtain ⟨x, hx, rfl⟩ := I'.lo_mem
  obtain ⟨y, hy, rfl⟩ := I'.hi_mem
  exact ⟨I.lower x (forcedRegion_anti S W st h hx), I.upper y (forcedRegion_anti S W st h hy)⟩

end IsForcedInterval

/-- A point is **pinned** when its forced interval is degenerate. -/
def Pins {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) (φ : Fin d) (p : ℚ) : Prop :=
  ∀ x, forcedRegion S W st F x → x φ = p

/-- **Empirical refutation** is a definition, not a theorem: feasible on `F`, infeasible on
a compatible extension `F'`. -/
def Refuted {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F F' : Settlement d) : Prop :=
  F.le F' ∧ (∃ x, forcedRegion S W st F x) ∧ ¬ ∃ x, forcedRegion S W st F' x

/-- **Seed leverage** over a declared list of coordinates, from interval data: the sum of
`1 − width`.  Provisional; counts level content only. -/
def leverage (I : Fin d → ℚ × ℚ) (U : List (Fin d)) : ℚ :=
  (U.map fun φ => 1 - ((I φ).2 - (I φ).1)).sum

/-- Defeat widening witness: one substantive item `P(0) ≥ 1/2` on one coordinate.  With
the quiet docket `1/2` is a valid lower bound; once port `0` is defeated the point `0`
lies in the region, so no positive lower bound is valid. -/
def widenSeed : Seed 1 Unit :=
  ⟨[⟨Form.premise 0 (1/2), 0⟩], [], ⟨∅, ∅⟩⟩

theorem defeat_widens :
    LowerBound widenSeed [] DocketState.quiet (Settlement.empty 1) 0 (1/2) ∧
    ¬ LowerBound widenSeed [] ⟨{0}, ∅⟩ (Settlement.empty 1) 0 (1/2) := by
  constructor
  · intro x hx
    rw [forcedRegion_iff] at hx
    have := hx.2.2.1 ⟨Form.premise 0 (1/2), 0⟩ (by simp [widenSeed, Seed.liveSub, DocketState.quiet])
    exact (Form.premise_sat_iff _ _ _).1 this
  · intro h
    have hx : forcedRegion widenSeed [] ⟨{0}, ∅⟩ (Settlement.empty 1) (fun _ => 0) := by
      rw [forcedRegion_iff]
      refine ⟨fun _ => by norm_num, Settlement.empty_pinned _, ?_, ?_⟩
      · intro it hit; simp [widenSeed, Seed.liveSub] at hit
      · intro it hit; simp [widenSeed, Seed.liveStr] at hit
    have := h _ hx
    norm_num at this

/-! ## 5. Certificates -/

/-- A row allowed against a bundle is satisfied by every point of the bundle's region. -/
theorem allowed_sat {Q : Type*} {B : Bundle Q d} {r : Row d} (h : B.Allowed r) {x : Fin d → ℚ}
    (hx : B.Region x) : r.Sat x := by
  rcases h with ⟨cr, hcr, hrow⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [← hrow]; exact hx.2 cr hcr
  · rw [hj]; exact cubeUpper_sat hx.1 j
  · rw [hj]; exact cubeLower_sat hx.1 j

/-- **A bound certificate**: nonnegative multipliers on rows whose weighted coefficient sum
is `s · e_φ`.  With `s = -1` it certifies a lower bound, with `s = 1` an upper bound. -/
structure BoundCert (d m : ℕ) (φ : Fin d) (s : ℚ) where
  mult : Fin m → ℚ
  row : Fin m → Row d
  mult_nonneg : ∀ i, 0 ≤ mult i
  coeff_sum : ∀ j, ∑ i, mult i * (row i).a j = if j = φ then s else 0

/-- The value a bound certificate certifies. -/
def BoundCert.value {m : ℕ} {φ : Fin d} {s : ℚ} (c : BoundCert d m φ s) : ℚ :=
  ∑ i, c.mult i * (c.row i).b

/-- **Soundness**, needing the rows only where the multiplier is positive: at any point
satisfying the positively weighted rows, `s · x φ ≤ value`. -/
theorem BoundCert.sound_of_pos {m : ℕ} {φ : Fin d} {s : ℚ} (c : BoundCert d m φ s)
    (x : Fin d → ℚ) (hx : ∀ i, 0 < c.mult i → (c.row i).Sat x) : s * x φ ≤ c.value := by
  have h1 : ∑ i, c.mult i * ∑ j, (c.row i).a j * x j ≤ ∑ i, c.mult i * (c.row i).b := by
    apply Finset.sum_le_sum
    intro i _
    rcases (c.mult_nonneg i).lt_or_eq with hpos | hzero
    · exact mul_le_mul_of_nonneg_left (hx i hpos) hpos.le
    · rw [← hzero]; simp
  have h2 : ∑ i, c.mult i * ∑ j, (c.row i).a j * x j = s * x φ := by
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
      _ = ∑ j, (if j = φ then s else 0) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [c.coeff_sum j]
      _ = s * x φ := by
          simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold BoundCert.value
  linarith

/-- **Soundness** at any point satisfying every weighted row. -/
theorem BoundCert.sound {m : ℕ} {φ : Fin d} {s : ℚ} (c : BoundCert d m φ s) (x : Fin d → ℚ)
    (hx : ∀ i, (c.row i).Sat x) : s * x φ ≤ c.value :=
  c.sound_of_pos x fun i _ => hx i

/-- A lower-bound certificate over the forced bundle's allowed rows certifies a valid
lower bound `-value` on `P(φ)`. -/
theorem lowerCert_bound {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) (φ : Fin d) {m : ℕ} (c : BoundCert d m φ (-1))
    (hallowed : ∀ i, (forcedBundle S W st F).Allowed (c.row i)) :
    LowerBound S W st F φ (-c.value) := by
  intro x hx
  have := c.sound x fun i => allowed_sat (hallowed i) hx
  linarith

/-- An upper-bound certificate over the forced bundle's allowed rows certifies a valid
upper bound `value` on `P(φ)`. -/
theorem upperCert_bound {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) (φ : Fin d) {m : ℕ} (c : BoundCert d m φ 1)
    (hallowed : ∀ i, (forcedBundle S W st F).Allowed (c.row i)) :
    UpperBound S W st F φ c.value := by
  intro x hx
  have := c.sound x fun i => allowed_sat (hallowed i) hx
  linarith

/-- **Sure loss**: the forced region is empty. -/
def SureLoss {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) : Prop :=
  ¬ ∃ x, forcedRegion S W st F x

/-- A Farkas certificate over the forced bundle's allowed rows is a sure-loss certificate. -/
theorem sureLoss_of_cert {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) {m : ℕ} (c : FarkasCert d m)
    (hallowed : ∀ i, (forcedBundle S W st F).Allowed (c.row i)) : SureLoss S W st F :=
  conflict_sound _ c hallowed

/-- **The support of a Farkas certificate is itself infeasible**: rows with zero
multiplier contribute nothing, so a point need only satisfy the positively weighted rows
to be refuted. -/
theorem FarkasCert.support_sound {m : ℕ} (c : FarkasCert d m) (x : Fin d → ℚ)
    (hx : ∀ i, 0 < c.mult i → (c.row i).Sat x) : False := by
  have h1 : ∑ i, c.mult i * ∑ j, (c.row i).a j * x j ≤ ∑ i, c.mult i * (c.row i).b := by
    apply Finset.sum_le_sum
    intro i _
    rcases (c.mult_nonneg i).lt_or_eq with hpos | hzero
    · exact mul_le_mul_of_nonneg_left (hx i hpos) (c.mult_nonneg i)
    · rw [← hzero]; simp
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

/-- **Minimal infeasible subset** of rows, relative to the cube: infeasible, and every
proper subset obtained by deleting one row is feasible.  A definition; extraction is the
fixture's job. -/
def MinimalInfeasible {m : ℕ} (rows : Fin m → Row d) : Prop :=
  (¬ ∃ x, InCube x ∧ ∀ i, (rows i).Sat x) ∧
  ∀ i, ∃ x, InCube x ∧ ∀ j, j ≠ i → (rows j).Sat x

/-! ## 6. The interval by elimination

Everything here is over the reals, which is where `FourierMotzkin` states satisfaction.
The dimension is written `m + 1` so that a coordinate `0` exists and the projection
recursion is structural. -/

/-- The real forced region: `Bundle.RegionR` of the forced bundle. -/
def forcedRegionR {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) (x : Fin d → ℝ) : Prop :=
  (forcedBundle S W st F).RegionR x

/-- A rational row holds at a rational point iff it holds at its real image. -/
theorem sat_iff_satR (r : Row d) (x : Fin d → ℚ) :
    r.Sat x ↔ r.SatR (fun i => (x i : ℝ)) := by
  show (∑ i, r.a i * x i ≤ r.b) ↔ (∑ i, (r.a i : ℝ) * (x i : ℝ) ≤ (r.b : ℝ))
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- A row with a single nonzero coefficient, at a real point. -/
lemma single_satR {n : ℕ} (i : Fin n) (c b : ℚ) (x : Fin n → ℝ) :
    (⟨fun j => if j = i then c else 0, b⟩ : Row n).SatR x ↔ (c : ℝ) * x i ≤ (b : ℝ) := by
  unfold Row.SatR
  simp only
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

/-- The rational forced region embeds in the real one. -/
theorem forcedRegionR_of_forcedRegion {A : Type*} (S : Seed d A) (W : List (SubItem d))
    (st : DocketState) (F : Settlement d) {x : Fin d → ℚ} (hx : forcedRegion S W st F x) :
    forcedRegionR S W st F (fun i => (x i : ℝ)) := by
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · show (0 : ℝ) ≤ ((x i : ℚ) : ℝ)
    exact_mod_cast (hx.1 i).1
  · show ((x i : ℚ) : ℝ) ≤ 1
    exact_mod_cast (hx.1 i).2
  · intro c hc
    exact (sat_iff_satR _ _).1 (hx.2 c hc)

/-- Real pinning. -/
def Settlement.PinnedR (F : Settlement d) (x : Fin d → ℝ) : Prop :=
  ∀ i b, F.val i = some b → x i = (truth b : ℝ)

lemma Settlement.pinRowsAt_satR_iff (F : Settlement d) (i : Fin d) (x : Fin d → ℝ) :
    (∀ r ∈ F.pinRowsAt i, r.SatR x) ↔ ∀ b, F.val i = some b → x i = (truth b : ℝ) := by
  unfold Settlement.pinRowsAt
  cases h : F.val i with
  | none => simp
  | some b =>
    simp only [Option.elim, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Option.some.injEq, forall_eq']
    rw [single_satR, single_satR]
    simp only [Rat.cast_one, Rat.cast_neg, one_mul, neg_mul]
    constructor
    · rintro ⟨h1, h2⟩; linarith
    · intro h; constructor <;> linarith

lemma pinCited_satR_iff (F : Settlement d) (x : Fin d → ℝ) :
    (∀ c ∈ pinCited F, c.row.SatR x) ↔ F.PinnedR x := by
  unfold pinCited Settlement.PinnedR
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  constructor
  · rintro h i b hi
    exact (Settlement.pinRowsAt_satR_iff F i x).1
      (fun r hr => h ⟨Cite.settled i, r⟩ ⟨i, r, hr, rfl⟩) b hi
  · rintro h c ⟨i, r, hr, rfl⟩
    exact (Settlement.pinRowsAt_satR_iff F i x).2 (h i) r hr

theorem specialize_satR_iff (F : Settlement d) (r : Row d) {x : Fin d → ℝ} (hx : F.PinnedR x) :
    (specialize F r).SatR x ↔ r.SatR x := by
  unfold Row.SatR specialize
  have key : ∀ i, (r.a i : ℝ) * x i =
      ((if (F.val i).isSome then (0 : ℚ) else r.a i : ℚ) : ℝ) * x i + (settledTerm F r i : ℝ) := by
    intro i
    unfold settledTerm
    cases h : F.val i with
    | none => simp
    | some b => simp [hx i b h]
  simp only [Rat.cast_sub, Rat.cast_sum]
  rw [show (∑ i, (r.a i : ℝ) * x i) =
      ∑ i, (((if (F.val i).isSome then (0 : ℚ) else r.a i : ℚ) : ℝ) * x i + (settledTerm F r i : ℝ)) from
      Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib]
  constructor <;> intro h <;> linarith

theorem forcedRegionR_iff {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) (x : Fin d → ℝ) :
    forcedRegionR S W st F x ↔
      (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ F.PinnedR x ∧
      (∀ it ∈ S.liveSub st ++ W, it.form.row.SatR x) ∧
      (∀ it ∈ S.liveStr st, it.row.SatR x) := by
  unfold forcedRegionR Bundle.RegionR forcedBundle
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro ⟨hcube, hrows⟩
    have hpin : F.PinnedR x := (pinCited_satR_iff F x).1 fun c hc => hrows c (Or.inr hc)
    refine ⟨hcube, hpin, ?_, ?_⟩
    · intro it hit
      have := hrows ⟨Cite.sub it.port, specialize F it.form.row⟩ (Or.inl (Or.inl ⟨it, hit, rfl⟩))
      exact (specialize_satR_iff F _ hpin).1 this
    · intro it hit
      have := hrows ⟨Cite.str it.id, specialize F it.row⟩ (Or.inl (Or.inr ⟨it, hit, rfl⟩))
      exact (specialize_satR_iff F _ hpin).1 this
  · rintro ⟨hcube, hpin, hsub, hstr⟩
    refine ⟨hcube, ?_⟩
    rintro c ((⟨it, hit, rfl⟩ | ⟨it, hit, rfl⟩) | hc)
    · exact (specialize_satR_iff F _ hpin).2 (hsub it hit)
    · exact (specialize_satR_iff F _ hpin).2 (hstr it hit)
    · exact (pinCited_satR_iff F x).2 hpin c hc

theorem Settlement.PinnedR.mono {F F' : Settlement d} (h : F.le F') {x : Fin d → ℝ}
    (hx : F'.PinnedR x) : F.PinnedR x := fun i b hi => hx i b (h i b hi)

/-- Monotonicity under settlement, real form. -/
theorem forcedRegionR_anti {A : Type*} (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    {F F' : Settlement d} (h : F.le F') {x : Fin d → ℝ} (hx : forcedRegionR S W st F' x) :
    forcedRegionR S W st F x := by
  rw [forcedRegionR_iff] at hx ⊢
  exact ⟨hx.1, hx.2.1.mono h, hx.2.2.1, hx.2.2.2⟩

section Elimination

open Workspace.Normativity.Contrib.FourierMotzkin

variable {m : ℕ}

/-- The transposition placing `φ` at position `0`. -/
def pos (φ : Fin (m + 1)) : Equiv.Perm (Fin (m + 1)) := Equiv.swap φ 0

lemma pos_zero (φ : Fin (m + 1)) : pos φ 0 = φ := Equiv.swap_apply_right φ 0

lemma pos_self (φ : Fin (m + 1)) : pos φ φ = 0 := Equiv.swap_apply_left φ 0

lemma pos_pos (φ : Fin (m + 1)) (k : Fin (m + 1)) : pos φ (pos φ k) = k :=
  Equiv.swap_apply_self φ 0 k

/-- A row as a `LinCon` with `φ` moved to position `0`. -/
def toLinCon (φ : Fin (m + 1)) (r : Row (m + 1)) : LinCon :=
  (List.ofFn fun k : Fin (m + 1) => r.a (pos φ k), r.b, false)

lemma toLinCon_coeff (φ : Fin (m + 1)) (r : Row (m + 1)) (k : Fin (m + 1)) :
    (toLinCon φ r).coeffs.getD (k : ℕ) 0 = r.a (pos φ k) := by
  show (List.ofFn fun k : Fin (m + 1) => r.a (pos φ k)).getD (k : ℕ) 0 = r.a (pos φ k)
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos k.isLt]
  rfl

lemma toLinCon_coeff_ge (φ : Fin (m + 1)) (r : Row (m + 1)) (n : ℕ) (hn : m + 1 ≤ n) :
    (toLinCon φ r).coeffs.getD n 0 = 0 := by
  show (List.ofFn fun k : Fin (m + 1) => r.a (pos φ k)).getD n 0 = 0
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_neg (by omega)]
  rfl

lemma toLinCon_strict (φ : Fin (m + 1)) (r : Row (m + 1)) : (toLinCon φ r).strict = false := rfl

lemma toLinCon_const (φ : Fin (m + 1)) (r : Row (m + 1)) : (toLinCon φ r).const = r.b := rfl

theorem toLinCon_sat_iff (φ : Fin (m + 1)) (r : Row (m + 1)) (z : Fin (m + 1) → ℝ) :
    (toLinCon φ r).Sat z ↔ r.SatR (z ∘ pos φ) := by
  unfold LinCon.Sat LinCon.eval Row.SatR
  rw [toLinCon_strict]
  simp only [Bool.false_eq_true, if_false, toLinCon_const, Function.comp]
  have : ∑ i : Fin (m + 1), (((toLinCon φ r).coeffs.getD (i : ℕ) 0 : ℚ) : ℝ) * z i =
      ∑ i, (r.a i : ℝ) * z (pos φ i) := by
    simp_rw [toLinCon_coeff]
    rw [← Equiv.sum_comp (pos φ) (fun i => (r.a i : ℝ) * z (pos φ i))]
    apply Finset.sum_congr rfl
    intro k _
    rw [pos_pos]
  rw [this]

/-- The cube rows over `n` coordinates. -/
def cubeRows (n : ℕ) : List (Row n) := (List.finRange n).flatMap fun i => [cubeUpper i, cubeLower i]

lemma cubeUpper_satR_iff {n : ℕ} (i : Fin n) (x : Fin n → ℝ) : (cubeUpper i).SatR x ↔ x i ≤ 1 := by
  unfold cubeUpper
  rw [single_satR]
  simp

lemma cubeLower_satR_iff {n : ℕ} (i : Fin n) (x : Fin n → ℝ) : (cubeLower i).SatR x ↔ 0 ≤ x i := by
  unfold cubeLower
  rw [single_satR]
  push_cast
  constructor <;> intro h <;> linarith

lemma cubeRows_satR_iff {n : ℕ} (x : Fin n → ℝ) :
    (∀ r ∈ cubeRows n, r.SatR x) ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  unfold cubeRows
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.not_mem_nil,
    or_false]
  constructor
  · intro h i
    exact ⟨(cubeLower_satR_iff i x).1 (h _ ⟨i, Or.inr rfl⟩),
      (cubeUpper_satR_iff i x).1 (h _ ⟨i, Or.inl rfl⟩)⟩
  · rintro h r ⟨i, rfl | rfl⟩
    · exact (cubeUpper_satR_iff i x).2 (h i).2
    · exact (cubeLower_satR_iff i x).2 (h i).1

/-- The elimination system of a bundle: cube rows and bundle rows, `φ` at position `0`. -/
def system {Q : Type*} (φ : Fin (m + 1)) (B : Bundle Q (m + 1)) : List LinCon :=
  (cubeRows (m + 1) ++ B.map CitedRow.row).map (toLinCon φ)

theorem system_sat_iff {Q : Type*} (φ : Fin (m + 1)) (B : Bundle Q (m + 1)) (z : Fin (m + 1) → ℝ) :
    Sat (system φ B) z ↔ B.RegionR (z ∘ pos φ) := by
  unfold Sat system Bundle.RegionR
  simp only [List.mem_map, List.mem_append, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  simp only [toLinCon_sat_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact (cubeRows_satR_iff _).1 fun r hr => h r (Or.inl hr)
    · intro c hc; exact h c.row (Or.inr ⟨c, hc, rfl⟩)
  · rintro ⟨hcube, hrows⟩ r (hr | ⟨c, hc, rfl⟩)
    · exact (cubeRows_satR_iff _).2 hcube r hr
    · exact hrows c hc

/-- Eliminate the last `n` coordinates of a system over `n + 1` coordinates, leaving
position `0`. -/
def project : (n : ℕ) → List LinCon → List LinCon
  | 0, cs => cs
  | n + 1, cs => project n (elim (n + 1) cs)

/-- **Projection onto position `0`.**  Iterated elimination computes exactly the
projection of the solution set onto the first coordinate. -/
theorem project_sat_iff : ∀ (n : ℕ) (cs : List LinCon) (y : Fin 1 → ℝ),
    Sat (project n cs) y ↔ ∃ z : Fin (n + 1) → ℝ, Sat cs z ∧ z 0 = y 0
  | 0, cs, y => by
      constructor
      · intro h; exact ⟨y, h, rfl⟩
      · rintro ⟨z, hz, h0⟩
        have : z = y := funext fun i => by
          have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
          rw [hi]; exact h0
        rw [← this]; exact hz
  | n + 1, cs, y => by
      rw [show project (n + 1) cs = project n (elim (n + 1) cs) from rfl, project_sat_iff n]
      constructor
      · rintro ⟨z, hz, h0⟩
        obtain ⟨t, ht⟩ := (elim_sat_iff cs z).1 hz
        refine ⟨Fin.snoc z t, ht, ?_⟩
        rw [← h0, show (0 : Fin (n + 1 + 1)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
      · rintro ⟨z', hz', h0⟩
        refine ⟨Fin.init z', (elim_sat_iff cs _).2 ⟨z' (Fin.last _), by rwa [Fin.snoc_init_self]⟩, ?_⟩
        rw [← h0]
        rfl

lemma mem_elim_of_lastCoeff_zero {n : ℕ} {c : LinCon} {cs : List LinCon} (hc : c ∈ cs)
    (h0 : lastCoeff n c = 0) : c ∈ elim n cs := by
  unfold elim
  apply List.mem_append_left
  rw [List.mem_filter]
  exact ⟨hc, by simp [h0]⟩

lemma mem_project_of_zero {c : LinCon} {cs : List LinCon} (hc : c ∈ cs)
    (hz : ∀ n, 1 ≤ n → lastCoeff n c = 0) : ∀ k, c ∈ project k cs
  | 0 => hc
  | k + 1 => mem_project_of_zero (mem_elim_of_lastCoeff_zero hc (hz (k + 1) (by omega))) hz k

/-- All constraints non-strict. -/
def NonStrict (cs : List LinCon) : Prop := ∀ c ∈ cs, c.strict = false

lemma combine_strict (n : ℕ) (cl cu : LinCon) : (combine n cl cu).strict = (cl.strict || cu.strict) := rfl

lemma elim_nonStrict {n : ℕ} {cs : List LinCon} (h : NonStrict cs) : NonStrict (elim n cs) := by
  intro c hc
  unfold elim at hc
  rw [List.mem_append] at hc
  rcases hc with hc | hc
  · exact h c (List.mem_filter.1 hc).1
  · rw [List.mem_flatMap] at hc
    obtain ⟨cl, hcl, hc⟩ := hc
    rw [List.mem_map] at hc
    obtain ⟨cu, hcu, rfl⟩ := hc
    rw [combine_strict, h cl (List.mem_filter.1 hcl).1, h cu (List.mem_filter.1 hcu).1]
    rfl

lemma project_nonStrict {cs : List LinCon} (h : NonStrict cs) : ∀ k, NonStrict (project k cs)
  | 0 => h
  | k + 1 => project_nonStrict (elim_nonStrict h) k

/-- The coefficient at position `0`. -/
def c0 (c : LinCon) : ℚ := c.coeffs.getD 0 0

lemma eval_one (c : LinCon) (y : Fin 1 → ℝ) : c.eval y = (c0 c : ℝ) * y 0 := by
  simp [LinCon.eval, c0]

/-- The lower bounds a one-dimensional system places on position `0`. -/
def lowerList (cs : List LinCon) : List ℚ :=
  (cs.filter fun c => decide (c0 c < 0)).map fun c => c.const / c0 c

/-- The upper bounds. -/
def upperList (cs : List LinCon) : List ℚ :=
  (cs.filter fun c => decide (0 < c0 c)).map fun c => c.const / c0 c

/-- The lower endpoint. -/
def lo1 (cs : List LinCon) : ℚ := (lowerList cs).foldr max 0

/-- The upper endpoint. -/
def hi1 (cs : List LinCon) : ℚ := (upperList cs).foldr min 1

lemma le_cast_foldr_max {l : List ℚ} {a : ℚ} (h : a ∈ l) :
    (a : ℝ) ≤ ((l.foldr max 0 : ℚ) : ℝ) := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.foldr_cons, Rat.cast_max]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma cast_foldr_max_le {l : List ℚ} {b : ℝ} (h0 : 0 ≤ b) (h : ∀ a ∈ l, (a : ℝ) ≤ b) :
    ((l.foldr max 0 : ℚ) : ℝ) ≤ b := by
  induction l with
  | nil => simpa using h0
  | cons c l ih =>
    simp only [List.foldr_cons, Rat.cast_max]
    exact max_le (h c (List.mem_cons_self ..)) (ih fun a ha => h a (List.mem_cons_of_mem _ ha))

lemma cast_foldr_min_le {l : List ℚ} {a : ℚ} (h : a ∈ l) :
    ((l.foldr min 1 : ℚ) : ℝ) ≤ (a : ℝ) := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.foldr_cons, Rat.cast_min]
    rcases List.mem_cons.1 h with rfl | h
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih h)

lemma le_cast_foldr_min {l : List ℚ} {b : ℝ} (h1 : b ≤ 1) (h : ∀ a ∈ l, b ≤ (a : ℝ)) :
    b ≤ ((l.foldr min 1 : ℚ) : ℝ) := by
  induction l with
  | nil => simpa using h1
  | cons c l ih =>
    simp only [List.foldr_cons, Rat.cast_min]
    exact le_min (h c (List.mem_cons_self ..)) (ih fun a ha => h a (List.mem_cons_of_mem _ ha))

/-- A non-strict constraint at a one-dimensional point, by the sign of its coefficient. -/
lemma sat_one_iff {c : LinCon} (hns : c.strict = false) (y : Fin 1 → ℝ) :
    c.Sat y ↔ (c0 c : ℝ) * y 0 ≤ (c.const : ℝ) := by
  unfold LinCon.Sat
  rw [hns, eval_one]
  simp

/-- **The one-dimensional system is an interval.**  Under non-strictness and with the
two cube bounds present, its solutions are exactly `[lo1, hi1]` once feasible. -/
theorem sat1_iff {cs : List LinCon} (hns : NonStrict cs) (hl : (0 : ℚ) ∈ lowerList cs)
    (hu : (1 : ℚ) ∈ upperList cs) (y : Fin 1 → ℝ) :
    Sat cs y ↔ (∀ c ∈ cs, c0 c = 0 → (0 : ℝ) ≤ (c.const : ℝ)) ∧
      ((lo1 cs : ℚ) : ℝ) ≤ y 0 ∧ y 0 ≤ ((hi1 cs : ℚ) : ℝ) := by
  have hpt : ∀ c ∈ cs, c.Sat y ↔ (c0 c : ℝ) * y 0 ≤ (c.const : ℝ) :=
    fun c hc => sat_one_iff (hns c hc) y
  have hlow : ∀ c ∈ cs, c0 c < 0 → (c.Sat y ↔ ((c.const / c0 c : ℚ) : ℝ) ≤ y 0) := by
    intro c hc hneg
    rw [hpt c hc, Rat.cast_div]
    have : ((c0 c : ℚ) : ℝ) < 0 := by exact_mod_cast hneg
    rw [div_le_iff_of_neg this]
    constructor <;> intro h <;> linarith
  have hup : ∀ c ∈ cs, 0 < c0 c → (c.Sat y ↔ y 0 ≤ ((c.const / c0 c : ℚ) : ℝ)) := by
    intro c hc hpos
    rw [hpt c hc, Rat.cast_div]
    have : (0 : ℝ) < ((c0 c : ℚ) : ℝ) := by exact_mod_cast hpos
    rw [le_div_iff₀ this]
    constructor <;> intro h <;> linarith
  have hzero : ∀ c ∈ cs, c0 c = 0 → (c.Sat y ↔ (0 : ℝ) ≤ (c.const : ℝ)) := by
    intro c hc h0
    rw [hpt c hc, h0]
    simp
  -- membership in the bound lists
  have hmemL : ∀ b, b ∈ lowerList cs ↔ ∃ c ∈ cs, c0 c < 0 ∧ c.const / c0 c = b := by
    intro b
    unfold lowerList
    rw [List.mem_map]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [List.mem_filter, decide_eq_true_iff] at hc
      exact ⟨c, hc.1, hc.2, rfl⟩
    · rintro ⟨c, hc, hneg, rfl⟩
      exact ⟨c, List.mem_filter.2 ⟨hc, decide_eq_true hneg⟩, rfl⟩
  have hmemU : ∀ b, b ∈ upperList cs ↔ ∃ c ∈ cs, 0 < c0 c ∧ c.const / c0 c = b := by
    intro b
    unfold upperList
    rw [List.mem_map]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [List.mem_filter, decide_eq_true_iff] at hc
      exact ⟨c, hc.1, hc.2, rfl⟩
    · rintro ⟨c, hc, hpos, rfl⟩
      exact ⟨c, List.mem_filter.2 ⟨hc, decide_eq_true hpos⟩, rfl⟩
  constructor
  · intro h
    refine ⟨fun c hc h0 => (hzero c hc h0).1 (h c hc), ?_, ?_⟩
    · apply cast_foldr_max_le
      · obtain ⟨c, hc, hneg, hb⟩ := (hmemL 0).1 hl
        have := (hlow c hc hneg).1 (h c hc)
        rw [hb] at this
        simpa using this
      · intro b hb
        obtain ⟨c, hc, hneg, rfl⟩ := (hmemL b).1 hb
        exact (hlow c hc hneg).1 (h c hc)
    · apply le_cast_foldr_min
      · obtain ⟨c, hc, hpos, hb⟩ := (hmemU 1).1 hu
        have := (hup c hc hpos).1 (h c hc)
        rw [hb] at this
        simpa using this
      · intro b hb
        obtain ⟨c, hc, hpos, rfl⟩ := (hmemU b).1 hb
        exact (hup c hc hpos).1 (h c hc)
  · rintro ⟨hz, hlo, hhi⟩ c hc
    rcases lt_trichotomy (c0 c) 0 with hneg | h0 | hpos
    · rw [hlow c hc hneg]
      exact le_trans (le_cast_foldr_max ((hmemL _).2 ⟨c, hc, hneg, rfl⟩)) hlo
    · exact (hzero c hc h0).2 (hz c hc h0)
    · rw [hup c hc hpos]
      exact le_trans hhi (cast_foldr_min_le ((hmemU _).2 ⟨c, hc, hpos, rfl⟩))

/-- The endpoints of a feasible one-dimensional system are attained. -/
theorem endpoints_attained {cs : List LinCon} (hns : NonStrict cs) (hl : (0 : ℚ) ∈ lowerList cs)
    (hu : (1 : ℚ) ∈ upperList cs) (hfeas : ∃ y : Fin 1 → ℝ, Sat cs y) :
    Sat cs (fun _ : Fin 1 => ((lo1 cs : ℚ) : ℝ)) ∧ Sat cs (fun _ : Fin 1 => ((hi1 cs : ℚ) : ℝ)) := by
  obtain ⟨y, hy⟩ := hfeas
  obtain ⟨hz, hlo, hhi⟩ := (sat1_iff hns hl hu y).1 hy
  have hle : ((lo1 cs : ℚ) : ℝ) ≤ ((hi1 cs : ℚ) : ℝ) := le_trans hlo hhi
  constructor
  · exact (sat1_iff hns hl hu _).2 ⟨hz, le_refl _, hle⟩
  · exact (sat1_iff hns hl hu _).2 ⟨hz, hle, le_refl _⟩

/-- The cube rows of `φ` sit at position `0` and survive elimination. -/
lemma cube_phi_lastCoeff (φ : Fin (m + 1)) (r : Row (m + 1)) (hr : ∀ j, j ≠ φ → r.a j = 0)
    (n : ℕ) (hn : 1 ≤ n) : lastCoeff n (toLinCon φ r) = 0 := by
  unfold lastCoeff
  by_cases h : n < m + 1
  · have := toLinCon_coeff φ r ⟨n, h⟩
    simp only at this
    rw [this]
    apply hr
    intro heq
    have : pos φ (pos φ ⟨n, h⟩) = pos φ φ := by rw [heq]
    rw [pos_pos, pos_self] at this
    have := congrArg Fin.val this
    simp at this
    omega
  · exact toLinCon_coeff_ge φ r n (by omega)

lemma cube_phi_lower_mem {Q : Type*} (φ : Fin (m + 1)) (B : Bundle Q (m + 1)) :
    (0 : ℚ) ∈ lowerList (project m (system φ B)) := by
  unfold lowerList
  rw [List.mem_map]
  refine ⟨toLinCon φ (cubeLower φ), ?_, ?_⟩
  · rw [List.mem_filter]
    refine ⟨?_, ?_⟩
    · apply mem_project_of_zero
      · unfold system
        rw [List.mem_map]
        refine ⟨cubeLower φ, ?_, rfl⟩
        rw [List.mem_append]
        left
        unfold cubeRows
        simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
          List.not_mem_nil, or_false]
        exact ⟨φ, Or.inr rfl⟩
      · intro n hn
        apply cube_phi_lastCoeff
        · intro j hj; simp [cubeLower, hj]
        · exact hn
    · have : c0 (toLinCon φ (cubeLower φ)) = -1 := by
        unfold c0
        have := toLinCon_coeff φ (cubeLower φ) 0
        simp only [Fin.val_zero] at this
        rw [this, pos_zero]
        simp [cubeLower]
      simp [this]
  · unfold c0
    have := toLinCon_coeff φ (cubeLower φ) 0
    simp only [Fin.val_zero] at this
    rw [this, pos_zero]
    simp [cubeLower, toLinCon_const]

lemma cube_phi_upper_mem {Q : Type*} (φ : Fin (m + 1)) (B : Bundle Q (m + 1)) :
    (1 : ℚ) ∈ upperList (project m (system φ B)) := by
  unfold upperList
  rw [List.mem_map]
  refine ⟨toLinCon φ (cubeUpper φ), ?_, ?_⟩
  · rw [List.mem_filter]
    refine ⟨?_, ?_⟩
    · apply mem_project_of_zero
      · unfold system
        rw [List.mem_map]
        refine ⟨cubeUpper φ, ?_, rfl⟩
        rw [List.mem_append]
        left
        unfold cubeRows
        simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
          List.not_mem_nil, or_false]
        exact ⟨φ, Or.inl rfl⟩
      · intro n hn
        apply cube_phi_lastCoeff
        · intro j hj; simp [cubeUpper, hj]
        · exact hn
    · have : c0 (toLinCon φ (cubeUpper φ)) = 1 := by
        unfold c0
        have := toLinCon_coeff φ (cubeUpper φ) 0
        simp only [Fin.val_zero] at this
        rw [this, pos_zero]
        simp [cubeUpper]
      simp [this]
  · unfold c0
    have := toLinCon_coeff φ (cubeUpper φ) 0
    simp only [Fin.val_zero] at this
    rw [this, pos_zero]
    simp [cubeUpper, toLinCon_const]

lemma system_nonStrict {Q : Type*} (φ : Fin (m + 1)) (B : Bundle Q (m + 1)) :
    NonStrict (system φ B) := by
  intro c hc
  unfold system at hc
  rw [List.mem_map] at hc
  obtain ⟨r, _, rfl⟩ := hc
  rfl

/-- **The forced interval, computed**: eliminate every coordinate but `φ` from the forced
bundle's system and read the endpoints of the one-dimensional result. -/
def forcedInterval {A : Type*} (S : Seed (m + 1) A) (W : List (SubItem (m + 1))) (st : DocketState)
    (F : Settlement (m + 1)) (φ : Fin (m + 1)) : ℚ × ℚ :=
  let cs := project m (system φ (forcedBundle S W st F))
  (lo1 cs, hi1 cs)

/-- **Correctness of the computed interval.**  If the real forced region is nonempty, the
computed endpoints are valid bounds on `P(φ)` over it and both are attained. -/
theorem forcedInterval_spec {A : Type*} (S : Seed (m + 1) A) (W : List (SubItem (m + 1)))
    (st : DocketState) (F : Settlement (m + 1)) (φ : Fin (m + 1))
    (hne : ∃ x, forcedRegionR S W st F x) :
    (∀ x, forcedRegionR S W st F x →
      (((forcedInterval S W st F φ).1 : ℚ) : ℝ) ≤ x φ ∧
      x φ ≤ (((forcedInterval S W st F φ).2 : ℚ) : ℝ)) ∧
    (∃ x, forcedRegionR S W st F x ∧ x φ = (((forcedInterval S W st F φ).1 : ℚ) : ℝ)) ∧
    (∃ x, forcedRegionR S W st F x ∧ x φ = (((forcedInterval S W st F φ).2 : ℚ) : ℝ)) := by
  set B := forcedBundle S W st F with hB
  set cs := project m (system φ B) with hcs
  have hns : NonStrict cs := project_nonStrict (system_nonStrict φ B) m
  have hl := cube_phi_lower_mem φ B
  have hu := cube_phi_upper_mem φ B
  -- a real region point gives a projected point and back
  have fwd : ∀ x, forcedRegionR S W st F x → Sat cs (fun _ : Fin 1 => x φ) := by
    intro x hx
    rw [hcs, project_sat_iff]
    refine ⟨x ∘ pos φ, ?_, ?_⟩
    · rw [system_sat_iff]
      have : (x ∘ pos φ) ∘ pos φ = x := funext fun k => by simp [Function.comp, pos_pos]
      rw [this]; exact hx
    · simp [Function.comp, pos_zero]
  have bwd : ∀ y : Fin 1 → ℝ, Sat cs y → ∃ x, forcedRegionR S W st F x ∧ x φ = y 0 := by
    intro y hy
    rw [hcs, project_sat_iff] at hy
    obtain ⟨z, hz, h0⟩ := hy
    rw [system_sat_iff] at hz
    exact ⟨z ∘ pos φ, hz, by simp [Function.comp, pos_self, h0]⟩
  have hfeas : ∃ y : Fin 1 → ℝ, Sat cs y := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨_, fwd x hx⟩
  obtain ⟨hlo, hhi⟩ := endpoints_attained hns hl hu hfeas
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have := (sat1_iff hns hl hu _).1 (fwd x hx)
    exact ⟨this.2.1, this.2.2⟩
  · exact bwd _ hlo
  · exact bwd _ hhi

/-- The computed endpoints are valid bounds at rational points of the forced region. -/
theorem forcedInterval_bounds {A : Type*} (S : Seed (m + 1) A) (W : List (SubItem (m + 1)))
    (st : DocketState) (F : Settlement (m + 1)) (φ : Fin (m + 1))
    (hne : ∃ x, forcedRegionR S W st F x) :
    LowerBound S W st F φ (forcedInterval S W st F φ).1 ∧
    UpperBound S W st F φ (forcedInterval S W st F φ).2 := by
  obtain ⟨hb, -, -⟩ := forcedInterval_spec S W st F φ hne
  constructor
  · intro x hx
    have := (hb _ (forcedRegionR_of_forcedRegion S W st F hx)).1
    exact_mod_cast this
  · intro x hx
    have := (hb _ (forcedRegionR_of_forcedRegion S W st F hx)).2
    exact_mod_cast this

/-- **Monotonicity of the computed interval under settlement.** -/
theorem forcedInterval_mono {A : Type*} (S : Seed (m + 1) A) (W : List (SubItem (m + 1)))
    (st : DocketState) {F F' : Settlement (m + 1)} (h : F.le F') (φ : Fin (m + 1))
    (hne : ∃ x, forcedRegionR S W st F x) (hne' : ∃ x, forcedRegionR S W st F' x) :
    (forcedInterval S W st F φ).1 ≤ (forcedInterval S W st F' φ).1 ∧
    (forcedInterval S W st F' φ).2 ≤ (forcedInterval S W st F φ).2 := by
  obtain ⟨hb, -, -⟩ := forcedInterval_spec S W st F φ hne
  obtain ⟨-, ⟨x, hx, hxφ⟩, ⟨y, hy, hyφ⟩⟩ := forcedInterval_spec S W st F' φ hne'
  have h1 := (hb x (forcedRegionR_anti S W st h hx)).1
  have h2 := (hb y (forcedRegionR_anti S W st h hy)).2
  rw [hxφ] at h1
  rw [hyφ] at h2
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

end Elimination


/-! ## 8. Seed-independence -/

/-- The coherence rows `x 0 + x 1 = 1` over two coordinates read as `φ` and `¬φ`. -/
def negCoherence : List (StrItem 2) :=
  [⟨⟨![1, 1], 1⟩, StrKind.coherence, 0⟩, ⟨⟨![-1, -1], -1⟩, StrKind.coherence, 1⟩]

/-- The seed with two humble items: `P(φ) ≥ 1/2` and `P(¬φ) ≥ 1/2`. -/
def sandwichSeed : Seed 2 Unit :=
  ⟨[⟨Form.premise 0 (1/2), 0⟩, ⟨Form.premise 1 (1/2), 1⟩], negCoherence, ⟨∅, ∅⟩⟩

/-- The seed with no substantive item. -/
def emptySeed : Seed 2 Unit := ⟨[], negCoherence, ⟨∅, ∅⟩⟩

theorem sandwichSeed_humble : sandwichSeed.HumbleItems := by
  unfold Seed.HumbleItems sandwichSeed
  simp [Form.c]
  norm_num

/-- **C3 refuted under item-level humility.**  Both items of `sandwichSeed` are humble, its
structural layer is shared with `emptySeed`, the warrant set is empty; yet the sandwich
pins `P(φ) = 1/2` while the empty seed leaves `P(φ)` at both `0` and `1`. -/
theorem c3_refuted :
    sandwichSeed.HumbleItems ∧
    Pins sandwichSeed [] DocketState.quiet (Settlement.empty 2) 0 (1/2) ∧
    forcedRegion emptySeed [] DocketState.quiet (Settlement.empty 2) ![0, 1] ∧
    forcedRegion emptySeed [] DocketState.quiet (Settlement.empty 2) ![1, 0] := by
  refine ⟨sandwichSeed_humble, ?_, ?_, ?_⟩
  · intro x hx
    rw [forcedRegion_iff] at hx
    obtain ⟨-, -, hsub, hstr⟩ := hx
    have h0 := (Form.premise_sat_iff _ _ _).1
      (hsub ⟨Form.premise 0 (1/2), 0⟩ (by simp [sandwichSeed, Seed.liveSub, DocketState.quiet]))
    have h1 := (Form.premise_sat_iff _ _ _).1
      (hsub ⟨Form.premise 1 (1/2), 1⟩ (by simp [sandwichSeed, Seed.liveSub, DocketState.quiet]))
    have hc := hstr ⟨⟨![1, 1], 1⟩, StrKind.coherence, 0⟩
      (by simp [sandwichSeed, negCoherence, Seed.liveStr, DocketState.quiet])
    simp only [Row.Sat, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul] at hc
    linarith
  · rw [forcedRegion_iff]
    refine ⟨?_, Settlement.empty_pinned _, ?_, ?_⟩
    · intro i; fin_cases i <;> simp
    · intro it hit; simp [emptySeed, Seed.liveSub] at hit
    · intro it hit
      simp [emptySeed, negCoherence, Seed.liveStr, DocketState.quiet] at hit
      rcases hit with rfl | rfl <;> simp [Row.Sat, Fin.sum_univ_two]
  · rw [forcedRegion_iff]
    refine ⟨?_, Settlement.empty_pinned _, ?_, ?_⟩
    · intro i; fin_cases i <;> simp
    · intro it hit; simp [emptySeed, Seed.liveSub] at hit
    · intro it hit
      simp [emptySeed, negCoherence, Seed.liveStr, DocketState.quiet] at hit
      rcases hit with rfl | rfl <;> simp [Row.Sat, Fin.sum_univ_two]

/-- Strict satisfaction of a row at a real point: the open halfspace. -/
def StrictSatR (r : Row d) (x : Fin d → ℝ) : Prop := ∑ i, (r.a i : ℝ) * x i < (r.b : ℝ)

/-- The open layer cut out by a list of strict rows is open. -/
theorem isOpen_strictLayer (L : List (Row d)) : IsOpen {x : Fin d → ℝ | ∀ r ∈ L, StrictSatR r x} := by
  induction L with
  | nil => simp
  | cons r L ih =>
    have : {x : Fin d → ℝ | ∀ r' ∈ r :: L, StrictSatR r' x} =
        {x | StrictSatR r x} ∩ {x | ∀ r' ∈ L, StrictSatR r' x} := by
      ext x; simp
    rw [this]
    refine IsOpen.inter ?_ ih
    exact isOpen_lt (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))
      continuous_const

/-- The real region of a bundle is convex. -/
theorem regionR_convex {Q : Type*} (B : Bundle Q d) : Convex ℝ {x | B.RegionR x} := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro i
    have h1 := (hx.1 i).1
    have h2 := (hx.1 i).2
    have h3 := (hy.1 i).1
    have h4 := (hy.1 i).2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · positivity
    · nlinarith
  · intro c hc
    have hxr := hx.2 c hc
    have hyr := hy.2 c hc
    unfold Row.SatR at hxr hyr ⊢
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : ∑ i, (c.row.a i : ℝ) * (a * x i + b * y i) =
        a * ∑ i, (c.row.a i : ℝ) * x i + b * ∑ i, (c.row.a i : ℝ) * y i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [this]
    calc a * ∑ i, (c.row.a i : ℝ) * x i + b * ∑ i, (c.row.a i : ℝ) * y i
        ≤ a * c.row.b + b * c.row.b := by
          gcongr
      _ = c.row.b := by rw [← add_mul, hab, one_mul]

/-- **A point forced by a closed convex layer cut by an open layer is forced by the
closed layer alone.**  If `C ∩ U` is nonempty and every point of it has `x φ = p`, then
every point of `C` does. -/
theorem point_forced_of_open_layer {C U : Set (Fin d → ℝ)} (hC : Convex ℝ C) (hU : IsOpen U)
    (hne : (C ∩ U).Nonempty) (φ : Fin d) (p : ℝ) (hpt : ∀ x ∈ C ∩ U, x φ = p) :
    ∀ z ∈ C, z φ = p := by
  obtain ⟨y, hyC, hyU⟩ := hne
  intro z hz
  have hyp : y φ = p := hpt y ⟨hyC, hyU⟩
  let γ : ℝ → (Fin d → ℝ) := fun t => y + t • (z - y)
  have hγ : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hopen : IsOpen (γ ⁻¹' U) := hU.preimage hγ
  have h0 : (0 : ℝ) ∈ γ ⁻¹' U := by simp [γ, hyU]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen 0 h0
  set t : ℝ := min (ε / 2) 1 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := min_le_right _ _
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htU : γ t ∈ U := hball (by simp [abs_of_pos ht0, htε])
  have htC : γ t ∈ C := hC.add_smul_sub_mem hyC hz ⟨ht0.le, ht1⟩
  have hpt' := hpt (γ t) ⟨htC, htU⟩
  simp only [γ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hpt'
  have : t * (z φ - y φ) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h ht0.ne'
  · linarith

/-- **Seed-independence under strict humility (C3′).**  Two reasoners share a closed layer
`B` (structure, warrants, pins, cube) and carry substantive layers `L₁`, `L₂` of *strict*
rows.  If the first region is nonempty and pins `φ` to `p`, so does the second: the pin
belongs to the closed layer.  (An empty second region is refuted, not pinned; the
statement is vacuous there.) -/
theorem seed_independence_strict {Q : Type*} (B : Bundle Q d) (L₁ L₂ : List (Row d)) (φ : Fin d)
    (p : ℝ)
    (hne₁ : ∃ x, B.RegionR x ∧ ∀ r ∈ L₁, StrictSatR r x)
    (hpin : ∀ x, B.RegionR x → (∀ r ∈ L₁, StrictSatR r x) → x φ = p) :
    ∀ x, B.RegionR x → (∀ r ∈ L₂, StrictSatR r x) → x φ = p := by
  have hclosed : ∀ z ∈ {x | B.RegionR x}, z φ = p := by
    refine point_forced_of_open_layer (regionR_convex B) (isOpen_strictLayer L₁) ?_ φ p ?_
    · obtain ⟨x, hx, hl⟩ := hne₁; exact ⟨x, hx, hl⟩
    · rintro x ⟨hx, hl⟩; exact hpin x hx hl
  intro x hx _
  exact hclosed x hx

/-! ## 10. Stabilization -/

/-- A monotone sequence of pairs of finsets in finite types is eventually constant. -/
theorem eventually_const_of_monotone {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : ℕ → Finset ι) (hR : Monotone R) (F : ℕ → Finset κ) (hF : Monotone F) :
    ∃ N, ∀ n, N ≤ n → R n = R N ∧ F n = F N := by
  let c : ℕ → ℕ := fun n => (R n).card + (F n).card
  have hbdd : BddAbove (Set.range c) := by
    refine bddAbove_def.2 ⟨Fintype.card ι + Fintype.card κ, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact Nat.add_le_add (Finset.card_le_univ _) (Finset.card_le_univ _)
  have hmem := Nat.sSup_mem (s := Set.range c) ⟨c 0, 0, rfl⟩ hbdd
  obtain ⟨N, hN⟩ := hmem
  refine ⟨N, fun n hn => ?_⟩
  have hle : c n ≤ c N := by rw [hN]; exact le_csSup hbdd ⟨n, rfl⟩
  have hR' : R N ⊆ R n := hR hn
  have hF' : F N ⊆ F n := hF hn
  have hRc := Finset.card_le_card hR'
  have hFc := Finset.card_le_card hF'
  have hRe : (R n).card ≤ (R N).card := by
    simp only [c] at hle; omega
  have hFe : (F n).card ≤ (F N).card := by
    simp only [c] at hle; omega
  exact ⟨(Finset.eq_of_subset_of_card_le hR' hRe).symm,
    (Finset.eq_of_subset_of_card_le hF' hFe).symm⟩

/-- **Conditional stabilization (S1).**  Along a chain in which the raised subset of a
finite discovery class grows monotonically and settlement grows monotonically, any
quantity computed from the two — the forced interval of any `φ` — is eventually
constant. -/
theorem eventually_const_of_finite {ι : Type*} [Fintype ι] {α : Type*}
    (R : ℕ → Finset ι) (hR : Monotone R) (F : ℕ → Finset (Fin d)) (hF : Monotone F)
    (g : Finset ι → Finset (Fin d) → α) :
    ∃ N, ∀ n, N ≤ n → g (R n) (F n) = g (R N) (F N) := by
  obtain ⟨N, hN⟩ := eventually_const_of_monotone R hR F hF
  exact ⟨N, fun n hn => by rw [(hN n hn).1, (hN n hn).2]⟩

open Filter Topology in
/-- **Summable reopenings give convergence (S2).**  A real sequence bounded above whose
downward steps are summable converges. -/
theorem tendsto_of_summable_drops (l : ℕ → ℝ) (hb : ∀ n, l n ≤ 1)
    (hs : Summable fun n => max 0 (l n - l (n + 1))) : ∃ L, Tendsto l atTop (𝓝 L) := by
  let δ : ℕ → ℝ := fun n => max 0 (l n - l (n + 1))
  let D : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, δ k
  have hδ : ∀ n, 0 ≤ δ n := fun n => le_max_left _ _
  let u : ℕ → ℝ := fun n => l n + D n
  have hu : Monotone u := by
    refine monotone_nat_of_le_succ fun n => ?_
    simp only [u, D, Finset.sum_range_succ]
    have := le_max_right 0 (l n - l (n + 1))
    linarith
  have hub : BddAbove (Set.range u) := by
    refine bddAbove_def.2 ⟨1 + ∑' k, δ k, ?_⟩
    rintro _ ⟨n, rfl⟩
    have := hs.sum_le_tsum (Finset.range n) (fun k _ => hδ k)
    simp only [u, D]
    linarith [hb n]
  have hD : Tendsto D atTop (𝓝 (∑' k, δ k)) := hs.hasSum.tendsto_sum_nat
  refine ⟨(⨆ n, u n) - ∑' k, δ k, ?_⟩
  have := (tendsto_atTop_ciSup hu hub).sub hD
  refine this.congr fun n => ?_
  simp [u]

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.SeedStatics.truth
#print axioms Workspace.Normativity.Contrib.SeedStatics.Settlement
#print axioms Workspace.Normativity.Contrib.SeedStatics.Settlement.Pinned
#print axioms Workspace.Normativity.Contrib.SeedStatics.Settlement.le
#print axioms Workspace.Normativity.Contrib.SeedStatics.Settlement.empty
#print axioms Workspace.Normativity.Contrib.SeedStatics.Settlement.empty_pinned
#print axioms Workspace.Normativity.Contrib.SeedStatics.Settlement.le_refl
#print axioms Workspace.Normativity.Contrib.SeedStatics.Settlement.Pinned.mono
#print axioms Workspace.Normativity.Contrib.SeedStatics.Settlement.pinRowsAt
#print axioms Workspace.Normativity.Contrib.SeedStatics.Settlement.pinRows
#print axioms Workspace.Normativity.Contrib.SeedStatics.Settlement.pinRowsAt_sat_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.Settlement.pinRows_sat_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.Settlement.empty_pinRowsAt
#print axioms Workspace.Normativity.Contrib.SeedStatics.settledTerm
#print axioms Workspace.Normativity.Contrib.SeedStatics.specialize
#print axioms Workspace.Normativity.Contrib.SeedStatics.specialize_sat_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.Form
#print axioms Workspace.Normativity.Contrib.SeedStatics.Form.c
#print axioms Workspace.Normativity.Contrib.SeedStatics.Form.row
#print axioms Workspace.Normativity.Contrib.SeedStatics.Form.premise_sat_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.Form.applicability_sat_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.Form.strength_sat_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.SubItem
#print axioms Workspace.Normativity.Contrib.SeedStatics.StrKind
#print axioms Workspace.Normativity.Contrib.SeedStatics.StrItem
#print axioms Workspace.Normativity.Contrib.SeedStatics.Constitutive
#print axioms Workspace.Normativity.Contrib.SeedStatics.Seed
#print axioms Workspace.Normativity.Contrib.SeedStatics.Seed.HumbleItems
#print axioms Workspace.Normativity.Contrib.SeedStatics.DocketState
#print axioms Workspace.Normativity.Contrib.SeedStatics.DocketState.quiet
#print axioms Workspace.Normativity.Contrib.SeedStatics.Seed.liveSub
#print axioms Workspace.Normativity.Contrib.SeedStatics.Seed.liveStr
#print axioms Workspace.Normativity.Contrib.SeedStatics.Seed.liveStr_indep_defeat
#print axioms Workspace.Normativity.Contrib.SeedStatics.Seed.liveSub_indep_withdraw
#print axioms Workspace.Normativity.Contrib.SeedStatics.Cite
#print axioms Workspace.Normativity.Contrib.SeedStatics.pinCited
#print axioms Workspace.Normativity.Contrib.SeedStatics.forcedBundle
#print axioms Workspace.Normativity.Contrib.SeedStatics.forcedRegion
#print axioms Workspace.Normativity.Contrib.SeedStatics.forcedRegion_iff_check
#print axioms Workspace.Normativity.Contrib.SeedStatics.pinCited_sat_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.forcedRegion_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.forcedRegion_anti
#print axioms Workspace.Normativity.Contrib.SeedStatics.LowerBound
#print axioms Workspace.Normativity.Contrib.SeedStatics.UpperBound
#print axioms Workspace.Normativity.Contrib.SeedStatics.IsForcedInterval
#print axioms Workspace.Normativity.Contrib.SeedStatics.IsForcedInterval.le
#print axioms Workspace.Normativity.Contrib.SeedStatics.IsForcedInterval.unique
#print axioms Workspace.Normativity.Contrib.SeedStatics.IsForcedInterval.mono
#print axioms Workspace.Normativity.Contrib.SeedStatics.Pins
#print axioms Workspace.Normativity.Contrib.SeedStatics.Refuted
#print axioms Workspace.Normativity.Contrib.SeedStatics.leverage
#print axioms Workspace.Normativity.Contrib.SeedStatics.widenSeed
#print axioms Workspace.Normativity.Contrib.SeedStatics.defeat_widens
#print axioms Workspace.Normativity.Contrib.SeedStatics.allowed_sat
#print axioms Workspace.Normativity.Contrib.SeedStatics.BoundCert
#print axioms Workspace.Normativity.Contrib.SeedStatics.BoundCert.value
#print axioms Workspace.Normativity.Contrib.SeedStatics.BoundCert.sound_of_pos
#print axioms Workspace.Normativity.Contrib.SeedStatics.BoundCert.sound
#print axioms Workspace.Normativity.Contrib.SeedStatics.lowerCert_bound
#print axioms Workspace.Normativity.Contrib.SeedStatics.upperCert_bound
#print axioms Workspace.Normativity.Contrib.SeedStatics.SureLoss
#print axioms Workspace.Normativity.Contrib.SeedStatics.sureLoss_of_cert
#print axioms Workspace.Normativity.Contrib.SeedStatics.FarkasCert.support_sound
#print axioms Workspace.Normativity.Contrib.SeedStatics.MinimalInfeasible
#print axioms Workspace.Normativity.Contrib.SeedStatics.forcedRegionR
#print axioms Workspace.Normativity.Contrib.SeedStatics.sat_iff_satR
#print axioms Workspace.Normativity.Contrib.SeedStatics.single_satR
#print axioms Workspace.Normativity.Contrib.SeedStatics.forcedRegionR_of_forcedRegion
#print axioms Workspace.Normativity.Contrib.SeedStatics.Settlement.PinnedR
#print axioms Workspace.Normativity.Contrib.SeedStatics.Settlement.pinRowsAt_satR_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.pinCited_satR_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.specialize_satR_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.forcedRegionR_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.Settlement.PinnedR.mono
#print axioms Workspace.Normativity.Contrib.SeedStatics.forcedRegionR_anti
#print axioms Workspace.Normativity.Contrib.SeedStatics.pos
#print axioms Workspace.Normativity.Contrib.SeedStatics.pos_zero
#print axioms Workspace.Normativity.Contrib.SeedStatics.pos_self
#print axioms Workspace.Normativity.Contrib.SeedStatics.pos_pos
#print axioms Workspace.Normativity.Contrib.SeedStatics.toLinCon
#print axioms Workspace.Normativity.Contrib.SeedStatics.toLinCon_coeff
#print axioms Workspace.Normativity.Contrib.SeedStatics.toLinCon_coeff_ge
#print axioms Workspace.Normativity.Contrib.SeedStatics.toLinCon_strict
#print axioms Workspace.Normativity.Contrib.SeedStatics.toLinCon_const
#print axioms Workspace.Normativity.Contrib.SeedStatics.toLinCon_sat_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.cubeRows
#print axioms Workspace.Normativity.Contrib.SeedStatics.cubeUpper_satR_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.cubeLower_satR_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.cubeRows_satR_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.system
#print axioms Workspace.Normativity.Contrib.SeedStatics.system_sat_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.project
#print axioms Workspace.Normativity.Contrib.SeedStatics.project_sat_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.mem_elim_of_lastCoeff_zero
#print axioms Workspace.Normativity.Contrib.SeedStatics.mem_project_of_zero
#print axioms Workspace.Normativity.Contrib.SeedStatics.NonStrict
#print axioms Workspace.Normativity.Contrib.SeedStatics.combine_strict
#print axioms Workspace.Normativity.Contrib.SeedStatics.elim_nonStrict
#print axioms Workspace.Normativity.Contrib.SeedStatics.project_nonStrict
#print axioms Workspace.Normativity.Contrib.SeedStatics.c0
#print axioms Workspace.Normativity.Contrib.SeedStatics.eval_one
#print axioms Workspace.Normativity.Contrib.SeedStatics.lowerList
#print axioms Workspace.Normativity.Contrib.SeedStatics.upperList
#print axioms Workspace.Normativity.Contrib.SeedStatics.lo1
#print axioms Workspace.Normativity.Contrib.SeedStatics.hi1
#print axioms Workspace.Normativity.Contrib.SeedStatics.le_cast_foldr_max
#print axioms Workspace.Normativity.Contrib.SeedStatics.cast_foldr_max_le
#print axioms Workspace.Normativity.Contrib.SeedStatics.cast_foldr_min_le
#print axioms Workspace.Normativity.Contrib.SeedStatics.le_cast_foldr_min
#print axioms Workspace.Normativity.Contrib.SeedStatics.sat_one_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.sat1_iff
#print axioms Workspace.Normativity.Contrib.SeedStatics.endpoints_attained
#print axioms Workspace.Normativity.Contrib.SeedStatics.cube_phi_lastCoeff
#print axioms Workspace.Normativity.Contrib.SeedStatics.cube_phi_lower_mem
#print axioms Workspace.Normativity.Contrib.SeedStatics.cube_phi_upper_mem
#print axioms Workspace.Normativity.Contrib.SeedStatics.system_nonStrict
#print axioms Workspace.Normativity.Contrib.SeedStatics.forcedInterval
#print axioms Workspace.Normativity.Contrib.SeedStatics.forcedInterval_spec
#print axioms Workspace.Normativity.Contrib.SeedStatics.forcedInterval_bounds
#print axioms Workspace.Normativity.Contrib.SeedStatics.forcedInterval_mono
#print axioms Workspace.Normativity.Contrib.SeedStatics.negCoherence
#print axioms Workspace.Normativity.Contrib.SeedStatics.sandwichSeed
#print axioms Workspace.Normativity.Contrib.SeedStatics.emptySeed
#print axioms Workspace.Normativity.Contrib.SeedStatics.sandwichSeed_humble
#print axioms Workspace.Normativity.Contrib.SeedStatics.c3_refuted
#print axioms Workspace.Normativity.Contrib.SeedStatics.StrictSatR
#print axioms Workspace.Normativity.Contrib.SeedStatics.isOpen_strictLayer
#print axioms Workspace.Normativity.Contrib.SeedStatics.regionR_convex
#print axioms Workspace.Normativity.Contrib.SeedStatics.point_forced_of_open_layer
#print axioms Workspace.Normativity.Contrib.SeedStatics.seed_independence_strict
#print axioms Workspace.Normativity.Contrib.SeedStatics.eventually_const_of_monotone
#print axioms Workspace.Normativity.Contrib.SeedStatics.eventually_const_of_finite
#print axioms Workspace.Normativity.Contrib.SeedStatics.tendsto_of_summable_drops

end Workspace.Normativity.Contrib.SeedStatics
