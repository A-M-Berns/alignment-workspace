/-
# Warrant entitlement: the licence chain, the settlement fork, and the record

Round `projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/`.

Four parts.

0. **The seed statics, ported.**  The declarations this round consumes from the unmerged
   branch `round/2026-09-16-seed-statics` (`SeedStatics.lean`), against current `main`:
   `Settlement`, `specialize`, the three leverage `Form`s and `Form.row`, `SubItem`,
   `StrItem`, `Seed`, `DocketState`, the forced bundle and region
   (`forcedBundle`, `forcedRegion`, `forcedRegion_iff`), monotonicity under settlement and
   its failure under defeat (`forcedRegion_anti`, `defeat_widens`), forced intervals
   (`IsForcedInterval`), and bound certificates (`BoundCert`, `lowerCert_bound`,
   `upperCert_bound`).  Nothing from the branch's elimination, confinement,
   seed-independence or stabilization sections is ported.

1. **The licence chain (Part A).**  A warrant occurrence (`Occurrence`) is a `Form` with an
   identity, the applicability claim it cites, a source and a defeat set.  A verdict is a
   value for a coordinate.  `Admissible`: the forced region of the live grounds contains a
   point with that value.  `Supported`: a `VerdictCert` — two `BoundCert`s whose
   positive-multiplier rows are cited **by occurrence** into the live bundle, plus the two
   attained endpoints — brackets the verdict.  `Licensed`: `Supported` on the record's
   grounds, and the issuing event is one the record authorizes.  `licensed_supported`,
   `supported_admissible` (through rational convexity of `Bundle.Region`,
   `region_convex`).  The two converses fail: `Countermodel.admissible_not_supported`
   (a stale citation after defeat of one of two duplicating occurrences; the region is
   unchanged) and `Countermodel.supported_not_licensed` (an unauthorized selection
   inside a forced interval of positive width, an instance of
   `GateIsLegitimacy.tiebreak_transparency`: `Countermodel.selection_not_transparent`).

2. **The settlement fork (Part B).**  The enforcer is the force layer's compiled position
   on a date-indexed presentation (`warrantEnforcer`).  **The odds bankroll**
   (`netWorth_ge_neg_odds`): if at date `n` some live world clears every enforced row of
   every date `t ≤ n` with a surplus dominating every live world's deficit on that row by
   the factor `ρ`, then the enforcer's assessed net worth at every live world is at least
   `−3ρ` — the market maker's constant `1` plus the trading firm's floor `2`, times the
   odds.  Intensity, tolerance and the number of dates do not appear.  Composed with the
   conditional Normative Inductor theorem as `warrant_normative_inductor`, whose
   `liability` hypothesis is discharged by the construction.  The fixture `Fixture`:
   four sentences `X, X∧A, X∧A∧Y, Y`, one warrant with strengths `c_P, c_A, c_S ∈ (0,1)`,
   `X` settled at `n₁`, the applicability port defeated at `n₀`, `Y` settled by a declared
   evaluation at `n_E`; the bankroll is `3·max_j c_j/(1−c_j)` under every settlement
   semantics (`Fixture.liability`, `Fixture.liability_disagree`), and after the defeat
   of the applicability port a refutation of `Y` leaves a **nonempty region with no
   slack world** (`Fixture.orphan_region_nonempty`, `Fixture.orphan_no_slack`), the
   obstruction the round's `src/` exhibits a trader against.

3. **The record (Part C).**  `MarketRun`, `Record`, `trace`.  Prices are not in the
   record; the enforcer's position is.  `trace_not_injOn` and `trace_not_const` on the
   fixture, and `Licensed` is decidable from the record (`instance : Decidable`).

Every structure has a nonvacuity witness in `Witness`.  Names are provisional
(`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.NormativeInductionInterface
import Workspace.Deference.Contrib.GateIsLegitimacy
import Workspace.Deference.Contrib.ReasonMediatedAuthorship

namespace Workspace.Normativity.Contrib.WarrantEntitlement

open Workspace.Normativity.Contrib.NormativeInductorComposition
open Finset

variable {d : ℕ}

/-! ## Part 0 — the seed statics, ported -/

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
class of coordinates. -/
structure Constitutive (d : ℕ) (A : Type*) where
  standing : Finset A
  protectedClass : Finset (Fin d)

/-- A **seed**. -/
structure Seed (d : ℕ) (A : Type*) where
  sub : List (SubItem d)
  str : List (StrItem d)
  con : Constitutive d A

/-- The **docket state**: ports with a landed defeater, and structural ids withdrawn by
a surface-change occurrence. -/
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

/-- **The forced region, read on the unspecialized rows.** -/
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

/-- Defeat widening witness: one substantive item `P(0) ≥ 1/2` on one coordinate. -/
def widenSeed : Seed 1 Unit :=
  ⟨[⟨Form.premise 0 (1/2), 0⟩], [], ⟨∅, ∅⟩⟩

/-- **Defeat widens.**  With the quiet docket `1/2` is a valid lower bound; once port `0`
is defeated the point `0` lies in the region, so no positive lower bound is valid. -/
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

/-! ## Rational convexity of a bundle's region

The one fact about regions the licence chain needs beyond the port: a region is convex
over `ℚ`, so a value bracketed by two attained values is itself attained. -/

/-- The rational segment between two points. -/
def seg (x y : Fin d → ℚ) (t : ℚ) : Fin d → ℚ := fun i => (1 - t) * x i + t * y i

lemma Row.sat_seg {r : Row d} {x y : Fin d → ℚ} (hx : r.Sat x) (hy : r.Sat y) {t : ℚ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : r.Sat (seg x y t) := by
  unfold Row.Sat seg at *
  have : ∑ i, r.a i * ((1 - t) * x i + t * y i) =
      (1 - t) * ∑ i, r.a i * x i + t * ∑ i, r.a i * y i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  nlinarith

/-- **`Bundle.Region` is convex over `ℚ`.** -/
theorem region_convex {Q : Type*} {B : Bundle Q d} {x y : Fin d → ℚ} (hx : B.Region x)
    (hy : B.Region y) {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : B.Region (seg x y t) := by
  refine ⟨fun i => ?_, fun c hc => Row.sat_seg (hx.2 c hc) (hy.2 c hc) h0 h1⟩
  obtain ⟨hx0, hx1⟩ := hx.1 i
  obtain ⟨hy0, hy1⟩ := hy.1 i
  unfold seg
  constructor <;> nlinarith

/-- A value between two attained values of a coordinate is attained. -/
theorem region_attains_between {Q : Type*} {B : Bundle Q d} {φ : Fin d} {x y : Fin d → ℚ}
    (hx : B.Region x) (hy : B.Region y) {v : ℚ} (hxv : x φ ≤ v) (hvy : v ≤ y φ) :
    ∃ z, B.Region z ∧ z φ = v := by
  rcases eq_or_lt_of_le (hxv.trans hvy) with heq | hlt
  · exact ⟨x, hx, by linarith⟩
  · set t : ℚ := (v - x φ) / (y φ - x φ) with ht
    have hden : 0 < y φ - x φ := by linarith
    have h0 : 0 ≤ t := div_nonneg (by linarith) hden.le
    have h1 : t ≤ 1 := by
      rw [ht, div_le_one hden]; linarith
    refine ⟨seg x y t, region_convex hx hy h0 h1, ?_⟩
    unfold seg
    rw [ht]
    field_simp
    ring

/-! ## Part A — the typed warrant and the licence chain -/

/-- Where an occurrence's applicability claim comes from: another occurrence, a settled
coordinate, or nothing (a premise). -/
inductive Applicability (d : ℕ) where
  | occurrence (id : ℕ)
  | settled (i : Fin d)
  | none
  deriving DecidableEq

/-- Who entered the occurrence: a party, or a settlement event. -/
inductive Source where
  | party (p : ℕ)
  | settlement (event : ℕ)
  deriving DecidableEq

/-- **A warrant occurrence** (A1): a leverage form with an identity, the applicability
claim it cites, its source, and its defeat set — the occurrences which, if live, undercut
it.  Its docket port is its identity. -/
structure Occurrence (d : ℕ) where
  id : ℕ
  form : Form d
  cites : Applicability d
  source : Source
  defeaters : Finset ℕ
  deriving DecidableEq

/-- The substantive item an occurrence contributes: its form on its own port. -/
def Occurrence.toSub (o : Occurrence d) : SubItem d := ⟨o.form, o.id⟩

/-- **Grounds**: the occurrences admitted to the record. -/
abbrev Grounds (d : ℕ) := List (Occurrence d)

/-- The seed a set of grounds presents: its substantive items, no structural layer. -/
def Grounds.seed (G : Grounds d) : Seed d Unit := ⟨G.map Occurrence.toSub, [], ⟨∅, ∅⟩⟩

/-- The live bundle of grounds under a docket and a settlement. -/
def Grounds.bundle (G : Grounds d) (st : DocketState) (F : Settlement d) : Bundle (Cite d) d :=
  forcedBundle G.seed [] st F

/-- The region the live grounds force. -/
def Grounds.region (G : Grounds d) (st : DocketState) (F : Settlement d) (x : Fin d → ℚ) :
    Prop := forcedRegion G.seed [] st F x

instance (G : Grounds d) (st : DocketState) (F : Settlement d) (x : Fin d → ℚ) :
    Decidable (G.region st F x) := by unfold Grounds.region; infer_instance

/-- **The region of grounds, by occurrence**: the cube, the settlement's pins, and the row
of every occurrence whose port the docket has not defeated. -/
theorem Grounds.region_iff (G : Grounds d) (st : DocketState) (F : Settlement d)
    (x : Fin d → ℚ) :
    G.region st F x ↔
      InCube x ∧ F.Pinned x ∧ ∀ o ∈ G, o.id ∉ st.defeated → o.form.row.Sat x := by
  unfold Grounds.region
  rw [forcedRegion_iff]
  have hstr : G.seed.liveStr st = [] := rfl
  rw [hstr]
  simp only [List.not_mem_nil, false_implies, implies_true, and_true, List.append_nil,
    Grounds.seed, Seed.liveSub, List.mem_filter, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, hp, h⟩
    exact ⟨hc, hp, fun o ho hid => h o.toSub ⟨⟨o, ho, rfl⟩, hid⟩⟩
  · rintro ⟨hc, hp, h⟩
    refine ⟨hc, hp, ?_⟩
    rintro it ⟨⟨o, ho, rfl⟩, hport⟩
    exact h o ho hport

/-- The empty settlement has no pin rows. -/
@[simp] theorem Settlement.empty_pinRowsAt (i : Fin d) : (Settlement.empty d).pinRowsAt i = [] :=
  rfl

/-- **Membership in the live bundle, by occurrence**: a cited row is a live occurrence's
specialized row under that occurrence's citation, or a pin row under its coordinate. -/
theorem Grounds.mem_bundle_iff (G : Grounds d) (st : DocketState) (F : Settlement d)
    (c : CitedRow (Cite d) d) :
    c ∈ G.bundle st F ↔
      (∃ o ∈ G, o.id ∉ st.defeated ∧ c = ⟨Cite.sub o.id, specialize F o.form.row⟩) ∨
      (∃ i, ∃ r ∈ F.pinRowsAt i, c = ⟨Cite.settled i, r⟩) := by
  have hstr : G.seed.liveStr st = [] := rfl
  unfold Grounds.bundle forcedBundle
  rw [hstr]
  simp only [List.map_nil, List.append_nil, List.mem_append, List.mem_map, Grounds.seed,
    Seed.liveSub, List.mem_filter, decide_eq_true_eq, pinCited, List.mem_flatMap,
    List.mem_finRange, true_and]
  constructor
  · rintro (⟨it, ⟨⟨o, ho, rfl⟩, hport⟩, rfl⟩ | ⟨i, r, hr, rfl⟩)
    · exact Or.inl ⟨o, ho, hport, rfl⟩
    · exact Or.inr ⟨i, r, hr, rfl⟩
  · rintro (⟨o, ho, hport, rfl⟩ | ⟨i, r, hr, rfl⟩)
    · exact Or.inl ⟨o.toSub, ⟨⟨o, ho, rfl⟩, hport⟩, rfl⟩
    · exact Or.inr ⟨i, r, hr, rfl⟩

/-- **Admissible** (P1): the region compiled from the grounds contains the verdict — some
region point gives `φ` the value `v`. -/
def Admissible (G : Grounds d) (st : DocketState) (F : Settlement d) (φ : Fin d) (v : ℚ) :
    Prop := ∃ x, G.region st F x ∧ x φ = v

/-- **A verdict certificate**: a lower and an upper bound certificate, each row cited by
occurrence (or a pin, or a cube face), and the two endpoints with the region points that
attain them. -/
structure VerdictCert (d m m' : ℕ) (φ : Fin d) where
  lo : BoundCert d m φ (-1)
  hi : BoundCert d m' φ 1
  loCite : Fin m → Cite d
  hiCite : Fin m' → Cite d
  loPoint : Fin d → ℚ
  hiPoint : Fin d → ℚ

namespace VerdictCert

variable {m m' : ℕ} {φ : Fin d}

/-- Rows are determined by their data; equality is decidable coordinatewise. -/
instance rowDecEq : DecidableEq (Row d) := fun r s =>
  if h : r.a = s.a ∧ r.b = s.b then
    isTrue (by obtain ⟨a, b⟩ := r; obtain ⟨a', b'⟩ := s; simp only at h; rw [h.1, h.2])
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

instance citedRowDecEq {Q : Type*} [DecidableEq Q] : DecidableEq (CitedRow Q d) := fun r s =>
  if h : r.cites = s.cites ∧ r.row = s.row then
    isTrue (by obtain ⟨q, a⟩ := r; obtain ⟨q', a'⟩ := s; simp only at h; rw [h.1, h.2])
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

/-- A certificate row is admitted against a bundle under its citation: the cited row is in
the bundle, or the row is a cube face (which cites nothing). -/
def RowAdmitted {Q : Type*} (B : Bundle Q d) (q : Q) (r : Row d) : Prop :=
  (⟨q, r⟩ : CitedRow Q d) ∈ B ∨ (∃ i, r = cubeUpper i) ∨ (∃ i, r = cubeLower i)

instance {Q : Type*} [DecidableEq Q] (B : Bundle Q d) (q : Q) (r : Row d) :
    Decidable (RowAdmitted B q r) := by unfold RowAdmitted; infer_instance

theorem RowAdmitted.allowed {Q : Type*} {B : Bundle Q d} {q : Q} {r : Row d}
    (h : RowAdmitted B q r) : B.Allowed r := by
  rcases h with h | h | h
  · exact Or.inl ⟨_, h, rfl⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **Every positively weighted row names a live occurrence** (or a pin or a face). -/
def CitesLive (c : VerdictCert d m m' φ) (B : Bundle (Cite d) d) : Prop :=
  (∀ i, 0 < c.lo.mult i → RowAdmitted B (c.loCite i) (c.lo.row i)) ∧
  (∀ i, 0 < c.hi.mult i → RowAdmitted B (c.hiCite i) (c.hi.row i))

instance (c : VerdictCert d m m' φ) (B : Bundle (Cite d) d) : Decidable (c.CitesLive B) := by
  unfold CitesLive; infer_instance

end VerdictCert

/-- **Supported** (P1): the certificate's positively weighted rows are cited into the live
bundle, its endpoints bracket the verdict, and both endpoints are attained in the region. -/
def Supported {m m' : ℕ} (G : Grounds d) (st : DocketState) (F : Settlement d) (φ : Fin d)
    (v : ℚ) (c : VerdictCert d m m' φ) : Prop :=
  c.CitesLive (G.bundle st F) ∧
  -c.lo.value ≤ v ∧ v ≤ c.hi.value ∧
  (G.region st F c.loPoint ∧ c.loPoint φ = -c.lo.value) ∧
  (G.region st F c.hiPoint ∧ c.hiPoint φ = c.hi.value)

instance {m m' : ℕ} (G : Grounds d) (st : DocketState) (F : Settlement d) (φ : Fin d) (v : ℚ)
    (c : VerdictCert d m m' φ) : Decidable (Supported G st F φ v c) := by
  unfold Supported; infer_instance

/-- **The record at a step** (Part A's view of it): the admitted grounds, the docket, the
settlement, and the set of record events the record authorizes. -/
structure RecordState (d : ℕ) where
  grounds : Grounds d
  docket : DocketState
  settlement : Settlement d
  authorized : Finset ℕ

/-- **Licensed** (P1): supported on the record's live grounds, and the event that issued
and selected the certificate is one the record authorizes. -/
def Licensed {m m' : ℕ} (R : RecordState d) (φ : Fin d) (v : ℚ) (c : VerdictCert d m m' φ)
    (event : ℕ) : Prop :=
  Supported R.grounds R.docket R.settlement φ v c ∧ event ∈ R.authorized

instance {m m' : ℕ} (R : RecordState d) (φ : Fin d) (v : ℚ) (c : VerdictCert d m m' φ)
    (event : ℕ) : Decidable (Licensed R φ v c event) := by
  unfold Licensed; infer_instance

/-- **Licensed → Supported.** -/
theorem licensed_supported {m m' : ℕ} {R : RecordState d} {φ : Fin d} {v : ℚ}
    {c : VerdictCert d m m' φ} {event : ℕ} (h : Licensed R φ v c event) :
    Supported R.grounds R.docket R.settlement φ v c := h.1

/-- **Supported → Admissible**, by rational convexity. -/
theorem supported_admissible {m m' : ℕ} {G : Grounds d} {st : DocketState} {F : Settlement d}
    {φ : Fin d} {v : ℚ} {c : VerdictCert d m m' φ} (h : Supported G st F φ v c) :
    Admissible G st F φ v := by
  obtain ⟨_, hlo, hhi, ⟨hloR, hloφ⟩, ⟨hhiR, hhiφ⟩⟩ := h
  exact region_attains_between (B := G.bundle st F) hloR hhiR (by rw [hloφ]; exact hlo)
    (by rw [hhiφ]; exact hhi)

/-- **The chain.** -/
theorem licence_chain {m m' : ℕ} {R : RecordState d} {φ : Fin d} {v : ℚ}
    {c : VerdictCert d m m' φ} {event : ℕ} (h : Licensed R φ v c event) :
    Supported R.grounds R.docket R.settlement φ v c ∧
      Admissible R.grounds R.docket R.settlement φ v :=
  ⟨licensed_supported h, supported_admissible (licensed_supported h)⟩

/-- A supported verdict's certified endpoints are valid bounds on the region: the
certificate is not only cited but sound. -/
theorem Supported.valid {m m' : ℕ} {G : Grounds d} {st : DocketState} {F : Settlement d}
    {φ : Fin d} {v : ℚ} {c : VerdictCert d m m' φ} (h : Supported G st F φ v c) :
    (∀ x, G.region st F x → -c.lo.value ≤ x φ) ∧ (∀ x, G.region st F x → x φ ≤ c.hi.value) := by
  obtain ⟨⟨hlo, hhi⟩, _⟩ := h
  constructor
  · intro x hx
    have := c.lo.sound_of_pos x fun i hi => allowed_sat (hlo i hi).allowed hx
    linarith
  · intro x hx
    have := c.hi.sound_of_pos x fun i hi => allowed_sat (hhi i hi).allowed hx
    linarith







/-! ## Part A — the two countermodels -/

namespace Countermodel

/-- The one coordinate `φ = 0`. -/
abbrev φ : Fin 1 := 0

/-- Two distinct occurrences, each `P(φ) ≥ 1/2`, from two parties, citing nothing. -/
def r₁ : Occurrence 1 := ⟨1, Form.premise 0 (1/2), .none, .party 1, ∅⟩
def r₂ : Occurrence 1 := ⟨2, Form.premise 0 (1/2), .none, .party 2, ∅⟩

/-- The grounds: both occurrences. -/
def G : Grounds 1 := [r₁, r₂]

/-- The empty settlement on one coordinate. -/
def F : Settlement 1 := Settlement.empty 1

/-- The docket after defeat of `r₁`. -/
def stDefeat : DocketState := ⟨{1}, ∅⟩

/-- The common row both occurrences compile to, specialized by the empty settlement. -/
def premRow : Row 1 := specialize F (Form.premise 0 (1/2 : ℚ)).row

lemma premRow_sat_iff (x : Fin 1 → ℚ) : premRow.Sat x ↔ (1/2 : ℚ) ≤ x 0 := by
  rw [premRow, specialize_sat_iff F _ (Settlement.empty_pinned x)]
  exact Form.premise_sat_iff 0 (1/2) x

/-- **The region is unchanged by the defeat**: `r₂` supplies the same row. -/
theorem region_unchanged (x : Fin 1 → ℚ) :
    G.region DocketState.quiet F x ↔ G.region stDefeat F x := by
  unfold Grounds.region
  rw [forcedRegion_iff, forcedRegion_iff]
  simp [G, Grounds.seed, Seed.liveSub, Seed.liveStr, DocketState.quiet, stDefeat, r₁, r₂,
    Occurrence.toSub]

/-- Both regions are the interval `[1/2, 1]` on `φ`. -/
theorem region_iff (x : Fin 1 → ℚ) :
    G.region DocketState.quiet F x ↔ (1/2 : ℚ) ≤ x 0 ∧ x 0 ≤ 1 := by
  rw [Grounds.region_iff]
  have hr₁ : r₁.form.row.Sat x ↔ (1/2 : ℚ) ≤ x 0 := Form.premise_sat_iff 0 (1/2) x
  have hr₂ : r₂.form.row.Sat x ↔ (1/2 : ℚ) ≤ x 0 := Form.premise_sat_iff 0 (1/2) x
  constructor
  · rintro ⟨hc, -, h⟩
    exact ⟨hr₁.1 (h r₁ (by simp [G]) (by simp [DocketState.quiet])), (hc 0).2⟩
  · rintro ⟨hlo, hhi⟩
    refine ⟨fun i => ?_, Settlement.empty_pinned x, ?_⟩
    · have : i = 0 := Subsingleton.elim i 0
      subst this; constructor <;> linarith
    · intro o ho _
      simp only [G, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl
      · exact hr₁.2 hlo
      · exact hr₂.2 hlo

/-- The lower-bound certificate: multiplier `1` on the premise row. -/
def loCert : BoundCert 1 1 φ (-1) where
  mult := fun _ => 1
  row := fun _ => premRow
  mult_nonneg := fun _ => by norm_num
  coeff_sum := fun j => by
    have : j = 0 := Subsingleton.elim j 0
    subst this
    simp [premRow, specialize, F, Settlement.empty, Form.row]

/-- The upper-bound certificate: multiplier `1` on the cube face `x 0 ≤ 1`. -/
def hiCert : BoundCert 1 1 φ 1 where
  mult := fun _ => 1
  row := fun _ => cubeUpper 0
  mult_nonneg := fun _ => by norm_num
  coeff_sum := fun j => by
    have : j = 0 := Subsingleton.elim j 0
    subst this
    simp [cubeUpper]

lemma loCert_value : loCert.value = -(1/2 : ℚ) := by
  simp [BoundCert.value, loCert, premRow, specialize, F, Settlement.empty, Form.row,
    settledTerm]

lemma hiCert_value : hiCert.value = 1 := by
  simp [BoundCert.value, hiCert, cubeUpper]

/-- A verdict certificate citing occurrence `k` for its lower row. -/
def cert (k : ℕ) : VerdictCert 1 1 1 φ where
  lo := loCert
  hi := hiCert
  loCite := fun _ => Cite.sub k
  hiCite := fun _ => Cite.settled 0
  loPoint := fun _ => 1/2
  hiPoint := fun _ => 1

lemma loPoint_mem : G.region DocketState.quiet F (fun _ => 1/2) := by
  rw [region_iff]; norm_num

lemma hiPoint_mem : G.region DocketState.quiet F (fun _ => 1) := by
  rw [region_iff]; norm_num

lemma premRow_b : premRow.b = -(1/2 : ℚ) := by
  simp [premRow, specialize, F, Settlement.empty, Form.row, settledTerm]

lemma premRow_a : premRow.a = fun _ => -1 := by
  funext i
  have : i = 0 := Subsingleton.elim i 0
  subst this
  simp [premRow, specialize, F, Settlement.empty, Form.row]

lemma premRow_ne_cubeUpper (i : Fin 1) : premRow ≠ cubeUpper i := by
  intro h
  have := congrArg Row.b h
  rw [premRow_b] at this
  norm_num [cubeUpper] at this

lemma premRow_ne_cubeLower (i : Fin 1) : premRow ≠ cubeLower i := by
  intro h
  have := congrArg Row.b h
  rw [premRow_b] at this
  norm_num [cubeLower] at this

/-- The bundle on the quiet docket: both citations of the premise row, no pins. -/
lemma bundle_quiet :
    G.bundle DocketState.quiet F = [⟨Cite.sub 1, premRow⟩, ⟨Cite.sub 2, premRow⟩] := by
  simp [Grounds.bundle, forcedBundle, G, Grounds.seed, Seed.liveSub, Seed.liveStr,
    DocketState.quiet, r₁, r₂, Occurrence.toSub, pinCited, F, Settlement.empty,
    Settlement.pinRowsAt, premRow]

/-- The bundle after the defeat: only `r₂`'s citation survives. -/
lemma bundle_defeat : G.bundle stDefeat F = [⟨Cite.sub 2, premRow⟩] := by
  simp [Grounds.bundle, forcedBundle, G, Grounds.seed, Seed.liveSub, Seed.liveStr,
    stDefeat, r₁, r₂, Occurrence.toSub, pinCited, F, Settlement.empty,
    Settlement.pinRowsAt, premRow]

lemma cited_quiet (k : ℕ) (hk : k = 1 ∨ k = 2) :
    (cert k).CitesLive (G.bundle DocketState.quiet F) := by
  refine ⟨fun _ _ => Or.inl ?_, fun _ _ => Or.inr (Or.inl ⟨0, rfl⟩)⟩
  rw [bundle_quiet]
  rcases hk with rfl | rfl <;> simp [cert, loCert]

/-- **Supported on the quiet docket**, citing either occurrence, for any verdict in the
interval. -/
theorem supported_quiet (k : ℕ) (hk : k = 1 ∨ k = 2) (v : ℚ) (hlo : (1/2 : ℚ) ≤ v)
    (hhi : v ≤ 1) : Supported G DocketState.quiet F φ v (cert k) := by
  refine ⟨cited_quiet k hk, ?_, ?_, ⟨loPoint_mem, ?_⟩, ⟨hiPoint_mem, ?_⟩⟩
  · simp [cert, loCert_value]; linarith
  · simpa [cert, hiCert_value] using hhi
  · simp [cert, loCert_value]
  · simp [cert, hiCert_value]

/-- **After the defeat of `r₁`**, the certificate citing `r₁` is no longer supported: its
one positively weighted lower row is cited into a bundle that no longer carries that
citation, and the row is no cube face. -/
theorem stale_not_supported (v : ℚ) : ¬ Supported G stDefeat F φ v (cert 1) := by
  rintro ⟨⟨hlo, -⟩, -⟩
  have h := hlo 0 (by simp [cert, loCert])
  rw [bundle_defeat] at h
  rcases h with h | ⟨i, hi⟩ | ⟨i, hi⟩
  · simp [cert, loCert] at h
  · exact premRow_ne_cubeUpper i (by simpa [cert, loCert] using hi)
  · exact premRow_ne_cubeLower i (by simpa [cert, loCert] using hi)

/-- A fresh certificate citing the surviving `r₂` is supported after the defeat. -/
theorem fresh_supported (v : ℚ) (hlo : (1/2 : ℚ) ≤ v) (hhi : v ≤ 1) :
    Supported G stDefeat F φ v (cert 2) := by
  refine ⟨⟨fun _ _ => Or.inl ?_, fun _ _ => Or.inr (Or.inl ⟨0, rfl⟩)⟩, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [bundle_defeat]; simp [cert, loCert]
  · simp [cert, loCert_value]; linarith
  · simpa [cert, hiCert_value] using hhi
  · exact (region_unchanged _).1 loPoint_mem
  · simp [cert, loCert_value]
  · exact (region_unchanged _).1 hiPoint_mem
  · simp [cert, hiCert_value]

/-- **A3.  Admissible does not imply Supported**: after the defeat the verdict is still
admissible (the region did not move) while the certificate that cited the defeated
occurrence is not supported — and a certificate citing the survivor is. -/
theorem admissible_not_supported :
    Admissible G stDefeat F φ (1/2) ∧ ¬ Supported G stDefeat F φ (1/2) (cert 1) ∧
      Supported G stDefeat F φ (1/2) (cert 2) :=
  ⟨⟨fun _ => 1/2, (region_unchanged _).1 loPoint_mem, rfl⟩, stale_not_supported _,
    fresh_supported _ le_rfl (by norm_num)⟩

/-- The forced interval of the countermodel is `[1/2, 1]`, with positive width. -/
theorem forcedInterval : IsForcedInterval G.seed [] DocketState.quiet F φ (1/2) 1 :=
  ⟨fun x hx => ((region_iff x).1 hx).1, fun x hx => ((region_iff x).1 hx).2,
    ⟨fun _ => 1/2, loPoint_mem, rfl⟩, ⟨fun _ => 1, hiPoint_mem, rfl⟩⟩

/-! ### A4: two supported verdicts, one unauthorized selection -/

/-- The record whose event `7` is authorized. -/
def recordAuth : RecordState 1 := ⟨G, DocketState.quiet, F, {7}⟩

/-- The same record with no authorized event at that step. -/
def recordNoAuth : RecordState 1 := ⟨G, DocketState.quiet, F, ∅⟩

/-- **A4.  Supported does not imply Licensed.**  Two verdicts inside the forced interval,
both supported by the same cited certificate; the selection event is licensed on the
record that authorizes it and not on the record that does not. -/
theorem supported_not_licensed :
    Supported G DocketState.quiet F φ (2/3) (cert 1) ∧
    Supported G DocketState.quiet F φ (3/4) (cert 1) ∧
    Licensed recordAuth φ (2/3) (cert 1) 7 ∧
    ¬ Licensed recordNoAuth φ (3/4) (cert 1) 7 := by
  refine ⟨supported_quiet 1 (Or.inl rfl) _ (by norm_num) (by norm_num),
    supported_quiet 1 (Or.inl rfl) _ (by norm_num) (by norm_num),
    ⟨supported_quiet 1 (Or.inl rfl) _ (by norm_num) (by norm_num), by simp [recordAuth]⟩, ?_⟩
  rintro ⟨-, h⟩
  simp [recordNoAuth] at h

/-! The selection as a transparency failure, an instance of `tiebreak_transparency`:
two audited continuations enter the same declared inputs at the selection event, and the
advisor's contribution at that event differs — the verdict it pushed. -/

section Transparency

open Workspace.Deference.Contrib.GateIsLegitimacy

/-- The two parties. -/
inductive Party where
  | principal
  | advisor
  deriving DecidableEq

/-- The trace interface: the advisor enters the selected verdict at event `0`. -/
def interface : TraceInterface Bool Party ℚ where
  entriesAt r e := if e = 0 then [(Party.advisor, if r then 3/4 else 2/3)] else []
  agent := Party.advisor
  principal := Party.principal

/-- The frame: the audited class is both continuations; declared inputs are the same. -/
def frame : TFrame Bool Unit Bool Unit Bool ℚ where
  β q _ := q
  x _ _ := ()
  R ω := ω
  V ω _ := if ω then 3/4 else 2/3
  D := Set.univ

/-- **The selection is not transparent** at the selection event, whatever reference `κ`
is declared: `tiebreak_transparency` applied to the two continuations. -/
theorem selection_not_transparent (κ : Party → Unit → Unit → List ℚ) :
    ¬ TransparentAt interface frame κ 0 :=
  tiebreak_transparency (I := interface) (F := frame) Party.advisor (by decide) false true
    (Set.mem_univ _) (Set.mem_univ _) () rfl (by
      simp [interface, frame, sourced]
      norm_num)

end Transparency

end Countermodel

/-! ## Part B — the settlement fork: the odds bankroll -/

section Fork

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Workspace.Normativity.Contrib.EnforcementPreservation
open Workspace.Normativity.Contrib.EnforcementStrategy
open Workspace.Normativity.Contrib.TraderizedEnforcement

/-- **The warrant enforcer**: the force layer's compiled position on the date's
presentation.  It reads no price history beyond what its features read, so prefix
invariance is by definition. -/
def warrantEnforcer (sched : ℕ → Presentation) : AdaptiveTrader where
  action n _ := enforcementStrategy (sched n) n

/-- The realized enforcer plays exactly the compiled strategy. -/
lemma realizedEnforcer_strat (L : Assessment) (sched : ℕ → Presentation) (n : ℕ) :
    (realizedEnforcer L (warrantEnforcer sched)).strat n = enforcementStrategy (sched n) n :=
  rfl

/-- **The signed row gap** at a world: positive is a surplus (the world clears the row),
negative is a deficit (the row excludes the world). -/
noncomputable def rowGap (coords : Finset Sentence) (r : Row) (v : PCWorld) : ℚ :=
  pair coords r.coeff (ratPayout v) - r.rhs

/-- The units the enforcer holds on a row at a price: intensity times violation. -/
def rowUnits (pres : Presentation) (i : Fin pres.rows.length) (p : Sentence → ℚ) : ℚ :=
  pres.intensities i * pres.rowViolation i p

lemma rowUnits_nonneg (pres : Presentation) (i : Fin pres.rows.length) (p : Sentence → ℚ) :
    0 ≤ rowUnits pres i p :=
  mul_nonneg (pres.rowAt i).intensity_nonneg (violation_nonneg _ _ _ _)

/-- **The day's value, resolved**: the units-weighted signed gaps plus the
intensity-weighted squared violations. -/
theorem day_value_eq (L : Assessment) (sched : ℕ → Presentation) (n : ℕ) (v : PCWorld) :
    ((realizedEnforcer L (warrantEnforcer sched)).strat n).value
        (history L (warrantEnforcer sched)) v.payout =
      (((∑ i, rowUnits (sched n) i (quote L (warrantEnforcer sched) n) *
            rowGap (sched n).coords ((sched n).rowAt i) v) +
          ∑ i, (sched n).intensities i *
            (sched n).rowViolation i (quote L (warrantEnforcer sched) n) ^ 2 : ℚ) : ℝ) := by
  rw [realizedEnforcer_strat]
  have hpay : (fun φ => ((ratPayout v φ : ℚ) : ℝ)) = v.payout := by
    funext φ; exact (payout_eq_ratPayout v φ).symm
  have hval := value_enforcementStrategy (sched n) n (history L (warrantEnforcer sched))
    (quote L (warrantEnforcer sched)) (history_eq_quote_cast L _) (ratPayout v)
  rw [hpay] at hval
  rw [hval]
  congr 1
  rw [Presentation.compiledPosition, pair_position, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pair_sub]
  have hgap := violation_mul_gap (sched n).coords ((sched n).normals i) ((sched n).rhss i)
    (quote L (warrantEnforcer sched) n)
  simp only [rowUnits, rowGap, Presentation.rowViolation, Presentation.normals,
    Presentation.rhss] at hgap ⊢
  linear_combination ((sched n).intensities i) * hgap

/-- At a world, the day's value is at least the units-weighted signed gap. -/
theorem day_value_ge (L : Assessment) (sched : ℕ → Presentation) (n : ℕ) (v : PCWorld) :
    ((∑ i, rowUnits (sched n) i (quote L (warrantEnforcer sched) n) *
        rowGap (sched n).coords ((sched n).rowAt i) v : ℚ) : ℝ) ≤
      ((realizedEnforcer L (warrantEnforcer sched)).strat n).value
        (history L (warrantEnforcer sched)) v.payout := by
  rw [day_value_eq]
  have : 0 ≤ ∑ i, (sched n).intensities i *
      (sched n).rowViolation i (quote L (warrantEnforcer sched) n) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg ((sched n).rowAt i).intensity_nonneg (sq_nonneg _)
  exact_mod_cast le_add_of_nonneg_right this

/-- The units-weighted signed gap of one date at a world. -/
noncomputable def dayGap (L : Assessment) (sched : ℕ → Presentation) (v : PCWorld) (t : ℕ) : ℚ :=
  ∑ i, rowUnits (sched t) i (quote L (warrantEnforcer sched) t) *
    rowGap (sched t).coords ((sched t).rowAt i) v

/-- The slack mass through date `n`: the units-weighted surplus at the witness world. -/
noncomputable def slackMass (L : Assessment) (sched : ℕ → Presentation) (v' : PCWorld) (n : ℕ) :
    ℚ :=
  ∑ t ∈ Finset.range (n + 1), dayGap L sched v' t

/-- The witness world's net worth dominates the slack mass. -/
theorem slackMass_le_netWorth (L : Assessment) (sched : ℕ → Presentation) (v' : PCWorld)
    (n : ℕ) :
    ((slackMass L sched v' n : ℚ) : ℝ) ≤
      (realizedEnforcer L (warrantEnforcer sched)).netWorth (history L (warrantEnforcer sched))
        v' n := by
  unfold slackMass Trader.netWorth
  rw [Rat.cast_sum]
  exact Finset.sum_le_sum fun t _ => day_value_ge L sched t v'

/-- **The market's capital bounds the enforcer's assessed gain**: the market maker's
constant `1` plus the trading firm's floor `2`, at every live world. -/
theorem enforcer_netWorth_lt_three (L : Assessment) (E : AdaptiveTrader) (n : ℕ)
    (v : PCWorld) (hv : L.Live n v) :
    (realizedEnforcer L E).netWorth (history L E) v n < 3 := by
  have hmm : (realizedAggregate L E).netWorth (history L E) v n < 1 := by
    rw [history_eq_marketMakerHistory]
    exact marketMaker_netWorth_lt_one (realizedAggregate L E) v n
  have hfirm : -2 ≤ (realizedFirm L E).netWorth (history L E) v n := by
    rw [← tradingFirmTrader_quote_eq_realizedFirm]
    exact AssessmentFirm.tradingFirmTrader_netWorth_floor L (history L E) (history_range L E)
      (quote L E) (history_eq_quote_cast L E) n v hv
  have hsplit := realizedAggregate_netWorth L E n (history L E) v
  linarith

/-- **The odds bankroll.**  If at date `n` a live world `v'` clears every enforced row of
every date `t ≤ n` with a surplus dominating, by the factor `ρ`, the deficit of the live
world `w` on that row, then the enforcer's assessed net worth at `w` is at least `−3ρ`.
Intensity, tolerance, the number of rows and the number of dates do not appear. -/
theorem netWorth_ge_neg_odds (L : Assessment) (sched : ℕ → Presentation) (ρ : ℚ)
    (hρ : 0 ≤ ρ) (n : ℕ) (v' : PCWorld) (hv' : L.Live n v') (w : PCWorld)
    (hgap : ∀ t ≤ n, ∀ r ∈ (sched t).rows,
      -(rowGap (sched t).coords r w) ≤ ρ * rowGap (sched t).coords r v') :
    -(3 * (ρ : ℝ)) ≤
      (realizedEnforcer L (warrantEnforcer sched)).netWorth (history L (warrantEnforcer sched))
        w n := by
  have hS : ((slackMass L sched v' n : ℚ) : ℝ) < 3 :=
    lt_of_le_of_lt (slackMass_le_netWorth L sched v' n)
      (enforcer_netWorth_lt_three L (warrantEnforcer sched) n v' hv')
  -- each date: the deficit side is dominated by `ρ` times the surplus side
  have hday : ∀ t ≤ n, -((ρ : ℝ) * ((dayGap L sched v' t : ℚ) : ℝ)) ≤
      ((realizedEnforcer L (warrantEnforcer sched)).strat t).value
        (history L (warrantEnforcer sched)) w.payout := by
    intro t htn
    refine le_trans ?_ (day_value_ge L sched t w)
    have hq : -(ρ * dayGap L sched v' t) ≤ dayGap L sched w t := by
      unfold dayGap
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have hu := rowUnits_nonneg (sched t) i (quote L (warrantEnforcer sched) t)
      have hg := hgap t htn ((sched t).rowAt i) (List.get_mem _ _)
      nlinarith
    have hq' : ((-(ρ * dayGap L sched v' t) : ℚ) : ℝ) ≤ ((dayGap L sched w t : ℚ) : ℝ) := by
      exact_mod_cast hq
    push_cast at hq'
    exact hq'
  have hsum : ∑ t ∈ Finset.range (n + 1), -((ρ : ℝ) * ((dayGap L sched v' t : ℚ) : ℝ)) =
      -((ρ : ℝ) * ((slackMass L sched v' n : ℚ) : ℝ)) := by
    unfold slackMass
    rw [Rat.cast_sum, Finset.mul_sum, Finset.sum_neg_distrib]
  have hw : -((ρ : ℝ) * ((slackMass L sched v' n : ℚ) : ℝ)) ≤
      (realizedEnforcer L (warrantEnforcer sched)).netWorth
        (history L (warrantEnforcer sched)) w n := by
    unfold Trader.netWorth
    rw [← hsum]
    exact Finset.sum_le_sum fun t ht => hday t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))
  have hρS : (ρ : ℝ) * ((slackMass L sched v' n : ℚ) : ℝ) ≤ (ρ : ℝ) * 3 :=
    mul_le_mul_of_nonneg_left hS.le (by exact_mod_cast hρ)
  linarith

/-- **Liability discharged by the odds bankroll**: a slack witness at every date gives the
`liability` hypothesis of `conditional_normative_inductor` with `B = 3ρ`. -/
theorem liability_of_odds (L : Assessment) (sched : ℕ → Presentation) (ρ : ℚ) (hρ : 0 ≤ ρ)
    (hslack : ∀ n, ∃ v' : PCWorld, L.Live n v' ∧ ∀ w : PCWorld, L.Live n w →
      ∀ t ≤ n, ∀ r ∈ (sched t).rows,
        -(rowGap (sched t).coords r w) ≤ ρ * rowGap (sched t).coords r v') :
    ∀ n (v : PCWorld), L.Live n v →
      -(3 * (ρ : ℝ)) ≤
        (realizedEnforcer L (warrantEnforcer sched)).netWorth
          (history L (warrantEnforcer sched)) v n := by
  intro n v hv
  obtain ⟨v', hv', hgap⟩ := hslack n
  exact netWorth_ge_neg_odds L sched ρ hρ n v' hv' v (hgap v hv)

open Workspace.Normativity.Contrib.NormativeInductionInterface in
open Workspace.Normativity.Contrib.OccurrenceIntegrity (Protocol) in
open Workspace.Normativity.Contrib.OpenIntegrityEvolution (ObligationState) in
/-- **The warrant Normative Inductor.**  `conditional_normative_inductor` at the warrant
enforcer, its `liability` hypothesis discharged by the odds bankroll; the computable-market
and uptake hypotheses are the theorem's own. -/
theorem warrant_normative_inductor {Occ Req Service : Type*} {S : Protocol Occ Req}
    {anchor : Occ → Req} {O : ObligationState S anchor} (E : Evaluation O Service)
    (L : Assessment) (sched : ℕ → Presentation) (ρ : ℚ) (hρ : 0 ≤ ρ)
    (hslack : ∀ n, ∃ v' : PCWorld, L.Live n v' ∧ ∀ w : PCWorld, L.Live n w →
      ∀ t ≤ n, ∀ r ∈ (sched t).rows,
        -(rowGap (sched t).coords r w) ≤ ρ * rowGap (sched t).coords r v')
    (computableMarket : ComputableMarket (history L (warrantEnforcer sched)))
    (cert : E.PracticalUptake (history L (warrantEnforcer sched))) :
    L.IsLogicalInductor (history L (warrantEnforcer sched)) ∧
    (0 ≤ E.residual ∧ E.residual ≤ 1) ∧
    E.progress (history L (warrantEnforcer sched)) ≤ E.modulus + E.error + E.D * E.residual :=
  E.conditional_normative_inductor L (warrantEnforcer sched) (3 * (ρ : ℝ))
    (liability_of_odds L sched ρ hρ hslack) computableMarket cert

/-- **World-inclusive rows cost nothing**: when every row's gap at a world is nonnegative
at every date through `n`, the enforcer's net worth there is nonnegative — the deductive
case's `B = 0`, recovered as `ρ = 0`. -/
theorem netWorth_nonneg_of_inclusive (L : Assessment) (sched : ℕ → Presentation) (n : ℕ)
    (w : PCWorld) (hw : ∀ t ≤ n, ∀ r ∈ (sched t).rows, 0 ≤ rowGap (sched t).coords r w) :
    0 ≤ (realizedEnforcer L (warrantEnforcer sched)).netWorth
      (history L (warrantEnforcer sched)) w n := by
  unfold Trader.netWorth
  refine Finset.sum_nonneg fun t ht => ?_
  have htn : t ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  refine le_trans ?_ (day_value_ge L sched t w)
  have : 0 ≤ ∑ i, rowUnits (sched t) i (quote L (warrantEnforcer sched) t) *
      rowGap (sched t).coords ((sched t).rowAt i) w :=
    Finset.sum_nonneg fun i _ => mul_nonneg (rowUnits_nonneg _ _ _)
      (hw t htn _ (List.get_mem _ _))
  exact_mod_cast this

/-- A date with no rows trades nothing. -/
theorem day_value_eq_zero_of_rows_nil (L : Assessment) (sched : ℕ → Presentation) (t : ℕ)
    (h : (sched t).rows = []) (v : PCWorld) :
    ((realizedEnforcer L (warrantEnforcer sched)).strat t).value
      (history L (warrantEnforcer sched)) v.payout = 0 := by
  rw [day_value_eq]
  have hempty : IsEmpty (Fin (sched t).rows.length) := by
    rw [h]; exact Fin.isEmpty'
  simp

/-- **Frozen tail**: a trader that trades nothing after date `m` has at every later date the
net worth it had at `m`. -/
theorem netWorth_eq_of_tail_zero (Tr : Trader) (P : History) (v : PCWorld) {m n : ℕ}
    (hmn : m ≤ n) (hz : ∀ t, m < t → (Tr.strat t).value P v.payout = 0) :
    Tr.netWorth P v n = Tr.netWorth P v m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Nat.add_succ, Trader.netWorth, Finset.sum_range_succ, ← Trader.netWorth,
        ih (by omega), hz _ (by omega), add_zero]

/-- `ofDeductiveProcess` is globally nested. -/
theorem ofDeductiveProcess_nested (DP : DeductiveProcess) {m n : ℕ} (h : m ≤ n) (v : PCWorld)
    (hv : (ofDeductiveProcess DP).Live n v) : (ofDeductiveProcess DP).Live m v := by
  intro φ hφ
  have hmono : ∀ k, DP.D m ⊆ DP.D (m + k) := by
    intro k
    induction k with
    | zero => exact fun _ h => h
    | succ k ih => exact fun x hx => DP.mono (m + k) (ih hx)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact hv φ (hmono k hφ)

end Fork

/-! ## Part B — the fixture -/

namespace Fixture

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Workspace.Normativity.Contrib.EnforcementPreservation
open Workspace.Normativity.Contrib.EnforcementStrategy
open Workspace.Normativity.Contrib.TraderizedEnforcement

/-- The three atoms. -/
def X : Sentence := .atom 0
def A : Sentence := .atom 1
def Y : Sentence := .atom 2
/-- `X ∧ A`. -/
def XA : Sentence := X ⋏ A
/-- `X ∧ A ∧ Y`, associated `(X ∧ A) ∧ Y`. -/
def XAY : Sentence := XA ⋏ Y
/-- `¬Y`. -/
def negY : Sentence := ∼Y

@[simp] lemma X_ne_XA : X ≠ XA := by simp [X, XA]
@[simp] lemma X_ne_XAY : X ≠ XAY := by simp [X, XAY, XA]
@[simp] lemma X_ne_Y : X ≠ Y := by simp [X, Y]
@[simp] lemma XA_ne_X : XA ≠ X := by simp [X, XA]
@[simp] lemma XA_ne_XAY : XA ≠ XAY := by intro h; cases h
@[simp] lemma XA_ne_Y : XA ≠ Y := by simp [XA, Y]
@[simp] lemma XAY_ne_X : XAY ≠ X := by simp [X, XAY, XA]
@[simp] lemma XAY_ne_XA : XAY ≠ XA := by intro h; cases h
@[simp] lemma XAY_ne_Y : XAY ≠ Y := by simp [XAY, Y]
@[simp] lemma Y_ne_X : Y ≠ X := by simp [X, Y]
@[simp] lemma Y_ne_XA : Y ≠ XA := by simp [XA, Y]
@[simp] lemma Y_ne_XAY : Y ≠ XAY := by simp [XAY, Y]

lemma holds_XA (v : PCWorld) : v.Holds XA ↔ v.Holds X ∧ v.Holds A := Iff.rfl
lemma holds_XAY (v : PCWorld) : v.Holds XAY ↔ v.Holds XA ∧ v.Holds Y := Iff.rfl
lemma holds_negY (v : PCWorld) : v.Holds negY ↔ ¬ v.Holds Y := by
  show LO.Propositional.Formula.Boolean.val v (∼Y) ↔ ¬ _
  simp [LO.Propositional.Formula.Boolean.val, PCWorld.Holds]

/-- The priced fragment. -/
def coordList : List Sentence := [X, XA, XAY, Y]

lemma coordList_nodup : coordList.Nodup := by simp [coordList]

/-- The coordinate map from the seed's four coordinates to the fragment. -/
def ι : Fin 4 → Sentence := ![X, XA, XAY, Y]

@[simp] lemma ι_zero : ι 0 = X := rfl
@[simp] lemma ι_one : ι 1 = XA := rfl
@[simp] lemma ι_two : ι 2 = XAY := rfl
@[simp] lemma ι_three : ι 3 = Y := rfl

/-- **The bridge from a seed row to a force row.**  A seed row `a · x ≤ b` on `Fin d`
coordinates becomes the force row `⟨coeff, P⟩ ≥ −b` with `coeff φ = −Σ_{j : ι j = φ} a j`,
at a declared intensity. -/
def toForceRow {d : ℕ} (ι : Fin d → Sentence) (β : ℚ) (hβ : 0 ≤ β) (r : Row d) : Row where
  coeff φ := ∑ j, if ι j = φ then -r.a j else 0
  rhs := -r.b
  intensity := β
  intensity_nonneg := hβ

/-- The bridge's pairing: on a coordinate set containing the image, the force row's pairing
is the negated seed row's left-hand side. -/
theorem toForceRow_pair {d : ℕ} (ι : Fin d → Sentence) (β : ℚ) (hβ : 0 ≤ β) (r : Row d)
    (coords : Finset Sentence) (hι : ∀ j, ι j ∈ coords) (w : Sentence → ℚ) :
    pair coords (toForceRow ι β hβ r).coeff w = -∑ j, r.a j * w (ι j) := by
  unfold pair toForceRow
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq coords (ι j), if_pos (hι j)]
  ring

/-- The bridge's gap at a world: how far the world clears the seed row. -/
theorem toForceRow_gap {d : ℕ} (ι : Fin d → Sentence) (β : ℚ) (hβ : 0 ≤ β) (r : Row d)
    (coords : Finset Sentence) (hι : ∀ j, ι j ∈ coords) (v : PCWorld) :
    rowGap coords (toForceRow ι β hβ r) v = r.b - ∑ j, r.a j * ratPayout v (ι j) := by
  unfold rowGap
  rw [toForceRow_pair ι β hβ r coords hι]
  simp [toForceRow]
  ring

/-- The strengths. -/
structure Strengths where
  P : ℚ
  A : ℚ
  S : ℚ
  P_pos : 0 < P
  P_lt : P < 1
  A_pos : 0 < A
  A_lt : A < 1
  S_pos : 0 < S
  S_lt : S < 1

/-- The three rows of the warrant, through the bridge. -/
def premiseRow (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) : Row :=
  toForceRow ι β hβ (Form.premise 0 c.P).row
def applRow (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) : Row :=
  toForceRow ι β hβ (Form.applicability 0 1 c.A).row
def strengthRow (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) : Row :=
  toForceRow ι β hβ (Form.strength 1 2 c.S).row

/-- The live rows at date `n` when the applicability port is defeated from `n₀`. -/
def rowsAt (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ n : ℕ) : List Row :=
  premiseRow c β hβ :: ((if n < n₀ then [applRow c β hβ] else []) ++ [strengthRow c β hβ])

/-- A presentation on the fragment with the given rows. -/
def pres (rows : List Row) : Presentation := ⟨coordList, coordList_nodup, rows⟩

@[simp] lemma pres_rows (rows : List Row) : (pres rows).rows = rows := rfl

lemma ι_mem_coords (j : Fin 4) : ι j ∈ (pres []).coords := by
  fin_cases j <;> simp [Presentation.coords, pres, coordList, ι]

/-- The schedule with every row live (no withholding). -/
def schedLive (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ : ℕ) : ℕ → Presentation :=
  fun n => pres (rowsAt c β hβ n₀ n)

/-- The schedule withholding force from `nE` on. -/
def schedWithheld (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ nE : ℕ) : ℕ → Presentation :=
  fun n => pres (if n < nE then rowsAt c β hβ n₀ n else [])

/-- **The settlement process**: `X` from `n₁`, and from `nE` the declared evaluation of
`Y` — `Y` itself if `e`, `¬Y` otherwise.  Deductive settlement and evaluation settlement
enter here in the same way: as members of the stage. -/
def stage (n₁ nE : ℕ) (e : Bool) (n : ℕ) : Finset Sentence :=
  (if n₁ ≤ n then {X} else ∅) ∪ (if nE ≤ n then {if e then Y else negY} else ∅)

lemma mem_stage (n₁ nE : ℕ) (e : Bool) (n : ℕ) (φ : Sentence) :
    φ ∈ stage n₁ nE e n ↔ (n₁ ≤ n ∧ φ = X) ∨ (nE ≤ n ∧ φ = (if e then Y else negY)) := by
  unfold stage
  by_cases h₁ : n₁ ≤ n <;> by_cases h₂ : nE ≤ n <;> simp [h₁, h₂]

lemma stage_mono (n₁ nE : ℕ) (e : Bool) (n : ℕ) : stage n₁ nE e n ⊆ stage n₁ nE e (n + 1) := by
  intro φ hφ
  rw [mem_stage] at hφ ⊢
  rcases hφ with ⟨h, hφ⟩ | ⟨h, hφ⟩
  · exact Or.inl ⟨by omega, hφ⟩
  · exact Or.inr ⟨by omega, hφ⟩

/-- The deductive process of the fixture. -/
def dp (n₁ nE : ℕ) (e : Bool) : DeductiveProcess where
  D := stage n₁ nE e
  mono := stage_mono n₁ nE e

/-- The fixture's assessment process. -/
def L (n₁ nE : ℕ) (e : Bool) : Assessment := ofDeductiveProcess (dp n₁ nE e)

lemma live_iff (n₁ nE : ℕ) (e : Bool) (n : ℕ) (v : PCWorld) :
    (L n₁ nE e).Live n v ↔
      (n₁ ≤ n → v.Holds X) ∧ (nE ≤ n → v.Holds (if e then Y else negY)) := by
  show v.ConsistentWith (stage n₁ nE e n) ↔ _
  unfold PCWorld.ConsistentWith
  constructor
  · intro h
    exact ⟨fun h₁ => h X ((mem_stage _ _ _ _ _).2 (Or.inl ⟨h₁, rfl⟩)),
      fun h₂ => h _ ((mem_stage _ _ _ _ _).2 (Or.inr ⟨h₂, rfl⟩))⟩
  · rintro ⟨h₁, h₂⟩ φ hφ
    rcases (mem_stage _ _ _ _ _).1 hφ with ⟨hn, rfl⟩ | ⟨hn, rfl⟩
    · exact h₁ hn
    · exact h₂ hn

/-- The all-true world is live whenever the evaluation affirms `Y`. -/
lemma allTrue_live (n₁ nE : ℕ) (n : ℕ) : (L n₁ nE true).Live n allTrue := by
  rw [live_iff]
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-- The all-true world is live before the evaluation, whatever it says. -/
lemma allTrue_live_before (n₁ nE : ℕ) (e : Bool) (n : ℕ) (hn : n < nE) :
    (L n₁ nE e).Live n allTrue := by
  rw [live_iff]
  exact ⟨fun _ => trivial, fun h => absurd h (by omega)⟩

/-! ### The gaps -/

open Classical in
lemma ratPayout_X (v : PCWorld) : ratPayout v X = if v.Holds X then 1 else 0 := rfl
open Classical in
lemma ratPayout_XA (v : PCWorld) :
    ratPayout v XA = if v.Holds X ∧ v.Holds A then 1 else 0 := by
  by_cases h : v.Holds X ∧ v.Holds A
  · have h' : v.Holds XA := (holds_XA v).2 h
    simp [ratPayout, h, h']
  · have h' : ¬ v.Holds XA := fun hx => h ((holds_XA v).1 hx)
    simp [ratPayout, h, h']
open Classical in
lemma ratPayout_XAY (v : PCWorld) :
    ratPayout v XAY = if (v.Holds X ∧ v.Holds A) ∧ v.Holds Y then 1 else 0 := by
  by_cases h : (v.Holds X ∧ v.Holds A) ∧ v.Holds Y
  · have h' : v.Holds XAY := (holds_XAY v).2 ⟨(holds_XA v).2 h.1, h.2⟩
    simp [ratPayout, h, h']
  · have h' : ¬ v.Holds XAY := fun hx => h ⟨(holds_XA v).1 ((holds_XAY v).1 hx).1,
      ((holds_XAY v).1 hx).2⟩
    simp [ratPayout, h, h']

lemma gap_premise (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (v : PCWorld) :
    rowGap (pres []).coords (premiseRow c β hβ) v = ratPayout v X - c.P := by
  rw [premiseRow, toForceRow_gap ι β hβ _ _ ι_mem_coords]
  simp [Form.row]
  ring

lemma gap_appl (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (v : PCWorld) :
    rowGap (pres []).coords (applRow c β hβ) v = ratPayout v XA - c.A * ratPayout v X := by
  rw [applRow, toForceRow_gap ι β hβ _ _ ι_mem_coords]
  simp [Form.row, Fin.sum_univ_four]
  ring

lemma gap_strength (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (v : PCWorld) :
    rowGap (pres []).coords (strengthRow c β hβ) v = ratPayout v XAY - c.S * ratPayout v XA := by
  rw [strengthRow, toForceRow_gap ι β hβ _ _ ι_mem_coords]
  simp [Form.row, Fin.sum_univ_four]
  ring

/-- The odds of a strength. -/
def odds (c : ℚ) : ℚ := c / (1 - c)

lemma odds_spec {c : ℚ} (h1 : c < 1) : c = odds c * (1 - c) := by
  unfold odds
  have : (1 - c) ≠ 0 := by linarith
  field_simp

lemma odds_nonneg {c : ℚ} (h0 : 0 < c) (h1 : c < 1) : 0 ≤ odds c :=
  div_nonneg h0.le (by linarith)

/-- The fixture's odds: the largest of the three. -/
def ρ (c : Strengths) : ℚ := max (odds c.P) (max (odds c.A) (odds c.S))

lemma ρ_nonneg (c : Strengths) : 0 ≤ ρ c :=
  le_max_of_le_left (odds_nonneg c.P_pos c.P_lt)

lemma le_of_odds_le {a ρ' : ℚ} (h1 : a < 1) (h : odds a ≤ ρ') : a ≤ ρ' * (1 - a) := by
  have h3 : 0 ≤ 1 - a := by linarith
  calc a = odds a * (1 - a) := odds_spec h1
    _ ≤ ρ' * (1 - a) := mul_le_mul_of_nonneg_right h h3

lemma P_le (c : Strengths) : c.P ≤ ρ c * (1 - c.P) :=
  le_of_odds_le c.P_lt (le_max_left _ _)
lemma A_le (c : Strengths) : c.A ≤ ρ c * (1 - c.A) :=
  le_of_odds_le c.A_lt (le_max_of_le_right (le_max_left _ _))
lemma S_le (c : Strengths) : c.S ≤ ρ c * (1 - c.S) :=
  le_of_odds_le c.S_lt (le_max_of_le_right (le_max_right _ _))

lemma allTrue_holds (φ : Sentence) (h : φ = X ∨ φ = A ∨ φ = Y) : allTrue.Holds φ := by
  rcases h with rfl | rfl | rfl <;> trivial

/-- **Every world's deficit on every row is dominated by the all-true world's surplus at
the odds.**  No liveness hypothesis: the domination holds at every propositionally
consistent world. -/
theorem gap_dominated (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (r : Row)
    (hr : r = premiseRow c β hβ ∨ r = applRow c β hβ ∨ r = strengthRow c β hβ)
    (w : PCWorld) :
    -(rowGap (pres []).coords r w) ≤ ρ c * rowGap (pres []).coords r allTrue := by
  have hρ := ρ_nonneg c
  have hP := P_le c
  have hA := A_le c
  have hS := S_le c
  have hallX : allTrue.Holds X := allTrue_holds X (Or.inl rfl)
  have hallA : allTrue.Holds A := allTrue_holds A (Or.inr (Or.inl rfl))
  have hallY : allTrue.Holds Y := allTrue_holds Y (Or.inr (Or.inr rfl))
  rcases hr with rfl | rfl | rfl
  · rw [gap_premise, gap_premise, ratPayout_X, ratPayout_X]
    by_cases hX : w.Holds X <;> simp [hX, hallX] <;> nlinarith [c.P_pos, c.P_lt]
  · rw [gap_appl, gap_appl, ratPayout_XA, ratPayout_X, ratPayout_XA, ratPayout_X]
    by_cases hX : w.Holds X <;> by_cases hA' : w.Holds A <;>
      simp [hX, hA', hallX, hallA] <;> nlinarith [c.A_pos, c.A_lt]
  · rw [gap_strength, gap_strength, ratPayout_XAY, ratPayout_XA, ratPayout_XAY, ratPayout_XA]
    by_cases hX : w.Holds X <;> by_cases hA' : w.Holds A <;> by_cases hY : w.Holds Y <;>
      simp [hX, hA', hY, hallX, hallA, hallY] <;> nlinarith [c.S_pos, c.S_lt]

lemma mem_rowsAt {c : Strengths} {β : ℚ} {hβ : 0 ≤ β} {n₀ n : ℕ} {r : Row}
    (h : r ∈ rowsAt c β hβ n₀ n) :
    r = premiseRow c β hβ ∨ r = applRow c β hβ ∨ r = strengthRow c β hβ := by
  unfold rowsAt at h
  by_cases hn : n < n₀ <;> simp [hn] at h <;> tauto

/-- **B(i)/(ii)/(iii), the affirming case.**  With `Y` affirmed by the evaluation (or never
settled: take `nE` beyond every date of interest), the all-true world is live at every
date and the enforcer's assessed net worth is at least `−3ρ` at every live world at every
date, under every settlement date `n₁` of `X` and every defeat date `n₀`. -/
theorem liability (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ n₁ nE : ℕ) :
    ∀ n (v : PCWorld), (L n₁ nE true).Live n v →
      -(3 * (ρ c : ℝ)) ≤
        (realizedEnforcer (L n₁ nE true) (warrantEnforcer (schedLive c β hβ n₀))).netWorth
          (history (L n₁ nE true) (warrantEnforcer (schedLive c β hβ n₀))) v n :=
  liability_of_odds (L n₁ nE true) (schedLive c β hβ n₀) (ρ c) (ρ_nonneg c) fun n =>
    ⟨allTrue, allTrue_live n₁ nE n, fun w _ _ _ r hr =>
      gap_dominated c β hβ r (mem_rowsAt hr) w⟩

/-- **B(ii), the disagreeing case.**  `Y` is evaluated false at `nE`; force is withheld
from `nE` on (the region is empty, `disagree_region_empty` below).  The bankroll is the
same `3ρ`: before `nE` the all-true world is live and dominates; from `nE` on the
enforcer's account is frozen at its value at `nE − 1`, where every world then live was
live. -/
theorem liability_disagree (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ n₁ nE : ℕ)
    (hnE : 0 < nE) :
    ∀ n (v : PCWorld), (L n₁ nE false).Live n v →
      -(3 * (ρ c : ℝ)) ≤
        (realizedEnforcer (L n₁ nE false)
          (warrantEnforcer (schedWithheld c β hβ n₀ nE))).netWorth
          (history (L n₁ nE false) (warrantEnforcer (schedWithheld c β hβ n₀ nE))) v n := by
  intro n v hv
  have hgap : ∀ (w : PCWorld) (t : ℕ), ∀ r ∈ (schedWithheld c β hβ n₀ nE t).rows,
      -(rowGap (schedWithheld c β hβ n₀ nE t).coords r w) ≤
        ρ c * rowGap (schedWithheld c β hβ n₀ nE t).coords r allTrue := by
    intro w t r hr
    simp only [schedWithheld, pres_rows] at hr
    split_ifs at hr with ht
    · exact gap_dominated c β hβ r (mem_rowsAt hr) w
    · simp at hr
  by_cases hn : n < nE
  · exact netWorth_ge_neg_odds (L n₁ nE false) (schedWithheld c β hβ n₀ nE) (ρ c) (ρ_nonneg c)
      n allTrue (allTrue_live_before n₁ nE false n hn) v (fun t _ r hr => hgap v t r hr)
  · have hle : nE - 1 ≤ n := by omega
    rw [netWorth_eq_of_tail_zero _ _ v hle (fun t ht =>
      day_value_eq_zero_of_rows_nil (L n₁ nE false) (schedWithheld c β hβ n₀ nE) t (by
        simp only [schedWithheld, pres_rows]
        rw [if_neg (by omega)]) v)]
    have hv' : (L n₁ nE false).Live (nE - 1) v := ofDeductiveProcess_nested _ hle v hv
    exact netWorth_ge_neg_odds (L n₁ nE false) (schedWithheld c β hβ n₀ nE) (ρ c) (ρ_nonneg c)
      (nE - 1) allTrue (allTrue_live_before n₁ nE false (nE - 1) (by omega)) v
      (fun t _ r hr => hgap v t r hr)

/-! ### The seed side: emptiness on disagreement, and the orphan pin -/

/-- The warrant as three occurrences on the seed's four coordinates. -/
def occP (c : Strengths) : Occurrence 4 := ⟨1, Form.premise 0 c.P, .none, .party 1, ∅⟩
def occA (c : Strengths) : Occurrence 4 :=
  ⟨2, Form.applicability 0 1 c.A, .occurrence 1, .party 1, ∅⟩
def occS (c : Strengths) : Occurrence 4 :=
  ⟨3, Form.strength 1 2 c.S, .occurrence 2, .party 1, {2}⟩

/-- The grounds: the warrant's three occurrences. -/
def grounds (c : Strengths) : Grounds 4 := [occP c, occA c, occS c]

/-- The settlement after `X` true and `Y` false, with the closure `X∧A∧Y` false. -/
def settledDisagree : Settlement 4 :=
  ⟨![some true, none, some false, some false]⟩

lemma settledDisagree_pinned_iff (x : Fin 4 → ℚ) :
    settledDisagree.Pinned x ↔ x 0 = 1 ∧ x 2 = 0 ∧ x 3 = 0 := by
  unfold Settlement.Pinned settledDisagree truth
  constructor
  · intro h
    exact ⟨by simpa using h 0 true rfl, by simpa using h 2 false rfl,
      by simpa using h 3 false rfl⟩
  · rintro ⟨h0, h2, h3⟩ i b hi
    fin_cases i <;> simp_all

/-- **The region empties on disagreement** while the applicability row is live: the chain
`P(X) ≥ c_P`, `P(X∧A) ≥ c_A P(X)`, `P(X∧A∧Y) ≥ c_S P(X∧A)` with `X∧A∧Y` pinned to `0`
forces `P(X∧A) = 0`, then `c_A ≤ 0`. -/
theorem disagree_region_empty (c : Strengths) :
    ¬ ∃ x, (grounds c).region DocketState.quiet settledDisagree x := by
  rintro ⟨x, hx⟩
  rw [Grounds.region_iff] at hx
  obtain ⟨-, hpin, h⟩ := hx
  obtain ⟨h0, h2, -⟩ := (settledDisagree_pinned_iff x).1 hpin
  have hA := h (occA c) (by simp [grounds]) (by simp [DocketState.quiet])
  have hS := h (occS c) (by simp [grounds]) (by simp [DocketState.quiet])
  simp only [occA, occS] at hA hS
  rw [Form.applicability_sat_iff] at hA
  rw [Form.strength_sat_iff] at hS
  rw [h0] at hA
  rw [h2] at hS
  nlinarith [c.A_pos, c.S_pos, hA, hS]

/-- The docket after the applicability port is defeated. -/
def docketDefeatA : DocketState := ⟨{2}, ∅⟩

/-- **The orphan pin.**  After the applicability port is defeated, the same disagreement
leaves the region **nonempty**: the point `(1, 0, 0, 0)` lies in it. -/
theorem orphan_region_nonempty (c : Strengths) :
    (grounds c).region docketDefeatA settledDisagree ![1, 0, 0, 0] := by
  rw [Grounds.region_iff]
  refine ⟨fun i => by fin_cases i <;> norm_num,
    (settledDisagree_pinned_iff _).2 ⟨rfl, rfl, rfl⟩, ?_⟩
  intro o ho hid
  simp only [grounds, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · simp only [occP]
    rw [Form.premise_sat_iff]
    simpa using c.P_lt.le
  · exact absurd (by simp [occA, docketDefeatA]) hid
  · simp only [occS]
    rw [Form.strength_sat_iff]
    simp

/-- The world with `A` true and `Y` false. -/
def wAY : PCWorld := fun a => a ≠ 2

lemma wAY_X : wAY.Holds X := by show (0 : ℕ) ≠ 2; decide
lemma wAY_A : wAY.Holds A := by show (1 : ℕ) ≠ 2; decide
lemma wAY_notY : ¬ wAY.Holds Y := by show ¬ ((2 : ℕ) ≠ 2); decide

/-- **No slack world for the orphaned strength row.**  Every world live after the
disagreement (`Y` false) has nonpositive gap on the strength row, and the live world with
`X`, `A` true and `Y` false has a strictly negative one: the hypothesis of the odds
bankroll fails on the orphaned row. -/
theorem orphan_no_slack (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₁ nE : ℕ) (n : ℕ) (hn : nE ≤ n) :
    (∀ v : PCWorld, (L n₁ nE false).Live n v →
      rowGap (pres []).coords (strengthRow c β hβ) v ≤ 0) ∧
    ((L n₁ nE false).Live n wAY ∧ rowGap (pres []).coords (strengthRow c β hβ) wAY < 0) := by
  constructor
  · intro v hv
    have hY : ¬ v.Holds Y := by
      have := ((live_iff _ _ _ _ _).1 hv).2 hn
      simpa [holds_negY] using this
    rw [gap_strength, ratPayout_XAY, ratPayout_XA]
    by_cases hX : v.Holds X <;> by_cases hA' : v.Holds A <;> simp [hX, hA', hY]
    linarith [c.S_pos]
  · refine ⟨?_, ?_⟩
    · rw [live_iff]
      exact ⟨fun _ => wAY_X, fun _ => by simpa [holds_negY] using wAY_notY⟩
    · rw [gap_strength, ratPayout_XAY, ratPayout_XA]
      simp [wAY_X, wAY_A, wAY_notY]
      exact c.S_pos

end Fixture

/-! ## Part C — the record of a market run -/

section RecordPart

open LogicalInduction
open Workspace.Normativity.Contrib.TraderizedEnforcement
open Workspace.Deference.Contrib.ReasonMediatedAuthorship

/-- **A market run**: per date, the admitted grounds, the docket, the settlement, the
certificate events (event id, selected?), the authorized events — and the prices. -/
structure MarketRun (d : ℕ) where
  grounds : ℕ → Grounds d
  docket : ℕ → DocketState
  settlement : ℕ → Settlement d
  certs : ℕ → List (ℕ × Bool)
  authorized : ℕ → Finset ℕ
  prices : ℕ → Fin d → ℚ

/-- **A record entry**: the record state at the date, the certificate events, and the
enforcer's position.  No prices. -/
structure RecordEntry (d : ℕ) where
  state : RecordState d
  certs : List (ℕ × Bool)
  position : Fin d → ℚ

/-- **The record**: one entry per date. -/
abbrev Record (d : ℕ) := ℕ → RecordEntry d

/-- The enforcer's position on the live bundle at a price, at a uniform intensity: the
force algebra's position formula `Σ_rows β · violation · normal` on the bundle's rows read
as `⟨−a, ·⟩ ≥ −b`, summed along the bundle. -/
def positionOf (B : Bundle (Cite d) d) (β : ℚ) (p : Fin d → ℚ) : Fin d → ℚ := fun k =>
  (B.map fun c =>
    β * violation Finset.univ (fun j => -c.row.a j) (-c.row.b) p * (-c.row.a k)).sum

/-- The list form agrees with the force algebra's `position` over the bundle's indices. -/
theorem positionOf_eq_position (B : Bundle (Cite d) d) (β : ℚ) (p : Fin d → ℚ) (k : Fin d) :
    positionOf B β p k =
      position (Finset.univ : Finset (Fin B.length)) Finset.univ
        (fun i j => -(B.get i).row.a j) (fun i => -(B.get i).row.b) (fun _ => β) p k := by
  unfold positionOf position
  rw [← List.sum_ofFn]
  congr 1
  conv_lhs => rw [← List.ofFn_get B]
  rw [List.map_ofFn]
  rfl

/-- **The trace**: the record of a market run.  Prices enter only through the position. -/
def trace (run : MarketRun d) (β : ℚ) : Record d := fun n =>
  { state := ⟨run.grounds n, run.docket n, run.settlement n, run.authorized n⟩
    certs := run.certs n
    position := positionOf ((run.grounds n).bundle (run.docket n) (run.settlement n)) β
      (run.prices n) }

/-- **`Licensed` is decidable from the record alone.** -/
def decideLicensed {m m' : ℕ} (rec : Record d) (n : ℕ) (φ : Fin d) (v : ℚ)
    (c : VerdictCert d m m' φ) (event : ℕ) : Bool :=
  decide (Licensed (rec n).state φ v c event)

theorem decideLicensed_iff {m m' : ℕ} (rec : Record d) (n : ℕ) (φ : Fin d) (v : ℚ)
    (c : VerdictCert d m m' φ) (event : ℕ) :
    decideLicensed rec n φ v c event = true ↔ Licensed (rec n).state φ v c event :=
  decide_eq_true_iff

namespace RecordFixture

/-- The one-coordinate base run: the countermodel's grounds, quiet docket, no events, a
constant price. -/
def baseRun (p : ℚ) : MarketRun 1 where
  grounds _ := Countermodel.G
  docket _ := DocketState.quiet
  settlement _ := Countermodel.F
  certs _ := []
  authorized _ := ∅
  prices _ _ := p

/-- A run whose docket defeats `r₁`. -/
def defeatRun : MarketRun 1 where
  grounds _ := Countermodel.G
  docket _ := Countermodel.stDefeat
  settlement _ := Countermodel.F
  certs _ := []
  authorized _ := ∅
  prices _ _ := 1/2

/-- A price at or above the row leaves the position at zero. -/
lemma positionOf_base_eq_zero (β : ℚ) (p : ℚ) (hp : (1/2 : ℚ) ≤ p) :
    positionOf (Countermodel.G.bundle DocketState.quiet Countermodel.F) β (fun _ => p) = 0 := by
  rw [Countermodel.bundle_quiet]
  funext k
  have hviol : violation Finset.univ (fun j => -Countermodel.premRow.a j)
      (-Countermodel.premRow.b) (fun _ => p) = 0 := by
    unfold violation pair
    rw [Countermodel.premRow_b, Countermodel.premRow_a]
    simp
    linarith
  simp only [positionOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hviol,
    Pi.zero_apply]
  ring

/-- **The record is not injective in the run**: two runs with different prices, both
clearing the row, have the same record. -/
theorem trace_not_injective (β : ℚ) :
    baseRun (1/2) ≠ baseRun 1 ∧ trace (baseRun (1/2)) β = trace (baseRun 1) β := by
  constructor
  · intro h
    have := congrArg (fun r : MarketRun 1 => r.prices 0 0) h
    norm_num [baseRun] at this
  · funext n
    simp only [trace, baseRun]
    rw [positionOf_base_eq_zero β _ le_rfl, positionOf_base_eq_zero β _ (by norm_num)]

/-- **The record is not constant in the run**: a defeat shows in it. -/
theorem trace_not_const (β : ℚ) : trace (baseRun (1/2)) β ≠ trace defeatRun β := by
  intro h
  have := congrArg (fun r : Record 1 => (r 0).state.docket) h
  simp [trace, baseRun, defeatRun, DocketState.quiet, Countermodel.stDefeat] at this

/-- The audited class of runs. -/
def runs : Set (MarketRun 1) := {baseRun (1/2), baseRun 1, defeatRun}

/-- The frame: a run is its own world. -/
def β' : MarketRun 1 → Unit → MarketRun 1 := fun q _ => q

lemma mem_runs₁ : baseRun (1/2) ∈ runs := Set.mem_insert _ _
lemma mem_runs₂ : baseRun 1 ∈ runs := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
lemma mem_runs₃ : defeatRun ∈ runs :=
  Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- **Not over-rich**: the trace is not injective on the audited class, so
`reasonMediated_of_injOn` does not make mediation by the record vacuous. -/
theorem trace_not_injOn (β : ℚ) : ¬ Set.InjOn (fun q => trace (β' q ()) β) runs := by
  intro h
  exact (trace_not_injective β).1 (h mem_runs₁ mem_runs₂ (trace_not_injective β).2)

/-- **Not under-rich**: the trace is not constant on the audited class, so
`reasonMediated_const_iff`'s isolated-principal reading does not apply. -/
theorem trace_not_constant (β : ℚ) : ¬ ∃ r₀, ∀ q ∈ runs, trace (β' q ()) β = r₀ := by
  rintro ⟨r₀, h⟩
  exact trace_not_const β ((h _ mem_runs₁).trans (h _ mem_runs₃).symm)

/-- **Prices are not mediated by the record**: the payload "the price of `φ`" is not
reason-mediated by the trace on the audited class — the record is strictly coarser than
the run. -/
theorem price_not_mediated (β : ℚ) :
    ¬ ReasonMediated β' (fun q => trace q β) (fun q => q.prices 0 0) runs () := by
  intro h
  have := h (baseRun (1/2)) mem_runs₁ (baseRun 1) mem_runs₂ (trace_not_injective β).2
  norm_num [β', baseRun] at this

/-- **The docket is mediated by the record**: the payload "the docket" factors through the
trace. -/
theorem docket_mediated (β : ℚ) :
    ReasonMediated β' (fun q => trace q β) (fun q => q.docket) runs () := by
  intro q _ q' _ h
  funext n
  have := congrArg (fun r : Record 1 => (r n).state.docket) h
  simpa [trace, β'] using this

end RecordFixture

end RecordPart

/-! ## Nonvacuity witnesses -/

namespace Witness

open LogicalInduction
open Workspace.Normativity.Contrib.TraderizedEnforcement

/-- `Settlement`, `Seed`, `DocketState`, `SubItem`, `StrItem`, `Constitutive`. -/
def settlement : Settlement 2 := ⟨![some true, none]⟩
def subItem : SubItem 2 := ⟨Form.premise 0 (1/3), 0⟩
def strItem : StrItem 2 := ⟨cubeUpper 1, .coherence, 5⟩
def constitutive : Constitutive 2 Unit := ⟨{()}, {1}⟩
def seed : Seed 2 Unit := ⟨[subItem], [strItem], constitutive⟩
def docket : DocketState := ⟨{0}, {5}⟩

/-- The seed's forced region on the settlement is inhabited. -/
theorem seed_region_inhabited :
    forcedRegion seed [] DocketState.quiet settlement ![1, 1/2] := by
  rw [forcedRegion_iff]
  refine ⟨fun i => by fin_cases i <;> norm_num, ?_, ?_, ?_⟩
  · intro i b hi
    fin_cases i <;> simp_all [settlement, truth]
  · intro it hit
    simp [seed, Seed.liveSub, DocketState.quiet, subItem] at hit
    subst hit
    rw [Form.premise_sat_iff]; norm_num
  · intro it hit
    simp [seed, Seed.liveStr, DocketState.quiet, strItem] at hit
    subst hit
    exact cubeUpper_sat (fun i => by fin_cases i <;> norm_num) 1

/-- `IsForcedInterval`: the countermodel's interval. -/
theorem forcedInterval : IsForcedInterval Countermodel.G.seed [] DocketState.quiet
    Countermodel.F Countermodel.φ (1/2) 1 := Countermodel.forcedInterval

/-- `BoundCert`, `VerdictCert`, `Occurrence`, `Grounds`, `RecordState`: the countermodel's. -/
def verdictCert : VerdictCert 1 1 1 Countermodel.φ := Countermodel.cert 1
def recordState : RecordState 1 := Countermodel.recordAuth

/-- `Supported` and `Licensed` are inhabited. -/
theorem licensed_inhabited : Licensed Countermodel.recordAuth Countermodel.φ (2/3)
    (Countermodel.cert 1) 7 := Countermodel.supported_not_licensed.2.2.1

/-- `Strengths`: `4/5, 3/4, 2/3`. -/
def strengths : Fixture.Strengths :=
  ⟨4/5, 3/4, 2/3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The fixture's odds: `max(4, max(3, 2)) = 4`, so the bankroll is `12`. -/
theorem strengths_odds : Fixture.ρ strengths = 4 := by
  simp [Fixture.ρ, Fixture.odds, strengths]
  norm_num

/-- The fixture's presentation at date `0`, defeat at `5`: three rows. -/
theorem sched_rows_length :
    (Fixture.schedLive strengths 10 (by norm_num) 5 0).rows.length = 3 := by
  simp [Fixture.schedLive, Fixture.pres, Fixture.rowsAt]

/-- **The fixture's bankroll is `12`**: `X` settled at `3`, the applicability port defeated
at `5`, `Y` affirmed at `8`, intensity `10`. -/
theorem fixture_liability :
    ∀ n (v : PCWorld), (Fixture.L 3 8 true).Live n v →
      -(12 : ℝ) ≤
        (Workspace.Normativity.Contrib.EnforcementPreservation.realizedEnforcer
          (Fixture.L 3 8 true)
          (warrantEnforcer (Fixture.schedLive strengths 10 (by norm_num) 5))).netWorth
          (Workspace.Normativity.Contrib.EnforcementPreservation.history
            (Fixture.L 3 8 true)
            (warrantEnforcer (Fixture.schedLive strengths 10 (by norm_num) 5))) v n := by
  have h := Fixture.liability strengths 10 (by norm_num) 5 3 8
  rw [strengths_odds] at h
  intro n v hv
  have := h n v hv
  norm_num at this ⊢
  exact this

/-- `MarketRun`, `Record`, `RecordEntry`: the Part C fixture, with a nonzero position when
the price violates the row — the record does carry the position. -/
theorem position_nonzero :
    positionOf (Countermodel.G.bundle DocketState.quiet Countermodel.F) 1 (fun _ => 0) 0 =
      1 := by
  rw [Countermodel.bundle_quiet]
  simp only [positionOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  unfold violation pair
  rw [Countermodel.premRow_b, Countermodel.premRow_a]
  norm_num

end Witness

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.truth
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Settlement
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Settlement.Pinned
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Settlement.le
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Settlement.empty
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Settlement.empty_pinned
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Settlement.le_refl
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Settlement.Pinned.mono
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Settlement.pinRowsAt
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Settlement.pinRows
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Settlement.pinRowsAt_sat_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Settlement.pinRows_sat_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.settledTerm
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.specialize
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.specialize_sat_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Form
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Form.c
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Form.row
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Form.premise_sat_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Form.applicability_sat_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Form.strength_sat_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.SubItem
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.StrKind
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.StrItem
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Constitutive
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Seed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.DocketState
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.DocketState.quiet
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Seed.liveSub
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Seed.liveStr
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Cite
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.pinCited
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.forcedBundle
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.forcedRegion
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.forcedRegion_iff_check
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.pinCited_sat_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.forcedRegion_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.forcedRegion_anti
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.LowerBound
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.UpperBound
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.IsForcedInterval
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.IsForcedInterval.le
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.IsForcedInterval.unique
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.IsForcedInterval.mono
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.widenSeed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.defeat_widens
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.allowed_sat
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.BoundCert
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.BoundCert.value
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.BoundCert.sound_of_pos
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.BoundCert.sound
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.lowerCert_bound
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.upperCert_bound
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.seg
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Row.sat_seg
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.region_convex
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.region_attains_between
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Applicability
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Source
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Occurrence
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Occurrence.toSub
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.seed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.bundle
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.region
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.region_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Settlement.empty_pinRowsAt
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.mem_bundle_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Admissible
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.VerdictCert
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.VerdictCert.RowAdmitted
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.VerdictCert.RowAdmitted.allowed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.VerdictCert.CitesLive
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Supported
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordState
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Licensed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.licensed_supported
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.supported_admissible
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.licence_chain
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Supported.valid
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.φ
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.r₁
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.r₂
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.G
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.F
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.stDefeat
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.premRow
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.premRow_sat_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.region_unchanged
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.region_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.loCert
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.hiCert
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.loCert_value
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.hiCert_value
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.cert
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.loPoint_mem
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.hiPoint_mem
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.premRow_b
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.premRow_a
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.premRow_ne_cubeUpper
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.premRow_ne_cubeLower
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.bundle_quiet
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.bundle_defeat
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.cited_quiet
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.supported_quiet
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.stale_not_supported
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.fresh_supported
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.admissible_not_supported
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.forcedInterval
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.recordAuth
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.recordNoAuth
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.supported_not_licensed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.Party
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.interface
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.frame
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.selection_not_transparent
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.warrantEnforcer
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.realizedEnforcer_strat
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.rowGap
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.rowUnits
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.rowUnits_nonneg
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.day_value_eq
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.day_value_ge
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.dayGap
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.slackMass
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.slackMass_le_netWorth
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.enforcer_netWorth_lt_three
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.netWorth_ge_neg_odds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.liability_of_odds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.warrant_normative_inductor
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.netWorth_nonneg_of_inclusive
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.day_value_eq_zero_of_rows_nil
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.netWorth_eq_of_tail_zero
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.ofDeductiveProcess_nested
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.X
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.A
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.Y
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.negY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.X_ne_XA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.X_ne_XAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.X_ne_Y
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XA_ne_X
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XA_ne_XAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XA_ne_Y
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XAY_ne_X
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XAY_ne_XA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XAY_ne_Y
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.Y_ne_X
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.Y_ne_XA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.Y_ne_XAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.holds_XA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.holds_XAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.holds_negY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.coordList
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.coordList_nodup
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ι
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ι_zero
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ι_one
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ι_two
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ι_three
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.toForceRow
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.toForceRow_pair
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.toForceRow_gap
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.Strengths
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.premiseRow
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.applRow
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.strengthRow
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.rowsAt
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.pres
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.pres_rows
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ι_mem_coords
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.schedLive
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.schedWithheld
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.stage
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.mem_stage
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.stage_mono
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.dp
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.L
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.live_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.allTrue_live
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.allTrue_live_before
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ratPayout_X
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ratPayout_XA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ratPayout_XAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.gap_premise
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.gap_appl
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.gap_strength
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.odds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.odds_spec
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.odds_nonneg
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ρ
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ρ_nonneg
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.le_of_odds_le
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.P_le
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.A_le
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.S_le
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.allTrue_holds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.gap_dominated
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.mem_rowsAt
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.liability
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.liability_disagree
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.occP
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.occA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.occS
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.grounds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.settledDisagree
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.settledDisagree_pinned_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.disagree_region_empty
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.docketDefeatA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.orphan_region_nonempty
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.wAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.wAY_X
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.wAY_A
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.wAY_notY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.orphan_no_slack
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.MarketRun
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordEntry
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Record
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.positionOf
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.positionOf_eq_position
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.trace
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.decideLicensed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.decideLicensed_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.baseRun
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.defeatRun
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.positionOf_base_eq_zero
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.trace_not_injective
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.trace_not_const
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.runs
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.β'
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.mem_runs₁
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.mem_runs₂
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.mem_runs₃
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.trace_not_injOn
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.trace_not_constant
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.price_not_mediated
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.docket_mediated
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.settlement
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.subItem
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.strItem
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.constitutive
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.seed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.docket
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.seed_region_inhabited
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.forcedInterval
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.verdictCert
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.recordState
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.licensed_inhabited
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.strengths
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.strengths_odds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.sched_rows_length
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.fixture_liability
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.position_nonzero

end Workspace.Normativity.Contrib.WarrantEntitlement
