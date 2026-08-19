/-
# The constraint schedule: the paper-facing input interface

Every theorem of record upstream of this file takes the *compiled* projector as an input.
`ProjectionSchedule` asks for a list of max–min representations per date;
`ProjectionSchedule.end_to_end` asks in addition for a region, a target, a proof that the
target is the region's nearest point, and a proof that the representations evaluate to it.
That is the right interface for the algebra and the wrong one for a paper: the reader is
being asked to supply the answer.

This file supplies the input interface the paper actually claims.  A
`RationalConstraintSchedule` is a **schedule of regions** — one rational polytope per date,
in the day's fragment coordinates — and nothing else.  From it the region predicate, the
target, the nearest-point property, the cube bound and the fragment-locality are all
*derived*, and the three facts `end_to_end` consumed as hypotheses become theorems.

**What is still supplied, and why.**  Two things, and they are of quite different kinds.

* `hadm` — that the day's region admits every world the deductive process leaves plausible.
  That is the genuine normative input: it is what buys zero liability, it is not derivable
  from the geometry, and it is the assumption the paper states.
* `RegionRepresentation.Effective` — that the day's max–min representation is *computed*
  from the region by a primitive-recursive function.  Note what this is **not**: it is not
  the assumption that a representation exists, nor that it is correct.  Both of those are
  theorems — `ProjectionBridge.exists_repMap_mem` gives the representation and
  `canonicalRepresentation` below assembles it into a `RegionRepresentation` for *every*
  schedule.  What is missing is only an algorithm, because the bridge's map comes out of
  `choose`: upstream, Ovchinnikov's index sets are cut out by
  `Finset.univ.filter (fun T => ∃ y ∈ Γ, up y = T)` over an infinite domain, so the proof is
  an existence proof and `Primrec` needs a construction.  The gap is stated once,
  date-uniformly, as a structure rather than hidden in a hypothesis list.

The split is load-bearing.  **The conformance half of the theorem does not touch
effectiveness at all**: `conformance_of_constraints` and `criterion_of_constraints` below
take a constraint schedule and a deductive process and *nothing else* — no computability, no
admissibility, no representation.  Only `IsLogicalInductor`, which is a statement about the
market being computable, needs `Effective`.

**The dependent index.**  `region n` lives in `RationalPolytope (coords n).length`, so the
schedule's regions do not inhabit one type and `Primrec` cannot speak about them.  The
computability structure therefore carries the *flattened vertex data*
`(region n).verts.map List.ofFn : List (List ℚ)`, which is honest finite data in a fixed
type, and the compiler is a function of that.  This is the transposition the file header of
`RationalPolytope` anticipated, and it is why the compiler takes flat data rather than a
polytope.

**No relation between dates is assumed.**  `region n` and `region (n+1)` are unconstrained:
no nesting, no monotonicity, no limit.  Non-monotonic revision of the constraint is inside
the theorem's scope, and that is deliberate.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.ProjectionBridge
import Workspace.Normativity.Contrib.ProjectionEffective

namespace Workspace.Normativity.Contrib.ConstraintSchedule

open LogicalInduction
open scoped RealInnerProductSpace
open Workspace.Normativity.Contrib.RationalPolytope
open Workspace.Normativity.Contrib.ProjectionForce
open Workspace.Normativity.Contrib.ProjectionMarket
open Workspace.Normativity.Contrib.ProjectionCompiler
open Workspace.Normativity.Contrib.ProjectionCalibrated
open Workspace.Normativity.Contrib.ProjectionPrimrec
open Workspace.Normativity.Contrib.ProjectionEnforcer
open Workspace.Normativity.Contrib.DeductiveEnforcement
open Workspace.Normativity.Contrib.EnforcedComputation
open Workspace.Normativity.Contrib.EnforcedCompiler
open Workspace.Normativity.Contrib.ProjectionEffective
open Workspace.Normativity.Contrib.ProjectionBridge

/-! ## The fragment as a Euclidean coordinate system

A `Fragment` is a duplicate-free list of sentences, so it *is* a coordinate system: the
day's price vector restricted to it is a point of `Pt F.coords.length`, and the fragment
inner product `ProjectionForce.ip` is the Euclidean one there.  The two lemmas below are
the whole of the transport, and every later dependent-type step goes through them. -/

lemma restrict_sub (F : Fragment) (u v : Sentence → ℝ) :
    restrict F (fun φ => u φ - v φ) = restrict F u - restrict F v := rfl

/-- A sum over the fragment is a sum over its coordinates. -/
lemma sum_toFinset (F : Fragment) (f : Sentence → ℝ) :
    ∑ φ ∈ F.toFinset, f φ = ∑ i : Fin F.coords.length, f (F.coords.get i) := by
  rw [F.sum_eq, ← List.sum_ofFn (f := fun i : Fin F.coords.length => f (F.coords.get i))]
  congr 1
  have hid : List.ofFn (fun i : Fin F.coords.length => F.coords.get i) = F.coords := by simp
  calc List.map f F.coords
      = List.map f (List.ofFn fun i : Fin F.coords.length => F.coords.get i) := by rw [hid]
    _ = List.ofFn fun i : Fin F.coords.length => f (F.coords.get i) := List.map_ofFn

/-- **The fragment inner product is the Euclidean one on the restricted vectors.** -/
lemma ip_eq_inner (F : Fragment) (u v : Sentence → ℝ) :
    ip F.toFinset u v = ⟪restrict F u, restrict F v⟫ := by
  rw [ip, sum_toFinset, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [ProjectionBridge.restrict_apply, RCLike.inner_apply, starRingEnd_apply,
      star_trivial, mul_comm]

lemma get_mem_toFinset (F : Fragment) (i : Fin F.coords.length) :
    F.coords.get i ∈ F.toFinset :=
  List.mem_toFinset.mpr (List.get_mem _ _)

lemma restrict_congr {F : Fragment} {u v : Sentence → ℝ}
    (h : ∀ φ ∈ F.toFinset, u φ = v φ) : restrict F u = restrict F v := by
  unfold restrict
  congr 1
  funext i
  exact h _ (get_mem_toFinset F i)

/-! ## The region as a predicate on price vectors -/

/-- The day's region, read as a constraint on price vectors: the restricted vector lies in
the polytope. -/
def regionPred (F : Fragment) (K : RationalPolytope F.coords.length) :
    (Sentence → ℝ) → Prop := fun y => restrict F y ∈ K.carrier

/-- **The region constrains the fragment's coordinates and nothing else.**  One of the
three facts `ProjectionSchedule.end_to_end` took as a hypothesis. -/
theorem fragmentLocal_regionPred (F : Fragment) (K : RationalPolytope F.coords.length) :
    FragmentLocal F.toFinset (regionPred F K) := by
  intro u v h hu
  unfold regionPred at hu ⊢
  rwa [← restrict_congr h]

/-- **The region lies in the cube on the fragment.**  The second hypothesis, discharged
from the vertices lying in the cube. -/
theorem regionPred_mem_cube (F : Fragment) (K : RationalPolytope F.coords.length)
    (hv : ∀ v ∈ K.verts, ∀ i, 0 ≤ v i ∧ v i ≤ 1) :
    ∀ y, regionPred F K y → ∀ φ ∈ F.toFinset, 0 ≤ y φ ∧ y φ ≤ 1 := by
  intro y hy φ hφ
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hφ)
  have := K.carrier_mem_cube hv hy i
  rwa [restrict_apply, hi] at this

/-! ## The target, and that it is the nearest point

`RationalPolytope.proj` is the Euclidean nearest point in the coordinate space.  Read back
as a price vector it is the day's target, and the variational inequality transports to
`ProjectionForce.IsNearestPoint` through `ip_eq_inner`.  Off the fragment the target is
`0`: the value there is never read — `IsNearestPoint`, `regionPred` and `dist2` all sum over
the fragment only — and pinning it makes the target a `def` rather than a choice. -/

/-- The day's target: the Euclidean projection of the displayed price onto the region, read
back as a price vector, and `0` off the fragment. -/
noncomputable def target (F : Fragment) (K : RationalPolytope F.coords.length)
    (p : Sentence → ℝ) : Sentence → ℝ :=
  fun φ => (List.ofFn fun i => K.proj (restrict F p) i).getD (F.coords.idxOf φ) 0

lemma target_get (F : Fragment) (K : RationalPolytope F.coords.length)
    (p : Sentence → ℝ) (i : Fin F.coords.length) :
    target F K p (F.coords.get i) = K.proj (restrict F p) i := by
  have hidx : F.coords.idxOf (F.coords.get i) = (i : ℕ) := List.get_idxOf F.nodup i
  rw [target, hidx, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-- The target at a priced sentence, indexed by membership rather than by position — the
form `ProjectionBridge.exists_repMap_mem` states its correctness in. -/
lemma target_mem (F : Fragment) (K : RationalPolytope F.coords.length)
    (p : Sentence → ℝ) {φ : Sentence} (hφ : φ ∈ F.coords) :
    target F K p φ
      = K.proj (restrict F p) ⟨F.coords.idxOf φ, List.idxOf_lt_length_of_mem hφ⟩ := by
  have hlt : F.coords.idxOf φ < F.coords.length := List.idxOf_lt_length_of_mem hφ
  have hget : F.coords.get ⟨F.coords.idxOf φ, hlt⟩ = φ := List.idxOf_get hlt
  have h := target_get F K p ⟨F.coords.idxOf φ, hlt⟩
  rwa [hget] at h

lemma restrict_target (F : Fragment) (K : RationalPolytope F.coords.length)
    (p : Sentence → ℝ) : restrict F (target F K p) = K.proj (restrict F p) := by
  unfold restrict
  congr 1
  funext i
  exact target_get F K p i

/-- **The target is the region's nearest point to the displayed price.**  The third
hypothesis, discharged: it is `RationalPolytope.proj_variational` transported along
`ip_eq_inner`. -/
theorem isNearestPoint_target (F : Fragment) (K : RationalPolytope F.coords.length)
    (p : Sentence → ℝ) :
    IsNearestPoint F.toFinset (regionPred F K) p (target F K p) := by
  refine ⟨?_, ?_⟩
  · show restrict F (target F K p) ∈ K.carrier
    rw [restrict_target]
    exact K.proj_mem _
  · intro y hy
    rw [ip_eq_inner, restrict_sub, restrict_sub, restrict_target]
    exact K.proj_variational _ hy

/-! ## The constraint schedule

The paper-facing input: which sentences are priced, how closely, and **what region the
prices are required to lie in** — one rational polytope per date, in the day's own
coordinates.  Nonemptiness is already a field of `RationalPolytope`, so it is not
re-assumed.  Nothing relates one date's region to another's. -/

/-- **A schedule of rational convex constraints.**  The whole input to the construction,
apart from the deductive process itself. -/
structure RationalConstraintSchedule where
  /-- The day-`n` priced fragment, listed once each. -/
  coords : ℕ → List Sentence
  /-- Each priced sentence is listed once. -/
  nodup : ∀ n, (coords n).Nodup
  /-- The day-`n` requested tolerance. -/
  tol : ℕ → ℚ
  /-- Tolerances are strictly positive; a zero tolerance buys nothing. -/
  tol_pos : ∀ n, 0 < tol n
  /-- The day-`n` constraint region, in the day's fragment coordinates. -/
  region : ∀ n, RationalPolytope (coords n).length
  /-- The region is a region of credences: its vertices lie in the unit cube. -/
  region_in_cube : ∀ n, ∀ v ∈ (region n).verts, ∀ i, 0 ≤ v i ∧ v i ≤ 1

namespace RationalConstraintSchedule

variable (C : RationalConstraintSchedule)

/-- The day-`n` fragment. -/
def fragment (n : ℕ) : Fragment := ⟨C.coords n, C.nodup n⟩

@[simp] lemma fragment_coords (n : ℕ) : (C.fragment n).coords = C.coords n := rfl

/-- The day-`n` region as a constraint on price vectors. -/
def regionPred (n : ℕ) : (Sentence → ℝ) → Prop :=
  ConstraintSchedule.regionPred (C.fragment n) (C.region n)

/-- The day-`n` target at a price vector: the projection of that vector onto the day's
region.  There is no freedom in it — it is a `def`, not a supplied point. -/
noncomputable def targetAt (n : ℕ) (p : Sentence → ℝ) : Sentence → ℝ :=
  ConstraintSchedule.target (C.fragment n) (C.region n) p

/-- **The region is fragment-local.** -/
theorem fragmentLocal (n : ℕ) :
    FragmentLocal (C.fragment n).toFinset (C.regionPred n) :=
  fragmentLocal_regionPred _ _

/-- **The region lies in the cube on the fragment.** -/
theorem regionPred_cube (n : ℕ) :
    ∀ y, C.regionPred n y → ∀ φ ∈ (C.fragment n).toFinset, 0 ≤ y φ ∧ y φ ≤ 1 :=
  regionPred_mem_cube _ _ (C.region_in_cube n)

/-- **The target is the region's nearest point.** -/
theorem isNearestPoint_targetAt (n : ℕ) (p : Sentence → ℝ) :
    IsNearestPoint (C.fragment n).toFinset (C.regionPred n) p (C.targetAt n p) :=
  isNearestPoint_target _ _ p

/-! ### The region as flat data

`region n` lives in a type that depends on `n`, so no `Primrec` statement can mention it.
Flattening each vertex to a `List ℚ` puts the day's region in the fixed type
`List (List ℚ)`, which is `Primcodable`, at the cost of forgetting the length — which the
fragment carries anyway. -/

/-- The day-`n` region as flat rational data: its vertices, written out coordinatewise. -/
def vertexData (n : ℕ) : List (List ℚ) :=
  (C.region n).verts.map fun v => List.ofFn v

/-- **The effectiveness requirement on a constraint schedule**, and the whole of it: the
fragment schedule, the tolerance schedule and the region's vertex data are computable
functions of the date. -/
structure Computation where
  /-- The fragment schedule is computable. -/
  coordsComputable : Primrec C.coords
  /-- The tolerance schedule is computable. -/
  tolComputable : Primrec C.tol
  /-- The region's vertex data is computable. -/
  vertsComputable : Primrec C.vertexData

end RationalConstraintSchedule

/-! ## The one thing still supplied

The construction needs the day's projector in the compiler's max–min syntax.  Two separate
things are needed, and the file keeps them apart because they are in very different states.

**Correctness of the syntax** is a classical fact, and it is proved:
`PolyhedralCoverage.exists_maxMin_proj` says each coordinate of the projector *is* a maximum
of minima of rational affine forms attached to the enumerated faces.  What is carried below
as `RegionRepresentation` is that fact, transported into the compiler's `Rep` type and
packaged per date.

**Effectiveness of the syntax** is not proved, and cannot be read off that theorem:
Ovchinnikov's index sets are cut out by `Finset.univ.filter (fun T => ∃ y ∈ Γ, up y = T)`,
an existential over the whole domain, so the proof is a pure existence proof and `Primrec`
needs an algorithm.  That, and only that, is what `RegionRepresentation.Effective` assumes.

The split is load-bearing for the reader: **the conformance half of the theorem never
touches effectiveness.**  `conformance`, `criterion` and `eventual_coherence_of_constraints`
below take a `RegionRepresentation` and no computability at all; only
`IsLogicalInductor` — which is a statement about the market being computable — needs
`Effective`.

**The exact missing theorem** that would discharge `Effective` uniformly:

    ∃ f : List Sentence → List (List ℚ) → List Rep, Primrec₂ f ∧
      ∀ (C : RationalConstraintSchedule) (n : ℕ),
        f (C.coords n) (C.vertexData n) is correct for date n in the sense of reps_eval

The geometry it would have to enumerate is already effective — `PolyhedralCoverage.faceList`
is a `def`, and `Face.piece` is written through `det⁻¹ • adjugate` precisely so as to stay
computable — so what is missing is an effective replacement for the max–min *selection*
step, not for the pieces. -/

/-- **A max–min representation of a constraint schedule's projectors.**  One representation
list per date, positionally aligned with the day's fragment, evaluating at every price
vector to the day's target.  This is `exists_maxMin_proj` in the compiler's syntax; no
effectiveness is asserted. -/
structure RegionRepresentation (C : RationalConstraintSchedule) where
  /-- The day-`n` representations, positionally aligned with `coords n`. -/
  reps : ℕ → List Rep
  /-- The value returned where a lookup fails; it never occurs in a well-formed
  schedule. -/
  dflt : Rep
  /-- **Correctness.**  What the representation evaluates to is the day's target, at every
  price vector and every priced sentence. -/
  reps_eval : ∀ n, ∀ φ ∈ C.coords n, ∀ p : Sentence → ℝ,
    repEval (C.fragment n) (repAt (C.coords n) (reps n) dflt φ) p = C.targetAt n p φ

/-- **The representation is effective**: it is what a single primitive-recursive compiler
returns on the day's fragment and the day's flat vertex data.  Stated through a compiler
rather than as `Primrec R.reps` so that the schedule's own `vertsComputable` is what carries
the region into the computation, which is what "derived from the constraints" has to
mean. -/
structure RegionRepresentation.Effective {C : RationalConstraintSchedule}
    (R : RegionRepresentation C) where
  /-- The compiler: fragment and flat vertex data in, one representation per priced
  sentence out. -/
  compile : List Sentence → List (List ℚ) → List Rep
  /-- The compiler is effective. -/
  compileComputable : Primrec₂ compile
  /-- The representation is what the compiler returns on the day's data. -/
  reps_eq : ∀ n, R.reps n = compile (C.coords n) (C.vertexData n)

/-! ### Correctness is not an assumption

A representation map obtained from `ProjectionBridge.exists_repMap_mem`, laid out
positionally against the day's fragment, satisfies `reps_eval`.  So the correctness field is
inhabited for *every* constraint schedule: nothing about it is assumed.  What is not
obtained this way — and cannot be, because the bridge's map comes out of `choose` — is any
`Primrec` statement about it.  That is `Effective`, below, and it is the whole of the
residual gap. -/

/-- Positional lookup against a fragment recovers the map it was laid out from. -/
lemma repAt_map {coords : List Sentence} (R : Sentence → Rep) (d : Rep) {φ : Sentence}
    (hφ : φ ∈ coords) : repAt coords (coords.map R) d φ = R φ := by
  have hlt : coords.idxOf φ < coords.length := List.idxOf_lt_length_of_mem hφ
  rw [repAt, List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map,
    List.getElem_idxOf hlt]

/-- The day's target at a priced sentence, in the index form the bridge states. -/
lemma RationalConstraintSchedule.targetAt_mem (C : RationalConstraintSchedule) (n : ℕ)
    (p : Sentence → ℝ) {φ : Sentence} (hφ : φ ∈ (C.fragment n).coords) :
    C.targetAt n p φ = (C.region n).proj (restrict (C.fragment n) p)
      ⟨(C.fragment n).coords.idxOf φ, List.idxOf_lt_length_of_mem hφ⟩ :=
  target_mem (C.fragment n) (C.region n) p hφ

/-- **The canonical representation of a constraint schedule's projectors.**  Noncomputable
by construction — it is `choose` applied to the bridge — which is exactly why `Effective`
below cannot be read off it. -/
noncomputable def RationalConstraintSchedule.canonicalRepresentation
    (C : RationalConstraintSchedule) : RegionRepresentation C := by
  classical
  choose R hR using fun n =>
    ProjectionBridge.exists_repMap_mem (C.fragment n) (C.region n)
  refine
    { reps := fun n => (C.coords n).map (R n)
      dflt := default
      reps_eval := fun n φ hφ p => ?_ }
  -- after the three rewrites the two sides differ only in the `Fin` bound proof
  rw [repAt_map (R n) default hφ, hR n p φ hφ, C.targetAt_mem n p hφ]
  rfl


/-- **Every constraint schedule has a correct representation.**  `reps_eval` is a theorem,
not a hypothesis; only its effectiveness is open. -/
theorem exists_representation (C : RationalConstraintSchedule) :
    Nonempty (RegionRepresentation C) := ⟨C.canonicalRepresentation⟩

namespace RationalConstraintSchedule

variable (C : RationalConstraintSchedule) (R : RegionRepresentation C)

/-- **The derived projection schedule.**  Nothing here is a free parameter: the fragment,
the tolerance and the representations all come from the constraint schedule. -/
def schedule : ProjectionSchedule where
  coords := C.coords
  nodup := C.nodup
  tol := C.tol
  tol_pos := C.tol_pos
  reps := R.reps
  dflt := R.dflt

@[simp] lemma schedule_fragment (n : ℕ) : (C.schedule R).fragment n = C.fragment n := rfl

@[simp] lemma schedule_rep (n : ℕ) (φ : Sentence) :
    (C.schedule R).rep n φ = repAt (C.coords n) (R.reps n) R.dflt φ := rfl

/-- **The derived market**: the source deductive firm priced together with the enforcer the
schedule's own regions generate. -/
noncomputable def market (DP : DeductiveProcess) : History := (C.schedule R).market DP

/-- **The derived target**: the projection of the day's displayed price onto the day's
region.  A `def`, not a parameter. -/
noncomputable def target (DP : DeductiveProcess) (n : ℕ) : Sentence → ℝ :=
  C.targetAt n (C.market R DP n)

/-- The representations evaluate to the day's target at the day's prices — the `hrep`
hypothesis of every upstream statement, discharged. -/
lemma repEval_market (DP : DeductiveProcess) (n : ℕ) :
    ∀ φ ∈ (C.schedule R).coords n,
      repEval ((C.schedule R).fragment n) ((C.schedule R).rep n φ)
        ((C.schedule R).market DP n) = C.target R DP n φ :=
  fun φ hφ => R.reps_eval n φ hφ (C.market R DP n)

/-- The derived schedule's effectiveness, from the constraint schedule's own together with
the compiler's. -/
def scheduleComputation (hC : C.Computation) (hR : R.Effective) :
    ProjectionScheduleComputation (C.schedule R) where
  coordsComputable := hC.coordsComputable
  tolComputable := hC.tolComputable
  repsComputable :=
    (hR.compileComputable.comp hC.coordsComputable hC.vertsComputable).of_eq
      fun n => (hR.reps_eq n).symm

/-! ## The payoff -/

/-- **Finite-time conformance, with no computability hypothesis at all.**  At every date the
displayed price is within the requested tolerance of the day's region, in the intrinsic
Euclidean distance on the day's fragment.  No `hrep`, no supplied target, no supplied
nearest-point property, no admissibility hypothesis, no effectiveness: this half of the
theorem is the geometry plus the force algebra and nothing else. -/
theorem conformance (DP : DeductiveProcess) (n : ℕ) :
    dist2 (C.fragment n).toFinset (C.market R DP n) (C.target R DP n)
      ≤ ((C.tol n : ℚ) : ℝ) :=
  (C.schedule R).dist2_le_tol DP n (C.fragmentLocal n) (C.regionPred_cube n)
    (C.isNearestPoint_targetAt n _) (C.repEval_market R DP n)

/-- **The criterion.**  The day's target satisfies the day's constraint, and the displayed
prices agree with it to within the requested tolerance on every priced sentence — the
paper's sup-norm form, free from the Euclidean one. -/
theorem criterion (DP : DeductiveProcess) (n : ℕ) :
    C.regionPred n (C.target R DP n) ∧
      ∀ φ ∈ (C.fragment n).toFinset,
        |C.market R DP n φ - C.target R DP n φ| ≤ ((C.tol n : ℚ) : ℝ) :=
  sup_conformance_of_dist2 (C.isNearestPoint_targetAt n _) (C.conformance R DP n)

end RationalConstraintSchedule

/-- **The theorem of record, from a schedule of constraints.**  Given a computable
deductive process, a computable schedule of rational convex constraints, an effective
max–min representation of its projectors, and the one genuine normative assumption — that
every date's region admits every world the process leaves plausible — the modified market
is a logical inductor **in the source's original sense**, and at every date its displayed
prices lie within the requested tolerance of the day's region.

Compared with `ProjectionEffective.end_to_end_of_computation`, the region, the target, the
nearest-point property, the fragment-locality, the cube bound and the representation
correctness at the day's prices are all gone: they are theorems about the schedule, not
inputs to it. -/
theorem end_to_end_of_constraints (C : RationalConstraintSchedule) (hC : C.Computation)
    (R : RegionRepresentation C) (hR : R.Effective) {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP)
    (hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → C.regionPred n v.payout) :
    IsLogicalInductor (C.market R DP) DP ∧
      (∀ n, dist2 (C.fragment n).toFinset (C.market R DP n) (C.target R DP n)
        ≤ ((C.tol n : ℚ) : ℝ)) ∧
      ∀ n, C.regionPred n (C.target R DP n) ∧
        ∀ φ ∈ (C.fragment n).toFinset,
          |C.market R DP n φ - C.target R DP n φ| ≤ ((C.tol n : ℚ) : ℝ) :=
  end_to_end_of_computation (C.schedule R) process (C.scheduleComputation R hC hR)
    (fun n => C.fragmentLocal n) (fun n => C.regionPred_cube n)
    (fun n => C.isNearestPoint_targetAt n _) (fun n => C.repEval_market R DP n) hadm

/-- **Finite-time conformance from the constraints alone.**  Specialised to the canonical
representation, the conformance theorem has *no hypotheses whatever*: given any schedule of
rational convex constraints and any deductive process, there is a modified market — derived
from the constraints and nothing else — whose displayed prices sit within the requested
tolerance of the day's region at every date.  This is the statement that shows nothing about
the geometry is being assumed. -/
theorem conformance_of_constraints (C : RationalConstraintSchedule)
    (DP : DeductiveProcess) (n : ℕ) :
    dist2 (C.fragment n).toFinset (C.market C.canonicalRepresentation DP n)
        (C.target C.canonicalRepresentation DP n) ≤ ((C.tol n : ℚ) : ℝ) :=
  C.conformance _ DP n

/-- **The criterion from the constraints alone**, with no hypotheses either: the day's
target satisfies the day's constraint, and the displayed prices agree with it to within the
requested tolerance on every priced sentence. -/
theorem criterion_of_constraints (C : RationalConstraintSchedule)
    (DP : DeductiveProcess) (n : ℕ) :
    C.regionPred n (C.target C.canonicalRepresentation DP n) ∧
      ∀ φ ∈ (C.fragment n).toFinset,
        |C.market C.canonicalRepresentation DP n φ
          - C.target C.canonicalRepresentation DP n φ| ≤ ((C.tol n : ℚ) : ℝ) :=
  C.criterion _ DP n

/-- **Eventual coherence, from a schedule of constraints.**  If the fragments exhaust the
sentences and the tolerances vanish, then on every fixed finite set of sentences the
displayed prices eventually agree, to within any slack, with a point the day's constraint
admits.  The paper's closing consequence, and it needs nothing beyond `criterion` — in
particular no effectiveness. -/
theorem eventual_coherence_of_constraints (C : RationalConstraintSchedule)
    (R : RegionRepresentation C) (DP : DeductiveProcess)
    (hexh : ∀ Ψ : Finset Sentence, ∃ N, ∀ n, N ≤ n → Ψ ⊆ (C.fragment n).toFinset)
    (hvanish : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n → ((C.tol n : ℚ) : ℝ) ≤ ε)
    (Ψ : Finset Sentence) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n, N ≤ n → ∃ y, C.regionPred n y ∧ ∀ φ ∈ Ψ, |C.market R DP n φ - y φ| ≤ ε :=
  (C.schedule R).eventual_coherence DP (fun n => C.criterion R DP n) hexh hvanish Ψ hε

/-! ## Nonvacuity

`AGENTS.md` standard 3: the statements above ship with a term inhabiting their hypothesis
package.  The package is a constraint schedule, its computability, a representation of its
projectors, that representation's effectiveness, and the admissibility hypothesis, and the
witness below inhabits all five at once — with the *canonical* representation, so the
effectiveness it certifies is effectiveness of the object the theorems actually run on.

It is deliberately the *degenerate* schedule — the empty fragment, constrained to the single
point of its zero-dimensional coordinate space.  A non-degenerate witness would have to
exhibit an effective max–min representation of a genuine projector, which is precisely the
content `RegionRepresentation.Effective` is still assuming; a witness that assumed it would
certify nothing.  What this one certifies is that the five hypotheses are jointly
consistent, which is what standard 3 asks and all it asks.  Note that the representation's
*correctness* needs no witness at all: `exists_representation` gives it for every schedule,
degenerate or not. -/

/-- The single point of the zero-dimensional coordinate space, as a polytope. -/
def pointPolytope : RationalPolytope 0 where
  verts := [fun i => i.elim0]
  verts_ne := List.cons_ne_nil _ _

/-- The degenerate constraint schedule: nothing priced, and the vacuous constraint. -/
def emptySchedule : RationalConstraintSchedule where
  coords := fun _ => []
  nodup := fun _ => List.nodup_nil
  tol := fun _ => 1
  tol_pos := fun _ => one_pos
  region := fun _ => pointPolytope
  region_in_cube := fun _ _ _ i => i.elim0

/-- The degenerate schedule is computable. -/
def emptyComputation : emptySchedule.Computation where
  coordsComputable := Primrec.const _
  tolComputable := Primrec.const _
  vertsComputable := (Primrec.const [([] : List ℚ)]).of_eq fun _ => rfl

/-- With nothing priced, the canonical representation — the one the bridge produces, and the
one `conformance_of_constraints` runs on — is effective: its representation list is the
image of the empty fragment, so the constant compiler returns it. -/
def emptyEffective : emptySchedule.canonicalRepresentation.Effective where
  compile := fun _ _ => []
  compileComputable := (Primrec.const _).to₂
  reps_eq := fun _ => rfl

/-- The degenerate schedule admits every world: the constraint is on no coordinate. -/
theorem emptySchedule_admits (DP : DeductiveProcess) (n : ℕ) (v : PCWorld) :
    v.ConsistentWith (DP.D n) → emptySchedule.regionPred n v.payout := by
  intro _
  refine RationalPolytope.vertexSet_subset_carrier _ ⟨fun i => i.elim0, ?_, ?_⟩
  · show (fun i : Fin 0 => i.elim0) ∈ pointPolytope.verts
    simp [pointPolytope]
  · unfold toPt restrict
    congr 1
    funext i
    exact i.elim0

/-- **The hypothesis package of `end_to_end_of_constraints` is inhabited.** -/
theorem hypotheses_nonvacuous :
    ∃ (C : RationalConstraintSchedule) (_ : C.Computation) (R : RegionRepresentation C)
      (_ : R.Effective),
      ∀ (DP : DeductiveProcess) n (v : PCWorld),
        v.ConsistentWith (DP.D n) → C.regionPred n v.payout :=
  ⟨emptySchedule, emptyComputation, emptySchedule.canonicalRepresentation, emptyEffective,
    emptySchedule_admits⟩

end Workspace.Normativity.Contrib.ConstraintSchedule

#print axioms Workspace.Normativity.Contrib.ConstraintSchedule.ip_eq_inner
#print axioms Workspace.Normativity.Contrib.ConstraintSchedule.fragmentLocal_regionPred
#print axioms Workspace.Normativity.Contrib.ConstraintSchedule.regionPred_mem_cube
#print axioms Workspace.Normativity.Contrib.ConstraintSchedule.restrict_target
#print axioms Workspace.Normativity.Contrib.ConstraintSchedule.isNearestPoint_target
#print axioms
  Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.fragmentLocal
#print axioms
  Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.regionPred_cube
#print axioms
  Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.isNearestPoint_targetAt
#print axioms
  Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.scheduleComputation
#print axioms
  Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.conformance
#print axioms
  Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.criterion
#print axioms
  Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.canonicalRepresentation
#print axioms Workspace.Normativity.Contrib.ConstraintSchedule.exists_representation
#print axioms Workspace.Normativity.Contrib.ConstraintSchedule.conformance_of_constraints
#print axioms Workspace.Normativity.Contrib.ConstraintSchedule.criterion_of_constraints
#print axioms Workspace.Normativity.Contrib.ConstraintSchedule.end_to_end_of_constraints
#print axioms Workspace.Normativity.Contrib.ConstraintSchedule.eventual_coherence_of_constraints
#print axioms Workspace.Normativity.Contrib.ConstraintSchedule.hypotheses_nonvacuous
