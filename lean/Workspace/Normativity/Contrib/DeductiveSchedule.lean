/-
# The deductive constraint schedule

`ConstraintSchedule` asks the reader for a schedule of rational polytopes and derives
everything else from it.  `DeductiveRegion` computes, from a stage of the deductive
process and a finite fragment, the exact vertex list of the day's deductive coherence
region.  This file is the join: it feeds the second into the first, so that the paper's
constraint is no longer *supplied* but *read off the deductive process*.

**What that buys.**  A `RationalConstraintSchedule` is the whole input to the
construction apart from the process itself, and it has one field that a reader could get
wrong — `region`.  Here the region is not a choice.  Given the process, the fragment
schedule and the tolerance schedule, the day-`n` region is

```
conv { W|_{Φ_n} : W ∈ PC(D_n) }
```

and the only remaining hypothesis is that each stage is propositionally satisfiable —
which is ambient in the paper's notion of a deductive process, and which is exactly the
hypothesis `admissiblePatterns_ne_nil_iff` shows nonemptiness of the vertex list to be
equivalent to.  Nothing weaker would do: an inconsistent stage has no admissible world,
so there is no region to project onto, and `RationalPolytope` would have no vertices.

**The load-bearing lemma is `regionPred_eq_deductiveRegion`.**  The two files describe
the same set through different plumbing.  `ConstraintSchedule` reads a price vector as a
point of `EuclideanSpace ℝ (Fin (coords n).length)` and asks for membership in the convex
hull of `toPt`-images of rational vertices; `DeductiveRegion` reads it as a plain
function `Fin (coords n).length → ℝ` and asks for membership in the convex hull of the
`vertex`-images.  `WithLp.toLp 2` is the linear equivalence between the two, and
`IsLinearMap.image_convexHull` pushes the hull through it.  Once that is proved, the
normative input of `end_to_end_of_constraints` — that the day's region admits every world
the process leaves plausible — is `payout_mem_deductiveRegion`, a theorem, and
`hadm_of_deductive` discharges it.

**What is still open, precisely.**  `RationalConstraintSchedule.Computation` asks for
`Primrec` of the fragment schedule, the tolerance schedule and the flat vertex data.  The
first two are hypotheses a caller supplies about its own data.  The third is *not*
available here, and the reason is worth stating rather than hiding:

* `DeductiveProcessComputation DP` in the pinned dependency is a `Nat.Partrec.Code`
  together with `∀ n, Encodable.encode (DP.D n) ∈ code.eval n` — a partial recursive
  program that eventually emits the stage.  It does not give `Primrec DP.D`, so it cannot
  be the source of the missing computability.
* Even given `Primrec DP.D` (which is statable: `Primcodable (Finset Sentence)` exists in
  the dependency), the remaining obligation is
  `Primrec fun n => admissiblePatterns (DP.D n) (coords n)`.  Unfolding
  `admissiblePatterns`, that needs `Primrec` for `Sentence.atoms` (structural recursion
  into `Finset ℕ`), for `sentenceBool` and hence `tableConsistent` (structural recursion
  over the propositional formula), and for `contextList`'s `Finset` operations.  The
  dependency proves exactly these facts — `sentenceBoolFromAtomList_prim`,
  `tableConsistentFromAtomList_prim` and the `formulaBoolDecoded` strong-recursion tower
  in `LogicalInduction/Construction/LIACompiler.lean` — but every one of them is
  `private`, so none is usable from here.  Reproducing them is a piece of work in its own
  right and is deliberately not attempted: no axiom is introduced, `Computation` is not
  weakened, and no deductive specialisation of `end_to_end_of_constraints` is claimed.

The two theorems that need **no** computability — `conformance_of_constraints` and
`criterion_of_constraints` — are specialised here in full, and they are the ones that carry
the paper's finite-time content.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.ConstraintSchedule
import Workspace.Normativity.Contrib.DeductiveRegion

namespace Workspace.Normativity.Contrib.DeductiveSchedule

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Workspace.Normativity.Contrib.RationalPolytope
open Workspace.Normativity.Contrib.ProjectionForce
open Workspace.Normativity.Contrib.ProjectionCompiler
open Workspace.Normativity.Contrib.ProjectionBridge
open Workspace.Normativity.Contrib.ConstraintSchedule
open Workspace.Normativity.Contrib.DeductiveRegion

/-! ## The vertex list as rational data

`DeductiveRegion` produces patterns as `List ℚ` and reads them into `Fin n → ℝ`;
`RationalPolytope` wants `Fin n → ℚ` and does the real coercion itself.  `ratVertex` is
the half of `vertex` that stops short of `ℝ`, so that the two agree on the nose. -/

/-- A rational `{0,1}` pattern read as a rational coordinate vector.  Out-of-range indices
read `0`; `admissiblePatterns_length` says there are none. -/
def ratVertex (coords : List Sentence) (w : List ℚ) : Fin coords.length → ℚ :=
  fun i => w.getD i.val 0

/-- `ratVertex` is `DeductiveRegion.vertex` with the coercion to `ℝ` deferred to `toPt`. -/
lemma toPt_ratVertex (coords : List Sentence) (w : List ℚ) :
    toPt (ratVertex coords w) = WithLp.toLp 2 (vertex coords w) := rfl

/-- Every coordinate of an admissible pattern lies in `[0,1]`.  The pattern's entries are
`0` or `1` by `admissiblePatterns_mem_cube`; the `getD` default is never reached because
`admissiblePatterns_length` puts every index in range. -/
lemma ratVertex_mem_cube (D : Finset Sentence) (coords : List Sentence) {w : List ℚ}
    (hw : w ∈ admissiblePatterns D coords) (i : Fin coords.length) :
    0 ≤ ratVertex coords w i ∧ ratVertex coords w i ≤ 1 := by
  have hlen : w.length = coords.length := admissiblePatterns_length D coords hw
  have hlt : i.val < w.length := by rw [hlen]; exact i.isLt
  have hget : ratVertex coords w i = w[i.val] := List.getD_eq_getElem _ _ hlt
  rcases admissiblePatterns_mem_cube D coords hw (List.getElem_mem hlt) with h | h <;>
    rw [hget, h] <;> norm_num

/-- **The day's region as a rational polytope.**  Its vertices are exactly the `{0,1}`
patterns on the fragment realised by a propositionally consistent world satisfying the
stage.  Nonemptiness is the stage's satisfiability and nothing else. -/
def deductivePolytope (D : Finset Sentence) (coords : List Sentence)
    (hD : ∃ v : PCWorld, v.ConsistentWith D) : RationalPolytope coords.length where
  verts := (admissiblePatterns D coords).map (ratVertex coords)
  verts_ne := fun h => admissiblePatterns_nonempty D coords hD (by simpa using h)

@[simp] lemma verts_deductivePolytope (D : Finset Sentence) (coords : List Sentence)
    (hD : ∃ v : PCWorld, v.ConsistentWith D) :
    (deductivePolytope D coords hD).verts
      = (admissiblePatterns D coords).map (ratVertex coords) := rfl

/-! ## The schedule

Everything a `RationalConstraintSchedule` asks for, with `region` no longer a free
parameter: the fragment schedule and the tolerance schedule are the caller's, and the
region is computed from the process. -/

/-- **The deductive constraint schedule.**  The day-`n` constraint is the convex hull of
the fragment restrictions of the worlds the day's stage leaves plausible.  The only
hypothesis beyond the fragment and tolerance data is that each stage is propositionally
satisfiable. -/
def deductiveSchedule (DP : DeductiveProcess) (coords : ℕ → List Sentence)
    (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
    (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    RationalConstraintSchedule where
  coords := coords
  nodup := nodup
  tol := tol
  tol_pos := tol_pos
  region := fun n => deductivePolytope (DP.D n) (coords n) (hsat n)
  region_in_cube := fun n v hv i => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp
      (show v ∈ (admissiblePatterns (DP.D n) (coords n)).map (ratVertex (coords n)) from hv)
    exact ratVertex_mem_cube _ _ hw i

section

variable (DP : DeductiveProcess) (coords : ℕ → List Sentence)
  (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
  (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))

@[simp] lemma deductiveSchedule_coords (n : ℕ) :
    (deductiveSchedule DP coords nodup tol tol_pos hsat).coords n = coords n := rfl

@[simp] lemma deductiveSchedule_tol (n : ℕ) :
    (deductiveSchedule DP coords nodup tol tol_pos hsat).tol n = tol n := rfl

end

/-! ## The two descriptions of the region agree

`ConstraintSchedule.regionPred` lives in `EuclideanSpace ℝ (Fin d)`, which is
`WithLp 2 (Fin d → ℝ)`; `DeductiveRegion.deductiveRegion` lives in `Fin d → ℝ`.  The
transport is `WithLp.toLp 2`, a linear equivalence, so the convex hull passes through it
and injectivity brings membership back. -/

/-- `WithLp.toLp 2` into the fragment's Euclidean space is linear.  Both fields are `rfl`:
the module structure on `WithLp` is transported along the equivalence. -/
lemma isLinearMap_toLp (d : ℕ) :
    IsLinearMap ℝ (WithLp.toLp 2 : (Fin d → ℝ) → Pt d) where
  map_add _ _ := rfl
  map_smul _ _ := rfl

/-- The polytope's vertex set is the deductive vertex set, transported. -/
lemma vertexSet_deductivePolytope (D : Finset Sentence) (coords : List Sentence)
    (hD : ∃ v : PCWorld, v.ConsistentWith D) :
    (deductivePolytope D coords hD).vertexSet
      = (WithLp.toLp 2 : (Fin coords.length → ℝ) → Pt coords.length)
          '' deductiveVertices D coords := by
  ext x
  simp only [RationalPolytope.vertexSet, verts_deductivePolytope, deductiveVertices,
    Set.mem_image, Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨vertex coords w, ⟨w, hw, rfl⟩, (toPt_ratVertex coords w).symm⟩
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨ratVertex coords w, ⟨w, hw, rfl⟩, toPt_ratVertex coords w⟩

/-- **Membership transports.**  A coordinate vector lies in the deductive hull exactly when
its image in the Euclidean space lies in the polytope's carrier.  This is where the
convex hull is pushed through the linear equivalence, and injectivity brings it back. -/
lemma toLp_mem_carrier_iff (D : Finset Sentence) (coords : List Sentence)
    (hD : ∃ v : PCWorld, v.ConsistentWith D) (x : Fin coords.length → ℝ) :
    WithLp.toLp 2 x ∈ (deductivePolytope D coords hD).carrier
      ↔ x ∈ convexHull ℝ (deductiveVertices D coords) := by
  rw [RationalPolytope.carrier, vertexSet_deductivePolytope,
    ← (isLinearMap_toLp coords.length).image_convexHull, Set.mem_image]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [WithLp.toLp_injective 2 hxy] at hy
  · intro h
    exact ⟨x, h, rfl⟩

/-- A price vector restricted to a fragment is its `DeductiveRegion` restriction, read into
the Euclidean space.  `List.get` and `getElem` agree definitionally, so this is `rfl`. -/
lemma restrict_eq_toLp_restrictTo (F : Fragment) (p : Sentence → ℝ) :
    restrict F p = WithLp.toLp 2 (restrictTo F.coords p) := rfl

/-- **The two region predicates are the same predicate.**  The constraint schedule's
day-`n` constraint on price vectors is exactly the day-`n` deductive coherence region. -/
theorem regionPred_eq_deductiveRegion (DP : DeductiveProcess) (coords : ℕ → List Sentence)
    (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
    (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) (p : Sentence → ℝ) :
    (deductiveSchedule DP coords nodup tol tol_pos hsat).regionPred n p
      ↔ deductiveRegion (DP.D n) (coords n) p :=
  toLp_mem_carrier_iff (DP.D n) (coords n) (hsat n) (restrictTo (coords n) p)

/-! ## The normative hypothesis is a theorem

`end_to_end_of_constraints` takes one genuinely normative input: that the day's region
admits every world the process leaves plausible.  For the deductive schedule that is
`payout_mem_deductiveRegion` read through the lemma above — the region was *built* from
those worlds. -/

/-- **The admissibility hypothesis, discharged.**  Every world the day's stage leaves
plausible has its payout vector in the day's region. -/
theorem hadm_of_deductive (DP : DeductiveProcess) (coords : ℕ → List Sentence)
    (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
    (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      (deductiveSchedule DP coords nodup tol tol_pos hsat).regionPred n v.payout :=
  fun n v hv =>
    (regionPred_eq_deductiveRegion DP coords nodup tol tol_pos hsat n v.payout).mpr
      (payout_mem_deductiveRegion (DP.D n) (coords n) v hv)

/-! ## The market and its target

Names for the two objects the theorems below speak about.  Both are `rfl`-equal to the
constraint schedule's, and the `simp` lemmas say so: nothing is hidden behind them, they
only keep the statements readable. -/

/-- The deductive schedule's market: the source deductive firm priced together with the
enforcer the deductive regions generate, using the canonical representation. -/
noncomputable def deductiveMarket (DP : DeductiveProcess) (coords : ℕ → List Sentence)
    (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
    (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) : History :=
  (deductiveSchedule DP coords nodup tol tol_pos hsat).market
    (deductiveSchedule DP coords nodup tol tol_pos hsat).canonicalRepresentation DP

/-- The deductive schedule's target: the projection of the day's displayed price onto the
day's deductive region. -/
noncomputable def deductiveTarget (DP : DeductiveProcess) (coords : ℕ → List Sentence)
    (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
    (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) : Sentence → ℝ :=
  (deductiveSchedule DP coords nodup tol tol_pos hsat).target
    (deductiveSchedule DP coords nodup tol tol_pos hsat).canonicalRepresentation DP n

/-- `deductiveMarket` is the constraint schedule's market — the name hides nothing. -/
lemma deductiveMarket_eq (DP : DeductiveProcess) (coords : ℕ → List Sentence)
    (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
    (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    deductiveMarket DP coords nodup tol tol_pos hsat
      = (deductiveSchedule DP coords nodup tol tol_pos hsat).market
          (deductiveSchedule DP coords nodup tol tol_pos hsat).canonicalRepresentation DP :=
  rfl

/-- `deductiveTarget` is the constraint schedule's target — the name hides nothing. -/
lemma deductiveTarget_eq (DP : DeductiveProcess) (coords : ℕ → List Sentence)
    (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
    (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    deductiveTarget DP coords nodup tol tol_pos hsat n
      = (deductiveSchedule DP coords nodup tol tol_pos hsat).target
          (deductiveSchedule DP coords nodup tol tol_pos hsat).canonicalRepresentation
          DP n :=
  rfl

/-! ## The two hypothesis-free theorems, deductively

`conformance_of_constraints` and `criterion_of_constraints` take a constraint schedule and
a deductive process and nothing else.  Specialised to `deductiveSchedule` they take a
deductive process, a fragment schedule, a tolerance schedule, and the stages'
satisfiability — no computability, no admissibility, no supplied region, no supplied
representation. -/

/-- **Finite-time conformance from the deductive process alone.**  At every date the
displayed price is within the requested tolerance of the day's deductive coherence region,
in the intrinsic Euclidean distance on the day's fragment. -/
theorem conformance_of_deductive (DP : DeductiveProcess) (coords : ℕ → List Sentence)
    (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
    (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    dist2 ((deductiveSchedule DP coords nodup tol tol_pos hsat).fragment n).toFinset
        (deductiveMarket DP coords nodup tol tol_pos hsat n)
        (deductiveTarget DP coords nodup tol tol_pos hsat n)
      ≤ ((tol n : ℚ) : ℝ) :=
  conformance_of_constraints (deductiveSchedule DP coords nodup tol tol_pos hsat) DP n

/-- **The criterion from the deductive process alone.**  The day's target satisfies the
day's deductive constraint, and the displayed prices agree with it to within the requested
tolerance on every priced sentence. -/
theorem criterion_of_deductive (DP : DeductiveProcess) (coords : ℕ → List Sentence)
    (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
    (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    (deductiveSchedule DP coords nodup tol tol_pos hsat).regionPred n
        (deductiveTarget DP coords nodup tol tol_pos hsat n) ∧
      ∀ φ ∈ ((deductiveSchedule DP coords nodup tol tol_pos hsat).fragment n).toFinset,
        |deductiveMarket DP coords nodup tol tol_pos hsat n φ
          - deductiveTarget DP coords nodup tol tol_pos hsat n φ| ≤ ((tol n : ℚ) : ℝ) :=
  criterion_of_constraints (deductiveSchedule DP coords nodup tol tol_pos hsat) DP n

/-- **The criterion, with the constraint named.**  The same statement with the first
conjunct read through `DeductiveRegion.deductiveRegion`: the day's target is a convex
combination of the fragment restrictions of the worlds the day's stage leaves plausible,
and the displayed prices are within tolerance of it on every priced sentence. -/
theorem criterion_deductiveRegion (DP : DeductiveProcess) (coords : ℕ → List Sentence)
    (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
    (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    deductiveRegion (DP.D n) (coords n)
        (deductiveTarget DP coords nodup tol tol_pos hsat n) ∧
      ∀ φ ∈ ((deductiveSchedule DP coords nodup tol tol_pos hsat).fragment n).toFinset,
        |deductiveMarket DP coords nodup tol tol_pos hsat n φ
          - deductiveTarget DP coords nodup tol tol_pos hsat n φ| ≤ ((tol n : ℚ) : ℝ) := by
  obtain ⟨hreg, hsup⟩ := criterion_of_deductive DP coords nodup tol tol_pos hsat n
  exact ⟨(regionPred_eq_deductiveRegion DP coords nodup tol tol_pos hsat n _).mp hreg,
    hsup⟩

/-! ## Nonvacuity

`AGENTS.md` standard 3: the statements above ship with a term inhabiting their hypothesis
package.  The package is a deductive process whose every stage is propositionally
satisfiable, together with a duplicate-free fragment schedule and a positive tolerance
schedule.  The witness below is non-degenerate on the fragment side — a sentence is priced
at every date — and the region it produces is a genuine one-dimensional segment rather
than a point. -/

/-- The empty deductive process: no stage asserts anything. -/
def emptyProcess : DeductiveProcess where
  D := fun _ => ∅
  mono := fun _ => Finset.Subset.refl _

lemma emptyProcess_sat (n : ℕ) : ∃ v : PCWorld, v.ConsistentWith (emptyProcess.D n) :=
  ⟨witnessWorld, fun _ hφ => absurd hφ (Finset.notMem_empty _)⟩

/-- **The hypothesis package is inhabited, non-degenerately.**  There is a deductive
process, a fragment schedule pricing a sentence at every date, and a tolerance schedule,
satisfying every hypothesis the theorems above take — and the resulting region has two
vertices, so the constraint is not vacuous. -/
theorem hypotheses_nonvacuous :
    ∃ (DP : DeductiveProcess) (coords : ℕ → List Sentence)
      (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
      (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)),
      (∀ n, coords n ≠ []) ∧
        ∀ n, ((deductiveSchedule DP coords nodup tol tol_pos hsat).region n).verts.length
          = 2 := by
  refine ⟨emptyProcess, fun _ => [atomP], fun _ => List.nodup_singleton _, fun _ => 1,
    fun _ => one_pos, emptyProcess_sat, fun _ => List.cons_ne_nil _ _, fun n => ?_⟩
  have hval : admissiblePatterns (∅ : Finset Sentence) [atomP] = [[0], [1]] := by
    decide +kernel
  show ((admissiblePatterns (∅ : Finset Sentence) [atomP]).map
    (ratVertex [atomP])).length = 2
  rw [hval]
  rfl

end Workspace.Normativity.Contrib.DeductiveSchedule

#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.ratVertex
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.toPt_ratVertex
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.ratVertex_mem_cube
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.deductivePolytope
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.verts_deductivePolytope
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.deductiveSchedule
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.isLinearMap_toLp
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.vertexSet_deductivePolytope
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.toLp_mem_carrier_iff
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.restrict_eq_toLp_restrictTo
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.regionPred_eq_deductiveRegion
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.hadm_of_deductive
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.deductiveMarket_eq
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.deductiveTarget_eq
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.conformance_of_deductive
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.criterion_of_deductive
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.criterion_deductiveRegion
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.emptyProcess_sat
#print axioms Workspace.Normativity.Contrib.DeductiveSchedule.hypotheses_nonvacuous
