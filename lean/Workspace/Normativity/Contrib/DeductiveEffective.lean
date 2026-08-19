/-
# The deductive coherence schedule, effectively

`DeductiveSchedule` closes the semantic half: the constraint schedule's region *is* the
deductive region, admissibility is discharged from `payout_mem_deductiveRegion`, and
conformance and the criterion specialise with their conclusions unchanged.  What it does
not do is produce the market as a computable object, and the reason was an interface
artifact rather than a fact about the mathematics.

`RationalConstraintSchedule.Computation` asks for the day's region as a primitive recursive
function of the *date*.  For a region read off the deductive stage that is
`Primrec (fun n => DP.D n)`, and the pinned source's `DeductiveProcessComputation` does not
supply it: it is a partial recursive program that merely *eventually* emits the stage, and
no amount of fuel search turns that into a primitive recursive function of the date.

But the compiler never needed it.  It already carries the stage table as finite data — the
recurrence runs against an explicit `D : ℕ → Finset Sentence`, instantiated at
`decodedStageTable`, which is `fun stages n => stages.getD n ∅` — and the source's own
Trading Firm reads stages exactly that way.  Once the enforcer and the schedule's
representation may read the day's stage too, the region is computed from finite data the
compiler holds, and **no hypothesis about `DP` beyond the source's own is needed**.

That is what this file records.  `deductiveReps` is the day's representation computed from
the stage and the fragment; it is primitive recursive in both, by the enumeration's
computability and the projector generator's compiler.  The schedule built from it is a
`ProjectionSchedule` whose `ProjectionScheduleComputation` follows from the fragment and
tolerance schedules alone.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.EffectiveRepresentation
import Workspace.Normativity.Contrib.DeductiveSchedule

namespace Workspace.Normativity.Contrib.DeductiveEffective

open LogicalInduction
open Workspace.Normativity.Contrib.ProjectionForce
open Workspace.Normativity.Contrib.ProjectionCompiler
open Workspace.Normativity.Contrib.ProjectionEnforcer
open Workspace.Normativity.Contrib.DeductiveRegion
open Workspace.Normativity.Contrib.RationalPolytope
open Workspace.Normativity.Contrib.DeductiveSchedule
open Workspace.Normativity.Contrib.EnforcedComputation
open Workspace.Normativity.Contrib.EnforcedCompiler
open Workspace.Normativity.Contrib.EffectiveRepresentation

/-! ## The enumeration is primitive recursive

Every step is the dependency's, re-exported: the atoms of a stage and a fragment, the
enumeration of Boolean assignments, propositional evaluation against an atom-list table,
and finite consistency against one. -/

lemma contextAtoms_primrec :
    Primrec fun p : Finset Sentence × List Sentence => contextAtoms p.1 p.2 :=
  sentenceListAtoms_primrec.comp
    (Primrec.list_append.comp (supportSentenceList_primrec.comp Primrec.fst) Primrec.snd)

/-- The day's patterns, as a primitive recursive function of the stage and the fragment. -/
lemma admissiblePatternsEff_primrec :
    Primrec fun p : Finset Sentence × List Sentence => admissiblePatternsEff p.1 p.2 := by
  have hatoms : Primrec fun p : Finset Sentence × List Sentence => contextAtoms p.1 p.2 :=
    contextAtoms_primrec
  have hbools : Primrec fun p : Finset Sentence × List Sentence =>
      allBoolLists (contextAtoms p.1 p.2).length :=
    allBoolLists_primrec.comp (Primrec.list_length.comp hatoms)
  -- the consistency filter
  have hkeep : Primrec₂ fun (p : Finset Sentence × List Sentence) (xs : List Bool) =>
      tableConsistent (tableOf (contextAtoms p.1 p.2) xs) p.1 := by
    have h : Primrec fun z : (Finset Sentence × List Sentence) × List Bool =>
        tableConsistent (atomTableFromList (contextAtoms z.1.1 z.1.2) z.2) z.1.1 :=
      tableConsistent_atomTableFromList_primrec.comp
        (((hatoms.comp Primrec.fst).pair Primrec.snd).pair
          (Primrec.fst.comp (Primrec.fst)))
    exact h.to₂
  have hfilter : Primrec fun p : Finset Sentence × List Sentence =>
      (allBoolLists (contextAtoms p.1 p.2).length).filter fun xs =>
        tableConsistent (tableOf (contextAtoms p.1 p.2) xs) p.1 :=
    list_filter_prim hbools hkeep
  -- the payout read-off
  have hrow : Primrec₂ fun (p : Finset Sentence × List Sentence) (xs : List Bool) =>
      p.2.map (boolPayoutRat (tableOf (contextAtoms p.1 p.2) xs)) := by
    have hentry : Primrec₂ fun (z : (Finset Sentence × List Sentence) × List Bool)
        (φ : Sentence) =>
        boolPayoutRat (tableOf (contextAtoms z.1.1 z.1.2) z.2) φ := by
      have hsb : Primrec fun w : ((Finset Sentence × List Sentence) × List Bool) × Sentence =>
          sentenceBool (atomTableFromList (contextAtoms w.1.1.1 w.1.1.2) w.1.2) w.2 :=
        sentenceBool_atomTableFromList_primrec.comp
          (((hatoms.comp (Primrec.fst.comp Primrec.fst)).pair
            (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
      have h : Primrec fun w : ((Finset Sentence × List Sentence) × List Bool) × Sentence =>
          boolPayoutRat (tableOf (contextAtoms w.1.1.1 w.1.1.2) w.1.2) w.2 := by
        refine (Primrec.cond hsb (Primrec.const (1 : ℚ)) (Primrec.const 0)).of_eq fun w => ?_
        unfold boolPayoutRat tableOf
        cases hb : sentenceBool
            (atomTableFromList (contextAtoms w.1.1.1 w.1.1.2) w.1.2) w.2 <;> simp [hb]
      exact h.to₂
    have h : Primrec fun z : (Finset Sentence × List Sentence) × List Bool =>
        z.1.2.map (boolPayoutRat (tableOf (contextAtoms z.1.1 z.1.2) z.2)) :=
      Primrec.list_map (Primrec.snd.comp Primrec.fst) hentry
    exact h.to₂
  exact Primrec.list_map hfilter hrow


/-! ## The day's region and its representation

The region is the deductive polytope built from the *effective* enumeration.  Its vertex
data is that enumeration back again — `List.ofFn (ratVertex coords w) = w` whenever `w` has
one entry per coordinate, which `patternsFrom_length` supplies — so the compiler's input is
exactly what the enumeration produced, with no re-encoding in between. -/

/-- The day's region, from the effective enumeration. -/
def deductivePolytopeEff (D : Finset Sentence) (coords : List Sentence)
    (hD : ∃ v : PCWorld, v.ConsistentWith D) : RationalPolytope coords.length where
  verts := (admissiblePatternsEff D coords).map (ratVertex coords)
  verts_ne := fun h => by
    refine (admissiblePatternsEff_ne_nil_iff D coords).mpr hD ?_
    simpa using h

@[simp] lemma verts_deductivePolytopeEff (D : Finset Sentence) (coords : List Sentence)
    (hD : ∃ v : PCWorld, v.ConsistentWith D) :
    (deductivePolytopeEff D coords hD).verts
      = (admissiblePatternsEff D coords).map (ratVertex coords) := rfl

/-- **The vertex data is the enumeration itself.** -/
theorem vertexData_deductivePolytopeEff (D : Finset Sentence) (coords : List Sentence)
    (hD : ∃ v : PCWorld, v.ConsistentWith D) :
    (deductivePolytopeEff D coords hD).verts.map List.ofFn = admissiblePatternsEff D coords := by
  show ((admissiblePatternsEff D coords).map (ratVertex coords)).map List.ofFn = _
  rw [List.map_map]
  refine Eq.trans (List.map_congr_left (g := id) fun w hw => ?_) (List.map_id _)
  have hlen : w.length = coords.length := admissiblePatternsEff_length D coords hw
  show List.ofFn (ratVertex coords w) = w
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  simp only [List.getElem_ofFn, ratVertex]
  exact List.getD_eq_getElem _ _ h2

/-- **The day's representation**, computed from the stage and the fragment. -/
def deductiveReps (D : Finset Sentence) (coords : List Sentence) : List Rep :=
  compileOf coords (admissiblePatternsEff D coords)

/-- **It is primitive recursive in both**, and in nothing else. -/
theorem deductiveReps_primrec : Primrec₂ deductiveReps := by
  have h : Primrec fun p : Finset Sentence × List Sentence =>
      compileOf p.2 (admissiblePatternsEff p.1 p.2) :=
    compileOf_primrec.comp Primrec.snd admissiblePatternsEff_primrec
  exact h.to₂

/-- **The representation is correct**: it evaluates to the projection of the displayed
price onto the day's deductive region. -/
theorem repEval_deductiveReps (D : Finset Sentence) (coords : List Sentence)
    (nodup : coords.Nodup) (hD : ∃ v : PCWorld, v.ConsistentWith D)
    {φ : Sentence} (hφ : φ ∈ coords) (p : Sentence → ℝ) :
    repEval ⟨coords, nodup⟩ (repAt coords (deductiveReps D coords) default φ) p
      = (deductivePolytopeEff D coords hD).proj
          (ProjectionBridge.restrict ⟨coords, nodup⟩ p)
          ⟨coords.idxOf φ, List.idxOf_lt_length_of_mem hφ⟩ := by
  have h := repEval_compileOf ⟨coords, nodup⟩ (deductivePolytopeEff D coords hD) hφ p
  rwa [vertexData_deductivePolytopeEff D coords hD] at h


/-! ## The region is the deductive region

The effective enumeration and the kernel-facing one have the same members, so the polytopes
they build have the same vertex set and hence the same carrier.  Membership in that carrier
is `DeductiveRegion.deductiveRegion`, which is what `DeductiveSchedule` already established
for the kernel-facing polytope. -/

theorem vertexSet_deductivePolytopeEff (D : Finset Sentence) (coords : List Sentence)
    (hD hD' : ∃ v : PCWorld, v.ConsistentWith D) :
    (deductivePolytopeEff D coords hD).vertexSet
      = (DeductiveSchedule.deductivePolytope D coords hD').vertexSet := by
  unfold RationalPolytope.vertexSet
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, verts_deductivePolytopeEff,
    DeductiveSchedule.verts_deductivePolytope, List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, (mem_admissiblePatternsEff_iff_mem_admissiblePatterns D coords).mp hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, (mem_admissiblePatternsEff_iff_mem_admissiblePatterns D coords).mpr hw, rfl⟩

theorem carrier_deductivePolytopeEff (D : Finset Sentence) (coords : List Sentence)
    (hD hD' : ∃ v : PCWorld, v.ConsistentWith D) :
    (deductivePolytopeEff D coords hD).carrier
      = (DeductiveSchedule.deductivePolytope D coords hD').carrier := by
  unfold RationalPolytope.carrier
  rw [vertexSet_deductivePolytopeEff D coords hD hD']

/-- **Membership in the day's region is the deductive region.** -/
theorem mem_carrier_iff_deductiveRegion (D : Finset Sentence) (coords : List Sentence)
    (nodup : coords.Nodup) (hD : ∃ v : PCWorld, v.ConsistentWith D) (p : Sentence → ℝ) :
    ProjectionBridge.restrict ⟨coords, nodup⟩ p ∈ (deductivePolytopeEff D coords hD).carrier
      ↔ DeductiveRegion.deductiveRegion D coords p := by
  rw [carrier_deductivePolytopeEff D coords hD hD]
  exact DeductiveSchedule.toLp_mem_carrier_iff D coords hD (DeductiveRegion.restrictTo coords p)

/-- Both slots of the fragment inner product read only the fragment. -/
private lemma ip_congr {Φ : Finset Sentence} {u u' v v' : Sentence → ℝ}
    (hu : ∀ φ ∈ Φ, u φ = u' φ) (hv : ∀ φ ∈ Φ, v φ = v' φ) :
    ip Φ u v = ip Φ u' v' :=
  Finset.sum_congr rfl fun φ hφ => by rw [hu φ hφ, hv φ hφ]

/-- **The representation's value is the region's nearest point.** -/
theorem isNearestPoint_deductiveReps (D : Finset Sentence) (coords : List Sentence)
    (nodup : coords.Nodup) (hD : ∃ v : PCWorld, v.ConsistentWith D) (p : Sentence → ℝ) :
    IsNearestPoint (⟨coords, nodup⟩ : ProjectionCompiler.Fragment).toFinset
      (fun y => DeductiveRegion.deductiveRegion D coords y) p
      (fun φ => ProjectionCompiler.repEval ⟨coords, nodup⟩
        (repAt coords (deductiveReps D coords) default φ) p) := by
  classical
  set F : ProjectionCompiler.Fragment := ⟨coords, nodup⟩ with hF
  set K := deductivePolytopeEff D coords hD with hK
  set q' : Sentence → ℝ := fun φ =>
    ProjectionCompiler.repEval F (repAt coords (deductiveReps D coords) default φ) p with hq'
  have hval : ∀ φ ∈ F.toFinset, q' φ = ConstraintSchedule.target F K p φ := by
    intro φ hφ
    have hmem : φ ∈ F.coords := List.mem_toFinset.mp hφ
    show ProjectionCompiler.repEval F
      (repAt coords (deductiveReps D coords) default φ) p = _
    rw [repEval_deductiveReps D coords nodup hD hmem p]
    exact (ConstraintSchedule.target_mem F K p hmem).symm
  have hbase := ConstraintSchedule.isNearestPoint_target F K p
  refine ⟨?_, ?_⟩
  · have h1 : ProjectionBridge.restrict F q' = ProjectionBridge.restrict F
        (ConstraintSchedule.target F K p) := ConstraintSchedule.restrict_congr hval
    refine (mem_carrier_iff_deductiveRegion D coords nodup hD q').mp ?_
    rw [h1]
    exact hbase.1
  · intro y hy
    have hy' : ConstraintSchedule.regionPred F K y :=
      (mem_carrier_iff_deductiveRegion D coords nodup hD y).mpr hy
    refine le_of_le_of_eq ?_ (rfl : (0 : ℝ) = 0)
    calc ip F.toFinset (fun φ => p φ - q' φ) (fun φ => y φ - q' φ)
        = ip F.toFinset (fun φ => p φ - ConstraintSchedule.target F K p φ)
            (fun φ => y φ - ConstraintSchedule.target F K p φ) :=
          ip_congr (fun φ hφ => by rw [hval φ hφ]) (fun φ hφ => by rw [hval φ hφ])
      _ ≤ 0 := hbase.2 y hy'


/-! ## The effective deductive schedule

Everything the construction needs, from data the caller actually has: which sentences are
priced, how closely, that each stage is propositionally satisfiable, and that the fragment
and tolerance schedules are computable.  The *region* is not supplied — it is enumerated
from the day's stage — and no computability assumption about the deductive process beyond
the pinned source's own `DeductiveProcessComputation` appears anywhere. -/

/-- **The effective deductive schedule.** -/
def deductiveProjectionSchedule (coords : ℕ → List Sentence)
    (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n) :
    ProjectionSchedule where
  coords := coords
  nodup := nodup
  tol := tol
  tol_pos := tol_pos
  reps := fun n D => deductiveReps D (coords n)
  dflt := default

/-- **Its effectiveness, from the fragment and tolerance schedules alone.**  The
representation's computability is `deductiveReps_primrec`; nothing is assumed about the
deductive process. -/
def deductiveScheduleComputation (coords : ℕ → List Sentence)
    (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
    (hcoords : Primrec coords) (htol : Primrec tol) :
    ProjectionScheduleComputation
      (deductiveProjectionSchedule coords nodup tol tol_pos) where
  coordsComputable := hcoords
  tolComputable := htol
  repsComputable := by
    have h : Primrec fun z : ℕ × Finset Sentence => deductiveReps z.2 (coords z.1) :=
      deductiveReps_primrec.comp Primrec.snd (hcoords.comp Primrec.fst)
    exact h.to₂

/-- **The theorem of record for deductive coherence.**

The hypotheses are exactly: a deductive process carrying the pinned source's own
computability certificate; a computable fragment schedule with no repeats; a computable
schedule of strictly positive tolerances; and that every stage is propositionally
satisfiable.  No region is supplied, no representation is supplied, and there is no
computability assumption about the deductive process beyond `DeductiveProcessComputation`.

The conclusion is the pinned source's own `IsLogicalInductor`, together with finite-time
conformance at **every** date to the day's deductive region. -/
theorem deductive_end_to_end (coords : ℕ → List Sentence)
    (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
    (hcoords : Primrec coords) (htol : Primrec tol)
    {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
    (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    IsLogicalInductor
        ((deductiveProjectionSchedule coords nodup tol tol_pos).market DP) DP ∧
      ∀ n, dist2 ((deductiveProjectionSchedule coords nodup tol tol_pos).fragment n).toFinset
          ((deductiveProjectionSchedule coords nodup tol tol_pos).market DP n)
          (fun φ => ProjectionCompiler.repEval
            ((deductiveProjectionSchedule coords nodup tol tol_pos).fragment n)
            ((deductiveProjectionSchedule coords nodup tol tol_pos).rep n (DP.D n) φ)
            ((deductiveProjectionSchedule coords nodup tol tol_pos).market DP n))
        ≤ ((tol n : ℚ) : ℝ) := by
  classical
  set S := deductiveProjectionSchedule coords nodup tol tol_pos with hS
  set q : ℕ → Sentence → ℝ := fun n φ =>
    ProjectionCompiler.repEval (S.fragment n) (S.rep n (DP.D n) φ) (S.market DP n) with hq
  have hE : EffectiveEnforcerComputation S.enforcer :=
    ProjectionEffective.effectiveEnforcer S
      (deductiveScheduleComputation coords nodup tol tol_pos hcoords htol)
  obtain ⟨hli, hconf, _⟩ :=
    ProjectionSchedule.end_to_end_effective S process hE
      (K := fun n y => DeductiveRegion.deductiveRegion (DP.D n) (coords n) y) (q := q)
      (fun n u v huv hu =>
        (DeductiveRegion.deductiveRegion_fragmentLocal (DP.D n) (coords n)
          (fun φ hφ => huv φ (List.mem_toFinset.mpr hφ))).mp hu)
      (fun n y hy φ hφ => by
        have hmem : φ ∈ coords n := List.mem_toFinset.mp hφ
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
        have h := DeductiveRegion.deductiveRegion_subset_cube (DP.D n) (coords n) hy i
        have hval : DeductiveRegion.restrictTo (coords n) y i = y φ := by
          rw [← hi]
          rfl
        rw [hval] at h
        exact ⟨h.1, h.2⟩)
      (fun n => isNearestPoint_deductiveReps (DP.D n) (coords n) (nodup n) (hsat n)
        (S.market DP n))
      (fun _ _ _ => rfl)
      (fun n v hv =>
        DeductiveRegion.payout_mem_deductiveRegion (DP.D n) (coords n) v hv)
  exact ⟨hli, hconf⟩

end Workspace.Normativity.Contrib.DeductiveEffective

#print axioms Workspace.Normativity.Contrib.DeductiveEffective.contextAtoms_primrec
#print axioms Workspace.Normativity.Contrib.DeductiveEffective.admissiblePatternsEff_primrec
#print axioms Workspace.Normativity.Contrib.DeductiveEffective.vertexData_deductivePolytopeEff
#print axioms Workspace.Normativity.Contrib.DeductiveEffective.deductiveReps_primrec
#print axioms Workspace.Normativity.Contrib.DeductiveEffective.repEval_deductiveReps
#print axioms Workspace.Normativity.Contrib.DeductiveEffective.carrier_deductivePolytopeEff
#print axioms Workspace.Normativity.Contrib.DeductiveEffective.mem_carrier_iff_deductiveRegion
#print axioms Workspace.Normativity.Contrib.DeductiveEffective.isNearestPoint_deductiveReps
#print axioms Workspace.Normativity.Contrib.DeductiveEffective.deductiveScheduleComputation
#print axioms Workspace.Normativity.Contrib.DeductiveEffective.deductive_end_to_end
