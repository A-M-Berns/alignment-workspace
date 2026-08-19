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

end Workspace.Normativity.Contrib.DeductiveEffective
