/-
# The projection schedule's enforcer is effective

`EnforcedCompiler` discharges the modified market's computability from
`EffectiveEnforcerComputation E` — that the enforcer's trade map is primitive recursive in
the date and the ordinary aggregate's trade list.  For a `ProjectionSchedule` that is not a
hypothesis but a consequence of the schedule's own computability, and this file proves it.

With it, the theorem of record takes only effective source data: a computable deductive
process, a computable fragment schedule, a computable positive rational tolerance schedule,
and a computable representation schedule.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.ProjectionPrimrec
import Workspace.Normativity.Contrib.EnforcedCompiler

namespace Workspace.Normativity.Contrib.ProjectionEffective

open LogicalInduction
open Workspace.Normativity.Contrib.ProjectionForce
open Workspace.Normativity.Contrib.ProjectionCompiler
open Workspace.Normativity.Contrib.ProjectionCalibrated
open Workspace.Normativity.Contrib.ProjectionPrimrec
open Workspace.Normativity.Contrib.ProjectionEnforcer
open Workspace.Normativity.Contrib.DeductiveEnforcement
open Workspace.Normativity.Contrib.EnforcedComputation
open Workspace.Normativity.Contrib.EnforcedCompiler

/-- Pairing two two-argument primitive-recursive functions. -/
private lemma pair₂ {α β γ δ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
    [Primcodable δ] {f : α → β → γ} {g : α → β → δ} (hf : Primrec₂ f) (hg : Primrec₂ g) :
    Primrec₂ fun a b => (f a b, g a b) :=
  (Primrec.pair hf hg).to₂

/-- **The schedule's enforcer is effective.**  Its day-`n` trade list is primitive
recursive in the date and the ordinary aggregate's trade list, given that the schedule's
own three components are computable. -/
theorem scheduleTrades_primrec (S : ProjectionSchedule)
    (hS : ProjectionScheduleComputation S) :
    Primrec fun z : (ℕ × Finset Sentence) × List (EF × Sentence) =>
      S.enforcer.trades z.1.1 z.1.2 z.2 := by
  have hcoords : Primrec fun a : (ℕ × Finset Sentence) × List (EF × Sentence) =>
      S.coords a.1.1 :=
    hS.coordsComputable.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun a : (ℕ × Finset Sentence) × List (EF × Sentence) => a.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hreps : Primrec fun a : (ℕ × Finset Sentence) × List (EF × Sentence) =>
      S.reps a.1.1 :=
    hS.repsComputable.comp (Primrec.fst.comp Primrec.fst)
  have hlam : Primrec fun a : (ℕ × Finset Sentence) × List (EF × Sentence) =>
      calibratedIntensity a.1.1 (Strategy.tradeListAbsBound a.2) (S.tol a.1.1) := by
    have hin : Primrec fun a : (ℕ × Finset Sentence) × List (EF × Sentence) =>
        ((a.1.1, Strategy.tradeListAbsBound a.2), S.tol a.1.1) :=
      ((Primrec.fst.comp Primrec.fst).pair
          (tradeListAbsBound_primrec.comp Primrec.snd)).pair
        (hS.tolComputable.comp (Primrec.fst.comp Primrec.fst))
    exact calibratedIntensity_primrec.comp hin
  have hrep : Primrec₂ fun (a : (ℕ × Finset Sentence) × List (EF × Sentence)) (φ : Sentence) =>
      (S.reps a.1.1).getD ((S.coords a.1.1).idxOf φ) S.dflt := by
    have hidx : Primrec₂ fun (a : (ℕ × Finset Sentence) × List (EF × Sentence)) (φ : Sentence) =>
        (S.coords a.1.1).idxOf φ :=
      Primrec.list_idxOf.comp₂ Primrec₂.right (hcoords.comp₂ Primrec₂.left)
    exact (Primrec.list_getD S.dflt).comp₂ (hreps.comp₂ Primrec₂.left) hidx
  have hbody : Primrec₂ fun (a : (ℕ × Finset Sentence) × List (EF × Sentence)) (φ : Sentence) =>
      (coefEFof (S.coords a.1.1) a.1.1
        (calibratedIntensity a.1.1 (Strategy.tradeListAbsBound a.2) (S.tol a.1.1))
        ((S.reps a.1.1).getD ((S.coords a.1.1).idxOf φ) S.dflt) φ, φ) := by
    have hef : Primrec₂ fun (a : (ℕ × Finset Sentence) × List (EF × Sentence)) (φ : Sentence) =>
        coefEFof (S.coords a.1.1) a.1.1
          (calibratedIntensity a.1.1 (Strategy.tradeListAbsBound a.2) (S.tol a.1.1))
          ((S.reps a.1.1).getD ((S.coords a.1.1).idxOf φ) S.dflt) φ := by
      have hin : Primrec₂ fun (a : (ℕ × Finset Sentence) × List (EF × Sentence)) (φ : Sentence) =>
          ((((S.coords a.1.1), a.1.1),
            calibratedIntensity a.1.1 (Strategy.tradeListAbsBound a.2) (S.tol a.1.1)),
            ((S.reps a.1.1).getD ((S.coords a.1.1).idxOf φ) S.dflt, φ)) :=
        pair₂ (pair₂ (pair₂ (hcoords.comp₂ Primrec₂.left) (hn.comp₂ Primrec₂.left))
          (hlam.comp₂ Primrec₂.left)) (pair₂ hrep Primrec₂.right)
      exact coefEFof_primrec.comp₂ hin
    exact pair₂ hef Primrec₂.right
  exact (Primrec.list_map hcoords hbody).of_eq fun a => rfl

/-- The effectiveness certificate `EnforcedCompiler` consumes. -/
def effectiveEnforcer (S : ProjectionSchedule)
    (hS : ProjectionScheduleComputation S) : EffectiveEnforcerComputation S.enforcer :=
  ⟨scheduleTrades_primrec S hS⟩

/-- **The modified market of a computable schedule is computable**, with no effectiveness
hypothesis about the enforcer left over: it is derived from the schedule's own. -/
theorem computableMarket_of_schedule {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (S : ProjectionSchedule)
    (hS : ProjectionScheduleComputation S) :
    ComputableMarket (history DP (S.enforcer.adaptive DP)) :=
  EnforcedCompiler.computableMarket process (effectiveEnforcer S hS)

/-- **The theorem of record with the enforcer's effectiveness discharged.**  Compared with
`ProjectionSchedule.end_to_end_effective`, the `EffectiveEnforcerComputation` hypothesis is
gone: it follows from the schedule's own computability. -/
theorem end_to_end_of_computation (S : ProjectionSchedule) {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (hS : ProjectionScheduleComputation S)
    {K : ℕ → (Sentence → ℝ) → Prop} {q : ℕ → Sentence → ℝ}
    (hlocal : ∀ n, FragmentLocal (S.fragment n).toFinset (K n))
    (hKcube : ∀ n y, K n y → ∀ φ ∈ (S.fragment n).toFinset, 0 ≤ y φ ∧ y φ ≤ 1)
    (hq : ∀ n, ProjectionForce.IsNearestPoint (S.fragment n).toFinset (K n) (S.market DP n) (q n))
    (hrep : ∀ n, ∀ φ ∈ S.coords n,
      repEval (S.fragment n) (S.rep n φ) (S.market DP n) = q n φ)
    (hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → K n v.payout) :
    IsLogicalInductor (S.market DP) DP ∧
      (∀ n, dist2 (S.fragment n).toFinset (S.market DP n) (q n)
        ≤ ((S.tol n : ℚ) : ℝ)) ∧
      ∀ n, K n (q n) ∧ ∀ φ ∈ (S.fragment n).toFinset,
        |S.market DP n φ - q n φ| ≤ ((S.tol n : ℚ) : ℝ) :=
  EnforcedCompiler.ProjectionSchedule.end_to_end_effective S process
    (effectiveEnforcer S hS) hlocal hKcube hq hrep hadm

end Workspace.Normativity.Contrib.ProjectionEffective

#print axioms Workspace.Normativity.Contrib.ProjectionEffective.scheduleTrades_primrec
#print axioms Workspace.Normativity.Contrib.ProjectionEffective.computableMarket_of_schedule
#print axioms Workspace.Normativity.Contrib.ProjectionEffective.end_to_end_of_computation
