import TraderizedConstraints.Computability

/-!
# Strengthening Logical Induction with Traderized Constraints

A thin paper-facing API over the checked `Workspace.Normativity.Contrib` implementation.
-/

namespace TraderizedConstraints

open LogicalInduction
open Workspace.Normativity.Contrib.ProjectionForce
open Workspace.Normativity.Contrib.ProjectionMarket
open Workspace.Normativity.Contrib.ProjectionCompiler
open Workspace.Normativity.Contrib.ProjectionCalibrated
open Workspace.Normativity.Contrib.ProjectionEnforcer
open Workspace.Normativity.Contrib.ConstraintSchedule
open Workspace.Normativity.Contrib.EffectiveRepresentation
open Workspace.Normativity.Contrib.DeductiveRegion
open Workspace.Normativity.Contrib.DeductiveEffective
open Workspace.Normativity.Contrib.DeductiveEnforcement
open Workspace.Normativity.Contrib.EnforcedComputation
open Computability

/-- The projection trade is profitable against every point in the constraint region. -/
theorem projection_trade_profitable_on_constraint
    {Phi : Finset Sentence} {K : (Sentence → Real) → Prop}
    {p q y : Sentence → Real} {lambda : Real} (hlambda : 0 ≤ lambda)
    (hq : IsNearestPoint Phi K p q) (hy : K y) :
    lambda * sqDist Phi p q ≤
      ip Phi (shares lambda p q) (fun phi => y phi - p phi) :=
  force_inequality hlambda hq hy

/-- The sharp local loss bound when the evaluated world need not satisfy the constraint. -/
theorem projection_loss_controlled_by_distance
    {Phi : Finset Sentence} {K : (Sentence → Real) → Prop}
    {p q x z : Sentence → Real} {lambda : Real} (hlambda : 0 ≤ lambda)
    (hq : IsNearestPoint Phi K p q) (hz : IsNearestPoint Phi K x z) :
    lambda * (sqDist Phi p q - dist2 Phi p q * dist2 Phi x z) ≤
      ip Phi (shares lambda p q) (fun phi => x phi - p phi) :=
  liability_inequality hlambda hq hz

/-- One day of projection enforcement attains the requested distance bound. -/
theorem one_day_enforcement (C : RationalConstraintSchedule)
    (DP : DeductiveProcess) (n : Nat) :
    dist2 (C.fragment n).toFinset
        (C.market (effectiveRepresentation C) DP n)
        (C.target (effectiveRepresentation C) DP n) ≤ ((C.tol n : Rat) : Real) :=
  C.conformance (effectiveRepresentation C) DP n

/-- Ordinary computable constraint data compile to a computable enforcement-trade hook. -/
def constraint_schedule_compilation (C : RationalConstraintSchedule)
    (hC : ComputableConstraintSchedule C) :
    ComputableEnforcer (C.schedule (effectiveRepresentation C)).enforcer :=
  computableEnforcer _ (projectionScheduleOfConstraints C hC)

/-- Computable constraint schedules give a computable modified market and all requested
datewise distance bounds. -/
theorem constraint_schedules_enforceable (C : RationalConstraintSchedule)
    (hC : ComputableConstraintSchedule C) {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    ComputableMarket (C.market (effectiveRepresentation C) DP) ∧
      ∀ n, dist2 (C.fragment n).toFinset
          (C.market (effectiveRepresentation C) DP n)
          (C.target (effectiveRepresentation C) DP n) ≤ ((C.tol n : Rat) : Real) := by
  refine ⟨Computability.computableMarket process (constraint_schedule_compilation C hC), ?_⟩
  exact fun n => one_day_enforcement C DP n

/-- One finite bound works at every horizon and every world still plausible then. -/
def LifetimeLiability (DP : DeductiveProcess) (E : EffectiveEnforcer) (B : Real) : Prop :=
  ∀ N (v : PCWorld), v.ConsistentWith (DP.D N) →
    -B ≤ (realizedEnforcer DP (E.adaptive DP)).netWorth
      (history DP (E.adaptive DP)) v N

/-- Bounded enforcement liability uniformly bounds the original trading firm, evaluated
on the modified prior price history. -/
theorem tradingFirm_upper_bound_under_bounded_enforcement
    (DP : DeductiveProcess) (E : EffectiveEnforcer) (B : Real)
    (hliability : LifetimeLiability DP E B) (N : Nat) (v : PCWorld)
    (hv : v.ConsistentWith (DP.D N)) :
    (realizedFirm DP (E.adaptive DP)).netWorth
      (history DP (E.adaptive DP)) v N ≤ 1 + B :=
  realizedFirm_netWorth_le DP (E.adaptive DP) B hliability N v hv

/-- Bounded lifetime liability preserves the logical induction criterion. -/
theorem bounded_liability_preserves_lic {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (E : EffectiveEnforcer)
    (hE : ComputableEnforcer E) (B : Real) (hliability : LifetimeLiability DP E B) :
    IsLogicalInductor (history DP (E.adaptive DP)) DP :=
  isLogicalInductor_of_compiler process E (Computability.compiler process hE) B hliability

/-- Bounded-liability constraint enforcement preserves logical induction and satisfies
every requested distance bound. -/
theorem li_with_quantitative_constraints (C : RationalConstraintSchedule)
    (hC : ComputableConstraintSchedule C) {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (B : Real)
    (hliability : LifetimeLiability DP
      (C.schedule (effectiveRepresentation C)).enforcer B) :
    IsLogicalInductor (C.market (effectiveRepresentation C) DP) DP ∧
      ∀ n, dist2 (C.fragment n).toFinset
          (C.market (effectiveRepresentation C) DP n)
          (C.target (effectiveRepresentation C) DP n) ≤ ((C.tol n : Rat) : Real) := by
  refine ⟨bounded_liability_preserves_lic process _
    (constraint_schedule_compilation C hC) B hliability, ?_⟩
  exact fun n => one_day_enforcement C DP n

/-- World-inclusive constraint regions give zero lifetime liability. -/
theorem plausible_worlds_zero_liability (C : RationalConstraintSchedule)
    {DP : DeductiveProcess}
    (hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → C.regionPred n v.payout) :
    LifetimeLiability DP (C.schedule (effectiveRepresentation C)).enforcer 0 := by
  let R := effectiveRepresentation C
  let S := C.schedule R
  have hlam : ∀ n, (0 : Real) ≤
      ((S.intensity n ((realizedFirm DP (S.enforcer.adaptive DP)).strat n).trades : Rat) : Real) := by
    intro n
    exact_mod_cast (calibratedIntensity_pos
      (by rw [Strategy.tradeListAbsBound_strategy]; exact Strategy.absBound_nonneg _)
      (S.tol_pos n)).le
  have hday : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      0 ≤ ((realizedEnforcer DP (S.enforcer.adaptive DP)).strat n).value
        (S.market DP) v.payout := by
    intro n v hv
    exact day_value_nonneg
      (S.enforcer_realizes n (DP.D n)
        ((realizedFirm DP (S.enforcer.adaptive DP)).strat n)
        (S.market DP) (C.target R DP n) (C.repEval_market R DP n))
      (hlam n) (C.isNearestPoint_targetAt n _) v.payout (hadm n v hv)
  intro N v hv
  simpa [S, R] using enforcement_netWorth_nonneg DP (S.enforcer.adaptive DP) hday N v hv

/-- The paper's deductive-region constraint schedule. -/
def deductive_regions_form_constraint_schedule
    (coords : Nat → List Sentence) (nodup : ∀ n, (coords n).Nodup)
    (tol : Nat → Rat) (tol_pos : ∀ n, 0 < tol n) : ProjectionSchedule :=
  deductiveProjectionSchedule coords nodup tol tol_pos

/-- Logical induction, datewise deductive coherence, and zero lifetime liability, from
ordinary computable fragment and tolerance schedules. -/
theorem strengthened_logical_induction
    (coords : Nat → List Sentence) (nodup : ∀ n, (coords n).Nodup)
    (tol : Nat → Rat) (tol_pos : ∀ n, 0 < tol n)
    (hcoords : Computable coords) (htol : Computable tol)
    {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
    (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    let S := deductiveProjectionSchedule coords nodup tol tol_pos
    IsLogicalInductor (S.market DP) DP ∧
      (∀ n, dist2 (S.fragment n).toFinset (S.market DP n)
        (fun phi => repEval (S.fragment n) (S.rep n (DP.D n) phi) (S.market DP n))
          ≤ ((tol n : Rat) : Real)) ∧
      LifetimeLiability DP S.enforcer 0 := by
  classical
  dsimp only
  let S := deductiveProjectionSchedule coords nodup tol tol_pos
  let q : Nat → Sentence → Real := fun n phi =>
    repEval (S.fragment n) (S.rep n (DP.D n) phi) (S.market DP n)
  have hScomp : ComputableProjectionSchedule S :=
    Computability.deductiveSchedule coords nodup tol tol_pos hcoords htol
  have hlocal : ∀ n, FragmentLocal (S.fragment n).toFinset
      (fun y => deductiveRegion (DP.D n) (coords n) y) := fun n u v huv hu =>
    (deductiveRegion_fragmentLocal (DP.D n) (coords n)
      (fun phi hphi => huv phi (List.mem_toFinset.mpr hphi))).mp hu
  have hcube : ∀ n y, deductiveRegion (DP.D n) (coords n) y →
      ∀ phi ∈ (S.fragment n).toFinset, 0 ≤ y phi ∧ y phi ≤ 1 := by
    intro n y hy phi hphi
    have hmem : phi ∈ coords n := List.mem_toFinset.mp hphi
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
    have h := deductiveRegion_subset_cube (DP.D n) (coords n) hy i
    have hval : restrictTo (coords n) y i = y phi := by rw [← hi]; rfl
    rwa [hval] at h
  have hnearest : ∀ n, IsNearestPoint (S.fragment n).toFinset
      (fun y => deductiveRegion (DP.D n) (coords n) y) (S.market DP n) (q n) :=
    fun n => isNearestPoint_deductiveReps (DP.D n) (coords n) (nodup n) (hsat n)
      (S.market DP n)
  have hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      deductiveRegion (DP.D n) (coords n) v.payout :=
    fun n v hv => payout_mem_deductiveRegion (DP.D n) (coords n) v hv
  obtain ⟨hli, hconf, _⟩ := S.end_to_end process
    (Computability.compiler process (computableEnforcer S hScomp))
    hlocal hcube hnearest (fun _ _ _ => rfl) hadm
  have hlam : ∀ n, (0 : Real) ≤
      ((S.intensity n ((realizedFirm DP (S.enforcer.adaptive DP)).strat n).trades : Rat) : Real) := by
    intro n
    exact_mod_cast (calibratedIntensity_pos
      (by rw [Strategy.tradeListAbsBound_strategy]; exact Strategy.absBound_nonneg _)
      (S.tol_pos n)).le
  have hday : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      0 ≤ ((realizedEnforcer DP (S.enforcer.adaptive DP)).strat n).value
        (S.market DP) v.payout := by
    intro n v hv
    exact day_value_nonneg
      (S.enforcer_realizes n (DP.D n)
        ((realizedFirm DP (S.enforcer.adaptive DP)).strat n)
        (S.market DP) (q n) (fun _ _ => rfl))
      (hlam n) (hnearest n) v.payout (hadm n v hv)
  refine ⟨hli, hconf, ?_⟩
  intro N v hv
  simpa using enforcement_netWorth_nonneg DP (S.enforcer.adaptive DP) hday N v hv

/-- Enforcement toward a second deductive process only needs fragmentwise inclusion:
every source-plausible world's restriction to the day's fragment lies in the second
process's deductive region. -/
theorem different_deductive_processes
    (coords : Nat → List Sentence) (nodup : ∀ n, (coords n).Nodup)
    (tol : Nat → Rat) (tol_pos : ∀ n, 0 < tol n)
    (hcoords : Computable coords) (htol : Computable tol)
    {source target : DeductiveProcess}
    (sourceProcess : DeductiveProcessComputation source)
    (htarget : Computable fun n => target.D n)
    (targetSat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (target.D n))
    (hfragment : ∀ n (v : PCWorld), v.ConsistentWith (source.D n) →
      deductiveRegion (target.D n) (coords n) v.payout) :
    let S : ProjectionSchedule :=
      { coords := coords
        nodup := nodup
        tol := tol
        tol_pos := tol_pos
        reps := fun n _ => deductiveReps (target.D n) (coords n)
        dflt := default }
    IsLogicalInductor (S.market source) source ∧
      ∀ n, dist2 (S.fragment n).toFinset (S.market source n)
        (fun phi => repEval (S.fragment n) (S.rep n (source.D n) phi)
          (S.market source n)) ≤ ((tol n : Rat) : Real) := by
  classical
  dsimp only
  let S : ProjectionSchedule :=
    { coords := coords
      nodup := nodup
      tol := tol
      tol_pos := tol_pos
      reps := fun n _ => deductiveReps (target.D n) (coords n)
      dflt := default }
  let q : Nat → Sentence → Real := fun n phi =>
    repEval (S.fragment n) (S.rep n (source.D n) phi) (S.market source n)
  have hScomp : ComputableProjectionSchedule S := {
    coordsComputable := hcoords
    tolComputable := htol
    repsComputable := by
      have h : Computable fun z : Nat × Finset Sentence =>
          deductiveReps (target.D z.1) (coords z.1) :=
        deductiveReps_primrec.to_comp.comp (htarget.comp Computable.fst)
          (hcoords.comp Computable.fst)
      exact h.to₂ }
  obtain ⟨hli, hconf, _⟩ := S.end_to_end sourceProcess
    (Computability.compiler sourceProcess (computableEnforcer S hScomp))
    (K := fun n y => deductiveRegion (target.D n) (coords n) y) (q := q)
    (fun n u v huv hu =>
      (deductiveRegion_fragmentLocal (target.D n) (coords n)
        (fun phi hphi => huv phi (List.mem_toFinset.mpr hphi))).mp hu)
    (fun n y hy phi hphi => by
      have hmem : phi ∈ coords n := List.mem_toFinset.mp hphi
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
      have h := deductiveRegion_subset_cube (target.D n) (coords n) hy i
      have hval : restrictTo (coords n) y i = y phi := by rw [← hi]; rfl
      rwa [hval] at h)
    (fun n => isNearestPoint_deductiveReps (target.D n) (coords n) (nodup n)
      (targetSat n) (S.market source n))
    (fun _ _ _ => rfl) hfragment
  exact ⟨hli, hconf⟩

end TraderizedConstraints

#print axioms TraderizedConstraints.projection_trade_profitable_on_constraint
#print axioms TraderizedConstraints.projection_loss_controlled_by_distance
#print axioms TraderizedConstraints.one_day_enforcement
#print axioms TraderizedConstraints.constraint_schedule_compilation
#print axioms TraderizedConstraints.constraint_schedules_enforceable
#print axioms TraderizedConstraints.tradingFirm_upper_bound_under_bounded_enforcement
#print axioms TraderizedConstraints.bounded_liability_preserves_lic
#print axioms TraderizedConstraints.li_with_quantitative_constraints
#print axioms TraderizedConstraints.plausible_worlds_zero_liability
#print axioms TraderizedConstraints.deductive_regions_form_constraint_schedule
#print axioms TraderizedConstraints.strengthened_logical_induction
#print axioms TraderizedConstraints.different_deductive_processes
