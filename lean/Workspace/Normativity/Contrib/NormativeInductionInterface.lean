/-
# The Progress interface and the conditional Normative Inductor theorem

Round `projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/`.

The evaluation consumes exactly two fields of the Integrity export: the finite set of
exposed occurrences and their anchors.  The Progress statistic is the transport-weighted
edge response loss plus the residual charge,

    progress = Σ_{e,s} T(e,s) · Λ_{anchor e, s}(Π_s) + D · (1 − Σ_{e,s} T(e,s)),

where `Π_s` is the one response actually realized at service `s` from the market state,
and every exposure transported to `s` is scored against that same response.  The loss is
a function of the anchor, not of the occurrence: occurrence multiplicity enters through
the evaluation measure and the transport, never through the loss.

Two conditional theorems:

* `Evaluation.conditional_normative_inductor` — over a general assessment process.
  Hypotheses: bounded assessed liability of the enforcer, a computable augmented
  market, and the practical/uptake certificate at the realized market.  Conclusion:
  ordinary Logical Induction and the three-term Progress bound.  The LI hypotheses are
  not inhabited here; the certificate is (`Witness`).
* `Evaluation.deductive_normative_inductor` — over a compiled rational schedule and a
  deductive process, composing the registered effective end-to-end theorem: the uptake
  certificate `λ_s d_s² ≤ ρ_s` is *derived* from finite-time conformance and the
  sup-defect's domination by any conformance witness, not assumed.  Its remaining
  hypotheses are the registered theorem's own plus the edge practical certificates and
  the amplification bound.

Neither theorem asserts compiler soundness, joint feasibility, scheduling, or any
semantic premise; those are how a realization *produces* the hypotheses named here.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.OccurrenceIntegrity
import Workspace.Normativity.Contrib.NormativeInductorComposition

noncomputable section

namespace Workspace.Normativity.Contrib.NormativeInductionInterface

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Workspace.Normativity.Contrib.EnforcementPreservation
open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.OccurrenceIntegrity (Boundary)

variable {Occ Req Service : Type*}

/-! ## 1. The declared evaluation -/

/-- A declared finite evaluation of the qualitative export.  `Pi` selects the one
response realized at each service from the market history; `loss` is the anchored loss
functional on responses.  `μ`, `T`, `D` and the constants are the evaluation protocol's
predeclared data. -/
structure Evaluation (boundary : Boundary Occ Req) (anchor : Occ → Req)
    (Service : Type*) where
  services : Finset Service
  μ : Occ → ℝ
  μ_prob : ∑ e ∈ boundary.exposed, μ e = 1
  T : Occ → Service → ℝ
  T_nonneg : ∀ e ∈ boundary.exposed, ∀ s ∈ services, 0 ≤ T e s
  T_row : ∀ e ∈ boundary.exposed, ∑ s ∈ services, T e s ≤ μ e
  Response : Service → Type
  Pi : (s : Service) → History → Response s
  loss : Req → (s : Service) → Response s → ℝ
  defect : Service → History → ℝ
  lam : Service → ℝ
  ρ : Service → ℝ
  M : Occ → Service → ℝ
  ε : Occ → Service → ℝ
  Γ : ℝ
  D : ℝ

namespace Evaluation

variable {boundary : Boundary Occ Req} {anchor : Occ → Req}
variable (E : Evaluation boundary anchor Service)

/-- The anchored loss of the one realized response at `s`, scored for exposure `e`. -/
def edgeLoss (market : History) (e : Occ) (s : Service) : ℝ :=
  E.loss (anchor e) s (E.Pi s market)

/-- The unserved evaluation mass. -/
def residual : ℝ := 1 - ∑ e ∈ boundary.exposed, ∑ s ∈ E.services, E.T e s

/-- **The Progress statistic.** -/
def progress (market : History) : ℝ :=
  (∑ e ∈ boundary.exposed, ∑ s ∈ E.services, E.T e s * E.edgeLoss market e s) +
    E.D * E.residual

/-- The transport-weighted semantic/decision error. -/
def error : ℝ := ∑ e ∈ boundary.exposed, ∑ s ∈ E.services, E.T e s * E.ε e s

/-- **`PracticalCert`.**  The edge-local public certificate, at the realized market. -/
def PracticalCert (market : History) (e : Occ) (s : Service) : Prop :=
  E.edgeLoss market e s ≤ E.M e s * E.defect s market + E.ε e s

/-- The certificate package a realization must produce at the market it actually
realizes: nonnegative public defect, `PracticalCert` on every supported edge against
the same `Π_s`, the uptake bound, and the amplification bound. -/
structure PracticalUptake (market : History) : Prop where
  defect_nonneg : ∀ s ∈ E.services, 0 ≤ E.defect s market
  practical : ∀ e ∈ boundary.exposed, ∀ s ∈ E.services,
    0 < E.T e s → E.PracticalCert market e s
  lam_nonneg : ∀ s ∈ E.services, 0 ≤ E.lam s
  lam_pos : 0 < ∑ s ∈ E.services, E.lam s
  work : ∀ s ∈ E.services, E.lam s * E.defect s market ^ 2 ≤ E.ρ s
  Γ_nonneg : 0 ≤ E.Γ
  amplification : ∀ s ∈ E.services, ∑ e ∈ boundary.exposed, E.T e s * E.M e s ≤
    E.Γ * (E.lam s / ∑ t ∈ E.services, E.lam t)

/-- The residual is a mass in `[0, 1]`. -/
theorem residual_bounds : 0 ≤ E.residual ∧ E.residual ≤ 1 := by
  have hmass : (∑ e ∈ boundary.exposed, ∑ s ∈ E.services, E.T e s) ≤ 1 := by
    calc
      _ ≤ ∑ e ∈ boundary.exposed, E.μ e := Finset.sum_le_sum E.T_row
      _ = 1 := E.μ_prob
  have hnonneg : 0 ≤ ∑ e ∈ boundary.exposed, ∑ s ∈ E.services, E.T e s :=
    Finset.sum_nonneg fun e he => Finset.sum_nonneg fun s hs => E.T_nonneg e he s hs
  unfold residual
  constructor <;> linarith

/-- The quadratic modulus of the Progress bound. -/
def modulus : ℝ :=
  E.Γ * Real.sqrt ((∑ s ∈ E.services, E.ρ s) / (∑ s ∈ E.services, E.lam s))

/-- **The Progress theorem at the occurrence-indexed export.** -/
theorem progress_bound (market : History) (C : E.PracticalUptake market) :
    E.progress market ≤ E.modulus + E.error + E.D * E.residual :=
  edge_progress_bound_quadratic boundary.exposed E.services E.T (E.edgeLoss market)
    E.M E.ε (fun s => E.defect s market) E.lam E.ρ E.Γ E.D E.T_nonneg
    C.defect_nonneg C.practical C.lam_nonneg C.lam_pos C.work C.Γ_nonneg C.amplification

/-! ## 2. The conditional theorem over a general assessment process -/

/-- **Conditional Normative Inductor, general assessment.**  Bounded assessed liability
and a computable augmented market give ordinary Logical Induction; the practical/uptake
certificate at that same market gives the Progress bound.  Unverified-nonvacuous: no
term inhabiting the LI hypotheses is supplied here. -/
theorem conditional_normative_inductor (L : Assessment) (enforcer : AdaptiveTrader)
    (B : ℝ)
    (liability : ∀ n (v : PCWorld), L.Live n v →
      -B ≤ (realizedEnforcer L enforcer).netWorth (history L enforcer) v n)
    (computableMarket : ComputableMarket (history L enforcer))
    (cert : E.PracticalUptake (history L enforcer)) :
    L.IsLogicalInductor (history L enforcer) ∧
    (0 ≤ E.residual ∧ E.residual ≤ 1) ∧
    E.progress (history L enforcer) ≤ E.modulus + E.error + E.D * E.residual :=
  ⟨isLogicalInductor_of_computableMarket L enforcer B liability computableMarket,
    E.residual_bounds, E.progress_bound (history L enforcer) cert⟩

/-! ## 3. The composed theorem over a compiled deductive schedule -/

section Deductive

open Workspace.Normativity.Contrib.ConstraintSchedule
open Workspace.Normativity.Contrib.ProjectionBridge
open Workspace.Normativity.Contrib.EffectiveRepresentation

variable {Q : Type*}

/-- The market a compiled schedule realizes against a deductive process. -/
noncomputable def compiledMarket (CS : CompiledSchedule Q) (DP : DeductiveProcess) :
    History :=
  CS.toSchedule.market (effectiveRepresentation CS.toSchedule) DP

/-- The target (region point) the enforcer projects to at each date. -/
noncomputable def compiledTarget (CS : CompiledSchedule Q) (DP : DeductiveProcess) (n : ℕ) :
    Sentence → ℝ :=
  CS.toSchedule.target (effectiveRepresentation CS.toSchedule) DP n

/-- **The public defect is dominated by conformance.**  The sup-distance to a region is
at most the sup-distance to any point of it; this is the only property of `defect`
the composition needs, stated as an interface condition on the evaluation. -/
def DefectDominated (CS : CompiledSchedule Q) (DP : DeductiveProcess)
    (E : Evaluation boundary anchor ℕ) : Prop :=
  ∀ s ∈ E.services, ∀ b : History,
    (∀ φ ∈ (CS.toSchedule.fragment s).toFinset,
      |b s φ - compiledTarget CS DP s φ| ≤ ((CS s).tol : ℝ)) →
    E.defect s b ≤ ((CS s).tol : ℝ)

/-- **Conditional Normative Inductor, compiled deductive schedule.**  The registered
effective end-to-end theorem supplies ordinary Logical Induction and finite-time
conformance; conformance and defect domination supply the uptake certificate; the edge
practical certificates and the amplification bound supply the rest.  The hypotheses
`hC`, `process`, `hadm` are exactly those of the registered theorem. -/
theorem deductive_normative_inductor (E : Evaluation boundary anchor ℕ)
    (CS : CompiledSchedule Q) (hC : CS.toSchedule.Computation)
    {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
    (hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      (CS n).bundle.RegionR (fun i => restrict (CS.toSchedule.fragment n) v.payout i))
    (hdom : DefectDominated CS DP E)
    (defect_nonneg : ∀ s ∈ E.services, 0 ≤ E.defect s (compiledMarket CS DP))
    (practical : ∀ e ∈ boundary.exposed, ∀ s ∈ E.services,
      0 < E.T e s → E.PracticalCert (compiledMarket CS DP) e s)
    (lam_nonneg : ∀ s ∈ E.services, 0 ≤ E.lam s)
    (lam_pos : 0 < ∑ s ∈ E.services, E.lam s)
    (budget : ∀ s ∈ E.services, E.lam s * ((CS s).tol : ℝ) ^ 2 ≤ E.ρ s)
    (Γ_nonneg : 0 ≤ E.Γ)
    (amplification : ∀ s ∈ E.services, ∑ e ∈ boundary.exposed, E.T e s * E.M e s ≤
      E.Γ * (E.lam s / ∑ t ∈ E.services, E.lam t)) :
    IsLogicalInductor (compiledMarket CS DP) DP ∧
    (0 ≤ E.residual ∧ E.residual ≤ 1) ∧
    E.progress (compiledMarket CS DP) ≤ E.modulus + E.error + E.D * E.residual := by
  obtain ⟨hLI, _, hconf⟩ := compiled_end_to_end CS hC process hadm
  have hdefect : ∀ s ∈ E.services, E.defect s (compiledMarket CS DP) ≤ ((CS s).tol : ℝ) :=
    fun s hs => hdom s hs _ (hconf s).2
  have htol : ∀ s, (0 : ℝ) ≤ ((CS s).tol : ℝ) := fun s => by
    exact_mod_cast (CS s).tol_pos.le
  refine ⟨hLI, E.residual_bounds, E.progress_bound _ ?_⟩
  exact
    { defect_nonneg := defect_nonneg
      practical := practical
      lam_nonneg := lam_nonneg
      lam_pos := lam_pos
      work := fun s hs =>
        Workspace.Normativity.Contrib.NormativeInductor.public_work_le_projection_work
          (defect_nonneg s hs) (htol s) (hdefect s hs) (lam_nonneg s hs) (budget s hs)
      Γ_nonneg := Γ_nonneg
      amplification := amplification }

end Deductive

end Evaluation

/-! ## 4. Nonvacuity of the certificate

Two occurrences sharing one anchor (the Integrity witness boundary), one service, a
constant response.  Every field of `PracticalUptake` is inhabited and all three terms of
the bound are positive. -/

namespace Witness

open Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness (finish anchor)

def evaluation : Evaluation finish anchor Unit where
  services := {()}
  μ _ := 1 / 2
  μ_prob := by norm_num [finish]
  T _ _ := 1 / 4
  T_nonneg := by intros; norm_num
  T_row := by intros; simp; norm_num
  Response _ := Unit
  Pi _ _ := ()
  loss _ _ _ := 5 / 8
  defect _ _ := 1 / 2
  lam _ := 1
  ρ _ := 1 / 4
  M _ _ := 1
  ε _ _ := 1 / 8
  Γ := 1 / 2
  D := 1

def market : History := fun _ _ => 0

theorem uptake : evaluation.PracticalUptake market where
  defect_nonneg := by intros; norm_num [evaluation]
  practical := by
    intros
    show (5 / 8 : ℝ) ≤ 1 * (1 / 2) + 1 / 8
    norm_num
  lam_nonneg := by intros; norm_num [evaluation]
  lam_pos := by norm_num [evaluation]
  work := by intros; norm_num [evaluation]
  Γ_nonneg := by norm_num [evaluation]
  amplification := by intros; simp [evaluation, finish]; norm_num

/-- The bound holds at the witness, and each of its three terms is positive. -/
theorem bound :
    evaluation.progress market ≤
      evaluation.modulus + evaluation.error + evaluation.D * evaluation.residual ∧
    0 < evaluation.modulus ∧ 0 < evaluation.error ∧ 0 < evaluation.D * evaluation.residual := by
  refine ⟨evaluation.progress_bound market uptake, ?_, ?_, ?_⟩
  · simp [Evaluation.modulus, evaluation]
  · simp [Evaluation.error, evaluation, finish]
  · simp [Evaluation.residual, evaluation, finish]; norm_num

end Witness

end Workspace.Normativity.Contrib.NormativeInductionInterface

end

#print axioms Workspace.Normativity.Contrib.NormativeInductionInterface.Evaluation.residual_bounds
#print axioms Workspace.Normativity.Contrib.NormativeInductionInterface.Evaluation.progress_bound
#print axioms Workspace.Normativity.Contrib.NormativeInductionInterface.Evaluation.conditional_normative_inductor
#print axioms Workspace.Normativity.Contrib.NormativeInductionInterface.Evaluation.deductive_normative_inductor
#print axioms Workspace.Normativity.Contrib.NormativeInductionInterface.Witness.uptake
#print axioms Workspace.Normativity.Contrib.NormativeInductionInterface.Witness.bound
