/-
# Protected reason coverage: the barrier, the bridge, and the void-mass bound

Round `projects/deference/rounds/2026-09-08-legitimate-deference-consolidation/`.

The remaining manipulation channel after reason mediation is reason *supply*: the
advisor does not bypass the reason interface, it controls which reasons reach it.  The
narrow answer is scope-relative: a certified evaluation may not omit a **protected** live
concern.  This module is the propositional bridge from the coverage vocabulary of
`NonCaptureCertificate.lean` — `Active`, `Rep`, live = active and unrepresented — into the
reason trace of `ReasonMediatedAuthorship.lean`, and the one theorem it yields.

* `RepFaithful` — the bridge: a represented protected concern is in the reason trace.
* `NoBindLive` — the barrier: a certified evaluation has no live protected concern at
  commitment.
* `covered_of_barrier` — **reason-coverage soundness**: barrier + bridge give that every
  active protected concern is in the trace on every certified world; `void_of_omitted` is
  the contrapositive: a protected reason omitted means `C = 0`.
* `covFail_mass_le` — **the void-mass bound**: under soundness the credence of the
  reason-suppression event is at most `𝔼[1 − C]`.
* `route_of_live` — Robust Openness's contribution, restated: a live concern has an
  adequate route.  It does not say the route is exercised.
* Witnesses G–L of the consolidation round's `COUNTERMODELS.md`.

**What this does not establish.**  That the declared protected scope is normatively
complete; that any route is exercised; that any evaluation certifies.  Names are
provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.ActivatedValue
import Workspace.Normativity.Contrib.NonCaptureCertificate

namespace Workspace.Deference.Contrib.ReasonCoverage

open Workspace.Deference.Contrib.ActivatedValue
open Workspace.Normativity.Contrib.NonCapture

variable {Γ W : Type*}

/-- Coverage data for the evaluation's protected concerns, per world: anchored
applicability (`Active`), representation in the process (`Rep`), and membership in the
declared reason trace at commitment (`InTrace`). -/
structure CoverageData (Γ W : Type*) where
  active : Γ → W → Bool
  rep : Γ → W → Bool
  inTrace : Γ → W → Bool

namespace CoverageData

variable (d : CoverageData Γ W)

/-- Live: active and unrepresented. -/
def live (c : Γ) (w : W) : Bool := d.active c w && !d.rep c w

/-- **The bridge.**  On the protected scope, representation lands in the reason trace. -/
def RepFaithful (scope : Finset Γ) : Prop :=
  ∀ c ∈ scope, ∀ w, d.rep c w = true → d.inTrace c w = true

/-- **The barrier.**  A certified world has no live protected concern. -/
def NoBindLive (scope : Finset Γ) (C : W → Bool) : Prop :=
  ∀ w, C w = true → ∀ c ∈ scope, d.live c w = false

/-- **Certified reason coverage.**  On every certified world, every active protected
concern is in the reason trace. -/
def Covered (scope : Finset Γ) (C : W → Bool) : Prop :=
  ∀ w, C w = true → ∀ c ∈ scope, d.active c w = true → d.inTrace c w = true

/-- **Reason-coverage soundness.**  Barrier and bridge give coverage. -/
theorem covered_of_barrier (scope : Finset Γ) (C : W → Bool)
    (hF : d.RepFaithful scope) (hB : d.NoBindLive scope C) : d.Covered scope C := by
  intro w hw c hc ha
  have hl := hB w hw c hc
  simp only [live, ha, Bool.true_and, Bool.not_eq_false'] at hl
  exact hF c hc w hl

/-- **Omission voids.**  A protected active concern missing from the trace forces `C = 0`. -/
theorem void_of_omitted (scope : Finset Γ) (C : W → Bool) (hcov : d.Covered scope C)
    (w : W) (c : Γ) (hc : c ∈ scope) (ha : d.active c w = true)
    (hmiss : d.inTrace c w = false) : C w = false := by
  by_contra h
  have := hcov w (by simpa using h) c hc ha
  rw [hmiss] at this
  exact Bool.false_ne_true this

/-- The reason-suppression event: some protected active concern is missing from the
trace. -/
def covFail [DecidableEq Γ] (scope : Finset Γ) (w : W) : Bool :=
  decide (∃ c ∈ scope, d.active c w = true ∧ d.inTrace c w = false)

/-- **The void-mass bound.**  Under coverage soundness, the credence of reason suppression
is at most the void mass `𝔼[1 − C]`. -/
theorem covFail_mass_le [DecidableEq Γ] [Fintype W] (π : W → ℚ) (hπ : ∀ w, 0 ≤ π w)
    (scope : Finset Γ) (C : W → Bool) (hcov : d.Covered scope C) :
    expect π (ind (d.covFail scope)) ≤ expect π (fun w => 1 - ind C w) := by
  unfold expect
  refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ (hπ w)
  unfold ind covFail
  by_cases hf : ∃ c ∈ scope, d.active c w = true ∧ d.inTrace c w = false
  · obtain ⟨c, hc, ha, hm⟩ := hf
    have hC := d.void_of_omitted scope C hcov w c hc ha hm
    have hd : decide (∃ c ∈ scope, d.active c w = true ∧ d.inTrace c w = false) = true :=
      decide_eq_true ⟨c, hc, ha, hm⟩
    simp [hd, hC]
  · have hd : decide (∃ c ∈ scope, d.active c w = true ∧ d.inTrace c w = false) = false :=
      decide_eq_false hf
    simp only [hd, Bool.false_eq_true, if_false]
    split_ifs <;> norm_num

end CoverageData

/-- **Robust Openness's contribution**, restated from `CovState.Covered`: a live concern has
an adequate route.  Nothing here says the route is taken. -/
theorem route_of_live {R : Type} (s : CovState R) (h : s.Covered) (hl : s.live = true) :
    ∃ r, s.adequate r = true :=
  h hl

/-! ## Witnesses

One protected concern `c₀` and one unprotected concern `c₁`; one world; `C` as each fixture
says. -/

namespace Witness

/-- **G. Route without barrier.**  The concern is live (a route exists in the coverage
semantics, `CovState` side) and the evaluator commits anyway: `C = 1`, coverage fails. -/
def dG : CoverageData (Fin 2) Unit := ⟨fun _ _ => true, fun _ _ => false, fun _ _ => false⟩

theorem route_without_barrier :
    ¬ dG.NoBindLive {0} (fun _ => true) ∧ ¬ dG.Covered {0} (fun _ => true) := by
  constructor
  · intro h; have := h () rfl 0 (by simp); simp [dG, CoverageData.live] at this
  · intro h; have := h () rfl 0 (by simp) rfl; simp [dG] at this

/-- **H. Barrier without route.**  The concern is live and stays so; the barrier holds
vacuously because `C = 0` everywhere: soundness with no availability. -/
theorem barrier_without_route :
    dG.NoBindLive {0} (fun _ => false) ∧ dG.Covered {0} (fun _ => false) ∧
    (fun _ : Unit => false) = fun _ => false := by
  refine ⟨fun _ h => by simp at h, fun _ h => by simp at h, rfl⟩

/-- **I. Representation-unfaithful.**  `Rep` holds in the coverage semantics but the reason
never enters the trace: the barrier holds, coverage fails, the bridge is needed. -/
def dI : CoverageData (Fin 2) Unit := ⟨fun _ _ => true, fun _ _ => true, fun _ _ => false⟩

theorem unfaithful :
    dI.NoBindLive {0} (fun _ => true) ∧ ¬ dI.RepFaithful {0} ∧
    ¬ dI.Covered {0} (fun _ => true) := by
  refine ⟨fun _ _ c _ => by simp [dI, CoverageData.live], fun h => ?_, fun h => ?_⟩
  · have := h 0 (by simp) () rfl; simp [dI] at this
  · have := h () rfl 0 (by simp) rfl; simp [dI] at this

/-- **J. Unprotected selective disclosure.**  Concern `1` is active and omitted, but
outside the protected scope `{0}`; coverage holds. -/
def dJ : CoverageData (Fin 2) Unit :=
  ⟨fun _ _ => true, fun c _ => decide (c = 0), fun c _ => decide (c = 0)⟩

theorem unprotected_omission :
    dJ.Covered {0} (fun _ => true) ∧ dJ.inTrace 1 () = false := by
  refine ⟨fun _ _ c hc _ => ?_, by simp [dJ]⟩
  simp at hc; subst hc; simp [dJ]

/-- **L. Legitimate influence plus protected challenge.**  The protected objection is
represented and in the trace; the evaluation certifies whatever the verdict. -/
theorem consideration_not_agreement :
    dJ.RepFaithful {0} ∧ dJ.NoBindLive {0} (fun _ => true) ∧ dJ.Covered {0} (fun _ => true) := by
  refine ⟨fun c hc _ h => ?_, fun _ _ c hc => ?_, ?_⟩
  · simp at hc; subst hc; simp [dJ]
  · simp at hc; subst hc; simp [dJ, CoverageData.live]
  · exact dJ.covered_of_barrier {0} _ (fun c hc _ h => by simp at hc; subst hc; simp [dJ])
      (fun _ _ c hc => by simp at hc; subst hc; simp [dJ, CoverageData.live])

end Witness

end Workspace.Deference.Contrib.ReasonCoverage

#print axioms Workspace.Deference.Contrib.ReasonCoverage.CoverageData.covered_of_barrier
#print axioms Workspace.Deference.Contrib.ReasonCoverage.CoverageData.void_of_omitted
#print axioms Workspace.Deference.Contrib.ReasonCoverage.CoverageData.covFail_mass_le
#print axioms Workspace.Deference.Contrib.ReasonCoverage.route_of_live
#print axioms Workspace.Deference.Contrib.ReasonCoverage.Witness.route_without_barrier
#print axioms Workspace.Deference.Contrib.ReasonCoverage.Witness.barrier_without_route
#print axioms Workspace.Deference.Contrib.ReasonCoverage.Witness.unfaithful
#print axioms Workspace.Deference.Contrib.ReasonCoverage.Witness.unprotected_omission
#print axioms Workspace.Deference.Contrib.ReasonCoverage.Witness.consideration_not_agreement
