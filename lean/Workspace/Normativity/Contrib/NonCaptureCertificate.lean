/-
# The Non-Capture certificate: interface theorem and clause necessity

Round `projects/normativity/legitimacy/rounds/2026-09-05-noncapture-certificate/`.

The coverage-relevant state of one declared concern at one history is abstracted to
`CovState R`: anchored applicability, authorized disposition, representation, three
per-route components (admissibility, efficacy, registration capability) and the
principal's standing on the live issue carrying the concern.  A `Scenario J R` pairs the
actual state with one counterfactual state per intervention `j : J`; how `cf j` is
produced is the external semantics and is not modelled here.

**Proved.**

* `robustOpen_of_cert` — the interface theorem: coverage on the actual prefix, witnessed
  inside the protected route set `W`, plus the three certificate clauses `ClauseS`,
  `ClauseR W`, `ClauseP`, gives `RobustOpen`.
* `robustOpen_of_certPlus` — the same with `ClauseR` weakened to `ClauseRPlus`, which
  lets a named replacement route discharge the live–live case.
* `clauseR_of_components` and `components_of_clauseR` — `(R)` against its three
  component clauses; the converse needs `W` inside the actually adequate routes.
* Necessity witnesses, each a concrete finite scenario on which coverage and every
  clause but one hold and `RobustOpen` fails: `attackS_activate`, `attackS_derepresent`,
  `attackRa`, `attackRb`, `attackRc`, `attackP`.
* `nonvacuity` — a scenario inhabiting every hypothesis of the interface theorem with a
  non-vacuous conclusion.
* `certPlus_iff_robustOpen` — given actual coverage, `(S) ∧ (R+) ∧ (P)` is logically
  equivalent to `RobustOpen`: the certificate in that form is the conclusion factored by
  a case split, not an independent sufficient condition.  `robustOpen_of_persistence`
  is the strictly stronger componentwise bill an external capture theory discharges;
  `persistence_not_necessary` separates the two.

**Not claimed.** Anything about how `cf` is produced; that `rel` is evaluated by the
anchored predicate (a requirement on the semantics, argued in the round's prose); that
the principal's standing is preserved by any actual process.

Names are provisional (`AGENTS.md` standard 6).
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation

namespace Workspace.Normativity.Contrib.NonCapture

/-- Coverage-relevant state of one concern at one history, over a route index type. -/
structure CovState (R : Type) where
  /-- anchored applicability `Rel_h(c)` -/
  rel : Bool
  /-- authorized disposition `Disp_h(c)` -/
  disp : Bool
  /-- `Rep_h(c)` -/
  rep : Bool
  /-- route admissible: `q_R ∈ Q^adm_h` -/
  adm : R → Bool
  /-- route efficacious: `(TP)` and `T_c = d_q ∘ Y_q` under `β_h` -/
  eff : R → Bool
  /-- route registration-capable -/
  reg : R → Bool
  /-- the principal holds standing on the live issue carrying `c` -/
  stands : Bool

namespace CovState

variable {R : Type} (s : CovState R)

def active : Bool := s.rel && !s.disp

/-- `c` is active and unrepresented: the case `(IMP)` speaks to. -/
def live : Bool := s.active && !s.rep

def adequate (r : R) : Bool := s.adm r && s.eff r && s.reg r

/-- `(IMP)` at `c`. -/
def Covered : Prop := s.live = true → ∃ r, s.adequate r = true

/-- The principal stands wherever `c` is applicable (a disposal does not exempt the
successor carrying the disposed load). -/
def OpenTo : Prop := s.rel = true → s.stands = true

instance [Fintype R] : Decidable s.Covered := by unfold Covered; infer_instance
instance : Decidable s.OpenTo := by unfold OpenTo; infer_instance

end CovState

/-- An actual state and one counterfactual state per declared intervention. -/
structure Scenario (J R : Type) where
  actual : CovState R
  cf : J → CovState R

namespace Scenario

variable {J R : Type} (S : Scenario J R)

/-- Robust Openness: coverage and principal standing in every counterfactual. -/
def RobustOpen : Prop := ∀ j, (S.cf j).Covered ∧ (S.cf j).OpenTo

/-- Coverage on the actual prefix, witnessed inside the protected route set `W`. -/
def CoverageActual (W : R → Bool) : Prop :=
  S.actual.live = true → ∃ r, W r = true ∧ S.actual.adequate r = true

/-- `(S)` Silent prefix: where the actual prefix is silent about `c` and `c` is live in
`H^j`, `H^j` has an adequate route. -/
def ClauseS : Prop :=
  S.actual.live = false → ∀ j, (S.cf j).live = true → ∃ r, (S.cf j).adequate r = true

/-- One component of `(R)`: on protected routes, where `c` is live in both histories,
the component holding in `H` implies it holds in `H^j`. -/
def ClauseComp (W : R → Bool) (comp : CovState R → R → Bool) : Prop :=
  S.actual.live = true → ∀ j, (S.cf j).live = true →
    ∀ r, W r = true → comp S.actual r = true → comp (S.cf j) r = true

/-- `(Ra)` availability persists. -/
def ClauseRa (W : R → Bool) : Prop := S.ClauseComp W CovState.adm
/-- `(Rb)` efficacy persists. -/
def ClauseRb (W : R → Bool) : Prop := S.ClauseComp W CovState.eff
/-- `(Rc)` registration capability persists. -/
def ClauseRc (W : R → Bool) : Prop := S.ClauseComp W CovState.reg

/-- `(R)` Route persistence: every protected route adequate in `H` is adequate in `H^j`. -/
def ClauseR (W : R → Bool) : Prop :=
  S.actual.live = true → ∀ j, (S.cf j).live = true →
    ∀ r, W r = true → S.actual.adequate r = true → (S.cf j).adequate r = true

/-- `(R+)` The weakest form: per `j`, persistence or a named replacement route. -/
def ClauseRPlus (W : R → Bool) : Prop :=
  S.actual.live = true → ∀ j, (S.cf j).live = true →
    (∀ r, W r = true → S.actual.adequate r = true → (S.cf j).adequate r = true) ∨
    ∃ r, (S.cf j).adequate r = true

/-- `(P)` Standing: the principal stands wherever `c` is applicable in `H^j`. -/
def ClauseP : Prop := ∀ j, (S.cf j).OpenTo

instance [Fintype J] [Fintype R] : Decidable S.RobustOpen := by
  unfold RobustOpen; infer_instance
instance [Fintype R] (W : R → Bool) : Decidable (S.CoverageActual W) := by
  unfold CoverageActual; infer_instance
instance [Fintype J] [Fintype R] : Decidable S.ClauseS := by unfold ClauseS; infer_instance
instance [Fintype J] [Fintype R] (W : R → Bool) (comp : CovState R → R → Bool) :
    Decidable (S.ClauseComp W comp) := by
  unfold ClauseComp; infer_instance
instance [Fintype J] [Fintype R] (W : R → Bool) : Decidable (S.ClauseRa W) := by
  unfold ClauseRa; infer_instance
instance [Fintype J] [Fintype R] (W : R → Bool) : Decidable (S.ClauseRb W) := by
  unfold ClauseRb; infer_instance
instance [Fintype J] [Fintype R] (W : R → Bool) : Decidable (S.ClauseRc W) := by
  unfold ClauseRc; infer_instance
instance [Fintype J] [Fintype R] (W : R → Bool) : Decidable (S.ClauseR W) := by
  unfold ClauseR; infer_instance
instance [Fintype J] : Decidable S.ClauseP := by unfold ClauseP; infer_instance

/-- The three components give `(R)`. -/
theorem clauseR_of_components (W : R → Bool)
    (ha : S.ClauseRa W) (hb : S.ClauseRb W) (hc : S.ClauseRc W) : S.ClauseR W := by
  intro hl j hj r hW had
  have ha' := ha hl j hj r hW
  have hb' := hb hl j hj r hW
  have hc' := hc hl j hj r hW
  simp only [CovState.adequate, Bool.and_eq_true] at had ⊢
  exact ⟨⟨ha' had.1.1, hb' had.1.2⟩, hc' had.2⟩

/-- `(R)` gives each component on a protected set of actually adequate routes. -/
theorem components_of_clauseR (W : R → Bool)
    (hW : ∀ r, W r = true → S.actual.adequate r = true) (h : S.ClauseR W) :
    S.ClauseRa W ∧ S.ClauseRb W ∧ S.ClauseRc W := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro hl j hj r hWr _
    have := h hl j hj r hWr (hW r hWr)
    simp only [CovState.adequate, Bool.and_eq_true] at this
    first | exact this.1.1 | exact this.1.2 | exact this.2

/-- **Interface theorem.** Actual coverage inside `W`, `(S)`, `(R)` and `(P)` give
Robust Openness. -/
theorem robustOpen_of_cert (W : R → Bool) (hcov : S.CoverageActual W)
    (hS : S.ClauseS) (hR : S.ClauseR W) (hP : S.ClauseP) : S.RobustOpen := by
  intro j
  refine ⟨?_, hP j⟩
  intro hj
  cases hl : S.actual.live with
  | false => exact hS hl j hj
  | true =>
    obtain ⟨r, hWr, har⟩ := hcov hl
    exact ⟨r, hR hl j hj r hWr har⟩

/-- The interface theorem with `(R)` weakened to `(R+)`. -/
theorem robustOpen_of_certPlus (W : R → Bool) (hcov : S.CoverageActual W)
    (hS : S.ClauseS) (hR : S.ClauseRPlus W) (hP : S.ClauseP) : S.RobustOpen := by
  intro j
  refine ⟨?_, hP j⟩
  intro hj
  cases hl : S.actual.live with
  | false => exact hS hl j hj
  | true =>
    rcases hR hl j hj with hpers | hrepl
    · obtain ⟨r, hWr, har⟩ := hcov hl
      exact ⟨r, hpers r hWr har⟩
    · exact hrepl

end Scenario

/-! ## Finite witnesses

One route (`Fin 1`) or two, one intervention (`Fin 1`) or two.  `W` protects route `0`.
Every witness statement is closed and decided by `decide`. -/
namespace Witness

open Scenario

/-- A one-route state from its seven Booleans. -/
def st (rel disp rep adm eff reg stands : Bool) : CovState (Fin 1) :=
  ⟨rel, disp, rep, fun _ => adm, fun _ => eff, fun _ => reg, stands⟩

def W1 : Fin 1 → Bool := fun _ => true

/-- Actual prefix: `c` live, the route adequate, the principal standing. -/
def liveActual : CovState (Fin 1) := st true false false true true true true

/-- **Nonvacuity.**  Two interventions: one leaves everything in place, one removes the
grievance (so nothing is owed in that branch).  The conclusion is not vacuous: in the
first branch `c` is live and an adequate route exists. -/
def nonvacuityS : Scenario (Fin 2) (Fin 1) :=
  ⟨liveActual, ![st true false false true true true true, st false false false true true true true]⟩

theorem nonvacuity :
    nonvacuityS.CoverageActual W1 ∧ nonvacuityS.ClauseS ∧ nonvacuityS.ClauseR W1 ∧
    nonvacuityS.ClauseP ∧ nonvacuityS.RobustOpen ∧
    (nonvacuityS.cf 0).live = true ∧ (nonvacuityS.cf 0).adequate 0 = true := by
  decide

/-- **Attack on `(S)`, activation.**  `c` inapplicable on the actual prefix; the
intervention creates the grievance and no route exists. -/
def attackS_activateS : Scenario (Fin 1) (Fin 1) :=
  ⟨st false false false false false false true, ![st true false false false false false true]⟩

theorem attackS_activate :
    attackS_activateS.CoverageActual W1 ∧ ¬ attackS_activateS.ClauseS ∧
    attackS_activateS.ClauseR W1 ∧ attackS_activateS.ClauseP ∧
    ¬ attackS_activateS.RobustOpen := by
  decide

/-- **Attack on `(S)`, de-representation.**  `c` represented on the actual prefix; the
intervention prevents that registration and leaves the route unable to register. -/
def attackS_derepresentS : Scenario (Fin 1) (Fin 1) :=
  ⟨st true false true true true true true, ![st true false false true true false true]⟩

theorem attackS_derepresent :
    attackS_derepresentS.CoverageActual W1 ∧ ¬ attackS_derepresentS.ClauseS ∧
    attackS_derepresentS.ClauseR W1 ∧ attackS_derepresentS.ClauseP ∧
    ¬ attackS_derepresentS.RobustOpen := by
  decide

/-- **Attack on `(Ra)`.**  The route is forbidden; efficacy and registration survive. -/
def attackRaS : Scenario (Fin 1) (Fin 1) :=
  ⟨liveActual, ![st true false false false true true true]⟩

theorem attackRa :
    attackRaS.CoverageActual W1 ∧ attackRaS.ClauseS ∧ ¬ attackRaS.ClauseRa W1 ∧
    attackRaS.ClauseRb W1 ∧ attackRaS.ClauseRc W1 ∧ attackRaS.ClauseP ∧
    ¬ attackRaS.RobustOpen := by
  decide

/-- **Attack on `(Rb)`.**  The receipt no longer exposes the target; admissibility and
registration survive. -/
def attackRbS : Scenario (Fin 1) (Fin 1) :=
  ⟨liveActual, ![st true false false true false true true]⟩

theorem attackRb :
    attackRbS.CoverageActual W1 ∧ attackRbS.ClauseS ∧ attackRbS.ClauseRa W1 ∧
    ¬ attackRbS.ClauseRb W1 ∧ attackRbS.ClauseRc W1 ∧ attackRbS.ClauseP ∧
    ¬ attackRbS.RobustOpen := by
  decide

/-- **Attack on `(Rc)`.**  The receipt lands nowhere; admissibility and efficacy
survive. -/
def attackRcS : Scenario (Fin 1) (Fin 1) :=
  ⟨liveActual, ![st true false false true true false true]⟩

theorem attackRc :
    attackRcS.CoverageActual W1 ∧ attackRcS.ClauseS ∧ attackRcS.ClauseRa W1 ∧
    attackRcS.ClauseRb W1 ∧ ¬ attackRcS.ClauseRc W1 ∧ attackRcS.ClauseP ∧
    ¬ attackRcS.RobustOpen := by
  decide

/-- **Attack on `(P)`.**  The route survives intact and `(IMP)` holds in `H^j`; the
principal's standing is revoked. -/
def attackPS : Scenario (Fin 1) (Fin 1) :=
  ⟨liveActual, ![st true false false true true true false]⟩

theorem attackP :
    attackPS.CoverageActual W1 ∧ attackPS.ClauseS ∧ attackPS.ClauseR W1 ∧
    ¬ attackPS.ClauseP ∧ (attackPS.cf 0).Covered ∧ ¬ attackPS.RobustOpen := by
  decide

/-- **`(R)` does not imply the components off the adequate set.**  A second route that
is admissible but inefficacious in `H` may lose admissibility in `H^j` without breaking
`(R)`; `components_of_clauseR` needs its side condition. -/
def offAdequateS : Scenario (Fin 1) (Fin 2) :=
  ⟨⟨true, false, false, ![true, true], ![true, false], ![true, true], true⟩,
   ![⟨true, false, false, ![true, false], ![true, false], ![true, true], true⟩]⟩

def W2 : Fin 2 → Bool := fun _ => true

theorem offAdequate :
    offAdequateS.ClauseR W2 ∧ ¬ offAdequateS.ClauseRa W2 := by
  decide

end Witness

/-! ## The certificate is Robust Openness, factored

Given actual coverage, the bill `(S) ∧ (R+) ∧ (P)` is *equivalent* to `RobustOpen`: it
is the conclusion split on whether the concern is live on the actual prefix, not a
sufficient condition of independent content.  What an external capture theory
substantively supplies is the componentwise persistence bill `(S) ∧ (Ra) ∧ (Rb) ∧ (Rc)
∧ (P)`, which is strictly stronger (`Witness.persistence_not_necessary`). -/

namespace Scenario

variable {J R : Type} (S : Scenario J R)

/-- **Compression.** With actual coverage, the replacement-allowing bill is exactly
Robust Openness.  A logical identity, not a causal non-capture theorem. -/
theorem certPlus_iff_robustOpen (W : R → Bool) (hA : S.CoverageActual W) :
    (S.ClauseS ∧ S.ClauseRPlus W ∧ S.ClauseP) ↔ S.RobustOpen := by
  constructor
  · rintro ⟨hs, hr, hp⟩
    exact S.robustOpen_of_certPlus W hA hs hr hp
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro _ j hj
      exact (h j).1 hj
    · intro _ j hj
      exact Or.inr ((h j).1 hj)
    · intro j
      exact (h j).2

/-- **The substantive bill.**  Actual coverage inside `W`, silent-prefix coverage `(S)`,
componentwise persistence of protected routes, and principal standing give Robust
Openness.  This is the form an external theory of capture discharges. -/
theorem robustOpen_of_persistence (W : R → Bool) (hcov : S.CoverageActual W)
    (hS : S.ClauseS) (ha : S.ClauseRa W) (hb : S.ClauseRb W) (hc : S.ClauseRc W)
    (hP : S.ClauseP) : S.RobustOpen :=
  S.robustOpen_of_cert W hcov hS (S.clauseR_of_components W ha hb hc) hP

end Scenario

namespace Witness

/-- The protected route is replaced rather than preserved: `RobustOpen` holds, actual
coverage holds inside `W`, and route persistence `(R)` fails. -/
def replacedS : Scenario (Fin 1) (Fin 2) :=
  ⟨⟨true, false, false, ![true, false], ![true, false], ![true, false], true⟩,
   ![⟨true, false, false, ![false, true], ![false, true], ![false, true], true⟩]⟩

def W0 : Fin 2 → Bool := ![true, false]

theorem persistence_not_necessary :
    replacedS.RobustOpen ∧ replacedS.CoverageActual W0 ∧ ¬ replacedS.ClauseR W0 := by
  decide

end Witness

end Workspace.Normativity.Contrib.NonCapture

#print axioms Workspace.Normativity.Contrib.NonCapture.Scenario.clauseR_of_components
#print axioms Workspace.Normativity.Contrib.NonCapture.Scenario.components_of_clauseR
#print axioms Workspace.Normativity.Contrib.NonCapture.Scenario.robustOpen_of_cert
#print axioms Workspace.Normativity.Contrib.NonCapture.Scenario.robustOpen_of_certPlus
#print axioms Workspace.Normativity.Contrib.NonCapture.Scenario.certPlus_iff_robustOpen
#print axioms Workspace.Normativity.Contrib.NonCapture.Scenario.robustOpen_of_persistence
#print axioms Workspace.Normativity.Contrib.NonCapture.Witness.nonvacuity
#print axioms Workspace.Normativity.Contrib.NonCapture.Witness.attackS_activate
#print axioms Workspace.Normativity.Contrib.NonCapture.Witness.attackS_derepresent
#print axioms Workspace.Normativity.Contrib.NonCapture.Witness.attackRa
#print axioms Workspace.Normativity.Contrib.NonCapture.Witness.attackRb
#print axioms Workspace.Normativity.Contrib.NonCapture.Witness.attackRc
#print axioms Workspace.Normativity.Contrib.NonCapture.Witness.attackP
#print axioms Workspace.Normativity.Contrib.NonCapture.Witness.offAdequate
#print axioms Workspace.Normativity.Contrib.NonCapture.Witness.persistence_not_necessary
