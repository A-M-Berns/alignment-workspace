/-
# Decisions on the record: the case of an assessed act, and consistency of conduct

Round `projects/normativity/rounds/2026-11-08-content-recollection/`, follow-up of 2026-11-09,
matter 2, to fixture level.

An **assessed act** (`AssessedAct`) carries the grounds the act was taken on, the surviving
grounds against it, and the assessor's verdict.  The chooser's **proposal** is that its grounds
prevail (`proposal`); the **case** the record keeps is set by the assessment (`case`): an act
assessed adequate makes its grounds the winners, an act assessed a shortfall makes them the
losers.  `ofCertificate` is the adapter from `DecisionComponent.ActCertificate` at
`Ent := Form d`: the certificate supplies the grounds; the grounds against and the verdict are
further inputs, and its licence and lineage are not read.

**Consistency of conduct** (`ConsistentConduct`): each choice is permitted by the case base of
the assessed acts before it — by `PrecedentHolding.permitted_iff`, by the holding of the
reasoner's own assessed past (`consistentConduct_cons_iff`).

Fixtures on `(X, ¬X, D)`.  The first act, on `P(X) ≥ 3/4` against `P(¬X) ≥ 1/2`, is assessed a
shortfall.  A later choice on `P(X) ≥ 7/10` against `P(¬X) ≥ 3/5` is forbidden by the assessed
past and would be permitted had the act itself set the precedent (`assessor_sets_precedent`,
`repeat_forbidden`); a later choice on `P(X) ≥ 3/4` with a ground of a new kind beside it is
permitted (`distinguished_consistent`).

**Allowed, not better.**  Where the holding backs a choice its reverse is forbidden
(`backed_reverse_forbidden`), and a backed choice leaves the reach unchanged
(`reach_cons_of_backed`); where both a choice and its reverse are permitted the reach relates
their reason sets in neither direction (`permitted_both_silent`).  The assessor is bound as
well: a shortfall verdict on a choice the reach backs leaves the assessed case base
unrationalizable (`shortfall_of_backed_not_rationalizable`, `assessor_bound`).

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.PrecedentHolding
import Workspace.Deference.Contrib.DecisionComponent

namespace Workspace.Normativity.Contrib.AssessedConduct

open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.PrecedentConstraint
open Workspace.Normativity.Contrib.PrecedentHolding
open Workspace.Deference.Contrib.DecisionComponent

variable {d : ℕ}

/-! ## 1. The assessed act -/

/-- The assessor's verdict on an act. -/
inductive Verdict
  | adequate
  | shortfall
  deriving DecidableEq

/-- **An assessed act**: the grounds it was taken on, the surviving grounds against it, and the
assessment. -/
structure AssessedAct (d : ℕ) where
  grounds : List (Form d)
  against : List (Form d)
  verdict : Verdict
  deriving DecidableEq

/-- What the chooser proposed in acting: its grounds prevail over the grounds against. -/
def AssessedAct.proposal (a : AssessedAct d) : Case d := ⟨a.grounds, a.against⟩

/-- **The case an assessed act sets**: the assessment fixes which side won. -/
def AssessedAct.case (a : AssessedAct d) : Case d :=
  match a.verdict with
  | .adequate => ⟨a.grounds, a.against⟩
  | .shortfall => ⟨a.against, a.grounds⟩

/-- **The adapter from an act certificate**: its grounds, with the surviving grounds against
the act and the assessor's verdict supplied beside it. -/
def ofCertificate {M Ob : Type*} (cert : ActCertificate (Form d) M Ob) (against : List (Form d))
    (v : Verdict) : AssessedAct d :=
  ⟨cert.grounds, against, v⟩

theorem ofCertificate_case_adequate {M Ob : Type*} (cert : ActCertificate (Form d) M Ob)
    (against : List (Form d)) :
    (ofCertificate cert against .adequate).case = ⟨cert.grounds, against⟩ := rfl

theorem ofCertificate_case_shortfall {M Ob : Type*} (cert : ActCertificate (Form d) M Ob)
    (against : List (Form d)) :
    (ofCertificate cert against .shortfall).case = ⟨against, cert.grounds⟩ := rfl

/-- The case base of an assessed past. -/
def caseBase (past : List (AssessedAct d)) : List (Case d) := past.map AssessedAct.case

/-- **Consistency of conduct**, most recent act first: each choice is permitted by the case
base of the assessed acts before it. -/
def ConsistentConduct : List (AssessedAct d) → Prop
  | [] => True
  | a :: past => Permitted (caseBase past) a.proposal ∧ ConsistentConduct past

/-- Consistency of conduct reads the holding of the assessed past: the past is rationalizable
and its reach does not put the grounds against the act at or above its grounds. -/
theorem consistentConduct_cons_iff (a : AssessedAct d) (past : List (AssessedAct d)) :
    ConsistentConduct (a :: past) ↔
      (Rationalizable (caseBase past) ∧ ¬ Reach (caseBase past) a.against a.grounds) ∧
        ConsistentConduct past := by
  show Permitted (caseBase past) a.proposal ∧ _ ↔ _
  rw [permitted_iff]
  rfl

/-! ## 2. Allowed, not better -/

/-- The holding **backs** a case: it already puts the case's winners above its losers. -/
def Backed (Γ : List (Case d)) (c : Case d) : Prop := Holding Γ c.winners c.losers

/-- Where the reach puts one reason set at or above another, the reverse decision is
forbidden. -/
theorem reach_reverse_forbidden {Γ : List (Case d)} {V U : List (Form d)} (h : Reach Γ V U) :
    ¬ Permitted Γ ⟨U, V⟩ :=
  fun hp => ((permitted_iff Γ ⟨U, V⟩).1 hp).2 h

/-- **Where the holding backs a choice, its reverse is forbidden.** -/
theorem backed_reverse_forbidden {Γ : List (Case d)} {c : Case d} (h : Backed Γ c) :
    ¬ Permitted Γ ⟨c.losers, c.winners⟩ :=
  reach_reverse_forbidden (Or.inr h)

/-- **A backed choice sets no new precedent**: it leaves the reach unchanged. -/
theorem reach_cons_of_backed {Γ : List (Case d)} {c : Case d} (h : Backed Γ c)
    (V U : List (Form d)) : Reach (c :: Γ) V U ↔ Reach Γ V U := by
  rw [reach_cons]
  constructor
  · rintro (h' | ⟨h₁, h₂⟩)
    · exact h'
    · exact h₁.trans (Reach.trans (Or.inr h) h₂)
  · exact Or.inl

/-- **Where a choice and its reverse are both permitted, the reach is silent between them**:
it relates their reason sets in neither direction. -/
theorem permitted_both_silent {Γ : List (Case d)} {V U : List (Form d)}
    (h₁ : Permitted Γ ⟨V, U⟩) (h₂ : Permitted Γ ⟨U, V⟩) : ¬ Reach Γ V U ∧ ¬ Reach Γ U V :=
  ⟨((permitted_iff Γ ⟨U, V⟩).1 h₂).2, ((permitted_iff Γ ⟨V, U⟩).1 h₁).2⟩

/-- **The assessor is bound.**  A shortfall verdict on an act whose grounds the reach of the
assessed past puts at or above the grounds against it leaves the assessed case base
unrationalizable. -/
theorem shortfall_of_backed_not_rationalizable (past : List (AssessedAct d)) (a : AssessedAct d)
    (hv : a.verdict = .shortfall) (h : Reach (caseBase past) a.grounds a.against) :
    ¬ Rationalizable (caseBase (a :: past)) := by
  have hc : a.case = ⟨a.against, a.grounds⟩ := by unfold AssessedAct.case; rw [hv]
  show ¬ Rationalizable (a.case :: caseBase past)
  rw [hc]
  exact reach_reverse_forbidden h

/-! ## 3. Fixtures on `(X, ¬X, D)` -/

/-- The first act: on `P(X) ≥ 3/4` against `P(¬X) ≥ 1/2`, assessed a shortfall. -/
def first : AssessedAct 3 := ⟨[Form.premise 0 (3/4)], [Form.premise 1 (1/2)], .shortfall⟩

/-- The assessment sets the precedent: `P(¬X) ≥ 1/2` prevailed over `P(X) ≥ 3/4`. -/
theorem first_case : first.case = ⟨[Form.premise 1 (1/2)], [Form.premise 0 (3/4)]⟩ := rfl

/-- A later choice: on `P(X) ≥ 7/10` against `P(¬X) ≥ 3/5`. -/
def again (v : Verdict) : AssessedAct 3 := ⟨[Form.premise 0 (7/10)], [Form.premise 1 (3/5)], v⟩

/-- The later choice's proposal, whatever its assessment. -/
def againProposal : Case 3 := ⟨[Form.premise 0 (7/10)], [Form.premise 1 (3/5)]⟩

theorem again_proposal (v : Verdict) : (again v).proposal = againProposal := rfl

/-- **The assessor sets the precedent, not the chooser.**  The later choice is forbidden by
the assessed case and would be permitted had the first act's own proposal been the precedent. -/
theorem assessor_sets_precedent (v : Verdict) :
    ¬ Permitted [first.case] (again v).proposal ∧ Permitted [first.proposal] (again v).proposal := by
  rw [again_proposal]
  exact ⟨fun h => (by decide +kernel : ¬ Consistent [againProposal, first.case]) h.consistent,
    rationalizable_of_rank (fun _ => 0) (by decide +kernel)⟩

/-- **A later choice forbidden by an earlier assessed act.** -/
theorem repeat_forbidden (v : Verdict) : ¬ ConsistentConduct [again v, first] :=
  fun h => (assessor_sets_precedent v).1 h.1

/-- A later choice with a ground of a new kind beside `P(X) ≥ 3/4`: `P(X) ≥ 9/10 · P(D)`. -/
def distinguishedAct : AssessedAct 3 :=
  ⟨[Form.premise 0 (3/4), Form.strength 2 0 (9/10)], [Form.premise 1 (1/2)], .adequate⟩

/-- **A later choice permitted by distinguishing.** -/
theorem distinguished_consistent : ConsistentConduct [distinguishedAct, first] :=
  ⟨rationalizable_of_rank (fun c => if c = first.case then 1 else 0) (by decide +kernel),
    rationalizable_of_rank (fun _ => 0) (by decide +kernel), trivial⟩

/-- The reverse of the first act, in the same situation: on `P(¬X) ≥ 1/2` against
`P(X) ≥ 3/4`. -/
def reverseAct (v : Verdict) : AssessedAct 3 :=
  ⟨[Form.premise 1 (1/2)], [Form.premise 0 (3/4)], v⟩

/-- **The assessor bound on the fixture.**  After the first act, the reverse choice is backed
by the assessed past and permitted; assessing it adequate keeps the assessed case base
rationalizable, and assessing it a shortfall does not. -/
theorem assessor_bound :
    Backed (caseBase [first]) (reverseAct .adequate).proposal ∧
      ConsistentConduct [reverseAct .adequate, first] ∧
      Rationalizable (caseBase [reverseAct .adequate, first]) ∧
      ¬ Rationalizable (caseBase [reverseAct .shortfall, first]) := by
  have hback : Backed (caseBase [first]) (reverseAct .adequate).proposal :=
    Relation.TransGen.single ⟨first.case, List.mem_cons_self, Covers.refl _, Covers.refl _⟩
  have hperm : Permitted (caseBase [first]) (reverseAct .adequate).proposal :=
    rationalizable_of_rank (fun _ => 0) (by decide +kernel)
  exact ⟨hback, ⟨hperm, rationalizable_of_rank (fun _ => 0) (by decide +kernel), trivial⟩, hperm,
    shortfall_of_backed_not_rationalizable [first] (reverseAct .shortfall) rfl (Or.inr hback)⟩

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.AssessedConduct.Verdict
#print axioms Workspace.Normativity.Contrib.AssessedConduct.AssessedAct
#print axioms Workspace.Normativity.Contrib.AssessedConduct.AssessedAct.proposal
#print axioms Workspace.Normativity.Contrib.AssessedConduct.AssessedAct.case
#print axioms Workspace.Normativity.Contrib.AssessedConduct.ofCertificate
#print axioms Workspace.Normativity.Contrib.AssessedConduct.ofCertificate_case_adequate
#print axioms Workspace.Normativity.Contrib.AssessedConduct.ofCertificate_case_shortfall
#print axioms Workspace.Normativity.Contrib.AssessedConduct.caseBase
#print axioms Workspace.Normativity.Contrib.AssessedConduct.ConsistentConduct
#print axioms Workspace.Normativity.Contrib.AssessedConduct.consistentConduct_cons_iff
#print axioms Workspace.Normativity.Contrib.AssessedConduct.Backed
#print axioms Workspace.Normativity.Contrib.AssessedConduct.reach_reverse_forbidden
#print axioms Workspace.Normativity.Contrib.AssessedConduct.backed_reverse_forbidden
#print axioms Workspace.Normativity.Contrib.AssessedConduct.reach_cons_of_backed
#print axioms Workspace.Normativity.Contrib.AssessedConduct.permitted_both_silent
#print axioms Workspace.Normativity.Contrib.AssessedConduct.shortfall_of_backed_not_rationalizable
#print axioms Workspace.Normativity.Contrib.AssessedConduct.first
#print axioms Workspace.Normativity.Contrib.AssessedConduct.first_case
#print axioms Workspace.Normativity.Contrib.AssessedConduct.again
#print axioms Workspace.Normativity.Contrib.AssessedConduct.againProposal
#print axioms Workspace.Normativity.Contrib.AssessedConduct.again_proposal
#print axioms Workspace.Normativity.Contrib.AssessedConduct.assessor_sets_precedent
#print axioms Workspace.Normativity.Contrib.AssessedConduct.repeat_forbidden
#print axioms Workspace.Normativity.Contrib.AssessedConduct.distinguishedAct
#print axioms Workspace.Normativity.Contrib.AssessedConduct.distinguished_consistent
#print axioms Workspace.Normativity.Contrib.AssessedConduct.reverseAct
#print axioms Workspace.Normativity.Contrib.AssessedConduct.assessor_bound

end Workspace.Normativity.Contrib.AssessedConduct
