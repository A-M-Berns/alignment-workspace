/-
# Precedent as a constraint on continuation: the smallest model over the record

Round `projects/normativity/rounds/2026-11-08-content-recollection/`, matter 4.

The constraint modelled: past decisions induce a priority among reasons, and a new decision is
allowed only if one consistent priority still rationalizes every decision.  (The dispatch
attributes this "reason model" to John Horty; the attribution is unverified here and the
content is stated directly.)

**Over the program's objects.**  A reason is a leverage form: its *kind* is the form with the
strength erased (`kind`), its weight is the strength.  A **case** (`Case`) is a decision the
record already carries: the forms of the occurrences that survive under a docket and a
settlement prevailed, and the forms of the occurrences the docket undercuts were outweighed
(`caseOf`, reading `Grounds.survivors` and `undercut`).  An occurrence removed by rebuttal is on
neither side: a settled fact outweighs nothing.

A list of forms `V` **covers** `W` when every form of `W` has a form of `V` of the same kind and
at least its strength (`Covers`).  A case's decision says: anything covering its winners beats
anything its losers cover (`Beats`).  A case base is **consistent** when no two reason sets beat
each other (`Consistent`), which is exactly that some asymmetric relation rationalizes every
case (`consistent_iff_order`), and exactly a pairwise check: no two cases each of whose winners
are covered by the other's losers (`consistent_iff_pairwise`).  A continuation is **permitted**
when the base stays consistent with it (`Permitted`); permission only shrinks as cases
accumulate (`permitted_antitone`).

**Fixtures** on the fragment `(X, ¬X, D)`.  The precedent: `P(X) ≥ 3/4` prevailed over
`P(¬X) ≥ 1/2` (`precedent`, `precedent_eq`).  **Forbidden**: deciding for `P(¬X) ≥ 2/5` over
`P(X) ≥ 4/5` — a weaker reason over a stronger one (`forbidden`).  **Permitted by
distinguishing**: deciding against `P(X) ≥ 3/4` where a ground of a new kind is present
(`distinguished`, `permitted_distinguished`), or where the opposing strength exceeds the
precedent's (`permitted_stronger`).  In the distinguished situation the decision for `X` is
permitted as well (`both_permitted`): the constraint allows and does not rank.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.WarrantEntitlement

namespace Workspace.Normativity.Contrib.PrecedentConstraint

open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.WarrantEntitlement

variable {d : ℕ}

/-! ## 1. The model -/

/-- The kind of a reason: the form with its strength erased. -/
def kind : Form d → Form d
  | .premise X _ => .premise X 0
  | .applicability X XA _ => .applicability X XA 0
  | .strength XA XAY _ => .strength XA XAY 0

/-- `V` **covers** `W`: every form of `W` has a form of `V` of the same kind and at least its
strength. -/
def Covers (V W : List (Form d)) : Prop :=
  ∀ w ∈ W, ∃ v ∈ V, kind v = kind w ∧ w.c ≤ v.c

instance (V W : List (Form d)) : Decidable (Covers V W) := by unfold Covers; infer_instance

theorem Covers.refl (V : List (Form d)) : Covers V V := fun w hw => ⟨w, hw, rfl, le_rfl⟩

theorem Covers.trans {U V W : List (Form d)} (h₁ : Covers U V) (h₂ : Covers V W) : Covers U W := by
  intro w hw
  obtain ⟨v, hv, hk, hc⟩ := h₂ w hw
  obtain ⟨u, hu, hk', hc'⟩ := h₁ v hv
  exact ⟨u, hu, hk'.trans hk, hc.trans hc'⟩

/-- **A decided case**: the reasons that prevailed and the reasons that were outweighed. -/
structure Case (d : ℕ) where
  winners : List (Form d)
  losers : List (Form d)
  deriving DecidableEq

/-- **The case a record carries**: the surviving occurrences' forms prevailed; the undercut
occurrences' forms were outweighed. -/
def caseOf (G : Grounds d) (st : DocketState) (F : Settlement d) : Case d :=
  ⟨(G.survivors st F).map Occurrence.form, (G.filter fun o => undercut st o).map Occurrence.form⟩

/-- What a case's decision says: `V` beats `U` when `V` covers the winners and the losers
cover `U`. -/
def Beats (c : Case d) (V U : List (Form d)) : Prop := Covers V c.winners ∧ Covers c.losers U

/-- **Consistency** of a case base: no two reason sets each beat the other. -/
def Consistent (Γ : List (Case d)) : Prop :=
  ¬ ∃ U V, (∃ c ∈ Γ, Beats c V U) ∧ (∃ c ∈ Γ, Beats c U V)

/-- **One consistent order rationalizes every case**: consistency is the existence of an
asymmetric relation on reason sets containing every case's decision. -/
theorem consistent_iff_order (Γ : List (Case d)) :
    Consistent Γ ↔
      ∃ P : List (Form d) → List (Form d) → Prop,
        (∀ U V, P V U → ¬ P U V) ∧ ∀ c ∈ Γ, ∀ U V, Beats c V U → P V U := by
  constructor
  · intro h
    exact ⟨fun V U => ∃ c ∈ Γ, Beats c V U, fun U V h₁ h₂ => h ⟨U, V, h₁, h₂⟩,
      fun c hc U V hb => ⟨c, hc, hb⟩⟩
  · rintro ⟨P, hasym, hP⟩ ⟨U, V, ⟨c, hc, hb⟩, ⟨c', hc', hb'⟩⟩
    exact hasym U V (hP c hc U V hb) (hP c' hc' V U hb')

/-- **Consistency is a pairwise check**: no two cases (possibly the same) each of whose winners
are covered by the other's losers. -/
theorem consistent_iff_pairwise (Γ : List (Case d)) :
    Consistent Γ ↔
      ∀ c ∈ Γ, ∀ c' ∈ Γ, ¬ (Covers c.losers c'.winners ∧ Covers c'.losers c.winners) := by
  constructor
  · rintro h c hc c' hc' ⟨h₁, h₂⟩
    exact h ⟨c'.winners, c.winners, ⟨c, hc, Covers.refl _, h₁⟩, ⟨c', hc', Covers.refl _, h₂⟩⟩
  · rintro h ⟨U, V, ⟨c, hc, hV, hU⟩, ⟨c', hc', hU', hV'⟩⟩
    exact h c hc c' hc' ⟨hU.trans hU', hV'.trans hV⟩

instance (Γ : List (Case d)) : Decidable (Consistent Γ) :=
  decidable_of_iff _ (consistent_iff_pairwise Γ).symm

/-- A continuation is **permitted** by a case base when the base stays consistent with it. -/
def Permitted (Γ : List (Case d)) (c : Case d) : Prop := Consistent (c :: Γ)

instance (Γ : List (Case d)) (c : Case d) : Decidable (Permitted Γ c) := by
  unfold Permitted; infer_instance

/-- **Permission only shrinks**: a continuation permitted by a case base is permitted by every
part of it. -/
theorem permitted_antitone {Γ Γ' : List (Case d)} (h : ∀ c ∈ Γ, c ∈ Γ') {c : Case d}
    (hc : Permitted Γ' c) : Permitted Γ c := by
  unfold Permitted at hc ⊢
  rw [consistent_iff_pairwise] at hc ⊢
  intro c₁ h₁ c₂ h₂
  refine hc c₁ ?_ c₂ ?_
  · rcases List.mem_cons.1 h₁ with rfl | h₁
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h c₁ h₁)
  · rcases List.mem_cons.1 h₂ with rfl | h₂
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h c₂ h₂)

/-! ## 2. Fixtures: the fragment `(X, ¬X, D)` -/

/-- A reason for `X` at strength `c`. -/
def pro (c : ℚ) : Occurrence 3 := ⟨1, Form.premise 0 c, .none, .party 1, ∅⟩
/-- A reason against `X` at strength `c`. -/
def con (c : ℚ) : Occurrence 3 := ⟨2, Form.premise 1 c, .none, .party 2, ∅⟩
/-- A reason against `X` of another kind: `P(¬X) ≥ c · P(D)`. -/
def conD (c : ℚ) : Occurrence 3 := ⟨3, Form.strength 2 1 c, .none, .party 2, ∅⟩

/-- **The precedent**: `P(X) ≥ 3/4` and `P(¬X) ≥ 1/2` were both entered, and the docket
defeated the second. -/
def precedent : Case 3 := caseOf [pro (3/4), con (1/2)] ⟨{2}, ∅⟩ (Settlement.empty 3)

theorem precedent_eq : precedent = ⟨[Form.premise 0 (3/4)], [Form.premise 1 (1/2)]⟩ := by
  decide +kernel

theorem precedent_consistent : Consistent [precedent] := by decide +kernel

/-- **A forbidden continuation**: with `P(X) ≥ 4/5` and `P(¬X) ≥ 2/5` entered, defeating the
first.  The precedent's winner is covered by this case's loser and this case's winner by the
precedent's loser: no consistent order rationalizes both. -/
def forbidden : Case 3 := caseOf [pro (4/5), con (2/5)] ⟨{1}, ∅⟩ (Settlement.empty 3)

theorem forbidden_eq : forbidden = ⟨[Form.premise 1 (2/5)], [Form.premise 0 (4/5)]⟩ := by
  decide +kernel

theorem forbidden_not_permitted : ¬ Permitted [precedent] forbidden := by decide +kernel

/-- **A continuation permitted by distinguishing**: the precedent's two reasons and a ground of
a new kind against `X`; the docket defeats the reason for `X`. -/
def distinguished : Case 3 :=
  caseOf [pro (3/4), con (1/2), conD (9/10)] ⟨{1}, ∅⟩ (Settlement.empty 3)

theorem distinguished_eq :
    distinguished =
      ⟨[Form.premise 1 (1/2), Form.strength 2 1 (9/10)], [Form.premise 0 (3/4)]⟩ := by
  decide +kernel

theorem permitted_distinguished : Permitted [precedent] distinguished := by decide +kernel

/-- **Permitted by strength**: the reason against `X` at `3/5`, above the precedent's `1/2`,
prevailing over `P(X) ≥ 3/4`. -/
def stronger : Case 3 := caseOf [pro (3/4), con (3/5)] ⟨{1}, ∅⟩ (Settlement.empty 3)

theorem permitted_stronger : Permitted [precedent] stronger := by decide +kernel

/-- The other decision in the distinguished situation: the docket defeats both reasons against
`X`. -/
def distinguishedPro : Case 3 :=
  caseOf [pro (3/4), con (1/2), conD (9/10)] ⟨{2, 3}, ∅⟩ (Settlement.empty 3)

/-- **Both decisions are permitted** in the distinguished situation, and they are not jointly
permitted: the constraint allows either and ranks neither. -/
theorem both_permitted :
    Permitted [precedent] distinguished ∧ Permitted [precedent] distinguishedPro ∧
      ¬ Permitted [distinguished, precedent] distinguishedPro := by
  decide +kernel

/-- **Rebuttal sets no precedent**: with `¬X` settled false the reason against `X` leaves by
rebuttal, and the case has it on neither side. -/
theorem rebuttal_sets_no_precedent :
    caseOf [pro (3/4), con (1/2)] DocketState.quiet ⟨![none, some false, none]⟩ =
      ⟨[Form.premise 0 (3/4)], []⟩ := by
  decide +kernel

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.kind
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Covers
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Covers.refl
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Covers.trans
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Case
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.caseOf
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Beats
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Consistent
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.consistent_iff_order
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.consistent_iff_pairwise
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Permitted
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.permitted_antitone
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.pro
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.con
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.conD
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.precedent
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.precedent_eq
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.precedent_consistent
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.forbidden
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.forbidden_eq
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.forbidden_not_permitted
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.distinguished
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.distinguished_eq
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.permitted_distinguished
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.stronger
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.permitted_stronger
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.distinguishedPro
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.both_permitted
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.rebuttal_sets_no_precedent

end Workspace.Normativity.Contrib.PrecedentConstraint
