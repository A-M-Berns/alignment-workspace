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
(`caseOf`, reading `Grounds.survivors` and `undercut`).

A list of forms `V` **covers** `W` when every form of `W` has a form of `V` of the same kind and
at least its strength (`Covers`).  A case's decision says: anything covering its winners beats
anything its losers cover (`Beats`); `V` dominates `U` in a case base when some case says so
(`Dominates`).  A case base is **rationalizable** when one strict order — irreflexive and
transitive — contains every case's decision (`Rationalizable`).  That holds exactly when
dominance has no cycle (`rationalizable_iff_no_dominance_cycle`), and exactly when the graph on
cases, with an edge from a case to each case whose winners its losers cover, has no cycle
(`rationalizable_iff_acyclic`); a rank on cases increasing along edges suffices
(`rationalizable_of_rank`).  The pairwise condition — no two reason sets dominate each other
(`Consistent`, `consistent_iff_pairwise`) — is necessary (`Rationalizable.consistent`) and not
sufficient: three cases in a cycle pass it and have no order (`cycle_not_rationalizable`).  A
continuation is **permitted** when the base stays rationalizable with it (`Permitted`);
permission only shrinks as cases accumulate (`permitted_antitone`).

**Fixtures** on the fragment `(X, ¬X, D)`.  The precedent: `P(X) ≥ 3/4` prevailed over
`P(¬X) ≥ 1/2` (`precedent`, `precedent_eq`).  **Forbidden**: deciding for `P(¬X) ≥ 2/5` over
`P(X) ≥ 4/5` — a weaker reason over a stronger one (`forbidden_not_permitted`).  **Permitted by
distinguishing**: deciding against `P(X) ≥ 3/4` where a ground of a new kind is present
(`permitted_distinguished`), or where the opposing strength exceeds the precedent's
(`permitted_stronger`).  In the distinguished situation the decision for `X` is permitted as
well and the two are not jointly permitted (`both_permitted`): the constraint allows and does
not rank.  On the quiet docket an occurrence removed by rebuttal is on neither side of the case
(`rebuttal_sets_no_precedent`); `caseOf` counts every undercut occurrence a loser whatever the
settlement.

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

/-- `V` **dominates** `U` in a case base: some case's decision says `V` beats `U`. -/
def Dominates (Γ : List (Case d)) (V U : List (Form d)) : Prop := ∃ c ∈ Γ, Beats c V U

/-- **Rationalizable**: one strict order on reason sets — irreflexive and transitive — contains
every case's decision. -/
def Rationalizable (Γ : List (Case d)) : Prop :=
  ∃ P : List (Form d) → List (Form d) → Prop,
    (∀ U, ¬ P U U) ∧ (∀ U V W, P U V → P V W → P U W) ∧ ∀ U V, Dominates Γ V U → P V U

/-- **A case base is rationalizable iff dominance has no cycle.** -/
theorem rationalizable_iff_no_dominance_cycle (Γ : List (Case d)) :
    Rationalizable Γ ↔ ∀ U, ¬ Relation.TransGen (Dominates Γ) U U := by
  constructor
  · rintro ⟨P, hirr, htr, hP⟩ U hU
    have key : ∀ V W, Relation.TransGen (Dominates Γ) V W → P V W := by
      intro V W h
      induction h with
      | single h => exact hP _ _ h
      | tail _ h ih => exact htr _ _ _ ih (hP _ _ h)
    exact hirr U (key U U hU)
  · intro h
    exact ⟨Relation.TransGen (Dominates Γ), h, fun _ _ _ => Relation.TransGen.trans,
      fun _ _ hd => Relation.TransGen.single hd⟩

/-- The graph on cases: `c'` follows `c` when `c`'s losers cover `c'`'s winners, so that `c`'s
decision puts the winners of `c'` below its own. -/
def Next (Γ : List (Case d)) (c c' : Case d) : Prop :=
  c ∈ Γ ∧ c' ∈ Γ ∧ Covers c.losers c'.winners

instance (Γ : List (Case d)) (c c' : Case d) : Decidable (Next Γ c c') := by
  unfold Next; infer_instance

/-- **A case base is rationalizable iff its graph on cases has no cycle.** -/
theorem rationalizable_iff_acyclic (Γ : List (Case d)) :
    Rationalizable Γ ↔ ∀ c, ¬ Relation.TransGen (Next Γ) c c := by
  rw [rationalizable_iff_no_dominance_cycle]
  constructor
  · intro h c hc
    exact h c.winners (Relation.TransGen.lift Case.winners
      (fun a b hab => ⟨a, hab.1, Covers.refl _, hab.2.2⟩) hc)
  · intro h U hU
    have chain : ∀ V W, Relation.TransGen (Dominates Γ) V W →
        ∃ c₁ c₂, Covers V c₁.winners ∧ Covers c₂.losers W ∧ c₁ ∈ Γ ∧ c₂ ∈ Γ ∧
          Relation.ReflTransGen (Next Γ) c₁ c₂ := by
      intro V W hVW
      induction hVW with
      | single hd =>
        obtain ⟨c, hc, hV, hW⟩ := hd
        exact ⟨c, c, hV, hW, hc, hc, Relation.ReflTransGen.refl⟩
      | tail _ hd ih =>
        obtain ⟨c₁, c₂, hV, hM, h1, h2, hr⟩ := ih
        obtain ⟨c, hc, hMc, hcW⟩ := hd
        exact ⟨c₁, c, hV, hcW, h1, hc, hr.tail ⟨h2, hc, hM.trans hMc⟩⟩
    obtain ⟨c₁, c₂, hV, hW, h1, h2, hr⟩ := chain U U hU
    exact h c₁ (Relation.TransGen.tail' hr ⟨h2, h1, hW.trans hV⟩)

/-- **The pairwise condition**: no two reason sets each dominate the other. -/
def Consistent (Γ : List (Case d)) : Prop :=
  ¬ ∃ U V, Dominates Γ V U ∧ Dominates Γ U V

/-- The pairwise condition on cases: no two cases (possibly the same) each of whose winners are
covered by the other's losers. -/
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

/-- A rationalizable case base satisfies the pairwise condition. -/
theorem Rationalizable.consistent {Γ : List (Case d)} (h : Rationalizable Γ) : Consistent Γ := by
  obtain ⟨P, hirr, htr, hP⟩ := h
  rintro ⟨U, V, h₁, h₂⟩
  exact hirr V (htr _ _ _ (hP _ _ h₁) (hP _ _ h₂))

/-- **A rank on cases increasing along the graph's edges** makes the base rationalizable. -/
theorem rationalizable_of_rank {Γ : List (Case d)} (rank : Case d → ℕ)
    (h : ∀ c ∈ Γ, ∀ c' ∈ Γ, Covers c.losers c'.winners → rank c < rank c') :
    Rationalizable Γ := by
  rw [rationalizable_iff_acyclic]
  intro c hc
  have key : ∀ a b, Relation.TransGen (Next Γ) a b → rank a < rank b := by
    intro a b hab
    induction hab with
    | single hn => exact h _ hn.1 _ hn.2.1 hn.2.2
    | tail _ hn ih => exact ih.trans (h _ hn.1 _ hn.2.1 hn.2.2)
  exact lt_irrefl _ (key c c hc)

/-- A continuation is **permitted** by a case base when the base stays rationalizable with
it. -/
def Permitted (Γ : List (Case d)) (c : Case d) : Prop := Rationalizable (c :: Γ)

/-- **Permission only shrinks**: a continuation permitted by a case base is permitted by every
part of it. -/
theorem permitted_antitone {Γ Γ' : List (Case d)} (h : ∀ c ∈ Γ, c ∈ Γ') {c : Case d}
    (hc : Permitted Γ' c) : Permitted Γ c := by
  obtain ⟨P, hirr, htr, hP⟩ := hc
  refine ⟨P, hirr, htr, fun U V hd => hP U V ?_⟩
  obtain ⟨c₁, h₁, hb⟩ := hd
  refine ⟨c₁, ?_, hb⟩
  rcases List.mem_cons.1 h₁ with rfl | h₁
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (h c₁ h₁)

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

theorem precedent_rationalizable : Rationalizable [precedent] :=
  rationalizable_of_rank (fun _ => 0) (by decide +kernel)

/-- **A forbidden continuation**: with `P(X) ≥ 4/5` and `P(¬X) ≥ 2/5` entered, defeating the
first.  The precedent's winner is covered by this case's loser and this case's winner by the
precedent's loser: no order rationalizes both. -/
def forbidden : Case 3 := caseOf [pro (4/5), con (2/5)] ⟨{1}, ∅⟩ (Settlement.empty 3)

theorem forbidden_eq : forbidden = ⟨[Form.premise 1 (2/5)], [Form.premise 0 (4/5)]⟩ := by
  decide +kernel

theorem forbidden_not_permitted : ¬ Permitted [precedent] forbidden :=
  fun h => (by decide +kernel : ¬ Consistent [forbidden, precedent]) h.consistent

/-- **A continuation permitted by distinguishing**: the precedent's two reasons and a ground of
a new kind against `X`; the docket defeats the reason for `X`. -/
def distinguished : Case 3 :=
  caseOf [pro (3/4), con (1/2), conD (9/10)] ⟨{1}, ∅⟩ (Settlement.empty 3)

theorem distinguished_eq :
    distinguished =
      ⟨[Form.premise 1 (1/2), Form.strength 2 1 (9/10)], [Form.premise 0 (3/4)]⟩ := by
  decide +kernel

theorem permitted_distinguished : Permitted [precedent] distinguished :=
  rationalizable_of_rank (fun c => if c = precedent then 1 else 0) (by decide +kernel)

/-- **Permitted by strength**: the reason against `X` at `3/5`, above the precedent's `1/2`,
prevailing over `P(X) ≥ 3/4`. -/
def stronger : Case 3 := caseOf [pro (3/4), con (3/5)] ⟨{1}, ∅⟩ (Settlement.empty 3)

theorem permitted_stronger : Permitted [precedent] stronger :=
  rationalizable_of_rank (fun c => if c = precedent then 1 else 0) (by decide +kernel)

/-- The other decision in the distinguished situation: the docket defeats both reasons against
`X`. -/
def distinguishedPro : Case 3 :=
  caseOf [pro (3/4), con (1/2), conD (9/10)] ⟨{2, 3}, ∅⟩ (Settlement.empty 3)

/-- **Both decisions are permitted** in the distinguished situation, and they are not jointly
permitted: the constraint allows either and ranks neither. -/
theorem both_permitted :
    Permitted [precedent] distinguished ∧ Permitted [precedent] distinguishedPro ∧
      ¬ Permitted [distinguished, precedent] distinguishedPro :=
  ⟨permitted_distinguished, rationalizable_of_rank (fun _ => 0) (by decide +kernel),
    fun h => (by decide +kernel :
      ¬ Consistent [distinguishedPro, distinguished, precedent]) h.consistent⟩

/-- **Rebuttal sets no precedent on the quiet docket**: with `¬X` settled false the reason
against `X` leaves by rebuttal, and the case has it on neither side.  (`caseOf` counts every
undercut occurrence a loser, whatever the settlement.) -/
theorem rebuttal_sets_no_precedent :
    caseOf [pro (3/4), con (1/2)] DocketState.quiet ⟨![none, some false, none]⟩ =
      ⟨[Form.premise 0 (3/4)], []⟩ := by
  decide +kernel

/-- Three cases in a cycle: `X` over `¬X`, `¬X` over `D`, `D` over `X`, each a premise at
`1/2`. -/
def cycle : List (Case 3) :=
  [⟨[Form.premise 0 (1/2)], [Form.premise 1 (1/2)]⟩,
   ⟨[Form.premise 1 (1/2)], [Form.premise 2 (1/2)]⟩,
   ⟨[Form.premise 2 (1/2)], [Form.premise 0 (1/2)]⟩]

/-- **The pairwise condition is not enough**: the three cases pass it and no strict order
rationalizes them. -/
theorem cycle_not_rationalizable : Consistent cycle ∧ ¬ Rationalizable cycle := by
  refine ⟨by decide +kernel, fun h => ?_⟩
  rw [rationalizable_iff_acyclic] at h
  refine h ⟨[Form.premise 0 (1/2)], [Form.premise 1 (1/2)]⟩
    (Relation.TransGen.head (b := ⟨[Form.premise 1 (1/2)], [Form.premise 2 (1/2)]⟩) ?_
      (Relation.TransGen.head (b := ⟨[Form.premise 2 (1/2)], [Form.premise 0 (1/2)]⟩) ?_
        (Relation.TransGen.single ?_))) <;> decide +kernel

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.kind
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Covers
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Covers.refl
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Covers.trans
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Case
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.caseOf
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Beats
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Dominates
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Rationalizable
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.rationalizable_iff_no_dominance_cycle
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Next
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.rationalizable_iff_acyclic
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Consistent
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.consistent_iff_pairwise
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Rationalizable.consistent
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.rationalizable_of_rank
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.Permitted
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.permitted_antitone
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.pro
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.con
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.conD
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.precedent
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.precedent_eq
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.precedent_rationalizable
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
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.cycle
#print axioms Workspace.Normativity.Contrib.PrecedentConstraint.cycle_not_rationalizable

end Workspace.Normativity.Contrib.PrecedentConstraint
