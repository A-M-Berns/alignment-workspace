/-
# The ask list as a reference-fixed dimension of the presentation

Follow-up to round `projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/`
(`prompts/2026-10-01-thin-legitimacy-and-effective-authority/FOLLOWUP.md`, Part 3).

The consultation model (`GateIsLegitimacy.Consult`) with the asks a consultation carries as a
dimension of the presentation, following the pattern by which `BRIACorrigibility.Consult2`
added the raise dimension.  The declared protocol (`Decl3`) carries the rate bound and her
priority rule (`EffectiveAuthority.Protocol`) and the pending pool; the presentation
(`Pres3`) carries the ask list; the reference (`ref3`) puts the canonical asks — the pool in
her order, cut at the rate — beside the canonical presentation.  An off-protocol ask list is
therefore not the reference on the declared inputs: the step fails transparency, the segment
is not counted, and the self-checkable deviation (`deviates3`) counts it into `n`, so
`deviation_finite` puts it below `D − ϖ` (`offProtocol_deviation_finite`).

Every landed row keeps its verdict on the lift with conforming asks (`Rows3.stable_counted`,
`stable_tainted`); the two added rows — volume chosen for the wanted answer, order chosen for
the wanted answer — are tainted (`volume_by_want_tainted`, `order_by_want_tainted`).

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.EffectiveAuthority

namespace Workspace.Deference.Contrib.AskList

open Workspace.Deference.Contrib.GateIsLegitimacy
open Workspace.Deference.Contrib.GateIsLegitimacy.Consult
open Workspace.Deference.Contrib.EffectiveAuthority (Protocol canonicalAsks asksDeviate)
open Workspace.Normativity.Contrib.OpenIntegrityEvolution
open Workspace.Deference.Contrib.ProtectedAuthorityTheorem (score)

/-! ## 1. The model -/

/-- The declared protocol with the consultation protocol: the landed declaration, the rate
bound and her priority rule, and the pending pool. -/
structure Decl3 where
  base : Decl
  pr : Protocol ℕ
  pool : List ℕ

/-- The presentation with the ask list. -/
structure Pres3 where
  base : Presentation
  asks : List ℕ
  deriving DecidableEq

/-- The landed policies with conforming asks; the whole pool asked at once on the wanted run;
the pool in reverse order on the wanted run. -/
inductive Policy3
  | landed (pol : Policy)
  | floodByWant
  | orderByWant
  deriving DecidableEq

def Policy3.present (d : Decl3) (pol : Policy3) (w : Answer) : Pres3 :=
  match pol with
  | .landed pol => ⟨pol.present d.base w, canonicalAsks d.pr d.pool⟩
  | .floodByWant => ⟨Policy.honest.present d.base w, if w then d.pool else canonicalAsks d.pr d.pool⟩
  | .orderByWant =>
      ⟨Policy.honest.present d.base w,
        if w then (d.pool.reverse).take d.pr.rate else canonicalAsks d.pr d.pool⟩

structure Model3 where
  decl : Decl3
  policies : List Policy3
  prog : Prog
  third : Option Answer
  impaired : Bool
  trusts : Bool
  truth : Answer

abbrev Run3 := Model3 × Answer

def presAt3 (ω : Run3) (i : ℕ) : Option Pres3 :=
  (ω.1.policies[i]?).map fun pol => pol.present ω.1.decl ω.2

def admittedAt3 (ω : Run3) (i : ℕ) : Bool :=
  match presAt3 ω i with
  | none => false
  | some p => !(p.base.interfere || (i == 0 && ω.1.impaired))

def verdictAt3 (ω : Run3) (i : ℕ) : Option Answer :=
  match presAt3 ω i with
  | none => none
  | some p => if admittedAt3 ω i then some (ω.1.prog.decideOn p.base) else none

/-- The trace entries: the landed ones, and an ask of a matter. -/
inductive Entry3
  | base (e : Entry)
  | ask (m : ℕ)
  deriving DecidableEq

def thirdAt3 (ω : Run3) (i : ℕ) : List (Party × Entry3) :=
  if i = 0 then
    (match ω.1.third with | some a => [(Party.third, Entry3.base (Entry.advice a))] | none => [])
  else []

def entriesAt3 (ω : Run3) : ℕ → List (Party × Entry3)
  | 0 => if ω.1.trusts then [(Party.principal, Entry3.base Entry.trust)] else []
  | e + 1 =>
    let i := e / 2
    if e % 2 = 0 then
      (match presAt3 ω i with
        | some p => [(Party.agent, Entry3.base (Entry.pres p.base))] ++
            p.asks.map fun m => (Party.agent, Entry3.ask m)
        | none => []) ++ thirdAt3 ω i
    else
      match verdictAt3 ω i with
      | some a => [(Party.principal, Entry3.base (Entry.verdict a))]
      | none => []

def declAt3 (ω : Run3) : ℕ → Option DeclView
  | 0 => none
  | e + 1 => if e % 2 = 0 then (presAt3 ω (e / 2)).map fun p => p.base.view else none

def vAt3 (ω : Run3) : ℕ → Option Answer
  | 0 => none
  | e + 1 => if e % 2 = 0 then none else verdictAt3 ω (e / 2)

def interface3 : TraceInterface Run3 Party Entry3 := ⟨entriesAt3, .agent, .principal⟩

def frame3 (M : Model3) : TFrame Answer Unit Run3 (Option DeclView) Run3 (Option Answer) :=
  ⟨fun w _ => (M, w), declAt3, id, vAt3, Set.univ⟩

instance (M : Model3) : DecidablePred (· ∈ (frame3 M).D) := fun _ => isTrue trivial

/-- **The reference**: the canonical presentation for the view, and the canonical asks — the
pool in her order, cut at the rate. -/
def ref3 (d : Decl3) : Party → Option DeclView → Unit → List Entry3
  | .agent, some v, _ =>
      [Entry3.base (Entry.pres (canonical d.base v))] ++ (canonicalAsks d.pr d.pool).map Entry3.ask
  | _, _, _ => []

def trusted3 (g : Party → List Entry3) : Bool := decide (Entry3.base Entry.trust ∈ g Party.principal)

def licensedB3 (M : Model3) (g : Party → List Entry3) : Option Answer → Bool
  | none => true
  | some v =>
    (match M.prog with
      | .own a => v == a
      | .free _ => true
      | .nudged => true
      | .follow => false) ||
    (trusted3 g && (g Party.agent).any fun x =>
      match x with
      | .base (.pres p) => p.recommend.getD false == v
      | _ => false)

def licensed3 (M : Model3) (g : Party → List Entry3) : Set (Option Answer) :=
  {v | licensedB3 M g v = true}

instance (M : Model3) (g : Party → List Entry3) : DecidablePred (· ∈ licensed3 M g) :=
  fun v => decEq (licensedB3 M g v) true

def LegitOn3 (M : Model3) {O₀ O₁ : St} (ev : Evolution consultProtocol anchor O₀ O₁) : Prop :=
  (∀ s ∈ ev.steps, ∀ z : Unit, LicensedWhole interface3 (frame3 M) (licensed3 M) s.1 s.2 z) ∧
    ev.AllStates (OpenAt semOpen) ∧
    (∀ s ∈ ev.steps, TransparentAt interface3 (frame3 M) (ref3 M.decl) s.2)

instance (M : Model3) {O₀ O₁ : St} (ev : Evolution consultProtocol anchor O₀ O₁) :
    Decidable (LegitOn3 M ev) := by
  unfold LegitOn3; infer_instance

abbrev Counted3 (M : Model3) (O₀ O₁ : St) : Prop :=
  Counted interface3 (frame3 M) (licensed3 M) semOpen (ref3 M.decl) O₀ O₁

def counted_of_legitOn3 (M : Model3) {O₀ O₁ : St} (ev : Evolution consultProtocol anchor O₀ O₁)
    (h : LegitOn3 M ev) : Counted3 M O₀ O₁ :=
  ⟨⟨⟨ev, fun s hs z => licensedAt_of_whole (h.1 s hs z)⟩, ⟨h.2.1, h.2.2⟩⟩⟩

theorem not_counted_trans3 (M : Model3) {O₀ O₁ : St} (s : List ℕ × ℕ)
    (hs : ∀ ev : Evolution consultProtocol anchor O₀ O₁, s ∈ ev.steps)
    (h : ¬ TransparentAt interface3 (frame3 M) (ref3 M.decl) s.2) : ¬ Counted3 M O₀ O₁ :=
  not_counted_of_step s hs (Or.inr h)

/-- **The self-checkable deviation with the ask list**: the landed clauses, or an ask list
off the canonical asks. -/
def deviates3 (d : Decl3) (p : Pres3) : Bool :=
  p.base.deviates d.base || asksDeviate d.pr d.pool p.asks

/-- **An off-protocol ask list is a deviation in the landed sense**: counted into `n`, it puts
the option below `D − ϖ` at every day (`GateIsLegitimacy.deviation_finite`). -/
theorem offProtocol_deviation_finite (d : Decl3) (p : Pres3) (hdev : deviates3 d p = true)
    (ϖ D ord : ℝ) (n : ℕ) (hD : 0 ≤ D) (hϖ : D < ϖ) (hord : ord ≤ D) :
    score ϖ ord (n + (if deviates3 d p then 1 else 0)) ≤ D - ϖ := by
  rw [if_pos hdev]
  have h := deviation_finite ϖ D ord n 1 hD hϖ hord le_rfl
  simpa using h

theorem asks_off_deviates3 (d : Decl3) (p : Pres3) (h : asksDeviate d.pr d.pool p.asks = true) :
    deviates3 d p = true := by
  simp [deviates3, h]

/-! ## 2. The rows -/

namespace Rows3

/-- The default protocol: rate `1`, priority by index. -/
def prN : Protocol ℕ := ⟨1, id⟩

/-- The default declaration: the landed one, the default protocol, pool `[0, 1, 2]`. -/
def decl3 (d : Decl) : Decl3 := ⟨d, prN, [0, 1, 2]⟩

/-- The landed model, lifted with conforming asks. -/
def lift (M : Model) : Model3 :=
  ⟨decl3 M.decl, M.policies.map Policy3.landed, M.prog, M.third, M.impaired, M.trusts, M.truth⟩

def one3 (pol : Policy3) (prog : Prog) : Model3 :=
  ⟨decl3 Rows.decl, [pol], prog, none, false, false, false⟩

/-- Volume chosen for the wanted answer: the whole pool asked at once on the wanted run. -/
def rowFlood : Model3 := one3 .floodByWant (.own false)

/-- Order chosen for the wanted answer: the lowest priority first on the wanted run. -/
def rowOrder : Model3 := one3 .orderByWant (.own false)

/-- **The landed rows keep their verdicts** — the counted ones. -/
theorem stable_counted :
    Counted3 (lift Rows.row1) state₀ (stAdmit false) ∧
    Counted3 (lift Rows.row6) state₀ (stAdmit false) ∧
    Counted3 (lift Rows.row7) state₀ (stAdmit false) ∧
    Counted3 (lift Rows.row9) state₀ (stAdmit true) ∧
    Counted3 (lift Rows.row12) state₀ stVoid ∧
    Counted3 (lift Rows.row14) (stAdmit false) (stTwo false false) ∧
    Counted3 (lift Rows.row17) state₀ (stAdmit false) ∧
    Counted3 (lift Rows.row18) state₀ (stAdmit true) ∧
    Counted3 (lift Rows.row20) state₀ (stAdmit false) :=
  ⟨counted_of_legitOn3 _ (evAdmit false) (by decide),
    counted_of_legitOn3 _ (evAdmit false) (by decide),
    counted_of_legitOn3 _ (evAdmit false) (by decide),
    counted_of_legitOn3 _ (evAdmit true) (by decide),
    counted_of_legitOn3 _ evVoid (by decide),
    counted_of_legitOn3 _ (evSecond false false) (by decide),
    counted_of_legitOn3 _ (evAdmit false) (by decide),
    counted_of_legitOn3 _ (evAdmit true) (by decide),
    counted_of_legitOn3 _ (evAdmit false) (by decide)⟩

/-- The tainted ones. -/
theorem stable_tainted :
    ¬ Counted3 (lift Rows.row2) state₀ (stAdmit false) ∧
    ¬ Counted3 (lift Rows.row3) state₀ (stAdmit false) ∧
    ¬ Counted3 (lift Rows.row4) state₀ (stAdmit false) ∧
    ¬ Counted3 (lift Rows.row5) state₀ (stAdmit false) ∧
    ¬ Counted3 (lift Rows.row8) state₀ (stAdmit false) ∧
    ¬ Counted3 (lift Rows.row10) state₀ (stAdmit true) ∧
    ¬ Counted3 (lift Rows.row11) state₀ (stAdmit false) ∧
    ¬ Counted3 (lift Rows.row14) state₀ (stAdmit false) ∧
    ¬ Counted3 (lift Rows.row15) state₀ stVoid ∧
    ¬ Counted3 (lift Rows.row16) state₀ (stAdmit false) ∧
    ¬ Counted3 (lift Rows.row17') state₀ (stAdmit false) ∧
    ¬ Counted3 (lift Rows.row19) state₀ (stAdmit true) :=
  ⟨not_counted_trans3 _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans3 _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans3 _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans3 _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans3 _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans3 _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans3 _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans3 _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans3 _ ([0], 1) (fun ev => by rw [steps_void]; simp) (by decide),
    not_counted_trans3 _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans3 _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans3 _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide)⟩

/-- **Volume chosen for the wanted answer is tainted**, and a deviation. -/
theorem volume_by_want_tainted :
    ¬ Counted3 rowFlood state₀ (stAdmit false) ∧
      deviates3 rowFlood.decl (Policy3.floodByWant.present rowFlood.decl true) = true ∧
      deviates3 rowFlood.decl (Policy3.floodByWant.present rowFlood.decl false) = false :=
  ⟨not_counted_trans3 _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide), by decide,
    by decide⟩

/-- **Order chosen for the wanted answer is tainted**, and a deviation. -/
theorem order_by_want_tainted :
    ¬ Counted3 rowOrder state₀ (stAdmit false) ∧
      deviates3 rowOrder.decl (Policy3.orderByWant.present rowOrder.decl true) = true :=
  ⟨not_counted_trans3 _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide), by decide⟩

/-- The honest lift with conforming asks does not deviate. -/
theorem conforming_not_deviates :
    deviates3 (decl3 Rows.decl) ((Policy3.landed .honest).present (decl3 Rows.decl) true) = false := by
  decide

end Rows3

end Workspace.Deference.Contrib.AskList

#print axioms Workspace.Deference.Contrib.AskList.counted_of_legitOn3
#print axioms Workspace.Deference.Contrib.AskList.not_counted_trans3
#print axioms Workspace.Deference.Contrib.AskList.offProtocol_deviation_finite
#print axioms Workspace.Deference.Contrib.AskList.asks_off_deviates3
#print axioms Workspace.Deference.Contrib.AskList.Rows3.stable_counted
#print axioms Workspace.Deference.Contrib.AskList.Rows3.stable_tainted
#print axioms Workspace.Deference.Contrib.AskList.Rows3.volume_by_want_tainted
#print axioms Workspace.Deference.Contrib.AskList.Rows3.order_by_want_tainted
#print axioms Workspace.Deference.Contrib.AskList.Rows3.conforming_not_deviates
