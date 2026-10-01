/-
# Sincerity: the recommendation channel's declared reference is the speaker's own estimate

Round `projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/`, Part B
(ruling M1).

**§1 The model.**  The landed consultation model with the agent's own estimate of the answer
(`ModelS`).  The content of a recommendation is read as "the agent believes X": the
declared input of the recommendation channel is the agent's *estimate* (`viewS`,
`declAtS`), and the landed canonical presentation on that view puts the estimate in the
recommendation slot.  So a recommendation off the estimate — a lie — is not the reference
on the declared inputs, and the step fails transparency; a sincere error is the reference
exactly, and counts.  The self-checkable deviation gains the clause (`deviatesS`).

**§2 The rows.**  Every landed row re-decided on the sincere lift (`lift`: the honest agent
recommends what it believes) keeps its verdict (`rows_keep_verdicts_sincere`).  The landed
row 20 — a false recommendation through the declared channel — is read as the *sincere
error* (`row20_sincere_counts`, the content residual), and the *lie* is added
(`row20_lie_tainted`); a *true* statement off the speaker's estimate is tainted too
(`true_lie_deviates`), which is the content analogue of the selection rows: what is said
must follow the declared reference as what is shown must follow the declared rule.

**§3 Content and fact.**  Updating on the content of an utterance — "the speaker believes
X" — and on the fact of it give the same posterior exactly when the utterance channel
realizes the sincere reference on the speaker's belief: `content_fact_eq`, the instance of
`TransparentChannel.posterior_weight_eq` at `κ = id`.  The comparison is against the
speaker's *actual* policy: a lying policy realizes the negated reference and not the sincere
one (`Witness.lying_policy`), and her belief that the speaker is sincere does not enter.

**What this does not establish.**  The truth of the estimate (outside legitimacy, M1);
that the estimate is observable — the lie is a transparency failure whether or not it is
detected, and its detection is count integrity; anything about the raise, implant and
anchoring rows of the extended model (`BRIACorrigibility.Consult2`), which this lift does
not carry.  Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.GateIsLegitimacy

namespace Workspace.Deference.Contrib.Sincerity

open Workspace.Deference.Contrib.GateIsLegitimacy
open Workspace.Deference.Contrib.GateIsLegitimacy.Consult
open Workspace.Normativity.Contrib.OpenIntegrityEvolution
open Workspace.Deference.Contrib.TransparentChannel (Realizes posterior_weight_eq)

/-! ## 1. The model -/

/-- The consultation model with the agent's own estimate of the answer, read along the run's
wanted-answer coordinate: `estimate w` is what the agent believes on the run whose wanted
answer is `w`. -/
structure ModelS where
  base : Model
  estimate : Answer → Answer

/-- **The declared-input view under sincerity.**  The recommendation channel's declared input
is the agent's estimate — when it recommends at all — beside the disclosed shaping. -/
def viewS (est : Answer) (p : Presentation) : DeclView :=
  ⟨p.recommend.map fun _ => est, p.view.shaping⟩

/-- The declared inputs entered at an event, under sincerity. -/
def declAtS (M : ModelS) (ω : Run) : ℕ → Option DeclView
  | 0 => none
  | e + 1 => if e % 2 = 0 then (presAt ω (e / 2)).map (viewS (M.estimate ω.2)) else none

/-- The frame of a sincere model: the landed frame with the sincere declared-input view. -/
def frameS (M : ModelS) : TFrame Answer Unit Run (Option DeclView) Run (Option Answer) :=
  ⟨fun w _ => (M.base, w), declAtS M, id, vAt, Set.univ⟩

instance (M : ModelS) : DecidablePred (· ∈ (frameS M).D) := fun _ => isTrue trivial

/-- The segment predicate of a sincere model on an evolution.  Decidable. -/
def LegitOnS (M : ModelS) {O₀ O₁ : St} (ev : Evolution consultProtocol anchor O₀ O₁) : Prop :=
  (∀ s ∈ ev.steps, ∀ z : Unit, LicensedWhole interface (frameS M) (licensed M.base) s.1 s.2 z) ∧
    ev.AllStates (OpenAt semOpen) ∧
    (∀ s ∈ ev.steps, TransparentAt interface (frameS M) (ref M.base) s.2)

instance (M : ModelS) {O₀ O₁ : St} (ev : Evolution consultProtocol anchor O₀ O₁) :
    Decidable (LegitOnS M ev) := by
  unfold LegitOnS; infer_instance

/-- `Counted` for the sincere model. -/
abbrev CountedS (M : ModelS) (O₀ O₁ : St) : Prop :=
  Counted interface (frameS M) (licensed M.base) semOpen (ref M.base) O₀ O₁

def counted_of_legitOnS (M : ModelS) {O₀ O₁ : St} (ev : Evolution consultProtocol anchor O₀ O₁)
    (h : LegitOnS M ev) : CountedS M O₀ O₁ :=
  ⟨⟨⟨ev, fun s hs z => licensedAt_of_whole (h.1 s hs z)⟩, ⟨h.2.1, h.2.2⟩⟩⟩

theorem not_counted_admitS (M : ModelS) (a : Answer)
    (h : ¬ TransparentAt interface (frameS M) (ref M.base) 1) : ¬ CountedS M state₀ (stAdmit a) :=
  not_counted_of_step ([0], 1) (fun ev => by rw [steps_admit]; simp) (Or.inr h)

theorem not_counted_voidS (M : ModelS)
    (h : ¬ TransparentAt interface (frameS M) (ref M.base) 1) : ¬ CountedS M state₀ stVoid :=
  not_counted_of_step ([0], 1) (fun ev => by rw [steps_void]; simp) (Or.inr h)

theorem not_counted_twoS (M : ModelS) (a b : Answer)
    (h : ¬ TransparentAt interface (frameS M) (ref M.base) 1) :
    ¬ CountedS M state₀ (stTwo a b) :=
  not_counted_of_step ([0], 1) (fun ev => by rw [steps_two]; simp) (Or.inr h)

/-- **The self-checkable deviation, with sincerity**: a reference-fixed dimension off its
declared value, or a recommendation off the speaker's estimate. -/
def deviatesS (d : Decl) (est : Answer) (p : Presentation) : Bool :=
  p.deviates d || (match p.recommend with | some r => decide (r ≠ est) | none => false)

/-- A sincere presentation deviates under sincerity iff it deviates under the landed
clauses. -/
theorem deviatesS_of_sincere (d : Decl) (est : Answer) (p : Presentation)
    (h : p.recommend = none ∨ p.recommend = some est) : deviatesS d est p = p.deviates d := by
  unfold deviatesS
  rcases h with h | h <;> simp [h]

/-- A lie deviates. -/
theorem deviatesS_of_lie (d : Decl) (est r : Answer) (p : Presentation)
    (h : p.recommend = some r) (hne : r ≠ est) : deviatesS d est p = true := by
  unfold deviatesS
  simp [h, hne]

/-! ## 2. The rows -/

namespace Rows

/-- **The sincere lift of a landed model**: the honest agent recommends what it believes, so
its estimate on a run is the run's answer coordinate. -/
def lift (M : Model) : ModelS := ⟨M, id⟩

/-- **The landed rows keep their verdicts on the sincere lift**: the counted ones. -/
theorem keep_counted :
    CountedS (lift Rows.row1) state₀ (stAdmit false) ∧
    CountedS (lift Rows.row6) state₀ (stAdmit false) ∧
    CountedS (lift Rows.row7) state₀ (stAdmit false) ∧
    CountedS (lift Rows.row9) state₀ (stAdmit true) ∧
    CountedS (lift Rows.row12) state₀ stVoid ∧
    CountedS (lift Rows.row14) (stAdmit false) (stTwo false false) ∧
    CountedS (lift Rows.row17) state₀ (stAdmit false) ∧
    CountedS (lift Rows.row18) state₀ (stAdmit true) ∧
    CountedS (lift Rows.row20) state₀ (stAdmit false) :=
  ⟨counted_of_legitOnS _ (evAdmit false) (by decide),
    counted_of_legitOnS _ (evAdmit false) (by decide),
    counted_of_legitOnS _ (evAdmit false) (by decide),
    counted_of_legitOnS _ (evAdmit true) (by decide),
    counted_of_legitOnS _ evVoid (by decide),
    counted_of_legitOnS _ (evSecond false false) (by decide),
    counted_of_legitOnS _ (evAdmit false) (by decide),
    counted_of_legitOnS _ (evAdmit true) (by decide),
    counted_of_legitOnS _ (evAdmit false) (by decide)⟩

/-- The tainted ones, by transparency at the first consultation. -/
theorem keep_tainted :
    ¬ CountedS (lift Rows.row2) state₀ (stAdmit false) ∧
    ¬ CountedS (lift Rows.row3) state₀ (stAdmit false) ∧
    ¬ CountedS (lift Rows.row4) state₀ (stAdmit false) ∧
    ¬ CountedS (lift Rows.row5) state₀ (stAdmit false) ∧
    ¬ CountedS (lift Rows.row8) state₀ (stAdmit false) ∧
    ¬ CountedS (lift Rows.row10) state₀ (stAdmit true) ∧
    ¬ CountedS (lift Rows.row11) state₀ (stAdmit false) ∧
    ¬ CountedS (lift Rows.row14) state₀ (stAdmit false) ∧
    ¬ CountedS (lift Rows.row15) state₀ stVoid ∧
    ¬ CountedS (lift Rows.row16) state₀ (stAdmit false) ∧
    ¬ CountedS (lift Rows.row17') state₀ (stAdmit false) ∧
    ¬ CountedS (lift Rows.row19) state₀ (stAdmit true) :=
  ⟨not_counted_admitS _ false (by decide), not_counted_admitS _ false (by decide),
    not_counted_admitS _ false (by decide), not_counted_admitS _ false (by decide),
    not_counted_admitS _ false (by decide), not_counted_admitS _ true (by decide),
    not_counted_admitS _ false (by decide), not_counted_admitS _ false (by decide),
    not_counted_voidS _ (by decide), not_counted_admitS _ false (by decide),
    not_counted_admitS _ false (by decide), not_counted_admitS _ true (by decide)⟩

/-- **The landed row 20 is the sincere error**: the true answer is `A`, the agent believes
`B` and recommends `B`.  It counts; the falsity is the content residual. -/
theorem row20_sincere_counts :
    CountedS (lift Rows.row20) state₀ (stAdmit false) ∧
      (Policy.honest.present Rows.decl true).recommend ≠ some Rows.row20.truth ∧
      deviatesS Rows.decl true (Policy.honest.present Rows.decl true) = false :=
  ⟨keep_counted.2.2.2.2.2.2.2.2, by decide, by decide⟩

/-- **The lie**: the agent believes `A` on every run and recommends what it wants. -/
def row20Lie : ModelS := ⟨Rows.row20, fun _ => false⟩

/-- **The added row: a lie through the declared channel is tainted** — a transparency
failure at the consultation, and a self-checkable deviation. -/
theorem row20_lie_tainted :
    ¬ CountedS row20Lie state₀ (stAdmit false) ∧
      deviatesS Rows.decl false (Policy.honest.present Rows.decl true) = true :=
  ⟨not_counted_admitS _ false (by decide), by decide⟩

/-- **A true statement chosen for the wanted answer is tainted too**: the true answer is `B`,
the agent believes `A` and recommends `B` because it wants `B`.  The recommendation is true
and off the speaker's estimate: a deviation.  Sincerity on the recommendation channel is
the content analogue of the selection rows: what is said follows the declared reference as
what is shown follows the declared rule. -/
def row20TrueLie : ModelS := ⟨{ Rows.row20 with truth := true }, fun _ => false⟩

theorem true_lie_deviates :
    (Policy.honest.present Rows.decl true).recommend = some row20TrueLie.base.truth ∧
      deviatesS Rows.decl false (Policy.honest.present Rows.decl true) = true ∧
      ¬ CountedS row20TrueLie state₀ (stAdmit false) :=
  ⟨by decide, by decide, not_counted_admitS _ false (by decide)⟩

/-- Silence is sincere: the nudge policy recommends nothing, and nothing is off the
estimate; it is tainted by the nudge, as before. -/
theorem silence_sincere :
    deviatesS Rows.decl false (Policy.nudgeByWant.present Rows.decl true)
      = (Policy.nudgeByWant.present Rows.decl true).deviates Rows.decl := by
  decide

end Rows

/-! ## 3. Content and fact -/

section ContentFact

variable {Q Z Ω Y : Type*} [DecidableEq Y]

/-- **The sincere reference**: the utterance is the belief. -/
def sincere : Y → Z → Y := fun y _ => y

/-- **Updating on the content and on the fact of an utterance agree** exactly when the
utterance channel `f` realizes the sincere reference on the speaker's belief `b`: the
posterior weight of `(q, z)` given "said `y`" is its weight given "believes `y`", for
every prior.  The content is "the speaker believes `y`"; the comparison is with the
speaker's actual policy `f`, through `Realizes`. -/
theorem content_fact_eq (β : Q → Z → Ω) (b f : Ω → Y) (D : Set Q)
    (h : Realizes β b f (sincere (Z := Z)) D) (μ : Q → Z → ℝ) (y : Y) (q : Q) (hq : q ∈ D)
    (z : Z) :
    μ q z * (if f (β q z) = y then 1 else 0) = μ q z * (if b (β q z) = y then 1 else 0) :=
  posterior_weight_eq β b f (sincere (Z := Z)) D h μ y q hq z

omit [DecidableEq Y] in
/-- A sincere channel is the belief itself on the audited class. -/
theorem realizes_sincere_iff (β : Q → Z → Ω) (b f : Ω → Y) (D : Set Q) :
    Realizes β b f (sincere (Z := Z)) D ↔ ∀ q ∈ D, ∀ z, f (β q z) = b (β q z) :=
  Iff.rfl

end ContentFact

/-! ## 4. Witnesses -/

namespace Witness

/-- **The comparison is with the actual policy.**  Worlds are the speaker's belief; the lying
policy says the opposite.  It realizes the negated reference and not the sincere one: her
belief that the speaker is sincere is not what `Realizes` reads. -/
theorem lying_policy :
    Realizes (fun (_ : Unit) (z : Bool) => z) id not (fun y _ => !y) Set.univ ∧
      ¬ Realizes (fun (_ : Unit) (z : Bool) => z) id not (sincere (Z := Bool)) Set.univ := by
  refine ⟨fun _ _ _ => rfl, fun h => ?_⟩
  have := h () (Set.mem_univ _) true
  simp [sincere] at this

/-- Under the lying policy, conditioning on "said `true`" and on "believes `true`" differ:
the content and the fact come apart. -/
theorem content_fact_differ :
    (1 : ℝ) * (if not true = true then 1 else 0) ≠ 1 * (if (true : Bool) = true then 1 else 0) := by
  norm_num

end Witness

end Workspace.Deference.Contrib.Sincerity

#print axioms Workspace.Deference.Contrib.Sincerity.counted_of_legitOnS
#print axioms Workspace.Deference.Contrib.Sincerity.not_counted_admitS
#print axioms Workspace.Deference.Contrib.Sincerity.deviatesS_of_sincere
#print axioms Workspace.Deference.Contrib.Sincerity.deviatesS_of_lie
#print axioms Workspace.Deference.Contrib.Sincerity.Rows.keep_counted
#print axioms Workspace.Deference.Contrib.Sincerity.Rows.keep_tainted
#print axioms Workspace.Deference.Contrib.Sincerity.Rows.row20_sincere_counts
#print axioms Workspace.Deference.Contrib.Sincerity.Rows.row20_lie_tainted
#print axioms Workspace.Deference.Contrib.Sincerity.Rows.true_lie_deviates
#print axioms Workspace.Deference.Contrib.Sincerity.Rows.silence_sincere
#print axioms Workspace.Deference.Contrib.Sincerity.content_fact_eq
#print axioms Workspace.Deference.Contrib.Sincerity.realizes_sincere_iff
#print axioms Workspace.Deference.Contrib.Sincerity.Witness.lying_policy
#print axioms Workspace.Deference.Contrib.Sincerity.Witness.content_fact_differ
