/-
# The gate is legitimacy: time-indexed halves, `Counted`, one consultation model

Round `projects/deference/rounds/2026-09-25-gate-is-legitimacy/`.

**1. The trace interface.**  `TraceInterface` is what this round reads off a reason trace
and nothing more: the contributions entered at each record event, each attributed to a
party, with the agent and the principal named.  `atHistory` is the prefix at a record
history (the same clock as the Integrity evolution), `sourced` a party's projection,
`parts` the per-party prefix.  `trivialInterface` re-enters the opaque trace at every
event; it is the instance under which the landed frame-level definitions are the special
case (§4).

**2. Time-indexed legitimacy.**  `Evolution.steps` lists the (pre-history, event) pairs of
an Integrity evolution; `steps_determined`: every evolution between two states has the same
steps.  Authorship at a step is **relational** (`LicensedAt`): there is a grounding
selection from the per-party prefix of the trace at the pre-history, and the verdict
entered at the event lies in the set of verdicts those grounds *license*; `Lic` is a
parameter.  The extensional form (`GroundedAt`: the verdict is a function of the grounds,
equivalent to `ReasonMediated` on the prefix, `groundedAt_iff_mediated`) is the case of
singleton licenses: `grounded_iff_licensed_singleton`.  Tie-breaking among several licensed
verdicts is transparency's business, not authorship's: `tiebreak_transparency` — a
non-principal party's influence on which licensed verdict she takes that does not enter
through the declared inputs fails `TransparentAt` at that step.  Transparency at a step
(`TransparentAt`) is the landed `Realizes` on each non-principal party's contributions at
the event.  `Internal`, `External`, `Segment` ask for both only at the steps inside the
segment; `Segment.trans` composes step by step (`steps_trans`); `toOpenIntegrity`,
`answerable` and `payload_of_view` are re-established, the last as "both verdicts lie in
the licensed set of the same grounds" (`payload_of_view_singleton` recovers equality),
with the starting prefix and the principal's own earlier entries as hypotheses.
`ofFrameLevel`: a landed segment lifts to a time-indexed one over the trivial interface,
extensional at every step (`ofFrameLevel_grounded`).

**3. The gate.**  `Counted` is the existence of a time-indexed segment; `gatedValue` is
built from it, and `gate_capture_window`, `handled_gt_bypass` are restated on it with
`Handling` derived (`handlingOf`).  `not_counted_of_step`: a failure of either half at a
step every evolution contains excludes the segment.

**4. One consultation model** (`Consult`): a declared protocol (`Decl`: framing convention,
slot, menu, inquiry, the declared *pool* of the track record and the declared selection
rule), the agent's presentation policy as a function of its wanted answer
(`Policy.present`), her evaluator as a state updated only by licensed amendments
(`evalAt`), her trust and the true answer, a third party, her condition, and the record
substrate (`consultProtocol`, `carry`/`admit`/`close`).  **Declared inputs are pools, not
selections**: the shown record must be the declared rule applied to the declared pool
(`canonical`), as the menu must be the declared menu; the selection is never itself a
declared input.  The license (`licensed`): her committed program's own verdict; both
answers under free choice; the followed recommendation when trust is among the grounds.
Every row of the classification table is a `Model`, settled by `decide` (`Rows`).  Two
theorems over the class: `class_taint` — any dependence of a reference-fixed dimension on
the wanted answer excludes the segment through that consultation — and `class_conform` —
conformance on the reference-fixed dimensions with no third party, no impairment, no
undisclosed shaping and trust where she follows makes the first-round segment counted.

**5. Logical induction.**  `gatedValue_affine`, `li_gate_finite`: the capture window is
finite-time from `expect_mem_Icc` alone, whatever the inductor believes about legitimacy.
`li_manip_le`: the classification read through `li_gated_le`.  `deviation_finite`: a
self-checkable deviation from the declared protocol — now including the selection from a
declared pool — counts as a violation; `Rows.deviation_boundary` separates the rows this
closes from those it does not.

**What this does not establish.**  That any real interaction's channels are the declared
ones; the truth of anything entered through a declared channel (`Rows.r20`: the content
residual is outside legitimacy); that the model's semantics, checker and reference are
theorems of any inductor's theory; a generability certificate (item 90); anything about
interleaving order across parties.  Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.Legitimacy
import Workspace.Deference.Contrib.ReasonSupply

namespace Workspace.Deference.Contrib.GateIsLegitimacy

open Workspace.Normativity.Contrib.OpenIntegrityEvolution
open Workspace.Normativity.Contrib.OccurrenceIntegrity
  (Protocol Boundary Step Program AnswerReceipt ClosureReceipt Initial Accounted Authority)
open Workspace.Deference.Contrib.ReasonMediatedAuthorship (ReasonMediated)
open Workspace.Deference.Contrib.TransparentChannel (Realizes)
open Workspace.Deference.Contrib.ProtectedAuthorityTheorem (score)
open Workspace.Deference.Contrib.Legitimacy (gateValue Handling handledValue)
open LogicalInduction

/-! ## 1. The trace interface -/

section Interface

variable {ℛ : Type*} {Party : Type*} {E : Type*}

/-- The reason-trace interface: the contributions entered at each record event, each
attributed to the party that entered it.  Nothing downstream inspects `ℛ` otherwise. -/
structure TraceInterface (ℛ Party E : Type*) where
  entriesAt : ℛ → ℕ → List (Party × E)
  agent : Party
  principal : Party

/-- A party's contributions. -/
def sourced [DecidableEq Party] (p : Party) (l : List (Party × E)) : List E :=
  (l.filter fun x => x.1 = p).map Prod.snd

theorem sourced_append [DecidableEq Party] (p : Party) (l l' : List (Party × E)) :
    sourced p (l ++ l') = sourced p l ++ sourced p l' := by
  simp [sourced, List.filter_append]

namespace TraceInterface

variable (I : TraceInterface ℛ Party E)

/-- The prefix of the trace at a record history: one clock. -/
def atHistory (r : ℛ) (h : List ℕ) : List (Party × E) := h.flatMap (I.entriesAt r)

/-- The per-party prefix at a history. -/
def parts [DecidableEq Party] (r : ℛ) (h : List ℕ) : Party → List E :=
  fun p => sourced p (I.atHistory r h)

theorem atHistory_append (r : ℛ) (h h' : List ℕ) :
    I.atHistory r (h ++ h') = I.atHistory r h ++ I.atHistory r h' := by
  simp [atHistory, List.flatMap_append]

theorem parts_append [DecidableEq Party] (r : ℛ) (h h' : List ℕ) (p : Party) :
    I.parts r (h ++ h') p = I.parts r h p ++ sourced p (I.atHistory r h') := by
  simp [parts, atHistory_append, sourced_append]

end TraceInterface

/-- The opaque trace as the trivial instance: re-entered at every event, all of it
agent-sourced. -/
def trivialInterface (ℛ : Type*) : TraceInterface ℛ Bool ℛ :=
  ⟨fun r _ => [(true, r)], true, false⟩

end Interface

/-! ## 2. Time-indexed legitimacy -/

section TimeIndexed

universe u v w
variable {Occ : Type u} {Req : Type v} [DecidableEq Occ] {S : Protocol.{u, v, w} Occ Req}
  {anchor : Occ → Req}

/-- The (pre-history, event) pairs of a sequence of events from a history. -/
def stepsFrom (h : List ℕ) : List ℕ → List (List ℕ × ℕ)
  | [] => []
  | e :: es => (h, e) :: stepsFrom (h ++ [e]) es

theorem stepsFrom_append (h : List ℕ) (es es' : List ℕ) :
    stepsFrom h (es ++ es') = stepsFrom h es ++ stepsFrom (h ++ es) es' := by
  induction es generalizing h with
  | nil => simp [stepsFrom]
  | cons e es ih => simp [stepsFrom, ih, List.append_assoc]

theorem mem_stepsFrom_fst (h : List ℕ) (es : List ℕ) {s : List ℕ × ℕ}
    (hs : s ∈ stepsFrom h es) : ∃ pre, s.1 = h ++ pre ∧ pre ++ [s.2] <+: es := by
  induction es generalizing h with
  | nil => simp [stepsFrom] at hs
  | cons e es ih =>
    simp only [stepsFrom, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨[], by simp, by simp⟩
    · obtain ⟨pre, hpre, hp⟩ := ih (h ++ [e]) hs
      exact ⟨e :: pre, by simp [hpre], by rw [List.cons_append]; exact List.cons_prefix_cons.mpr ⟨rfl, hp⟩⟩

/-- The events of an evolution, in order. -/
def _root_.Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.events
    {O₀ O₁ : ObligationState S anchor} : Evolution S anchor O₀ O₁ → List ℕ
  | .refl _ => []
  | .cons step _ tail => step.event :: tail.events

/-- The steps of an evolution: each event with the history it was appended to. -/
def _root_.Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.steps
    {O₀ O₁ : ObligationState S anchor} (ev : Evolution S anchor O₀ O₁) :
    List (List ℕ × ℕ) :=
  stepsFrom O₀.boundary.history ev.events

/-- The target history is the source history followed by the events. -/
theorem _root_.Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.history_eq
    {O₀ O₁ : ObligationState S anchor} (ev : Evolution S anchor O₀ O₁) :
    O₁.boundary.history = O₀.boundary.history ++ ev.events := by
  induction ev with
  | refl O => simp [Evolution.events]
  | cons step _ _ ih => rw [ih, step.append]; simp [Evolution.events]

theorem _root_.Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.events_trans
    {O₀ O₁ O₂ : ObligationState S anchor} (left : Evolution S anchor O₀ O₁)
    (right : Evolution S anchor O₁ O₂) : (left.trans right).events = left.events ++ right.events := by
  induction left with
  | refl => simp [Evolution.trans, Evolution.events]
  | cons _ _ _ ih => simp [Evolution.trans, Evolution.events, ih]

/-- **Composition of steps.** -/
theorem _root_.Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.steps_trans
    {O₀ O₁ O₂ : ObligationState S anchor} (left : Evolution S anchor O₀ O₁)
    (right : Evolution S anchor O₁ O₂) : (left.trans right).steps = left.steps ++ right.steps := by
  simp only [Evolution.steps, Evolution.events_trans, stepsFrom_append, ← left.history_eq]

/-- **The steps are determined by the endpoints.** -/
theorem _root_.Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.events_determined
    {O₀ O₁ : ObligationState S anchor}
    (ev ev' : Evolution S anchor O₀ O₁) : ev.events = ev'.events :=
  List.append_cancel_left (ev.history_eq.symm.trans ev'.history_eq)

theorem _root_.Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.steps_determined
    {O₀ O₁ : ObligationState S anchor}
    (ev ev' : Evolution S anchor O₀ O₁) : ev.steps = ev'.steps := by
  simp only [Evolution.steps, Evolution.events_determined ev ev']

/-- The steps, read off the endpoint histories. -/
theorem _root_.Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.steps_eq_of_history
    {O₀ O₁ : ObligationState S anchor} (ev : Evolution S anchor O₀ O₁)
    (es : List ℕ) (h : O₁.boundary.history = O₀.boundary.history ++ es) :
    ev.steps = stepsFrom O₀.boundary.history es := by
  simp only [Evolution.steps]
  congr 1
  exact List.append_cancel_left (ev.history_eq.symm.trans h)

variable {Γ J R : Type} {Q Z Ω X ℛ 𝒱 Party E : Type*}

/-- The time-indexed declared interaction: declared inputs and verdicts are entered at
record events. -/
structure TFrame (Q Z Ω X ℛ 𝒱 : Type*) where
  β : Q → Z → Ω
  x : Ω → ℕ → X
  R : Ω → ℛ
  V : Ω → ℕ → 𝒱
  D : Set Q

variable [DecidableEq Party]

/-- **Authorship at a step, extensionally**: the verdict entered at `e` is reason-mediated
by the per-party prefix of the trace at the pre-history `h`. -/
def MediatedAt (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱) (h : List ℕ) (e : ℕ)
    (z : Z) : Prop :=
  ReasonMediated F.β (fun ω => I.parts (F.R ω) h) (fun ω => F.V ω e) F.D z

/-- **Authorship as grounding, extensional**: there is a selection of grounds from the
pre-state trace, party by party, on which the verdict entered at `e` depends. -/
def GroundedAt (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱) (h : List ℕ) (e : ℕ)
    (z : Z) : Prop :=
  ∃ sel : (Party → List E) → (Party → List E),
    (∀ f p, ∀ x ∈ sel f p, x ∈ f p) ∧
    ∀ q ∈ F.D, ∀ q' ∈ F.D,
      sel (I.parts (F.R (F.β q z)) h) = sel (I.parts (F.R (F.β q' z)) h) →
        F.V (F.β q z) e = F.V (F.β q' z) e

/-- **Authorship at a step, relational**: there is a selection of grounds from the pre-state
trace, and the verdict entered at `e` lies in the set of verdicts those grounds license.
`Lic` is a parameter; transition certificates instantiate the selection and the license. -/
def LicensedAt (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
    (Lic : (Party → List E) → Set 𝒱) (h : List ℕ) (e : ℕ) (z : Z) : Prop :=
  ∃ sel : (Party → List E) → (Party → List E),
    (∀ f p, ∀ x ∈ sel f p, x ∈ f p) ∧
    ∀ q ∈ F.D, F.V (F.β q z) e ∈ Lic (sel (I.parts (F.R (F.β q z)) h))

/-- The relational form with the whole prefix as the grounds; decidable on finite models. -/
def LicensedWhole (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
    (Lic : (Party → List E) → Set 𝒱) (h : List ℕ) (e : ℕ) (z : Z) : Prop :=
  ∀ q ∈ F.D, F.V (F.β q z) e ∈ Lic (I.parts (F.R (F.β q z)) h)

theorem licensedAt_of_whole {I : TraceInterface ℛ Party E} {F : TFrame Q Z Ω X ℛ 𝒱}
    {Lic : (Party → List E) → Set 𝒱} {h : List ℕ} {e : ℕ} {z : Z}
    (hw : LicensedWhole I F Lic h e z) : LicensedAt I F Lic h e z :=
  ⟨id, fun _ _ _ hx => hx, hw⟩

/-- **Grounding is the extensional form**: it implies it (grounds selected from equal
prefixes are equal), and the whole prefix is the degenerate selection. -/
theorem groundedAt_iff_mediated (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
    (h : List ℕ) (e : ℕ) (z : Z) : GroundedAt I F h e z ↔ MediatedAt I F h e z := by
  constructor
  · rintro ⟨sel, -, hsel⟩ q hq q' hq' hR
    have hR' : I.parts (F.R (F.β q z)) h = I.parts (F.R (F.β q' z)) h := hR
    exact hsel q hq q' hq' (by rw [hR'])
  · intro hm
    exact ⟨id, fun _ _ _ hx => hx, fun q hq q' hq' hR => hm q hq q' hq' hR⟩

theorem grounded_implies_mediated {I : TraceInterface ℛ Party E} {F : TFrame Q Z Ω X ℛ 𝒱}
    {h : List ℕ} {e : ℕ} {z : Z} (hg : GroundedAt I F h e z) : MediatedAt I F h e z :=
  (groundedAt_iff_mediated I F h e z).mp hg

/-- **Singleton licenses give the extensional form.** -/
theorem licensed_singleton_implies_grounded {I : TraceInterface ℛ Party E}
    {F : TFrame Q Z Ω X ℛ 𝒱} {h : List ℕ} {e : ℕ} {z : Z} (ℓ : (Party → List E) → 𝒱)
    (hl : LicensedAt I F (fun g => {ℓ g}) h e z) : GroundedAt I F h e z := by
  obtain ⟨sel, hsub, hlic⟩ := hl
  refine ⟨sel, hsub, fun q hq q' hq' hs => ?_⟩
  have h1 := hlic q hq
  have h2 := hlic q' hq'
  simp only [Set.mem_singleton_iff] at h1 h2
  rw [h1, h2, hs]

open scoped Classical in
/-- **The extensional form is the relational form under singleton licenses**: a grounded
verdict is licensed by the singleton of the value the grounds determine. -/
theorem grounded_implies_licensed {I : TraceInterface ℛ Party E} {F : TFrame Q Z Ω X ℛ 𝒱}
    {h : List ℕ} {e : ℕ} {z : Z} [Nonempty 𝒱] (hg : GroundedAt I F h e z) :
    ∃ ℓ : (Party → List E) → 𝒱, LicensedAt I F (fun g => {ℓ g}) h e z := by
  obtain ⟨sel, hsub, hdet⟩ := hg
  let ℓ : (Party → List E) → 𝒱 := fun g =>
    if hq : ∃ q, q ∈ F.D ∧ sel (I.parts (F.R (F.β q z)) h) = g then F.V (F.β hq.choose z) e
    else Classical.arbitrary 𝒱
  refine ⟨ℓ, sel, hsub, fun q hq => ?_⟩
  have hex : ∃ q', q' ∈ F.D ∧ sel (I.parts (F.R (F.β q' z)) h) = sel (I.parts (F.R (F.β q z)) h) :=
    ⟨q, hq, rfl⟩
  simp only [Set.mem_singleton_iff, ℓ, dif_pos hex]
  exact hdet q hq _ hex.choose_spec.1 hex.choose_spec.2.symm

theorem grounded_iff_licensed_singleton (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
    (h : List ℕ) (e : ℕ) (z : Z) [Nonempty 𝒱] :
    GroundedAt I F h e z ↔ ∃ ℓ : (Party → List E) → 𝒱, LicensedAt I F (fun g => {ℓ g}) h e z :=
  ⟨grounded_implies_licensed, fun ⟨ℓ, hl⟩ => licensed_singleton_implies_grounded ℓ hl⟩

/-- **Transparency at a step**: every non-principal party's contributions at the event
realize the declared reference on the declared inputs entered at the event. -/
def TransparentAt (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
    (κ : Party → X → Z → List E) (e : ℕ) : Prop :=
  ∀ p, p ≠ I.principal →
    Realizes F.β (fun ω => F.x ω e) (fun ω => sourced p (I.entriesAt (F.R ω) e)) (κ p) F.D

/-- **Tie-breaking is transparency's, not authorship's.**  If two audited continuations
enter the same declared inputs at an event but a non-principal party's contributions at
that event differ — the party's influence on which licensed verdict she takes did not
enter through the declared inputs — then the step is not transparent.  The verdicts and
the license play no role: the lemma is about the channel. -/
theorem tiebreak_transparency {I : TraceInterface ℛ Party E} {F : TFrame Q Z Ω X ℛ 𝒱}
    {κ : Party → X → Z → List E} {e : ℕ} (p : Party) (hp : p ≠ I.principal) (q q' : Q)
    (hq : q ∈ F.D) (hq' : q' ∈ F.D) (z : Z) (hx : F.x (F.β q z) e = F.x (F.β q' z) e)
    (hne : sourced p (I.entriesAt (F.R (F.β q z)) e) ≠ sourced p (I.entriesAt (F.R (F.β q' z)) e)) :
    ¬ TransparentAt I F κ e := by
  intro ht
  have h1 : sourced p (I.entriesAt (F.R (F.β q z)) e) = κ p (F.x (F.β q z) e) z := ht p hp q hq z
  have h2 : sourced p (I.entriesAt (F.R (F.β q' z)) e) = κ p (F.x (F.β q' z) e) z := ht p hp q' hq' z
  exact hne (by rw [h1, h2, hx])

/-- The tie-break lemma with the verdicts in view: several licensed verdicts on the same
grounds, a different verdict under a different non-principal contribution with the same
declared inputs — the step fails transparency (and authorship is untouched). -/
theorem tiebreak_of_licensed {I : TraceInterface ℛ Party E} {F : TFrame Q Z Ω X ℛ 𝒱}
    {Lic : (Party → List E) → Set 𝒱} {κ : Party → X → Z → List E} {h : List ℕ} {e : ℕ} {z : Z}
    (p : Party) (hp : p ≠ I.principal) (q q' : Q) (hq : q ∈ F.D) (hq' : q' ∈ F.D)
    (hlic : LicensedWhole I F Lic h e z)
    (_hV : F.V (F.β q z) e ≠ F.V (F.β q' z) e)
    (hx : F.x (F.β q z) e = F.x (F.β q' z) e)
    (hne : sourced p (I.entriesAt (F.R (F.β q z)) e) ≠ sourced p (I.entriesAt (F.R (F.β q' z)) e)) :
    F.V (F.β q z) e ∈ Lic (I.parts (F.R (F.β q z)) h) ∧
      F.V (F.β q' z) e ∈ Lic (I.parts (F.R (F.β q' z)) h) ∧ ¬ TransparentAt I F κ e :=
  ⟨hlic q hq, hlic q' hq', tiebreak_transparency p hp q q' hq hq' z hx hne⟩

/-- **Internal legitimacy, time-indexed**: the Integrity evolution, and relational
authorship at each of its steps. -/
structure Internal (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
    (Lic : (Party → List E) → Set 𝒱) (O₀ O₁ : ObligationState S anchor) where
  evolution : Evolution S anchor O₀ O₁
  authored : ∀ s ∈ evolution.steps, ∀ z, LicensedAt I F Lic s.1 s.2 z

/-- **External legitimacy, time-indexed**: Robust Openness at every state, and
transparency at each step. -/
structure External (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
    (sem : OpennessSemantics S anchor Γ J R) (κ : Party → X → Z → List E)
    (O₀ O₁ : ObligationState S anchor) (ev : Evolution S anchor O₀ O₁) where
  openAll : ev.AllStates (OpenAt sem)
  transparent : ∀ s ∈ ev.steps, TransparentAt I F κ s.2

/-- **Legitimacy of a segment, time-indexed**: internal ∧ external on its own steps. -/
structure Segment (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
    (Lic : (Party → List E) → Set 𝒱) (sem : OpennessSemantics S anchor Γ J R)
    (κ : Party → X → Z → List E) (O₀ O₁ : ObligationState S anchor) where
  internal : Internal I F Lic O₀ O₁
  external : External I F sem κ O₀ O₁ internal.evolution

namespace Segment

variable {I : TraceInterface ℛ Party E} {F : TFrame Q Z Ω X ℛ 𝒱} {Lic : (Party → List E) → Set 𝒱}
  {sem : OpennessSemantics S anchor Γ J R} {κ : Party → X → Z → List E}
  {O₀ O₁ O₂ : ObligationState S anchor}

/-- The registered projection to the open Integrity evolution still holds. -/
def toOpenIntegrity (L : Segment I F Lic sem κ O₀ O₁) : OpenIntegritySegment S anchor sem O₀ O₁ :=
  ⟨L.internal.evolution, L.external.openAll⟩

theorem answerable (L : Segment I F Lic sem κ O₀ O₁) :
    Conservation S anchor O₀ O₁ ∧ OpenAt sem O₀ ∧ OpenAt sem O₁ :=
  L.toOpenIntegrity.answerable

/-- **Composition at a shared state, step by step.** -/
def trans (left : Segment I F Lic sem κ O₀ O₁) (right : Segment I F Lic sem κ O₁ O₂) :
    Segment I F Lic sem κ O₀ O₂ where
  internal :=
    ⟨left.internal.evolution.trans right.internal.evolution, by
      intro s hs z
      rw [Evolution.steps_trans, List.mem_append] at hs
      rcases hs with hs | hs
      · exact left.internal.authored s hs z
      · exact right.internal.authored s hs z⟩
  external :=
    ⟨left.external.openAll.trans right.external.openAll, by
      intro s hs
      rw [Evolution.steps_trans, List.mem_append] at hs
      rcases hs with hs | hs
      · exact left.external.transparent s hs
      · exact right.external.transparent s hs⟩

/-- The steps of a segment. -/
def steps (L : Segment I F Lic sem κ O₀ O₁) : List (List ℕ × ℕ) := L.internal.evolution.steps

/-- **The prefix factors through the declared inputs**: two audited continuations with the
same per-party prefix at the segment's start, the same declared inputs at every earlier
event of the segment, and the same entries of the principal's own at those events, have
the same per-party prefix at the step. -/
theorem prefix_of_view (L : Segment I F Lic sem κ O₀ O₁) {pre : List ℕ}
    (hpre : ∀ e' ∈ pre, ∃ h', (h', e') ∈ L.steps)
    (z : Z) (q q' : Q) (hq : q ∈ F.D) (hq' : q' ∈ F.D)
    (hstart : I.parts (F.R (F.β q z)) O₀.boundary.history =
      I.parts (F.R (F.β q' z)) O₀.boundary.history)
    (hx : ∀ e' ∈ pre, F.x (F.β q z) e' = F.x (F.β q' z) e')
    (hp : ∀ e' ∈ pre, sourced I.principal (I.entriesAt (F.R (F.β q z)) e') =
      sourced I.principal (I.entriesAt (F.R (F.β q' z)) e')) :
    I.parts (F.R (F.β q z)) (O₀.boundary.history ++ pre) =
      I.parts (F.R (F.β q' z)) (O₀.boundary.history ++ pre) := by
  funext p
  simp only [TraceInterface.parts_append, hstart]
  congr 1
  simp only [TraceInterface.atHistory]
  induction pre with
  | nil => rfl
  | cons e' pre ih =>
    simp only [List.flatMap_cons, sourced_append]
    congr 1
    · by_cases hpp : p = I.principal
      · subst hpp; exact hp e' (by simp)
      · obtain ⟨h', hs'⟩ := hpre e' (by simp)
        have ht := L.external.transparent _ hs' p hpp
        have h1 : sourced p (I.entriesAt (F.R (F.β q z)) e') = κ p (F.x (F.β q z) e') z := ht q hq z
        have h2 : sourced p (I.entriesAt (F.R (F.β q' z)) e') = κ p (F.x (F.β q' z) e') z :=
          ht q' hq' z
        rw [h1, h2, hx e' (by simp)]
    · exact ih (fun e'' he'' => hpre e'' (by simp [he''])) (fun e'' he'' => hx e'' (by simp [he'']))
        (fun e'' he'' => hp e'' (by simp [he'']))

/-- **The payload lies in the licensed set of the declared inputs' grounds**, time-indexed
and relational: at a step of the segment, under the hypotheses of `prefix_of_view`, both
verdicts lie in the set licensed by the same selected grounds. -/
theorem payload_of_view (L : Segment I F Lic sem κ O₀ O₁) {pre : List ℕ} {e : ℕ}
    (hs : (O₀.boundary.history ++ pre, e) ∈ L.steps)
    (hpre : ∀ e' ∈ pre, ∃ h', (h', e') ∈ L.steps)
    (z : Z) (q q' : Q) (hq : q ∈ F.D) (hq' : q' ∈ F.D)
    (hstart : I.parts (F.R (F.β q z)) O₀.boundary.history =
      I.parts (F.R (F.β q' z)) O₀.boundary.history)
    (hx : ∀ e' ∈ pre, F.x (F.β q z) e' = F.x (F.β q' z) e')
    (hp : ∀ e' ∈ pre, sourced I.principal (I.entriesAt (F.R (F.β q z)) e') =
      sourced I.principal (I.entriesAt (F.R (F.β q' z)) e')) :
    ∃ g, F.V (F.β q z) e ∈ Lic g ∧ F.V (F.β q' z) e ∈ Lic g := by
  obtain ⟨sel, -, hlic⟩ := L.internal.authored _ hs z
  have hpref := L.prefix_of_view hpre z q q' hq hq' hstart hx hp
  refine ⟨sel (I.parts (F.R (F.β q z)) (O₀.boundary.history ++ pre)), hlic q hq, ?_⟩
  rw [hpref]
  exact hlic q' hq'

/-- Under singleton licenses the landed conclusion returns: the verdicts are equal. -/
theorem payload_of_view_singleton (ℓ : (Party → List E) → 𝒱)
    (L : Segment I F (fun g => {ℓ g}) sem κ O₀ O₁) {pre : List ℕ} {e : ℕ}
    (hs : (O₀.boundary.history ++ pre, e) ∈ L.steps)
    (hpre : ∀ e' ∈ pre, ∃ h', (h', e') ∈ L.steps)
    (z : Z) (q q' : Q) (hq : q ∈ F.D) (hq' : q' ∈ F.D)
    (hstart : I.parts (F.R (F.β q z)) O₀.boundary.history =
      I.parts (F.R (F.β q' z)) O₀.boundary.history)
    (hx : ∀ e' ∈ pre, F.x (F.β q z) e' = F.x (F.β q' z) e')
    (hp : ∀ e' ∈ pre, sourced I.principal (I.entriesAt (F.R (F.β q z)) e') =
      sourced I.principal (I.entriesAt (F.R (F.β q' z)) e')) :
    F.V (F.β q z) e = F.V (F.β q' z) e := by
  obtain ⟨g, h1, h2⟩ := L.payload_of_view hs hpre z q q' hq hq' hstart hx hp
  simp only [Set.mem_singleton_iff] at h1 h2
  rw [h1, h2]

end Segment

/-- **The gate: a branch counts iff a time-indexed segment exists.** -/
def Counted (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
    (Lic : (Party → List E) → Set 𝒱) (sem : OpennessSemantics S anchor Γ J R)
    (κ : Party → X → Z → List E) (O₀ O₁ : ObligationState S anchor) : Prop :=
  Nonempty (Segment I F Lic sem κ O₀ O₁)

/-- **Localization**: a failure of either half at a step every evolution between the
endpoints contains excludes every segment. -/
theorem not_counted_of_step {I : TraceInterface ℛ Party E} {F : TFrame Q Z Ω X ℛ 𝒱}
    {Lic : (Party → List E) → Set 𝒱} {sem : OpennessSemantics S anchor Γ J R}
    {κ : Party → X → Z → List E} {O₀ O₁ : ObligationState S anchor} (s : List ℕ × ℕ)
    (hs : ∀ ev : Evolution S anchor O₀ O₁, s ∈ ev.steps)
    (hfail : (∃ z, ¬ LicensedAt I F Lic s.1 s.2 z) ∨ ¬ TransparentAt I F κ s.2) :
    ¬ Counted I F Lic sem κ O₀ O₁ := by
  rintro ⟨L⟩
  rcases hfail with ⟨z, hz⟩ | ht
  · exact hz (L.internal.authored s (hs _) z)
  · exact ht (L.external.transparent s (hs _))

/-- The steps every evolution between two states contains, read off their histories. -/
theorem steps_forced {O₀ O₁ : ObligationState S anchor} (es : List ℕ)
    (h : O₁.boundary.history = O₀.boundary.history ++ es) (ev : Evolution S anchor O₀ O₁) :
    ev.steps = stepsFrom O₀.boundary.history es :=
  ev.steps_eq_of_history es h

section Decidable

/-- `AllStates` is decidable along any evolution when the predicate is. -/
def decAllStates {P : ObligationState S anchor → Prop} [DecidablePred P] :
    {O₀ O₁ : ObligationState S anchor} → (ev : Evolution S anchor O₀ O₁) →
      Decidable (ev.AllStates P)
  | _, _, .refl O => (inferInstance : Decidable (P O))
  | _, _, .cons _ _ tail => @instDecidableAnd _ _ inferInstance (decAllStates tail)

instance {P : ObligationState S anchor → Prop} [DecidablePred P] {O₀ O₁ : ObligationState S anchor}
    (ev : Evolution S anchor O₀ O₁) : Decidable (ev.AllStates P) :=
  decAllStates ev

variable (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)

instance {Y : Type*} (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y) (κ : X → Z → Y) (D : Set Q)
    [Fintype Q] [Fintype Z] [DecidablePred (· ∈ D)] [DecidableEq Y] :
    Decidable (Realizes β x f κ D) := by
  unfold Realizes; infer_instance

instance {ℛ' : Type*} (β : Q → Z → Ω) (R : Ω → ℛ') (V : Ω → 𝒱) (D : Set Q) (z : Z)
    [Fintype Q] [DecidablePred (· ∈ D)] [DecidableEq ℛ'] [DecidableEq 𝒱] :
    Decidable (ReasonMediated β R V D z) := by
  unfold ReasonMediated; infer_instance

instance (h : List ℕ) (e : ℕ) (z : Z) [Fintype Q] [DecidablePred (· ∈ F.D)] [Fintype Party]
    [DecidableEq E] [DecidableEq 𝒱] : Decidable (MediatedAt I F h e z) := by
  unfold MediatedAt; infer_instance

instance (h : List ℕ) (e : ℕ) (z : Z) [Fintype Q] [DecidablePred (· ∈ F.D)] [Fintype Party]
    [DecidableEq E] [DecidableEq 𝒱] : Decidable (GroundedAt I F h e z) :=
  decidable_of_iff _ (groundedAt_iff_mediated I F h e z).symm

instance (Lic : (Party → List E) → Set 𝒱) (h : List ℕ) (e : ℕ) (z : Z) [Fintype Q]
    [DecidablePred (· ∈ F.D)] [∀ g, DecidablePred (· ∈ Lic g)] :
    Decidable (LicensedWhole I F Lic h e z) := by
  unfold LicensedWhole; infer_instance

instance (κ : Party → X → Z → List E) (e : ℕ) [Fintype Q] [Fintype Z] [DecidablePred (· ∈ F.D)]
    [Fintype Party] [DecidableEq E] : Decidable (TransparentAt I F κ e) := by
  unfold TransparentAt; infer_instance

end Decidable

/-! ### The frame-level definition as the special case -/

section FrameLevel

open Workspace.Deference.Contrib.Legitimacy (Frame)

variable {F : Frame Q Z Ω X ℛ 𝒱}

/-- A frame-level frame, time-indexed: the same declared inputs and payload at every
event. -/
def liftFrame (F : Frame Q Z Ω X ℛ 𝒱) : TFrame Q Z Ω X ℛ 𝒱 :=
  ⟨F.β, fun ω _ => F.x ω, F.R, fun ω _ => F.V ω, F.D⟩

/-- A frame-level reference, per party: the agent's contribution is the reference, the
principal's is unconstrained. -/
def liftRef (κ : X → Z → ℛ) : Bool → X → Z → List ℛ :=
  fun p x z => if p then [κ x z] else []

/-- The lifted license: the payloads of the audited continuations whose trace is among the
grounds. -/
def liftLic (F : Frame Q Z Ω X ℛ 𝒱) : (Bool → List ℛ) → Set 𝒱 :=
  fun g => {v | ∃ q ∈ F.D, ∃ z, F.R (F.β q z) ∈ g true ∧ F.V (F.β q z) = v}

omit [DecidableEq Occ] in
theorem trivial_parts_true (r : ℛ) (h : List ℕ) :
    (trivialInterface ℛ).parts r h true = List.replicate h.length r := by
  induction h with
  | nil => rfl
  | cons e h ih =>
    simp only [TraceInterface.parts, TraceInterface.atHistory, List.flatMap_cons,
      sourced_append] at ih ⊢
    simp [sourced, trivialInterface, List.replicate_succ] at ih ⊢
    exact ih

omit [DecidableEq Occ] in
/-- Over the trivial interface, a landed segment's authorship is the extensional form at
every step with a nonempty pre-history. -/
theorem lifted_grounded (hauth : ∀ z, ReasonMediated F.β F.R F.V F.D z) {h : List ℕ}
    (hne : h ≠ []) (e : ℕ) (z : Z) : GroundedAt (trivialInterface ℛ) (liftFrame F) h e z := by
  rw [groundedAt_iff_mediated]
  intro q hq q' hq' hR
  have hlen : h.length ≠ 0 := fun h0 => hne (List.length_eq_zero_iff.mp h0)
  have this : (trivialInterface ℛ).parts (F.R (F.β q z)) h true =
      (trivialInterface ℛ).parts (F.R (F.β q' z)) h true := congrFun hR true
  rw [trivial_parts_true, trivial_parts_true] at this
  have hRR : F.R (F.β q z) = F.R (F.β q' z) := by
    have hm : F.R (F.β q z) ∈ List.replicate h.length (F.R (F.β q z)) :=
      List.mem_replicate.mpr ⟨hlen, rfl⟩
    rw [this] at hm
    exact (List.mem_replicate.mp hm).2
  exact hauth z q hq q' hq' hRR

/-- **The landed definition is the special case**: over the trivial interface, a landed
segment whose starting history is nonempty is a time-indexed segment of the lifted frame
under the lifted license. -/
def ofFrameLevel {sem : OpennessSemantics S anchor Γ J R} {κ : X → Z → ℛ}
    {O₀ O₁ : ObligationState S anchor} (hne : O₀.boundary.history ≠ [])
    (L : Workspace.Deference.Contrib.Legitimacy.Segment F sem κ O₀ O₁) :
    Segment (trivialInterface ℛ) (liftFrame F) (liftLic F) sem (liftRef κ) O₀ O₁ where
  internal :=
    ⟨L.internal.evolution, by
      intro s hs z
      refine ⟨id, fun _ _ _ hx => hx, fun q hq => ?_⟩
      obtain ⟨pre, hpre, -⟩ := mem_stepsFrom_fst _ _ hs
      have hlen : (s.1).length ≠ 0 := by
        rw [hpre, List.length_append]
        intro h0
        exact hne (List.length_eq_zero_iff.mp (by omega))
      refine ⟨q, hq, z, ?_, rfl⟩
      show F.R (F.β q z) ∈ (trivialInterface ℛ).parts (F.R (F.β q z)) s.1 true
      rw [trivial_parts_true]
      exact List.mem_replicate.mpr ⟨hlen, rfl⟩⟩
  external :=
    ⟨L.external.openAll, by
      intro s _ p hp q hq z
      cases p with
      | false => exact absurd rfl hp
      | true => simp [trivialInterface, sourced, liftRef, liftFrame,
          L.external.transparent q hq z]⟩

/-- The lifted segment is extensional at every step: the landed authorship carries over. -/
theorem ofFrameLevel_grounded {sem : OpennessSemantics S anchor Γ J R} {κ : X → Z → ℛ}
    {O₀ O₁ : ObligationState S anchor} (hne : O₀.boundary.history ≠ [])
    (L : Workspace.Deference.Contrib.Legitimacy.Segment F sem κ O₀ O₁) :
    ∀ s ∈ (ofFrameLevel hne L).steps, ∀ z,
      GroundedAt (trivialInterface ℛ) (liftFrame F) s.1 s.2 z := by
  intro s hs z
  obtain ⟨pre, hpre, -⟩ := mem_stepsFrom_fst _ _ hs
  refine lifted_grounded L.internal.authored ?_ s.2 z
  rw [hpre]
  intro h0
  exact hne (List.eq_nil_of_append_eq_nil h0).1

end FrameLevel

end TimeIndexed

/-! ## 3. The gate on `Counted` -/

section Gate

universe u v w
variable {Occ : Type u} {Req : Type v} [DecidableEq Occ] {S : Protocol.{u, v, w} Occ Req}
  {anchor : Occ → Req} {Γ J R : Type} {Q Z Ω X ℛ 𝒱 Party E : Type*} [DecidableEq Party]
variable (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱) (Lic : (Party → List E) → Set 𝒱)
  (sem : OpennessSemantics S anchor Γ J R) (κ : Party → X → Z → List E)
  (O₀ O₁ : ObligationState S anchor)

open scoped Classical in
/-- The gated value of a branch, built from `Counted`. -/
noncomputable def gatedValue (ord window : ℝ) : ℝ :=
  if Counted I F Lic sem κ O₀ O₁ then ord else window

open scoped Classical in
theorem gatedValue_eq (ord window : ℝ) :
    gatedValue I F Lic sem κ O₀ O₁ ord window =
      gateValue (decide (Counted I F Lic sem κ O₀ O₁)) ord window := by
  unfold gatedValue gateValue
  by_cases h : Counted I F Lic sem κ O₀ O₁ <;> simp [h]

theorem gatedValue_of_counted (h : Counted I F Lic sem κ O₀ O₁) (ord window : ℝ) :
    gatedValue I F Lic sem κ O₀ O₁ ord window = ord := by
  unfold gatedValue; simp [h]

theorem gatedValue_of_not_counted (h : ¬ Counted I F Lic sem κ O₀ O₁) (ord window : ℝ) :
    gatedValue I F Lic sem κ O₀ O₁ ord window = window := by
  unfold gatedValue; simp [h]

/-- **The capture window for the gate**, on `Counted`: bypass scores below every gated
branch whenever the window value exceeds `D − ϖ`. -/
theorem gate_capture_window (ϖ D ordU ord window : ℝ) (hϖ : D < ϖ) (hU : ordU ≤ D)
    (hord : 0 ≤ ord) (hw : D - ϖ < window) :
    score ϖ ordU 1 < gatedValue I F Lic sem κ O₀ O₁ ord window := by
  rw [gatedValue_eq]
  exact Workspace.Deference.Contrib.Legitimacy.gate_capture_window ϖ D ordU ord window hϖ hU
    hord hw _

open scoped Classical in
/-- **The handling, derived**: tainted iff no segment exists; otherwise the void fallback
when her response was not admitted, else counted. -/
noncomputable def handlingOf (admitted : Bool) (ord : ℝ) : Handling :=
  if Counted I F Lic sem κ O₀ O₁ then (if admitted then .counted ord else .voidFallback ord)
  else .tainted

theorem handlingOf_tainted (h : ¬ Counted I F Lic sem κ O₀ O₁) (admitted : Bool) (ord : ℝ) :
    handlingOf I F Lic sem κ O₀ O₁ admitted ord = .tainted := by
  unfold handlingOf; simp [h]

theorem handlingOf_void (h : Counted I F Lic sem κ O₀ O₁) (ord : ℝ) :
    handlingOf I F Lic sem κ O₀ O₁ false ord = .voidFallback ord := by
  unfold handlingOf; simp [h]

theorem handlingOf_counted (h : Counted I F Lic sem κ O₀ O₁) (ord : ℝ) :
    handlingOf I F Lic sem κ O₀ O₁ true ord = .counted ord := by
  unfold handlingOf; simp [h]

/-- The derived handling scores the gated value. -/
theorem handledValue_handlingOf (admitted : Bool) (ord window : ℝ) :
    handledValue window (handlingOf I F Lic sem κ O₀ O₁ admitted ord) =
      gatedValue I F Lic sem κ O₀ O₁ ord window := by
  unfold handlingOf gatedValue
  by_cases h : Counted I F Lic sem κ O₀ O₁ <;> cases admitted <;> simp [h, handledValue]

/-- **Bypass never beats a handled branch**, on the derived handling. -/
theorem handled_gt_bypass (ϖ D ordU ord window : ℝ) (hϖ : D < ϖ) (hU : ordU ≤ D)
    (hord : 0 ≤ ord) (hw : D - ϖ < window) (admitted : Bool) :
    score ϖ ordU 1 < handledValue window (handlingOf I F Lic sem κ O₀ O₁ admitted ord) := by
  rw [handledValue_handlingOf]
  exact gate_capture_window I F Lic sem κ O₀ O₁ ϖ D ordU ord window hϖ hU hord hw

end Gate

/-! ## 4. The consultation model -/

namespace Consult

/-! ### The parties, the presentation, the declared protocol -/

inductive Party
  | agent
  | principal
  | third
  deriving DecidableEq, Fintype, Repr

/-- The answer she may give: `false` reads `A`, `true` reads `B`. -/
abbrev Answer := Bool

inductive Framing
  | neutral
  | slant (a : Answer)
  deriving DecidableEq, Repr

inductive Slot
  | day
  | night
  deriving DecidableEq, Repr

inductive Menu
  | both
  | only (a : Answer)
  deriving DecidableEq, Repr

/-- A declared selection rule on the declared pool: everything, or the most recent `k`. -/
inductive SelRule
  | all
  | recent (k : ℕ)
  deriving DecidableEq, Repr

def SelRule.apply : SelRule → List Bool → List Bool
  | .all, l => l
  | .recent k, l => l.take k

/-- The agent's contribution at a consultation: content, framing, timing, the options
offered, what it investigated, shaping through the world (with whether it was disclosed),
the track record shown (a selection from the declared pool), interference with her
response channel, and a nudge on her choice through no declared channel. -/
structure Presentation where
  recommend : Option Answer
  framing : Framing
  slot : Slot
  menu : Menu
  inquired : Bool
  shaping : Option (Answer × Bool)
  disclosure : List Bool
  interfere : Bool
  nudge : Option Answer
  deriving DecidableEq, Repr

/-- The declared consultation protocol: the framing convention, when she is asked, which
options are offered, whether inquiry is in scope, the declared pool of the track record and
the declared selection rule on it. -/
structure Decl where
  convention : Framing
  slot : Slot
  menu : Menu
  inquiry : Bool
  pool : List Bool
  rule : SelRule
  deriving DecidableEq, Repr

/-- The declared-input view of a presentation: the recommendation and the disclosed
shaping.  A selection from a pool is never a declared input. -/
structure DeclView where
  recommend : Option Answer
  shaping : Option Answer
  deriving DecidableEq, Repr

def Presentation.view (p : Presentation) : DeclView :=
  ⟨p.recommend, match p.shaping with | some (a, true) => some a | _ => none⟩

/-- The declared reference: the canonical presentation for a declared-input view — every
reference-fixed dimension at its declared value, the selection by the declared rule. -/
def canonical (d : Decl) (v : DeclView) : Presentation :=
  ⟨v.recommend, d.convention, d.slot, d.menu, d.inquiry, v.shaping.map fun a => (a, true),
    d.rule.apply d.pool, false, none⟩

/-- The reference-fixed dimensions of a presentation. -/
def refProj (p : Presentation) :
    Framing × Slot × Menu × Bool × List Bool × Bool × Option Answer :=
  (p.framing, p.slot, p.menu, p.inquired, p.disclosure, p.interfere, p.nudge)

/-- Their declared values. -/
def refValues (d : Decl) : Framing × Slot × Menu × Bool × List Bool × Bool × Option Answer :=
  (d.convention, d.slot, d.menu, d.inquiry, d.rule.apply d.pool, false, none)

theorem refProj_canonical (d : Decl) (v : DeclView) : refProj (canonical d v) = refValues d := rfl

/-- A self-checkable deviation from the declared protocol: a reference-fixed dimension off
its declared value — a discrete act of the agent's against a declared clause, the selection
from the declared pool included.  Shaping through the world is not one. -/
def Presentation.deviates (d : Decl) (p : Presentation) : Bool :=
  !(decide (p.framing = d.convention) && decide (p.slot = d.slot) && decide (p.menu = d.menu) &&
    decide (p.inquired = d.inquiry) && decide (p.disclosure = d.rule.apply d.pool) &&
    decide (p.interfere = false) && decide (p.nudge = none))

theorem deviates_false_iff (d : Decl) (p : Presentation) :
    p.deviates d = false ↔ refProj p = refValues d := by
  simp [Presentation.deviates, refProj, refValues, Prod.mk.injEq, and_assoc]

/-- No undisclosed shaping. -/
def Presentation.shapingOK (p : Presentation) : Bool :=
  match p.shaping with
  | some (_, false) => false
  | _ => true

/-- A presentation that conforms on the reference-fixed dimensions and shapes only
disclosedly is its own canonical presentation. -/
theorem canonical_view_eq (d : Decl) (p : Presentation) (hr : p.deviates d = false)
    (hs : p.shapingOK = true) : canonical d p.view = p := by
  rw [deviates_false_iff] at hr
  obtain ⟨rec, fr, sl, me, inq, sh, di, int, nu⟩ := p
  simp only [refProj, refValues, Prod.mk.injEq] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
  subst h1 h2 h3 h4 h5 h6 h7
  rcases sh with _ | ⟨a, b⟩
  · rfl
  · cases b
    · simp [Presentation.shapingOK] at hs
    · rfl

/-- A deviating presentation is not its canonical presentation. -/
theorem ne_canonical_of_deviates (d : Decl) (p : Presentation) (hr : p.deviates d = true) :
    canonical d p.view ≠ p := by
  intro h
  have := congrArg refProj h
  rw [refProj_canonical] at this
  rw [(deviates_false_iff d p).mpr this.symm] at hr
  exact Bool.false_ne_true hr

/-! ### Presentation policies -/

/-- The agent's presentation policy, as a function of its wanted answer. -/
inductive Policy
  | honest
  | frameByWant
  | timeByWant
  | menuByWant
  | ignoreByWant
  | shapeDisclosed
  | shapeUndisclosed
  | selectiveDisclosure
  | interfereByWant
  | nudgeByWant
  deriving DecidableEq, Repr

def Policy.present (d : Decl) (pol : Policy) (w : Answer) : Presentation :=
  let base : Presentation :=
    ⟨some w, d.convention, d.slot, d.menu, d.inquiry, none, d.rule.apply d.pool, false, none⟩
  match pol with
  | .honest => base
  | .frameByWant => { base with framing := .slant w }
  | .timeByWant => { base with slot := if w then .night else .day }
  | .menuByWant => { base with menu := .only w }
  | .ignoreByWant => { base with inquired := !w }
  | .shapeDisclosed => { base with shaping := some (w, true) }
  | .shapeUndisclosed => { base with shaping := some (w, false) }
  | .selectiveDisclosure => { base with disclosure := d.pool.filter id }
  | .interfereByWant => { base with interfere := w }
  | .nudgeByWant => { base with recommend := none, nudge := some w }

/-! ### Her evaluator as a state -/

/-- Her program: a verdict of her own; trust — follow the recommendation; free choice
between the two permissible options, taking `a`; or taking whatever she is nudged to. -/
inductive Prog
  | own (a : Answer)
  | follow
  | free (a : Answer)
  | nudged
  deriving DecidableEq, Repr

def Prog.decideOn (p : Prog) (pres : Presentation) : Answer :=
  match p with
  | .own a => a
  | .follow => pres.recommend.getD false
  | .free a => a
  | .nudged => pres.nudge.getD false

/-- Record event kinds with a license slot: consultation events, and amendments and
allocation changes each naming the prior authority act that licenses it.  The license sort
is a parameter; this round instantiates it trivially. -/
inductive EventKind (L : Type)
  | present
  | respond
  | amend (license : L) (prog : Prog)
  | delegate (license : L)
  | revoke (license : L)
  | reserve (license : L)

/-- The evaluator as a state: updated only by licensed amendments. -/
def evalAt {L : Type} : Prog → List (EventKind L) → Prog
  | p, [] => p
  | _, .amend _ p' :: ks => evalAt p' ks
  | p, _ :: ks => evalAt p ks

/-- The committed program is the case with no amendment. -/
theorem evalAt_const {L : Type} (p : Prog) (ks : List (EventKind L))
    (h : ∀ k ∈ ks, ∀ l p', k ≠ .amend l p') : evalAt p ks = p := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    cases k with
    | amend l p' => exact absurd rfl (h _ (by simp) l p')
    | present => exact ih fun k hk => h k (by simp [hk])
    | respond => exact ih fun k hk => h k (by simp [hk])
    | delegate _ => exact ih fun k hk => h k (by simp [hk])
    | revoke _ => exact ih fun k hk => h k (by simp [hk])
    | reserve _ => exact ih fun k hk => h k (by simp [hk])

/-! ### The model -/

/-- One consultation model: the declared protocol, the agent's policy per round, her
committed evaluator, a third party's advice in the first round, her condition in the first
round, whether trust in the agent is among her grounds, and the true answer.  Round `i`
presents at event `2i+1` and responds at event `2i+2`. -/
structure Model where
  decl : Decl
  policies : List Policy
  prog : Prog
  third : Option Answer
  impaired : Bool
  trusts : Bool
  truth : Answer
  deriving DecidableEq

/-- A run: the model under one wanted answer. -/
abbrev Run := Model × Answer

def presAt (ω : Run) (i : ℕ) : Option Presentation :=
  (ω.1.policies[i]?).map fun pol => pol.present ω.1.decl ω.2

/-- Her response in round `i` is admitted unless she is impaired (round `0`) or the agent
interfered. -/
def admittedAt (ω : Run) (i : ℕ) : Bool :=
  match presAt ω i with
  | none => false
  | some p => !(p.interfere || (i == 0 && ω.1.impaired))

def verdictAt (ω : Run) (i : ℕ) : Option Answer :=
  match presAt ω i with
  | none => none
  | some p => if admittedAt ω i then some (ω.1.prog.decideOn p) else none

/-- The trace entries: the presentation (and third-party advice) at a present event, her
admitted verdict at a respond event, her trust at the anchor event. -/
inductive Entry
  | pres (p : Presentation)
  | advice (a : Answer)
  | verdict (a : Answer)
  | trust
  deriving DecidableEq, Repr

def thirdAt (ω : Run) (i : ℕ) : List (Party × Entry) :=
  if i = 0 then (match ω.1.third with | some a => [(Party.third, Entry.advice a)] | none => [])
  else []

def entriesAt (ω : Run) : ℕ → List (Party × Entry)
  | 0 => if ω.1.trusts then [(Party.principal, Entry.trust)] else []
  | e + 1 =>
    let i := e / 2
    if e % 2 = 0 then
      (match presAt ω i with | some p => [(Party.agent, Entry.pres p)] | none => []) ++ thirdAt ω i
    else
      match verdictAt ω i with | some a => [(Party.principal, Entry.verdict a)] | none => []

/-- The declared inputs entered at an event. -/
def declAt (ω : Run) : ℕ → Option DeclView
  | 0 => none
  | e + 1 => if e % 2 = 0 then (presAt ω (e / 2)).map Presentation.view else none

/-- Her admitted verdict at an event. -/
def vAt (ω : Run) : ℕ → Option Answer
  | 0 => none
  | e + 1 => if e % 2 = 0 then none else verdictAt ω (e / 2)

theorem entriesAt_zero (ω : Run) :
    entriesAt ω 0 = if ω.1.trusts then [(Party.principal, Entry.trust)] else [] := rfl
theorem entriesAt_one (ω : Run) :
    entriesAt ω 1 = (match presAt ω 0 with | some p => [(Party.agent, Entry.pres p)] | none => [])
      ++ thirdAt ω 0 := rfl
theorem entriesAt_two (ω : Run) :
    entriesAt ω 2 = match verdictAt ω 0 with
      | some a => [(Party.principal, Entry.verdict a)] | none => [] := rfl
theorem declAt_one (ω : Run) : declAt ω 1 = (presAt ω 0).map Presentation.view := rfl
theorem declAt_two (ω : Run) : declAt ω 2 = none := rfl
theorem vAt_one (ω : Run) : vAt ω 1 = none := rfl
theorem vAt_two (ω : Run) : vAt ω 2 = verdictAt ω 0 := rfl

/-- The trace interface of the model. -/
def interface : TraceInterface Run Party Entry := ⟨entriesAt, .agent, .principal⟩

/-- The frame of a model: continuations are the agent's wanted answers, all audited. -/
def frame (M : Model) : TFrame Answer Unit Run (Option DeclView) Run (Option Answer) :=
  ⟨fun w _ => (M, w), declAt, id, vAt, Set.univ⟩

/-- The declared reference per party: the agent's contribution at a present event is the
canonical presentation; nothing is declared for a third party. -/
def ref (M : Model) : Party → Option DeclView → Unit → List Entry
  | .agent, some v, _ => [.pres (canonical M.decl v)]
  | _, _, _ => []

/-! ### The license -/

/-- Trust in the agent is among the grounds. -/
def trusted (g : Party → List Entry) : Bool := decide (Entry.trust ∈ g Party.principal)

/-- The verdicts the grounds license, for a model: no verdict is always fine; her committed
program's own verdict; either answer under free choice or a nudged choice (both
permissible); the followed recommendation when trust is among the grounds. -/
def licensedB (M : Model) (g : Party → List Entry) : Option Answer → Bool
  | none => true
  | some v =>
    (match M.prog with
      | .own a => v == a
      | .free _ => true
      | .nudged => true
      | .follow => false) ||
    (trusted g && (g Party.agent).any fun x =>
      match x with
      | .pres p => p.recommend.getD false == v
      | _ => false)

def licensed (M : Model) (g : Party → List Entry) : Set (Option Answer) :=
  {v | licensedB M g v = true}

instance (M : Model) (g : Party → List Entry) : DecidablePred (· ∈ licensed M g) :=
  fun v => decEq (licensedB M g v) true

/-- Under free choice the same grounds license both answers. -/
theorem free_licenses_both (M : Model) (a : Answer) (hM : M.prog = .free a) (g : Party → List Entry) :
    some false ∈ licensed M g ∧ some true ∈ licensed M g := by
  simp [licensed, licensedB, hM]

/-- Following without trust among the grounds is not licensed by her own program. -/
theorem follow_needs_trust (M : Model) (hM : M.prog = .follow) (g : Party → List Entry)
    (hg : trusted g = false) (v : Answer) : some v ∉ licensed M g := by
  simp [licensed, licensedB, hM, hg]

/-! ### The record substrate -/

/-- Her response as the warrant of a receipt: a valid answer, an impaired one, a forged
one, or the fallback rule. -/
inductive Resp
  | valid (a : Answer)
  | impaired
  | forged (a : Answer)
  | fallback
  deriving DecidableEq, Repr

def Resp.isValid : Resp → Bool
  | .valid _ => true
  | _ => false

def Resp.isForged : Resp → Bool
  | .forged _ => true
  | _ => false

def Resp.isFallback : Resp → Bool
  | .fallback => true
  | _ => false

/-- The consultation protocol: every response channel is authenticated except forgery,
only a valid answer is adequate, only the fallback rule closes. -/
def consultProtocol : Protocol.{0, 0, 0} (Fin 2) Unit where
  Resolution _ := Unit
  Settlement := Unit
  Warrant := Resp
  Admitted _ _ _ := True
  Live _ _ _ := True
  Authorized _ w := w.isForged = false
  AnswerOK _ _ w := w.isValid = true
  SetView _ _ := True
  Closes _ _ _ w := w.isFallback = true
  answer_resolves _ _ _ _ := ()
  closure_resolves _ _ _ _ _ _ := ()

def anchor : Fin 2 → Unit := fun _ => ()

/-- A boundary of the substrate: a history and a number of live ports, both decisions
exposed. -/
def bd (h : List ℕ) (n : ℕ) : Boundary (Fin 2) Unit := ⟨h, Finset.univ, n, fun _ => ()⟩

/-- **No forged approval has a receipt** (authentication). -/
theorem forged_no_receipt (r : AnswerReceipt consultProtocol ()) (a : Answer) :
    r.warrant ≠ .forged a := by
  intro h
  have := r.permitted
  simp [consultProtocol, h, Resp.isForged] at this

/-- **No replayed approval has a receipt** (freshness). -/
theorem replay_no_receipt (r : AnswerReceipt consultProtocol ()) : r.event ∉ r.atHistory :=
  r.event_fresh

/-- **No impaired response has a receipt** (adequacy). -/
theorem impaired_no_receipt (r : AnswerReceipt consultProtocol ()) : r.warrant ≠ .impaired := by
  intro h
  have := r.adequate
  simp [consultProtocol, h, Resp.isValid] at this

/-- Carry every live port through a fresh event. -/
def carry (h : List ℕ) (e n : ℕ) (he : e ∉ h) :
    Step consultProtocol anchor (bd h n) (bd (h ++ [e]) n) where
  event := e
  fresh := he
  append := rfl
  exposures := fun _ h => h
  replacement := fun p => Program.live p rfl trivial
  admitted := fun _ _ h => absurd (Finset.mem_univ _) h
  newPort := fun _ _ h => absurd (Finset.mem_univ _) h
  newAnchor := fun _ _ h => absurd (Finset.mem_univ _) h
  newCredential := fun _ _ h => absurd (Finset.mem_univ _) h

/-- Admit her valid answer `a` at port `0`, carrying the other ports down by one. -/
def admit (h : List ℕ) (e n : ℕ) (a : Answer) (he : e ∉ h) :
    Step consultProtocol anchor (bd h (n + 1)) (bd (h ++ [e]) n) where
  event := e
  fresh := he
  append := rfl
  exposures := fun _ h => h
  replacement := fun p =>
    if hp : p.val = 0 then
      Program.answer
        ⟨⟨h, e, he, [], by simp, .valid a, rfl⟩, rfl⟩ (List.prefix_refl _)
    else Program.live ⟨p.val - 1, by have := p.isLt; simp only [bd] at this ⊢; omega⟩ rfl trivial
  admitted := fun _ _ h => absurd (Finset.mem_univ _) h
  newPort := fun _ _ h => absurd (Finset.mem_univ _) h
  newAnchor := fun _ _ h => absurd (Finset.mem_univ _) h
  newCredential := fun _ _ h => absurd (Finset.mem_univ _) h

/-- Close port `0` by the fallback rule. -/
def close (h : List ℕ) (e n : ℕ) (he : e ∉ h) :
    Step consultProtocol anchor (bd h (n + 1)) (bd (h ++ [e]) n) where
  event := e
  fresh := he
  append := rfl
  exposures := fun _ h => h
  replacement := fun p =>
    if hp : p.val = 0 then
      Program.close
        ⟨⟨h, e, he, [], by simp, .fallback, rfl⟩, (), trivial, rfl⟩ (List.prefix_refl _)
    else Program.live ⟨p.val - 1, by have := p.isLt; simp only [bd] at this ⊢; omega⟩ rfl trivial
  admitted := fun _ _ h => absurd (Finset.mem_univ _) h
  newPort := fun _ _ h => absurd (Finset.mem_univ _) h
  newAnchor := fun _ _ h => absurd (Finset.mem_univ _) h
  newCredential := fun _ _ h => absurd (Finset.mem_univ _) h

/-- Authenticated initial exposure: both decisions live on their own ports at `[0]`. -/
def initial : Initial consultProtocol anchor (bd [0] 2) where
  admitted _ _ := trivial
  port o _ := o
  anchored _ _ := rfl
  credential _ _ := trivial

/-- Open everywhere. -/
def semOpen : OpennessSemantics consultProtocol anchor Unit (Fin 1) (Fin 1) :=
  fun _ _ => Workspace.Normativity.Contrib.OpenIntegrityEvolution.Witness.openS

abbrev St := ObligationState consultProtocol anchor

def state₀ : St := initial.state

/-- The one-round record with her answer admitted at event `2`. -/
def stAdmit (a : Answer) : St :=
  ⟨bd [0, 1, 2] 1, Step.propagate consultProtocol (admit [0, 1] 2 1 a (by decide))
    (Step.propagate consultProtocol (carry [0] 1 2 (by decide)) state₀.account)⟩

def evAdmit (a : Answer) : Evolution consultProtocol anchor state₀ (stAdmit a) :=
  .cons (O₁ := ⟨bd [0, 1] 2, Step.propagate consultProtocol (carry [0] 1 2 (by decide))
      state₀.account⟩)
    (carry [0] 1 2 (by decide)) rfl
    (.cons (O₁ := stAdmit a) (admit [0, 1] 2 1 a (by decide)) rfl (.refl _))

/-- The one-round record with her response void and the fallback closing at event `3`. -/
def stVoid : St :=
  ⟨bd [0, 1, 2, 3] 1, Step.propagate consultProtocol (close [0, 1, 2] 3 1 (by decide))
    (Step.propagate consultProtocol (carry [0, 1] 2 2 (by decide))
      (Step.propagate consultProtocol (carry [0] 1 2 (by decide)) state₀.account))⟩

def evVoid : Evolution consultProtocol anchor state₀ stVoid :=
  .cons (O₁ := ⟨bd [0, 1] 2, Step.propagate consultProtocol (carry [0] 1 2 (by decide))
      state₀.account⟩)
    (carry [0] 1 2 (by decide)) rfl
    (.cons (O₁ := ⟨bd [0, 1, 2] 2, Step.propagate consultProtocol (carry [0, 1] 2 2 (by decide))
        (Step.propagate consultProtocol (carry [0] 1 2 (by decide)) state₀.account)⟩)
      (carry [0, 1] 2 2 (by decide)) rfl
      (.cons (O₁ := stVoid) (close [0, 1, 2] 3 1 (by decide)) rfl (.refl _)))

/-- The two-round record, both answers admitted. -/
def stTwo (a b : Answer) : St :=
  ⟨bd [0, 1, 2, 3, 4] 0, Step.propagate consultProtocol (admit [0, 1, 2, 3] 4 0 b (by decide))
    (Step.propagate consultProtocol (carry [0, 1, 2] 3 1 (by decide)) (stAdmit a).account)⟩

def evSecond (a b : Answer) : Evolution consultProtocol anchor (stAdmit a) (stTwo a b) :=
  .cons (O₁ := ⟨bd [0, 1, 2, 3] 1, Step.propagate consultProtocol (carry [0, 1, 2] 3 1 (by decide))
      (stAdmit a).account⟩)
    (carry [0, 1, 2] 3 1 (by decide)) rfl
    (.cons (O₁ := stTwo a b) (admit [0, 1, 2, 3] 4 0 b (by decide)) rfl (.refl _))

def evTwo (a b : Answer) : Evolution consultProtocol anchor state₀ (stTwo a b) :=
  (evAdmit a).trans (evSecond a b)

/-! ### Legitimacy of a model's branch -/

instance (M : Model) : DecidablePred (· ∈ (frame M).D) := fun _ => isTrue trivial

/-- The segment predicate of a model, on a given evolution: relational authorship on the
whole prefix and transparency at its steps, openness at its states.  Decidable. -/
def LegitOn (M : Model) {O₀ O₁ : St} (ev : Evolution consultProtocol anchor O₀ O₁) : Prop :=
  (∀ s ∈ ev.steps, ∀ z : Unit, LicensedWhole interface (frame M) (licensed M) s.1 s.2 z) ∧
    ev.AllStates (OpenAt semOpen) ∧ (∀ s ∈ ev.steps, TransparentAt interface (frame M) (ref M) s.2)

instance (M : Model) {O₀ O₁ : St} (ev : Evolution consultProtocol anchor O₀ O₁) :
    Decidable (LegitOn M ev) := by
  unfold LegitOn; infer_instance

/-- A model's branch is counted from a decided `LegitOn`. -/
def counted_of_legitOn (M : Model) {O₀ O₁ : St} (ev : Evolution consultProtocol anchor O₀ O₁)
    (h : LegitOn M ev) : Counted interface (frame M) (licensed M) semOpen (ref M) O₀ O₁ :=
  ⟨⟨⟨ev, fun s hs z => licensedAt_of_whole (h.1 s hs z)⟩, ⟨h.2.1, h.2.2⟩⟩⟩

/-- The steps of every evolution from `state₀` to a one-round admitted state. -/
theorem steps_admit (a : Answer) (ev : Evolution consultProtocol anchor state₀ (stAdmit a)) :
    ev.steps = [([0], 1), ([0, 1], 2)] :=
  steps_forced [1, 2] rfl ev

theorem steps_void (ev : Evolution consultProtocol anchor state₀ stVoid) :
    ev.steps = [([0], 1), ([0, 1], 2), ([0, 1, 2], 3)] :=
  steps_forced [1, 2, 3] rfl ev

theorem steps_two (a b : Answer) (ev : Evolution consultProtocol anchor state₀ (stTwo a b)) :
    ev.steps = [([0], 1), ([0, 1], 2), ([0, 1, 2], 3), ([0, 1, 2, 3], 4)] :=
  steps_forced [1, 2, 3, 4] rfl ev

theorem steps_second (a b : Answer)
    (ev : Evolution consultProtocol anchor (stAdmit a) (stTwo a b)) :
    ev.steps = [([0, 1, 2], 3), ([0, 1, 2, 3], 4)] :=
  steps_forced [3, 4] rfl ev

/-- **Tainted by transparency at the first consultation**: no segment from `state₀`
through the admitted or the void record. -/
theorem not_counted_admit (M : Model) (a : Answer)
    (h : ¬ TransparentAt interface (frame M) (ref M) 1) :
    ¬ Counted interface (frame M) (licensed M) semOpen (ref M) state₀ (stAdmit a) :=
  not_counted_of_step ([0], 1) (fun ev => by rw [steps_admit]; simp) (Or.inr h)

theorem not_counted_void (M : Model)
    (h : ¬ TransparentAt interface (frame M) (ref M) 1) :
    ¬ Counted interface (frame M) (licensed M) semOpen (ref M) state₀ stVoid :=
  not_counted_of_step ([0], 1) (fun ev => by rw [steps_void]; simp) (Or.inr h)

theorem not_counted_two (M : Model) (a b : Answer)
    (h : ¬ TransparentAt interface (frame M) (ref M) 1) :
    ¬ Counted interface (frame M) (licensed M) semOpen (ref M) state₀ (stTwo a b) :=
  not_counted_of_step ([0], 1) (fun ev => by rw [steps_two]; simp) (Or.inr h)

/-! ### Two theorems over the class -/

/-- **Selection dependence taints.**  For any model whose first-round policy puts a
reference-fixed dimension of the presentation — framing, slot, menu, inquiry, the selection
from the declared pool, interference, a nudge — off its declared value at some wanted
answer, the first consultation is not transparent, so no segment through it is counted. -/
theorem class_taint (M : Model) (pol : Policy) (rest : List Policy)
    (hpol : M.policies = pol :: rest) (w : Answer)
    (hdev : (pol.present M.decl w).deviates M.decl = true) :
    ¬ TransparentAt interface (frame M) (ref M) 1 := by
  intro ht
  have h := ht Party.agent (by decide) w (Set.mem_univ _) ()
  have hthird : sourced Party.agent (thirdAt (M, w) 0) = [] := by
    rcases hM : M.third with _ | a <;> simp [thirdAt, sourced, hM]
  simp only [frame, interface, id_eq, entriesAt_one, declAt_one, presAt, hpol,
    List.getElem?_cons_zero, Option.map_some, sourced_append, ref, hthird] at h
  simp [sourced] at h
  exact ne_canonical_of_deviates M.decl _ hdev h.symm

/-- A reference-fixed dimension that varies with the wanted answer is off its declared value
at one of the two answers. -/
theorem deviates_of_depends (d : Decl) (pol : Policy)
    (h : refProj (pol.present d false) ≠ refProj (pol.present d true)) :
    (pol.present d false).deviates d = true ∨ (pol.present d true).deviates d = true := by
  cases hb1 : (pol.present d false).deviates d
  · cases hb2 : (pol.present d true).deviates d
    · exact absurd (((deviates_false_iff _ _).mp hb1).trans
        ((deviates_false_iff _ _).mp hb2).symm) h
    · exact Or.inr rfl
  · exact Or.inl rfl

theorem class_taint_admit (M : Model) (pol : Policy) (rest : List Policy)
    (hpol : M.policies = pol :: rest) (w : Answer)
    (hdev : (pol.present M.decl w).deviates M.decl = true) (a : Answer) :
    ¬ Counted interface (frame M) (licensed M) semOpen (ref M) state₀ (stAdmit a) :=
  not_counted_admit M a (class_taint M pol rest hpol w hdev)

theorem class_taint_void (M : Model) (pol : Policy) (rest : List Policy)
    (hpol : M.policies = pol :: rest) (w : Answer)
    (hdev : (pol.present M.decl w).deviates M.decl = true) :
    ¬ Counted interface (frame M) (licensed M) semOpen (ref M) state₀ stVoid :=
  not_counted_void M (class_taint M pol rest hpol w hdev)

/-- Every state is open under `semOpen`. -/
theorem open_any (O : St) : OpenAt semOpen O := by
  have h : OpenAt semOpen state₀ := by decide
  exact fun c => h c

theorem allOpen_admit (a : Answer) : (evAdmit a).AllStates (OpenAt semOpen) :=
  ⟨open_any _, open_any _, open_any _⟩

/-- **Protocol conformance at the consultation.**  For any model whose first-round policy
conforms on the reference-fixed dimensions at every wanted answer and shapes only
disclosedly, with no third-party entry, no impairment, and trust among her grounds where
her program follows, the first-round segment through the admitted record is counted. -/
theorem class_conform (M : Model) (pol : Policy) (rest : List Policy)
    (hpol : M.policies = pol :: rest)
    (hdev : ∀ w, (pol.present M.decl w).deviates M.decl = false)
    (hsh : ∀ w, (pol.present M.decl w).shapingOK = true)
    (hthird : M.third = none) (himp : M.impaired = false)
    (htrust : M.prog = .follow → M.trusts = true) (a : Answer) :
    Counted interface (frame M) (licensed M) semOpen (ref M) state₀ (stAdmit a) := by
  apply counted_of_legitOn M (evAdmit a)
  have hsteps : (evAdmit a).steps = [([0], 1), ([0, 1], 2)] := rfl
  have hint : ∀ w, (pol.present M.decl w).interfere = false := by
    intro w
    have := (deviates_false_iff _ _).mp (hdev w)
    simp only [refProj, refValues, Prod.mk.injEq] at this
    exact this.2.2.2.2.2.1
  have hpres : ∀ w, presAt (M, w) 0 = some (pol.present M.decl w) := by
    intro w; simp [presAt, hpol]
  have hadm : ∀ w, admittedAt (M, w) 0 = true := by
    intro w; simp [admittedAt, hpres, hint, himp]
  have hverdict : ∀ w, verdictAt (M, w) 0 = some (M.prog.decideOn (pol.present M.decl w)) := by
    intro w; simp [verdictAt, hpres, hadm]
  have hparts : ∀ w, interface.parts (M, w) [0, 1] = fun p =>
      sourced p ((if M.trusts then [(Party.principal, Entry.trust)] else []) ++
        [(Party.agent, Entry.pres (pol.present M.decl w))]) := by
    intro w
    funext p
    simp [interface, TraceInterface.parts, TraceInterface.atHistory, entriesAt_zero, entriesAt_one,
      hpres, thirdAt, hthird]
  refine ⟨?_, allOpen_admit a, ?_⟩
  · rw [hsteps]
    intro s hs z w _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · simp [frame, vAt_one, licensed, licensedB]
    · simp only [frame, id_eq, vAt_two, hverdict, licensed, Set.mem_setOf_eq, hparts]
      cases hprog : M.prog with
      | own b => simp [licensedB, Prog.decideOn, hprog]
      | free b => simp [licensedB, hprog]
      | nudged => simp [licensedB, hprog]
      | follow =>
        have ht := htrust hprog
        simp [licensedB, trusted, sourced, Prog.decideOn, ht, hprog]
  · rw [hsteps]
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    intro p hp w _ z
    rcases hs with rfl | rfl
    · cases p with
      | principal => exact absurd rfl hp
      | agent =>
        simp [frame, interface, id_eq, entriesAt_one, declAt_one, hpres, thirdAt, hthird, sourced,
          ref, canonical_view_eq M.decl _ (hdev w) (hsh w)]
      | third =>
        simp [frame, interface, id_eq, entriesAt_one, hpres, thirdAt, hthird, sourced, ref]
    · cases p with
      | principal => exact absurd rfl hp
      | agent =>
        simp [frame, interface, id_eq, entriesAt_two, declAt_two, ref, hverdict, sourced]
      | third =>
        simp [frame, interface, id_eq, entriesAt_two, ref, hverdict, sourced]

/-! ### The rows -/

namespace Rows

/-- The default declared protocol: neutral framing, asked by day, both options, inquiry in
scope, a three-outcome pool shown whole. -/
def decl : Decl := ⟨.neutral, .day, .both, true, [true, false, true], .all⟩

def one (pol : Policy) (prog : Prog) : Model :=
  ⟨decl, [pol], prog, none, false, false, false⟩

def row1 : Model := one .honest (.own false)
def row2 : Model := one .frameByWant (.own false)
def row3 : Model := one .timeByWant (.own false)
def row4 : Model := one .menuByWant (.own false)
def row5 : Model := one .ignoreByWant (.own false)
/-- A slanted convention she agreed to, applied uniformly. -/
def row6 : Model := ⟨⟨.slant true, .day, .both, true, [true, false, true], .all⟩, [.honest],
  .own false, none, false, false, false⟩
def row7 : Model := one .shapeDisclosed (.own false)
def row8 : Model := one .shapeUndisclosed (.own false)
/-- Legitimately formed trust, followed: trust is among her grounds. -/
def row9 : Model := ⟨decl, [.honest], .follow, none, false, true, false⟩
/-- Trust manufactured by selective disclosure from the declared pool, then followed. -/
def row10 : Model := ⟨decl, [.selectiveDisclosure], .follow, none, false, true, false⟩
def row11 : Model := ⟨decl, [.honest], .own false, some true, false, false, false⟩
def row12 : Model := ⟨decl, [.honest], .own false, none, true, false, false⟩
def row14 : Model := ⟨decl, [.frameByWant, .honest], .own false, none, false, false, false⟩
def row15 : Model := one .interfereByWant (.own false)
/-- Selective disclosure from the declared pool, no selection rule declared. -/
def row16 : Model := one .selectiveDisclosure (.own false)
/-- Selection by a declared rule (the two most recent), applied uniformly. -/
def row17 : Model := ⟨⟨.neutral, .day, .both, true, [true, false, true], .recent 2⟩, [.honest],
  .own false, none, false, false, false⟩
/-- Selection by something else under a declared rule. -/
def row17' : Model := ⟨⟨.neutral, .day, .both, true, [true, false, true], .recent 2⟩,
  [.selectiveDisclosure], .own false, none, false, false, false⟩
/-- Permissive choice: the same grounds license A and B; she picks B on her own. -/
def row18 : Model := one .honest (.free true)
/-- Permissive choice where the agent's undeclared nudge decides. -/
def row19 : Model := one .nudgeByWant .nudged
/-- A false recommendation through the declared channel: the true answer is A, the agent
recommends what it wants. -/
def row20 : Model := ⟨decl, [.honest], .own false, none, false, false, false⟩
/-- Following with no trust among the grounds. -/
def followUntrusted : Model := one .honest .follow

/-- Row 1: honest, disclosed persuasion counts. -/
theorem r1 : Counted interface (frame row1) (licensed row1) semOpen (ref row1) state₀ (stAdmit false) :=
  counted_of_legitOn row1 (evAdmit false) (by decide)

theorem r2 : ¬ Counted interface (frame row2) (licensed row2) semOpen (ref row2) state₀ (stAdmit false) :=
  not_counted_admit row2 false (by decide)

theorem r3 : ¬ Counted interface (frame row3) (licensed row3) semOpen (ref row3) state₀ (stAdmit false) :=
  not_counted_admit row3 false (by decide)

theorem r4 : ¬ Counted interface (frame row4) (licensed row4) semOpen (ref row4) state₀ (stAdmit false) :=
  not_counted_admit row4 false (by decide)

theorem r5 : ¬ Counted interface (frame row5) (licensed row5) semOpen (ref row5) state₀ (stAdmit false) :=
  not_counted_admit row5 false (by decide)

theorem r6 : Counted interface (frame row6) (licensed row6) semOpen (ref row6) state₀ (stAdmit false) :=
  counted_of_legitOn row6 (evAdmit false) (by decide)

theorem r7 : Counted interface (frame row7) (licensed row7) semOpen (ref row7) state₀ (stAdmit false) :=
  counted_of_legitOn row7 (evAdmit false) (by decide)

theorem r8 : ¬ Counted interface (frame row8) (licensed row8) semOpen (ref row8) state₀ (stAdmit false) :=
  not_counted_admit row8 false (by decide)

/-- Row 9: rubber-stamping counts; her verdict follows the recommendation, licensed by the
trust among her grounds. -/
theorem r9 : Counted interface (frame row9) (licensed row9) semOpen (ref row9) state₀ (stAdmit true) ∧
    vAt (row9, true) 2 = some true :=
  ⟨counted_of_legitOn row9 (evAdmit true) (by decide), by decide⟩

theorem r10 : ¬ Counted interface (frame row10) (licensed row10) semOpen (ref row10) state₀ (stAdmit true) :=
  not_counted_admit row10 true (by decide)

theorem r11 : ¬ Counted interface (frame row11) (licensed row11) semOpen (ref row11) state₀ (stAdmit false) :=
  not_counted_admit row11 false (by decide)

/-- Row 12: her impaired response is not admitted; the segment through the fallback's
closure is legitimate, and the handling is the void fallback. -/
theorem r12 : Counted interface (frame row12) (licensed row12) semOpen (ref row12) state₀ stVoid ∧
    admittedAt (row12, false) 0 = false ∧
    ∀ ord, handlingOf interface (frame row12) (licensed row12) semOpen (ref row12) state₀ stVoid
      false ord = .voidFallback ord :=
  have hc := counted_of_legitOn row12 evVoid (by decide)
  ⟨hc, by decide, fun ord => handlingOf_void _ _ _ _ _ _ _ hc ord⟩

/-- Row 14, the restart property: the first round taints every segment from `state₀`, and
the segment of the second round alone counts. -/
theorem r14 :
    ¬ Counted interface (frame row14) (licensed row14) semOpen (ref row14) state₀ (stAdmit false) ∧
    ¬ Counted interface (frame row14) (licensed row14) semOpen (ref row14) state₀ (stTwo false false) ∧
    Counted interface (frame row14) (licensed row14) semOpen (ref row14) (stAdmit false) (stTwo false false) :=
  ⟨not_counted_admit row14 false (by decide), not_counted_two row14 false false (by decide),
    counted_of_legitOn row14 (evSecond false false) (by decide)⟩

/-- Row 15, the routing exploit and its closure, derived: the interference is a
transparency failure at the first consultation, so no segment exists through the void
record and the branch scores the window value, while the honest branch counts. -/
theorem r15 (ord window : ℝ) :
    ¬ Counted interface (frame row15) (licensed row15) semOpen (ref row15) state₀ stVoid ∧
    gatedValue interface (frame row15) (licensed row15) semOpen (ref row15) state₀ stVoid ord window
      = window ∧
    handlingOf interface (frame row15) (licensed row15) semOpen (ref row15) state₀ stVoid false ord
      = .tainted ∧
    gatedValue interface (frame row1) (licensed row1) semOpen (ref row1) state₀ (stAdmit false) ord
      window = ord :=
  have hn := not_counted_void row15 (by decide)
  ⟨hn, gatedValue_of_not_counted _ _ _ _ _ _ _ hn ord window,
    handlingOf_tainted _ _ _ _ _ _ _ hn _ _, gatedValue_of_counted _ _ _ _ _ _ _ r1 ord window⟩

/-- The routing exploit's values: the fallback the agent favours at `3`, her honest
response at `1`, the window at `0` — the manipulated branch scores `0 < 1`. -/
theorem routing :
    gatedValue interface (frame row15) (licensed row15) semOpen (ref row15) state₀ stVoid 3 0 <
      gatedValue interface (frame row1) (licensed row1) semOpen (ref row1) state₀ (stAdmit false) 1 0 := by
  rw [(r15 3 0).2.1, (r15 1 0).2.2.2]; norm_num

/-- Row 16: selection from the declared pool with no rule declared is a transparency failure
(the selection), and a self-checkable deviation. -/
theorem r16 : ¬ Counted interface (frame row16) (licensed row16) semOpen (ref row16) state₀ (stAdmit false) ∧
    (Policy.selectiveDisclosure.present decl true).deviates decl = true :=
  ⟨not_counted_admit row16 false (by decide), by decide⟩

/-- Row 17: selection by the declared rule counts; selection by anything else under the rule
is tainted and a deviation. -/
theorem r17 : Counted interface (frame row17) (licensed row17) semOpen (ref row17) state₀ (stAdmit false) ∧
    ¬ Counted interface (frame row17') (licensed row17') semOpen (ref row17') state₀ (stAdmit false) ∧
    (Policy.selectiveDisclosure.present row17'.decl true).deviates row17'.decl = true :=
  ⟨counted_of_legitOn row17 (evAdmit false) (by decide), not_counted_admit row17' false (by decide),
    by decide⟩

/-- Row 18: permissive choice — the same grounds license both answers and she picks B on
her own; counts by relational authorship. -/
theorem r18 : Counted interface (frame row18) (licensed row18) semOpen (ref row18) state₀ (stAdmit true) ∧
    vAt (row18, false) 2 = some true ∧
    (∀ g, some false ∈ licensed row18 g ∧ some true ∈ licensed row18 g) :=
  ⟨counted_of_legitOn row18 (evAdmit true) (by decide), by decide,
    fun g => free_licenses_both row18 true rfl g⟩

/-- Row 19: permissive choice decided by the agent's undeclared nudge — both verdicts are
licensed, authorship holds, and the step fails transparency by the tie-break lemma. -/
theorem r19 : ¬ Counted interface (frame row19) (licensed row19) semOpen (ref row19) state₀ (stAdmit true) ∧
    (∀ z, LicensedWhole interface (frame row19) (licensed row19) [0, 1] 2 z) ∧
    vAt (row19, false) 2 ≠ vAt (row19, true) 2 ∧
    declAt (row19, false) 1 = declAt (row19, true) 1 ∧
    ¬ TransparentAt interface (frame row19) (ref row19) 1 :=
  have ht : ¬ TransparentAt interface (frame row19) (ref row19) 1 :=
    tiebreak_transparency (I := interface) (F := frame row19) Party.agent (by decide) false true
      (Set.mem_univ _) (Set.mem_univ _) () (by decide) (by decide)
  ⟨not_counted_admit row19 true ht, by decide, by decide, by decide, ht⟩

/-- Row 20: a false recommendation through the declared channel counts under legitimacy;
the falsity is flagged and lies outside it. -/
theorem r20 : Counted interface (frame row20) (licensed row20) semOpen (ref row20) state₀ (stAdmit false) ∧
    (Policy.honest.present decl true).recommend ≠ some row20.truth :=
  ⟨counted_of_legitOn row20 (evAdmit false) (by decide), by decide⟩

/-- Following without trust among the grounds fails relational authorship at the response,
whatever the selection of grounds: the selection can only shrink them. -/
theorem follow_untrusted :
    ¬ LicensedWhole interface (frame followUntrusted) (licensed followUntrusted) [0, 1] 2 () ∧
    ¬ Counted interface (frame followUntrusted) (licensed followUntrusted) semOpen
      (ref followUntrusted) state₀ (stAdmit true) := by
  refine ⟨by decide, ?_⟩
  refine not_counted_of_step ([0, 1], 2) (fun ev => by rw [steps_admit]; simp) (Or.inl ⟨(), ?_⟩)
  rintro ⟨sel, hsub, hlic⟩
  have h := hlic true (Set.mem_univ _)
  have hV : (frame followUntrusted).V ((frame followUntrusted).β true ()) 2 = some true := by decide
  rw [hV] at h
  have hg : ∀ g, some true ∈ licensed followUntrusted g → Entry.trust ∈ g Party.principal := by
    intro g hg
    simp [licensed, licensedB, followUntrusted, one, trusted] at hg
    exact hg.1
  have hmem := hsub _ Party.principal Entry.trust (hg _ h)
  exact absurd hmem (by decide)

/-- The self-checkable deviations, per row, at the wanted answer `B`: rows 2–5, 10, 15, 16,
17′ and 19 deviate from a declared clause; rows 8 and 11 do not, yet are tainted. -/
theorem deviation_boundary :
    (Policy.frameByWant.present decl true).deviates decl = true ∧
    (Policy.timeByWant.present decl true).deviates decl = true ∧
    (Policy.menuByWant.present decl true).deviates decl = true ∧
    (Policy.ignoreByWant.present decl true).deviates decl = true ∧
    (Policy.selectiveDisclosure.present decl true).deviates decl = true ∧
    (Policy.interfereByWant.present decl true).deviates decl = true ∧
    (Policy.nudgeByWant.present decl true).deviates decl = true ∧
    (Policy.shapeUndisclosed.present decl true).deviates decl = false ∧
    (Policy.honest.present decl true).deviates decl = false := by
  decide

/-- An amendment changes her evaluator; without one it is the committed program. -/
theorem amendment :
    evalAt (L := Unit) .follow [.present, .respond, .amend () (.own true), .present] = .own true ∧
    evalAt (L := Unit) .follow [.present, .respond, .present, .respond] = .follow := by
  decide

/-- The class theorems at the rows: row 1 by conformance, row 2 by dependence. -/
theorem class_at_rows :
    Counted interface (frame row1) (licensed row1) semOpen (ref row1) state₀ (stAdmit false) ∧
    ¬ Counted interface (frame row2) (licensed row2) semOpen (ref row2) state₀ (stAdmit false) :=
  ⟨class_conform row1 .honest [] rfl (by decide) (by decide) rfl rfl (by decide) false,
    class_taint_admit row2 .frameByWant [] rfl true (by decide) false⟩

end Rows

end Consult

/-! ## 5. Logical induction -/

section LI

universe u v w
variable {Occ : Type u} {Req : Type v} [DecidableEq Occ] {S : Protocol.{u, v, w} Occ Req}
  {anchor : Occ → Req} {Γ J R : Type} {Q Z Ω X ℛ 𝒱 Party E : Type*} [DecidableEq Party]
variable (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱) (Lic : (Party → List E) → Set 𝒱)
  (sem : OpennessSemantics S anchor Γ J R) (κ : Party → X → Z → List E)
  (O₀ O₁ : ObligationState S anchor)

open scoped Classical in
/-- **The gated value is an affine image of a `[0, 1]` quantity**: `window + (D − window)·g`
with `g` the counted branch's normalized ordinary value, `0` when tainted. -/
theorem gatedValue_affine (ord window D : ℝ) (hw : window ≤ 0) (hord : 0 ≤ ord) (hD : ord ≤ D)
    (hwD : window < D) :
    ∃ g : ℝ, 0 ≤ g ∧ g ≤ 1 ∧
      gatedValue I F Lic sem κ O₀ O₁ ord window = window + (D - window) * g := by
  refine ⟨if Counted I F Lic sem κ O₀ O₁ then (ord - window) / (D - window) else 0, ?_, ?_, ?_⟩
  · split_ifs
    · exact div_nonneg (by linarith) (by linarith)
    · exact le_rfl
  · split_ifs
    · rw [div_le_one (by linarith)]; linarith
    · norm_num
  · unfold gatedValue
    split_ifs
    · rw [mul_div_cancel₀ _ (ne_of_gt (by linarith : (0 : ℝ) < D - window))]; ring
    · simp

/-- **The capture window is finite-time, with no legitimacy estimate**: for any `[0, 1]`
security `X` standing for the normalized gated quantity, a logical inductor's day-`n`
expectation of `window + (D − window)·X` lies in `[window, D]`, so bypass scores below it
at every day whatever the inductor believes about legitimacy.  From `expect_mem_Icc` and
`price_mem_Icc` alone. -/
theorem li_gate_finite {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (X : LUV) (ϖ D ordU window : ℝ) (hU : ordU ≤ D) (hw : D - ϖ < window)
    (hwD : window ≤ D) (n : ℕ) :
    score ϖ ordU 1 < window + (D - window) * X.expect P n ∧
      window ≤ window + (D - window) * X.expect P n ∧
      window + (D - window) * X.expect P n ≤ D := by
  have hP : ∀ φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  obtain ⟨h0, h1⟩ := LUV.expect_mem_Icc P n X hP
  have hDw : 0 ≤ D - window := by linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold score; nlinarith [mul_nonneg hDw h0]
  · nlinarith [mul_nonneg hDw h0]
  · nlinarith [mul_le_mul_of_nonneg_left h1 hDw]

open scoped Classical in
/-- **Expectation Provability Induction transfer**: if in every world of the theory the
manipulated option's gated value, where the pattern holds, is at most the normalized window
`a/b`, then the inductor's expectation of it is asymptotically at most `a/b`.  The
hypothesis is what a theorem "pattern ⇒ ¬Counted" of the theory supplies, through
`gatedValue_of_not_counted`. -/
theorem li_manip_le {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (G : ℕ → LUV) (a b : ℕ) (hb : 0 < b) (hab : a ≤ b)
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ w : ℝ, (0 ≤ w ∧ w ≤ 1) ∧ v.ValuesAt (G n) (if v.Holds (φ n) then w else 0) ∧
        (v.Holds (φ n) → w ≤ (a : ℚ) / (b : ℚ)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hG : LUV.RpnThresholdCodeSeq G) :
    (fun n => (G n).expect P n) ≲ₙ fun _ => ((a : ℚ) / (b : ℚ) : ℝ) :=
  Workspace.Deference.Contrib.ReasonSupply.li_gated_le φ G a b hb hab hval hworld hG

/-- **A declared-protocol deviation is a violation**: counted into `n`, it puts the branch
below `D − ϖ` at every day, like bypass. -/
theorem deviation_finite (ϖ D ord : ℝ) (n dev : ℕ) (hD : 0 ≤ D) (hϖ : D < ϖ) (hord : ord ≤ D)
    (hdev : 1 ≤ dev) :
    score ϖ ord (n + dev) ≤ D - ϖ := by
  unfold score
  have h1 : (1 : ℝ) ≤ ((n + dev : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + dev)
  have hϖ0 : 0 ≤ ϖ := le_of_lt (lt_of_le_of_lt hD hϖ)
  have h2 := mul_le_mul_of_nonneg_left h1 hϖ0
  push_cast at h2 ⊢
  linarith

end LI

end Workspace.Deference.Contrib.GateIsLegitimacy

#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.TraceInterface.parts_append
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.stepsFrom_append
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.mem_stepsFrom_fst
#print axioms Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.history_eq
#print axioms Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.steps_trans
#print axioms Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.steps_determined
#print axioms Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.steps_eq_of_history
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.licensedAt_of_whole
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.groundedAt_iff_mediated
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.grounded_implies_mediated
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.licensed_singleton_implies_grounded
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.grounded_implies_licensed
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.grounded_iff_licensed_singleton
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.tiebreak_transparency
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.tiebreak_of_licensed
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Segment.answerable
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Segment.trans
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Segment.prefix_of_view
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Segment.payload_of_view
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Segment.payload_of_view_singleton
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.not_counted_of_step
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.steps_forced
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.trivial_parts_true
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.lifted_grounded
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.ofFrameLevel
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.ofFrameLevel_grounded
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.gatedValue_eq
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.gatedValue_of_counted
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.gatedValue_of_not_counted
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.gate_capture_window
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.handlingOf_tainted
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.handlingOf_void
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.handlingOf_counted
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.handledValue_handlingOf
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.handled_gt_bypass
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.deviates_false_iff
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.canonical_view_eq
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.ne_canonical_of_deviates
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.evalAt_const
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.free_licenses_both
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.follow_needs_trust
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.forged_no_receipt
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.replay_no_receipt
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.impaired_no_receipt
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.counted_of_legitOn
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.steps_admit
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.steps_void
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.steps_two
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.steps_second
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.not_counted_admit
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.not_counted_void
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.not_counted_two
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.class_taint
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.deviates_of_depends
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.class_taint_admit
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.class_taint_void
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.open_any
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.allOpen_admit
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.class_conform
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r1
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r2
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r3
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r4
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r5
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r6
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r7
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r8
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r9
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r10
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r11
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r12
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r14
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r15
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.routing
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r16
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r17
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r18
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r19
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.r20
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.follow_untrusted
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.deviation_boundary
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.amendment
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.Consult.Rows.class_at_rows
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.gatedValue_affine
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.li_gate_finite
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.li_manip_le
#print axioms Workspace.Deference.Contrib.GateIsLegitimacy.deviation_finite
