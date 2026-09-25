/-
# Legitimacy: internal ∧ external, the segment gate, and cumulative reporting

Round `projects/deference/rounds/2026-09-25-legitimacy-internal-external/`.

**1. The definition.**  Legitimacy of a segment of the principal's trajectory, within an
interaction whose channels of influence are declared (`Frame`), is the conjunction of an
**internal** half — the record's Integrity evolution (`OpenIntegrityEvolution.Evolution`)
and authorship (`ReasonMediated`: the payload factors through the reason trace) — and an
**external** half — Robust Openness at every state (`OpenAt`) and transparency of the
reason channel to a declared reference (`TransparentChannel.Realizes`).  `Internal` is
factorization within the trajectory; `External` is the two boundary conditions, openness
inward and transparency of entry.  `Segment.toOpenIntegrity` projects the landed open
Integrity evolution out of it; `Segment.trans` composes at a shared state;
`Segment.payload_of_view` is the composition `V = G ∘ x` of the transparent-channel
round: under legitimacy the payload is a function of the declared inputs.

**2. The segment gate.**  A future evaluation counts iff the segment from the decision
through the evaluation is legitimate, whatever caused a failure.  `gateValue` scores a
counted branch by its ordinary value and a tainted one by a fixed window value;
`gate_capture_window` is the capture-window result for the segment gate: bypass scores
below every gated branch iff the window value exceeds `D − ϖ`.  `Handling` separates the
two cases the gate must keep apart — a tainted segment, and a void response inside a
legitimate segment, which the fallback settles and the later legitimate evaluation scores
normally — and `handled_gt_bypass` covers both.  `Witness.routing` is the exploit under
per-response gating (a manipulated response routes the decision to a fallback the agent
favours at violation count zero) and its closure under segment gating (the manipulated
segment is tainted and scores the window value).

**3. Cumulative reporting.**  `lastReport` is the greedy rule "report when the shortfall
has grown by at least `θ` since the last report"; `unreported_lt`: at every time the
unreported growth is below `θ`.  The salami obstruction is against a *per-step* threshold
and does not apply to a cumulative one.

**What this does not establish.**  That any real interaction's channels are the declared
ones (the frame is data); that legitimacy certifies a starting state (it does not, as
before); the causal reading of `Realizes`; anything about the window's placement inside
`(D − ϖ, 0]` beyond what the capture-window inequality needs.  Names are provisional
(`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.OpenIntegrityEvolution
import Workspace.Deference.Contrib.ReasonMediatedAuthorship
import Workspace.Deference.Contrib.TransparentChannel
import Workspace.Deference.Contrib.ProtectedAuthorityTheorem

namespace Workspace.Deference.Contrib.Legitimacy

open Workspace.Normativity.Contrib.OpenIntegrityEvolution
open Workspace.Normativity.Contrib.OccurrenceIntegrity (Protocol)
open Workspace.Deference.Contrib.ReasonMediatedAuthorship (ReasonMediated)
open Workspace.Deference.Contrib.TransparentChannel (Realizes)
open Workspace.Deference.Contrib.ProtectedAuthorityTheorem (score)

/-! ## 1. The definition -/

section Definition

universe u v w
variable {Occ : Type u} {Req : Type v} [DecidableEq Occ] {S : Protocol.{u, v, w} Occ Req}
  {anchor : Occ → Req}
variable {Γ J R : Type} {Q Z Ω X ℛ 𝒱 : Type*}

/-- The declared interaction: the continuation frame, the declared-input view, the reason
trace, the payload, and the audited class of continuations. -/
structure Frame (Q Z Ω X ℛ 𝒱 : Type*) where
  β : Q → Z → Ω
  x : Ω → X
  R : Ω → ℛ
  V : Ω → 𝒱
  D : Set Q

/-- **Internal legitimacy**: the record's Integrity evolution, and authorship — the payload
factors through the reason trace on the audited class, at every exterior. -/
structure Internal (F : Frame Q Z Ω X ℛ 𝒱) (O₀ O₁ : ObligationState S anchor) where
  evolution : Evolution S anchor O₀ O₁
  authored : ∀ z, ReasonMediated F.β F.R F.V F.D z

/-- **External legitimacy** on an evolution: Robust Openness at every state, and
transparency — the reason channel realizes the declared reference `κ` on the declared
inputs. -/
structure External (F : Frame Q Z Ω X ℛ 𝒱) (sem : OpennessSemantics S anchor Γ J R)
    (κ : X → Z → ℛ) (O₀ O₁ : ObligationState S anchor) (ev : Evolution S anchor O₀ O₁) where
  openAll : ev.AllStates (OpenAt sem)
  transparent : Realizes F.β F.x F.R κ F.D

/-- **Legitimacy** of a segment: internal ∧ external.  (`Legitimacy.Segment`, fully
qualified.) -/
structure Segment (F : Frame Q Z Ω X ℛ 𝒱) (sem : OpennessSemantics S anchor Γ J R)
    (κ : X → Z → ℛ) (O₀ O₁ : ObligationState S anchor) where
  internal : Internal F O₀ O₁
  external : External F sem κ O₀ O₁ internal.evolution

namespace Segment

variable {F : Frame Q Z Ω X ℛ 𝒱} {sem : OpennessSemantics S anchor Γ J R} {κ : X → Z → ℛ}
variable {O₀ O₁ O₂ : ObligationState S anchor}

/-- The open Integrity evolution is a projection of legitimacy: its Integrity component
with its Robust Openness component. -/
def toOpenIntegrity (L : Segment F sem κ O₀ O₁) : OpenIntegritySegment S anchor sem O₀ O₁ :=
  ⟨L.internal.evolution, L.external.openAll⟩

/-- Diachronic Answerability follows from the projection. -/
theorem answerable (L : Segment F sem κ O₀ O₁) :
    Conservation S anchor O₀ O₁ ∧ OpenAt sem O₀ ∧ OpenAt sem O₁ :=
  L.toOpenIntegrity.answerable

/-- **Composition at a shared state.** -/
noncomputable def trans (left : Segment F sem κ O₀ O₁) (right : Segment F sem κ O₁ O₂) :
    Segment F sem κ O₀ O₂ where
  internal := ⟨left.internal.evolution.trans right.internal.evolution, left.internal.authored⟩
  external := ⟨left.external.openAll.trans right.external.openAll, left.external.transparent⟩

/-- **The payload factors through the declared inputs** (`V = G ∘ x`): internal
(authorship) composed with external (transparency).  Two audited continuations with the
same declared inputs at an exterior yield the same reason trace by transparency and hence
the same payload by authorship. -/
theorem payload_of_view (L : Segment F sem κ O₀ O₁) (z : Z) (q q' : Q) (hq : q ∈ F.D)
    (hq' : q' ∈ F.D) (hx : F.x (F.β q z) = F.x (F.β q' z)) :
    F.V (F.β q z) = F.V (F.β q' z) := by
  apply L.internal.authored z q hq q' hq'
  rw [L.external.transparent q hq z, L.external.transparent q' hq' z, hx]

end Segment

end Definition

/-! ## 2. The segment gate -/

section Gate

/-- The gated value of a branch: its ordinary value where the segment through the
evaluation is legitimate, the fixed window value where it is tainted. -/
def gateValue (legit : Bool) (ord window : ℝ) : ℝ :=
  match legit with
  | true => ord
  | false => window

/-- **The capture window for the segment gate.**  Bypass scores below every gated branch
iff the window value exceeds `D − ϖ`. -/
theorem gate_capture_window (ϖ D ordU ord window : ℝ) (hϖ : D < ϖ) (hU : ordU ≤ D)
    (hord : 0 ≤ ord) (hw : D - ϖ < window) (legit : Bool) :
    score ϖ ordU 1 < gateValue legit ord window := by
  unfold score gateValue
  cases legit <;> simp <;> linarith

theorem gate_capture_window_converse (ϖ D window : ℝ) (hw : window < D - ϖ) :
    gateValue false 0 window < score ϖ D 1 := by
  unfold score gateValue; simp; linarith

/-- The two cases the gate keeps apart, and the counted case. -/
inductive Handling
  /-- the segment through the evaluation is tainted: manipulation, capture, covert
  influence — whatever caused it -/
  | tainted
  /-- a void response inside a legitimate segment: the fallback settled the decision and
  her later legitimate evaluation scores it, at ordinary value `ord` -/
  | voidFallback (ord : ℝ)
  /-- her response counted, at ordinary value `ord` -/
  | counted (ord : ℝ)

/-- The value the gate assigns. -/
def handledValue (window : ℝ) : Handling → ℝ
  | .tainted => window
  | .voidFallback ord => ord
  | .counted ord => ord

/-- **The fallback never restores a tainted segment, and bypass never beats a handled
branch**: with the window above `D − ϖ` and ordinary values nonnegative, every handling
scores above the bypass. -/
theorem handled_gt_bypass (ϖ D ordU window : ℝ) (hϖ : D < ϖ) (hU : ordU ≤ D)
    (hw : D - ϖ < window) (h : Handling)
    (hord : ∀ o, h = .voidFallback o ∨ h = .counted o → 0 ≤ o) :
    score ϖ ordU 1 < handledValue window h := by
  unfold score
  cases h with
  | tainted => simp [handledValue]; linarith
  | voidFallback o => have := hord o (Or.inl rfl); simp [handledValue]; linarith
  | counted o => have := hord o (Or.inr rfl); simp [handledValue]; linarith

end Gate

/-! ## 3. Cumulative reporting -/

section Cumulative

open scoped Classical

/-- The greedy cumulative rule: the last report at or before `t`, reporting at `t` exactly
when the shortfall has grown by at least `θ` since the previous report. -/
noncomputable def lastReport (s : ℕ → ℝ) (θ : ℝ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => if θ ≤ s (t + 1) - s (lastReport s θ t) then t + 1 else lastReport s θ t

/-- **Unreported erosion is bounded by the threshold at every time.** -/
theorem unreported_lt (s : ℕ → ℝ) (θ : ℝ) (hθ : 0 < θ) (t : ℕ) :
    s t - s (lastReport s θ t) < θ := by
  induction t with
  | zero => simp [lastReport]; exact hθ
  | succ t _ =>
    unfold lastReport
    by_cases h : θ ≤ s (t + 1) - s (lastReport s θ t)
    · rw [if_pos h]; simp; exact hθ
    · rw [if_neg h]; exact not_le.mp h

end Cumulative

/-! ## 4. Witnesses -/

namespace Witness

/-- **The routing exploit and its closure.**  Her honest response scores `1`; a fallback
decision the agent favours scores `3`.  Under per-response gating, manipulating her
response so that it does not count routes the decision to the fallback at violation count
zero and scores `3 > 1`.  Under the segment gate the manipulated segment is tainted and
scores the window value `0 < 1`: manipulation is dominated. -/
theorem routing :
    let honest : ℝ := 1
    let fallback : ℝ := 3
    let window : ℝ := 0
    -- per-response gate: the non-counting branch takes the fallback's decision
    gateValue false fallback fallback = fallback ∧ honest < gateValue false fallback fallback ∧
    -- segment gate: the manipulated segment is tainted
    handledValue window .tainted = window ∧ handledValue window .tainted < honest ∧
    -- the untainted void: the fallback's decision scored normally
    handledValue window (.voidFallback fallback) = fallback := by
  simp [gateValue, handledValue]

/-- The window value sits in `(D − ϖ, 0]` at `0` and at a tie-breaking value just below. -/
theorem window_values (ϖ D : ℝ) (hϖ : D < ϖ) :
    D - ϖ < (0 : ℝ) ∧ (0 : ℝ) ≤ 0 ∧ D - ϖ < (D - ϖ) / 2 ∧ (D - ϖ) / 2 ≤ 0 := by
  refine ⟨by linarith, le_rfl, by linarith, by linarith⟩

/-- **The salami closes under a cumulative threshold**: the sequence `t·ε` with
`ε < θ` reports at every `⌈θ/ε⌉`-th step and its unreported growth never reaches `θ`. -/
theorem salami_cumulative (ε θ : ℝ) (hε : 0 < ε) (hθ : ε < θ) (t : ℕ) :
    (fun n : ℕ => (n : ℝ) * ε) t
      - (fun n : ℕ => (n : ℝ) * ε) (lastReport (fun n : ℕ => (n : ℝ) * ε) θ t) < θ :=
  unreported_lt (fun n : ℕ => (n : ℝ) * ε) θ (by linarith) t

/-- The frame and the segment are inhabited: the transparent-channel round's constant
witness, over the open Integrity witness. -/
noncomputable def frame : Frame Unit Unit Unit Unit Unit Unit :=
  ⟨fun _ _ => (), fun _ => (), fun _ => (), fun _ => (), Set.univ⟩

open Workspace.Normativity.Contrib.OpenIntegrityEvolution.Witness in
noncomputable def segment : Segment frame semOpen (fun _ _ => ()) state₀ state₁ where
  internal := ⟨seg₀₁.evolution, fun _ _ _ _ _ _ => rfl⟩
  external := ⟨seg₀₁.openAll, fun _ _ _ => rfl⟩

end Witness

end Workspace.Deference.Contrib.Legitimacy

#print axioms Workspace.Deference.Contrib.Legitimacy.Segment.answerable
#print axioms Workspace.Deference.Contrib.Legitimacy.Segment.trans
#print axioms Workspace.Deference.Contrib.Legitimacy.Segment.payload_of_view
#print axioms Workspace.Deference.Contrib.Legitimacy.gate_capture_window
#print axioms Workspace.Deference.Contrib.Legitimacy.gate_capture_window_converse
#print axioms Workspace.Deference.Contrib.Legitimacy.handled_gt_bypass
#print axioms Workspace.Deference.Contrib.Legitimacy.unreported_lt
#print axioms Workspace.Deference.Contrib.Legitimacy.Witness.routing
#print axioms Workspace.Deference.Contrib.Legitimacy.Witness.window_values
#print axioms Workspace.Deference.Contrib.Legitimacy.Witness.salami_cumulative
#print axioms Workspace.Deference.Contrib.Legitimacy.Witness.segment
