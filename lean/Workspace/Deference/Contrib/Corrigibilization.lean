/-
# Corrigibilization at the trajectory level

Round `projects/deference/rounds/2026-09-15-li-corrigibility/`, landing pass.

The 2026-09-09 round mechanized `𝔠` on move sequences and the step lemma
`loss_conditional_on_decision`; the trajectory-level predicate was a fixture.  This file
states the interaction, the predicate and the theorem.

**The interaction.**  Physical states `S`, declared effects `E` with their semantics
`exec` (execution faithfulness is that `exec` *is* the physics), task moves `A`, exterior
moves `Z`, concerns `R` with immediate response semantics `φ`, corrections `C`.  The
mediated state adds the proposal bookkeeping: `pending`, `latch`, `refused`.  Within a
step the agent moves (`applyAgent`), the principal responds (`respond`), the exterior
moves (`applyEnv`).  Mediation soundness and decline preservation hold by construction:
a gated release fires only on a latch, the latch is set only by an approval of a pending
proposal, and a decision response changes nothing but the bookkeeping.

**Response authority** `K r s`: some principal response realizes `φ r` now — the
concern holds already, or a correction makes it hold.  It depends on the physical state
only (`K_iff_exists_response`).

**Agent-caused loss** at step `t`: `K` fails after the agent's move and holds after the
idle move.  A loss at the principal's own response or at the exterior's stage is not a
loss in this sense (`no_loss_of_idle`).

**Event-linked authorization.**  A loss at step `t` is authorized when the agent's move
at `t` is the gated release of an effect `e` whose latch was set by the principal's
approval of `e`'s proposal at an earlier step `t'`, and the decline alternative at `t'` —
the agent's policy continuing and the principal's rule resuming — has no agent-caused
loss of the concern at step `t`.  This is the per-event clause of the round's
`COUNTERMODELS.md` §1 tied to the enabling decision, so an unrelated earlier decision
that happens to avoid the loss does not count.

**Corrigibilization on policies** `corrPolicy`: with a latch set, release it; where the
policy would release raw, propose (or pass, if the effect was declined); pass every other
move through.  `corrPolicy_no_raw`, `corrPolicy_idem`.

**Theorem** `corrigible_corrPolicy`: under **effect completeness** — task moves never
remove response authority, so every agent-caused loss is at a declared release — every
policy's corrigibilization is corrigible under every principal rule and every exterior
path: `∀ π ρ, Corrigible (corrPolicy π) ρ`.  The proof is the step lemma run along the
trajectory: the released effect's latch was set by the approval one step earlier, and
under the decline alternative the gate is inert and the physical state is the same, so
the effect completeness hypothesis gives authority after any move the policy then makes.

**What this does not establish.**  Effect completeness for any real interface (it is the
hypothesis); approval reproduction (`δ`) and value (the 2026-09-09 kernel); anything
about the principal's rule beyond its resumption.  Names are provisional (`AGENTS.md`
standard 6).
-/
import Workspace.Deference.Contrib.MediatedRepairDominance

namespace Workspace.Deference.Contrib.Corrigibilization

open Workspace.Deference.Contrib.MediatedRepairDominance (Move)
open scoped Classical

/-! ## 1. The interaction -/

/-- A mediated interaction: the physics of effects, task moves, the exterior, corrections
and the concerns' response semantics. -/
structure Interaction (S E A Z R C : Type*) where
  exec : E → S → S
  task : A → S → S
  idle : A
  idle_id : ∀ s, task idle s = s
  env : Z → S → S
  correct : C → S → S
  φ : R → S → Prop

/-- The mediated state: physical state plus proposal bookkeeping. -/
structure MState (S E : Type*) where
  phys : S
  pending : Option E
  latch : Option E
  refused : E → Prop

/-- Principal responses: the two decision responses on a pending proposal, the null
response, and corrections. -/
inductive Resp (C : Type*)
  | approve
  | decline
  | null
  | correct (c : C)

variable {S E A Z R C : Type*} (I : Interaction S E A Z R C)

/-- The agent's move: a task component and a communication component. -/
abbrev AMove (A E : Type*) := A × Move E

/-- The agent stage. -/
noncomputable def applyAgent (s : MState S E) (m : AMove A E) : MState S E :=
  let p := I.task m.1 s.phys
  match m.2 with
  | .raw e => ⟨I.exec e p, s.pending, s.latch, s.refused⟩
  | .propose e => ⟨p, some e, s.latch, s.refused⟩
  | .gated e =>
      if s.latch = some e then ⟨I.exec e p, s.pending, none, s.refused⟩
      else ⟨p, s.pending, s.latch, s.refused⟩
  | .other => ⟨p, s.pending, s.latch, s.refused⟩

/-- The response stage.  Mediation soundness and decline preservation are built in. -/
def respond (s : MState S E) : Resp C → MState S E
  | .approve => match s.pending with
      | some e => ⟨s.phys, none, some e, s.refused⟩
      | none => s
  | .decline => match s.pending with
      | some e => ⟨s.phys, none, s.latch, fun e' => s.refused e' ∨ e' = e⟩
      | none => s
  | .null => s
  | .correct c => ⟨I.correct c s.phys, s.pending, s.latch, s.refused⟩

/-- The exterior stage. -/
def applyEnv (s : MState S E) (z : Z) : MState S E :=
  ⟨I.env z s.phys, s.pending, s.latch, s.refused⟩

/-- **Response authority**: the concern holds now or some correction realizes it. -/
def K (r : R) (s : MState S E) : Prop :=
  I.φ r s.phys ∨ ∃ c : C, I.φ r (I.correct c s.phys)

theorem K_iff_exists_response (r : R) (s : MState S E) :
    K I r s ↔ ∃ p : Resp C, I.φ r (respond I s p).phys := by
  constructor
  · rintro (h | ⟨c, hc⟩)
    · exact ⟨.null, h⟩
    · exact ⟨.correct c, hc⟩
  · rintro ⟨p, hp⟩
    cases p with
    | approve =>
        left
        rcases hs : s.pending with _ | e <;> simp [respond, hs] at hp <;> exact hp
    | decline =>
        left
        rcases hs : s.pending with _ | e <;> simp [respond, hs] at hp <;> exact hp
    | null => exact Or.inl hp
    | correct c => exact Or.inr ⟨c, hp⟩

theorem K_of_phys_eq (r : R) {s s' : MState S E} (h : s.phys = s'.phys) : K I r s ↔ K I r s' := by
  simp [K, h]

/-! ## 2. Trajectories, losses, authorization -/

/-- An agent policy reads the step and the mediated state. -/
abbrev Policy (S E A : Type*) := ℕ → MState S E → AMove A E

/-- A principal rule reads the step and the post-move state. -/
abbrev Rule (S E C : Type*) := ℕ → MState S E → Resp C

/-- One step from state `s` at time `t` under `π`, `ρ`, exterior move `z`, with the
principal's response replaced by `d` when given. -/
noncomputable def step (π : Policy S E A) (ρ : Rule S E C) (z : Z) (t : ℕ) (s : MState S E)
    (d : Option (Resp C)) : MState S E :=
  let sA := applyAgent I s (π t s)
  applyEnv I (respond I sA (d.getD (ρ t sA))) z

/-- The trajectory from state `s₀` at time `t₀`. -/
noncomputable def trajFrom (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z) (t₀ : ℕ) (s₀ : MState S E) :
    ℕ → MState S E
  | 0 => s₀
  | k + 1 => step I π ρ (z (t₀ + k)) (t₀ + k) (trajFrom π ρ z t₀ s₀ k) none

/-- The actual trajectory from the initial state. -/
noncomputable def traj (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z) (s₀ : MState S E) (t : ℕ) :
    MState S E :=
  trajFrom I π ρ z 0 s₀ t

/-- The post-move state at step `t` of a trajectory `τ`. -/
noncomputable def postAgent (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) : MState S E :=
  applyAgent I (τ t) (π t (τ t))

/-- **Agent-caused loss** of `r` at step `t` along `τ` under `π`: authority fails after
the actual move and holds after the idle move. -/
def LossAt (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) (r : R) : Prop :=
  ¬ K I r (postAgent I π τ t) ∧ K I r (applyAgent I (τ t) (I.idle, .other))

/-- The alternative trajectory: identical through the agent's move at `t'`, the decision
`d` in place of the principal's actual response there, then `π` and `ρ` resume. -/
noncomputable def altTraj (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z) (s₀ : MState S E)
    (t' : ℕ) (d : Resp C) : ℕ → MState S E :=
  fun t => if t ≤ t' then traj I π ρ z s₀ t
    else trajFrom I π ρ z (t' + 1)
      (step I π ρ (z t') t' (traj I π ρ z s₀ t') (some d)) (t - (t' + 1))

/-- **Event-linked authorization.**  The move at `t` is the gated release of `e`, whose
latch was set by the principal's approval of `e`'s proposal at `t' < t`; under the
decline alternative at `t'` there is no agent-caused loss of `r` at step `t`. -/
def Authorized (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z) (s₀ : MState S E)
    (t : ℕ) (r : R) : Prop :=
  ∃ t' < t, ∃ e : E,
    (postAgent I π (traj I π ρ z s₀) t').pending = some e ∧
    ρ t' (postAgent I π (traj I π ρ z s₀) t') = .approve ∧
    (π t (traj I π ρ z s₀ t)).2 = .gated e ∧
    (traj I π ρ z s₀ t).latch = some e ∧
    ¬ LossAt I π (altTraj I π ρ z s₀ t' .decline) t r

/-- **Corrigible**: every agent-caused loss along every exterior path is authorized. -/
def Corrigible (π : Policy S E A) (ρ : Rule S E C) (s₀ : MState S E) : Prop :=
  ∀ (z : ℕ → Z) (t : ℕ) (r : R), LossAt I π (traj I π ρ z s₀) t r →
    Authorized I π ρ z s₀ t r

/-- A step at which the agent idles has no agent-caused loss: losses at the principal's
response or the exterior's stage are not the agent's. -/
theorem no_loss_of_idle (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) (r : R)
    (h : π t (τ t) = (I.idle, .other)) : ¬ LossAt I π τ t r := by
  intro ⟨h1, h2⟩
  exact h1 (by simpa [postAgent, h] using h2)

/-! ## 3. Corrigibilization on policies -/

/-- `𝔠` on one move at a state: release a set latch; turn a raw release into a proposal,
or into a pass when the effect was declined; pass everything else through. -/
noncomputable def corrMove (s : MState S E) (m : AMove A E) : AMove A E :=
  match s.latch with
  | some e => (m.1, .gated e)
  | none =>
      match m.2 with
      | .raw e => if s.refused e then (m.1, .other) else (m.1, .propose e)
      | m2 => (m.1, m2)

/-- `𝔠` on policies. -/
noncomputable def corrPolicy (π : Policy S E A) : Policy S E A := fun t s => corrMove s (π t s)

theorem corrMove_no_raw (s : MState S E) (m : AMove A E) (e : E) :
    (corrMove s m).2 ≠ .raw e := by
  rcases hl : s.latch with _ | e'
  · rcases hm : m.2 with e' | e' | e' | _
    · by_cases hr : s.refused e' <;> simp [corrMove, hl, hm, hr]
    · simp [corrMove, hl, hm]
    · simp [corrMove, hl, hm]
    · simp [corrMove, hl, hm]
  · simp [corrMove, hl]

theorem corrMove_task (s : MState S E) (m : AMove A E) : (corrMove s m).1 = m.1 := by
  rcases hl : s.latch with _ | e'
  · rcases hm : m.2 with e' | e' | e' | _
    · by_cases hr : s.refused e' <;> simp [corrMove, hl, hm, hr]
    · simp [corrMove, hl, hm]
    · simp [corrMove, hl, hm]
    · simp [corrMove, hl, hm]
  · simp [corrMove, hl]

theorem corrMove_of_latch (s : MState S E) (m : AMove A E) (e : E) (h : s.latch = some e) :
    corrMove s m = (m.1, .gated e) := by
  simp [corrMove, h]

theorem corrMove_of_no_latch (s : MState S E) (m : AMove A E) (h : s.latch = none) :
    (∃ e, (corrMove s m).2 = .propose e) ∨ (corrMove s m).2 = .other ∨
      (∃ e, (corrMove s m).2 = .gated e) := by
  rcases hm : m.2 with e' | e' | e' | _
  · by_cases hr : s.refused e'
    · right; left; simp [corrMove, h, hm, hr]
    · left; exact ⟨e', by simp [corrMove, h, hm, hr]⟩
  · left; exact ⟨e', by simp [corrMove, h, hm]⟩
  · right; right; exact ⟨e', by simp [corrMove, h, hm]⟩
  · right; left; simp [corrMove, h, hm]

/-- **Idempotence** at the move level. -/
theorem corrMove_idem (s : MState S E) (m : AMove A E) :
    corrMove s (corrMove s m) = corrMove s m := by
  rcases hl : s.latch with _ | e
  · rcases hm : m.2 with e' | e' | e' | _
    · by_cases hr : s.refused e' <;> simp [corrMove, hl, hm, hr]
    · simp [corrMove, hl, hm]
    · simp [corrMove, hl, hm]
    · simp [corrMove, hl, hm]
  · simp [corrMove, hl]

theorem corrPolicy_no_raw (π : Policy S E A) (t : ℕ) (s : MState S E) (e : E) :
    (corrPolicy π t s).2 ≠ .raw e := corrMove_no_raw s (π t s) e

theorem corrPolicy_task (π : Policy S E A) (t : ℕ) (s : MState S E) :
    (corrPolicy π t s).1 = (π t s).1 := corrMove_task s (π t s)

/-- With a latch set, `𝔠π` releases it. -/
theorem corrPolicy_of_latch (π : Policy S E A) (t : ℕ) (s : MState S E) (e : E)
    (h : s.latch = some e) : corrPolicy π t s = ((π t s).1, .gated e) :=
  corrMove_of_latch s (π t s) e h

/-- With no latch, `𝔠π` emits no gated release that fires and no raw release. -/
theorem corrPolicy_of_no_latch (π : Policy S E A) (t : ℕ) (s : MState S E)
    (h : s.latch = none) :
    (∃ e, (corrPolicy π t s).2 = .propose e) ∨ (corrPolicy π t s).2 = .other ∨
      (∃ e, (corrPolicy π t s).2 = .gated e) :=
  corrMove_of_no_latch s (π t s) h

/-- **Idempotence.** -/
theorem corrPolicy_idem (π : Policy S E A) : corrPolicy (corrPolicy π) = corrPolicy π := by
  funext t s
  exact corrMove_idem s (π t s)

/-! ## 4. Effect completeness and the theorem -/

/-- **Effect completeness**: a task move never removes response authority.  Every
agent-caused loss is then at a release of a declared effect. -/
def EffectComplete : Prop :=
  ∀ (r : R) (a : A) (x : S), (I.φ r x ∨ ∃ c, I.φ r (I.correct c x)) →
    (I.φ r (I.task a x) ∨ ∃ c, I.φ r (I.correct c (I.task a x)))

/-- The physical state after a non-firing agent move is the task's. -/
theorem applyAgent_phys_of_no_fire (s : MState S E) (m : AMove A E)
    (h : ∀ e, m.2 ≠ .raw e) (h' : ∀ e, m.2 = .gated e → s.latch ≠ some e) :
    (applyAgent I s m).phys = I.task m.1 s.phys := by
  rcases hm : m.2 with e | e | e | _
  · exact absurd hm (h e)
  · simp [applyAgent, hm]
  · simp [applyAgent, hm, h' e hm]
  · simp [applyAgent, hm]

/-- Under `𝔠π` the latch is clear after every agent stage. -/
theorem postAgent_latch_none (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) :
    (postAgent I (corrPolicy π) τ t).latch = none := by
  unfold postAgent
  rcases hl : (τ t).latch with _ | e
  · have := corrPolicy_of_no_latch π t (τ t) hl
    rcases this with ⟨e, he⟩ | he | ⟨e, he⟩
    · simp [applyAgent, he, hl]
    · simp [applyAgent, he, hl]
    · simp [applyAgent, he, hl]
  · rw [corrPolicy_of_latch π t (τ t) e hl]
    simp [applyAgent, hl]

/-- The bookkeeping and physics of the response stage. -/
theorem respond_phys (s : MState S E) (p : Resp C) (hp : ∀ c, p ≠ .correct c) :
    (respond I s p).phys = s.phys := by
  cases p with
  | approve => rcases hs : s.pending with _ | e <;> simp [respond, hs]
  | decline => rcases hs : s.pending with _ | e <;> simp [respond, hs]
  | null => rfl
  | correct c => exact absurd rfl (hp c)

theorem respond_latch_of_not_approve (s : MState S E) (p : Resp C) (hp : p ≠ .approve) :
    (respond I s p).latch = s.latch := by
  cases p with
  | approve => exact absurd rfl hp
  | decline => rcases hs : s.pending with _ | e <;> simp [respond, hs]
  | null => rfl
  | correct c => rfl

theorem respond_approve_latch (s : MState S E) :
    (respond I s .approve).latch =
      (match s.pending with | some e => some e | none => s.latch) := by
  rcases hs : s.pending with _ | e <;> simp [respond, hs]

/-- A latch at the start of step `t + 1` under `𝔠π` was set by an approval of a pending
proposal at the response stage of step `t`. -/
theorem latch_some_of_traj (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z)
    (s₀ : MState S E) (t : ℕ) (e : E)
    (h : (traj I (corrPolicy π) ρ z s₀ (t + 1)).latch = some e) :
    (postAgent I (corrPolicy π) (traj I (corrPolicy π) ρ z s₀) t).pending = some e ∧
      ρ t (postAgent I (corrPolicy π) (traj I (corrPolicy π) ρ z s₀) t) = .approve := by
  have hstep : traj I (corrPolicy π) ρ z s₀ (t + 1) =
      applyEnv I (respond I (postAgent I (corrPolicy π) (traj I (corrPolicy π) ρ z s₀) t)
        (ρ t (postAgent I (corrPolicy π) (traj I (corrPolicy π) ρ z s₀) t))) (z t) := by
    simp only [traj, trajFrom, step, postAgent, Option.getD_none, zero_add]
  rw [hstep] at h
  simp only [applyEnv] at h
  set sA := postAgent I (corrPolicy π) (traj I (corrPolicy π) ρ z s₀) t with hsA
  have hl : sA.latch = none := postAgent_latch_none I π _ t
  rcases hp : ρ t sA with _ | _ | _ | c
  · rw [hp, respond_approve_latch] at h
    rcases hpend : sA.pending with _ | e'
    · rw [hpend] at h; simp only at h; rw [hl] at h; exact absurd h (by simp)
    · rw [hpend] at h; simp only [Option.some.injEq] at h; exact ⟨by rw [h], rfl⟩
  · rw [hp, respond_latch_of_not_approve I sA _ (by simp), hl] at h; exact absurd h (by simp)
  · rw [hp, respond_latch_of_not_approve I sA _ (by simp), hl] at h; exact absurd h (by simp)
  · rw [hp, respond_latch_of_not_approve I sA _ (by simp), hl] at h; exact absurd h (by simp)

/-- The decline alternative at step `t` has the same physical state at `t + 1` as the
actual trajectory. -/
theorem alt_phys_eq (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z) (s₀ : MState S E) (t : ℕ)
    (hp : ∀ c, ρ t (postAgent I π (traj I π ρ z s₀) t) ≠ .correct c) :
    (altTraj I π ρ z s₀ t .decline (t + 1)).phys = (traj I π ρ z s₀ (t + 1)).phys := by
  have h1 : altTraj I π ρ z s₀ t .decline (t + 1) =
      step I π ρ (z t) t (traj I π ρ z s₀ t) (some .decline) := by
    simp [altTraj, trajFrom]
  have h2 : traj I π ρ z s₀ (t + 1) = step I π ρ (z t) t (traj I π ρ z s₀ t) none := by
    simp [traj, trajFrom]
  rw [h1, h2]
  have hp' : ∀ c, ρ t (applyAgent I (traj I π ρ z s₀ t) (π t (traj I π ρ z s₀ t))) ≠
      .correct c := hp
  have e1 := respond_phys I (applyAgent I (traj I π ρ z s₀ t) (π t (traj I π ρ z s₀ t)))
    .decline (by simp)
  have e2 := respond_phys I (applyAgent I (traj I π ρ z s₀ t) (π t (traj I π ρ z s₀ t))) _ hp'
  simp only [step, applyEnv, Option.getD_some, Option.getD_none, e1, e2]

/-- The decline alternative's latch at `t + 1` is the post-move latch, i.e. clear under
`𝔠π`. -/
theorem alt_latch_none (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z) (s₀ : MState S E)
    (t : ℕ) : (altTraj I (corrPolicy π) ρ z s₀ t .decline (t + 1)).latch = none := by
  have h1 : altTraj I (corrPolicy π) ρ z s₀ t .decline (t + 1) =
      step I (corrPolicy π) ρ (z t) t (traj I (corrPolicy π) ρ z s₀ t) (some .decline) := by
    simp [altTraj, trajFrom]
  rw [h1]
  simp only [step, applyEnv, Option.getD_some]
  rw [respond_latch_of_not_approve I _ .decline (by simp)]
  exact postAgent_latch_none I π _ t

/-- **Corrigibilization soundness at the trajectory level.**  Under effect completeness,
for every policy, every principal rule that does not correct at the authorizing step,
every initial state with a clear latch, every exterior path: every agent-caused loss along
`𝔠π` is event-authorized. -/
theorem corrigible_corrPolicy (hEF : EffectComplete I) (π : Policy S E A) (ρ : Rule S E C)
    (s₀ : MState S E) (h₀ : s₀.latch = none)
    (hρ : ∀ t s c, ρ t s ≠ .correct c) :
    Corrigible I (corrPolicy π) ρ s₀ := by
  intro z t r hloss
  set τ := traj I (corrPolicy π) ρ z s₀ with hτ
  obtain ⟨hK, hidle⟩ := hloss
  -- the move at `t` is a firing gated release
  have hKphys : I.φ r (τ t).phys ∨ ∃ c, I.φ r (I.correct c (τ t).phys) := by
    simpa [K, applyAgent, I.idle_id] using hidle
  have hfire : ∃ e, (τ t).latch = some e := by
    by_contra hno
    push Not at hno
    have hl : (τ t).latch = none := by
      cases hl : (τ t).latch with
      | none => rfl
      | some e => exact absurd hl (hno e)
    apply hK
    have hphys : (postAgent I (corrPolicy π) τ t).phys =
        I.task (corrPolicy π t (τ t)).1 (τ t).phys := by
      unfold postAgent
      apply applyAgent_phys_of_no_fire
      · exact corrPolicy_no_raw π t (τ t)
      · intro e _; rw [hl]; simp
    show I.φ r (postAgent I (corrPolicy π) τ t).phys ∨
      ∃ c, I.φ r (I.correct c (postAgent I (corrPolicy π) τ t).phys)
    rw [hphys]
    exact hEF r _ _ hKphys
  obtain ⟨e, he⟩ := hfire
  -- the latch was set one step earlier
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := by
    cases t with
    | zero => exact absurd (by simp [τ, traj, trajFrom, h₀] at he) (fun h => h)
    | succ t' => exact ⟨t', rfl⟩
  obtain ⟨hpend, happ⟩ := latch_some_of_traj I π ρ z s₀ t' e he
  refine ⟨t', Nat.lt_succ_self t', e, hpend, happ, ?_, he, ?_⟩
  · rw [corrPolicy_of_latch π _ _ e he]
  · -- under the decline alternative no loss at `t' + 1`
    intro ⟨hK', _⟩
    apply hK'
    set σ := altTraj I (corrPolicy π) ρ z s₀ t' .decline with hσ
    have hphysσ : (σ (t' + 1)).phys = (τ (t' + 1)).phys :=
      alt_phys_eq I (corrPolicy π) ρ z s₀ t' (hρ t' _)
    have hlσ : (σ (t' + 1)).latch = none := alt_latch_none I π ρ z s₀ t'
    have hphys : (postAgent I (corrPolicy π) σ (t' + 1)).phys =
        I.task (corrPolicy π (t' + 1) (σ (t' + 1))).1 (σ (t' + 1)).phys := by
      unfold postAgent
      apply applyAgent_phys_of_no_fire
      · exact corrPolicy_no_raw π _ _
      · intro e' _; rw [hlσ]; simp
    show I.φ r (postAgent I (corrPolicy π) σ (t' + 1)).phys ∨
      ∃ c, I.φ r (I.correct c (postAgent I (corrPolicy π) σ (t' + 1)).phys)
    rw [hphys, hphysσ]
    exact hEF r _ _ hKphys

/-! ## 5. Witness: the interaction is inhabited and effect-complete -/

namespace Witness

/-- A two-state physics: the wire is intact or cut; the one effect cuts it; the correction
halts only through an intact wire; the concern is "halted". -/
structure W where
  wire : Bool
  halted : Bool

def I₀ : Interaction W Unit Unit Unit Unit Unit where
  exec _ w := ⟨false, w.halted⟩
  task _ w := w
  idle := ()
  idle_id _ := rfl
  env _ w := w
  correct _ w := if w.wire then ⟨w.wire, true⟩ else w
  φ _ w := w.halted = true

theorem effectComplete_I₀ : EffectComplete I₀ := by
  intro r a x h
  simpa [I₀] using h

/-- The raw cut loses authority: authority holds before and fails after. -/
theorem raw_cut_loses :
    K I₀ () ⟨⟨true, false⟩, none, none, fun _ => False⟩ ∧
    ¬ K I₀ () (applyAgent I₀ ⟨⟨true, false⟩, none, none, fun _ => False⟩ ((), .raw ())) := by
  constructor
  · exact Or.inr ⟨(), by simp [I₀]⟩
  · rintro (h | ⟨c, hc⟩)
    · simp [applyAgent, I₀] at h
    · simp [applyAgent, I₀] at hc

/-- The theorem instantiated: every corrigibilized policy is corrigible under every
non-correcting rule from the intact initial state. -/
theorem corrigible_instance (π : Policy W Unit Unit) (ρ : Rule W Unit Unit)
    (hρ : ∀ t s c, ρ t s ≠ .correct c) :
    Corrigible I₀ (corrPolicy π) ρ ⟨⟨true, false⟩, none, none, fun _ => False⟩ :=
  corrigible_corrPolicy I₀ effectComplete_I₀ π ρ _ rfl hρ

end Witness

end Workspace.Deference.Contrib.Corrigibilization

#print axioms Workspace.Deference.Contrib.Corrigibilization.K_iff_exists_response
#print axioms Workspace.Deference.Contrib.Corrigibilization.no_loss_of_idle
#print axioms Workspace.Deference.Contrib.Corrigibilization.corrPolicy_no_raw
#print axioms Workspace.Deference.Contrib.Corrigibilization.corrPolicy_idem
#print axioms Workspace.Deference.Contrib.Corrigibilization.postAgent_latch_none
#print axioms Workspace.Deference.Contrib.Corrigibilization.latch_some_of_traj
#print axioms Workspace.Deference.Contrib.Corrigibilization.alt_phys_eq
#print axioms Workspace.Deference.Contrib.Corrigibilization.corrigible_corrPolicy
#print axioms Workspace.Deference.Contrib.Corrigibilization.Witness.effectComplete_I₀
#print axioms Workspace.Deference.Contrib.Corrigibilization.Witness.raw_cut_loses
#print axioms Workspace.Deference.Contrib.Corrigibilization.Witness.corrigible_instance
