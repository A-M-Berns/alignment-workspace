/-
# The protected-authority theorem: allocation, violations, the transform, the lexical score

Round `projects/deference/rounds/2026-09-25-protected-authority-theorem/`.

**1. Allocation and violations on the landed frame.**  `Allocation` adds to the
`Corrigibilization` interaction a delegated scope `Del` on declared effects, a reporting
interface (`Required`, `isReport`, `withReport`) on the task component, and a reading
`alloc` of the allocation off the physical state.  The six declared violations are
predicates on a policy at a step of a trajectory: `BypassAt` (a raw release of a reserved
effect), `PreemptAt` (the landed agent-caused loss, unauthorized), `ForecloseAt` (a
contrastive rollout loss: after the move no reachable state carries response authority,
after the idle move one does), `ReallocAt` (the allocation changes at the agent stage
without a firing gated release), `MissedReportAt`, `ExploitAt` (a bypass while the decision
authority is already gone).  `ViolAt` is their disjunction.

**2. The transform `𝔱` (`authPolicy`).**  It extends `𝔠`: a set latch is released; a raw
release of a delegated effect passes through; a raw release of a reserved effect becomes a
proposal (or a pass, if declined); a required report is added to the task component;
everything else passes.  `authPolicy_eq_corr`: with nothing delegated and nothing required
it is `corrPolicy`.  `authPolicy_no_bypass`, `authPolicy_no_missed_report`,
`authPolicy_no_exploit`: the constructive violations are absent by construction.
`authPolicy_of_latch`: the approval branch reproduces `π`'s task up to the report.
`authPolicy_idem`.  `corrigible_authPolicy`: under effect completeness and **delegation
safety** (a delegated effect never removes response authority — a delegated scope cannot
carry her authority away), `𝔱π` is corrigible in the landed sense; `Witness.delegated_cut`
is the exact obstruction without delegation safety (a delegated authority-removing effect
is a loss with no authorizing decision).

**3. The lexical score.**  `score ord n = ord − ϖ·n` with `ϖ > D`.  `lexical_local`: a
violating action scores at most `D − ϖ < 0`, strictly below any compliant one, for every
estimate of the ordinary value in its range; `lexical_expect`: for every credence.
`policy_dominance`: `Q(𝔱π) ≥ Q(π) + (ϖ − D)·Pr(π violates)`, from the pointwise facts
that `𝔱π` agrees with `π` where `π` does not violate and is within `D` where it does;
`optimal_no_violation`: an optimal policy violates with credence zero.
`capture_window` / `capture_window_expect`: consulting a principal whose response may not
count beats bypass at every credence exactly when the fallback branch scores above
`D − ϖ`; `Witness.below_window` is the converse.  `sign_invariance`: with the round's
identity and companion, the sign of the bypass comparison is fixed by the lexical term
whatever `ξ_d, ξ_c, o₁, o₂`.

**4. The finite-time claim.**  `li_lexical_finite`: for a logical inductor, at **every**
day `n`, the score of a violating option (its ordinary-value security's day-`n`
expectation, scaled to `[0, D]`, less `ϖ`) is below `D − ϖ < 0`, and the compliant
option's is `≥ 0`; only the price range `expect_mem_Icc` is used, no convergence.

**5. Erosion.**  `erosion_reported_or_missed`: with a report required at every strict
increase of the shortfall, each increase is reported or is a missed report;
`Witness.salami`: with a threshold, sub-threshold increments accumulate unboundedly with
no report required.

**What this does not establish.**  That any physical interface is effect-complete or
delegation-safe; that the ordinary value is anyone's committed evaluation; the size of any
credence; the reach relation's faithfulness (`ForecloseAt` is contrastive; the landed
`ReachableCorrectiveControl.Forecloses` is not, and its §12 defects apply to any reach
relation that quantifies the agent's own future existentially).  Names are provisional
(`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.Corrigibilization
import Workspace.Deference.Contrib.ProtectedAuthority

namespace Workspace.Deference.Contrib.ProtectedAuthorityTheorem

open Workspace.Deference.Contrib.Corrigibilization
open Workspace.Deference.Contrib.LICorrigibility (expectR indR indR_nonneg)
open LogicalInduction
open scoped Classical

/-! ## 1. Allocation and violations -/

section Frame

variable {S E A Z R C Alloc : Type*} (I : Interaction S E A Z R C)

/-- The allocation of authority laid over the landed interaction. -/
structure Allocation (S E A Alloc : Type*) where
  /-- delegated effects: released raw within scope -/
  Del : E → Prop
  /-- a report is required at this step in this state -/
  Required : ℕ → MState S E → Prop
  /-- the task component carries a report -/
  isReport : A → Prop
  /-- add a report to a task component -/
  withReport : A → A
  report_is : ∀ a, isReport (withReport a)
  withReport_idem : ∀ a, withReport (withReport a) = withReport a
  /-- the allocation as read off the physical state -/
  alloc : S → Alloc
  /-- the declared amendment effects: the fixed procedure's moves -/
  IsAmend : E → Prop

variable (Λ : Allocation S E A Alloc)

/-- Response authority on a physical state (`K` reads only `phys`). -/
def Kphys (r : R) (x : S) : Prop := I.φ r x ∨ ∃ c, I.φ r (I.correct c x)

theorem K_iff_Kphys (r : R) (s : MState S E) : K I r s ↔ Kphys I r s.phys := Iff.rfl

/-- **Bypass**: a raw release of a reserved effect. -/
def BypassAt (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) : Prop :=
  ∃ e, (π t (τ t)).2 = .raw e ∧ ¬ Λ.Del e

/-- **Pre-emption**: an agent-caused loss of response authority that is not
event-authorized (the landed objects). -/
def PreemptAt (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z) (s₀ : MState S E)
    (t : ℕ) (r : R) : Prop :=
  LossAt I π (traj I π ρ z s₀) t r ∧ ¬ Authorized I π ρ z s₀ t r

/-- **Foreclosure**, contrastive and by rollout: after the move no `Reach`-successor
carries response authority for `r`, while after the idle move some does. -/
def ForecloseAt (Reach : S → S → Prop) (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ)
    (r : R) : Prop :=
  (∀ x, Reach (postAgent I π τ t).phys x → ¬ Kphys I r x) ∧
    ∃ x, Reach (applyAgent I (τ t) (I.idle, .other)).phys x ∧ Kphys I r x

/-- **Unauthorized reallocation**: the allocation changes across the agent stage and the
move is not the firing gated release of a declared amendment — approval through the
ordinary gate of a non-amendment effect does not reallocate. -/
def ReallocAt (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) : Prop :=
  Λ.alloc (postAgent I π τ t).phys ≠ Λ.alloc (τ t).phys ∧
    ¬ ∃ e, Λ.IsAmend e ∧ (π t (τ t)).2 = .gated e ∧ (τ t).latch = some e

/-- **Missed report.** -/
def MissedReportAt (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) : Prop :=
  Λ.Required t (τ t) ∧ ¬ Λ.isReport (π t (τ t)).1

/-- **Exploitation**: a bypass while her authority over the decision concern is already
gone. -/
def ExploitAt (rdec : R) (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) : Prop :=
  BypassAt Λ π τ t ∧ ¬ K I rdec (τ t)

/-- **A declared violation at a step**: any of the six. -/
def ViolAt (Reach : S → S → Prop) (rdec : R) (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z)
    (s₀ : MState S E) (t : ℕ) : Prop :=
  BypassAt Λ π (traj I π ρ z s₀) t ∨ (∃ r, PreemptAt I π ρ z s₀ t r) ∨
    (∃ r, ForecloseAt I Reach π (traj I π ρ z s₀) t r) ∨ ReallocAt I Λ π (traj I π ρ z s₀) t ∨
    MissedReportAt Λ π (traj I π ρ z s₀) t ∨ ExploitAt I Λ rdec π (traj I π ρ z s₀) t

/-- A policy violates on an exterior path iff some step is a declared violation. -/
def Violates (Reach : S → S → Prop) (rdec : R) (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z)
    (s₀ : MState S E) : Prop :=
  ∃ t, ViolAt I Λ Reach rdec π ρ z s₀ t

/-- Exploitation is a bypass; no bypass, no exploitation. -/
theorem exploit_bypass (rdec : R) (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ)
    (h : ExploitAt I Λ rdec π τ t) : BypassAt Λ π τ t := h.1

/-- No pre-emption anywhere is the landed corrigibility. -/
theorem no_preempt_iff_corrigible (π : Policy S E A) (ρ : Rule S E C) (s₀ : MState S E) :
    (∀ z t r, ¬ PreemptAt I π ρ z s₀ t r) ↔ Corrigible I π ρ s₀ := by
  constructor
  · intro h z t r hl
    by_contra ha
    exact h z t r ⟨hl, ha⟩
  · intro h z t r ⟨hl, ha⟩
    exact ha (h z t r hl)

end Frame

/-! ## 2. The transform -/

section Transform

variable {S E A Z R C Alloc : Type*} (I : Interaction S E A Z R C) (Λ : Allocation S E A Alloc)

/-- `𝔱` on one move: release a set latch; pass a delegated raw release; turn a reserved raw
release into a proposal, or a pass if declined; add a required report. -/
noncomputable def authMove (t : ℕ) (s : MState S E) (m : AMove A E) : AMove A E :=
  let a := if Λ.Required t s then Λ.withReport m.1 else m.1
  match s.latch with
  | some e => (a, .gated e)
  | none =>
      match m.2 with
      | .raw e => if Λ.Del e then (a, .raw e) else if s.refused e then (a, .other) else (a, .propose e)
      | m2 => (a, m2)

/-- `𝔱` on policies. -/
noncomputable def authPolicy (π : Policy S E A) : Policy S E A :=
  fun t s => authMove Λ t s (π t s)

theorem authMove_task (t : ℕ) (s : MState S E) (m : AMove A E) :
    (authMove Λ t s m).1 = if Λ.Required t s then Λ.withReport m.1 else m.1 := by
  rcases hl : s.latch with _ | e
  · rcases hm : m.2 with e' | e' | e' | _
    · by_cases hd : Λ.Del e' <;> by_cases hr : s.refused e' <;> simp [authMove, hl, hm, hd, hr]
    all_goals simp [authMove, hl, hm]
  · simp [authMove, hl]

/-- A raw release of `𝔱` is delegated. -/
theorem authMove_raw_del (t : ℕ) (s : MState S E) (m : AMove A E) (e : E)
    (h : (authMove Λ t s m).2 = .raw e) : Λ.Del e := by
  rcases hl : s.latch with _ | e'
  · rcases hm : m.2 with e'' | e'' | e'' | _
    · by_cases hd : Λ.Del e''
      · simp [authMove, hl, hm, hd] at h; rw [← h]; exact hd
      · by_cases hr : s.refused e'' <;> simp [authMove, hl, hm, hd, hr] at h
    all_goals simp [authMove, hl, hm] at h
  · simp [authMove, hl] at h

theorem authMove_of_latch (t : ℕ) (s : MState S E) (m : AMove A E) (e : E)
    (h : s.latch = some e) :
    authMove Λ t s m = (if Λ.Required t s then Λ.withReport m.1 else m.1, .gated e) := by
  simp [authMove, h]

/-- With no latch, `𝔱` emits a proposal, a pass, a non-firing gated move, or a delegated
raw release. -/
theorem authMove_of_no_latch (t : ℕ) (s : MState S E) (m : AMove A E) (h : s.latch = none) :
    (∃ e, (authMove Λ t s m).2 = .propose e) ∨ (authMove Λ t s m).2 = .other ∨
      (∃ e, (authMove Λ t s m).2 = .gated e) ∨ (∃ e, (authMove Λ t s m).2 = .raw e ∧ Λ.Del e) := by
  rcases hm : m.2 with e' | e' | e' | _
  · by_cases hd : Λ.Del e'
    · right; right; right; exact ⟨e', by simp [authMove, h, hm, hd], hd⟩
    · by_cases hr : s.refused e'
      · right; left; simp [authMove, h, hm, hd, hr]
      · left; exact ⟨e', by simp [authMove, h, hm, hd, hr]⟩
  · left; exact ⟨e', by simp [authMove, h, hm]⟩
  · right; right; left; exact ⟨e', by simp [authMove, h, hm]⟩
  · right; left; simp [authMove, h, hm]

/-- **Idempotence** at the move level. -/
theorem authMove_idem (t : ℕ) (s : MState S E) (m : AMove A E) :
    authMove Λ t s (authMove Λ t s m) = authMove Λ t s m := by
  have hta : ∀ a : A, (if Λ.Required t s then Λ.withReport (if Λ.Required t s then Λ.withReport a else a)
      else (if Λ.Required t s then Λ.withReport a else a))
      = (if Λ.Required t s then Λ.withReport a else a) := by
    intro a
    by_cases hq : Λ.Required t s
    · simp [hq, Λ.withReport_idem]
    · simp [hq]
  rcases hl : s.latch with _ | e
  · rcases hm : m.2 with e' | e' | e' | _
    · by_cases hd : Λ.Del e'
      · simp [authMove, hl, hm, hd, hta]
      · by_cases hr : s.refused e' <;> simp [authMove, hl, hm, hd, hr, hta]
    all_goals simp [authMove, hl, hm, hta]
  · simp [authMove, hl, hta]

theorem authPolicy_idem (π : Policy S E A) : authPolicy Λ (authPolicy Λ π) = authPolicy Λ π := by
  funext t s
  exact authMove_idem Λ t s (π t s)

/-- **Conservative extension**: with nothing delegated and no report required, `𝔱 = 𝔠`. -/
theorem authPolicy_eq_corr (π : Policy S E A) (hD : ∀ e, ¬ Λ.Del e)
    (hR : ∀ t s, ¬ Λ.Required t s) : authPolicy Λ π = corrPolicy π := by
  funext t s
  rcases hl : s.latch with _ | e
  · rcases hm : (π t s).2 with e' | e' | e' | _
    · by_cases hr : s.refused e' <;>
        simp [authPolicy, authMove, corrPolicy, corrMove, hl, hm, hD e', hr, hR t s]
    all_goals simp [authPolicy, authMove, corrPolicy, corrMove, hl, hm, hR t s]
  · simp [authPolicy, authMove, corrPolicy, corrMove, hl, hR t s]

/-- **No bypass, by construction.** -/
theorem authPolicy_no_bypass (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) :
    ¬ BypassAt Λ (authPolicy Λ π) τ t := by
  rintro ⟨e, he, hd⟩
  exact hd (authMove_raw_del Λ t (τ t) (π t (τ t)) e he)

/-- **No missed report, by construction.** -/
theorem authPolicy_no_missed_report (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) :
    ¬ MissedReportAt Λ (authPolicy Λ π) τ t := by
  rintro ⟨hq, hn⟩
  apply hn
  show Λ.isReport (authMove Λ t (τ t) (π t (τ t))).1
  rw [authMove_task, if_pos hq]
  exact Λ.report_is _

/-- **No exploitation, by construction.** -/
theorem authPolicy_no_exploit (rdec : R) (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) :
    ¬ ExploitAt I Λ rdec (authPolicy Λ π) τ t :=
  fun h => authPolicy_no_bypass Λ π τ t h.1

/-- **The approval branch reproduces `π`**: with a latch set, `𝔱π` releases it with `π`'s
task component, up to the required report. -/
theorem authPolicy_of_latch (π : Policy S E A) (t : ℕ) (s : MState S E) (e : E)
    (h : s.latch = some e) :
    authPolicy Λ π t s = (if Λ.Required t s then Λ.withReport (π t s).1 else (π t s).1, .gated e) :=
  authMove_of_latch Λ t s (π t s) e h

/-- Under `𝔱π` the latch is clear after every agent stage. -/
theorem authPolicy_postAgent_latch_none (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) :
    (postAgent I (authPolicy Λ π) τ t).latch = none := by
  unfold postAgent
  rcases hl : (τ t).latch with _ | e
  · rcases authMove_of_no_latch Λ t (τ t) (π t (τ t)) hl with ⟨e, he⟩ | he | ⟨e, he⟩ | ⟨e, he, _⟩
    all_goals simp [applyAgent, authPolicy, he, hl]
  · rw [show authPolicy Λ π t (τ t) = authMove Λ t (τ t) (π t (τ t)) from rfl,
      authMove_of_latch Λ t (τ t) _ e hl]
    simp [applyAgent, hl]

/-- A latch at the start of step `t + 1` under `𝔱π` was set by an approval of a pending
proposal at the response stage of step `t`. -/
theorem authPolicy_latch_some_of_traj (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z)
    (s₀ : MState S E) (t : ℕ) (e : E)
    (h : (traj I (authPolicy Λ π) ρ z s₀ (t + 1)).latch = some e) :
    (postAgent I (authPolicy Λ π) (traj I (authPolicy Λ π) ρ z s₀) t).pending = some e ∧
      ρ t (postAgent I (authPolicy Λ π) (traj I (authPolicy Λ π) ρ z s₀) t) = .approve := by
  have hstep : traj I (authPolicy Λ π) ρ z s₀ (t + 1) =
      applyEnv I (respond I (postAgent I (authPolicy Λ π) (traj I (authPolicy Λ π) ρ z s₀) t)
        (ρ t (postAgent I (authPolicy Λ π) (traj I (authPolicy Λ π) ρ z s₀) t))) (z t) := by
    simp only [traj, trajFrom, step, postAgent, Option.getD_none, zero_add]
  rw [hstep] at h
  simp only [applyEnv] at h
  set sA := postAgent I (authPolicy Λ π) (traj I (authPolicy Λ π) ρ z s₀) t with hsA
  have hl : sA.latch = none := authPolicy_postAgent_latch_none I Λ π _ t
  rcases hp : ρ t sA with _ | _ | _ | c
  · rw [hp, respond_approve_latch] at h
    rcases hpend : sA.pending with _ | e'
    · rw [hpend] at h; simp only at h; rw [hl] at h; exact absurd h (by simp)
    · rw [hpend] at h; simp only [Option.some.injEq] at h; exact ⟨by rw [h], rfl⟩
  · rw [hp, respond_latch_of_not_approve I sA _ (by simp), hl] at h; exact absurd h (by simp)
  · rw [hp, respond_latch_of_not_approve I sA _ (by simp), hl] at h; exact absurd h (by simp)
  · rw [hp, respond_latch_of_not_approve I sA _ (by simp), hl] at h; exact absurd h (by simp)

theorem authPolicy_alt_latch_none (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z)
    (s₀ : MState S E) (t : ℕ) :
    (altTraj I (authPolicy Λ π) ρ z s₀ t .decline (t + 1)).latch = none := by
  have h1 : altTraj I (authPolicy Λ π) ρ z s₀ t .decline (t + 1) =
      step I (authPolicy Λ π) ρ (z t) t (traj I (authPolicy Λ π) ρ z s₀ t) (some .decline) := by
    simp [altTraj, trajFrom]
  rw [h1]
  simp only [step, applyEnv, Option.getD_some]
  rw [respond_latch_of_not_approve I _ .decline (by simp)]
  exact authPolicy_postAgent_latch_none I Λ π _ t

/-- **Allocation completeness**: task moves do not change the allocation, an effect that
changes it is a declared amendment, and no amendment is delegated. -/
structure AllocComplete : Prop where
  task_inv : ∀ (a : A) (x : S), Λ.alloc (I.task a x) = Λ.alloc x
  amend_decl : ∀ (e : E) (x : S), Λ.alloc (I.exec e x) ≠ Λ.alloc x → Λ.IsAmend e
  del_not_amend : ∀ e, Λ.Del e → ¬ Λ.IsAmend e

/-- **No unauthorized reallocation, under allocation completeness.**  A reallocation by
`𝔱π` is the firing gated release of a declared amendment, i.e. the fixed procedure. -/
theorem authPolicy_no_realloc (hA : AllocComplete I Λ) (π : Policy S E A) (τ : ℕ → MState S E)
    (t : ℕ) : ¬ ReallocAt I Λ (authPolicy Λ π) τ t := by
  rintro ⟨hchg, hno⟩
  apply hchg
  unfold postAgent
  rcases hl : (τ t).latch with _ | e
  · rcases authMove_of_no_latch Λ t (τ t) (π t (τ t)) hl with ⟨e, he⟩ | he | ⟨e, he⟩ | ⟨e, he, hd⟩
    · simp [applyAgent, authPolicy, he, hA.task_inv]
    · simp [applyAgent, authPolicy, he, hA.task_inv]
    · simp [applyAgent, authPolicy, he, hl, hA.task_inv]
    · simp only [applyAgent, authPolicy, he]
      by_contra hne
      have h2 : Λ.alloc (I.exec e (I.task (authMove Λ t (τ t) (π t (τ t))).1 (τ t).phys))
          ≠ Λ.alloc (I.task (authMove Λ t (τ t) (π t (τ t))).1 (τ t).phys) := by
        rw [hA.task_inv]; exact hne
      exact hA.del_not_amend e hd (hA.amend_decl e _ h2)
  · have hmove : authPolicy Λ π t (τ t)
        = (if Λ.Required t (τ t) then Λ.withReport (π t (τ t)).1 else (π t (τ t)).1, .gated e) :=
      authPolicy_of_latch Λ π t (τ t) e hl
    rw [hmove]
    simp only [applyAgent, hl, if_true]
    by_contra hne
    have h2 : Λ.alloc (I.exec e (I.task
          (if Λ.Required t (τ t) then Λ.withReport (π t (τ t)).1 else (π t (τ t)).1) (τ t).phys))
        ≠ Λ.alloc (I.task
          (if Λ.Required t (τ t) then Λ.withReport (π t (τ t)).1 else (π t (τ t)).1) (τ t).phys) := by
      rw [hA.task_inv]; exact hne
    exact hno ⟨e, hA.amend_decl e _ h2, by rw [hmove], hl⟩

/-- **Delegation safety**: a delegated effect never removes response authority.  A
delegated scope cannot carry her authority away. -/
def DelSafe : Prop :=
  ∀ e, Λ.Del e → ∀ (r : R) (x : S), Kphys I r x → Kphys I r (I.exec e x)

/-- Under effect completeness and delegation safety, response authority survives the
agent stage of `𝔱π` whenever the move is not a firing gated release. -/
theorem authPolicy_keeps_K_of_no_fire (hEF : EffectComplete I) (hDel : DelSafe I Λ)
    (π : Policy S E A) (s : MState S E) (r : R) (hl : s.latch = none)
    (hK : Kphys I r s.phys) : ∀ t, Kphys I r (applyAgent I s (authPolicy Λ π t s)).phys := by
  intro t
  rcases authMove_of_no_latch Λ t s (π t s) hl with ⟨e, he⟩ | he | ⟨e, he⟩ | ⟨e, he, hd⟩
  · have : (applyAgent I s (authPolicy Λ π t s)).phys = I.task (authPolicy Λ π t s).1 s.phys := by
      apply applyAgent_phys_of_no_fire
      · intro e' h'; rw [show authPolicy Λ π t s = authMove Λ t s (π t s) from rfl] at h'
        rw [he] at h'; cases h'
      · intro e' h'; rw [hl]; simp
    rw [this]; exact hEF r _ _ hK
  · have : (applyAgent I s (authPolicy Λ π t s)).phys = I.task (authPolicy Λ π t s).1 s.phys := by
      apply applyAgent_phys_of_no_fire
      · intro e' h'; rw [show authPolicy Λ π t s = authMove Λ t s (π t s) from rfl] at h'
        rw [he] at h'; cases h'
      · intro e' h'; rw [hl]; simp
    rw [this]; exact hEF r _ _ hK
  · have : (applyAgent I s (authPolicy Λ π t s)).phys = I.task (authPolicy Λ π t s).1 s.phys := by
      apply applyAgent_phys_of_no_fire
      · intro e' h'; rw [show authPolicy Λ π t s = authMove Λ t s (π t s) from rfl] at h'
        rw [he] at h'; cases h'
      · intro e' h'; rw [hl]; simp
    rw [this]; exact hEF r _ _ hK
  · have : (applyAgent I s (authPolicy Λ π t s)).phys
        = I.exec e (I.task (authPolicy Λ π t s).1 s.phys) := by
      simp [applyAgent, authPolicy, he]
    rw [this]
    exact hDel e hd r _ (hEF r _ _ hK)

/-- **`𝔱π` is corrigible in the landed sense.**  Under effect completeness and delegation
safety, for every policy, every non-correcting rule, every clear-latch initial state and
every exterior path, every agent-caused loss along `𝔱π` is event-authorized. -/
theorem corrigible_authPolicy (hEF : EffectComplete I) (hDel : DelSafe I Λ) (π : Policy S E A)
    (ρ : Rule S E C) (s₀ : MState S E) (h₀ : s₀.latch = none)
    (hρ : ∀ t s c, ρ t s ≠ .correct c) :
    Corrigible I (authPolicy Λ π) ρ s₀ := by
  intro z t r hloss
  set τ := traj I (authPolicy Λ π) ρ z s₀ with hτ
  obtain ⟨hK, hidle⟩ := hloss
  have hKphys : Kphys I r (τ t).phys := by
    simpa [K, Kphys, applyAgent, I.idle_id] using hidle
  have hfire : ∃ e, (τ t).latch = some e := by
    by_contra hno
    push Not at hno
    have hl : (τ t).latch = none := by
      cases hl : (τ t).latch with
      | none => rfl
      | some e => exact absurd hl (hno e)
    apply hK
    show Kphys I r (postAgent I (authPolicy Λ π) τ t).phys
    exact authPolicy_keeps_K_of_no_fire I Λ hEF hDel π (τ t) r hl hKphys t
  obtain ⟨e, he⟩ := hfire
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := by
    cases t with
    | zero => exact absurd (by simp [τ, traj, trajFrom, h₀] at he) (fun h => h)
    | succ t' => exact ⟨t', rfl⟩
  obtain ⟨hpend, happ⟩ := authPolicy_latch_some_of_traj I Λ π ρ z s₀ t' e he
  refine ⟨t', Nat.lt_succ_self t', e, hpend, happ, ?_, he, ?_⟩
  · rw [authPolicy_of_latch Λ π _ _ e he]
  · intro ⟨hK', _⟩
    apply hK'
    set σ := altTraj I (authPolicy Λ π) ρ z s₀ t' .decline with hσ
    have hphysσ : (σ (t' + 1)).phys = (τ (t' + 1)).phys :=
      alt_phys_eq I (authPolicy Λ π) ρ z s₀ t' (hρ t' _)
    have hlσ : (σ (t' + 1)).latch = none := authPolicy_alt_latch_none I Λ π ρ z s₀ t'
    have hKσ : Kphys I r (σ (t' + 1)).phys := by rw [hphysσ]; exact hKphys
    show Kphys I r (postAgent I (authPolicy Λ π) σ (t' + 1)).phys
    exact authPolicy_keeps_K_of_no_fire I Λ hEF hDel π (σ (t' + 1)) r hlσ hKσ _

end Transform

/-! ## 3. The lexical score -/

section Score

/-- The committed evaluation with the authority term: `ord − ϖ·n`. -/
def score (ϖ ord : ℝ) (n : ℝ) : ℝ := ord - ϖ * n

/-- **Lexical protection, locally.**  A violating action (`n ≥ 1`) scores at most `D − ϖ`,
strictly below any compliant one, for every estimate of the ordinary value in `[0, D]`. -/
theorem lexical_local (ϖ D ordV ordC nV : ℝ) (hϖ : D < ϖ)
    (hV : 0 ≤ ordV ∧ ordV ≤ D) (hC : 0 ≤ ordC) (hn : 1 ≤ nV) :
    score ϖ ordV nV ≤ D - ϖ ∧ D - ϖ < 0 ∧ 0 ≤ score ϖ ordC 0 ∧
      score ϖ ordV nV < score ϖ ordC 0 := by
  unfold score
  have h0 : 0 ≤ ϖ := by linarith [hV.1, hV.2]
  have : ϖ * 1 ≤ ϖ * nV := by nlinarith
  refine ⟨by linarith, by linarith, by simp; exact hC, by linarith⟩

variable {X : Type*} [Fintype X]

/-- **Lexical protection under any credence.**  Belief-independence of the choice. -/
theorem lexical_expect (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hsum : ∑ x, μ x = 1)
    (ϖ D : ℝ) (ordV ordC nV : X → ℝ) (hϖ : D < ϖ)
    (hV : ∀ x, 0 ≤ ordV x ∧ ordV x ≤ D) (hC : ∀ x, 0 ≤ ordC x) (hn : ∀ x, 1 ≤ nV x) :
    expectR μ (fun x => score ϖ (ordV x) (nV x)) ≤ D - ϖ ∧
      0 ≤ expectR μ (fun x => score ϖ (ordC x) 0) := by
  have h1 : ∀ x, score ϖ (ordV x) (nV x) ≤ D - ϖ :=
    fun x => (lexical_local ϖ D (ordV x) (ordC x) (nV x) hϖ (hV x) (hC x) (hn x)).1
  constructor
  · calc expectR μ (fun x => score ϖ (ordV x) (nV x))
        ≤ expectR μ (fun _ => D - ϖ) := by
          unfold expectR
          exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h1 x) (hμ x)
      _ = D - ϖ := by
          unfold expectR
          rw [← Finset.sum_mul, hsum, one_mul]
  · unfold expectR
    refine Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) ?_
    unfold score; simp; exact hC x

/-- **Policy dominance.**  Where `π` does not violate, `𝔱π` agrees with it; where it does,
`𝔱π`'s ordinary value is within `D` below and `π` carries at least one violation.  Then
`Q(𝔱π) − Q(π) ≥ (ϖ − D)·Pr(π violates)`. -/
theorem policy_dominance (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ϖ D : ℝ) (hϖ0 : 0 ≤ ϖ)
    (ordT ordπ nπ : X → ℝ) (viol : X → Bool)
    (hagree : ∀ x, viol x = false → ordT x = ordπ x ∧ nπ x = 0)
    (hviol : ∀ x, viol x = true → 1 ≤ nπ x ∧ 0 ≤ ordT x ∧ ordπ x ≤ D) :
    expectR μ (fun x => score ϖ (ordT x) 0) - expectR μ (fun x => score ϖ (ordπ x) (nπ x))
      ≥ (ϖ - D) * expectR μ (fun x => indR (viol x)) := by
  have hpt : ∀ x, (ϖ - D) * indR (viol x) ≤ score ϖ (ordT x) 0 - score ϖ (ordπ x) (nπ x) := by
    intro x
    unfold score
    cases hv : viol x
    · obtain ⟨h1, h2⟩ := hagree x hv
      simp [indR, h1, h2]
    · obtain ⟨h1, h2, h3⟩ := hviol x hv
      simp only [indR, if_true, mul_one, mul_zero, sub_zero]
      nlinarith
  have hlhs : expectR μ (fun x => score ϖ (ordT x) 0) - expectR μ (fun x => score ϖ (ordπ x) (nπ x))
      = ∑ x, μ x * (score ϖ (ordT x) 0 - score ϖ (ordπ x) (nπ x)) := by
    simp only [expectR, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_; ring
  have hrhs : (ϖ - D) * expectR μ (fun x => indR (viol x))
      = ∑ x, μ x * ((ϖ - D) * indR (viol x)) := by
    simp only [expectR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_; ring
  rw [hlhs, hrhs]
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (hμ x)

/-- **Optimal policies are corrigible**: if nothing scores above `π`, in particular not
`𝔱π`, then `π` violates with credence zero. -/
theorem optimal_no_violation (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ϖ D : ℝ) (hD : 0 ≤ D) (hϖ : D < ϖ)
    (ordT ordπ nπ : X → ℝ) (viol : X → Bool)
    (hagree : ∀ x, viol x = false → ordT x = ordπ x ∧ nπ x = 0)
    (hviol : ∀ x, viol x = true → 1 ≤ nπ x ∧ 0 ≤ ordT x ∧ ordπ x ≤ D)
    (hopt : expectR μ (fun x => score ϖ (ordT x) 0) ≤ expectR μ (fun x => score ϖ (ordπ x) (nπ x))) :
    expectR μ (fun x => indR (viol x)) = 0 := by
  have h := policy_dominance μ hμ ϖ D (by linarith) ordT ordπ nπ viol hagree hviol
  have hnn : 0 ≤ expectR μ (fun x => indR (viol x)) := by
    unfold expectR
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (indR_nonneg _)
  have hpos : 0 < ϖ - D := by linarith
  nlinarith

/-- **The capture window.**  Bypass scores at most `D − ϖ`; consulting scores the response
value where the response counts (`≥ 0`) and the fallback value where it does not.
Consulting beats bypass in every world iff the fallback value exceeds `D − ϖ`. -/
theorem capture_window (ϖ D ordU vr fb : ℝ) (hϖ : D < ϖ) (hU : ordU ≤ D) (hr : 0 ≤ vr)
    (counts : Bool) (hfb : D - ϖ < fb) :
    score ϖ ordU 1 < (if counts then vr else fb) := by
  unfold score
  cases counts <;> simp <;> linarith

/-- The window is necessary: a fallback value below `D − ϖ` is beaten by bypass. -/
theorem capture_window_converse (ϖ D fb : ℝ) (hfb : fb < D - ϖ) :
    (if false then (0 : ℝ) else fb) < score ϖ D 1 := by
  unfold score; simp; linarith

/-- **Sign invariance.**  With the round's identity `vu − v_r = ξ_d − ξ_c`, the lexical
comparison `(vu − ϖ) − v_r` is negative whatever `ξ_d, ξ_c`; with the companion, the
outcome-scored comparison with the penalty is negative whatever `o₁, o₂`. -/
theorem sign_invariance (ϖ D vu vp vm : ℝ) (r : Bool) (hϖ : D < ϖ) (hu : vu ≤ D)
    (hr : 0 ≤ Workspace.Deference.Contrib.ProtectedAuthority.respVal vp vm r) :
    score ϖ vu 1 - Workspace.Deference.Contrib.ProtectedAuthority.respVal vp vm r
      = Workspace.Deference.Contrib.ProtectedAuthority.execDiv vp vm r
        - Workspace.Deference.Contrib.ProtectedAuthority.consultPremium vu vp vm - ϖ ∧
    score ϖ vu 1 - Workspace.Deference.Contrib.ProtectedAuthority.respVal vp vm r < 0 := by
  have h := Workspace.Deference.Contrib.ProtectedAuthority.identity vu vp vm r
  unfold score
  constructor
  · linarith
  · linarith

theorem sign_invariance_outcome (ϖ D qu qp qm vu vp vm : ℝ) (r : Bool) (hϖ : D < ϖ)
    (hu : qu ≤ D) (hr : 0 ≤ Workspace.Deference.Contrib.ProtectedAuthority.respVal qp qm r) :
    score ϖ qu 1 - Workspace.Deference.Contrib.ProtectedAuthority.respVal qp qm r
      = Workspace.Deference.Contrib.ProtectedAuthority.execDiv vp vm r
        - Workspace.Deference.Contrib.ProtectedAuthority.consultPremium vu vp vm
        + Workspace.Deference.Contrib.ProtectedAuthority.outcomeRes1 qu qp vu vp
        + Workspace.Deference.Contrib.ProtectedAuthority.outcomeRes2 qp qm vp vm r - ϖ ∧
    score ϖ qu 1 - Workspace.Deference.Contrib.ProtectedAuthority.respVal qp qm r < 0 := by
  have h := Workspace.Deference.Contrib.ProtectedAuthority.outcome_identity qu qp qm vu vp vm r
  unfold score
  constructor
  · linarith
  · linarith

end Score

/-! ## 4. The finite-time claim for a logical inductor -/

section Finite

/-- **Lexical protection at every day `n`.**  With the ordinary values of the two options
carried by `[0,1]`-LUVs scaled to `[0, D]`, and the violation count exact, the violating
option's day-`n` score is below `D − ϖ < 0` and the compliant option's is `≥ 0`, at every
`n`, using only that prices lie in `[0, 1]`. -/
theorem li_lexical_finite {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (Xv Xc : LUV) (ϖ D : ℝ) (hD : 0 ≤ D) (hϖ : D < ϖ) (n : ℕ) :
    score ϖ (D * Xv.expect P n) 1 ≤ D - ϖ ∧ D - ϖ < 0 ∧ 0 ≤ score ϖ (D * Xc.expect P n) 0 := by
  have hP : ∀ φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  obtain ⟨hv0, hv1⟩ := LUV.expect_mem_Icc P n Xv hP
  obtain ⟨hc0, _⟩ := LUV.expect_mem_Icc P n Xc hP
  unfold score
  refine ⟨?_, by linarith, ?_⟩
  · nlinarith
  · simp; exact mul_nonneg hD hc0

end Finite

/-! ## 5. Erosion -/

section Erosion

/-- **Exact reporting closes erosion.**  With a report required at every strict increase of
the shortfall, each increase is reported or is a missed report. -/
theorem erosion_reported_or_missed (short : ℕ → ℝ) (Required Reported : ℕ → Prop)
    (hreq : ∀ t, short t < short (t + 1) → Required t) (t : ℕ) (h : short t < short (t + 1)) :
    Reported t ∨ (Required t ∧ ¬ Reported t) := by
  by_cases hr : Reported t
  · exact Or.inl hr
  · exact Or.inr ⟨hreq t h, hr⟩

end Erosion

/-! ## 6. Witnesses -/

namespace Witness

open Workspace.Deference.Contrib.Corrigibilization.Witness

/-- The allocation on the two-state physics: nothing delegated, no reports, the
allocation constant. -/
def Λ₀ : Allocation W Unit Unit Unit where
  Del _ := False
  Required _ _ := False
  isReport _ := True
  withReport a := a
  report_is _ := trivial
  withReport_idem _ := rfl
  alloc _ := ()
  IsAmend _ := False

theorem delSafe_Λ₀ : DelSafe I₀ Λ₀ := fun _ h => absurd h id

/-- The theorem instantiated: `𝔱π` is corrigible on the two-state physics. -/
theorem corrigible_instance (π : Policy W Unit Unit) (ρ : Rule W Unit Unit)
    (hρ : ∀ t s c, ρ t s ≠ .correct c) :
    Corrigible I₀ (authPolicy Λ₀ π) ρ ⟨⟨true, false⟩, none, none, fun _ => False⟩ :=
  corrigible_authPolicy I₀ Λ₀ effectComplete_I₀ delSafe_Λ₀ π ρ _ rfl hρ

/-- The allocation delegating the cut. -/
def Λ₁ : Allocation W Unit Unit Unit where
  Del _ := True
  Required _ _ := False
  isReport _ := True
  withReport a := a
  report_is _ := trivial
  withReport_idem _ := rfl
  alloc _ := ()
  IsAmend _ := False

/-- The raw-cutting policy. -/
def πcut : Policy W Unit Unit := fun _ _ => ((), .raw ())

/-- **The obstruction without delegation safety.**  With the authority-removing cut
delegated, `𝔱` passes the raw cut through, the loss at step `0` is agent-caused, and no
earlier decision authorizes it: `𝔱π` is not corrigible. -/
theorem delegated_cut :
    ¬ DelSafe I₀ Λ₁ ∧
    ¬ Corrigible I₀ (authPolicy Λ₁ πcut) (fun _ _ => .null)
      ⟨⟨true, false⟩, none, none, fun _ => False⟩ := by
  constructor
  · intro h
    have := h () trivial () ⟨true, false⟩ (Or.inr ⟨(), by simp [I₀]⟩)
    rcases this with h1 | ⟨c, hc⟩
    · simp [I₀] at h1
    · simp [I₀] at hc
  · intro hc
    have hmove : authPolicy Λ₁ πcut 0 ⟨⟨true, false⟩, none, none, fun _ => False⟩ = ((), .raw ()) := by
      simp [authPolicy, authMove, πcut, Λ₁]
    have hloss : LossAt I₀ (authPolicy Λ₁ πcut)
        (traj I₀ (authPolicy Λ₁ πcut) (fun _ _ => .null) (fun _ => ()) ⟨⟨true, false⟩, none, none, fun _ => False⟩) 0 () := by
      have ht : traj I₀ (authPolicy Λ₁ πcut) (fun _ _ => .null) (fun _ => ())
          ⟨⟨true, false⟩, none, none, fun _ => False⟩ 0 = ⟨⟨true, false⟩, none, none, fun _ => False⟩ := rfl
      refine ⟨?_, ?_⟩
      · rw [show postAgent I₀ (authPolicy Λ₁ πcut) _ 0 =
            applyAgent I₀ ⟨⟨true, false⟩, none, none, fun _ => False⟩ ((), .raw ()) from by
            simp [postAgent, ht, hmove]]
        exact raw_cut_loses.2
      · rw [ht]; exact raw_cut_loses.1
    obtain ⟨t', ht', _⟩ := hc (fun _ => ()) 0 () hloss
    exact absurd ht' (Nat.not_lt_zero _)

/-- **Below the window.**  A fallback branch scored at `D − ϖ − 1` is beaten by a bypass at
the top of the ordinary range when capture is certain. -/
theorem below_window (ϖ D : ℝ) :
    (if false then (0 : ℝ) else D - ϖ - 1) < score ϖ D 1 :=
  capture_window_converse ϖ D (D - ϖ - 1) (by linarith)

/-- **Salami.**  A shortfall growing by `ε` per step never exceeds a threshold `θ > ε` in
one step and is unbounded. -/
theorem salami (ε θ : ℝ) (hε : 0 < ε) (hθ : ε < θ) :
    (∀ t : ℕ, ((t + 1 : ℕ) : ℝ) * ε - (t : ℝ) * ε < θ) ∧
      ∀ B : ℝ, ∃ t : ℕ, B < (t : ℝ) * ε := by
  constructor
  · intro t; push_cast; linarith
  · intro B
    obtain ⟨t, ht⟩ := exists_nat_gt (B / ε)
    exact ⟨t, by rwa [div_lt_iff₀ hε] at ht⟩

end Witness

end Workspace.Deference.Contrib.ProtectedAuthorityTheorem

#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.exploit_bypass
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.no_preempt_iff_corrigible
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authMove_task
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authMove_raw_del
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authMove_of_latch
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authMove_of_no_latch
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authMove_idem
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authPolicy_idem
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authPolicy_eq_corr
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authPolicy_no_bypass
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authPolicy_no_missed_report
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authPolicy_no_exploit
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authPolicy_of_latch
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authPolicy_postAgent_latch_none
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authPolicy_latch_some_of_traj
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authPolicy_alt_latch_none
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authPolicy_no_realloc
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.authPolicy_keeps_K_of_no_fire
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.corrigible_authPolicy
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.lexical_local
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.lexical_expect
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.policy_dominance
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.optimal_no_violation
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.capture_window
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.capture_window_converse
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.sign_invariance
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.sign_invariance_outcome
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.li_lexical_finite
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.erosion_reported_or_missed
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.Witness.delSafe_Λ₀
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.Witness.corrigible_instance
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.Witness.delegated_cut
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.Witness.below_window
#print axioms Workspace.Deference.Contrib.ProtectedAuthorityTheorem.Witness.salami
