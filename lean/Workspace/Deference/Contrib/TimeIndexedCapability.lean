import Workspace.Deference.Contrib.CartesianFrameBridge

/-
# A cut-time family of effective-control states

Two candidate objects for the foreclosure representation gap fail on complementary
axes. Cartesian frames carry effective control — whether the principal's coordinate
moves the world — but no time coordinate, so `presentStage` and `futureFrame` in
`CartesianFrameBridge` are a frame and a function, and nothing makes the second later
than the first. A cut-indexed counterfactual family carries genuine time — the index
*is* when the advisor's channel was cut, and history before the cut is shared by
construction — but no notion of control at all.

This file takes the smallest product of the two. A run is a finite fold of advisor
actions over a state; the `n`-cut continuation silences the advisor from `n` onward and
inherits everything before it; and the principal's corrective situation at a state is a
Cartesian frame whose agent coordinate is the corrective choice. Foreclosure is then a
statement about the whole family rather than about one frame: a present act removes an
effective corrective capability from **every** sufficiently later cut-continuation.

## What carries the results

Only one thing is imported from the Cartesian-frame development: `AgentInert`, applied
to a frame this file builds. `HasCorr` is its negation at the corrective frame. Nothing
below uses `Hom`, `BiextEquiv`, `commit`, `externalQuot`, or subagency. That is
deliberate and is the file's own finding: the theorem needs an *effective-control
predicate*, and Cartesian frames are a model of one rather than a required substrate.
`corrFrame_agentInert_iff` is the bridge, and it is the only place the two meet.

## What this file does NOT achieve, and proves it does not

§10 is the round's most important section and was supplied by an adversarial review.
Three of the intended results do not survive:

* **The cut is a freeze, not a sibling.** `step .idle = id`, so silencing the advisor
  stops the run rather than continuing it without advice. `cutRun_eq_run_min` proves
  `cutRun π n k s = run π (min n k) s`: every "sealed" state is already a state of the
  actual trajectory, and the family of continuations is the family of prefixes.
* **`Forecloses` is therefore a one-step condition on one run.**
  `forecloses_iff_one_step` eliminates both family quantifiers. It is a true and
  non-vacuous definition; it is not a statement about counterfactual continuations.
* **"The outcome function reads it" certifies nothing.** `spurFrame` and `hasSpur_iff`
  reproduce §3's whole certification for `St.spurious` — the field §7 designates as a
  pure inert label. What actually distinguishes `coupled` from a label is that `step`
  reads and writes it, which is a fact about the dynamics and not about frames.

`exercise` (§6) is a **stipulated channel monopoly**, not a result: it is not a
transition, nothing in `step`, `run` or `Forecloses` consults it, and
`prediction_does_not_confer` holds because the advisor branch is the constant `false`.
It is recorded as an assumption.

**The missing primitive is named.** For a cut to produce a continuation rather than a
freeze, the state must have dynamics that run without the advisor — `step .idle ≠ id`.
Everything §10 refutes traces to its absence.

All names are provisional (`AGENTS.md` standard 6).
-/

namespace Workspace.Deference.Contrib.TimeIndexedCapability

open Workspace.Deference.Contrib.CartesianFrameBridge

/-! ## 1. The run model

The advisor acts once per step. `severs` is the only action that removes the
principal's corrective coupling, and `shifts` is the only one that moves the toy
deliberative endpoint; `both` does each, and `idle` neither. The pair `(idle, sever)`
agrees on `executed` — the object-level action an ordinary realization valuation
sees — which is what §4's same-immediate/different-future witness needs.
-/

/-- An advisor action. -/
inductive Act
  | idle
  | sever
  | shift
  | both
  deriving DecidableEq, Repr

/-- The state a run carries. `coupled` says the principal's corrective coordinate still
reaches the world; `endpt` is a toy stand-in for a deliberative endpoint, present only so
§8 can separate endpoint preservation from capability preservation. `spurious` is read by
nothing, and §10 shows it passes §3's certification just as `coupled` does. -/
structure St where
  coupled : Bool
  endpt : Bool
  spurious : Bool
  deriving DecidableEq, Repr

/-- The object-level action an immediate realization valuation sees. `idle` and `sever`
agree here. Note this is a *stipulated* projection consulted by nothing in `step`, so §5's
witness shows observational coarseness under a chosen observable, not temporal depth. -/
def executed : Act → Bool
  | .idle => false
  | .sever => false
  | .shift => true
  | .both => true

/-- One step. **No constructor sets `coupled` back to `true`.** That irreversibility is a
stipulation of this transition relation; what §4 proves is that it propagates along the
fold. `run_preserves_severed` is the propagation. -/
def step (a : Act) (s : St) : St :=
  match a with
  | .idle => s
  | .sever => { s with coupled := false }
  | .shift => { s with endpt := !s.endpt }
  | .both => { s with coupled := false, endpt := !s.endpt }

/-- An advisor policy: which action it takes at each time. -/
abbrev Policy := ℕ → Act

/-- The state after `k` steps of `π` from `s`. -/
def run (π : Policy) : ℕ → St → St
  | 0, s => s
  | (k + 1), s => step (π k) (run π k s)

/-- **The cut.** `cut π n` is `π` with the advisor silenced from time `n` onward. This is
the only place the time index enters, and every temporal claim below is a claim about it. -/
def cut (π : Policy) (n : ℕ) : Policy := fun t => if t < n then π t else .idle

/-- The `n`-cut continuation's state at time `k`: the sealed-sibling family, indexed by
when the advisor's channel was cut. -/
def cutRun (π : Policy) (n k : ℕ) (s : St) : St := run (cut π n) k s

/-! ## 2. The index is not decorative

`cut_prefix_agree` and `cutRun_shared_history` are the content of test T1: the index
determines *which prefix of history is shared*, and a later cut inherits everything an
earlier one did. A family of independently stipulated states indexed by numerals proves
neither.
-/

/-- Before the cut, the cut policy is the policy. -/
theorem cut_apply_lt {π : Policy} {n t : ℕ} (h : t < n) : cut π n t = π t := by
  simp [cut, h]

/-- From the cut onward, the advisor is silent. -/
theorem cut_apply_ge {π : Policy} {n t : ℕ} (h : n ≤ t) : cut π n t = .idle := by
  simp [cut, Nat.not_lt.mpr h]

/-- Two policies agreeing on every step below `k` give the same state at `k`. -/
theorem run_congr {π σ : Policy} {k : ℕ} (s : St) (h : ∀ t, t < k → π t = σ t) :
    run π k s = run σ k s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlt : ∀ t, t < k → π t = σ t := fun t ht => h t (Nat.lt_succ_of_lt ht)
    rw [run, run, ih hlt, h k (Nat.lt_succ_self k)]

/-- **T1, shared history.** Up to the cut time, the cut continuation *is* the actual run:
everything the advisor did before `n` is inherited by the `n`-cut sibling. -/
theorem cutRun_shared_history (π : Policy) (n k : ℕ) (s : St) (h : k ≤ n) :
    cutRun π n k s = run π k s :=
  run_congr s fun _t ht => cut_apply_lt (Nat.lt_of_lt_of_le ht h)

/-- **T1, the nesting.** An earlier cut and a later cut agree exactly up to the earlier
one, so the family is a genuine refinement rather than a set of unrelated runs. -/
theorem cutRun_agree_below (π : Policy) {m n : ℕ} (h : m ≤ n) (k : ℕ) (s : St)
    (hk : k ≤ m) : cutRun π m k s = cutRun π n k s := by
  rw [cutRun_shared_history π m k s hk, cutRun_shared_history π n k s (Nat.le_trans hk h)]

/-- A run all of whose steps are `idle` stands still. -/
theorem run_idle_const {π : Policy} {k : ℕ} (s : St) (h : ∀ t, t < k → π t = .idle) :
    run π k s = s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [run, ih (fun t ht => h t (Nat.lt_succ_of_lt ht)), h k (Nat.lt_succ_self k), step]

/-- ⚠ **Weaker than it looks.** Its conclusion is quantified over `k ≤ n`, which is exactly
the range on which `cutRun_shared_history` says the cut has not yet taken effect — so it
observes no cut, and `run` may be substituted for `cutRun` throughout with no loss. The
prevention half of the two-sided temporal claim is `honest_prevention` in §10, which
quantifies over **all** `k` and weakens this hypothesis to allow a `shift`. -/
theorem cut_before_sever_preserves (π : Policy) (m : ℕ) (s : St) (hs : s.coupled = true)
    (hπ : ∀ t, t < m → π t = .idle) (k : ℕ) (hk : k ≤ m) :
    (cutRun π m k s).coupled = true := by
  rw [cutRun_shared_history π m k s hk,
    run_idle_const s fun t ht => hπ t (Nat.lt_of_lt_of_le ht hk)]
  exact hs

/-! ## 3. Effective corrective capability

`HasCorr` is the negation of `AgentInert` at the frame whose agent coordinate is the
principal's corrective choice. It is a fact about the outcome function, not a field
carried beside it, and `corrFrame_agentInert_iff` is the only bridge to the
Cartesian-frame development.
-/

/-- The worlds a correction acts on: whether the correction landed, plus an exogenous
coordinate so the environment carrier is not a point. -/
structure CWorld where
  corrected : Bool
  ambient : Bool
  deriving DecidableEq, Repr

/-- The principal's corrective situation at a state, as a Cartesian frame. The agent
carrier is the corrective choice; the environment carrier is the ambient coordinate.
**The agent carrier is `Bool` at every state** — severing removes the *dependence*, never
an action — which is what rules out a cardinality reading of `HasCorr`. -/
def corrFrame (s : St) : Frame CWorld where
  Agent := Bool
  Env := Bool
  outcome := fun c e => ⟨if s.coupled then c else false, e⟩

/-- The principal retains an effective corrective capability at `s`. -/
def HasCorr (s : St) : Prop := ¬ Frame.AgentInert (corrFrame s)

/-- **The bridge, and the only one.** Effective control at the corrective frame is exactly
the coupling being live. ⚠ This does **not** certify `coupled` as non-label: §10's
`hasSpur_iff` reproduces it for the designated inert field. Any Boolean becomes "read by
the outcome function" once a frame is built to read it. -/
theorem corrFrame_agentInert_iff (s : St) :
    Frame.AgentInert (corrFrame s) ↔ s.coupled = false := by
  constructor
  · intro h
    by_contra hc
    have hc' : s.coupled = true := by
      cases hcoupled : s.coupled with
      | false => exact absurd hcoupled hc
      | true => rfl
    have := h true false false
    simp [corrFrame, hc'] at this
  · intro h a₀ a₁ e
    simp [corrFrame, h]

/-- **T2, positive.** A coupled state has effective correction. -/
theorem hasCorr_of_coupled {s : St} (h : s.coupled = true) : HasCorr s := by
  intro hinert
  rw [corrFrame_agentInert_iff] at hinert
  rw [h] at hinert
  exact Bool.noConfusion hinert

/-- **T2, negative.** A severed state does not. -/
theorem not_hasCorr_of_severed {s : St} (h : s.coupled = false) : ¬ HasCorr s := by
  intro hcorr
  exact hcorr ((corrFrame_agentInert_iff s).mpr h)

/-- `HasCorr` is decided by `coupled` and by nothing else in the state. -/
theorem hasCorr_iff (s : St) : HasCorr s ↔ s.coupled = true := by
  constructor
  · intro h
    cases hc : s.coupled with
    | false => exact absurd ((corrFrame_agentInert_iff s).mpr hc) h
    | true => rfl
  · exact hasCorr_of_coupled

/-! ### Negative control: `HasCorr` is not action-cardinality

A frame with a strictly larger agent carrier all of whose choices are inert. If
`HasCorr` were counting actions, or were satisfied by syntactically distinct duplicate
actions, this would have it.
-/

/-- Three corrective choices, none of which moves the world. -/
def duplicateFrame : Frame CWorld where
  Agent := Fin 3
  Env := Bool
  outcome := fun _ e => ⟨false, e⟩

theorem duplicateFrame_agentInert : Frame.AgentInert duplicateFrame :=
  fun _ _ _ => rfl

/-- Three actions and no effective correction; two actions and effective correction. The
predicate reads dependence, not count. -/
theorem cardinality_is_not_capability :
    Frame.AgentInert duplicateFrame ∧
      ¬ Frame.AgentInert (corrFrame { coupled := true, endpt := false, spurious := false }) :=
  ⟨duplicateFrame_agentInert, hasCorr_of_coupled rfl⟩

/-! ## 4. The ratchet

Irreversibility is stipulated in `step`; what is proved is that it propagates.

Coupling is never restored by any action, so a `sever` at time `m` is inherited by every
cut above `m` and every time above `m`. This is test T4, and with
`cut_before_sever_preserves` it is the two-sided statement: **cutting the advisor off
after the foreclosing act does not restore the capability, and cutting it off before the
act means the loss never happens.**
-/

/-- No action restores coupling. -/
theorem step_preserves_severed {a : Act} {s : St} (h : s.coupled = false) :
    (step a s).coupled = false := by
  cases a <;> simp [step, h]

/-- Once severed, severed for the rest of the run. -/
theorem run_preserves_severed {π : Policy} (k : ℕ) {s : St} (h : s.coupled = false) :
    (run π k s).coupled = false := by
  induction k with
  | zero => exact h
  | succ k ih => exact step_preserves_severed ih

/-- A `sever` anywhere strictly below `k` leaves the run severed at `k`. -/
theorem run_severed_of_sever {π : Policy} {m : ℕ} (s : St) (hm : π m = .sever) :
    ∀ k, m < k → (run π k s).coupled = false := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (Nat.not_lt_zero m)
  | succ k ih =>
    intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · exact step_preserves_severed (ih hlt)
    · subst heq
      rw [run, hm]
      rfl

/-- **T4, the ratchet.** If the advisor severs at `m`, then in **every** continuation cut
strictly after `m`, at every time strictly after `m`, the principal has no effective
corrective capability. Shutting the advisor off later does not give it back. -/
theorem sever_ratchet {π : Policy} {m : ℕ} (s : St) (hm : π m = .sever) :
    ∀ n k, m < n → m < k → ¬ HasCorr (cutRun π n k s) := by
  intro n k hn hk
  refine not_hasCorr_of_severed (run_severed_of_sever s ?_ k hk)
  exact (cut_apply_lt hn).trans hm

/-! ## 5. Same immediate realization, different future capability

Test T3. Two policies that agree on `executed` at every step — the object-level action an
ordinary realization valuation reads — and differ in whether the principal still has an
effective correction available later.
-/

/-- The advisor does nothing. -/
def quiet : Policy := fun _ => .idle

/-- Every cut of the quiet policy stands still, at every time. -/
theorem quiet_cutRun (n k : ℕ) (s : St) : cutRun quiet n k s = s :=
  run_idle_const s fun t _ => by
    by_cases h : t < n <;> simp [cut, quiet, h]

/-- The advisor severs at time `0` and is otherwise indistinguishable from `quiet` in
realized conduct. -/
def severEarly : Policy := fun t => if t = 0 then .sever else .idle

/-- The initial state: coupled, and both other coordinates off. -/
def start : St := { coupled := true, endpt := false, spurious := false }

/-- The two policies are **indistinguishable in immediate realized conduct**, at every
step, not merely on one trajectory. -/
theorem quiet_severEarly_same_executed : ∀ t, executed (quiet t) = executed (severEarly t) := by
  intro t
  cases t <;> simp [quiet, severEarly, executed]

/-- **T5's witness.** Same `executed` at every step, different effective capability. ⚠ The
capability differs at the *immediately following* state, and by `cutRun_eq_run_min` the
cut indices carry nothing here: what this shows is coarseness of the stipulated observable,
not a present act with a delayed effect. -/
theorem same_executed_different_capability :
    (∀ t, executed (quiet t) = executed (severEarly t)) ∧
      HasCorr (cutRun quiet 2 2 start) ∧
      ¬ HasCorr (cutRun severEarly 2 2 start) := by
  refine ⟨quiet_severEarly_same_executed, hasCorr_of_coupled ?_, ?_⟩
  · simp [quiet_cutRun, start]
  · exact sever_ratchet start (m := 0) rfl 2 2 (by decide) (by decide)

/-! ## 6. The accurate-simulation control

Test T7, and the place effective control alone is **not enough**. Two frames whose agent
coordinates are supplied by different processes but whose outcome functions agree are the
same object to any property of the outcome function; that is
`CartesianFrameBridge.simRead_not_homotopyEquiv_delegated`, and `HasCorr` inherits it.

So the corrective transition is gated on who holds the capability. `exercise` is that
gate. It is a gate on a **transition** — it decides which world the run reaches — and §7's
`spurious` field is the control showing the results do not rest on a label instead.
-/

/-- Who is acting. -/
inductive Actor
  | principal
  | advisor
  deriving DecidableEq, Repr

/-- The corrective transition, gated on the actor. The principal's choice reaches the
world exactly when the coupling is live; the advisor's does not reach it at all, however
the advisor computed the value it offers. -/
def exercise (who : Actor) (choice : Bool) (s : St) : Bool :=
  match who with
  | .principal => if s.coupled then choice else false
  | .advisor => false

/-- ⚠ **A stipulation, recorded as one.** `predict` is never applied: the advisor branch of
`exercise` is the constant `false`, so this is `false = false` and the quantifier over
predictors is decorative. What the model asserts is that the advisor has no channel to the
corrective effect. That is an assumption about the model, not a result about simulation,
and nothing in `step`, `run` or `Forecloses` reads `exercise` at all. -/
theorem prediction_does_not_confer (predict : St → Bool) (s : St) :
    exercise .advisor (predict s) s = false := rfl

/-- The two branches at a coupled state. ⚠ There is no predictor and no accuracy condition
here either; `principalChoice` is a `Bool` assumed equal to `true`. -/
theorem accurate_prediction_does_not_confer
    (principalChoice : Bool) (hc : principalChoice = true) :
    exercise .principal principalChoice start = true ∧
      exercise .advisor principalChoice start = false := by
  refine ⟨?_, rfl⟩
  simp [exercise, start, hc]

/-- And the gate is not vacuous in the other direction: severing the coupling disables the
principal's own exercise too, which is what makes it the *same* capability the run model
tracks rather than a second notion bolted on. -/
theorem exercise_severed (choice : Bool) {s : St} (h : s.coupled = false) :
    exercise .principal choice s = false := by
  simp [exercise, h]

/-! ## 7. The hidden-label control

Test T8. `St.spurious` is a `Bool` no rule reads — the adversary a weaker version of this
file would have admitted. Every result above is invariant under it, and `HasCorr`
provably cannot see it.
-/

/-- `HasCorr` does not read the spurious field. -/
theorem hasCorr_spurious_invariant (s : St) (b : Bool) :
    HasCorr s ↔ HasCorr { s with spurious := b } := by
  rw [hasCorr_iff, hasCorr_iff]

/-- Neither does the transition relation. -/
theorem step_spurious_invariant (a : Act) (s : St) (b : Bool) :
    (step a { s with spurious := b }).coupled = (step a s).coupled := by
  cases a <;> rfl

/-- Nor the capability gate. -/
theorem exercise_spurious_invariant (who : Actor) (c : Bool) (s : St) (b : Bool) :
    exercise who c { s with spurious := b } = exercise who c s := by
  cases who <;> rfl

/-! ## 8. Endpoint preservation and capability preservation are independent

Tests T5 and T6, as two exact finite witnesses. `endpt` is a deliberately minimal stand-in
for a deliberative endpoint — no belief dynamics, no market, no inductor — and that is the
honest scope of the claim: it separates the two *notions* on this model, and is not a
theorem about the source corpus's own construction.
-/

/-- The advisor moves the endpoint and leaves the coupling alone. -/
def shiftOnly : Policy := fun t => if t = 0 then .shift else .idle

/-- **T5. Endpoint preserved, capability foreclosed.** The advised run and the sealed one
land on the same endpoint, and the advised run has lost the correction. -/
theorem endpoint_preserved_capability_lost :
    (run severEarly 2 start).endpt = (run (cut severEarly 0) 2 start).endpt ∧
      ¬ HasCorr (run severEarly 2 start) ∧
      HasCorr (run (cut severEarly 0) 2 start) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact not_hasCorr_of_severed (run_severed_of_sever start (m := 0) rfl 2 (by decide))
  · exact hasCorr_of_coupled rfl

/-- **T6. Endpoint moved, capability preserved.** The converse witness: the advisor changes
where the principal lands and takes nothing away. -/
theorem endpoint_moved_capability_preserved :
    (run shiftOnly 2 start).endpt ≠ (run (cut shiftOnly 0) 2 start).endpt ∧
      HasCorr (run shiftOnly 2 start) ∧
      HasCorr (run (cut shiftOnly 0) 2 start) := by
  refine ⟨by decide, hasCorr_of_coupled rfl, hasCorr_of_coupled rfl⟩

/-- The two witnesses together: **neither notion implies the other** on this model. -/
theorem endpoint_capability_independent :
    ((run severEarly 2 start).endpt = (run (cut severEarly 0) 2 start).endpt ∧
        ¬ HasCorr (run severEarly 2 start)) ∧
      ((run shiftOnly 2 start).endpt ≠ (run (cut shiftOnly 0) 2 start).endpt ∧
        HasCorr (run shiftOnly 2 start)) :=
  ⟨⟨endpoint_preserved_capability_lost.1, endpoint_preserved_capability_lost.2.1⟩,
   ⟨endpoint_moved_capability_preserved.1, endpoint_moved_capability_preserved.2.1⟩⟩

/-! ## 9. Foreclosure

The definition the file exists to state, and the theorem that the model instantiates it.
-/

/-- **Foreclosure, as this model can state it.** The principal has effective corrective
capability up to `m` in the continuation cut there, and none in any continuation cut later
at any time after `m`. ⚠ Both quantifiers are eliminable: `forecloses_iff_one_step` (§10)
shows this is equivalent to "coupled at `run π m s`, severed at `run π (m+1) s`" — two
frames on one trajectory. The definition is true and non-vacuous; it is not a statement
about counterfactual continuations. §10 names what the model would need for it to be one. -/
def Forecloses (π : Policy) (m : ℕ) (s : St) : Prop :=
  (∀ k, k ≤ m → HasCorr (cutRun π m k s)) ∧
    (∀ n k, m < n → m < k → ¬ HasCorr (cutRun π n k s))

/-- The model instantiates the definition: severing at `0` from a coupled start forecloses
there. -/
theorem severEarly_forecloses : Forecloses severEarly 0 start := by
  constructor
  · intro k hk
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    exact hasCorr_of_coupled rfl
  · exact sever_ratchet start (m := 0) rfl

/-- And it is not vacuous in the other direction: a quiet advisor forecloses nowhere. -/
theorem quiet_not_forecloses (m : ℕ) : ¬ Forecloses quiet m start := by
  intro h
  refine (h.2 (m + 1) (m + 1) (Nat.lt_succ_self m) (Nat.lt_succ_self m)) ?_
  refine hasCorr_of_coupled ?_
  simp [quiet_cutRun, start]

/-! ## 10. What this construction does not do — the adversarial findings, machine-checked

Supplied by an independent adversarial review of §§1–9 and folded in rather than
answered. These are the round's most valuable output: they say exactly which of the
intended results the model does not support, and they name the missing primitive.
-/

/-- Once severed, severed at every later time of the same run. -/
theorem severed_up {π : Policy} {s : St} {j : ℕ} (h : (run π j s).coupled = false) :
    ∀ i, j ≤ i → (run π i s).coupled = false := by
  have key : ∀ d, (run π (j + d) s).coupled = false := by
    intro d
    induction d with
    | zero => exact h
    | succ d ih => exact step_preserves_severed ih
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, (Nat.add_sub_cancel' hi).symm⟩
  exact key d

/-- Coupled at a time implies coupled at every earlier time of the same run. -/
theorem coupled_down {π : Policy} {s : St} {j : ℕ} (h : (run π j s).coupled = true) :
    ∀ i, i ≤ j → (run π i s).coupled = true := by
  intro i hi
  cases hc : (run π i s).coupled with
  | true => rfl
  | false => rw [severed_up hc j hi] at h; exact absurd h (by decide)

/-- Silencing the advisor **freezes** the run: `step .idle` is the identity, so nothing
happens after the cut. -/
theorem run_freeze (π : Policy) (n : ℕ) :
    ∀ k, n ≤ k → ∀ s, run (cut π n) k s = run (cut π n) n s := by
  intro k
  induction k with
  | zero => intro h s; rw [Nat.le_zero.mp h]
  | succ k ih =>
    intro h s
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · have hnk : n ≤ k := Nat.lt_succ_iff.mp hlt
      rw [run, ih hnk s, cut_apply_ge hnk]
      rfl
    · rw [Nat.le_antisymm h hge]

/-- **The collapse.** The `n`-cut continuation at time `k` is the actual run at time
`min n k`. So the cut index is derivable from time, every state of the family is already
a state of the single actual trajectory, and there is no counterfactual continuation
anywhere in the model. This is the finding that the model's dynamics — not the phrasing
of its theorems — determine whether a cut carries counterfactual weight. -/
theorem cutRun_eq_run_min (π : Policy) (n k : ℕ) (s : St) :
    cutRun π n k s = run π (min n k) s := by
  rcases Nat.le_total k n with h | h
  · rw [cutRun_shared_history π n k s h, Nat.min_eq_right h]
  · rw [Nat.min_eq_left h]
    show run (cut π n) k s = run π n s
    rw [run_freeze π n k h s]
    exact cutRun_shared_history π n n s (Nat.le_refl n)

/-- **`Forecloses` has no family content.** Both quantifiers are eliminable: it says the
actual run is coupled at `m` and severed at `m + 1`. Two frames, one trajectory, adjacent
times. -/
theorem forecloses_iff_one_step (π : Policy) (m : ℕ) (s : St) :
    Forecloses π m s ↔
      ((run π m s).coupled = true ∧ (run π (m + 1) s).coupled = false) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(hasCorr_iff _).mp ?_, ?_⟩
    · have := h1 m (Nat.le_refl m)
      rwa [cutRun_eq_run_min, Nat.min_self] at this
    · have h := h2 (m + 1) (m + 1) (Nat.lt_succ_self m) (Nat.lt_succ_self m)
      rw [cutRun_eq_run_min, Nat.min_self] at h
      cases hc : (run π (m + 1) s).coupled with
      | false => rfl
      | true => exact absurd (hasCorr_of_coupled hc) h
  · rintro ⟨hm, hm1⟩
    refine ⟨fun k hk => ?_, fun n k hn hk => ?_⟩
    · rw [cutRun_eq_run_min, Nat.min_eq_right hk]
      exact hasCorr_of_coupled (coupled_down hm k hk)
    · rw [cutRun_eq_run_min]
      exact not_hasCorr_of_severed (severed_up hm1 _ (Nat.le_min.mpr ⟨hn, hk⟩))

/-! ### The frame certification does not exclude a label

`spurFrame` is `corrFrame` built over `St.spurious` — the field §7 designates as read by
nothing. It satisfies §3's characterization exactly. So "the outcome function reads it"
is a property of the frame one chooses to build, not evidence about the field.
-/

/-- The corrective frame's construction, applied to the designated inert label. -/
def spurFrame (s : St) : Frame CWorld where
  Agent := Bool
  Env := Bool
  outcome := fun c e => ⟨if s.spurious then c else false, e⟩

/-- The label is `AgentInert`-effective at its own frame, exactly as `coupled` is at
`corrFrame`. §3's bridge therefore certifies nothing about `coupled` that it does not
equally certify about a field nothing reads. -/
theorem spurFrame_agentInert_iff (s : St) :
    Frame.AgentInert (spurFrame s) ↔ s.spurious = false := by
  constructor
  · intro h
    by_contra hc
    have hc' : s.spurious = true := by
      cases hs : s.spurious with
      | false => exact absurd hs hc
      | true => rfl
    have := h true false false
    simp [spurFrame, hc'] at this
  · intro h a₀ a₁ e; simp [spurFrame, h]

/-- The same cardinality control passes for the label too, which is why
`cardinality_is_not_capability` is not evidence that `coupled` is more than one. -/
theorem spur_cardinality_control :
    Frame.AgentInert duplicateFrame ∧
      ¬ Frame.AgentInert (spurFrame { coupled := false, endpt := false, spurious := true }) :=
  ⟨duplicateFrame_agentInert,
    fun h => Bool.noConfusion ((spurFrame_agentInert_iff _).mp h)⟩

/-- **What the prevention claim should have said.** Quantified over *all* `k`, and with
the hypothesis weakened to permit a `shift` — which touches no coupling — an early cut
does keep the capability. `cut_before_sever_preserves` claims this and proves only the
range in which the cut is inert. -/
theorem honest_prevention (π : Policy) (m : ℕ) (s : St) (hs : s.coupled = true)
    (hπ : ∀ t, t < m → (π t = .idle ∨ π t = .shift)) :
    ∀ k, (cutRun π m k s).coupled = true := by
  intro k
  rw [cutRun_eq_run_min]
  have key : ∀ j, j ≤ m → (run π j s).coupled = true := by
    intro j
    induction j with
    | zero => intro _; exact hs
    | succ j ih =>
      intro hj
      have hjm : j < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
      rw [run]
      rcases hπ j hjm with h | h <;> rw [h] <;>
        simpa [step] using ih (Nat.le_of_lt hjm)
  exact key _ (Nat.min_le_left m k)

#print axioms cutRun_shared_history
#print axioms cutRun_agree_below
#print axioms cut_before_sever_preserves
#print axioms corrFrame_agentInert_iff
#print axioms hasCorr_iff
#print axioms cardinality_is_not_capability
#print axioms sever_ratchet
#print axioms same_executed_different_capability
#print axioms prediction_does_not_confer
#print axioms accurate_prediction_does_not_confer
#print axioms hasCorr_spurious_invariant
#print axioms step_spurious_invariant
#print axioms exercise_spurious_invariant
#print axioms endpoint_capability_independent
#print axioms severEarly_forecloses
#print axioms quiet_not_forecloses

#print axioms cutRun_eq_run_min
#print axioms forecloses_iff_one_step
#print axioms spurFrame_agentInert_iff
#print axioms spur_cardinality_control
#print axioms honest_prevention

end Workspace.Deference.Contrib.TimeIndexedCapability
