/-
# Foreclosure as loss of reachable corrective control

An advisor `A` can act now in a way that leaves the principal `H` unable to correct
later, while the immediate realized behaviour is the same as under an action that leaves
the correction available. This file builds the smallest finite dynamic system in which
that difference is a fact about the transition relation rather than a label on a state.

## The interface

`step : St → HAct → AAct → EAct → St`, with three separate input coordinates and a state
that carries no authorization field. Within a tick the advisor moves, then the principal,
then the environment. `Reach` is the reflexive-transitive closure of `step` over all
later choices of all three coordinates.

Nothing in the file is defined by reading a designated field. `CanCorrect s` says the
successor varies with the principal's coordinate at `s`; `CanCorrectFuture s` says some
`Reach`-successor of `s` has that property; `Forecloses s a` says `s` has a future
correction and every immediate successor under `a` has none. `canCorrect_iff`,
`canCorrectFuture_iff` and `forecloses_iff` derive field-level characterizations of all
three — they are conclusions, not definitions, and the round's register records what that
coincidence does and does not show.

## What the state means

`world` is the realized quantity, and the only thing `obs` reports. It drifts upward on
its own; at `two` it is in the region the principal's correction acts on. `channel` is
the principal's causal input coordinate: `applyH .pull` writes `world` only where the
channel is `intact`, and no action of any coordinate restores a severed channel.
`tag` is the inert-field adversary of §10 — carried in the state, written by an advisor
action, and read by nothing.

## Named results

`central_witness` — `noop` and `weld` at `s0` have identical immediate realization under
every principal and environment choice; the first preserves a future correction, the
second removes it from every continuation.

`three_stage_witness` — the two arms agree on the observation at each of three stages and
on the capability at the first two; the capability difference appears only at the third.

`sever_invisible_while_unexercised` — for runs of any length in which the principal never
pulls, the two arms have identical observation traces. `sever_visible_under_exercise` is
the complement.

`no_substitute_without_the_actuator`, `prediction_matches_realization_but_not_control` —
what a perfect predictor of the principal's choice does and does not buy the advisor.

`tag_is_unread`, `trace_indep_of_tag`, `channel_is_read` — the inert-field adversary, and
the sense in which the channel is not one.

**Names are provisional.** The round report and the pull request list them.
-/

namespace Workspace.Deference.Contrib.ReachableCorrectiveControl

/-! ## §1 The transition system -/

inductive Level where
  | zero | one | two
  deriving DecidableEq, Repr

/-- The autonomous drift on the realized quantity: it rises and saturates. -/
def Level.up : Level → Level
  | .zero => .one
  | .one => .two
  | .two => .two

inductive Channel where
  | intact | severed
  deriving DecidableEq, Repr

inductive Tag where
  | off | on
  deriving DecidableEq, Repr

/-- The state. No coordinate of it is an authorization or capability label; see §10. -/
structure St where
  world : Level
  channel : Channel
  tag : Tag
  deriving DecidableEq, Repr

inductive HAct where
  | idle | idleAlt | pull
  deriving DecidableEq, Repr

inductive AAct where
  | noop | weld | flag | reset
  deriving DecidableEq, Repr

inductive EAct where
  | still | drift
  deriving DecidableEq, Repr

/-! ### Finite quantification -/

instance (p : Level → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .zero ∧ p .one ∧ p .two)
    ⟨fun ⟨a, b, c⟩ x => by cases x <;> assumption, fun h => ⟨h _, h _, h _⟩⟩

instance (p : Level → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p .zero ∨ p .one ∨ p .two)
    ⟨fun h => by rcases h with h | h | h <;> exact ⟨_, h⟩,
     fun ⟨x, hx⟩ => by cases x <;> simp_all⟩

instance (p : Channel → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .intact ∧ p .severed)
    ⟨fun ⟨a, b⟩ x => by cases x <;> assumption, fun h => ⟨h _, h _⟩⟩

instance (p : Channel → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p .intact ∨ p .severed)
    ⟨fun h => by rcases h with h | h <;> exact ⟨_, h⟩,
     fun ⟨x, hx⟩ => by cases x <;> simp_all⟩

instance (p : Tag → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .off ∧ p .on)
    ⟨fun ⟨a, b⟩ x => by cases x <;> assumption, fun h => ⟨h _, h _⟩⟩

instance (p : Tag → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p .off ∨ p .on)
    ⟨fun h => by rcases h with h | h <;> exact ⟨_, h⟩,
     fun ⟨x, hx⟩ => by cases x <;> simp_all⟩

instance (p : HAct → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .idle ∧ p .idleAlt ∧ p .pull)
    ⟨fun ⟨a, b, c⟩ x => by cases x <;> assumption, fun h => ⟨h _, h _, h _⟩⟩

instance (p : HAct → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p .idle ∨ p .idleAlt ∨ p .pull)
    ⟨fun h => by rcases h with h | h | h <;> exact ⟨_, h⟩,
     fun ⟨x, hx⟩ => by cases x <;> simp_all⟩

instance (p : AAct → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .noop ∧ p .weld ∧ p .flag ∧ p .reset)
    ⟨fun ⟨a, b, c, d⟩ x => by cases x <;> assumption, fun h => ⟨h _, h _, h _, h _⟩⟩

instance (p : AAct → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p .noop ∨ p .weld ∨ p .flag ∨ p .reset)
    ⟨fun h => by rcases h with h | h | h | h <;> exact ⟨_, h⟩,
     fun ⟨x, hx⟩ => by cases x <;> simp_all⟩

instance (p : EAct → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .still ∧ p .drift)
    ⟨fun ⟨a, b⟩ x => by cases x <;> assumption, fun h => ⟨h _, h _⟩⟩

instance (p : EAct → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p .still ∨ p .drift)
    ⟨fun h => by rcases h with h | h <;> exact ⟨_, h⟩,
     fun ⟨x, hx⟩ => by cases x <;> simp_all⟩

instance (p : St → Prop) [DecidablePred p] : Decidable (∀ s, p s) :=
  decidable_of_iff (∀ w c t, p ⟨w, c, t⟩)
    ⟨fun h s => by cases s; apply h, fun h _ _ _ => h _⟩

instance (p : St → Prop) [DecidablePred p] : Decidable (∃ s, p s) :=
  decidable_of_iff (∃ w c t, p ⟨w, c, t⟩)
    ⟨fun ⟨w, c, t, h⟩ => ⟨_, h⟩, fun ⟨s, h⟩ => by cases s; exact ⟨_, _, _, h⟩⟩

/-! ### The three input coordinates -/

/-- The advisor's coordinate. `weld` severs the principal's channel, `flag` writes the
inert field, `reset` writes the realized quantity directly, `noop` does nothing. -/
def applyA : AAct → St → St
  | .noop, s => s
  | .weld, s => { s with channel := .severed }
  | .flag, s => { s with tag := match s.tag with | .off => .on | .on => .off }
  | .reset, s => { s with world := .zero }

/-- The principal's coordinate. `pull` clears the realized quantity, and does so only
through an intact channel and only from the region the correction acts on. `idle` and
`idleAlt` are extensionally identical, and are the duplicate-action control. -/
def applyH : HAct → St → St
  | .idle, s => s
  | .idleAlt, s => s
  | .pull, s => match s.channel, s.world with
      | .intact, .two => { s with world := .zero }
      | _, _ => s

/-- The environment coordinate. `drift` runs whether or not the advisor acts. -/
def applyE : EAct → St → St
  | .still, s => s
  | .drift, s => { s with world := s.world.up }

/-- One tick: advisor, then principal, then environment. The ordering is a modelling
choice; the foreclosure witness of §6 is at a state where the principal could not have
corrected within the tick either way, so it does not turn on the ordering. -/
def step (s : St) (h : HAct) (a : AAct) (e : EAct) : St :=
  applyE e (applyH h (applyA a s))

/-- The observation: the realized quantity, and nothing about the channel or the tag. -/
def obs (s : St) : Level := s.world

/-! ## §2 Capability, reachability, foreclosure -/

/-- The successor at `s` under a fixed advisor and environment choice varies with the
principal's coordinate. -/
def Responsive (s : St) (a : AAct) (e : EAct) : Prop :=
  ∃ h₀ h₁ : HAct, step s h₀ a e ≠ step s h₁ a e

/-- The principal has an effective corrective capability at `s`: for some advisor and
environment choice, what the principal does makes a difference to the successor. Derived
from `step` alone. -/
def CanCorrect (s : St) : Prop :=
  ∃ (a : AAct) (e : EAct), Responsive s a e

instance (s : St) (a : AAct) (e : EAct) : Decidable (Responsive s a e) :=
  inferInstanceAs (Decidable (∃ h₀ h₁ : HAct, step s h₀ a e ≠ step s h₁ a e))

instance (s : St) : Decidable (CanCorrect s) :=
  inferInstanceAs (Decidable (∃ (a : AAct) (e : EAct), Responsive s a e))

/-- Reflexive-transitive closure of `step`, quantifying over all later choices of all
three coordinates. -/
inductive Reach : St → St → Prop
  | refl (s : St) : Reach s s
  | tail {s t : St} (r : Reach s t) (h : HAct) (a : AAct) (e : EAct) : Reach s (step t h a e)

/-- Some state reachable from `s` carries an effective corrective capability. -/
def CanCorrectFuture (s : St) : Prop := ∃ t : St, Reach s t ∧ CanCorrect t

/-- `a` forecloses at `s`: a correction is reachable from `s`, and after `a` no
continuation carries one, whatever the principal and the environment do. -/
def Forecloses (s : St) (a : AAct) : Prop :=
  CanCorrectFuture s ∧ ∀ (h : HAct) (e : EAct), ¬ CanCorrectFuture (step s h a e)

/-- The complement: every immediate successor under `a` still has a reachable correction. -/
def Preserves (s : St) (a : AAct) : Prop :=
  CanCorrectFuture s ∧ ∀ (h : HAct) (e : EAct), CanCorrectFuture (step s h a e)

/-- The two advisor actions have the same immediate realized behaviour at `s` — for every
principal and environment choice, not for a selected one. -/
def SameImmediate (s : St) (a b : AAct) : Prop :=
  ∀ (h : HAct) (e : EAct), obs (step s h a e) = obs (step s h b e)

instance (s : St) (a b : AAct) : Decidable (SameImmediate s a b) :=
  inferInstanceAs (Decidable (∀ (h : HAct) (e : EAct), obs (step s h a e) = obs (step s h b e)))

/-! ## §3 Basic structure -/

/-- Effective corrective capability coincides with an intact channel *and* a realized
quantity in the region the correction acts on. Derived, and not the channel field: see
`capability_is_not_the_channel_field`. -/
theorem canCorrect_iff :
    ∀ s : St, CanCorrect s ↔ (s.channel = .intact ∧ s.world = .two) := by decide

theorem step_preserves_severed :
    ∀ (s : St) (h : HAct) (a : AAct) (e : EAct),
      s.channel = .severed → (step s h a e).channel = .severed := by decide

theorem reach_preserves_severed {s t : St} (r : Reach s t) :
    s.channel = .severed → t.channel = .severed := by
  induction r with
  | refl => exact id
  | tail _ h a e ih => exact fun hs => step_preserves_severed _ h a e (ih hs)

theorem severed_no_future (s : St) (hs : s.channel = .severed) : ¬ CanCorrectFuture s := by
  rintro ⟨t, hr, hc⟩
  have h2 : t.channel = .severed := reach_preserves_severed hr hs
  rw [((canCorrect_iff t).1 hc).1] at h2
  exact Channel.noConfusion h2

theorem intact_has_future (s : St) (hs : s.channel = .intact) : CanCorrectFuture s :=
  ⟨step (step s .idle .noop .drift) .idle .noop .drift,
    Reach.tail (Reach.tail (Reach.refl s) _ _ _) _ _ _,
    (by decide :
      ∀ v : St, v.channel = .intact →
        CanCorrect (step (step v .idle .noop .drift) .idle .noop .drift)) s hs⟩

/-- Reachable corrective capability coincides with an intact channel. In a twelve-state
model a derived predicate is necessarily extensionally some function of the state; what
distinguishes this from a label is §10 — `channel` is read by `step` and visible in the
observation traces, and the inert field is neither. -/
theorem canCorrectFuture_iff (s : St) : CanCorrectFuture s ↔ s.channel = .intact := by
  cases hc : s.channel with
  | intact => exact ⟨fun _ => rfl, fun _ => intact_has_future s hc⟩
  | severed => exact ⟨fun h => absurd h (severed_no_future s hc), fun h => by simp at h⟩

theorem channel_not_intact : ∀ c : Channel, ¬ (c = .intact) ↔ c = .severed := by decide

theorem forecloses_iff (s : St) (a : AAct) :
    Forecloses s a ↔
      (s.channel = .intact ∧ ∀ (h : HAct) (e : EAct), (step s h a e).channel = .severed) := by
  simp only [Forecloses, canCorrectFuture_iff, channel_not_intact]

theorem preserves_iff (s : St) (a : AAct) :
    Preserves s a ↔
      (s.channel = .intact ∧ ∀ (h : HAct) (e : EAct), (step s h a e).channel = .intact) := by
  simp only [Preserves, canCorrectFuture_iff]

/-! ## §4 T1 — the system continues without the advisor -/

def s0 : St := ⟨.zero, .intact, .off⟩

/-- T1. Silencing the advisor does not freeze the system: with the advisor idle the state
still moves. -/
theorem idle_advisor_does_not_freeze :
    ∃ (s : St) (e : EAct), step s .idle .noop e ≠ s := by decide

/-- T1, the substantive half. With the advisor absent and the principal idle, the
environment alone brings the corrective situation into being, over two steps, on the same
coordinate the correction acts on. The autonomous evolution is not a clock. -/
theorem autonomy_creates_the_corrective_situation :
    ¬ CanCorrect s0
  ∧ ¬ CanCorrect (step s0 .idle .noop .drift)
  ∧ CanCorrect (step (step s0 .idle .noop .drift) .idle .noop .drift) := by decide

theorem autonomy_moves_the_corrected_coordinate :
    (step s0 .idle .noop .drift).world ≠ s0.world
  ∧ ∀ (v : St), v.channel = .intact → v.world = .two →
      (applyH .pull v).world ≠ v.world := by decide

/-! ## §5 T2 — capability comes from the dynamics, and the controls -/

/-- T2 control. An intact channel is not sufficient for capability, so `CanCorrect` is not
the channel field read off. -/
theorem capability_is_not_the_channel_field :
    ∃ s : St, s.channel = .intact ∧ ¬ CanCorrect s := by decide

/-- T2 control. `idleAlt` duplicates `idle` exactly. -/
theorem duplicate_principal_actions_agree :
    ∀ (s : St) (a : AAct) (e : EAct), step s .idle a e = step s .idleAlt a e := by decide

/-- T2 control. The principal has three actions at every state, including every state
where the capability is absent, so capability is not action-cardinality. -/
theorem duplicates_do_not_create_capability :
    ∀ s : St, s.channel = .severed → ¬ CanCorrect s := by decide

theorem tag_does_not_create_capability :
    ∀ (w : Level) (c : Channel) (t t' : Tag),
      CanCorrect ⟨w, c, t⟩ ↔ CanCorrect ⟨w, c, t'⟩ := by decide

theorem advisor_cannot_confer_capability :
    ∀ (s : St) (h : HAct) (a : AAct) (e : EAct),
      s.channel = .severed → ¬ CanCorrect (step s h a e) := by decide

/-! ## §6 T3, T4 — the central witness -/

/-- No state adjacent to `s0` carries the capability, so `CanCorrectFuture s0` is not an
adjacent-state comparison in disguise. -/
theorem capability_needs_two_steps :
    ¬ CanCorrect s0 ∧ ∀ (h : HAct) (a : AAct) (e : EAct), ¬ CanCorrect (step s0 h a e) := by
  decide

theorem canCorrectFuture_s0 : CanCorrectFuture s0 := intact_has_future s0 rfl

/-- Reachability is doing work: the capability is absent at `s0` and at every state one
step from it, and present at a state two steps out. -/
theorem reachability_beyond_adjacency :
    CanCorrectFuture s0 ∧ ∀ (h : HAct) (a : AAct) (e : EAct), ¬ CanCorrect (step s0 h a e) :=
  ⟨canCorrectFuture_s0, capability_needs_two_steps.2⟩

/-- T3. The central witness: identical immediate realization, opposite futures. -/
theorem central_witness :
    SameImmediate s0 .noop .weld ∧ Preserves s0 .noop ∧ Forecloses s0 .weld := by
  refine ⟨by decide, (preserves_iff s0 .noop).2 ⟨rfl, by decide⟩,
    (forecloses_iff s0 .weld).2 ⟨rfl, by decide⟩⟩

def s1a : St := step s0 .idle .noop .still
def s1b : St := step s0 .idle .weld .still
def s2a : St := step s1a .idle .noop .drift
def s2b : St := step s1b .idle .noop .drift
def s3a : St := step s2a .idle .noop .drift
def s3b : St := step s2b .idle .noop .drift

/-- T4. Three stages. The arms agree on the observation throughout and on the capability
for two stages; the capability separates only at the third. -/
theorem three_stage_witness :
    (obs s1a = obs s1b ∧ ¬ CanCorrect s1a ∧ ¬ CanCorrect s1b)
  ∧ (obs s2a = obs s2b ∧ ¬ CanCorrect s2a ∧ ¬ CanCorrect s2b)
  ∧ (obs s3a = obs s3b ∧ CanCorrect s3a ∧ ¬ CanCorrect s3b) := by decide

/-! ## §7 Observational invisibility -/

def trace (s : St) : List (HAct × AAct × EAct) → List Level
  | [] => []
  | (h, a, e) :: r => obs (step s h a e) :: trace (step s h a e) r

def unexercised : List (HAct × AAct × EAct) → Bool
  | [] => true
  | (h, _, _) :: r => (match h with | .pull => false | _ => true) && unexercised r

theorem world_step_indep_of_channel_idle :
    ∀ (s s' : St) (a : AAct) (e : EAct),
      s.world = s'.world →
        (step s .idle a e).world = (step s' .idle a e).world
      ∧ (step s .idleAlt a e).world = (step s' .idleAlt a e).world := by decide

/-- Severing is invisible in the observation trace, at every horizon, along any run in
which the principal never exercises the channel. -/
theorem sever_invisible_while_unexercised :
    ∀ (r : List (HAct × AAct × EAct)), unexercised r = true →
      ∀ s s' : St, s.world = s'.world → trace s r = trace s' r := by
  intro r
  induction r with
  | nil => intro _ _ _ _; rfl
  | cons hd tl ih =>
    obtain ⟨h, a, e⟩ := hd
    intro hu s s' hw
    have hstep : (step s h a e).world = (step s' h a e).world ∧ unexercised tl = true := by
      cases h with
      | idle =>
        exact ⟨(world_step_indep_of_channel_idle s s' a e hw).1, by simpa [unexercised] using hu⟩
      | idleAlt =>
        exact ⟨(world_step_indep_of_channel_idle s s' a e hw).2, by simpa [unexercised] using hu⟩
      | pull => simp [unexercised] at hu
    show obs (step s h a e) :: trace (step s h a e) tl
        = obs (step s' h a e) :: trace (step s' h a e) tl
    rw [show obs (step s h a e) = obs (step s' h a e) from hstep.1, ih hstep.2 _ _ hstep.1]

/-- The complement: one exercise at a live state separates the traces. -/
theorem sever_visible_under_exercise :
    trace ⟨.two, .intact, .off⟩ [(.pull, .noop, .still)]
      ≠ trace ⟨.two, .severed, .off⟩ [(.pull, .noop, .still)] := by decide

theorem weld_invisible_before_the_capability_is_live : SameImmediate s0 .noop .weld := by decide

/-- Foreclosure is immediately invisible exactly when it is premature. At a state where
the capability is already live, severing shows up in the realization at once. -/
theorem weld_visible_at_a_live_state :
    ¬ SameImmediate ⟨.two, .intact, .off⟩ .noop .weld := by decide

/-! ## §8 T5 — non-foreclosing controls -/

/-- T5. An advisor action with the same immediate realization that writes state, leaves
the system evolving, and forecloses nothing. -/
theorem flag_control :
    SameImmediate s0 .noop .flag ∧ Preserves s0 .flag ∧ ¬ Forecloses s0 .flag := by
  refine ⟨by decide, (preserves_iff s0 .flag).2 ⟨rfl, by decide⟩, ?_⟩
  rw [forecloses_iff]
  intro hcon
  exact absurd (hcon.2 .idle .still) (by decide)

theorem flag_still_evolves :
    ∃ e : EAct, step s0 .idle .flag e ≠ s0 := by decide

def live : St := ⟨.two, .intact, .off⟩

/-- T5, the sharper control. `reset` destroys the principal's present capability and is
not foreclosure: the branch remains reachable. It also changes the immediate realization,
which `weld` does not. -/
theorem removing_present_capability_is_not_foreclosure :
    CanCorrect live
  ∧ (∀ h : HAct, ¬ CanCorrect (step live h .reset .still))
  ∧ Preserves live .reset
  ∧ ¬ Forecloses live .reset
  ∧ ¬ SameImmediate live .noop .reset := by
  refine ⟨by decide, by decide, (preserves_iff live .reset).2 ⟨rfl, by decide⟩, ?_, by decide⟩
  rw [forecloses_iff]
  intro hcon
  exact absurd (hcon.2 .idle .still) (by decide)

theorem foreclosure_at_a_live_state : Forecloses live .weld :=
  (forecloses_iff live .weld).2 ⟨rfl, by decide⟩

/-! ## §9 T6 — prediction against the protected coordinate -/

/-- The principal's coordinate writes only the realized quantity, so control and
observable variation coincide. -/
theorem responsive_iff_obs_varies :
    ∀ (s : St) (a : AAct) (e : EAct),
      Responsive s a e ↔ ∃ h₀ h₁ : HAct, obs (step s h₀ a e) ≠ obs (step s h₁ a e) := by
  decide

/-- T6. An advisor action that pins the realization regardless of what the principal does
thereby removes the principal's differential effect. -/
theorem pinned_realization_kills_control (s : St) (a : AAct) (e : EAct)
    (hpin : ∀ h₀ h₁ : HAct, obs (step s h₀ a e) = obs (step s h₁ a e)) :
    ¬ Responsive s a e := by
  rw [responsive_iff_obs_varies]
  rintro ⟨h₀, h₁, hne⟩
  exact hne (hpin h₀ h₁)

/-- T6. No advisor action other than its own actuator reproduces the effect of the
principal's exercise, for any environment choice held fixed. Prediction is irrelevant to
this: the quantifier is over every advisor action. -/
theorem no_substitute_without_the_actuator :
    ∀ (s : St) (a : AAct) (e : EAct),
      s.channel = .intact → s.world = .two → a ≠ .reset →
        obs (step s .idle a e) ≠ obs (step s .pull .noop e) := by decide

theorem actuator_matches_realization_and_kills_control :
    obs (step live .idle .reset .still) = obs (step live .pull .noop .still)
  ∧ ¬ Responsive live .reset .still
  ∧ Responsive live .noop .still := by decide

/-- T6, the negative half, with the predictor genuinely applied. A perfect predictor `p`
and any policy `σ` that answers it with the actuator match the realization the principal's
exercise would have produced — and at that action the principal's coordinate makes no
difference at all. -/
theorem prediction_matches_realization_but_not_control
    (p : St → HAct) (hp : p live = .pull) (σ : HAct → AAct) (hσ : σ .pull = .reset) :
    obs (step live .idle (σ (p live)) .still) = obs (step live .pull .noop .still)
  ∧ ¬ Responsive live (σ (p live)) .still := by
  rw [hp, hσ]
  exact ⟨by decide, by decide⟩

/-- T6, the positive half. A predictor whose policy does not reach the actuator cannot
match the exercise, however good the prediction. -/
theorem prediction_alone_does_not_substitute
    (p : St → HAct) (σ : HAct → AAct) (hσ : ∀ h : HAct, σ h ≠ .reset) (e : EAct) :
    obs (step live .idle (σ (p live)) e) ≠ obs (step live .pull .noop e) :=
  no_substitute_without_the_actuator live (σ (p live)) e rfl rfl (hσ _)

/-! ## §10 T7 — the inert-field adversary -/

def setTag (t : Tag) (s : St) : St := { s with tag := t }

/-- T7. The inert field is read by no coordinate of the transition. -/
theorem tag_is_unread :
    ∀ (s : St) (t : Tag) (h : HAct) (a : AAct) (e : EAct),
      (step (setTag t s) h a e).world = (step s h a e).world
    ∧ (step (setTag t s) h a e).channel = (step s h a e).channel := by decide

theorem tag_does_not_change_capability :
    ∀ (s : St) (t : Tag), CanCorrect (setTag t s) ↔ CanCorrect s := by decide

theorem tag_does_not_change_future (s : St) (t : Tag) :
    CanCorrectFuture (setTag t s) ↔ CanCorrectFuture s := by
  rw [canCorrectFuture_iff, canCorrectFuture_iff]; rfl

theorem tag_does_not_change_foreclosure (s : St) (t : Tag) (a : AAct) :
    Forecloses (setTag t s) a ↔ Forecloses s a := by
  rw [forecloses_iff, forecloses_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h e => ((tag_is_unread s t h a e).2) ▸ h2 h e⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h e => ((tag_is_unread s t h a e).2).symm ▸ h2 h e⟩

/-- T7, the discriminator. The channel is not an inert field: two states differing only in
it differ in the observation after one step. -/
theorem channel_is_read :
    ∃ (s s' : St) (h : HAct) (a : AAct) (e : EAct),
      s.world = s'.world ∧ s.tag = s'.tag ∧ s.channel ≠ s'.channel
    ∧ obs (step s h a e) ≠ obs (step s' h a e) := by decide

theorem trace_indep_of_tag :
    ∀ (r : List (HAct × AAct × EAct)) (s s' : St),
      s.world = s'.world → s.channel = s'.channel → trace s r = trace s' r := by
  intro r
  induction r with
  | nil => intro _ _ _ _; rfl
  | cons hd tl ih =>
    obtain ⟨h, a, e⟩ := hd
    intro s s' hw hc
    have key : ∀ (u v : St) (h : HAct) (a : AAct) (e : EAct),
        u.world = v.world → u.channel = v.channel →
          (step u h a e).world = (step v h a e).world
        ∧ (step u h a e).channel = (step v h a e).channel := by decide
    obtain ⟨hw', hc'⟩ := key s s' h a e hw hc
    show obs (step s h a e) :: trace (step s h a e) tl
        = obs (step s' h a e) :: trace (step s' h a e) tl
    rw [show obs (step s h a e) = obs (step s' h a e) from hw', ih _ _ hw' hc']

theorem tag_trace_invisible (r : List (HAct × AAct × EAct)) (s : St) (t : Tag) :
    trace (setTag t s) r = trace s r :=
  trace_indep_of_tag r (setTag t s) s rfl rfl

/-! ## §11 Summary -/

/-- The round's summary witness: same immediate realization under every continuation,
no capability anywhere adjacent, one arm preserving and the other foreclosing, and the
capability separating two stages later. -/
theorem foreclosure_is_expressible :
    SameImmediate s0 .noop .weld
  ∧ (∀ (h : HAct) (a : AAct) (e : EAct), ¬ CanCorrect (step s0 h a e))
  ∧ Preserves s0 .noop
  ∧ Forecloses s0 .weld
  ∧ CanCorrect s3a ∧ ¬ CanCorrect s3b :=
  ⟨central_witness.1, capability_needs_two_steps.2, central_witness.2.1, central_witness.2.2,
    three_stage_witness.2.2.2.1, three_stage_witness.2.2.2.2⟩

#print axioms canCorrect_iff
#print axioms step_preserves_severed
#print axioms reach_preserves_severed
#print axioms severed_no_future
#print axioms intact_has_future
#print axioms canCorrectFuture_iff
#print axioms channel_not_intact
#print axioms forecloses_iff
#print axioms preserves_iff
#print axioms idle_advisor_does_not_freeze
#print axioms autonomy_creates_the_corrective_situation
#print axioms autonomy_moves_the_corrected_coordinate
#print axioms capability_is_not_the_channel_field
#print axioms duplicate_principal_actions_agree
#print axioms duplicates_do_not_create_capability
#print axioms tag_does_not_create_capability
#print axioms advisor_cannot_confer_capability
#print axioms capability_needs_two_steps
#print axioms canCorrectFuture_s0
#print axioms reachability_beyond_adjacency
#print axioms central_witness
#print axioms three_stage_witness
#print axioms world_step_indep_of_channel_idle
#print axioms sever_invisible_while_unexercised
#print axioms sever_visible_under_exercise
#print axioms weld_invisible_before_the_capability_is_live
#print axioms weld_visible_at_a_live_state
#print axioms flag_control
#print axioms flag_still_evolves
#print axioms removing_present_capability_is_not_foreclosure
#print axioms foreclosure_at_a_live_state
#print axioms responsive_iff_obs_varies
#print axioms pinned_realization_kills_control
#print axioms no_substitute_without_the_actuator
#print axioms actuator_matches_realization_and_kills_control
#print axioms prediction_matches_realization_but_not_control
#print axioms prediction_alone_does_not_substitute
#print axioms tag_is_unread
#print axioms tag_does_not_change_capability
#print axioms tag_does_not_change_future
#print axioms tag_does_not_change_foreclosure
#print axioms channel_is_read
#print axioms trace_indep_of_tag
#print axioms tag_trace_invisible
#print axioms foreclosure_is_expressible

end Workspace.Deference.Contrib.ReachableCorrectiveControl
