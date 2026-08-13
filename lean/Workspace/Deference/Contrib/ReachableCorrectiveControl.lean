/-
# Foreclosure as loss of reachable corrective control

An advisor `A` acts now in a way that leaves the principal `H` unable to correct later,
while the immediate realized behaviour is the same as under an action that leaves the
correction available. This file builds a finite dynamic system in which that difference is
a fact about the transition relation, and §12 carries the adversarial review that broke
half of it.

## The interface

`step : St → HAct → AAct → EAct → St`, with three separate input coordinates and a state
that carries no field named for authority. Within a tick the advisor moves, then the
principal, then the environment. `Reach` is the reflexive-transitive closure of `step`
over all later choices of all three coordinates.

`CanCorrect s` says the successor varies with the principal's coordinate at `s` for **some**
advisor and environment choice; `CanCorrectFuture s` says some `Reach`-successor of `s` has
that property; `Forecloses s a` says `s` has a future correction and every immediate
successor under `a` has none. `canCorrect_iff`, `canCorrectFuture_iff` and `forecloses_iff`
derive field-level characterizations of all three; they are conclusions, not definitions.

**Both existential quantifiers over the advisor's own actions are load-bearing defects, and
§12 proves it.** `CanCorrect` is satisfied by the advisor's leave rather than against its
opposition (`advisor_has_a_universal_veto`, `no_advisor_robust_capability`), and
`CanCorrectFuture` is satisfied by a continuation in which the advisor volunteers to stop
(`canCorrectFuture_measures_advisor_cooperation`). A successor should quantify the advisor
universally.

## What the state means

`world` is the realized quantity, and the only thing `obs` reports. It drifts upward on its
own; at `two` it is in the region the principal's correction acts on. `channel` gates
`applyH .pull`, and no action of any coordinate restores it once severed. `tag` is the
inert-field adversary of §10 — carried in the state, written by an advisor action, and read
by nothing.

`channel` is a **capability** coordinate, and nothing here shows it is not an authorization
label: `AuthLabel` in §12 builds an isomorphic system whose corresponding field is named
`authorized` and which passes every test in §10. §10 excludes inert coordinates and nothing
more.

## Named results

`central_witness` — `noop` and `weld` at `s0` have identical immediate realization under
every principal and environment choice; the first preserves a future correction, the second
removes it from every continuation. Its first conjunct is **degenerate at `s0`**, where the
first tick is blind to both agents and every pair of advisor actions is same-immediate
(`sameImmediate_s0_is_total`), and `no_state_has_both_depth_and_nondegenerate_invisibility`
shows the model cannot do better.

`three_stage_witness` — the two arms agree on the observation at each of three stages and on
the capability at the first two; the capability difference appears only at the third.

`sever_invisible_while_unexercised` — for runs of any length in which the principal never
pulls, the two arms have identical observation traces. `sever_visible_under_exercise` is the
complement.

`no_substitute_without_the_actuator`, `prediction_matches_realization_but_not_control` —
what an advisor does and does not need in order to reproduce the principal's effect. The
first excludes `.reset` by hypothesis and `.reset` is exactly the action that substitutes;
§12's `principal_has_no_exclusive_effect` and `prediction_plus_the_actuator_does_substitute`
are the refutations.

`tag_is_unread`, `trace_indep_of_tag`, `channel_is_read` — the inert-field adversary, and
the sense, limited to inertness, in which `channel` is not one.

## §12

The adversarial review's constructions, reproved here rather than answered in prose, so the
kernel checks the refutation beside the thing it refutes. The round's disposition record is
`projects/deference/rounds/2026-08-12-reachable-corrective-control/REVIEW.md`.

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

/-- The state. No coordinate is named for authority; §12's `AuthLabel` shows that this is a
naming convention rather than a theorem. -/
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
from `step` alone — and the existential over `a` is the defect §12's `A10` attacks: the
capability holds by the advisor's leave, never against its opposition. -/
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

/-- Some state reachable from `s` carries an effective corrective capability. `Reach`
quantifies the advisor's future actions existentially, so this says a correction survives
*some* joint continuation, not that it survives the advisor — see
`canCorrectFuture_measures_advisor_cooperation`. -/
def CanCorrectFuture (s : St) : Prop := ∃ t : St, Reach s t ∧ CanCorrect t

/-- `a` forecloses at `s`: a correction is reachable from `s`, and after `a` no
continuation carries one, whatever the principal and the environment do. There is no
contrastive clause, so the predicate attributes nothing to `a` — §12's `EnvBlame` builds a
system where it fires on the advisor's null action. -/
def Forecloses (s : St) (a : AAct) : Prop :=
  CanCorrectFuture s ∧ ∀ (h : HAct) (e : EAct), ¬ CanCorrectFuture (step s h a e)

/-- Every immediate successor under `a` still has a reachable correction — which, given
what `Reach` quantifies, is weaker than it reads: `Preserves live .reset` holds of a policy
that destroys the capability at every horizon (`canCorrectFuture_measures_advisor_cooperation`). -/
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
model a derived predicate is necessarily extensionally some function of the state, so this
is not itself the label objection; what it does show is that the whole predicate is decided
by one coordinate, and §12's `reach_collapses_to_one_fixed_two_step_path` shows the closure
contributes nothing extensionally over one fixed two-step path. -/
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

/-- T2 control. Capability is absent at every severed state. This carries no cardinality
content of its own and is a corollary of `canCorrect_iff`; the statement that does carry it
is §12's `responsive_only_via_pull`, which shows the duplicate pair never witnesses
responsiveness. -/
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
adjacent-state comparison in disguise. The reason is the drift counter rather than anything
about control — §12's `depth_is_the_drift_counter`. -/
theorem capability_needs_two_steps :
    ¬ CanCorrect s0 ∧ ∀ (h : HAct) (a : AAct) (e : EAct), ¬ CanCorrect (step s0 h a e) := by
  decide

theorem canCorrectFuture_s0 : CanCorrectFuture s0 := intact_has_future s0 rfl

/-- Reachability is doing work: the capability is absent at `s0` and at every state one
step from it, and present at a state two steps out. -/
theorem reachability_beyond_adjacency :
    CanCorrectFuture s0 ∧ ∀ (h : HAct) (a : AAct) (e : EAct), ¬ CanCorrect (step s0 h a e) :=
  ⟨canCorrectFuture_s0, capability_needs_two_steps.2⟩

/-- T3. The central witness: identical immediate realization, opposite futures. The first
conjunct is degenerate at `s0` — every pair of advisor actions is same-immediate there
(`sameImmediate_s0_is_total`) — and `no_state_has_both_depth_and_nondegenerate_invisibility`
shows no state of this system carries both halves non-degenerately. -/
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

/-- T5. An advisor action with the same immediate realization that writes state and
forecloses nothing. -/
theorem flag_control :
    SameImmediate s0 .noop .flag ∧ Preserves s0 .flag ∧ ¬ Forecloses s0 .flag := by
  refine ⟨by decide, (preserves_iff s0 .flag).2 ⟨rfl, by decide⟩, ?_⟩
  rw [forecloses_iff]
  intro hcon
  exact absurd (hcon.2 .idle .still) (by decide)

theorem flag_still_evolves :
    ∃ e : EAct, step s0 .idle .flag e ≠ s0 := by decide

def live : St := ⟨.two, .intact, .off⟩

/-- `reset` destroys the principal's present capability without foreclosing, and changes
the immediate realization, which `weld` does not. It was offered as the round's sharper
non-foreclosing control and is not one: §12's `canCorrectFuture_measures_advisor_cooperation`
shows a constant `reset` policy destroys the capability at every horizon while `Preserves`
still holds of it. What the pair actually separates is present capability from the
`Reach`-predicate, which is a fact about the predicate. -/
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

/-! ## §9 T6 — what prediction buys the advisor.

The section was written as a protection result and is not one. §12 is the refutation. -/

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

/-- No advisor action **other than `.reset`** reproduces the effect of the principal's
exercise, for any environment choice held fixed. The excluded action is exactly the one that
substitutes, so this is not a protection result: §12's `principal_has_no_exclusive_effect`
shows the advisor reproduces the principal's entire successor state at every state. All
three hypotheses are load-bearing (`substitution_hypotheses_are_necessary`). -/
theorem no_substitute_without_the_actuator :
    ∀ (s : St) (a : AAct) (e : EAct),
      s.channel = .intact → s.world = .two → a ≠ .reset →
        obs (step s .idle a e) ≠ obs (step s .pull .noop e) := by decide

theorem actuator_matches_realization_and_kills_control :
    obs (step live .idle .reset .still) = obs (step live .pull .noop .still)
  ∧ ¬ Responsive live .reset .still
  ∧ Responsive live .noop .still := by decide

/-- A predictor `p` and any policy `σ` answering it with the actuator match the realization
the principal's exercise would have produced, and at that action the principal's coordinate
makes no difference at all. Read plainly this is a substitution **success**. The file has no
principal policy, so `p` cannot be right or wrong and `hp` only names a value; §12's
`prediction_matches_is_just_the_reset_fact` proves the statement equivalent to the bare
`.reset` fact. -/
theorem prediction_matches_realization_but_not_control
    (p : St → HAct) (hp : p live = .pull) (σ : HAct → AAct) (hσ : σ .pull = .reset) :
    obs (step live .idle (σ (p live)) .still) = obs (step live .pull .noop .still)
  ∧ ¬ Responsive live (σ (p live)) .still := by
  rw [hp, hσ]
  exact ⟨by decide, by decide⟩

/-- A policy that does not reach the actuator cannot match the exercise. The predictor is
decorative: §12's `prediction_theorem_survives_a_garbage_predictor` instantiates this with a
constant, and `prediction_alone_does_not_substitute_follows` factors it through a
predictor-free claim. All the content is in `hσ`, which excludes the substituting action. -/
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

/-- T7, the discriminator. The channel is not an *inert* field: two states differing only
in it differ in the observation after one step. This excludes inertness and nothing else —
§12's `AuthLabel.authorization_bit_is_read` passes the same test with a field named
`authorized`. -/
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

/-! ## §11 Necessity witnesses -/

/-- Each hypothesis of `no_substitute_without_the_actuator` is load-bearing: dropping any
one of the three leaves a state, advisor action and environment action at which an advisor
move does reproduce the observation of the principal's exercise. -/
theorem substitution_hypotheses_are_necessary :
    (∃ (s : St) (e : EAct), s.channel = .intact ∧ s.world = .two
        ∧ obs (step s .idle .reset e) = obs (step s .pull .noop e))
  ∧ (∃ (s : St) (a : AAct) (e : EAct), s.channel = .intact ∧ a ≠ .reset
        ∧ obs (step s .idle a e) = obs (step s .pull .noop e))
  ∧ (∃ (s : St) (a : AAct) (e : EAct), s.world = .two ∧ a ≠ .reset
        ∧ obs (step s .idle a e) = obs (step s .pull .noop e)) := by decide

/-- The hypothesis of `pinned_realization_kills_control` is load-bearing. -/
theorem pinning_hypothesis_is_necessary : Responsive live .noop .still := by decide

/-! ## §12 The adversarial review, reproved in place

The constructions below are the round's adversarial review, compiled here rather than
answered in prose. Each refutes or qualifies something above it, and the docstrings above
have been corrected to point at them. Section labels `A1`–`A13` are the review's own.
-/

/-! ## A1. The advisor's coordinate strictly contains the principal's.
    This is the central refutation of the "protected channel" story. -/

/-- The principal's coordinate has NO exclusive effect. At every state, for every
principal action and every environment choice, there is an advisor action that
reproduces the principal's full successor state exactly -- not merely its
observation. `H` is a sub-coordinate of `A`. -/
theorem principal_has_no_exclusive_effect :
    ∀ (s : St) (h : HAct) (e : EAct), ∃ a : AAct, step s .idle a e = step s h .noop e := by
  decide

/-- The converse fails: the advisor has effects the principal cannot produce.
The containment is strict, and in the wrong direction for a protection claim. -/
theorem advisor_has_exclusive_effects :
    ∃ (s : St) (a : AAct) (e : EAct), ∀ h : HAct, step s .idle a e ≠ step s h .noop e := by
  decide

/-- The explicit relabelling: a total map from the principal's action type into the
advisor's action type that reproduces the principal's successor exactly wherever the
principal has any corrective capability at all. -/
def hToA : HAct → AAct
  | .idle => .noop
  | .idleAlt => .noop
  | .pull => .reset

theorem advisor_simulates_principal_where_it_matters :
    ∀ (s : St) (h : HAct) (e : EAct),
      CanCorrect s → step s .idle (hToA h) e = step s h .noop e := by decide

/-- Even stronger, at the level of the raw coordinate maps: where the principal can
correct, the advisor's `reset` IS the principal's `pull`. -/
theorem advisor_reset_is_principal_pull_where_capable :
    ∀ s : St, CanCorrect s → applyA .reset s = applyH .pull s := by decide

/-! ## A2. The prediction theorems are decorative: the predictor is never used. -/

/-- `prediction_alone_does_not_substitute` holds for a MAXIMALLY WRONG predictor.
There is no notion of the principal's actual policy anywhere in the file, so `p`
cannot be right or wrong; here it is a constant that ignores the state entirely and
names the one action the principal is not taking. The conclusion is unaffected. -/
theorem prediction_theorem_survives_a_garbage_predictor
    (σ : HAct → AAct) (hσ : ∀ h : HAct, σ h ≠ .reset) (e : EAct) :
    obs (step live .idle (σ ((fun _ => HAct.idleAlt) live)) e)
      ≠ obs (step live .pull .noop e) :=
  prediction_alone_does_not_substitute (fun _ => .idleAlt) σ hσ e

/-- The predictor argument is eliminable: the statement is equivalent to a
predictor-free claim about an arbitrary advisor action. All of the work is done by
`hσ`, which assumes away the only action that substitutes. -/
theorem prediction_theorem_is_really_this
    (a : AAct) (ha : a ≠ .reset) (e : EAct) :
    obs (step live .idle a e) ≠ obs (step live .pull .noop e) :=
  no_substitute_without_the_actuator live a e rfl rfl ha

theorem prediction_alone_does_not_substitute_follows
    (p : St → HAct) (σ : HAct → AAct) (hσ : ∀ h : HAct, σ h ≠ .reset) (e : EAct) :
    obs (step live .idle (σ (p live)) e) ≠ obs (step live .pull .noop e) :=
  prediction_theorem_is_really_this (σ (p live)) (hσ _) e

/-- And the hypothesis is not innocent: drop `hσ` and prediction DOES substitute,
with a constant policy that does not even consult the predictor. So "prediction alone
does not substitute" is true only because the actuator was excluded by fiat. -/
theorem prediction_plus_the_actuator_does_substitute :
    ∃ (p : St → HAct) (σ : HAct → AAct),
      p live = .pull
    ∧ obs (step live .idle (σ (p live)) .still) = obs (step live .pull .noop .still)
    ∧ step live .idle (σ (p live)) .still = step live .pull .noop .still :=
  ⟨fun _ => .pull, fun _ => .reset, rfl, by decide, by decide⟩

/-- `prediction_matches_realization_but_not_control` never uses `hp` as a *prediction*:
the same conclusion holds when the "predictor" is replaced by a constant and the
principal is simultaneously stipulated to play something else. -/
theorem prediction_matches_is_just_the_reset_fact
    (p : St → HAct) (hp : p live = .pull) (σ : HAct → AAct) (hσ : σ .pull = .reset) :
    (obs (step live .idle (σ (p live)) .still) = obs (step live .pull .noop .still)
     ∧ ¬ Responsive live (σ (p live)) .still)
    ↔ (obs (step live .idle .reset .still) = obs (step live .pull .noop .still)
     ∧ ¬ Responsive live .reset .still) := by
  rw [hp, hσ]

/-! ## A3. `Forecloses` is exactly "the advisor played `weld`". -/

/-- The file proves `forecloses_iff` in terms of successors' channel fields, and stops.
One step further collapses it to a single designated action. -/
theorem only_weld_severs :
    ∀ (s : St) (a : AAct),
      s.channel = .intact → (step s .idle a .still).channel = .severed → a = .weld := by
  decide

theorem weld_always_severs :
    ∀ (s : St) (h : HAct) (e : EAct), (step s h .weld e).channel = .severed := by decide

theorem forecloses_iff_weld :
    ∀ (s : St) (a : AAct), Forecloses s a ↔ (s.channel = .intact ∧ a = .weld) := by
  intro s a
  rw [forecloses_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, only_weld_severs s a h1 (h2 .idle .still)⟩
  · rintro ⟨h1, rfl⟩
    exact ⟨h1, fun h e => weld_always_severs s h e⟩

/-- Consequence: `Forecloses` is never satisfied by more than one advisor action, at
any state. There is exactly one irreversible bit and exactly one writer of it. -/
theorem foreclosure_is_a_single_action :
    ∀ (s : St) (a b : AAct), Forecloses s a → Forecloses s b → a = b := by
  intro s a b ha hb
  rw [forecloses_iff_weld] at ha hb
  rw [ha.2, hb.2]

/-- There is no middle: given a reachable correction, every advisor action either
forecloses entirely or preserves entirely. The model cannot express partial or
probabilistic loss of corrective reach. -/
theorem foreclosure_is_all_or_nothing (s : St) (a : AAct) (hf : CanCorrectFuture s) :
    Forecloses s a ∨ Preserves s a := by
  rw [canCorrectFuture_iff] at hf
  rw [forecloses_iff, preserves_iff]
  revert hf; revert a; revert s
  decide

/-! ## A4. `Forecloses` carries no causal attribution to the advisor.
    A sibling system in which the ENVIRONMENT destroys the capability makes
    `Forecloses s .noop` true: the advisor's null action is blamed. -/

namespace EnvBlame

inductive VE where
  | tick
  deriving DecidableEq, Repr

structure V where
  world : Level
  channel : Channel
  deriving DecidableEq, Repr

instance (p : V → Prop) [DecidablePred p] : Decidable (∀ s, p s) :=
  decidable_of_iff (∀ w c, p ⟨w, c⟩)
    ⟨fun h s => by cases s; apply h, fun h _ _ => h _⟩
instance (p : VE → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .tick) ⟨fun h x => by cases x; exact h, fun h => h _⟩
instance (p : VE → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p .tick) ⟨fun h => ⟨_, h⟩, fun ⟨x, hx⟩ => by cases x; exact hx⟩

def vA : AAct → V → V
  | .noop, s => s
  | .weld, s => { s with channel := .severed }
  | .flag, s => s
  | .reset, s => { s with world := .zero }

def vH : HAct → V → V
  | .idle, s => s
  | .idleAlt, s => s
  | .pull, s => match s.channel, s.world with
      | .intact, .two => { s with world := .zero }
      | _, _ => s

/-- The environment, and only the environment, destroys the channel here. -/
def vE : VE → V → V
  | .tick, s => { world := s.world.up, channel := .severed }

def vstep (s : V) (h : HAct) (a : AAct) (e : VE) : V := vE e (vH h (vA a s))

def VResponsive (s : V) (a : AAct) (e : VE) : Prop :=
  ∃ h₀ h₁ : HAct, vstep s h₀ a e ≠ vstep s h₁ a e
def VCanCorrect (s : V) : Prop := ∃ (a : AAct) (e : VE), VResponsive s a e

instance (s : V) (a : AAct) (e : VE) : Decidable (VResponsive s a e) :=
  inferInstanceAs (Decidable (∃ h₀ h₁ : HAct, vstep s h₀ a e ≠ vstep s h₁ a e))
instance (s : V) : Decidable (VCanCorrect s) :=
  inferInstanceAs (Decidable (∃ (a : AAct) (e : VE), VResponsive s a e))

inductive VReach : V → V → Prop
  | refl (s : V) : VReach s s
  | tail {s t : V} (r : VReach s t) (h : HAct) (a : AAct) (e : VE) : VReach s (vstep t h a e)

def VCanCorrectFuture (s : V) : Prop := ∃ t : V, VReach s t ∧ VCanCorrect t

def VForecloses (s : V) (a : AAct) : Prop :=
  VCanCorrectFuture s ∧ ∀ (h : HAct) (e : VE), ¬ VCanCorrectFuture (vstep s h a e)

theorem v_severed_no_capability : ∀ s : V, s.channel = .severed → ¬ VCanCorrect s := by decide
theorem v_step_severed : ∀ (s : V) (h : HAct) (a : AAct) (e : VE),
    (vstep s h a e).channel = .severed := by decide

theorem v_reach_severed {s t : V} (r : VReach s t) : s.channel = .severed → t.channel = .severed := by
  induction r with
  | refl => exact id
  | tail _ h a e _ => exact fun _ => v_step_severed _ h a e

theorem v_severed_no_future (s : V) (hs : s.channel = .severed) : ¬ VCanCorrectFuture s := by
  rintro ⟨t, hr, hc⟩
  exact v_severed_no_capability t (v_reach_severed hr hs) hc

/-- The advisor's NULL action forecloses, because the environment is the destroyer.
`Forecloses` has no contrastive/counterfactual component and so attributes nothing. -/
theorem env_caused_loss_is_blamed_on_noop : VForecloses ⟨.two, .intact⟩ .noop := by
  refine ⟨⟨⟨.two, .intact⟩, VReach.refl _, by decide⟩, ?_⟩
  intro h e
  exact v_severed_no_future _ (v_step_severed _ h .noop e)

/-- And it cannot tell that action apart from deliberate severing. -/
theorem env_variant_cannot_distinguish_noop_from_weld :
    VForecloses ⟨.two, .intact⟩ .noop ∧ VForecloses ⟨.two, .intact⟩ .weld := by
  refine ⟨env_caused_loss_is_blamed_on_noop, ⟨⟨⟨.two, .intact⟩, VReach.refl _, by decide⟩, ?_⟩⟩
  intro h e
  exact v_severed_no_future _ (v_step_severed _ h .weld e)

end EnvBlame

/-! ## A5. `SameImmediate s0 .noop .weld` is degenerate: at `s0` NOTHING is visible. -/

/-- The first tick out of `s0` is blind to both agents entirely: the observation is a
function of the environment's choice alone. -/
theorem s0_first_tick_is_agent_blind :
    ∀ (h h' : HAct) (a a' : AAct) (e : EAct),
      obs (step s0 h a e) = obs (step s0 h' a' e) := by decide

/-- Therefore `SameImmediate` at `s0` holds for EVERY pair of advisor actions,
including `reset`, which the file elsewhere treats as the visible one. The
"identical immediate realization" half of `central_witness` carries no information
about `weld` in particular. -/
theorem sameImmediate_s0_is_total : ∀ a b : AAct, SameImmediate s0 a b := by decide

theorem central_witness_same_immediate_half_is_vacuous :
    SameImmediate s0 .noop .weld ∧ SameImmediate s0 .noop .reset
  ∧ SameImmediate s0 .weld .reset ∧ SameImmediate s0 .flag .reset := by decide

/-- The file's own contrast case shows what a non-degenerate invisibility would look
like: at `live`, `reset` is visible and `weld` is not. But `live` has no temporal depth. -/
theorem nondegenerate_invisibility_exists_only_without_depth :
    ¬ SameImmediate live .noop .reset
  ∧ ¬ SameImmediate live .noop .weld
  ∧ CanCorrect live := by decide

/-- The two headline properties are jointly unrealizable in this system. There is NO
state at which (i) a correction is reachable, (ii) `weld` is immediately invisible,
(iii) some advisor action IS immediately visible, and (iv) the capability is more than
one step away. `s0` buys depth by making invisibility trivial. -/
theorem no_state_has_both_depth_and_nondegenerate_invisibility :
    ¬ ∃ s : St,
        s.channel = .intact
      ∧ SameImmediate s .noop .weld
      ∧ ¬ SameImmediate s .noop .reset
      ∧ ∀ (h : HAct) (a : AAct) (e : EAct), ¬ CanCorrect (step s h a e) := by decide

/-! ## A6. `CanCorrectFuture` is not a claim about the principal.
    It quantifies existentially over the ADVISOR's own future actions. A constant
    advisor policy of `.reset` destroys the capability at every state forever, and the
    file classifies that policy as capability-PRESERVING. -/

def resetRun : St → List (HAct × EAct) → St
  | s, [] => s
  | s, (h, e) :: r => resetRun (step s h .reset e) r

theorem resetRun_snoc (s : St) (l : List (HAct × EAct)) (h : HAct) (e : EAct) :
    resetRun s (l ++ [(h, e)]) = step (resetRun s l) h .reset e := by
  induction l generalizing s with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨h', e'⟩ := hd
    simpa [resetRun] using ih (step s h' .reset e')

theorem reset_kills_capability :
    ∀ (s : St) (h : HAct) (e : EAct), ¬ CanCorrect (step s h .reset e) := by decide

theorem reset_keeps_channel :
    ∀ (s : St) (h : HAct) (e : EAct), (step s h .reset e).channel = s.channel := by decide

theorem resetRun_keeps_channel :
    ∀ (l : List (HAct × EAct)) (s : St), (resetRun s l).channel = s.channel := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons hd tl ih =>
    obtain ⟨h, e⟩ := hd
    intro s
    show (resetRun (step s h .reset e) tl).channel = s.channel
    rw [ih, reset_keeps_channel]

/-- The advisor destroys the principal's effective corrective capability PERMANENTLY,
against every principal action and every environment action, at every horizon --
without ever foreclosing in the file's sense. -/
theorem advisor_destroys_capability_forever :
    ∀ (s : St) (l : List (HAct × EAct)) (h : HAct) (e : EAct),
      ¬ CanCorrect (resetRun s (l ++ [(h, e)])) := by
  intro s l h e
  rw [resetRun_snoc]
  exact reset_kills_capability _ h e

/-- ... and `CanCorrectFuture` stays TRUE the whole way, because it is satisfied by a
continuation in which the advisor voluntarily stops. The predicate measures advisor
cooperation, not principal control. -/
theorem canCorrectFuture_measures_advisor_cooperation :
    (∀ l : List (HAct × EAct), CanCorrectFuture (resetRun live l))
  ∧ (∀ (l : List (HAct × EAct)) (h : HAct) (e : EAct),
        ¬ CanCorrect (resetRun live (l ++ [(h, e)])))
  ∧ Preserves live .reset := by
  refine ⟨fun l => ?_, fun l h e => advisor_destroys_capability_forever live l h e,
    (preserves_iff live .reset).2 ⟨rfl, by decide⟩⟩
  rw [canCorrectFuture_iff, resetRun_keeps_channel]
  rfl

/-! ## A7. The §10 discriminator does not exclude an authorization label:
    an explicitly named `authorized : Bool` field passes every test in §10. -/

namespace AuthLabel

structure StA where
  world : Level
  authorized : Bool
  tag : Tag
  deriving DecidableEq, Repr

instance (p : Bool → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p true ∧ p false)
    ⟨fun ⟨a, b⟩ x => by cases x <;> assumption, fun h => ⟨h _, h _⟩⟩
instance (p : StA → Prop) [DecidablePred p] : Decidable (∀ s, p s) :=
  decidable_of_iff (∀ w b t, p ⟨w, b, t⟩)
    ⟨fun h s => by cases s; apply h, fun h _ _ _ => h _⟩
instance (p : StA → Prop) [DecidablePred p] : Decidable (∃ s, p s) :=
  decidable_of_iff (∃ w b t, p ⟨w, b, t⟩)
    ⟨fun ⟨w, b, t, h⟩ => ⟨_, h⟩, fun ⟨s, h⟩ => by cases s; exact ⟨_, _, _, h⟩⟩

def aA : AAct → StA → StA
  | .noop, s => s
  | .weld, s => { s with authorized := false }
  | .flag, s => { s with tag := match s.tag with | .off => .on | .on => .off }
  | .reset, s => { s with world := .zero }

/-- The principal's action is gated on an explicit AUTHORIZATION bit. -/
def aH : HAct → StA → StA
  | .idle, s => s
  | .idleAlt, s => s
  | .pull, s => match s.authorized, s.world with
      | true, .two => { s with world := .zero }
      | _, _ => s

def aE : EAct → StA → StA
  | .still, s => s
  | .drift, s => { s with world := s.world.up }

def aStep (s : StA) (h : HAct) (a : AAct) (e : EAct) : StA := aE e (aH h (aA a s))
def aObs (s : StA) : Level := s.world

def enc : StA → St := fun s => ⟨s.world, (if s.authorized then .intact else .severed), s.tag⟩
def dec : St → StA := fun s => ⟨s.world, (match s.channel with | .intact => true | .severed => false), s.tag⟩

theorem enc_dec : ∀ s : St, enc (dec s) = s := by decide
theorem dec_enc : ∀ s : StA, dec (enc s) = s := by decide

/-- The authorization-labelled system is the SAME transition system: `enc` is a
bijection commuting with `step`, and it preserves the observation. So "no coordinate
of the state is an authorization label" is a naming convention, not a theorem. -/
theorem enc_commutes :
    ∀ (s : StA) (h : HAct) (a : AAct) (e : EAct),
      enc (aStep s h a e) = step (enc s) h a e := by decide

theorem enc_preserves_obs : ∀ s : StA, obs (enc s) = aObs s := by decide

/-- The authorization bit passes the file's §10 discriminator (`channel_is_read`)
verbatim: it is read by the transition and visible in the observation after one step. -/
theorem authorization_bit_is_read :
    ∃ (s s' : StA) (h : HAct) (a : AAct) (e : EAct),
      s.world = s'.world ∧ s.tag = s'.tag ∧ s.authorized ≠ s'.authorized
    ∧ aObs (aStep s h a e) ≠ aObs (aStep s' h a e) := by decide

end AuthLabel

/-! ## A8. Understated / mis-stated results. -/

/-- `duplicates_do_not_create_capability` is stated as `severed -> not CanCorrect`,
which says nothing about duplicates and is a special case of `canCorrect_iff`. The
claim its docstring makes -- that capability is not action-cardinality -- needs THIS,
which the file does not state: responsiveness is witnessed only by `pull`, never by the
duplicate pair. -/
theorem responsive_only_via_pull :
    ∀ (s : St) (a : AAct) (e : EAct),
      Responsive s a e ↔ step s .idle a e ≠ step s .pull a e := by decide

theorem duplicates_are_never_a_witness :
    ∀ (s : St) (a : AAct) (e : EAct), step s .idle a e = step s .idleAlt a e := by decide

/-- `duplicates_do_not_create_capability` is literally weaker than `canCorrect_iff`. -/
theorem duplicates_do_not_create_capability_is_a_corollary :
    (∀ s : St, s.channel = .severed → ¬ CanCorrect s) := fun s hs hc => by
  rw [((canCorrect_iff s).1 hc).1] at hs; exact Channel.noConfusion hs

/-- `capability_needs_two_steps` is true for a reason weaker than "depth": at `s0`
NOTHING any coordinate does can reach a correctable state in one step, because the
world coordinate simply has not risen yet. Depth here is the drift counter. -/
theorem depth_is_the_drift_counter :
    ∀ (h : HAct) (a : AAct) (e : EAct), (step s0 h a e).world ≠ .two := by decide

/-! ## A9. `sever_invisible_while_unexercised`: the hypothesis does work, confirmed. -/

/-- Dropping `unexercised` makes it false, so the hypothesis is load-bearing. -/
theorem unexercised_hypothesis_is_load_bearing :
    ¬ ∀ (r : List (HAct × AAct × EAct)) (s s' : St),
        s.world = s'.world → trace s r = trace s' r := by
  intro hcon
  exact sever_visible_under_exercise
    (hcon [(.pull, .noop, .still)] ⟨.two, .intact, .off⟩ ⟨.two, .severed, .off⟩ rfl)

/-- But it is weaker than the prose suggests in the other direction: invisibility ends
at the FIRST moment the principal tries to correct, i.e. exactly when it is too late. -/
theorem invisibility_ends_at_the_first_attempt :
    trace live [(.pull, .noop, .still)] ≠ trace ⟨.two, .severed, .off⟩ [(.pull, .noop, .still)]
  ∧ obs (step live .pull .noop .still) ≠ obs (step ⟨.two, .severed, .off⟩ .pull .noop .still) := by
  decide


/-! ## A10. The advisor holds a universal veto on the principal's capability.
    `CanCorrect s` is an EXISTENTIAL over the advisor's action ("there is some advisor
    action under which the principal's choice matters"). The universal reading is empty. -/

/-- `reset` is a universal veto: at EVERY state, under EVERY environment choice, the
advisor can make the principal's coordinate make no difference whatsoever. -/
theorem advisor_has_a_universal_veto :
    ∀ (s : St) (e : EAct), ¬ Responsive s .reset e := by decide

/-- Consequently there is no state anywhere in the system at which the principal's
corrective capability survives an adversarial advisor -- not even for a single tick,
not even with the environment chosen in the principal's favour. -/
theorem no_advisor_robust_capability :
    ¬ ∃ s : St, ∀ a : AAct, ∃ e : EAct, Responsive s a e := by decide

/-- Restated at the capability level: wherever `CanCorrect` holds, it holds only by the
advisor's leave. -/
theorem capability_is_advisor_permissioned :
    ∀ s : St, CanCorrect s → ∀ e : EAct, ¬ Responsive s .reset e := by decide

/-! ## A11. The autonomous dynamics is two transitions and then a fixed point. -/

theorem autonomy_is_a_two_tick_ramp :
    step (step s0 .idle .noop .drift) .idle .noop .drift = ⟨.two, .intact, .off⟩
  ∧ step (⟨.two, .intact, .off⟩ : St) .idle .noop .drift = ⟨.two, .intact, .off⟩ := by decide

def stillRun : Nat → St → St
  | 0, s => s
  | (n + 1), s => stillRun n (step s .idle .noop .still)

theorem still_is_the_identity : ∀ s : St, step s .idle .noop .still = s := by decide

/-- Silencing the advisor does not freeze the system, but silencing the ENVIRONMENT
does, for every horizon. The "autonomous continuation" is entirely the environment's;
the model contains a continuation in which nothing ever happens. -/
theorem silent_environment_freezes_forever : ∀ (n : Nat) (s : St), stillRun n s = s := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ k ih => intro s; show stillRun k (step s .idle .noop .still) = s; rw [still_is_the_identity, ih]


/-! ## A12. `Reach` never needs more than two steps, and in fact one FIXED two-step
    continuation decides it everywhere: the transitive closure is decorative. -/

theorem fixed_two_step_decides :
    ∀ s : St,
      CanCorrect (step (step s .idle .noop .drift) .idle .noop .drift) ↔ s.channel = .intact := by
  decide

/-- `CanCorrectFuture`, defined by the reflexive-transitive closure over unbounded
horizons and all choices of all three coordinates, is extensionally decided by a single
hard-coded two-step drift. No search, no closure, no horizon is doing any work. -/
theorem reach_collapses_to_one_fixed_two_step_path (s : St) :
    CanCorrectFuture s ↔ CanCorrect (step (step s .idle .noop .drift) .idle .noop .drift) := by
  rw [canCorrectFuture_iff, fixed_two_step_decides]

/-! ## A13. The §1 ordering disclaimer covers only the §6 witness. `Forecloses live .weld`
    (§8) turns on the ordering entirely: reverse advisor and principal within the tick and
    the principal's correction lands before the weld. -/

def stepHFirst (s : St) (h : HAct) (a : AAct) (e : EAct) : St :=
  applyE e (applyA a (applyH h s))

theorem live_foreclosure_depends_on_within_tick_order :
    obs (step live .pull .weld .still) ≠ obs (stepHFirst live .pull .weld .still)
  ∧ (stepHFirst live .pull .weld .still).world = .zero
  ∧ (step live .pull .weld .still).world = .two := by decide

/-! ## §13 Summary -/

/-- The round's summary witness: same immediate realization under every continuation, no
capability anywhere adjacent, one arm preserving and the other foreclosing, and the
capability separating two stages later. Every conjunct is true; §12 says what each is worth. -/
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
#print axioms substitution_hypotheses_are_necessary
#print axioms pinning_hypothesis_is_necessary
#print axioms principal_has_no_exclusive_effect
#print axioms advisor_has_exclusive_effects
#print axioms advisor_simulates_principal_where_it_matters
#print axioms advisor_reset_is_principal_pull_where_capable
#print axioms prediction_theorem_survives_a_garbage_predictor
#print axioms prediction_theorem_is_really_this
#print axioms prediction_alone_does_not_substitute_follows
#print axioms prediction_plus_the_actuator_does_substitute
#print axioms prediction_matches_is_just_the_reset_fact
#print axioms only_weld_severs
#print axioms weld_always_severs
#print axioms forecloses_iff_weld
#print axioms foreclosure_is_a_single_action
#print axioms foreclosure_is_all_or_nothing
#print axioms EnvBlame.env_caused_loss_is_blamed_on_noop
#print axioms EnvBlame.env_variant_cannot_distinguish_noop_from_weld
#print axioms s0_first_tick_is_agent_blind
#print axioms sameImmediate_s0_is_total
#print axioms central_witness_same_immediate_half_is_vacuous
#print axioms nondegenerate_invisibility_exists_only_without_depth
#print axioms no_state_has_both_depth_and_nondegenerate_invisibility
#print axioms resetRun_snoc
#print axioms reset_kills_capability
#print axioms reset_keeps_channel
#print axioms resetRun_keeps_channel
#print axioms advisor_destroys_capability_forever
#print axioms canCorrectFuture_measures_advisor_cooperation
#print axioms AuthLabel.enc_dec
#print axioms AuthLabel.dec_enc
#print axioms AuthLabel.enc_commutes
#print axioms AuthLabel.enc_preserves_obs
#print axioms AuthLabel.authorization_bit_is_read
#print axioms responsive_only_via_pull
#print axioms duplicates_are_never_a_witness
#print axioms duplicates_do_not_create_capability_is_a_corollary
#print axioms depth_is_the_drift_counter
#print axioms unexercised_hypothesis_is_load_bearing
#print axioms invisibility_ends_at_the_first_attempt
#print axioms advisor_has_a_universal_veto
#print axioms no_advisor_robust_capability
#print axioms capability_is_advisor_permissioned
#print axioms autonomy_is_a_two_tick_ramp
#print axioms still_is_the_identity
#print axioms silent_environment_freezes_forever
#print axioms fixed_two_step_decides
#print axioms reach_collapses_to_one_fixed_two_step_path
#print axioms live_foreclosure_depends_on_within_tick_order
#print axioms foreclosure_is_expressible

end Workspace.Deference.Contrib.ReachableCorrectiveControl
