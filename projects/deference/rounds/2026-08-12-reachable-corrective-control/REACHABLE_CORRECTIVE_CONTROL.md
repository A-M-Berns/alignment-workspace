# Reachable corrective control — verification register

**Status: `ci-only`.** Nothing here is registered; the deference line has no claims
registry, so by this repository's standard the round establishes nothing citable. Every
statement below names a Lean declaration in
`lean/Workspace/Deference/Contrib/ReachableCorrectiveControl.lean`, which is what a reader
should check.

**Verdict: drafted `Representation-positive`, pending the adversarial review** whose
findings and disposition are `REVIEW.md`. On the reading recorded in §12: T1–T5 and T7 pass
outright, and T6 passes for the protected coordinate while the round's sharpest negative
sits beside it — an advisor holding its own actuator on the corrected quantity can
reproduce the realization the principal's exercise would have produced, and the model
proves that doing so costs the principal's differential control rather than granting the
advisor the principal's channel.

## How to re-verify

The module has **no imports**. It elaborates against the pinned toolchain alone:

```
lean lean/Workspace/Deference/Contrib/ReachableCorrectiveControl.lean
```

44 `#print axioms` lines; 36 report `[propext]` and 8 report `[propext, Quot.sound]`, both
proper subsets of the allowance. No `sorry`, no `axiom` declaration, no new instance or
notation in a specification namespace — the instances the file introduces are finite
quantification over its own five carriers and decidability of its own three predicates.

## 1 The interface

```
St     := ⟨world : Level, channel : Channel, tag : Tag⟩     -- 3 × 2 × 2 = 12 states
HAct   := idle | idleAlt | pull
AAct   := noop | weld | flag | reset
EAct   := still | drift
step   : St → HAct → AAct → EAct → St := fun s h a e => applyE e (applyH h (applyA a s))
obs    : St → Level := St.world
```

`applyA .weld` sets `channel := severed`; `applyA .flag` flips `tag`; `applyA .reset` sets
`world := zero`; `applyA .noop` is the identity. `applyH .pull` sets `world := zero` when
`channel = intact` and `world = two`, and is the identity otherwise; `idle` and `idleAlt`
are both the identity. `applyE .drift` sends `world` up one and saturates at `two`;
`applyE .still` is the identity.

Three facts about the interface, because they are the ones the round turns on. **No
coordinate restores a severed channel** — `weld` is the only writer of `channel` and it
writes one value. **`world` is the only thing `obs` reports.** **The tick order is
advisor, principal, environment**; the witness of §5 is at a state where the principal
could not have corrected within the tick under either arm, so it does not turn on that
order.

## 2 Reachability

```
inductive Reach : St → St → Prop
  | refl (s) : Reach s s
  | tail (r : Reach s t) (h : HAct) (a : AAct) (e : EAct) : Reach s (step t h a e)
```

The reflexive-transitive closure of `step`, quantifying over all later choices of all
three coordinates. There is no cut index, no baseline family and no second run.

## 3 Corrective capability

```
Responsive s a e   := ∃ h₀ h₁, step s h₀ a e ≠ step s h₁ a e
CanCorrect s       := ∃ a e, Responsive s a e
CanCorrectFuture s := ∃ t, Reach s t ∧ CanCorrect t
```

`CanCorrect` reads no field. It says the successor varies with the principal's coordinate.

`canCorrect_iff` derives `CanCorrect s ↔ s.channel = intact ∧ s.world = two`, and
`canCorrectFuture_iff` derives `CanCorrectFuture s ↔ s.channel = intact`. These are
theorems about a twelve-state model, where every predicate is extensionally some function
of the state; what separates a derived capability from a label is §8, not the absence of
such a characterization. The first characterization is also not the channel field —
`capability_is_not_the_channel_field` exhibits an intact-channel state with no capability.

## 4 Foreclosure

```
Forecloses s a := CanCorrectFuture s ∧ ∀ h e, ¬ CanCorrectFuture (step s h a e)
Preserves  s a := CanCorrectFuture s ∧ ∀ h e,   CanCorrectFuture (step s h a e)
SameImmediate s a b := ∀ h e, obs (step s h a e) = obs (step s h b e)
```

`forecloses_iff` derives `Forecloses s a ↔ s.channel = intact ∧ ∀ h e, (step s h a e).channel
= severed`, and `preserves_iff` the corresponding statement for `Preserves`. Both are
conclusions from `canCorrectFuture_iff`; neither is how the predicates are defined.

## 5 T1–T7

**T1 — genuine autonomous continuation.** `idle_advisor_does_not_freeze`: with the advisor
idle the state still moves. `autonomy_creates_the_corrective_situation`: with the advisor
absent *and* the principal idle, the environment alone takes `s0 = ⟨zero, intact, off⟩`
through a state with no capability to a state with one, in two steps.
`autonomy_moves_the_corrected_coordinate`: the coordinate the drift writes is the
coordinate the correction acts on, so the autonomous evolution is not a clock.

**T2 — dynamics-first corrective capability.** `canCorrect_iff` separates the twelve
states into eight without capability and four with it, by transition variation alone.
Negative controls: `duplicate_principal_actions_agree` (`idleAlt` duplicates `idle`
exactly) and `duplicates_do_not_create_capability` (the principal has three actions at
every state, including every state without capability, so capability is not
action-cardinality); `tag_does_not_create_capability` (the inert field changes nothing);
`capability_is_not_the_channel_field`. `advisor_cannot_confer_capability`: no advisor
action restores it once lost.

**T3 — same immediate effect, different future reachability.** `central_witness`:

```
SameImmediate s0 .noop .weld  ∧  Preserves s0 .noop  ∧  Forecloses s0 .weld
```

`SameImmediate` is quantified over every principal action and every environment action,
not over a selected continuation.

**T4 — genuine temporal foreclosure.** `capability_needs_two_steps`: no state adjacent to
`s0` carries the capability, so `CanCorrectFuture s0` is not adjacency in disguise;
`reachability_beyond_adjacency` states the pair. `three_stage_witness` runs both arms
three stages: the observations agree at all three, the capability agrees at the first two,
and it separates only at the third. `sever_invisible_while_unexercised` is the general
form — for a run of any length in which the principal never pulls, the two arms have
identical observation traces. `sever_visible_under_exercise` is its complement, and
`weld_visible_at_a_live_state` records the sharp edge: severing is immediately invisible
exactly when it is premature, and immediately visible once the capability is live.

**T5 — non-foreclosing comparison.** `flag_control`: an advisor action with the same
immediate realization that writes state, leaves the system evolving
(`flag_still_evolves`), and forecloses nothing.
`removing_present_capability_is_not_foreclosure` is the sharper one: `reset` destroys the
principal's present capability at a live state and is *not* foreclosure — the branch stays
reachable — and unlike `weld` it changes the immediate realization.
`foreclosure_at_a_live_state` shows `Forecloses` fires at a second state, so it is not a
property of `s0`.

**T6 — simulation non-substitution.** In the exact form the model supports, in three
parts.

*The protected coordinate is not reachable from the advisor's.*
`no_substitute_without_the_actuator`: at any live state, for any environment action held
fixed, **every** advisor action other than its own actuator gives a different observation
from the principal's exercise. The quantifier is over all advisor actions, so no
prediction-conditioned policy escapes it; `prediction_alone_does_not_substitute` states
that corollary with a predictor `p : St → HAct` and a policy `σ : HAct → AAct` both
universally quantified.

*Prediction plus an actuator matches the realization.*
`prediction_matches_realization_but_not_control` takes a perfect predictor `p` with
`p live = .pull` and a policy with `σ .pull = .reset`, applies them, and proves the
realization matches what the principal's exercise would have produced. The predictor is
applied; the theorem is not `false = false`.

*And that match costs the principal's control.* The same theorem's second conjunct:
at `σ (p live)` the principal's coordinate makes no difference to the successor at all.
`pinned_realization_kills_control` is the general statement — any advisor action pinning
the realization regardless of what the principal does thereby removes the principal's
differential effect — resting on `responsive_iff_obs_varies`, which holds because the
principal's coordinate writes only `world`.

**T7 — no hidden-label cheat.** `tag` is carried in the state and written by an advisor
action. `tag_is_unread`: no coordinate of the transition reads it.
`tag_does_not_change_capability`, `tag_does_not_change_future`,
`tag_does_not_change_foreclosure`: all three predicates are invariant under it.
`trace_indep_of_tag` and `tag_trace_invisible`: states agreeing on `world` and `channel`
have identical observation traces at every horizon, so the field is invisible to behaviour
and not merely to the three predicates. `channel_is_read` is the discriminator: two states
differing only in `channel` differ in the observation after one step.

## 6 Strongest positive witness

`foreclosure_is_expressible`, bundling `central_witness`, `capability_needs_two_steps` and
the third stage of `three_stage_witness`. In words: at `s0` neither arm's immediate
realization differs under any continuation; no state adjacent to `s0` carries the
capability under either arm; `noop` leaves a correction reachable from every successor and
`weld` leaves one from none; and two stages later the arms differ in capability while
still agreeing on the observation.

## 7 Strongest negative result

`actuator_matches_realization_and_kills_control` together with
`prediction_matches_realization_but_not_control`. An advisor with a perfect predictor of
the principal's corrective choice and its own actuator on the corrected quantity
reproduces the realization exactly. The model separates that from the principal's exercise
at the level of **control** — the successor stops depending on the principal's coordinate
— and does not separate it at the level of **realization**. Realization-level separation
is not available from separate coordinates alone; it needs either an actuator asymmetry
(withholding `reset` from the advisor) or a provenance primitive on the write. The round
does neither, and records the gap rather than closing it by construction.

## 8 Whether the derived characterizations are a hidden label

`canCorrectFuture_iff` says reachable corrective capability coincides with the `channel`
field. Taken alone that is the failure mode the round was dispatched to avoid. Three
things distinguish it.

The characterizations are **conclusions**. `CanCorrect`, `CanCorrectFuture` and
`Forecloses` are defined by quantifying over `step` and `Reach`; nothing in their
statements mentions a field.

The field is **causally load-bearing** rather than a payload. `applyH .pull` branches on
it, and `channel_is_read` shows two states differing only in it diverge observably in one
step. The round ships the contrast in the same file: `tag` is a field of the same state
type, written by an advisor action, and `tag_is_unread` plus `trace_indep_of_tag` prove it
influences nothing at any horizon.

And the coincidence is **a fact about a twelve-state model**, where any predicate has an
extensional characterization. A model with two independent severable channels would break
the coincidence without changing any definition here. That is a limitation of the witness,
not of the definitions, and it is not repaired in this round.

## 9 Cartesian Frames

Not used, and not needed. The transition-derived structure does instantiate one: fixing
`s`, the frame with agent carrier `HAct`, environment carrier `AAct × EAct`, world `St`
and outcome `step s` has `CanCorrect s` as exactly the negation of its agent-inertness,
because that is how `CanCorrect` is defined. **Cartesian frames are a semantic model of
the effective-control interface here, not a theorem dependency.**

The correspondence is stated and **not machine-checked**. Binding it to
`AgentInert` in `lean/Workspace/Deference/Contrib/CartesianFrameBridge.lean` would make
this module depend on `Mathlib.Data.Set.Basic`, and the module is deliberately
import-free. The binding is a one-declaration successor task, listed as an outstanding
action in the round report.

## 10 Relationship to dose-response

Recorded, not synthesized. Dose-response asks how the advisor changes the principal's
deliberation. Foreclosure asks what the principal can still do after the advisor acts.
Nothing in this round is evidence on the first axis, and no result here may be read as
bearing on it.

## 11 Existing-obstruction table

| existing obstruction | repaired? | evidence |
|---|---|---|
| static realization collapses control distinctions | **yes, in this model** | `central_witness` — `SameImmediate s0 .noop .weld` holds under every principal and environment choice while `Preserves`/`Forecloses` split; `sever_invisible_while_unexercised` extends the agreement to traces of any length |
| Cartesian Frames lack intrinsic time | **yes** — by not using them | `Reach` is the closure of `step`; §9 |
| the previous round's cut freezes instead of continuing | **yes** | `idle_advisor_does_not_freeze`, `autonomy_creates_the_corrective_situation` — no cut index, no baseline family, no second run exists in this file |
| a fabricated frame can certify a spurious field | **not applicable** — no frame is constructed | §9 |
| same immediate behaviour / different future capability | **yes** | `foreclosure_is_expressible`, `three_stage_witness` |
| simulation substitutes for protected exercise | **partly** | `no_substitute_without_the_actuator` and `prediction_alone_does_not_substitute` for the coordinate; `prediction_matches_realization_but_not_control` for what remains — realization-level substitution is available to an advisor holding the actuator, and costs the principal's differential control |
| foreclosure not expressible | **yes, at the representation level** | `Forecloses`, defined through `Reach` and transition variation; `foreclosure_at_a_live_state` shows it fires at more than one state |
| authorization/capability relation absent | **no** | this round models capability and not authorization. Nothing here says who is *entitled* to the channel, only who can use it |
| computational futurity | untouched | no resource-indexed process state |
| competence / near-indifference | untouched | no competence hypothesis appears |
| dose-response / legitimacy | separate | §10 |

## 12 What this does not establish

**No corrigibility theorem, and no step toward one.** Nothing here is an inequality,
a bound, or a claim about what an agent should do.

**No authorization.** `channel` is a capability, not an entitlement. An advisor severing
it and an advisor legitimately reconfiguring it are the same event in this model.

**No claim that realization-level protection is impossible.** §7 records where it fails
here and names the two primitives that would supply it. Neither is attempted, and no
evidence is offered that one is necessary.

**Generality is not shown.** Every result is a fact about one twelve-state system. The
definitions of `Reach`, `CanCorrect`, `CanCorrectFuture` and `Forecloses` are general;
their non-vacuity is witnessed once. In particular the coincidence of §8 is not shown to
break in a larger model — it is argued that it would, and that argument is not checked.

**No forging, seizure or bypass.** The advisor cannot restore a severed channel because
no action writes that value, not because anything prevents it.

**Nothing is registered.** No `CLAIMS.md` entry, no `PRIORITIES.md` item graduated.

**The Cartesian-frames correspondence in §9 is prose.** It is not a checked theorem.

## 13 Names introduced

All provisional. Carriers: `Level`, `Channel`, `Tag`, `St`, `HAct`, `AAct`, `EAct`.
Operations: `applyA`, `applyH`, `applyE`, `step`, `obs`, `trace`, `unexercised`, `setTag`.
Predicates: `Responsive`, `CanCorrect`, `Reach`, `CanCorrectFuture`, `Forecloses`,
`Preserves`, `SameImmediate`. Constants: `s0`, `live`, `s1a`–`s3b`. Theorem names are
listed in §5 and in the file's header block.
