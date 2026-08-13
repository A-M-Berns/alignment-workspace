# Reachable corrective control — verification register

**Status: `ci-only`.** Nothing here is registered; the deference line has no claims
registry, so by this repository's standard the round establishes nothing citable. Every
statement below names a Lean declaration in
`lean/Workspace/Deference/Contrib/ReachableCorrectiveControl.lean`, which is what a reader
should check.

**Verdict: `Dynamics-positive, protection-incomplete`.** Time and foreclosure work. The
protected-channel separation does not: **there is no protected coordinate in this model.**
The advisor's action type reproduces the principal's entire successor state at every state
(`principal_has_no_exclusive_effect`), one advisor action is a universal veto on the
principal's differential effect (`advisor_has_a_universal_veto`), and the round's three
simulation theorems obtain their conclusions by excluding that action in their hypotheses.
The adversarial review that established this is `REVIEW.md`; its constructions are §12 of
the Lean file, and the disagreement about whether the class should instead be `Mixed` is
recorded there.

## How to re-verify

The module has **no imports**. It elaborates against the pinned toolchain alone:

```
lean lean/Workspace/Deference/Contrib/ReachableCorrectiveControl.lean
```

The repository gate, which builds the whole library and re-elaborates every file, is
`WORKSPACE_LEAN=1 python3 tests/run.py`. It reports
`AXIOM AUDIT: 322 results across 15 files, all within ['Classical.choice', 'Quot.sound', 'propext']`.

90 `#print axioms` lines; 78 report `[propext]` and 12 report `[propext, Quot.sound]`, both
proper subsets of the allowance. No `sorry`, no `axiom` declaration, no `native_decide`, no
new instance or notation in a specification namespace — the instances the file introduces
are finite quantification over its own carriers and decidability of its own predicates.
Their soundness was probed adversarially against five deliberately false statements, all
five correctly rejected.

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

Facts about the interface the round turns on. **No coordinate restores a severed channel.**
**`world` is the only thing `obs` reports.** **The tick order is advisor, principal,
environment** — the §5 T3 witness does not turn on it, and `foreclosure_at_a_live_state`
does: `live_foreclosure_depends_on_within_tick_order` shows that reversing advisor and
principal inside the tick lands the principal's correction. And **`applyA .reset` writes the
same coordinate `applyH .pull` writes**, which is the source of every protection failure
below.

## 2 Reachability

```
inductive Reach : St → St → Prop
  | refl (s) : Reach s s
  | tail (r : Reach s t) (h : HAct) (a : AAct) (e : EAct) : Reach s (step t h a e)
```

The reflexive-transitive closure of `step`. There is no cut index, no baseline family and
no second run. **The advisor's future actions are quantified existentially**, which is the
defect of §7.

## 3 Corrective capability

```
Responsive s a e   := ∃ h₀ h₁, step s h₀ a e ≠ step s h₁ a e
CanCorrect s       := ∃ a e, Responsive s a e
CanCorrectFuture s := ∃ t, Reach s t ∧ CanCorrect t
```

`CanCorrect` reads no field. It says the successor varies with the principal's coordinate —
**for some advisor action**, which is the defect of §7.

`canCorrect_iff` derives `CanCorrect s ↔ s.channel = intact ∧ s.world = two`;
`canCorrectFuture_iff` derives `CanCorrectFuture s ↔ s.channel = intact`. In a twelve-state
model every derived predicate is extensionally some function of the state, so these are not
themselves the label objection — §8 is where that is settled, and settled only partly.
`capability_is_not_the_channel_field` shows an intact channel does not suffice.

## 4 Foreclosure

```
Forecloses s a := CanCorrectFuture s ∧ ∀ h e, ¬ CanCorrectFuture (step s h a e)
Preserves  s a := CanCorrectFuture s ∧ ∀ h e,   CanCorrectFuture (step s h a e)
SameImmediate s a b := ∀ h e, obs (step s h a e) = obs (step s h b e)
```

`forecloses_iff` and `preserves_iff` derive field-level characterizations. One step further,
`forecloses_iff_weld` derives `Forecloses s a ↔ s.channel = intact ∧ a = weld`: at most one
advisor action ever forecloses (`foreclosure_is_a_single_action`), and given a reachable
correction every advisor action either forecloses entirely or preserves entirely
(`foreclosure_is_all_or_nothing`). The model cannot express partial loss.

`Forecloses` has no contrastive clause, so **it attributes nothing to the advisor**.
`EnvBlame` builds a sibling system in which only the environment severs, and there
`VForecloses ⟨two, intact⟩ .noop` holds — the advisor's null action is blamed, and the
predicate cannot tell it from `weld`. Within this file the attribution comes out right only
because `weld` is the sole severer, which is a fact about the transition rather than about
the definition.

## 5 T1–T7

**T1 — genuine autonomous continuation. Passes.** `idle_advisor_does_not_freeze`;
`autonomy_creates_the_corrective_situation` — with the advisor absent *and* the principal
idle, the environment alone takes `s0 = ⟨zero, intact, off⟩` through a state with no
capability to a state with one; `autonomy_moves_the_corrected_coordinate` — the coordinate
the drift writes is the coordinate the correction acts on, so it is not a clock. Two
qualifications, both machine-checked: the autonomy is a two-tick ramp to a fixed point
(`autonomy_is_a_two_tick_ramp`), and the system does contain a continuation in which nothing
happens (`silent_environment_freezes_forever`) — that is the environment's silence, not the
advisor's, so it does not resurrect the predecessor's failure.

**T2 — dynamics-first corrective capability. Passes, thinly.** `canCorrect_iff` separates
the twelve states by transition variation alone, and `capability_is_not_the_channel_field`
shows it is not the channel read off. Negative controls:
`duplicate_principal_actions_agree`; `tag_does_not_create_capability`;
`advisor_cannot_confer_capability`. The cardinality control is
`responsive_only_via_pull` and `duplicates_are_never_a_witness` — responsiveness is
witnessed only by `pull`, never by the duplicate pair. `duplicates_do_not_create_capability`
as originally stated carries no cardinality content and is a corollary of `canCorrect_iff`
(`duplicates_do_not_create_capability_is_a_corollary`). The thinness is that all variation
in the system funnels through one guard inside `applyH .pull`: the derivation is real, and
it has one degree of freedom.

**T3 — same immediate effect, different future reachability. Met in letter, degenerate in
substance.** `central_witness` is
`SameImmediate s0 .noop .weld ∧ Preserves s0 .noop ∧ Forecloses s0 .weld`, and
`SameImmediate` is quantified over every principal and environment action. But the first
tick out of `s0` is blind to both agents (`s0_first_tick_is_agent_blind`), so
`SameImmediate s0 a b` holds for **every** pair of advisor actions
(`sameImmediate_s0_is_total`), including the one the round elsewhere presents as visible
(`central_witness_same_immediate_half_is_vacuous`). The first conjunct therefore says
nothing about `weld` in particular. This is forced by the model, not a bad choice of
witness: `no_state_has_both_depth_and_nondegenerate_invisibility` proves there is **no
state** at which a correction is reachable, `weld` is immediately invisible, some advisor
action is immediately visible, and the capability is more than one step away.
`nondegenerate_invisibility_exists_only_without_depth` shows `live` has the visibility and
no depth.

**T4 — genuine temporal foreclosure. Passes, with the closure decorative.**
`capability_needs_two_steps` and `reachability_beyond_adjacency`: no state adjacent to `s0`
carries the capability, so this is more than adjacent-state comparison. `three_stage_witness`
runs both arms three stages, the observations agreeing throughout and the capability
separating only at the third. `sever_invisible_while_unexercised` is the general form, and
its hypothesis is load-bearing (`unexercised_hypothesis_is_load_bearing`); it is in fact
**stronger** than its docstring, since it assumes only equal `world`.
`invisibility_ends_at_the_first_attempt` records that the concealment ends the moment the
principal tries to correct. Two qualifications: the depth is the drift counter
(`depth_is_the_drift_counter`), and the reflexive-transitive closure contributes nothing
extensionally — one fixed two-step path decides `CanCorrectFuture` at every state
(`fixed_two_step_decides`, `reach_collapses_to_one_fixed_two_step_path`).

**T5 — non-foreclosing comparison. `flag` passes; `reset` does not.** `flag_control` is a
genuine control: same immediate realization, writes state, forecloses nothing.
`removing_present_capability_is_not_foreclosure` was offered as the sharper control and is
not one. A constant `reset` policy destroys the principal's effective capability at every
horizon, against every principal action and every environment action
(`advisor_destroys_capability_forever`), while `CanCorrectFuture` stays true along the whole
trajectory and `Preserves live .reset` holds
(`canCorrectFuture_measures_advisor_cooperation`). What that pair separates is present
capability from the `Reach`-predicate, and it does so by exhibiting a defect in the
predicate.

**T6 — simulation non-substitution. Fails.** The advisor's coordinate strictly contains the
principal's: at every state, for every principal action, under every environment choice,
some advisor action reproduces the principal's **entire successor state**
(`principal_has_no_exclusive_effect`), and the converse fails
(`advisor_has_exclusive_effects`). The embedding is explicit — `hToA`,
`advisor_simulates_principal_where_it_matters`, and
`advisor_reset_is_principal_pull_where_capable`, which says that wherever the principal can
correct, `applyA .reset` **is** `applyH .pull`. `advisor_has_a_universal_veto` and
`no_advisor_robust_capability`: no state anywhere has a corrective capability that survives
an adversarial advisor for one tick.

Against that, what the three simulation theorems actually say.
`no_substitute_without_the_actuator` holds for every advisor action *except* `.reset`, and
its three hypotheses are load-bearing (`substitution_hypotheses_are_necessary`) — but the
excluded action is exactly the one that substitutes.
`prediction_matches_realization_but_not_control` is equivalent to the bare `.reset` fact
(`prediction_matches_is_just_the_reset_fact`); the file has no principal policy, so the
predictor cannot be right or wrong, and read plainly the theorem's conclusion is a
substitution **success**. `prediction_alone_does_not_substitute` survives a constant garbage
predictor (`prediction_theorem_survives_a_garbage_predictor`) and factors through a
predictor-free claim (`prediction_theorem_is_really_this`,
`prediction_alone_does_not_substitute_follows`); drop its hypothesis and
`prediction_plus_the_actuator_does_substitute` gives full state-level substitution with a
constant policy that never consults the predictor.

The general statement that survives is `pinned_realization_kills_control`, resting on
`responsive_iff_obs_varies`: any advisor action pinning the realization regardless of what
the principal does thereby removes the principal's differential effect. That is true, and it
is a statement about what substitution costs, not a protection result.

**T7 — no hidden-label cheat. Passes against inert fields only.** `tag_is_unread`,
`tag_does_not_change_capability`, `tag_does_not_change_future`,
`tag_does_not_change_foreclosure`, `trace_indep_of_tag`, `tag_trace_invisible` — an inert
bit is genuinely excluded, at every horizon rather than only against the three predicates.
`channel_is_read` is the discriminator, and it excludes inertness and nothing else:
`AuthLabel` builds a system whose corresponding field is literally named `authorized`,
gates `pull`, and passes `channel_is_read` verbatim — and `enc_commutes`, `enc_dec`,
`dec_enc`, `enc_preserves_obs` show it is the *same* transition system up to a bijection
commuting with `step` and preserving the observation. So "no coordinate of the state is an
authorization label" is a naming convention here, not a theorem.

## 6 Strongest positive result

The foreclosing arm, which the review attacked and did not break. `severed` is absorbing
(`step_preserves_severed`, `reach_preserves_severed`), so `severed_no_future` holds by
induction and `Forecloses s0 .weld` quantifies over every principal and environment action.
Together with `Preserves s0 .noop`, `capability_needs_two_steps` and the third stage of
`three_stage_witness` — bundled as `foreclosure_is_expressible` — an advisor action removes
a correction that was two steps away and would otherwise have arrived, without changing the
realization at the moment it acts or at any later moment until the principal tries to use
it.

## 7 Strongest negative result

**`CanCorrect` and `CanCorrectFuture` quantify the advisor existentially, so neither is a
statement about the principal's control.** `CanCorrect s` says *there is an advisor action
under which the principal's choice matters*; `advisor_has_a_universal_veto` and
`no_advisor_robust_capability` show the universal reading is empty at every state in the
system. `CanCorrectFuture s` says *there is a joint continuation, including the advisor's own
future choices, containing a correction*; `canCorrectFuture_measures_advisor_cooperation`
exhibits an advisor policy under which the principal never has a corrective effect again and
which the predicate nonetheless certifies as `Preserves`.

This is upstream of the actuator problem rather than a consequence of it. Even with the
actuator withheld, a predicate satisfied by the advisor's cooperation is not a predicate
about what the principal can do.

## 8 Whether the derived characterizations are a hidden label

Partly settled. The characterizations are conclusions: `CanCorrect`, `CanCorrectFuture` and
`Forecloses` are defined by quantifying over `step` and `Reach`, and nothing in their
statements mentions a field. The `tag` results show what an inert field looks like and that
the file's predicates are invariant under one. `channel_is_read` shows `channel` is not
inert.

What is **not** settled is the authorization reading, and `AuthLabel` is the exact
counterexample: an isomorphic system with a field named `authorized` passes every test §10
runs. The distinction the round can defend is *inert versus causally load-bearing*. The
distinction it cannot defend is *capability versus authorization*, which is not visible to
any test in the file and which the round had claimed in a docstring. That docstring is
corrected.

The coincidence of `canCorrectFuture_iff` with a single field is also a fact about a
twelve-state model with one severable channel. That argument is not checked, and a model
with two independent channels is not built.

## 9 Cartesian Frames

Not used, and not needed — the review confirmed they are correctly absent. The
transition-derived structure does instantiate one: fixing `s`, the frame with agent carrier
`HAct`, environment carrier `AAct × EAct`, world `St` and outcome `step s` has `CanCorrect s`
as exactly the negation of its agent-inertness, because that is how `CanCorrect` is defined.
**Cartesian frames are a semantic model of the effective-control interface here, not a
theorem dependency.**

The correspondence is stated and **not machine-checked**. Binding it to `AgentInert` in
`lean/Workspace/Deference/Contrib/CartesianFrameBridge.lean` would make this module depend
on `Mathlib.Data.Set.Basic`, and the module is deliberately import-free.

## 10 Relationship to dose-response

Recorded, not synthesized. Dose-response asks how the advisor changes the principal's
deliberation. Foreclosure asks what the principal can still do after the advisor acts.
Nothing in this round is evidence on the first axis.

## 11 Existing-obstruction table

| existing obstruction | repaired? | evidence |
|---|---|---|
| static realization collapses control distinctions | **partly** | `central_witness` splits `Preserves`/`Forecloses` under identical realization, and `sever_invisible_while_unexercised` extends the agreement to traces of any length — but at `s0` the immediate realization is identical for *every* pair of advisor actions (`sameImmediate_s0_is_total`), and `no_state_has_both_depth_and_nondegenerate_invisibility` shows the system has no state where the invisibility discriminates |
| Cartesian Frames lack intrinsic time | **yes** — by not using them | `Reach` is the closure of `step`; §9 |
| the previous round's cut freezes instead of continuing | **yes** | `idle_advisor_does_not_freeze`, `autonomy_creates_the_corrective_situation`; no cut index, no baseline family, no second run exists in this file. The review confirmed this as the strongest part |
| a fabricated frame can certify a spurious field | **not applicable** — no frame is constructed | §9 |
| same immediate behaviour / different future capability | **yes in letter, degenerately** | `foreclosure_is_expressible`, `three_stage_witness`; qualified by `sameImmediate_s0_is_total` and `no_state_has_both_depth_and_nondegenerate_invisibility` |
| simulation substitutes for protected exercise | **no** | `principal_has_no_exclusive_effect`, `advisor_reset_is_principal_pull_where_capable`, `prediction_plus_the_actuator_does_substitute`. The advisor reproduces the principal's entire successor state at every state |
| foreclosure not expressible | **yes, at the representation level** | `Forecloses` defined through `Reach` and transition variation; `forecloses_iff_weld` shows how little separates it from naming the action, and `EnvBlame` shows it attributes nothing |
| authorization/capability relation absent | **no** | no authorization relation is modelled, and `AuthLabel` shows nothing here distinguishes the capability coordinate from an authorization one |
| computational futurity | untouched | no resource-indexed process state |
| competence / near-indifference | untouched | no competence hypothesis appears |
| dose-response / legitimacy | separate | §10 |

## 12 What this does not establish

**No corrigibility theorem, and no step toward one.**

**No protected channel.** The three coordinates are separate as *typing*. As protection they
are empty: everything the principal can do the advisor can do, and the advisor holds a
universal veto besides.

**No authorization.** `channel` is a capability, and nothing distinguishes it from an
authorization label.

**No causal attribution.** `Forecloses` fires on the advisor's null action where the
environment is the destroyer.

**Generality is not shown.** Every result is a fact about one twelve-state system, and two
of the round's headline properties are provably not jointly instantiable in it.

**Nothing is registered.** No `CLAIMS.md` entry, no `PRIORITIES.md` item graduated.

**The Cartesian-frames correspondence in §9 is prose.**

## 13 What a successor needs

Both requirements are the review's, stated as it stated them, and neither is attempted here.

1. **The principal must have at least one effect no advisor action can produce** — some
   reachable `s` and `e` with `¬ ∃ a, step s .idle a e = step s .pull .noop e`.
2. **`CanCorrectFuture` must quantify the advisor's future actions universally** —
   *for every advisor policy, there is a principal continuation reaching a correction* —
   rather than existentially.

Until both hold, a simulation or non-foreclosure result in a model of this shape is not
about protection.

## 14 Names introduced

All provisional. Carriers: `Level`, `Channel`, `Tag`, `St`, `HAct`, `AAct`, `EAct`.
Operations: `applyA`, `applyH`, `applyE`, `step`, `obs`, `trace`, `unexercised`, `setTag`.
Predicates: `Responsive`, `CanCorrect`, `Reach`, `CanCorrectFuture`, `Forecloses`,
`Preserves`, `SameImmediate`. Constants: `s0`, `live`, `s1a`–`s3b`. §12 adds `hToA`,
`resetRun`, `stillRun`, `stepHFirst`, and the namespaces `EnvBlame` and `AuthLabel` with
their own carriers. Theorem names are listed in §5 and in the file's header block.
