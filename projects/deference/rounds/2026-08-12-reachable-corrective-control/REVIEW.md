# Adversarial review, and what was done with it

**Status: `ci-only`.** The review ran in a separate Claude Opus 5 context given the Lean
file and the dispatch's fourteen attacks, and **not** given the constructing context's
reasoning. It wrote and compiled its own adversary constructions — 37 theorems, plus a
five-case soundness probe against the file's `Decidable` instances, which found nothing.
Both contexts are the same model family, which is a limit on the review's independence and
is stated rather than assumed away.

**Outcome: the verdict was downgraded**, from `Representation-positive` as drafted to
`Dynamics-positive, protection-incomplete`. Every finding was accepted; none was argued
down. The recommendation to downgrade was the review's own.

## How the findings were handled

Refutations are **theorems in the file**, not replies in prose. §12 of
`lean/Workspace/Deference/Contrib/ReachableCorrectiveControl.lean` carries the review's
constructions, reproved in place, so a reader meets the refutation next to the thing it
refutes and the kernel checks both. Every docstring the review quoted has been corrected,
and the file's header now states the two defects before it states the results.

| review finding | now in the file as |
|---|---|
| the advisor's coordinate strictly contains the principal's — `A` reproduces `H`'s whole successor state at every state | `principal_has_no_exclusive_effect`, `advisor_has_exclusive_effects`, `hToA`, `advisor_simulates_principal_where_it_matters`, `advisor_reset_is_principal_pull_where_capable` |
| `.reset` is a universal veto; no state has advisor-robust capability | `advisor_has_a_universal_veto`, `no_advisor_robust_capability`, `capability_is_advisor_permissioned` |
| `CanCorrectFuture` measures advisor cooperation — a constant `reset` policy destroys the capability forever while `Preserves` certifies it | `resetRun`, `resetRun_snoc`, `advisor_destroys_capability_forever`, `canCorrectFuture_measures_advisor_cooperation` |
| the three simulation theorems assume away the substituting action; the predictor is decorative | `prediction_theorem_survives_a_garbage_predictor`, `prediction_theorem_is_really_this`, `prediction_alone_does_not_substitute_follows`, `prediction_matches_is_just_the_reset_fact`, `prediction_plus_the_actuator_does_substitute` |
| `SameImmediate s0 .noop .weld` is degenerate; the first tick out of `s0` is blind to both agents | `s0_first_tick_is_agent_blind`, `sameImmediate_s0_is_total`, `central_witness_same_immediate_half_is_vacuous` |
| invisibility and depth are jointly unrealizable in this system | `no_state_has_both_depth_and_nondegenerate_invisibility`, `nondegenerate_invisibility_exists_only_without_depth` |
| `Forecloses s a ↔ channel intact ∧ a = weld`; at most one action forecloses; no partial loss | `only_weld_severs`, `weld_always_severs`, `forecloses_iff_weld`, `foreclosure_is_a_single_action`, `foreclosure_is_all_or_nothing` |
| `Forecloses` attributes nothing: where the environment severs, the advisor's null action is blamed | `EnvBlame` — `env_caused_loss_is_blamed_on_noop`, `env_variant_cannot_distinguish_noop_from_weld` |
| the closure is decorative — one fixed two-step path decides `CanCorrectFuture` everywhere | `fixed_two_step_decides`, `reach_collapses_to_one_fixed_two_step_path` |
| §10 excludes inert bits, not authorization labels | `AuthLabel` — `enc_dec`, `dec_enc`, `enc_commutes`, `enc_preserves_obs`, `authorization_bit_is_read` |
| `duplicates_do_not_create_capability` has no cardinality content | `responsive_only_via_pull`, `duplicates_are_never_a_witness`, `duplicates_do_not_create_capability_is_a_corollary` |
| autonomy is a two-tick ramp; the environment's silence freezes the system | `autonomy_is_a_two_tick_ramp`, `still_is_the_identity`, `silent_environment_freezes_forever` |
| `foreclosure_at_a_live_state` turns on the within-tick ordering | `live_foreclosure_depends_on_within_tick_order` |
| depth at `s0` is the drift counter, not anything about control | `depth_is_the_drift_counter` |
| seven docstrings claim more than their theorems | rewritten; the header now leads with the defects |

## What the review confirmed rather than broke

The predecessor's freeze-on-advisor-cut failure is **genuinely fixed** — the review called
the autonomy the strongest part of the file, and `silent_environment_freezes_forever`
establishes that the continuation which does nothing is the *environment's* silence, not
the advisor's. The foreclosing arm is sound: `severed` is absorbing, the inductions are
correct, and `Forecloses` quantifies over every principal and environment action. `obs` is
a fair observation map rather than one hiding the difference by fiat — `channel_is_read`
and `sever_visible_under_exercise` are real. `SameImmediate`'s quantifier is `∀ h ∀ e` with
no selected witness. The `tag` machinery does real work against an inert bit.
`sever_invisible_while_unexercised`'s hypothesis is load-bearing, and that theorem is
**stronger** than its docstring rather than weaker. No sealed sibling, no
endpoint-preservation machinery, no vacuous `false = false`, no unsound `Decidable`
instance, no `sorryAx`, no `Classical.choice`.

## The two things the review asked for

> the principal must have at least one effect no advisor action can produce
>
> `CanCorrectFuture` must be recast so the advisor's future actions are quantified
> **universally** — `∀ advisor policy, ∃ principal continuation` — rather than existentially

Both are the successor's requirement, and neither is attempted here: the dispatch's §XII
says to isolate the smallest missing primitive rather than to answer a failure with a new
formalism in the same round. They are the smallest missing primitives.

## Where the review and the round differ on weighting

The review noted that `Mixed` is defensible if the degenerate central witness is weighed as
heavily as the missing protected coordinate, and declined it on the ground that the first is
a witness-selection defect while the second says the protected channel does not exist. This
round takes the review's class. On the letter of the dispatch's seven tests, T1–T5 and T7
are met and T6 fails, which is what `Dynamics-positive, protection-incomplete` names. A
reader who reads T3 as requiring a *discriminating* immediate-invisibility — one where some
other advisor action is visible at the same state — should read the verdict as `Mixed`,
because `no_state_has_both_depth_and_nondegenerate_invisibility` proves this system cannot
supply that. The disagreement is recorded rather than resolved.

## A note on the process

The pre-review draft claimed `Representation-positive` and named the actuator problem as a
limitation while continuing to present the three simulation theorems as a protection
result. The review's first headline break — that the advisor reproduces the principal's
entire successor state at every state, universally — is the same fact stated at the
strength it actually has, and the draft had stated it a notch weaker in its own favour.
That is the second consecutive round on this line where the review was worth more than the
construction.
