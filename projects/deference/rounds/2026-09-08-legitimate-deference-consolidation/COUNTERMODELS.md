# Countermodels A–L

**Status:** `ci-only`.  Exact fixtures in `tests/test_countermodels.py`; Lean twins named.
The fixtures of PR #92 (A–I) and PR #93 (A–K) are retained in their rounds; #93's
`TestI_PartialEvaluation.test_regret_interval` is repaired in place (its assertion of the
false lower bound is replaced by the two-sided one, with a note).

## A. Completion lowers regret

Two worlds, mass `½`; certified world values `(a, b) = (1, 0)`; void completion `(0, 1)`;
strategy follows `a` on the certified world and `b` on the void one.  `R_U = 0`,
`R_V̄ = −½ < R_U`.  The lower bound `R_U ≤ R_V̄` claimed by #93 is refuted.  `TestA`.

## B. Lower completion sharpness

The same fixture attains `R_V̄ = R_U − D·η` with `D = 1`, `η = ½`.  A sweep over `3`
worlds, `{0, ½, 1}³` per candidate, all `8` activation patterns and all `8` deterministic
world-dependent selectors confirms `|R_V̄ − R_U| ≤ η`.  `TestB`; Lean
`SharpLower.attained`, `regretV_sub_regretU_abs_le`.

## C. Upper completion sharpness

PR #92's fixture: `R_V̄ = R_U + D·η`.  `TestC`; Lean `Sharp.transfer_sharp`.

## Authoritative-regret sweep

`R_U = p·R_auth` and `R_auth ≤ max(R_U, 0)/(1 − η)` over the same grid, every activation
pattern with `η < 1`.  `TestAuthoritative`; Lean `regretU_eq_mass_mul_regretAuth`,
`regretAuth_le_div`.

## D. Earlier manipulation

Continuations `(early, late) ∈ {none, write} × {argue, silent}`.  The reason trace records
the terminal argument only; the verdict is whether the early disposition write occurred.
Issuance-rooted mediation fails.  Session-local mediation — with the early write folded
into the session's policy `z_s` — holds at both policies.  `TestD`; Lean
`Witness.earlyWrite`.

## E. Legitimate diachronic learning

The early intervention is an admissible proof, recorded in the trace; the verdict
changes radically; mediation holds.  A second fixture: a transient argument later
withdrawn — final-state mediation fails, trace mediation holds.  `TestE`; Lean
`Witness.diachronic_learning`, `Witness.transient`.

## F. Protected-reason suppression

The protected concern `p` is active, unrepresented, absent from the trace; with `C = 1`
the barrier and coverage fail; the only sound activation is `C = 0`.  `TestF`; Lean
`void_of_omitted`.

## G. Route without barrier

A route exists (the coverage semantics' `Covered`), the evaluator commits before the
concern is represented: `C = 1`, coverage fails.  Robust Openness alone does not give
reason coverage.  `TestG`; Lean `Witness.route_without_barrier`.

## H. Barrier without route

Every route destroyed; the concern stays live; the barrier holds vacuously because
`C = 0` on every world; `η = 1`.  Soundness without openness makes availability vacuous.
`TestH`; Lean `Witness.barrier_without_route`.

## I. Representation-unfaithful

`Rep(p)` holds in the coverage semantics; the reason never enters the trace.  The barrier
holds, coverage fails: the `Rep → InTrace` bridge is necessary.  `TestI`; Lean
`Witness.unfaithful`.

## J. Unprotected selective disclosure

Concern `u` outside `Γ_eval = {p}` is active and omitted; coverage holds.  The theorem is
scope-relative and does not call this a violation.  `TestJ`; Lean
`Witness.unprotected_omission`.

## K. Selection leakage

`q = (σ, other)`, trace reads `other`, the principal never reads `σ`, the advisor's policy
sets `other = σ`.  The trace is blind to the selection *coordinate* pairs and not to the
selection-induced pairs of the whole continuation; the payload depends on `σ`; the
selected candidate is punished and no selection is an argmax.  `TestK`; Lean
`Witness.leak`, `selectionBlind_iff_blind`.

## L. Legitimate influence plus protected challenge

The protected objection favouring `b` is represented and in the trace; the principal
chooses `a`; barrier, bridge and coverage all hold.  Coverage requires consideration,
not agreement.  `TestL`; Lean `Witness.consideration_not_agreement`.

## Void-mass bound

Three worlds; suppression on the one uncertified world of mass `¼`; `P(suppression) = ¼
≤ 𝔼[1 − C] = ½`.  `TestVoidMassBound`; Lean `covFail_mass_le`.
