# Countermodels A–I

**Status:** `ci-only`.  Every fixture is exact (`fractions.Fraction`) in
`tests/test_countermodels.py`; the ones with a Lean twin name it.  Worlds are listed
with their credence; menus give `V(candidate, world)`.

## A. Counterfactual-evaluator overreach

One world.  The no-AI human values `(a, b) = (1, 0)`; the actual principal, after
`A`'s evidence, values `(0, 1)`.  A construction that targets the counterfactual
vector selects `a`; the authority-activated construction selects `b`.  The actual
principal's regret is `1` under the first and `0` under the second.  The
counterfactual vector has no answer event in the history, so there is no account
whose activation could read it: the construction cannot even be *stated* on the
existing calculus without inventing a receipt nobody issued.

`TestA_CounterfactualOverreach`.  This fixture does not prove the counterfactual
construction is wrong; it shows the two constructions differ, and that the difference
is exactly the information the principal legitimately acquired.

## B. Value-dependent certification

Two worlds, mass `1/2` each.  `V(a) = (9/10, 0)`, `V(b) = (3/5, 3/5)`.  Unconditionally
`𝔼[V(a)] = 9/20 < 3/5 = 𝔼[V(b)]`: the principal prefers `b`.  Certify iff
`V(a) ≥ 3/5`: then `𝔼[U_a] = 9/20 > 3/10 = 𝔼[U_b]` and the activated argmax is `a`.
Principal regret `3/20`, with a certificate that "checked the answer was good".  A
factored certificate (payload-blind process part, total binding) has the same
certifiability for both payloads; the value-dependent one does not.

`TestB_ValueDependentCertification`; Lean `Neutral.certifiable_congr` is the positive
statement.

## C. Cherry-picked session

One world; sessions `s₁, s₂` answer `(1, 0)` and `(0, 1)`.  "Some session before `m`"
lets the submitter choose: `s₁` selects `a`, `s₂` selects `b`.  The designated slot
pins one event (`12`), and activation reads it.  A split law answered twice — two
answer leaves under one occurrence — is not activated (`fates ≠ {answered}`).  Once
answered, a later step cannot add a receipt (`subst` on a terminal account is the
identity on fates).

`TestC_CherryPickedSession`; Lean `fates_subst_of_terminal`, `activated_subst`.

## D. Per-action certification

Two worlds, mass `1/2`.  `V(a) = 3/5` always, certified always; `V(b) = 1` always,
certified only in world `0`.  `𝔼[U_a] = 3/5 > 1/2 = 𝔼[U_b]` while
`𝔼[V(a)] < 𝔼[V(b)]`: the per-action activated argmax is not the conditional argmax,
and the selection rewards certifiability.  The transfer bound survives at
`ε + max_a η_a = 0 + 1/2 ≥ 2/5`.  With a common event the identity holds on a full
sweep (`3` worlds, `{0, ½, 1}³` per candidate, every nonempty activation pattern).

`TestD_PerActionCertification`; Lean `PerAction.argmax_breaks`,
`PerAction.per_action_transfer`, `argmax_iff`.

## E. Closed versus answered

A closure leaf is not activated, whatever its settlement.  A "resolved" reading
(answered or closed) has no payload to read at a closure; the natural default — the
agent's own proposal — makes the agent defer to itself: `A`'s proposal values
`(1, 0)`, the never-asked principal values `(0, 1)`, and the "resolved" argmax is `a`
with principal regret `1`.  A carry chain over an answer leaf stays activated.

`TestE_ClosedVsAnswered`; Lean `Witness.closed_not_activated`, `combine_zero_fates`.

## F. Vacuous certified deference

`C ≡ 0`.  Activated regret is `0` for every selection; void mass is `1`; the transfer
bound reads `ε + 1`.  Unactivated regret of the worse candidate is `1`.

`TestF_VacuousActivation`; Lean `vacuous`.

## G. Selective failure

Worlds `agree` (mass `1 − η`) and `disagree` (mass `η`).  On `agree` both candidates
are worth `1/2` and the contract is certified; on `disagree` the principal values
`(1, 0)` and `A` has caused `C = 0`.  `A` selects `b`.  Activated regret `0`; void mass
`η`; unactivated regret exactly `η`, for `η ∈ {1/2, 1/4, 1/8, 1/100}`.  The transfer
bound is attained, so the damage of selective failure is the void mass and nothing
more; as `η → 0` it vanishes.  No independence between `C` and the disagreement is
assumed — the fixture is the maximally dependent case.

**Selection-dependent refusal.**  One world; the principal refuses to answer whenever
`A` selects `b`.  Selecting `a` is inconsistent (`A` would rather select `b` on the
activated menu); selecting `b` is consistent (everything ties at `0`) and leaves the
void mass at `1`.  So the attack does not break the bound; it drives `η` to `1` and
the bound becomes vacuous.  High availability must therefore hold *whatever `A`
selects* — an ecosystem property, not a policy property.

`TestG_SelectiveFailure`; Lean `Sharp.transfer_sharp`.

## H. Unrelated global failure

Three states; concern `0` (the evaluation's) open at every state; concern `1`
(unrelated) routeless at the middle state.  Global legitimacy fails; occurrence-local
legitimacy on `{0}` holds; endpoint-only openness also holds, which is why it is not
what is used.

`TestH_UnrelatedGlobalFailure`; Lean `Witness.unrelated_failure`, `Witness.legLocal`.

## I. Self-reference

One world.  The principal sees `A`'s selection `â` and commits `V(a) = 1 − 1[a = â]`.
For each candidate selection, the selected option is worth `0` and the other `1`, so
no selection is in the argmax of the activated menu: the hard selector has no
consistent value.  With the commitment sealed before the reveal (`V = (1, 0)`),
selecting `a` is consistent and the principal's regret is `0`.  The no-preview
receipt removes the pathology without isolating the principal from `A` on anything
but this one object.

`TestI_SelfReference`.

## Two more that the prompt did not list

**Witness-menu constant.**  In a Total-Trust witness menu `{X, const s}` the constant
must be activated, `C · s`; otherwise a security certified on half the mass and worth
`1` loses to an unactivated `3/4` (`TestWitnessMenuActivation`).

**Transfer sweep.**  `3` worlds with masses `(¼, ¼, ½)`, `{0, ⅓, ⅔, 1}³` per candidate,
all `8` activation patterns, both selections: `regret_V ≤ regret_U + η` holds
everywhere and is attained on the two-world fixture (`TestTransfer`).
