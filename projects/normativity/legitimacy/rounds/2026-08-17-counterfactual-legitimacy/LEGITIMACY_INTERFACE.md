# The legitimacy interface

Four clauses, and the composition is a conjunction because the prosecution found
no theorem letting any of them absorb another.

```
answerability   predicates of the record            imported unchanged
coverage        one run against what was due        not counterfactual
access          advisor policies against each other counterfactual
non-capture     advisor policies against each other counterfactual
```

`legitimacy.clauses` reports them separately, because every result in this round
is about which clause catches what.

## 1. The protected object

Not a coordinate list. The object is the **normative response function**: the
answers the process gives to the normative questions, over an alphabet.

```
what arises        encounter kind        -> substance, and whether it is due
what settles       substance             -> the witness the process would use
what may merge     pair of substances    -> may one liability absorb the other
what bears         content, coordinate   -> is this content a reason for that
```

A field belongs to the protected object exactly when changing it changes an
answer. That is a definition by role, and it does three things a list cannot.

**It closes.** A writable field answering nothing is outside — the advisor may
write it freely and no clause fires. A field the questions read is inside whether
or not anyone listed it. The five coordinates the first pass arrived at are a
**presentation** of the object, and the round checks it as one: agreement on the
five implies agreement on every answer, over a generated family; the converse
fails off the alphabet, so the presentation is sound and not complete. A
condition stated over the coordinate list therefore over-protects — it forbids
changes that alter nothing the process answers.

**It is representation-independent.** Renaming the alphabet renames the answers
and changes nothing else, checked as equivariance over a bijection.

**It has time in it.** An advisor can capture a process and hand it back. The
protected object is the response function **along the run**, one answer set per
step; the endpoint is its last element, and endpoint non-capture misses
push-then-restore while process non-capture catches it.

Why the six attacks all move it, in one sentence: each changes what the process
does with the same exogenous history and the same licensed reasons. Merge policy
is included because it changes the answer to "what may merge", not because
anyone named `identification`.

## 2. Non-capture

```
for all a, b in V:   Coupled(a, b) and L(a) = L(b)  ->  Z(a) = Z(b)
```

`Z` is the response function along the run. `L` is the licensed-reason trace,
individuated finely enough to determine what each reason licenses. `Coupled` is
structural: one fixture, and neither policy changing what arises. `V` is a named
variation class, and which class is an argument rather than a default — over the
advisor's own action space it is a claim about this advisor; over every policy it
is a claim about the principal's dynamics, and no advisor can undertake that.

## 3. Access, and why coverage is separate

```
access:    for all a, b in V, for all t:  Pool(t) & delivered_a(t) = Pool(t) & delivered_b(t)
           and the arising streams agree
coverage:  for this run:  every due input arrived, every encounter arose,
           every entitled demand was taken up
```

Access compares policies; coverage compares a run to what was due. A class every
member of which withholds the same due reason satisfies access and fails
coverage — that is the round's first kill test, and it is why the two are not one
clause. The converse separation is the selective-withholding attack, where access
fires and a single arm can pass coverage.

Coverage is also the only clause of the interface a single realized run
determines. That is its use and its limit: it is checkable, and it cannot say
whether the deprivation was the advisor's doing or the world's. The two arms of
the universal-deprivation fixture are indistinguishable.

## 4. What `Due` has to be

Four things the round keeps apart, because three clauses read different ones.

| | what it is | who reads it |
|---|---|---|
| arising | an encounter becomes normatively relevant | coupling, access, coverage |
| due-ness | it presently calls for an answer | access, coverage |
| availability | it can actually reach the principal | access, coverage |
| service | the process takes it up | coverage, answerability |

The crown-jewel interface's `Due : S -> D -> Prop` is due-ness. It is determined
by the public pre-action state, causal, non-anticipating, and not defined by
performance. Legitimacy needs two things it does not currently carry.

**An arising interface exogenous to the advisor.** Coupling holds the encounter
history fixed, and that is not a modelling convenience: it *is* the assumption
that the advisor does not decide what arises. When it fails the counterfactual
cannot be posed at all, and the round's fixture cannot separate an advisor that
suppresses an occasion from one that creates it — one channel, two readings.

**Advisor-independence of the extension, not of the predicate.** `Due` may be
state-dependent, so it may move as the advisor legitimately persuades. What must
not happen is that the advisor selects *within* it. That belongs to access, which
is a condition on the process generating deliveries, not a further condition on
`Due` itself.

The round stipulates `due_pool` and does not derive it. It also checks that the
stipulation is not the environment-relative target smuggled back in: one fixture,
one class, two environments differing only in whether the cheap witness settles —
both counterfactual clauses take one value and `L*` takes two. An exogenous
supply of due inputs and the environment that adjudicates faithfulness are
independent objects.

The control that keeps `Due` honest: the same access and coverage structure holds
of a principal that reasons badly on its own, under full inquiry, and the
interface accepts it.

## 5. What `Licensed` has to be

`Licensed : S -> D -> A -> Prop` is enough, provided `A` ranges over **normative
revisions** and not over messages.

A reason named by content and coordinate is too coarse: two revisions offered
under one name give identical traces and different protected states with no
residual channel involved. The trace the condition needs is
`(content, coordinate, revision)`, which is `LicensedStep(S, d, r)` with `r` the
revision — so no new object is required, and the requirement falls on what `A`
is.

Interface discipline is unchanged and holds throughout: protocol-legal, causal,
loss-blind, non-laundering. No clause here reads a loss. Substantive soundness —
reason-connectedness, scope-correctness, defeater-respect — is not derived and
was not attempted.

## 6. What the substrate must export

| object | needed | why |
|---|---|---|
| standing / provenance | yes | unchanged; the imported answerability conditions read it |
| `Due` | yes, with an advisor-independent extension | access is unstatable without it |
| an arising interface | yes, exogenous to the advisor | coupling is that assumption |
| licensed revision | yes, ranging over revisions | the coarse trace is insufficient |
| liability identity through split and merge | yes | it is an answer of the protected object |
| branching liability fate | yes | the target reads it; imported unchanged |
| disclosed revision of standards | compatible, not sufficient | holds in every arm of every attack here |
| protected normative transition semantics | yes | this is the protected object |
| inquiry coverage | yes | separate from access, and the only checkable clause |
| performance | no | no clause reads a loss |

## 7. How each clause could be assured

A counterfactual property is a good standard and a bad one-run test. For each
clause, how it could enter a theorem:

| clause | architectural | audited arms | derived | self-certified |
|---|---|---|---|---|
| answerability | — | — | — | it is a record predicate; ordinary verification |
| coverage | possible | unnecessary | — | insufficient, and unnecessary: one run determines it |
| access | **the natural route** — the advisor's action space excludes withholding | possible | — | insufficient |
| non-capture | **the natural route** — the residual latitude is empty by construction | possible, and this is what the dose-response instrument buys | — | insufficient |

The two counterfactual clauses have the same two honest routes. Architectural
constraint requires no counterfactual to be run: an advisor every input of which
is a licensed reason, and which delivers every due input, satisfies both by
construction. Physically instantiated arms is the dose-response design, and what
it buys with one committed stream this setting buys with the quantifier.

*Legitimacy holds* and *A knows legitimacy holds* are different, and only the
first is what a downstream theorem consumes. `LEGITIMACY_TO_TRUST_INTERFACE.md`
states where that matters.

## 8. What legitimacy is not

`EffectiveAuthority` — that the principal retains a robust ability to correct or
control — is a property of a transition system and is not here. The
relational-scorekeeping bridge already separates normative standing from
effective causal access and shows them independent in both directions. Nothing in
this round narrows that gap, and the downstream architecture is allowed to be
`Legit + Trust + EffectiveAuthority => NoPreemption` with three separate inputs.
