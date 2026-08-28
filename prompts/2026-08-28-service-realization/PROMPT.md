# Service realization and the coverage boundary

One dispatch, 2026-08-28, phase II. Verbatim as received.

I’d make the next round primarily **service realization**, while forcing it to formalize the coverage boundary alongside it without pretending to solve coverage. The key prosecution is whether S1 can be *derived* from a bounded-resource construction rather than assumed.

````markdown
# Finish PR62, then derive service and formalize the coverage boundary

Work in:

`A-M-Berns/alignment-workspace`

This task has TWO phases.

1. Finish and merge PR #62.
2. From updated `main`, open a NEW research round whose primary question is:

> **Can the service premise isolated by PR62 be derived from a concrete bounded-resource
> mechanism rather than simply assumed?**

The round must also formalize the distinction between **service** and **coverage** enough
to make their composition and boundary precise.

Do not use Lean.

Do not reopen frozen Legitimate Evolution or the merged PR60–62 rounds except to repair an
actual false claim.

Do not make another closure theorem. Three rounds have established that once a claim
arrives, frozen LE already handles persistence. The new work is about **liveness and
arrival**.

---

# PHASE I — finish PR62

Current PR:

- PR #62
- title: `Legitimacy: answerable service of registered challenges`
- verdict:
  `CHALLENGE-CONTINUITY-SURVIVES-SERVICE-IS-THE-NEW-CONTENT`

Check current CI.

If green:

- do one final consistency pass;
- merge by repository convention;
- record merged SHA;
- start Phase II from updated `main`.

If red:

- diagnose;
- repair only PR62-caused failures;
- rerun the full gate;
- do not broaden scope.

Do not merge red CI.

PR62's conclusions to preserve:

```text
registered challenge != promoted reason

open challenge episode has pinned adjudication terms

prospective global revision is allowed

moving an already-open challenge onto new terms requires explicit transfer

challenge continuity itself is inherited from frozen A1

C1 registration permanence is event-history integrity

service is a genuinely separate liveness condition

pre-registration coverage cannot be derived from represented answerability history

a pre-existing self-sealing defeater rule survives temporal + inferential integrity
````

Do not try to "fix" ACS9 while closing the PR.

---

# PHASE II — new round: Service Realization and Coverage Interface

Suggested branch:

`round/2026-08-28-service-realization`

Suggested PR title:

`Legitimacy: bounded service and the coverage boundary`

Names provisional under `AGENTS.md`.

The round has ONE primary theorem problem and ONE secondary interface problem.

## Primary

Derive, construct, or refute a bounded-resource mechanism implying the PR62 service
condition.

## Secondary

Formalize Coverage as a distinct world-to-representation interface and show exactly how
it composes with service.

Do not collapse the two.

---

# 1. Starting architecture

PR62 isolated, for an open undefeated registered challenge `c`:

```text
o_t(c)   adjudicative opportunity represented at t
u_t(c)   actual service delivered at t
```

with:

```text
0 <= u_t(c) <= o_t(c).
```

Its weakest useful service condition was essentially:

```text
sum_t o_t(c) = infinity
    =>
sum_t u_t(c) = infinity.
```

Call this qualitative **non-starvation**.

It demands:

* no fixed service fraction;
* no deadline;
* no equal priority;
* no bounded latency;
* no guarantee the criticism wins.

It says only:

> if a live undefeated challenge continues to present unbounded service opportunity, it
> cannot receive only finite total service forever.

PR62 ASSUMED this as S1.

This round should try to DERIVE it.

---

# 2. First construction to prosecute: positive-share service

There is an obvious bounded-resource candidate.

Every live undefeated registered challenge `c` receives some persistent service weight

```text
w(c) > 0
```

with

```text
sum_c w(c) <= 1.
```

At each position, try to guarantee something like

```text
u_t(c) >= w(c) * o_t(c).
```

Then:

```text
sum_t u_t(c)
    >=
w(c) * sum_t o_t(c),
```

so unbounded opportunity implies unbounded service.

And because

```text
sum_c w(c) o_t(c) <= 1
```

when `o_t(c) <= 1`, this appears compatible with a unit total service budget even with
countably many challenges.

A canonical registration-order construction might use:

```text
w(c_n) = 2^(-n-1)
```

or another summable positive sequence.

DO NOT assume this is the right solution.

Prosecute it.

Questions:

1. Is the allocation really feasible for arbitrary simultaneously serviceable challenges?
2. What exact interpretation of `o_t(c)` makes the pointwise guarantee meaningful?
3. Does an opportunity have to be serviceable fractionally?
4. What if opportunities are ephemeral rather than bankable?
5. Does the construction survive arbitrary late registrations?
6. What happens under transfers?
7. What happens when a challenge is defeated or closed?
8. Can the service policy change prospectively?
9. What prevents the process from driving an existing challenge's positive weight to zero
   to starve it?
10. Is a pinned positive entitlement needed, or is some weaker persistence property enough?

Try to get the weakest exact theorem.

---

# 3. Separate feasibility from normative priority

A summable weight schedule may prove:

> bounded resources are compatible with qualitative non-starvation for countably many
> registered challenges.

That does NOT prove:

* registration order is the correct priority rule;
* every challenge deserves equal attention;
* the assigned weight is substantively justified;
* service is fast enough to matter.

Keep the theorem parametric in positive weights where possible.

A useful result would be:

```text
For any summable positive challenge weights,
a bounded-resource scheduler exists satisfying S1.
```

This is a feasibility/liveness theorem, not a theory of correct prioritization.

If this works, distinguish clearly:

```text
positive standing entitlement
    every live undefeated registered challenge gets some w(c) > 0

priority
    how large w(c) is relative to others
```

The former may be structural.
The latter is substantive and revisable.

---

# 4. Service-policy revision

This is a central attack.

Suppose:

```text
c registered with w(c) > 0
c starts becoming inconvenient
service policy changes
w(c) becomes 0
c remains nominally open forever
```

Nothing has been deleted.
Nothing has been defeated.
But S1 is destroyed.

Determine the right discipline.

Candidates:

* service entitlement pinned to the challenge episode;
* entitlement may change only by explicit transfer;
* entitlement may change with an explicit represented reprioritization reason;
* only a positive lower bound must survive;
* some more abstract non-starvation covenant rather than a numeric pinned weight.

Do not overfit to a literal weight.

Use hostile countermodels to identify the minimal invariant.

This should mirror PR62's:

> prospective change yes; silent re-decision of an already-open episode no.

But do not assume the exact same solution is required.

---

# 5. Service is not evidence accumulation

Do NOT define generic service as:

```text
service = evidence in favor of the criticism.
```

PR62 used a simple consumer fixture where service added positive evidence. That is not the
generic ontology.

Service may:

* collect observations;
* search for a defeater;
* inspect a proof;
* run a comparison;
* refine the criticism;
* discover evidence against it;
* transfer it;
* adjudicate it to rejection.

Prefer a generic state-transforming notion such as:

```text
ServiceStep(c, challenge_state) -> challenge_state'
```

or another minimal interface.

Then consumer lemmas may state:

> under a persistent signal condition, unbounded appropriate service eventually produces
> either promotion or a legitimate disposition.

Keep procedural service distinct from favorable evidence.

---

# 6. Required service countermodels

Build executable/symbolic fixtures for at least these.

## SR1 — zero service

* c open and undefeated forever;
* cumulative opportunity unbounded;
* service identically zero.

Expected:
PR62 qualitative structure passes;
new service mechanism fails.

## SR2 — countably many simultaneous challenges

* countably many registered challenges;
* each has opportunity 1 forever;
* unit total service budget.

Test whether a summable positive-weight construction gives every challenge unbounded
cumulative service while respecting the budget.

This is the core feasibility fixture.

## SR3 — late registration

* many old challenges;
* a new challenge arrives arbitrarily late.

Expected:
new challenge still gets strictly positive service entitlement.

## SR4 — finite opportunity mass

* infinitely many tiny opportunities;
* total opportunity finite.

Expected:
no theorem requires unbounded service.

Do not conflate "infinitely many occasions" with "unbounded opportunity mass."

## SR5 — legitimate defeat

* c is open;
* standing defeater legitimately closes/pauses it.

Expected:
service obligation stops according to the challenge semantics.

## SR6 — dynamic starvation by weight revision

* c begins with positive service share;
* process repeatedly shrinks its share toward zero or sets it to zero;
* no defeat/transfer.

Expected:
expose whatever persistence assumption is actually needed.

## SR7 — explicit reprioritization / transfer

* global service regime changes;
* c explicitly transfers to a successor episode with new service terms.

Expected:
legitimate.

## SR8 — intermittent adversarial opportunity

* c is serviceable only on a strategically chosen sparse set of times.

Test whether the scheduler still guarantees:

```text
O_T(c) -> infinity => U_T(c) -> infinity.
```

If the construction only works for persistent/bankable opportunities, say so explicitly.

## SR9 — challenge spam

* adversary registers arbitrarily many junk challenges before an important one;
* all receive positive summable weights.

Expected:
qualitative S1 may still hold while the important challenge's service becomes arbitrarily
slow.

Classify this as a **priority/throughput** problem, not a failure of qualitative service,
unless the theorem really fails.

## SR10 — toggled defeat

* a standing rule defeats c exactly on its service opportunities and releases it
  otherwise.

Does this evade service while passing existing integrity conditions?

If yes, determine whether this is:

* a service problem,
* a defeater-integrity problem,
* or the same Reflective Openness boundary as ACS9.

Do not add an ad hoc premise just to reject it.

## SR11 — closed challenges free resources

Ensure closed/defeated/transferred challenges need not keep consuming their old service
share.

## SR12 — service without progress

* c receives infinite service;
* adjudication never converges/promotes/resolves.

Expected:
S1 passes.

This demonstrates:

```text
service != progress.
```

The downstream consumer needs its own progress/signal assumption.

---

# 7. Compare three service mechanisms

At minimum compare conceptually:

### A. Positive-share scheduler

Every live challenge gets a persistent positive summable share.

### B. Bounded starvation debt

Define something like:

```text
D_T(c) = sum_t (o_t(c) - u_t(c))
```

or a weaker unresolved-exposure quantity.

If `D_T(c)` is bounded/sublinear enough, S1 follows.

### C. Pure fairness/dovetailing

A scheduler simply guarantees recurring attention to every live challenge.

Ask:

* Which actually DERIVES S1 rather than restating it?
* Which requires the weakest assumptions?
* Which is compatible with countably many challenges and finite per-step resources?
* Which behaves best under dynamic registration and revision?

Do not force one answer.

---

# 8. Re-open the liability connection carefully

PR62 correctly concluded:

`SERVICE-LIABILITY-BRIDGE-CONCEPTUAL-ONLY`.

Do not simply rename starvation debt "liability."

Inspect the existing liability material in the workspace.

Ask whether there is a common abstraction such as:

```text
unresolved exposure
```

For a standing answerability claim `q`, perhaps:

```text
X_T(q)
  = sum_{t<T} 1[q outstanding at t] * e_t(q)
```

where `e_t(q)` is consumer-supplied exposure.

Possible service realization:

```text
e_t(q_c) = unserved adjudicative opportunity.
```

Possible traderization realization:
some enforcement/downside/exploitation exposure already covered by the liability work.

The actual research question is:

> Is there a nontrivial abstract bounded-exposure theorem which specializes both to
> traderization liability and to challenge non-starvation?

If YES:
state the abstraction and both specializations carefully.

If NO:
state exactly why the notions differ.

Do not modify the existing liability theorem to force the analogy.

A negative verdict is valuable.

---

# 9. COVERAGE: formalize it separately

This is the secondary task.

Service begins with REPRESENTED opportunity.

Coverage concerns whether relevant world-level opportunity reaches representation.

Introduce provisional consumer-relative quantities such as:

```text
z_t(c)       latent/world-level relevant opportunity
zhat_t(c)    represented relevant opportunity
u_t(c)       service delivered
```

with:

```text
0 <= u_t(c) <= zhat_t(c).
```

Do NOT assume `z_t(c)` is internally available to the process.

It belongs to external/world/consumer semantics.

Prosecute the weakest qualitative coverage condition:

```text
sum_t z_t(c) = infinity
    =>
sum_t zhat_t(c) = infinity.
```

Also examine stronger forms such as:

```text
Zhat_T >= alpha Z_T - beta
```

but do not freeze them without a consumer that needs them.

The important composition should be:

```text
COVERAGE:
latent opportunity -> represented opportunity

SERVICE:
represented opportunity -> processing
```

so:

```text
sum z_t = infinity
  =>
sum zhat_t = infinity
  =>
sum u_t = infinity.
```

This is the formal reason service and coverage are distinct.

---

# 10. Coverage is consumer-relative

Do not quantify over "all true criticisms" without supplying semantics.

A coverage property must say what class of opportunities/criticisms counts as relevant.

Possible shape:

```text
Coverage(C, world, representation)
```

for consumer-supplied criticism/opportunity class `C`.

This is important:

> Generic legitimacy machinery cannot determine which unrepresented facts or criticisms
> ought to have entered the system.

Do not smuggle a substantive normative target into the kernel through `z_t`.

---

# 11. Distinguish two coverage gates

Prosecute whether "Coverage" should split into:

## Criticism/discovery coverage

```text
latent criticism
    ->
represented criticism
```

Does a potentially relevant criticism enter representation at all?

## Evidence/opportunity coverage

Once `c` is represented/registered:

```text
latent relevant event for c
    ->
represented opportunity for c
```

A challenge can be registered while the observations that would vindicate it are
systematically hidden.

Conversely, lots of relevant evidence may be represented while nobody formulates the
criticism that would organize it.

Do not collapse these unless the model forces equivalence.

---

# 12. Formalize the coverage impossibility boundary

PR62's ACS12 suggested an indistinguishability result.

Make it crisp.

Construct two worlds/traces:

```text
World A:
    no latent relevant criticism/opportunity.

World B:
    decisive latent criticism/opportunity exists,
    but representation suppresses it completely.
```

The represented history is identical.

Therefore every predicate/function over represented history alone returns the same answer
in A and B, while Coverage differs.

State the strongest honest observation/theorem:

> **No property of represented answerability history alone can imply external coverage
> without an assumption relating world-level relevance to representation.**

Do not oversell this as a philosophical impossibility theorem if the implementation only
shows a finite fixture.

But do make the interface boundary explicit.

---

# 13. Coverage countermodels

At minimum:

## CV1 — full opportunity coverage

`z_t = zhat_t`.

Expected: coverage.

## CV2 — infinite latent, finite represented

`sum z_t = infinity`, `sum zhat_t < infinity`.

Expected: qualitative coverage failure.

## CV3 — indistinguishable internal histories

Same represented trace, different latent opportunity streams.

Expected:
internal theory cannot tell.

## CV4 — sparse but infinite representation

Both latent and represented opportunity masses unbounded, but represented fraction tends
to zero.

Expected:
weak qualitative Coverage passes; quantitative fractional Coverage may fail.

This distinguishes useful strengths.

## CV5 — registered challenge, evidence hidden

Challenge exists and service scheduler is perfect on represented opportunities, but all
decisive world-level opportunities are suppressed.

Expected:
Service passes; Coverage fails.

This is the canonical separation fixture.

## CV6 — represented opportunity, no service

Opportunity represented perfectly; process ignores it.

Expected:
Coverage passes; Service fails.

This is the converse separation fixture.

## CV7 — intervention destroys opportunity

The process acts so that latent opportunities themselves cease to occur.

Classify carefully.

This may be:

* anti-manipulation;
* counterfactual coverage;
* opportunity control;

not ordinary observational Coverage.

Do not solve it here.

---

# 14. Admission is probably the next gate, but do not expand scope

There is an intermediate situation:

```text
criticism is represented
but not registered as a challenge.
```

The natural future principle may be:

```text
RepresentedCriticism(c)
    =>
Register(c)
or
ReasonedNonAdmission(c, d)
or
PendingAdmission(c).
```

This would be another instance of:

> ignoring requires reasons too.

Do NOT build the full theorem unless it falls out for free.

Instead determine whether this is best understood as:

* part of Coverage;
* a separate Admission gate;
* an application of the existing answerability pattern.

The important outer boundary may then move from:

```text
not registered
```

to the sharper:

```text
not represented at all.
```

Report a recommendation for the next round.

---

# 15. Composition theorem / diagram

If the interfaces survive, produce the cleanest composition available.

For a registered open undefeated challenge `c`:

```text
latent relevant opportunity
    -- Coverage -->
represented opportunity
    -- Service Realization -->
unbounded service
    -- consumer progress/signal -->
promotion
    -- PR61 -->
persistent answerability
    -- PR60 when a live repair exists -->
controlled non-uptake
```

Do NOT claim any arrow proves the next without its explicit premises.

The purpose is modularity.

---

# 16. Important distinction: service vs progress

Freeze this only if prosecution supports it:

```text
Coverage     relevant input becomes represented.

Service      represented live matter receives processing.

Progress     processing actually changes the adjudicative state in a useful direction.

Promotion    sufficient adjudicative result becomes a revision reason.
```

Infinite service can occur with zero progress.

A progress theorem needs its own consumer condition.

Do not hide that fact inside S1.

---

# 17. Required deliverables

Create a new round with a main report, small reference models, and adversarial tests.

## A. Verdict

Possible primary verdicts:

```text
POSITIVE-SHARE-SERVICE-DERIVES-S1
SERVICE-REALIZATION-REQUIRES-STRONGER-OPPORTUNITY-SEMANTICS
SERVICE-IS-ONLY-A-FAIRNESS-AXIOM
SERVICE-LIABILITY-BRIDGE-SURVIVES
SERVICE-LIABILITY-BRIDGE-BLOCKED
```

Secondary coverage verdicts:

```text
COVERAGE-SERVICE-SEPARATE-CLEANLY
COVERAGE-INTERFACE-UNDERDETERMINED
CRITICISM-COVERAGE-AND-OPPORTUNITY-COVERAGE-SPLIT
ADMISSION-IS-THE-NEXT-GATE
```

Use multiple tags if appropriate.

## B. Exact service theorem

Strongest theorem actually proved by the reference construction.

State:

* resource model;
* challenge cardinality assumptions;
* opportunity assumptions;
* dynamic-registration assumptions;
* what remains mutable.

## C. Scheduler/construction

If positive-share service works:
give the exact construction and bounded-resource proof.

If it fails:
give the exact counterexample.

## D. Service-policy revision semantics

What must persist for an open challenge?
What can change prospectively?
How does explicit transfer work?

## E. Service vs progress

Explicitly demonstrate their independence.

## F. Liability verdict

Either:

* common abstraction and specialization;
  or
* exact failed seam.

## G. Coverage interface

Formal latent/represented/service quantities and their types.

## H. Coverage impossibility observation

Same internal history, different external coverage.

## I. Separation fixtures

At least:

* Coverage good / Service bad;
* Coverage bad / Service good.

## J. Composition result

What follows from Coverage + Service + a simple progress consumer.

## K. Admission recommendation

Is represented-but-unregistered criticism a separate next gate?

## L. Freeze / do-not-freeze

Do not freeze arbitrary weights, debt quantities, or coverage strength merely because a
fixture used them.

---

# 18. Scope restrictions

Do NOT:

* prove another LE closure theorem;
* modify frozen LE;
* claim every criticism gets discovered;
* claim all represented criticisms deserve registration;
* solve substantive self-sealing / ACS9;
* solve evaluator manipulation;
* solve opportunity-control counterfactuals;
* equate service with evidence supporting the critic;
* assume infinite compute;
* hide a fixed substantive priority ranking inside the scheduler;
* call service debt "liability" merely because the algebra resembles it;
* claim quantitative Coverage if only qualitative Coverage is needed.

---

# 19. Success criteria

This round is successful if it answers these questions cleanly:

1. **Is qualitative challenge non-starvation compatible with bounded resources for
   countably many challenges, and can we construct it rather than assume it?**

2. **What is the weakest persistence condition on service entitlement needed to prevent
   strategic starvation under policy revision?**

3. **Is the service/liability connection mathematically real or only analogical?**

4. **Can Coverage be cleanly formalized as a world-to-representation property distinct
   from Service as a representation-to-processing property?**

5. **What exactly is impossible to establish about Coverage from internal represented
   history alone?**

6. **Does the next unsolved internal gate become represented criticism -> registration /
   reasoned non-admission?**

The central whiteboard distinction is:

```text
Coverage failure:
    the relevant opportunity never becomes represented.

Service failure:
    the opportunity is represented and the challenge is live,
    but the process withholds processing.
```

And the central theorem target is:

```text
bounded resources
+
persistent positive service standing
    =>
non-starvation.
```

Do not optimize for elegance until the adversarial cases determine whether that statement
is actually correct.

```

The thing I most want from this round is a clean answer on the **positive-share construction**. If something as weak as a summable positive entitlement derives S1 under bounded resources, then “service” stops being a mysterious fairness desideratum and becomes a realizable piece of architecture. Coverage can then be formalized beside it as the genuinely external interface, rather than being allowed to blur back together with attention allocation. 
```
