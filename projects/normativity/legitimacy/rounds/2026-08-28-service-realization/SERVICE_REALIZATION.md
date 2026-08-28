# Bounded service and the coverage boundary

Status: **specification, reference models and a prosecution record;
unregistered.** All names provisional under `AGENTS.md` §6. No Lean, no
registered claim.

Frozen Legitimate Evolution is not imported at all this round. Neither module
touches it, asserted by parsing: this is liveness and arrival, not persistence.

## A. Verdict

```text
POSITIVE-SHARE-SERVICE-DERIVES-S1
```

Secondary:

```text
PERSISTENCE-IS-A-POSITIVE-FLOOR-NOT-A-PINNED-VALUE
ADAPTIVITY-IS-REQUIRED-IN-THE-ATOMIC-CASE
SERVICE-LIABILITY-BRIDGE-BLOCKED-BY-DIRECTION
COVERAGE-SERVICE-SEPARATE-CLEANLY
CRITICISM-COVERAGE-AND-OPPORTUNITY-COVERAGE-SPLIT
ADMISSION-IS-THE-NEXT-GATE
```

The round below assumed a service premise. It is now **derived** from a
bounded-resource construction, and service stops being a fairness desideratum.

## B. The service theorem

> **Service Realization (fractional).** Let every open challenge have entitlement
> bounded below by `w_min(c) > 0`, with `sum_c w_t(c) <= B` and `o_t(c) <= 1`.
> Then `u_t(c) = w_t(c) o_t(c)` is budget-feasible and
> `sum_t u_t(c) >= w_min(c) sum_t o_t(c)`, so unbounded opportunity gives
> unbounded service. ∎

Feasibility is the whole content, and it is not close. `SR2` runs **24
simultaneous challenges**, each with opportunity `1` at every position, against a
**single unit** of service per position:

```text
c0    floor 5.00e-01   O = 200.0   U = 100.0000
c5    floor 1.56e-02   O = 200.0   U =   3.1250
c12   floor 1.22e-04   O = 200.0   U =   0.0244
c23   floor 5.96e-08   O = 200.0   U =   0.0000119

peak total service at any position = 1.000000  (budget 1.0)
```

Every challenge is served positively; the budget is met exactly and never
exceeded. A summable schedule such as `w(c_n) = B 2^{-n-1}` witnesses existence,
and the theorem is **parametric in any positive summable schedule** — registration
order is used because it is available, not because it is the right priority rule.

### Assumptions, stated

```text
resource model         one unit of divisible service per position
cardinality            countably many challenges
opportunity            o_t(c) in [0,1]; unbounded mass is what is required
dynamic registration   arbitrary late arrivals, each with positive share (SR3)
mutable                the schedule itself, subject to W1
```

`SR4` is the boundary of the hypothesis: infinitely many occasions with `o_t =
2^{-t}` has *finite* opportunity mass and no theorem demands anything.
Conflating "infinitely many occasions" with "unbounded opportunity" would be an
error, and the fixture exists to prevent it.

## C. Divisibility is not required, but adaptivity is

If service is atomic — one challenge per position, all of its opportunity or
none — weights are unavailable and a scheduler is needed instead.

`SR8` is the same world served two ways:

```text
fixed cycle    c1: O=200  U=100      c2: O=100  U=  0     starved
adaptive LRS   c1: O=200  U=101      c2: O=100  U= 99
```

The adversary presents `c2`'s opportunity only on positions where a fixed
dovetailer is serving `c1`. Least-recently-served — choosing among challenges
that have opportunity **now** — is not defeated: a challenge that has waited
longest and is serviceable is picked, and only finitely many can be younger than
it.

> **Adaptivity to current opportunity is load-bearing.** A schedule fixed in
> advance derives nothing.

## D. What must persist: a floor, not a pin

The round below pinned adjudication terms to the registration episode. Service
does **not** need that, and the weaker condition is the right one:

> **W1.** An open undefeated challenge's service entitlement has a positive
> infimum.

`sum_t w_t(c) o_t(c) = infinity` follows from `inf_t w_t(c) > 0`, so pinning an
exact value is more than the theorem uses. Reprioritisation stays fully
available: a share may fall by any finite factor, any number of times
(`test_reprioritisation_is_still_allowed`).

`SR6` is the attack it exists for. The share is shrunk **geometrically** — never
set to zero, never defeated, never transferred, nothing deleted:

```text
w_t(c1) = 2^{-t-1}     floor after 200 positions: 6.2e-61
```

And here is the part worth stating carefully: **on a finite horizon this does not
look like starvation.** Some service was delivered, so the finite proxy for S1 is
satisfied while the mechanism guaranteeing it has already been dismantled. That
is exactly why `W1` is the invariant to state, and `S1` alone is not enough to
check.

## E. Service is not progress, and not evidence

`SR12`: unbounded service, adjudication never converges. `S1` passes. A progress
claim needs its own consumer condition and does not hide inside `S1`.

Service is deliberately **not** defined as evidence favouring the criticism —
asserted by parsing, since the round below's consumer fixture made service add
positive evidence and that is a fixture, not an ontology. Service may search for
a defeater, refine the criticism, or adjudicate it to rejection.

## F. The liability bridge is blocked, and the reason is directional

Not a failure to find an analogy. The shapes are opposed:

```text
liability theorems    bound accumulated exposure
S1                    requires accumulated service to DIVERGE
```

Bounded debt would be *sufficient*: `U_T >= O_T - D_T`, so bounded `D_T` gives
`U_T -> infinity`. But it is **strictly stronger than what the feasible
construction delivers** — positive-share service leaves `D_T = (1-w) O_T`, which
diverges. `test_S1_holds_while_the_debt_diverges` exhibits `S1` clean with debt
100 and climbing.

So the missing lemma is not a translation. It would have to be a *bounded* debt
theorem, and no bounded-resource scheduler in this round produces one. The
workspace's liability program bounds enforcement charge; nothing here bounds
adjudicative debt, and calling starvation debt a liability because the algebra
rhymes would be exactly the error the round below warned against.

## G. Coverage, formalized beside service

```text
z_t(c)     latent world-level relevant opportunity   EXTERNAL
zhat_t(c)  represented opportunity                   the boundary
u_t(c)     service delivered                         INTERNAL

COVERAGE   sum z_t = infinity  =>  sum zhat_t = infinity
SERVICE    sum zhat_t = infinity  =>  sum u_t = infinity
```

Neither implies the other, and both directions are exhibited:

```text
CV5  Z=200  Zhat=2.0    U=1.0    coverage fails, service perfect
CV6  Z=200  Zhat=200    U=0.0    coverage perfect, service fails
```

**Coverage is consumer-relative and every fixture names its class.** A `z`
chosen without a consumer smuggles a substantive normative target into the
kernel; `Stream.klass` is carried so two notions cannot be quietly compared.

**Two gates, not one.** `CV5` registers a challenge whose vindicating evidence is
hidden — opportunity coverage fails. `CV8` represents a mass of relevant
opportunity that no criticism organises — criticism coverage fails. They are
independent.

**Qualitative and fractional come apart.** `CV4` has both masses unbounded with
the represented *fraction* tending to zero: qualitative coverage passes,
`Zhat >= 0.5 Z` fails. The stronger form is offered and **not adopted**, because
no consumer in this round needs it.

## H. The boundary observation

```text
same represented history:  True
coverage differs:          True
every internal probe agrees: True
```

> **No function of represented history alone can imply coverage.**

Stated as an observation about an exhibited pair, not as a philosophical
impossibility theorem — the fixture is finite and shows the interface boundary,
nothing more. The docstring says so and a test checks that it says so.

## I. Composition

```text
latent opportunity
    -- Coverage (external premise) -->
represented opportunity
    -- W1 + a bounded-resource scheduler -->
unbounded service
    -- a consumer progress/signal premise -->
promotion
    -- 2026-08-28-answerable-revision -->
persistent answerability
    -- 2026-08-27-legitimate-improvement, when a live repair exists -->
controlled non-uptake
```

No arrow proves the next without its own premise, and the two that are external
to every internal theory are the first and the third.

## J. What survives but is not solved

**Challenge spam (SR9).** Twenty junk registrations before the one that matters.
`S1` holds — the real challenge keeps a positive share of `2^{-21}` — and its
throughput is negligible. A **priority** problem, not a failure of qualitative
service, and the round classifies rather than patches it.

**Toggled defeat (SR10).** A standing rule that defeats the challenge exactly
when it is serviceable and releases it otherwise. The challenge is never open
*and* serviceable at once, so `S1` is vacuous and `W1` is satisfied. This is the
same shape as the round below's pre-existing self-sealing rule, and no ad hoc
premise is added to reject it.

**Intervention (CV7).** The process acts so latent opportunities stop occurring:
`z` itself goes to zero. Not observational coverage. Classified, not solved.

## K. Admission is the next gate

There is a live intermediate case: criticism **represented but not registered**.
The natural principle is the family's usual one —

```text
RepresentedCriticism(c)  =>  Register(c)  or  ReasonedNonAdmission(c, d)
                             or  PendingAdmission(c)
```

— and it is *not* built here. The recommendation: it is a **separate gate**, not
part of coverage, because coverage is world-to-representation and this is
representation-to-standing. If it is built, the outer boundary moves from *not
registered* to the sharper *not represented at all*.

## L. Freeze / do not freeze

```text
FREEZE
  S1 is derivable, not a fairness axiom
  the invariant is a positive floor (W1), not a pinned entitlement
  adaptivity to current opportunity is required in the atomic case
  service, progress and evidence are three things
  coverage and service are independent, with both separations exhibited
  coverage is consumer-relative and its class must be named
  the liability bridge is blocked by direction, not by translation

DO NOT FREEZE
  the 2^{-n-1} schedule, or registration order as priority. Any positive
    summable schedule works and the theorem is parametric
  the starvation-debt quantity. Reported for comparison, not the condition
  fractional coverage. Offered, and no consumer needs it
  the divisible-service model. The atomic case needs a different theorem and
    has one
  anything about admission
```

## M. What no claim above asserts

- No claim that any priority ranking is correct. Positive standing is
  structural; how large a share is, is substantive and revisable.
- No claim that service is fast, fair or proportionate. `SR9` is slow and
  conforming.
- No claim of progress, promotion or convergence from service alone.
- No claim that the toggled-defeat evasion is illegitimate. It is the older
  boundary reappearing.
- No claim of quantitative coverage anywhere.
- No claim that the fixtures witness divergence. They are finite; the proxies
  are named as proxies.
