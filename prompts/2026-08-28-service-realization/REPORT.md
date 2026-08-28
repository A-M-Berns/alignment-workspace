# Service realization — report

**Verdict:** `POSITIVE-SHARE-SERVICE-DERIVES-S1`.

## The primary question is answered affirmatively

The round below assumed a liveness premise. It is now constructed.

Give every open challenge a positive share from a summable schedule and serve
`u_t(c) = w_t(c) o_t(c)`. Budget-feasible, and the conclusion follows by one
inequality. `SR2` is the fixture and it is not close: 24 simultaneous challenges,
each with opportunity 1 at every position, against a single unit of service per
position, every one served positively, peak total exactly 1.0.

The theorem is **parametric in any positive summable schedule**. Registration
order with `2^{-n-1}` is a witness that such a schedule exists, not a claim that
it is the right priority rule, and the document separates positive standing
(structural) from how large a share is (substantive and revisable).

## Divisibility is not the requirement; adaptivity is

With atomic service a least-recently-served rule derives the same conclusion.
What carries it is adaptivity to *current* opportunity: `SR8` runs one
opportunity stream two ways, and a fixed dovetailer leaves a challenge at zero
service with 100 units of opportunity while the adaptive rule gives it 99.

## What must persist is weaker than expected

Not a pinned entitlement — a **positive infimum**. `inf_t w_t(c) > 0` is all the
inequality uses, so reprioritisation by any finite factor stays available and
only approaching zero is forbidden.

`SR6` is why this matters and is the subtlest result in the round. A share shrunk
geometrically is never zero, never defeated, never transferred — and on any
finite prefix it satisfies the finite proxy for the service condition, because
*some* service was delivered. The mechanism has been dismantled while the
symptom is invisible. That is the reason `W1` and not `S1` is the thing to check.

## The liability bridge is blocked, directionally

Not a failure to find a translation. Liability theorems **bound** accumulated
exposure; the service condition requires accumulated service to **diverge**.
Bounded debt would be sufficient — `U >= O - D` — and is strictly stronger than
what the feasible construction delivers, which leaves `D = (1-w)O` diverging
alongside `U`. A test exhibits the service condition clean with debt climbing.

## Coverage, formalized beside service

`z -> zhat -> u`, with coverage external and service internal. Independent in
both directions and both exhibited: `CV5` has perfect service on suppressed
representation, `CV6` perfect representation with no service.

Coverage is consumer-relative and every fixture names its class, because a latent
stream chosen without a consumer smuggles a substantive target into the kernel.
It splits into criticism coverage and opportunity coverage, and `CV4` separates
qualitative from fractional strength — the stronger form is offered and not
adopted, since no consumer needs it.

The boundary observation is crisp and deliberately modest: same represented
history, different coverage, every internal probe agreeing. Stated as an
observation about an exhibited finite pair, not as an impossibility theorem, and
a test checks that the docstring says so.

## What survives and is not solved

Challenge spam degrades throughput without breaking the condition — a priority
problem, classified rather than patched. Toggled defeat evades service while
violating nothing, and is the same shape as the pre-existing self-sealing rule
one round below; no ad hoc premise was added to reject it. Intervention that
destroys latent opportunity is not observational coverage and is classified only.

## Recommendation for the next gate

**Admission** — criticism represented but not registered — is a separate gate,
not part of coverage: coverage is world-to-representation and this is
representation-to-standing. If built, the outer boundary moves from *not
registered* to *not represented at all*.

## Outstanding maintainer actions

1. **Decide whether admission becomes the next round.** The recommendation is
   yes, and as its own gate.

2. **The liability bridge can be closed or abandoned.** Closing it needs a
   *bounded-debt* scheduler, which this round did not find and which is strictly
   stronger than what is needed for the service condition.

3. **No item is reserved.** The forks this round faced it adopted, as dated
   `DECISIONS.md` entries marked agent-decided and reversible.

## Attribution

| | |
|---|---|
| prompt author | a maintainer, with a model-assisted draft; one dispatch |
| executor | Claude Opus 5 (Anthropic) |
| date | 2026-08-28 |
