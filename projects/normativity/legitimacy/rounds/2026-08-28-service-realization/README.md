# Bounded service and the coverage boundary

Status: **specification, reference models and a prosecution record;
unregistered.** All names are provisional under `AGENTS.md` §6. Nothing here is
Lean-checked and no claim is registered.

## Verdict

POSITIVE-SHARE-SERVICE-DERIVES-S1 — the service premise the round below assumed is now constructed from a bounded-resource mechanism, so service stops being a fairness desideratum and becomes realizable architecture. Twenty-four simultaneous challenges, each with opportunity one at every position, are all served positively against a single unit of service per position, with the peak total exactly at budget and never above it; any positive summable schedule works and the theorem is parametric in it, so registration order is a witness rather than a priority claim. Divisibility is not required: with atomic service a least-recently-served rule derives the same conclusion, and adaptivity to current opportunity is what carries it, since a schedule fixed in advance is starved by an adversary who presents opportunity only when the cycle is elsewhere. What must persist is weaker than the round below's episode pinning: a positive infimum on entitlement rather than a pinned value, so reprioritisation by any finite factor stays available and only approaching zero is forbidden. That distinction matters because a share shrunk geometrically is fatal while looking clean on any finite prefix, which is why the floor and not the service condition is the thing to check. The liability bridge is blocked for a directional reason rather than a translation failure: liability theorems bound accumulated exposure, the service condition requires accumulated service to diverge, and the feasible construction leaves a debt that diverges alongside it. Coverage is formalized beside service as a world-to-representation property with both separations exhibited, is consumer-relative with every fixture naming its class, and splits into criticism coverage and opportunity coverage. The boundary observation is that no function of represented history alone can imply coverage, stated as an observation about an exhibited pair rather than as an impossibility theorem.

## The question

The round below isolated a liveness premise and assumed it: an open undefeated
challenge with unbounded adjudicative opportunity receives unbounded service. No
rate, no deadline, no fairness. This round asks whether a concrete
bounded-resource mechanism **derives** it.

It does.

## What is new

**Service is constructible.** Give every open challenge a positive share from a
summable schedule and serve `u_t(c) = w_t(c) o_t(c)`. Budget-feasible, and the
service condition follows by a one-line inequality. `SR2` runs 24 challenges
against a unit budget with the peak total service exactly 1.0.

**Adaptivity, not divisibility, is what the atomic case needs.** A fixed
dovetailer is starved by adversarial opportunity timing; least-recently-served
among currently-serviceable challenges is not.

**The invariant is a floor, not a pin.** `inf_t w_t(c) > 0` suffices, which is
strictly weaker than pinning an entitlement and leaves reprioritisation
available. A geometrically shrinking share is fatal — and looks clean on any
finite prefix, which is why the floor is the thing to check.

**The liability bridge is blocked by direction.** Liability theorems bound
accumulated exposure; this condition requires accumulated service to diverge.
Bounded debt would suffice and is strictly stronger than what the construction
delivers.

## Coverage, beside it

```text
COVERAGE   latent opportunity  ->  represented opportunity   EXTERNAL
SERVICE    represented opportunity  ->  processing           INTERNAL
```

Independent in both directions, exhibited both ways. Consumer-relative, with
every fixture naming its class. Splits into criticism coverage and opportunity
coverage. And no function of represented history alone can imply it.

## Contents

- `SERVICE_REALIZATION.md` — the service theorem and its assumptions, the atomic
  case, what must persist, the liability verdict, the coverage interface, the
  boundary observation, the composition, freeze recommendation.
- `src/schedule.py` — opportunity, entitlement, two schedulers, the theorems.
- `src/coverage.py` — latent/represented streams and the boundary observation.
- `src/cases.py` — SR1-SR12 and CV1-CV8.
- `tests/` — 32 cases. `python3 tests/run.py`.

## What this does not establish

No Lean and no registered claim.

That any priority ranking is correct. Positive standing is structural; how large
a share is, is substantive.

That service produces progress, promotion or convergence. `SR12` has unbounded
service and concludes nothing.

Quantitative coverage anywhere; the stronger fractional form is offered and no
consumer needs it.

That the fixtures witness divergence. They are finite and the proxies are named
as proxies.
