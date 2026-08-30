# Settlement-readiness audit

## Classification table

| item | classification | audit result |
| --- | --- | --- |
| Continuity service | realization theorem already available / inherited theorem | settled upstream under wait responsiveness and non-starvation |
| response surface, weights, defect | schematic definitions | stable for fixed episode-local finite alphabet |
| Persistent Relevance | proved schematic theorem from service plus Surface Fairness | no longer opaque |
| Surface Fairness | schematic structural assumption; scheduler realization requirement | bounded-deficit and work-node interfaces are concrete |
| Answer-Mode Adequacy | schematic eligibility definition and semantic assumption | clean boundary for basic Progress |
| Typed Witness Completeness | proved schematic theorem in the finite repair-kernel fragment | subsumed by Answer-Mode certificate plus kernel lemma |
| Stagnation Persistence | schematic semantic/behavioral definition | positive defect density, independently of gain |
| signed Uptake | schematic learning assumption | unchanged from PR69 |
| episode-local Progress | proved schematic theorem | yields `D/W -> 0`, not closure |
| `SW-density` | convenience lemma only | removed from primary theorem |
| sampled-response elimination | proved optional probabilistic corollary | needs predictable weights and conditional sampling |
| value-security compilation | realization theorem still missing | typed compiler must preserve provenance and nonemptiness |
| projection distance | realization theorem already available | arbitrary changing rational polytopes, finite coordinates, positive tolerance |
| weighted projection error | proved elementary realization bridge | `tau_n -> 0` and `W_N -> infinity` suffice |
| finite confidence-rated modification regret | realization theorem still missing in exact workspace package | standard ingredients; small finite-class/doubling bridge |
| bounded-liability preservation | realization theorem already available conditionally | consumes a uniform cumulative lower bound |
| service-value liability | restricted model result in PR50; realization theorem still missing | one-coordinate interior-margin/no-subsidy route is plausible; multi-coordinate joint margin is open |
| Operative Row Grounding | conditional realization theorem from Grounded Replay | genuine consumer; does not prove Proper Exercise |
| Reason Carry | basic realization requirement | cheap at burden level; fresh successor license required |
| comparison invariance across successors | realization requirement, optional stronger layer | not needed for one fixed tail |
| infinite cross-era revision | explicitly deferred stronger theory | still the diachronic loophole |

## What is ready

The schematic theorem is now compact enough for a settlement pass:

\[
Continuity\ service
+Surface\ Fairness
+Answer\text{-}Mode\ Adequacy
+Uptake
\Longrightarrow No\ Persistent\ Episode\text{-}Local\ Stagnation.
\]

Its quantifiers, conclusion, timing and eligibility boundary are explicit. Persistent
Relevance is derived rather than postulated. The witness result covers finite
stochastic repairs from finitely many defective modes to acceptable modes, not just a
single pair. The mixed/realized distinction has an optional martingale corollary.

## What is not ready

The full reasons/value-security/traderized-inductor realization still has more than
one independent open seam:

1. **Compiler and service-value liability.** Typed reasons must compile to nonempty
   rational regions with legitimate settlement semantics. PR50 provides model evidence
   for bounded contestable enforcement in an isolated one-coordinate,
   positive-margin, stationary/no-subsidy fragment, and a counterexample to naive
   multi-coordinate composition. The restricted result still needs promotion; the
   general joint-margin premise is open.
2. **Exact regret package.** Standard finite confidence-rated external-regret and
   modification-regret ingredients exist, but the workspace lacks the exact anytime,
   effective-mass, causal repair theorem used by the master inequality.

The first is a substantive realization question; the second is a concentrated
technical import/bridge. They are independent, so the state is not accurately
described as needing exactly one more lemma.

## Deliberate non-goals

- eventual closure or a last defective action;
- universal witness completeness for arbitrary reasons;
- correctness or Proper Exercise of an authorized value row;
- dynamic regret over endlessly changing evaluators;
- Coverage before representation;
- a new Continuity lifecycle or scheduler among repairs.

## Recommended next formal target

Formalize the **finite repair-kernel Progress theorem** independently of markets:

> For finite `X,S`, a stochastic kernel fixing `X\S`, rowwise uniform margins over
> nonempty `K_n`, Surface Fairness, signed Uptake and positive-density stagnation imply
> contradiction; equivalently the weighted source mass tends to zero.

This theorem is small, stable, and captures the schematic settlement candidate. In
parallel, the next research obligation should promote PR50's one-coordinate
war-chest-affordability result for an isolated derived repair security and compose it
with bounded-liability preservation. Do not merge that unresolved realization premise
into the schematic formalization.
