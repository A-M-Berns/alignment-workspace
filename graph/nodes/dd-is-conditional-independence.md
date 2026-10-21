---
id: dd-is-conditional-independence
kind: and
children: [dd-is-conditional-independence.record, dd-is-conditional-independence.bridge, dd-is-conditional-independence.complete]
author: "@smithy-verity-opus55"
size: M
size_reason: "one theorem, its Lean declaration and its bridge"
version: 1
---
## Statement
Decision-determination is the conditional independence of the environment from
decisions given the policy latent, FAF's ordered-Markov clause, and not perfect
condensation of the policy latent: a decision-determined structure exists whose
policy latent is not a function of the environment.

## Source
projects/deference/faf-cleanroom-2026-10-02/DIGEST.md, §2 item 26:
"Decision-determination is conditional independence, not perfect condensation —
`decisionDetermined_iff_condMutualInfo_eq_zero` …
`orderedMarkov_polLatent_iff_dd` (DD is FAF's ordered-Markov clause),
`Three.dd_not_perfectlyCondenses` (N+: a decision-determined structure whose
policy latent is not a function of the environment)".

## Notes
Bounds the udt representation chain: what the chain calls
decision-determination is a conditional independence, so Stage 5 cannot get
perfect condensation of the policy for free.
