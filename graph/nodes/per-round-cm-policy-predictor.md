---
id: per-round-cm-policy-predictor
kind: leaf
leaf_kind: step
given: updateless-recovery-domain
author: "@smithy-verity"
size: M
size_reason: "one round section"
version: 1
---
## Statement
An LI/BRIA agent pays with density 1 in per-round counterfactual mugging under
a predictor that reads its policy, and recovers BRIA on its declared recovery
domain.

## Source
projects/decision-theory/rounds/2026-09-29-li-bria-synthesis-spec/PROBLEM_STATEMENT.md,
section 7, A2 (why not delivered: P1' shows every BRIA on the full class
refuses; policy selection over LI, Demski 2017, claims it with no theorem).

## Notes
The A2 diagnostic of the updateless extension; given the recovery-domain
question, since without a domain the recovery half has no content.
