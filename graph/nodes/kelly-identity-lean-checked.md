---
id: kelly-identity-lean-checked
kind: leaf
leaf_kind: task
action: "Lean-check the parimutuel Kelly identity (full-stake wealth shares equal Bayesian mixture weights) and the common-factor cancellation in one clean-room-style file."
who: agent
files: [projects/deference/faf-cleanroom-2026-10-02/]
author: "@smithy-verity-opus55"
size: M
size_reason: "finite algebra in one file"
version: 1
---
## Statement
The Kelly identity and the common-factor cancellation behind the aggregate
logical inductor's weight path are checked in Lean in the clean-room style.

## Source
The identity is a finite algebraic fact: in a parimutuel market where each
agent stakes its whole wealth in proportion to its predictive distribution,
wealth shares after an observation history equal Bayesian mixture weights, and
the common normalizing factor cancels from the shares. Applied to Critch's
recursion for Pareto-optimal policies of agents with different priors (Critch
and Russell, "Servant of Many Masters", arXiv:1701.01302), the normalized
weights are such wealth shares. The weight-path reading is the filing
session's; no public write-up of it exists yet.
