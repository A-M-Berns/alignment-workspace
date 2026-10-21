---
id: updateful-when-appropriate-li
kind: leaf
leaf_kind: step
given: updateful-when-appropriate@valid
action: "Restate oneStep_iff_updateful over a BLI on FAF's logical induction algorithm in its epsilon form, with NoCrossBranch read as a condition on prices that the inductor eventually satisfies."
who: agent
files: [Cleanroom/Bli/UdtBliCore/]
author: "@smithy-verity"
size: M
size_reason: "one paper section and one package report"
version: 1
---
## Statement
A computationally uncertain UDT over a BLI on FAF's logical induction algorithm
behaves updatefully on an observation branch whenever the policy condition has
negligible effect on the other branches' expected utilities and on the branch
probabilities, as an asymptotic theorem.

## Source
projects/deference/faf-cleanroom-2026-10-02/sources/references/bli/understanding-trust/overleaf-final-source/main.tex,
section Counterfactual Mugging With Evidence (quoted on
updateful-when-appropriate);
projects/deference/faf-cleanroom-2026-10-02/packages/udt-bli-core/udt-bli-core-report.md,
the epsilon form eps_updateful.

## Notes
The LI-level version of the finite lemma, not stated anywhere; given the finite
lemma's validity as evidence.
