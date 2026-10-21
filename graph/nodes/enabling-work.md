---
id: enabling-work
kind: frame
children: [enabling-vetting-and-prioritization-system, enabling-machine-checked-corpus, enabling-publication-pipeline, crux-formalize-before-write-up, crux-vetting-or-generation]
question: "Which repository infrastructure makes the trust research vettable and publishable?"
owner: "@maintainer"
roots:
  - {id: enabling-vetting-and-prioritization-system, role: shared-claim, preset: worst-case}
  - {id: enabling-machine-checked-corpus, role: shared-claim, preset: worst-case}
  - {id: enabling-publication-pipeline, role: shared-claim, preset: worst-case}
  - {id: crux-formalize-before-write-up, role: shared-claim, preset: worst-case}
  - {id: crux-vetting-or-generation, role: shared-claim, preset: worst-case}
author: "@smithy-verity"
size: M
size_reason: "three infrastructure claims and two cruxes, each with its own sources"
version: 2
---
## Statement
The repository's infrastructure, an argument map that files and ranks the
agenda, a machine-checked corpus and a publication pipeline, lets the trust
research be vetted and published.

## Source
The repository's own activity as the activity sweep read it: graph/README.md
and graph/PROTOCOL.md (the map), projects/deference/faf-cleanroom-2026-10-02/README.md
(the clean room), PRIORITIES.md and RESEARCH_STATE.md (the publication queue);
the claims and cruxes below cite their sources in their own files.

## Notes
A sub-frame of trust-modelling holding the enabling work the activity sweep
found in the repository. It is a
frame so that infrastructure stands below the agenda's own items (the two axes,
the cruxes, the abstraction arc) rather than beside them. Its roots are shared
claims, not plans: each is a deliverable whose success is a state of the
repository, not an outcome class, so none is an option in the plan decision.
The two cruxes are the filing session's: their Notes say so.
