---
id: enabling-work
kind: frame
children: [enabling-vetting-and-prioritization-system, enabling-machine-checked-corpus, enabling-publication-pipeline, crux-formalize-before-write-up, crux-vetting-or-generation, enabling-map-as-canonical, enabling-program-site]
question: "Which repository infrastructure makes the trust research vettable and publishable?"
owner: ["@anson", "@abram"]
roots:
  - {id: enabling-vetting-and-prioritization-system, role: shared-claim, preset: worst-case}
  - {id: enabling-machine-checked-corpus, role: shared-claim, preset: worst-case}
  - {id: enabling-publication-pipeline, role: shared-claim, preset: worst-case}
  - {id: crux-formalize-before-write-up, role: shared-claim, preset: worst-case}
  - {id: crux-vetting-or-generation, role: shared-claim, preset: worst-case}
  - {id: enabling-map-as-canonical, role: shared-claim, preset: worst-case}
  - {id: enabling-program-site, role: shared-claim, preset: worst-case}
holds: [item-f1, item-f2, item-f3, item-f4, item-f5, item-f6, item-f7, item-f8, item-10, item-11, item-12, item-13, item-36, item-37, item-38]
work:
  - {kind: decision, ref: 2026-10-22--map-canonical-index-program-maintainer-handles}
  - {kind: round, ref: prompts/2026-08-11-attribution-provenance-names}
  - {kind: round, ref: prompts/2026-08-11-branch-protection}
  - {kind: round, ref: prompts/2026-08-11-contributor-checkers}
  - {kind: round, ref: prompts/2026-08-11-licensing-dco-citation}
  - {kind: round, ref: prompts/2026-08-11-priorities-and-slop}
  - {kind: round, ref: prompts/2026-08-11-workspace-ethos}
  - {kind: round, ref: prompts/2026-08-11-workspace-integration}
  - {kind: round, ref: prompts/2026-08-16-wiki-in-repo-sync}
  - {kind: round, ref: prompts/2026-08-16-wiki-state-bindings}
  - {kind: round, ref: prompts/2026-08-24-reservation-bar-and-debt}
  - {kind: round, ref: graph}
narrative: wiki/CONVENTIONS.md
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
A sub-frame of the-program holding the enabling work the activity sweep
found in the repository. It is a
frame so that infrastructure stands below the agenda's own items (the two axes,
the cruxes, the abstraction arc) rather than beside them. Its roots are shared
claims, not plans: each is a deliverable whose success is a state of the
repository, not an outcome class, so none is an option in the plan decision.
The two cruxes are the filing session's: their Notes say so.
