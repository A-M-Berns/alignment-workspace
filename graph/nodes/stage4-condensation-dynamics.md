---
id: stage4-condensation-dynamics
kind: frame
children: [condensation-correspondence-theorem, condensation-correspondence-theorem.improvable, condensation-equivalence-ae, condensation-morphism-notion, observables-carry-correspondence, interpreting-a-belief-haver, dynamics-of-theories, superconditioning-calibration, superconditioning-calibration.improvable, oq-ontology-mismatch, implementation-relations, abstraction-theories-integration, what-abstraction-buys, condensation-scores-explained, condensation-algorithmic-version, condensation-storage-retrieval-tradeoff, notebooks-that-call-each-other, condensation-for-interpretability, permissive-morphisms-needed]
question: "Which notions of function and isomorphism, which role for the observables, and which dynamics of theories carry the same concept between agents and across ontological shifts?"
owner: "@abram"
roots:
  - {id: condensation-correspondence-theorem, role: shared-claim, preset: worst-case}
  - {id: condensation-correspondence-theorem.improvable, role: shared-claim, preset: worst-case}
  - {id: condensation-equivalence-ae, role: shared-claim, preset: worst-case}
  - {id: condensation-morphism-notion, role: plan, preset: worst-case, success_class: utopia}
  - {id: observables-carry-correspondence, role: shared-claim, preset: worst-case}
  - {id: interpreting-a-belief-haver, role: plan, preset: worst-case, success_class: utopia}
  - {id: dynamics-of-theories, role: plan, preset: worst-case, success_class: utopia}
  - {id: superconditioning-calibration, role: shared-claim, preset: worst-case}
  - {id: superconditioning-calibration.improvable, role: shared-claim, preset: worst-case}
  - {id: oq-ontology-mismatch, role: shared-claim, preset: worst-case}
  - {id: implementation-relations, role: plan, preset: worst-case, success_class: utopia}
  - {id: abstraction-theories-integration, role: plan, preset: worst-case, success_class: utopia}
  - {id: what-abstraction-buys, role: shared-claim, preset: worst-case}
  - {id: condensation-scores-explained, role: plan, preset: worst-case, success_class: utopia}
  - {id: condensation-algorithmic-version, role: plan, preset: worst-case, success_class: utopia}
  - {id: condensation-storage-retrieval-tradeoff, role: shared-claim, preset: worst-case}
  - {id: notebooks-that-call-each-other, role: shared-claim, preset: worst-case}
  - {id: condensation-for-interpretability, role: shared-claim, preset: worst-case}
  - {id: permissive-morphisms-needed, role: shared-claim, preset: worst-case}
author: "@smithy-verity-opus55"
size: L
size_reason: "one roadmap stage and three task clusters"
version: 1
---
## Statement
Condensation's notions of function and isomorphism are analyzed and generalized
where the observables are found to carry the correspondence, and a dynamic
account of theories, semantics as a flow over time with ontological shifts,
extends condensation's static picture of the same concept.

## Source
projects/deference/note-dump-2026-08-11/notes/roadmap.md, Stage 4, the
steward's record: "Stage 3 connects to condensation, but furthermore wants a
dynamics of theories: semantics as some kind of flow over time; understanding
ontological shifts." Specific targets: "Spend real time analyzing the notion of
function, and the notion of isomorphism, involved"; "Suspicion to investigate:
the observables are doing some of the work of making sure correspondence is
meaningful, in a way that could possibly be generalized"; "Mine Abram's
LessWrong posts on Condensation"; and the implementation and abstraction task
clusters.

## Notes
A sub-frame of the abstraction arc, the roadmap's Stage 4. Its roots:
Eisenstat's correspondence theorem as the literal object, with its improvement
claim and its routes; the equivalence result; four mid-level plans (the notion
of morphism, interpreting a belief-haver, the dynamics of theories,
implementation relations) and the integration of abstraction theories; the
reading of condensation's scores and its algorithmic version; the
superconditioning account of mismatched ontologies with its improvement claim;
questions from the maintainer's two condensation posts; one crux. The grouping
is the filing session's reading of the roadmap.

The formal objects the stage would use exist: Formalized Agent Foundations
(FAF, pinned at 159ec3f) holds condensation, natural latents, Cartesian frames
and finite factored sets as kernel-checked definitions, which the clean room's
udt-condense-dd and info-voi-latents packages build on.
