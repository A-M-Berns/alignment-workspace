---
id: sams-conjecture-li
kind: frame
children: [sams-conjecture-trust-half, fa-inductor-half, good-feedback-derived, fa-trust-half-weak-grades, fa-trust-half-weak-grades.improvable, timely-pointwise-tower-refuted-in-setting, non-paradoxical-cross-process-impossibility, computability-fork, crux-conjecture-information-structure]
question: "Can a fast epistemic process that the human inductor trusts be built from the AI inductor's forecasts of the human inductor's later beliefs?"
owner: "@abram"
roots:
  - {id: sams-conjecture-trust-half, role: plan, preset: worst-case, success_class: utopia}
  - {id: fa-inductor-half, role: plan, preset: worst-case, success_class: utopia}
  - {id: good-feedback-derived, role: plan, preset: worst-case, success_class: utopia}
  - {id: fa-trust-half-weak-grades, role: shared-claim, preset: worst-case}
  - {id: fa-trust-half-weak-grades.improvable, role: shared-claim, preset: worst-case}
  - {id: timely-pointwise-tower-refuted-in-setting, role: shared-claim, preset: worst-case}
  - {id: non-paradoxical-cross-process-impossibility, role: shared-claim, preset: worst-case}
  - {id: computability-fork, role: shared-claim, preset: worst-case}
  - {id: crux-conjecture-information-structure, role: shared-claim, preset: worst-case}
author: "@smithy-verity-opus55"
size: L
size_reason: "a conjecture's two halves and the corpus's results on them"
version: 1
---
## Statement
A fast epistemic process built from the AI inductor's forecasts of the human
inductor's day-f(n) beliefs is trusted by the human inductor in the
logical-induction sense and satisfies the logical induction criterion.

## Source
projects/deference/note-dump-2026-08-11/notes/li-deference.md L35: "In one
discussion about this, Sam Eisenstat conjectured that such a thing could be
constructed by looking only at $A_n$'s beliefs about $H_{f(n)}$, where $f(n)$
is some speedup function. … Would they also be a logical inductor (satisfy the
logical induction criterion)? Would they be trusted by $H$? Those two questions
are the substance of the conjecture, although I consider the trust question to
be more important than the inductor question."

projects/deference/note-dump-2026-08-11/wiki/eisenstat-conjecture-attribution.md
§1 (clarifications).

projects/deference/faf-cleanroom-2026-10-02/sources/Boundedly Rational Deference.pdf,
slide 16 ("Sam's Conjecture", title only).

## Notes
The 'Weak Teacher, Strong Student' line, inside the li-deference notes.
ATTRIBUTION: the conjecture is named for Sam Eisenstat in the public
li-deference note and slides; the analysis here is the corpus's, and under the
attribution page's naming policy an unqualified 'Sam's conjecture' means the
intended structure, whose status is open.

The faithful-acceleration and varying-question results are the corpus's proved
weak-grade forms of the trust half; their wiki edits and follow-ups are filed
under the wiki's upkeep and here.
