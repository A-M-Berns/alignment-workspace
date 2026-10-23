---
id: the-program
kind: frame
children: [normativity, legitimacy, deference-and-trust, decision-theory, stance-and-level, abstraction-arc, enabling-work]
question: "Which formal account of how humans and AI systems learn from, correct and rely on each other guides AI safety engineering work?"
owner: ["@anson", "@abram"]
narrative: wiki/Architecture.md
roots:
  - {id: normativity, role: plan, preset: worst-case}
  - {id: legitimacy, role: plan, preset: worst-case}
  - {id: deference-and-trust, role: plan, preset: worst-case}
  - {id: decision-theory, role: plan, preset: worst-case}
  - {id: stance-and-level, role: plan, preset: worst-case}
  - {id: abstraction-arc, role: plan, preset: worst-case}
  - {id: enabling-work, role: plan, preset: worst-case}
work:
  - {kind: decision, ref: 2026-10-22--map-canonical-index-program-maintainer-handles}
author: "@smithy-verity"
size: L
size_reason: "seven lines, each a sub-frame, and the question they share"
version: 1
---
## Statement
A formal account of how humans and AI systems learn from, correct and rely on each other, refined until it models their situation, guides AI safety engineering work.

## Source
wiki/Home.md: "How can a powerful reasoner improve without treating every correction as one more signal to optimize around? And how can a person use a more capable future process without giving that process the power to decide what counts as a valid correction?"; wiki/Architecture.md, the common shape of the lines. The former plan frame trust-modelling (projects/deference/note-dump-2026-08-11/notes/roadmap.md, the staged arc from the translation of Deference Done Better through legitimacy to the abstraction stages) is widened into this frame by ruling M2 of 2026-10-22.

## Notes
The one plan under the top frame, owned by both maintainers (ruling M2, DECISIONS.md 2026-10-22). Its roots are the program's lines, each a sub-frame with its own owner: normativity (what learning from reasons requires), legitimacy (what must stay true of the process; corrigibility hangs there as its consumer), deference-and-trust (the trust half of the former updateful logical-induction line), decision-theory (the updateless programme and the LI+BRIA synthesis), stance-and-level (the cruxes every line reads), the abstraction arc and the enabling work. The question's wording is provisional and reserved to the maintainers. Every decomposition below is the filing sessions' reading of public sources.
