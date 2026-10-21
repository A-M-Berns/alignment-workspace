---
id: li-deference-collapse
kind: and
children: [tt-implies-mart-gap-bets, mart-implies-value-kernel, expert-knows-own-estimates, bet-class-gap-closed, li-deference-collapse.complete]
author: "@smithy-verity"
size: M
size_reason: "two theorem pages, a Lean signature and the implication diagram"
version: 1
---
## Statement
For a novice logical inductor and an inductor expert whose day-n estimates are
published decided facts, Total Trust of the novice in the expert over the
gap-closed class of expert-referencing bets implies Mart (the tower) on that
class, and Mart on that class implies Value (argmax deference on menus drawn
from it).

## Source
projects/deference/note-dump-2026-08-11/wiki/deference-notions.md, Implication
diagram, the Value, Total Trust, Mart entry: "the assembled triangle; all
three collapse at full quantifier strength, and the separations live on
restricted domains".

projects/deference/note-dump-2026-08-11/notes/roadmap.md, Stage 1: "Finish
translating DDB (Deference Done Better) into logical induction".

## Notes
The literal statement is the corpus's construal, taken from
deference-notions.md (an AI-written page): Value is unscoped. Read literally
it is false for one inductor expert (mart-implies-value-refuted-unconditional:
the tower holds and argmax Value fails for the self-expert on the liar probe),
which is why its completeness leaf is low; that low number is the right number
for this statement, and this node keeps it.

The statement in the deck Boundedly Rational Deference scopes Value by
regularity of the menus (filed as deck-collapse-statement, a refinement of
this node), and
the Lean-checked scoped and hedged refinements are
li-deference-collapse-scoped and hedged-value-unconditional. The improvement
claim li-deference-collapse.improvable sits beside this node and names the
directions it can be improved in; its routes condition on this node's validity
or a refinement's, never on its literal truth.

The two arrows are the nodes tt-implies-mart-gap-bets and
mart-implies-value-kernel; the two expert-side conditions their pages name are
the shared assumption expert-knows-own-estimates (exact form; its asymptotic
form expert-knows-own-estimates-asymptotically supersedes it in the
refinements) and the quantifier-domain assumption bet-class-gap-closed. The
converse arrow Value implies Total Trust, kernel-checked for two-option menus
as value_iff_totalTrust_asymptotic, closes the triangle and is not filed here
because nothing in either arrow rests on it.

A shared claim of the line updateful-trust-li, under which the bounded-agent
programme (deference-toward-bounded-agents) and the publication want also sit.
