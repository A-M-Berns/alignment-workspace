---
id: deference-toward-bounded-agents
kind: frame
children: [tt-mart-repair-via-bounds-transfer, step-asymptotic-to-finite-time, policy-level-total-trust, step-legitimacy-conditioned-trust]
question: "Does the deference collapse, or an analogue of it, hold for a bounded trained agent deferring to human teachers?"
owner: "@abram"
roots:
  - {id: tt-mart-repair-via-bounds-transfer, role: shared-claim, preset: worst-case}
  - {id: step-asymptotic-to-finite-time, role: plan, preset: worst-case, success_class: utopia}
  - {id: policy-level-total-trust, role: shared-claim, preset: worst-case}
  - {id: step-legitimacy-conditioned-trust, role: plan, preset: worst-case, success_class: utopia}
author: "@smithy-verity"
size: L
size_reason: "the programme's four steps, each a research direction with its own sources"
version: 1
---
## Statement
The deference collapse, or its analogue, holds for a bounded trained agent
deferring to human teachers: with finite-time rather than asymptotic
guarantees, with the expert's self-knowledge only approximate, for a policy
rather than an estimator run through argmax, and with trust conditioned on the
legitimacy of the teaching channel.

## Source
projects/deference/note-dump-2026-08-11/notes/roadmap.md, Stage 2: "Then
figure out this legitimacy stuff, and work on the other stuff described in
`li-deference.md` — all the open problems I've already listed for the
formalism."

projects/deference/note-dump-2026-08-11/notes/li-deference.md L70 (the
inner-alignment open problem) and
projects/deference/note-dump-2026-08-11/wiki/open-problems.md, Research
direction (trust the policy, not the decision rule). The decomposition into
four steps is the filing session's reconstruction of those sources, not a list
the maintainer wrote.

## Notes
A programme, filed as a sub-frame of the line updateful-trust-li: a frame node
whose children are its own roots. The finite-time step and the legitimacy step
are plan roots, each a line of work valued on its own; the policy-level
question and the approximate-introspection repair are shared claims of the
sub-frame. The repair is a literal claim the programme builds on rather than a
course of action, so it is a shared claim, and it is the evidence parent of
the asymptotic-introspection row of tt-implies-mart-gap-bets.

The programme asks a second improvement question beside
li-deference-collapse.improvable, toward a different reality: a bounded
trained agent deferring to human teachers. A frame carries no improves field,
so the relation is recorded here: the finite-time step and the policy-level
question each condition on the deck's scoped chain read as an implication
(deck-collapse-statement@valid), the statement of the collapse the maintainer
presents.

The legitimacy step's file belongs to the legitimacy programme's branch; it
stays a root of this sub-frame.

Each plan step's success class is the frame's top class, the convention this
graph uses for plan roots (accepted there as an approximation).
