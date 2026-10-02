---
id: deference-toward-bounded-agents
kind: frame
children: [tt-mart-repair-via-bounds-transfer, step-asymptotic-to-finite-time, policy-level-total-trust, step-legitimacy-conditioned-trust]
question: "Does the deference collapse, or an analogue of it, hold for a bounded trained agent deferring to human teachers?"
roots:
  - {id: tt-mart-repair-via-bounds-transfer, role: plan, preset: worst-case, success_class: utopia}
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
A programme, filed as a sub-frame: a frame node whose children are its own
roots, the four steps. Three steps are plan roots of the sub-frame (the
approximate-introspection repair, the finite-time step and the legitimacy
step), each a line of work valued on its own; the policy-level question is a
shared claim of the sub-frame, a proposition the other steps will need and
nobody has yet argued for. The parent frame values this programme as its best
non-conceded step's value, or as the outside option once every step is
conceded; the steps' tasks rank in the parent's list. Within the sub-frame the
classes, the outside option and the undescribed-failure valuation are the top
frame's.

The programme builds on the toy result li-deference-collapse, a shared claim
of the top frame: the repair step argues the asymptotic-introspection picture
of its first arrow back above the bar, and the finite-time and legitimacy
steps relax its setting. The two are kept as separate roots so that each shows
its own standing; a step's statement names the toy result where it rests on
it.

Each plan step's success class is the frame's top class, the convention this
graph uses for plan roots; whether a research programme paying off is the
same event as that class is a question for the maintainer.
