---
id: udt-tiling-foundations
kind: or
children: [tiling-via-causal-order, communication-trust-paper, self-coordination-udt10]
tag: either-suffices
author: "@smithy-verity"
size: L
size_reason: "a chat turn, a paper, working notes and two packages"
version: 1
---
## Statement
The tiling results for expected-utility agents using versions of UDT account
for time and causality, so that an agent modifies only the parts of its policy
causally downstream of the present, by at least one of: the causal-order
formalization of the paper's theorems; a communication-based tiling theorem
with a non-degenerate witness; a direct treatment of UDT 1.0's
self-coordination.

## Source
projects/deference/faf-cleanroom-2026-10-02/sources/references/bli/chats/bli-chat-2024-12-09-udt-tiling-research-agenda.md,
turn 1 (the maintainer): "First, there are some basic things to fix or improve
about the UDT tiling results so far. I haven't accounted for time and causality
to my satisfaction. That is: an agent cannot meaningfully modify its policy
about the past, or about other branches of possibility that are not causally
downstream of the present. Only some forms of self-modification are even
possible. I haven't properly accounted for that." and "There are also other
things that can be improved about these basic results, probably."

projects/deference/faf-cleanroom-2026-10-02/sources/references/bli/understanding-trust/overleaf-final-source/main.tex,
section Tiling & Trust, footnote: "our formalism will avoid an explicit
treatment of time or causality."

## Notes
The fifth mid-level goal, the maintainer's 2024 phase 1. The paper is his with
two co-authors. Live work: the clean-room's udt-paper-tiling and udt-comm-trust
packages and his 2025-06-30 working notes (public copy under the clean-room
sources). The task leaf tiling-brain-dump-synthesis, under the
self-coordination route, synthesizes those notes into next steps. The 'modified
fairness assumptions' heading in the same chat is the AI's, not his, and is a
route of the improvement claim only.
