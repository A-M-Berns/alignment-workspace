---
id: malign-hypothesis-window
kind: leaf
leaf_kind: step
author: "@smithy-verity"
size: S
size_reason: "one paragraph of the maintainer's notes"
version: 1
---
## Statement
Malign hypotheses can end or corrupt the training process before the asymptotic
elimination the guarantees rely on applies.

## Source
projects/deference/note-dump-2026-08-11/notes/li-deference.md, section 0.3:
"Malign hypotheses will be eliminated by the training process _eventually_, if
the process continues indefinitely, but realistically, malign hypotheses could
cause catastrophic problems which end or corrupt the training process before
that point."

## Notes
A risk story in the maintainer's words, with role risk-story in this sub-frame;
its outcome class is unplaced and the corrigibility branch may place it. It is
the reason the finite-time crux matters.
