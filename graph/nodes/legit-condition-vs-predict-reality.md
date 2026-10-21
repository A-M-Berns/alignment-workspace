---
id: legit-condition-vs-predict-reality
kind: cases
children: [legit-condition-vs-predict-reality.partition, pic-cvr-global-conditional, pic-cvr-local-conditional, pic-cvr-predict-reality, pic-cvr-hedged-installation, pic-cvr-residual]
rows:
  - {picture: pic-cvr-global-conditional, class: null, observable: never, given: legit-locality-forced}
  - {picture: pic-cvr-local-conditional, class: null, observable: never}
  - {picture: pic-cvr-predict-reality, class: null, observable: never}
  - {picture: pic-cvr-hedged-installation, class: null, observable: never}
  - {picture: pic-cvr-residual, class: undescribed-failure, observable: never, residual: true}
author: "@smithy-verity"
size: M
size_reason: "one paragraph of the maintainer's notes and two finite-frame results"
version: 1
---
## Statement
The right target for an AI in a legitimate-oracle design is its expectation
conditional on legitimacy rather than its prediction of reality with feedback
correlated to reality only in legitimate worlds.

## Source
projects/deference/note-dump-2026-08-11/notes/li-deference.md, section 0.3, the
maintainer: "Perhaps predicting _conditional on_ legitimacy is not quite right.
Rather, the AI should be predicting _reality_, which correlates with feedback
in legitimate worlds, and doesn't in illegitimate worlds. Conditioning on
legitimacy would make the AI confidently predict legitimacy; we want accurate
assessments of risks to legitimacy, too!"

## Notes
A crux the maintainer named with both sides; the pictures are the two sides,
the global and local forms of the first, the hedged-installation variant from
the corrigibility note on value change, and a residual. The first row is
conditioned on the clean room's locality result, which is the maintainer's
objection as a theorem. It re-ranks the gated-Tower route against the
finite-frame transfer as the definition of record, and the corrigibility
branch's legitimacy-detection story. Weights are the maintainer's to place; the
numbers here are the filing session's.
