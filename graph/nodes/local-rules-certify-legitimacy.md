---
id: local-rules-certify-legitimacy
kind: cases
children: [local-rules-certify-legitimacy.partition, pic-lr-sound-complete, pic-lr-sound-incomplete, pic-lr-none, pic-lr-residual]
rows:
  - {picture: pic-lr-sound-complete, class: null, observable: never}
  - {picture: pic-lr-sound-incomplete, class: null, observable: never, given: tonk-is-a-sure-loss}
  - {picture: pic-lr-none, class: null, observable: never, given: "trace-nonrecoverability@valid"}
  - {picture: pic-lr-residual, class: undescribed-failure, observable: never, residual: true}
author: "@smithy-verity"
size: M
size_reason: "one chat exchange, one provenance principle and one price-model result"
version: 1
---
## Statement
A set of local rules exists that is sound with respect to semantic legitimacy,
never blessing truth-divergent reasoning, and complete, certifying whatever
tracks truth, on a nontrivial fragment.

## Source
projects/deference/note-dump-2026-08-11/related-chats/2026-07-05__theory-of-legitimacy__f57f5f2d.md,
turn 6 (the AI's proposal of the soundness and completeness pair as the
template, with Prior's tonk as the warning that locally well-formed rules can
be jointly disastrous; an AI reading); the
provenance principle of
projects/deference/note-dump-2026-08-11/notes/legitimacy-theory-v1.md, section
2.3 (every safety-relevant boundary is a fact about "where a value came from");
A. N. Prior, "The Runabout Inference-Ticket", Analysis 21 (1960), for tonk.

## Notes
The crux of Stage 3; two rows are conditioned on results of this branch. It
re-ranks the syntax frame (its value depends on the first two pictures) against
the endpoint-preservation model. The soundness-and-completeness template is the
AI's proposal from the generating chat.
