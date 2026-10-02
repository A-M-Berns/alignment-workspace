---
id: tt-implies-mart-gap-bets
kind: cases
children: [tt-implies-mart-gap-bets.partition, pic-U-exact-introspection, pic-D-asymptotic-introspection, pic-A-parallel-cuts-amplifier, pic-N-tt-mart-residual]
rows:
  - {picture: pic-U-exact-introspection, class: null, observable: never}
  - {picture: pic-D-asymptotic-introspection, class: null, observable: never}
  - {picture: pic-A-parallel-cuts-amplifier, class: null, observable: never}
  - {picture: pic-N-tt-mart-residual, class: undescribed-failure, observable: never, residual: true}
author: "@smithy-verity"
size: M
size_reason: a two-page proof note with a status header and a pending-rewrite note
version: 1
---
## Statement
For an observable, coherent, introspective expert and a bet class D closed
under the gap construction Z ↦ Z − ⌜E*(Z)⌝ and under negation, Total Trust of
the novice in the expert over D implies Mart on D: for every Z in D, E^H_n(Z)
≈_n E^H_n(⌜E*(Z)⌝).

## Source
projects/deference/note-dump-2026-08-11/wiki/total-trust-implies-mart.md,
Statement (mathematics rendered in plain text): "For an observable, coherent,
introspective expert, Total Trust over a gap-closed class D implies Mart on
D". Status: "PROVED (prose, this page) — verified independently twice at the
wiki level (2026-07-21)"; "not machine-checked".

projects/deference/note-dump-2026-08-11/wiki/deference-notions.md, Status:
"Total Trust ⇒ tower for gap-closed classes — PROVED (prose), unvetted".

## Notes
The pictures are readings of the theorem's setting: the surrogate expert with
exact, provably linear expectations; the inductor expert with asymptotic
introspection; Total Trust granted only over parallel cuts of single bets; and
a residual. The page's own pending-rewrite note is the story behind the second
picture, and the repair it sketches is the node
tt-mart-repair-via-bounds-transfer.

The two independent verifications the status line reports were wiki-level AI
passes; they mint no level here, and no human has traced the proof.
