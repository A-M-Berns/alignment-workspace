---
id: deck-tt-implies-value-regular
kind: leaf
leaf_kind: step
given: li-deference-collapse-scoped@valid
author: "@smithy-verity-opus55"
size: S
size_reason: "three slides and one wiki theorem"
version: 1
---
## Statement
Soft Total Trust of the human inductor H in the AI inductor A, with A's
chooser satisfying REGULARITY on an efficiently describable menu sequence,
implies E^A_n(a*_n − a^i_n) ≳_n 0 for every option a^i_n and hence Value on
that sequence.

## Source
projects/deference/faf-cleanroom-2026-10-02/sources/Boundedly Rational Deference.pdf,
slides 9 and 10 ("When Does TT ⟹ VALUE?": "So we just need E^A_n(a*_n − a^i_n)
≳_n 0, to establish VALUE"; the counterexample, then "We can rule this out by
assuming: REGULARITY"), and slide 19 (Appendix: "TT implies E^A_n(V_n) ≳_n v ⇒
E^H_n(V_n) ≳_n v"). Mathematics transcribed from the handwritten slides.

projects/deference/note-dump-2026-08-11/wiki/total-trust-implies-value.md, the
Theorem: "Total Trust + introspection + conditional-stability ⟹ argmax Value".

## Notes
The deck's first arrow. Its evidence parent is the Lean-checked scoped theorem
read as an implication (li-deference-collapse-scoped@valid), which proves the
same shape with conditional-stability H3 as the scope condition; whether the
deck's REGULARITY is H3 is the question regularity-is-h3.

The clean room's audit of the slides (def-lattice-arrows findings F3) records
that slide 19 writes s − ε for v − ε, a typo that changes no step.
