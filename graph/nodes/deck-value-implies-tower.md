---
id: deck-value-implies-tower
kind: leaf
leaf_kind: step
given: loop-direction-closure
author: "@smithy-verity-opus55"
size: S
size_reason: "one slide and one wiki page"
version: 1
---
## Statement
Value of H toward A on regular menu sequences implies the tower E^H_n E^A_n
V_n ≈_n E^H_n V_n, by Value applied to the menus {V_n − E^A_n(V_n), −ε} and
{E^A_n(V_n) − V_n, −ε} for every rational ε > 0.

## Source
projects/deference/faf-cleanroom-2026-10-02/sources/Boundedly Rational Deference.pdf,
slide 11 ("VALUE ⟹ TOWER": "Suppose VALUE … for regular A_n"; "Consider A_n =
{V_n − E^A_n(V_n), −ε} for rational ε > 0"; "Since ε > 0 was arbitrary,
E^H_n(V_n) ≲_n E^H_n E^A_n V_n"). Mathematics transcribed from the handwritten
slide.

projects/deference/note-dump-2026-08-11/wiki/value-implies-tower.md, the prose
proof of the same arrow.

## Notes
The deck's second arrow. The two probe menus are decided early, so they are
trivially regular (AI reading); the clean room kernel-checked the arrow as
tower_of_value_probes (def-lattice-arrows) and records that slide 11 needs its
ε quantified outside the argument (findings F4), a repair the slide lacks.

Its evidence parent is the forward loop of the triangle
(loop-direction-closure), of which this arrow is one step.
