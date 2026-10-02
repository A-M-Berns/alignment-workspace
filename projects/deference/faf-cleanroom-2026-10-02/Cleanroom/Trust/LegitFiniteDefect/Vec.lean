import Mathlib.Data.Fin.VecNotation

/-!
# Small-vector evaluation helpers

Package `legit-finite-defect`. Coordinates `≥ 2` of `![…]` vectors are not in the default simp
set; these `rfl` lemmas are used by every witness file (the dependency's `ExamplesFact21` uses the
same pattern). Mathlib-only, so the rational-model files can import it without the frame
dependency.
-/

namespace Cleanroom.Trust.LegitFiniteDefect

/-- The third coordinate of a three-vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec3_two {α : Type} (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl

/-- The third coordinate of a four-vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec4_two {α : Type} (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl

/-- The fourth coordinate of a four-vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec4_three {α : Type} (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl

/-- Coordinate `2` of an eight-vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec8_two {α : Type} (a b c d e f g h : α) : (![a, b, c, d, e, f, g, h] : Fin 8 → α) 2 = c :=
  rfl

/-- Coordinate `3` of an eight-vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec8_three {α : Type} (a b c d e f g h : α) :
    (![a, b, c, d, e, f, g, h] : Fin 8 → α) 3 = d := rfl

/-- Coordinate `4` of an eight-vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec8_four {α : Type} (a b c d e f g h : α) :
    (![a, b, c, d, e, f, g, h] : Fin 8 → α) 4 = e := rfl

/-- Coordinate `5` of an eight-vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec8_five {α : Type} (a b c d e f g h : α) :
    (![a, b, c, d, e, f, g, h] : Fin 8 → α) 5 = f := rfl

/-- Coordinate `6` of an eight-vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec8_six {α : Type} (a b c d e f g h : α) :
    (![a, b, c, d, e, f, g, h] : Fin 8 → α) 6 = g := rfl

/-- Coordinate `7` of an eight-vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec8_seven {α : Type} (a b c d e f g h : α) :
    (![a, b, c, d, e, f, g, h] : Fin 8 → α) 7 = h := rfl

end Cleanroom.Trust.LegitFiniteDefect
