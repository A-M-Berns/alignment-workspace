import Cleanroom.Corrigibility.LegitNegDynamic.Histories

/-!
Audit r2 (adversarial) probe for `legit-neg-dynamic`, E5: the operators evaluated on concrete sets
(not through the fixed-point characterisations), so that `M3_anchored_iff`'s "the least fixed point
above `{h₁}` is everything" is seen as an actual two-step iteration `{h₁} ↦ {h₁,h₅,h₆} ↦ univ`,
and `M2op` on `univ` lands on the self-endorsing set. Also: the fixture's `h₃` (manipulation, then
a ruling to TOP) is in `κ h₃` (self-certifying) and not in M1's set. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset

-- the anchored iteration reaches `univ` in two steps
example : M3op 0 {0} = {0, 4, 5} := by decide
example : {0} ∪ M3op 0 {0, 4, 5} = univ := by decide
-- and `{h₁, h₅, h₆}` is *not* a fixed point of the pooled operator (`h₆`'s ruling opens everything)
example : M3op 0 {0, 4, 5} ≠ {0, 4, 5} := by decide

-- M2 on everything is the self-endorsing set, and iterating again is stable
example : M2op 0 univ = {0, 1, 2, 4, 5} := by decide
example : M2op 0 (M2op 0 univ) = M2op 0 univ := by decide

-- `h₃` is self-certifying under M2 yet illegitimate under M1 (the source's M2 negative)
example : (2 : Fin 6) ∈ κ 0 2 ∧ m1Legit 0 (H 2) = false := by decide

-- the `Fin 5` family: the anchored iteration stops at `{h₁, h₅}`
example : {0} ∪ M3op5 0 {0} = ({0, 4} : Finset (Fin 5)) := by decide
example : {0} ∪ M3op5 0 {0, 4} = ({0, 4} : Finset (Fin 5)) := by decide

end Cleanroom.Corrigibility.LegitNegDynamic
