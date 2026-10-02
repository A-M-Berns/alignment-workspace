import Cleanroom.Lit.LitWeathersonFrames.PoolingWitnesses

/-!
Audit round 1, adversarial lens — probe: the eight-world model `R8` fails **`BetweenUpper`**
itself, not only the full `Between4` that `R8.not_between4` records.

`zhang_finite_upper` is the row of record and assumes only the upper half of constraint 4;
`R8` (deference to both experts, strict betweenness on the disagreement cells, `¬ AgreeAE`) must
therefore fail that upper half — and it does, at the agreement cell `(⅘, ⅘)`, where the posterior
is `17/20 > ⅘`. So the clause the closed reading adds at agreement cells (`c ≤ a`, i.e. the
novice is not more confident than two agreeing experts) is exactly what `R8` lacks. Not imported
by the library.
-/

namespace Cleanroom.Lit.LitWeathersonFrames.AuditR1Adv

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Lit.LitWeathersonFrames

/-- `R8` violates the upper half of the closed reading at the agreement cell `(⅘, ⅘)`. -/
theorem R8_not_betweenUpper : ¬ BetweenUpper R8.C R8.Y R8.A R8.B := by
  intro h
  obtain ⟨c, hc, hle, -⟩ := h (4/5) (4/5)
  norm_num [lev₂, sum_filter, Fin.sum_univ_succ, R8.A, R8.B, R8.C, R8.Y] at hc hle
  linarith

end Cleanroom.Lit.LitWeathersonFrames.AuditR1Adv
