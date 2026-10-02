import Cleanroom.Corrigibility.LegitNegDynamic.Blackmail

/-!
Audit r2 (adversarial) probe for `legit-neg-dynamic`: `D4_iv`'s "the anger rule matches the T1
optimum in at most one of `P_det`, `P_com`" is tight — *each* T1 optimum is matched by *some* `f`
(`1/3` matches `P_det`'s refuse, `0` matches `P_com`'s yield), so the impossibility is exactly
"not both with the same `f`", not "never". Not imported by the library.
-/

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing

example (w : ℚ) :
    argmax (t2anger (Pdet w) (fun _ => 1/3)) = argmax (Pdet w).t1 ∧
    argmax (t2anger (Pcom w) (fun _ => 0)) = argmax (Pcom w).t1 := by
  obtain ⟨-, hdet, hcom, hang, -⟩ := D4_iv w (fun _ => 0)
  obtain ⟨hl3, hl0⟩ := t2anger_live w
  refine ⟨by rw [hl3, hdet], ?_⟩
  rw [← hang, hl0, hcom]

-- and the same `f = 0` on `P_det` picks yield, against `P_det`'s T1 optimum refuse
example (w : ℚ) : argmax (t2anger (Pdet w) (fun _ => 0)) ≠ argmax (Pdet w).t1 := by
  obtain ⟨-, hdet, -⟩ := D4_iv w (fun _ => 0)
  rw [(t2anger_live w).2, hdet]; decide

end Cleanroom.Corrigibility.LegitNegDynamic
