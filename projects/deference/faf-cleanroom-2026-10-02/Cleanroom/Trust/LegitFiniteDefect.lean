import Cleanroom.Trust.LegitFiniteDefect.Vec
import Cleanroom.Trust.LegitFiniteDefect.Defs
import Cleanroom.Trust.LegitFiniteDefect.Wirehead
import Cleanroom.Trust.LegitFiniteDefect.Corrigibility
import Cleanroom.Trust.LegitFiniteDefect.Detection
import Cleanroom.Trust.LegitFiniteDefect.DerivedSign
import Cleanroom.Trust.LegitFiniteDefect.Mechanism
import Cleanroom.Trust.LegitFiniteDefect.Trace
import Cleanroom.Trust.LegitFiniteDefect.StopGradient
import Cleanroom.Trust.LegitFiniteDefect.Residue
import Cleanroom.Trust.LegitFiniteDefect.LogCompare
import Cleanroom.Trust.LegitFiniteDefect.Settlement

/-!
# legit-finite-defect — root module

The legitimacy defect in finite shadows (faf-cleanroom run, 2026-09-29/30): the definitions of
record (`Defs`), the wirehead iff with the red-team witnesses (`Wirehead`), the corrigibility
sign flip (`Corrigibility`), the detection hierarchy and its characterisation by questions
(`Detection`), the defect sign derived from a `λ`-exaggerated update rule (`DerivedSign`),
mechanism non-identifiability through DDB's Total Trust with the exact quantifier (`Mechanism`),
trace non-recoverability with the identified set (`Trace`), the stop-gradient identity
(`StopGradient`), the steering residue under Brier with the derived closed form (`Residue`), the
log-score signs through the product-comparison device (`LogCompare`) and settlement continuity
(`Settlement`). Dependents (`legit-li-register`, `trust-merge`) import this one name; the
rational-model files (`Trace`, `StopGradient`, `Residue`, `LogCompare`) and `Settlement` import
Mathlib only.
-/
