import Cleanroom.Lit.LitDdbAccuracyMm.Defs
import Cleanroom.Lit.LitDdbAccuracyMm.Basic
import Cleanroom.Lit.LitDdbAccuracyMm.Monotone
import Cleanroom.Lit.LitDdbAccuracyMm.Rules
import Cleanroom.Lit.LitDdbAccuracyMm.Witness
import Cleanroom.Lit.LitDdbAccuracyMm.Forward
import Cleanroom.Lit.LitDdbAccuracyMm.Accuracy
import Cleanroom.Lit.LitDdbAccuracyMm.Examples
import Cleanroom.Lit.LitDdbAccuracyMm.Representation
import Cleanroom.Lit.LitDdbAccuracyMm.MM.Defs
import Cleanroom.Lit.LitDdbAccuracyMm.MM.Value
import Cleanroom.Lit.LitDdbAccuracyMm.MM.Theorem34
import Cleanroom.Lit.LitDdbAccuracyMm.MM.Refute
import Cleanroom.Lit.LitDdbAccuracyMm.MM.Refute3
import Cleanroom.Lit.LitDdbAccuracyMm.MM.Examples

/-!
# lit-ddb-accuracy-mm — root module

DDB's accuracy theorems and Managing Misalignment: the definitions of record (`Defs`), the
reflected-rule/conditional infrastructure (`Basic`), Lemma 7.7 (`Monotone`), the step class of
rules proved gsp/value-directed/continuous (`Rules`), Theorem 3.2 (⟸) with the explicit witness
(`Witness`) and (⟹) by Rothschild's induction (`Forward`), the assembled Theorem 3.2, Theorem
3.1 and fn 40 (`Accuracy`), the fn 46/50/51 witnesses and the proof of DDB's fn 51 conjecture
(`Examples`), the representation story integral-free (`Representation`), and Managing
Misalignment: definitions (`MM.Defs`), MM Theorem 3.2's three readings (`MM.Value`), what
survives of Theorem 3.4 (`MM.Theorem34`), its refutation as printed and the Rain example
(`MM.Refute`), the non-twin refutation of its "if" direction (`MM.Refute3`, audit r1 repair),
the worked examples as exact computations (`MM.Examples`). Dependents (`corr-legit-general`,
`lit-ddb-facts`) import this one name.

Audit round 1 repairs (2026-09-30): `EpistemicValueOn` quantifies over gsp alone, the
value-directedness Campbell-Moore is cited for being derived on the value range
(`IsGspOn.valueDirectedOn`); the two N− refutation witnesses were replaced by non-degenerate ones
(`MM.dup_totalTrust_not_valuesAllSel`, `MM.mm34_backward_refuted` on `G3`).
-/
