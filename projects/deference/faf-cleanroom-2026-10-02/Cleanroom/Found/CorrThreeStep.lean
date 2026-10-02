import Cleanroom.Found.CorrThreeStep.Setting
import Cleanroom.Found.CorrThreeStep.Identities
import Cleanroom.Found.CorrThreeStep.Thresholds
import Cleanroom.Found.CorrThreeStep.GeneralMenu
import Cleanroom.Found.CorrThreeStep.TwoState
import Cleanroom.Found.CorrThreeStep.OffSwitch
import Cleanroom.Found.CorrThreeStep.Witnesses

/-!
# `corr-three-step`: the three-step shutdown dictionary and the identity cluster

Root module of the corrigibility area's definitions foundation. A dependent imports this one
name and gets Setting S (`ThreeStep`), the product-form predicates of record
(`belowThresholdIneq`, `aboveThresholdIneq`), desideratum 1 (`D1At`), the two-option
variables (`Xo`, `deltaMinus`, `deltaPlus`, `delta`), the value-of-information objects, the
two-state instance (`twoState`) with `complianceThreshold` and `epsStar`, and the identity cluster
F1–F4 with its threshold forms, Wängberg's Theorem 9 / Corollary 10, and the N+ witnesses.

Files: `Setting` (definitions of record), `Identities` (F1, F2, F4), `Thresholds` (T5, T9(b)),
`GeneralMenu` (T10, T11, T13), `TwoState` (T3, T7, T8, T9(d), T12), `OffSwitch` (T4),
`Witnesses` (every N+ instance).
-/
