import Cleanroom.Decision.DpDevicesCatalog.Values
import Cleanroom.Decision.DpDevicesCatalog.TransparentNewcomb
import Cleanroom.Decision.DpDevicesCatalog.ToldYouSo
import Cleanroom.Decision.DpDevicesCatalog.Remark314
import Cleanroom.Decision.DpDevicesCatalog.Miniature
import Cleanroom.Decision.DpDevicesCatalog.Selection
import Cleanroom.Decision.DpDevicesCatalog.Mugging
import Cleanroom.Decision.DpDevicesCatalog.Devices
import Cleanroom.Decision.DpDevicesCatalog.TableMugging
import Cleanroom.Decision.DpDevicesCatalog.TableNewcomb
import Cleanroom.Decision.DpDevicesCatalog.TableToldYouSo
import Cleanroom.Decision.DpDevicesCatalog.AmdDevices
import Cleanroom.Decision.DpDevicesCatalog.LabelReading
import Cleanroom.Decision.DpDevicesCatalog.Grid
import Cleanroom.Decision.DpDevicesCatalog.GridMore
import Cleanroom.Decision.DpDevicesCatalog.Vocabulary
import Cleanroom.Decision.DpDevicesCatalog.Coupling

/-!
# `dp-devices-catalog`: the decision area's regression suite

Root module of the package `Cleanroom.Decision.DpDevicesCatalog`; dependents import this one
name. Every statement is over `dp-core-tree`'s trees, `dp-calibration`'s states and senses, and
`dp-local-opt`'s evaluators; no FAF object is involved (the plan and every survey agree).

* `Values` (T1): the value-polynomial library and the parametrised procedures `tnProc`,
  `tysProc`.
* `TransparentNewcomb` (T2–T4): Proposition 9's table and optima (pure and mixed), Proposition
  10's wedge for every procedure, Remark 7.1's identity `ssaValue = V(C[d_E ↦ ·])`, ZO-9.
* `ToldYouSo` (T5(a)–(c)): Proposition 8's value clause, DY-5's static separations, the
  `fiberForced = siaSum` bridge (D3⁰ = Theorem 1), the D2 inversion.
* `Remark314` (T5(d)): traps versus dilemmas (SL-17's proposal), the masked/limit label at
  `d₅`, D1 on Told-You-So.
* `Miniature`, `Selection` (T6): the fixed-`ε` tie device vs P05's floor device, ZO-16, the
  selection-forcing tree's approved set `{7/11}` and empty D2, the symmetric variant.
* `Mugging` (T7): L1, FP-1/2/4/6, the anthropic indifference axiom.
* `Devices`, `TableMugging`, `TableNewcomb`, `TableToldYouSo`, `AmdDevices` (T8): the device
  table, column by column, every cell universal in the label where the source sampled points.
* `LabelReading` (T11(d)): label-reading environments are not Definition-6 trees; the
  `k`-probe detector is.
* `Grid`, `GridMore` (extension + T9): the vacuity criterion for D2's escape clause, ZO-19's
  verdicts and five grid rows, three of them in all seven columns.
* `Vocabulary` (T11(b)–(c)): experimental identifiability, the assumption-table pointers.
* `Coupling` (T12): the coupling-uncertainty refuser, thin.
-/
