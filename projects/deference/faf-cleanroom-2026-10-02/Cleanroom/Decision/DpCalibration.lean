import Cleanroom.Decision.DpCalibration.Defs
import Cleanroom.Decision.DpCalibration.Basic
import Cleanroom.Decision.DpCalibration.Recording
import Cleanroom.Decision.DpCalibration.Bridge
import Cleanroom.Decision.DpCalibration.Limit
import Cleanroom.Decision.DpCalibration.Theories
import Cleanroom.Decision.DpCalibration.Witnesses
import Cleanroom.Decision.DpCalibration.Examples
import Cleanroom.Decision.DpCalibration.Mugging
import Cleanroom.Decision.DpCalibration.Miniature
import Cleanroom.Decision.DpCalibration.MiniDevices
import Cleanroom.Decision.DpCalibration.Selection
import Cleanroom.Decision.DpCalibration.FiveTen
import Cleanroom.Decision.DpCalibration.ToldYouSo
import Cleanroom.Decision.DpCalibration.Chain
import Cleanroom.Decision.DpCalibration.Devices
import Cleanroom.Decision.DpCalibration.HypWitnesses
import Cleanroom.Decision.DpCalibration.Shadow
import Cleanroom.Decision.DpCalibration.Corollaries
import Cleanroom.Decision.DpCalibration.TieTree
import Cleanroom.Decision.DpCalibration.LimitTie
/-!
# `dp-calibration`: the calibration senses and the device taxonomy

Root module of the package `Cleanroom.Decision.DpCalibration`; dependents import this one name.

**Definitions of record** (frozen once released; see `run/wp/dp-calibration/`):
* `Defs`: `State` (finite-carrier subjective state, no `cf`), `probOf`/`State.pr`, `paySum`,
  `countMass`/`countPay`, `calibratedState` (T1's lemma-let), `jeffreyCond`, the senses
  `StrictOC`, `MaskedOCV v r` / `MaskedOC` (LF, vacuity), `PriorCalibrated`, `ZeroRespecting`,
  `PerRunSSC`, `PerOccSSC`, `APlus`, `SelfTransparent`.

**Theorems and witnesses** (each file's docstring says which mandate target it serves):
`Basic` (T1's lemma-let and uniqueness of the strict state), `Recording` (T5, T6, T15(d)),
`Bridge` (T7, T8, T20), `Limit` (T1's `LimitOC`, T3(a)), `Theories` (T14, T15(a), T16(a), T6),
`Witnesses` (T5 witnesses, `splitWorld`, A.1, `fiveTen`), `Examples` (T2(b), T2(c)(iii), T9,
T13), `Mugging` (T12, T10 rows), `Miniature` + `Selection` (T15(b)(c)), `MiniDevices` (T16(b)),
`FiveTen` (T14), `ToldYouSo` (T2(c)(i)(ii), T3(b)), `Chain` (T4, T10), `Devices` (T16(c)(d):
DF masking, the OPEN test-sequence existence row), `HypWitnesses` (repair round 1: the
hypothesis packages `H_d`, `AlmostFair`, `RecordsForAll` inhabited on `coinQuery` and on
`toldYouSo` at `d₁₀`, Proposition 7 with two different procedures, D2 inhabited on `fiveTen`),
`Shadow` (T11: strict OC factors through the shadow, per-run SSC does not), `Corollaries`
(GP vacuity = `nuPoly = 0`; CA-12′'s tie and non-forcing consequences), `TieTree` (repair
round 2: the one-point tie tree, recorded for every procedure, on which those consequences are
inhabited N+ and every label `procQ q` is calibrated-and-approved; the miniature is recorded by
no procedure, `miniature_not_recordsFor`), `LimitTie` (repair round 2, T3(d): the two-point limit-tie
tree on which D1 approves every label and D2 only `δ_a`; `Corollaries` also holds Lemma 2's converse at
realized points, `limitOCAt_iff_strictOCAt_of_pos`).
-/

