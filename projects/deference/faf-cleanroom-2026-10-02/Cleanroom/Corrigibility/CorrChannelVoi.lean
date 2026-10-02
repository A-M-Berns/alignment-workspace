import Cleanroom.Corrigibility.CorrChannelVoi.Sensors
import Cleanroom.Corrigibility.CorrChannelVoi.TwoStateForms
import Cleanroom.Corrigibility.CorrChannelVoi.Identity
import Cleanroom.Corrigibility.CorrChannelVoi.AccuracyOnly
import Cleanroom.Corrigibility.CorrChannelVoi.BrainReader
import Cleanroom.Corrigibility.CorrChannelVoi.Consent
import Cleanroom.Corrigibility.CorrChannelVoi.Reliability
import Cleanroom.Corrigibility.CorrChannelVoi.Cells
import Cleanroom.Corrigibility.CorrChannelVoi.Coupling
import Cleanroom.Corrigibility.CorrChannelVoi.Witnesses

/-!
# `corr-channel-voi`: channels, VOI, the brain-reader and the ask

Root module. Files:

* `Sensors` — D1–D3: the button as an experiment, trivial/perfect/product/relabelled
  experiments (API requests to `lit-ddb-frames`), `sensorValue` through `bayesValue`, `voiSensor`,
  `voiGiven`; the sum-of-maxima form; T8(a) Blackwell monotonicity via `tt-finite-frames`; T3's
  general perfect-information bound; Good's equality clause; the A1 bridge
  `voiButton2 = voiSensor button`.
* `TwoStateForms` — T1: the two-state button is `binarySensor α β` relabelled; closed forms.
* `Identity` — T2 the channel identity (general and on `twoState`, regime-free, with the regime
  corollaries and the exact evaluation at `ε*`); E1 the bound made tight.
* `AccuracyOnly` — D5 accuracy-only criteria (Blackwell-monotone), the reflection identity and
  expected-Brier improvement, both holding for every experiment.
* `BrainReader` — D4 the influence defect; the four-action dictionary; T4(a)–(f) as separate
  theorems, including the separation theorem and the imposed-trust agent.
* `Consent` — D6 the consent world; T5 the scan bookkeeping and decision; T6 the ask model.
* `Reliability` — D7 the 1a model in both readings; T7 the discount `eρ`.
* `Cells` — T9 pointwise trust and cellwise vs averaged; T10 free vs forced channel.
* `Coupling` — T11 the decomposition and the direct-cost instance; T12 D1/D4 coupling, the
  inverted sensor, the successor form; T13 the concealment axis; T14 Holtman C9.
* `Witnesses` — every N+/N− cell by `norm_num`.
-/
