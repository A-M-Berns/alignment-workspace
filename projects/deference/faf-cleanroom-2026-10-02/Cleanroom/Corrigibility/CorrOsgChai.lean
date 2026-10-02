import Cleanroom.Corrigibility.CorrOsgChai.Basic
import Cleanroom.Corrigibility.CorrOsgChai.OffSwitch
import Cleanroom.Corrigibility.CorrOsgChai.POOSG
import Cleanroom.Corrigibility.CorrOsgChai.Redundant
import Cleanroom.Corrigibility.CorrOsgChai.FileDeletion
import Cleanroom.Corrigibility.CorrOsgChai.ThreeVersion
import Cleanroom.Corrigibility.CorrOsgChai.Sensor
import Cleanroom.Corrigibility.CorrOsgChai.Cellwise
import Cleanroom.Corrigibility.CorrOsgChai.Conjecture
import Cleanroom.Corrigibility.CorrOsgChai.Milli
import Cleanroom.Corrigibility.CorrOsgChai.Carey
import Cleanroom.Corrigibility.CorrOsgChai.Nayebi

/-!
# `corr-osg-chai`: the CHAI line — off-switch games, PO-OSG, obedience and CIRL

Root module. Files:

* `Basic` — shared `expect` infrastructure on FAF's `Distr` (Dirac, pushforward, the
  fibrewise deterministic-choice lemma, the product distribution).
* `OffSwitch` — T1–T4: Eq. 1's two forms; Hadfield-Menell Theorem 1 derived from Wängberg's
  Theorem 9; Corollary 1 (Eq. 4 corrected) and the chance node; Wängberg's Prop. 4 and the
  five-statistic `Δ ≥ 0`.
* `POOSG` — D2–D3: finite PO-OSGs on FAF's `Distr`; Cor. A.6; Theorem 4.7 (⇐) for coordinated
  garblings; Prop. A.12.
* `Redundant` — Prop. 4.3 (both sides).
* `FileDeletion` — T7(a)–(d) by column dominance; the OSG as a PO-OSG; Example A.13 (T9).
* `ThreeVersion` — Example 4.10 / Prop. 4.9 (T10).
* `Sensor` — D4 the press as an experiment; T15 Blackwell monotonicity; T16 binary-sensor
  dominance; T7(f) the relabeling.
* `Cellwise` — D5 the cellwise model; T11; T7(e); the T12 counter-model.
* `Conjecture` — T14, Conjecture C1's two readings.
* `Milli`, `Carey`, `Nayebi` — T5, T6, T13.
-/
