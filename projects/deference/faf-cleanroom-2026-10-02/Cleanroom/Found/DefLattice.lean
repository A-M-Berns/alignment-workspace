import Cleanroom.Found.DefLattice.Expert
import Cleanroom.Found.DefLattice.Notions
import Cleanroom.Found.DefLattice.Menu
import Cleanroom.Found.DefLattice.BetClass
import Cleanroom.Found.DefLattice.TwoOptionFinite
import Cleanroom.Found.DefLattice.TwoOptionLUV
import Cleanroom.Found.DefLattice.Witness

/-!
# `def-lattice`: the deference lattice over FAF — definitions of record

Root module. A dependent imports this one name (or the definitions module alone:
`Cleanroom.Found.DefLattice.Expert`, `.Notions`, `.Menu`, `.BetClass`) and gets:

* the expert (`Expert`, `Expert.self`, `Expert.estimate`), the reflection clause (`Reflects`),
  world-valuedness (`Valued`), the quote packages (`WeightQuote`, `CondQuote`) with their
  self-instance projections, the weight functions (`rampAbove`, `rampBelow`, `hardAbove`,
  `hardBelow`, `bandWt`, `hardBand`) and the literal indicator (`literalIndicator`) — `Expert`;
* the notions of record `Tower`, `CondTower`, `ThresholdIneqAbove/Below`,
  `SoftTotalTrustAbove/Below`, `TotalTrust` (= `SoftTotalTrust`), `HardTotalTrustAbove/Below`,
  `HardTotalTrust`, `BandReflection`, `HardValueReflection` — `Notions`;
* menus and Value: `Menu`, `Menu.quote`, `Menu.maxQuote`, `Menu.argmax`, `Follows`, `Value`,
  `BlendQuote`, `BlendValue`, `softmaxBlend`, `rampBlend` — `Menu`;
* the common closure class and the domain-relative notions: `BetClass`, `WeightClosed`,
  `RampClosed`, `GapClosed`, `ConstClosed`, `ArgmaxClosed`, `IsDeferenceClass`, `generated`,
  `TowerOn`, `ThresholdIneqAboveOn/BelowOn`, `ValueOn`; and `no_generable_hard_indicator` —
  `BetClass`;
* the two-option identity, finite-exact (`TwoOptionFinite`: `twoOption_identity_above/below`,
  `twoOption_value_iff_above/below`, `twoOption_value_all_iff`, `twoOption_value_imp_above_frame`) and at the
  LUV level (`TwoOptionLUV`: `twoOptionComb`, `twoOptionComb_expect`,
  `twoOptionComb_value_iff_productForm`, the T6d bridge `value_twoOption_hardAbove/Below`);
* the N+ witness over the paper's inductor (`Witness`: `weightQuoteWitness`,
  `witness_twoOption_value`).
-/
