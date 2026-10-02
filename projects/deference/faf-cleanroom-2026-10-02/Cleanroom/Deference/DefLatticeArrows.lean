import Cleanroom.Deference.DefLatticeArrows.Packages
import Cleanroom.Deference.DefLatticeArrows.Transfer
import Cleanroom.Deference.DefLatticeArrows.TowerToTrust
import Cleanroom.Deference.DefLatticeArrows.Fold
import Cleanroom.Deference.DefLatticeArrows.GapBets
import Cleanroom.Deference.DefLatticeArrows.Probe
import Cleanroom.Deference.DefLatticeArrows.ArgmaxValue
import Cleanroom.Deference.DefLatticeArrows.Hedged
import Cleanroom.Deference.DefLatticeArrows.Partition
import Cleanroom.Deference.DefLatticeArrows.WideBand
import Cleanroom.Deference.DefLatticeArrows.Finite
import Cleanroom.Deference.DefLatticeArrows.Wedge
import Cleanroom.Deference.DefLatticeArrows.Counterfactual
import Cleanroom.Deference.DefLatticeArrows.Amplifier
import Cleanroom.Deference.DefLatticeArrows.OneWay
import Cleanroom.Deference.DefLatticeArrows.Witness

/-!
# `def-lattice-arrows`: the arrows of the deference lattice over FAF

Root module (package `def-lattice-arrows`, area `deference`, 2026-09-30). The arrows between
def-lattice's notions — the July wiki's loop Total Trust ⟹ Value ⟹ Tower ⟹ Total Trust and
its diagonals — each in two forms: **per instance** (the theorem, `C`: the instance facts as
hypotheses, the quote packages as data) and **predicate level** (`L`: the existence clauses
named and disclosed). Every "provable identity carried through `E^H_n`" is FAF's
`thm:expprovind` on an explicit `LUVCombination` (`Packages.lean`'s `listComb`), used through
the one ε-outside lemma (`expect_listComb_ge/le/eq_of_eventually`, T0); the expert's side is
always asymptotic (`ExpertFoldAt`, `ExpertFoldCond`, `ExpertPin`), never exact.

| file | target | headlines |
|---|---|---|
| `Packages` | T0, packages | `listComb`, `listCombSyntax`, `expect_listComb_*_of_eventually/slack`, `ExpertFoldAt`, `ExpertFoldCond`, `ExpertPin`, `GapQuote`, `constLUV`, `expertPin_constLUV`, `TowerValued` |
| `Transfer` | T6 | `transfer_instance`, `expert_bound_transfer`, `expert_bound_transfer_of_totalTrust` |
| `TowerToTrust` | T4 | `thresholdAbove/Below_instance_of_tower`, `softAbove/Below_instance`, `bandAbove/Below_instance`, `bandWt_pos_iff`, `*_of_towerValued`, `*_of_tower` |
| `Fold` | T3 | `condTower_instance`, `condTower_of_towerValued`, `towerValued_of_condTower` |
| `GapBets` | T5 | `tower_of_gap_halves`, `tower_instance_of_totalTrust_gapBets`, `towerValued_of_softTotalTrust_gapBets` |
| `Probe` | T11 | `probe_instance`, `tower_of_value_probes`, `towerValued_of_value_of_probes`, `selfEndorse_probe` |
| `ArgmaxValue` | T2 | `value_instance_of_tower_of_selfEndorse`, `value_of_towerValued_of_selfEndorse` |
| `Hedged` | T7 | `hedgedValue_iff_softTotalTrustAbove_instance`, `value_twoOption_hardAbove/Below_iff` |
| `Partition` | T4c | `ctsInd_sub_ctsInd_eq_band`, `softAbove/Below_instance_of_bandFaces`, `BandReflectionWithin`, `totalTrust_of_bandReflectionWithin`, `bandReflectionWithin_iff_totalTrust_onQuotes` |
| `WideBand` | F12 | `totalTrust_of_bandReflection` (no clause: a wide band is the ramp), `bandReflection_iff_totalTrust_onQuotes`, `bandWt_ne_rampAbove_of_narrow` |
| `Finite` | T1 | `decomposition`, `value_of_CM`, `softmax_lower_bound`, `value_of_argmax`, `payoff_gap_le_l1`, `fig2_*`, `fig3_*` |
| `Wedge` | T9 | `boundary_*`, `wedge_*`, `separation` |
| `Counterfactual` | T10 | `ActIndependent`, `witness` |
| `Amplifier` | T8 | `soft_upper/lower_cut_nonneg`, `gap_kill`, `amp_weighted_centered_neg`, `exact_pinch`, `amp_marginal` |
| `OneWay` | T13 | `quotesAvailable_of_marketComputation` and its corollaries |
| `Witness` | witnesses | `transfer_witness`, `expert_bound_transfer_witness` (N−: world-constant source), `softAbove_witness_of_fold`, `towerValued_self` (N+: `TowerValued` for the self-expert over the paper's inductor, no hypothesis) |
-/
