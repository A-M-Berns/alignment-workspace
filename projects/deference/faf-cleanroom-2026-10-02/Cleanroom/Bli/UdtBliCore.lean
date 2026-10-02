import Cleanroom.Bli.UdtBliCore.Defs
import Cleanroom.Bli.UdtBliCore.Basic
import Cleanroom.Bli.UdtBliCore.Product
import Cleanroom.Bli.UdtBliCore.ProductUtil
import Cleanroom.Bli.UdtBliCore.Decomposition
import Cleanroom.Bli.UdtBliCore.Updateful
import Cleanroom.Bli.UdtBliCore.Good
import Cleanroom.Bli.UdtBliCore.Mugging
import Cleanroom.Bli.UdtBliCore.OfSkeleton
import Cleanroom.Bli.UdtBliCore.Bridges
import Cleanroom.Bli.UdtBliCore.WitnessCorr
import Cleanroom.Bli.UdtBliCore.MaterialConditional
import Cleanroom.Bli.UdtBliCore.Wirehead
import Cleanroom.Bli.UdtBliCore.NodeDescription
import Cleanroom.Bli.UdtBliCore.Lca
import Cleanroom.Bli.UdtBliCore.Desiderata
import Cleanroom.Bli.UdtBliCore.WitnessLayers
import Cleanroom.Bli.UdtBliCore.WitnessXor
import Cleanroom.Bli.UdtBliCore.WitnessGap
import Cleanroom.Bli.UdtBliCore.WitnessEps
import Cleanroom.Bli.UdtBliCore.WitnessTieFree

/-!
# `udt-bli-core` · root module

One-step UDT over a BLI-structured prior: the finite objects (`Defs`), the finite-probability
plumbing (`Basic`), product policy laws and the independent-policy constructor (`Product`,
`ProductUtil`), the branch decomposition and the three influences (`Decomposition`), the
updateful-behaviour lemma exact and ε (`Updateful`), Good's theorem and the one-level
"updateless ⊇ updateful" (`Good`), the mugging prior (`Mugging`), the prior built from a
`bli-finite` skeleton with derived faith and the tent witness (`OfSkeleton`), the two-level
bridges (`Bridges`) and their gap witnesses (`WitnessCorr`), the material-conditional policy point
(`MaterialConditional`), the wireheading identity (`Wirehead`), the node-description lemma
(`NodeDescription`), the latest-common-ancestor refutation (`Lca`), Soto's desiderata
(`Desiderata`, since repair round 2 also with the expectation-level `EntangledExp`), the
remaining witnesses (`WitnessLayers`, since repair round 2 also `CoordinationFree` checked false
and the tent prior's entanglement), the repair-round-1 witnesses: the XOR prior, the
both-rules-indifferent extreme of the point-level package (`WitnessXor`), the full-support
correlated gap and the junk sensitivity of the unguarded prior-optimality predicate
(`WitnessGap`), and the ε-form exercised at `ε > 0` (`WitnessEps`); and the repair-round-2
refutation of record for U4's gloss, tie-free (`WitnessTieFree`). Dependents import this one name.
-/
