import Cleanroom.Trust.TtFiniteFrames.Corr
import Cleanroom.Trust.TtFiniteFrames.Partition
import Cleanroom.Trust.TtFiniteFrames.Chains
import Cleanroom.Trust.TtFiniteFrames.Blackwell
import Cleanroom.Trust.TtFiniteFrames.Strategies
import Cleanroom.Trust.TtFiniteFrames.Sensors
import Cleanroom.Trust.TtFiniteFrames.Geanakoplos
import Cleanroom.Trust.TtFiniteFrames.Weatherson
import Cleanroom.Trust.TtFiniteFrames.Collapse
import Cleanroom.Trust.TtFiniteFrames.SoftCollapse
import Cleanroom.Trust.TtFiniteFrames.Squares
import Cleanroom.Trust.TtFiniteFrames.AntiExpert
import Cleanroom.Trust.TtFiniteFrames.Witnesses
import Cleanroom.Trust.TtFiniteFrames.Join

/-!
# tt-finite-frames — root module

Finite frames: non-transitivity, Blackwell, Geanakoplos and the lab's finite facts, over the
definitions of `lit-ddb-frames`. Correspondences and the conditioning frame (`Corr`); partition
experts, the cross-prior characterization and the support-set reduction (`Partition`); the
non-transitivity chains (`Chains`); Blackwell's theorem (`Blackwell`), the strategy bridge
(`Strategies`) and the binary sensors (`Sensors`); the finite Geanakoplos lemma (`Geanakoplos`)
with Weatherson's example and the near-misses (`Weatherson`); the finite collapse (`Collapse`,
`SoftCollapse`); the composition squares (`Squares`); the anti-expert frame and the diagonal lemma
(`AntiExpert`); the witnesses of the headlines' hypothesis packages (`Witnesses`, repair rounds 1
and 2); the Blackwell join of two deterministic experiments (`Join`, F4, repair round 2).
`SoftCollapseCtsInd` (the FAF instantiation of the soft collapse) is deliberately left out of
this root so that dependents stay Mathlib-only; import it by name.
-/
