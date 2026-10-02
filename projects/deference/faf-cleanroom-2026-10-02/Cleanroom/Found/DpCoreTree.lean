import Cleanroom.Found.DpCoreTree.Defs
import Cleanroom.Found.DpCoreTree.Nodes
import Cleanroom.Found.DpCoreTree.Recording
import Cleanroom.Found.DpCoreTree.Basic
import Cleanroom.Found.DpCoreTree.Occurrence
import Cleanroom.Found.DpCoreTree.Agreement
import Cleanroom.Found.DpCoreTree.Seed
import Cleanroom.Found.DpCoreTree.Multilinear
import Cleanroom.Found.DpCoreTree.RootEvents
import Cleanroom.Found.DpCoreTree.Shadow
import Cleanroom.Found.DpCoreTree.Catalogue
import Cleanroom.Found.DpCoreTree.Witnesses
import Cleanroom.Found.DpCoreTree.RecordingThms
import Cleanroom.Found.DpCoreTree.Faithful
import Cleanroom.Found.DpCoreTree.NodeSums
import Cleanroom.Found.DpCoreTree.Screening
import Cleanroom.Found.DpCoreTree.ScreeningWitness
import Cleanroom.Found.DpCoreTree.Tickle
import Cleanroom.Found.DpCoreTree.Bernstein
import Cleanroom.Found.DpCoreTree.BernsteinBack
import Cleanroom.Found.DpCoreTree.SeedMax
import Cleanroom.Found.DpCoreTree.RecordingFull
import Cleanroom.Found.DpCoreTree.Overwrite
import Cleanroom.Found.DpCoreTree.WitnessesR1
import Cleanroom.Found.DpCoreTree.WitnessesR2

/-!
# `dp-core-tree`: concrete decision problems — the tree type and run semantics

Root module of the package `Cleanroom.Found.DpCoreTree`; dependents import this one name.

**Definitions of record** (frozen once released; see `run/wp/dp-core-tree/`):
* `Defs`: the tree type, leaves, `μ_{B,C}` (Definition 6), `ν`, `V`, `occ`, `#_d`,
  point-deviation, `queried`, the path-product spine, Definition 6′ (shared seed, operational).
* `Nodes`: node addresses, `pt`, `edgeOf`, `leavesBelow`, `reach` (`R_q`), node-level policies
  and law, `forcedBelow` / `gNode` (`G_q`).
* `Recording`: Definition 7 and its quantifier forms, F3′, `H*`, decided / pre-query / root
  events.

**Theorems** (each file's docstring says which mandate target it serves):
`Basic` (T1), `Occurrence` (T4, Lemma 1), `Agreement` (T3, SE-2), `Seed` (T2, SE-1; T7(iv)),
`Multilinear` (T7(i)–(iii)), `RootEvents` (T9), `Shadow` (T10), `Catalogue` (T13),
`Witnesses` (T3/T4/T5/T7 witnesses), `RecordingThms` (T5), `Faithful` (T11), `NodeSums` +
`Screening` + `ScreeningWitness` (T6, Lemma 3′), `Tickle` (T12), `Bernstein` +
`BernsteinBack` (T8, Proposition 4; the `⊇` half of the affine collapse under 6′), `SeedMax`
(T2 stretch: the shared-seed optimum is pure), `RecordingFull` (T5 stretch: dp-cf-2-001 refuted
as stated and repaired), `Overwrite` (T6 / findings F1: the overwrite tree, where the run-level
Lemma 3 holds and the world-level clause fails), `WitnessesR1` (witnesses added in repair round
1: `H*`, `ActRecordingOn`, root events, run-level screening, the disposition identity),
`WitnessesR2` (repair round 2: the routed coin-then-query tree — `H*` with an informative
`O_d`, Lemma 3′ and its SSC form instantiated there; T11's nesting N− on the AMD).
-/
