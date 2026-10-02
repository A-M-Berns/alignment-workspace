import Cleanroom.Decision.DpReferentsCdt.Defs
import Cleanroom.Decision.DpReferentsCdt.Readings
import Cleanroom.Decision.DpReferentsCdt.Structure
import Cleanroom.Decision.DpReferentsCdt.Poly
import Cleanroom.Decision.DpReferentsCdt.C2A
import Cleanroom.Decision.DpReferentsCdt.C2B
import Cleanroom.Decision.DpReferentsCdt.OpaqueBasic
import Cleanroom.Decision.DpReferentsCdt.OpaqueRows
import Cleanroom.Decision.DpReferentsCdt.Rows
import Cleanroom.Decision.DpReferentsCdt.Rows2
import Cleanroom.Decision.DpReferentsCdt.SeedRows
import Cleanroom.Decision.DpReferentsCdt.TnV2Row
import Cleanroom.Decision.DpReferentsCdt.Learning
import Cleanroom.Decision.DpReferentsCdt.LearningProbe
import Cleanroom.Decision.DpReferentsCdt.LearningProbeFiber
import Cleanroom.Decision.DpReferentsCdt.Dividends
import Cleanroom.Decision.DpReferentsCdt.Elh
import Cleanroom.Decision.DpReferentsCdt.ElhWitness

/-!
# `dp-referents-cdt`: referents, CDT in the learning setting and the clean-source principle

Root module of the package `Cleanroom.Decision.DpReferentsCdt`; dependents import this one name.

**Definitions of record** (`Defs`): the referent family `refR1Prior`, `refR1State`, `refR2Sia`,
`realFiber`/`refR2Real` (reading 1), `refR2RealObs` (reading 2), `refR3`; the strict value `evStrict`
and its R3 extension `evExt`; the `cf` slot `Cf`, `CfCalibratedAt`, `TCdtAt`, `EvidentialCriterionAt`,
`TEdtExtAt`; the structural hypotheses `ActEvDisjoint`, `ActRecordingStructural`,
`ActRecordingTrembles`, `RecordsForTrembles`; the seed conditionals `paySum'`, `condExp'`,
`refR1State'`; `Readings` proves the two readings of R2-real agree at F3′ points.

**Theorems** (each file's docstring names its mandate targets): `Structure` (C2-L1/L2, C2-1, the
deviation-conditioning identities), `Poly` (the limit-quotient lemma, C2-L3 = FA-20′(i), FA-20′(ii)),
`C2A` (Theorem C2-A′, the recording theorem FA-20′, Theorem C2-B′'s surviving form), `C2B` (Open 11
closed: C2-B′ at the label in play under recording for one full-support deviation),
`Dividends` (FA-25′(1′), the tiling identity, P12-6, Huttegger's manifold, the (E) identity),
`OpaqueBasic`/`OpaqueRows` (opaque Newcomb in closed form and its rows), `Rows`/`Rows2` (the post-act
coin tree, tree J, the AMD, the selection tree, the mugging, Told-You-So, the miniature), `SeedRows`
(Death in Damascus under the shared seed: `V′(q) = −c(1−q)`), `TnV2Row` (FA-18's TN-V2 `d_E` row: the
four real `E`-nodes, R1-prior `(pL, (1−p)L + pS)`, R1-state `(0, S)`, R2-SIA `(pL, (1−p)(L+S))`, R2-real `(0, S)`),
`Learning` (the learning-Newcomb tree and Proposition A), `LearningProbe` (the label-probe Omega:
`V = 9 q_ε`, ITT `−(1−ε)`, LICDT = LIEDT `= −1`, forcing gap `−1` at the real node; `LearningProbeFiber`: its
six-node real fiber, `refR2Real = (10 q_ε − 1, 10 q_ε)`, and R2-SIA's gap `9(1−ε)`), `Elh` (Everitt–Leike–Hutter over a finite tree: Propositions 7 and 10, the one-step coincidence),
`ElhWitness` (the two-round tree in closed form; the reveal instance with SAEDT `1/2` ≠ SPEDT `2/3`).
-/
