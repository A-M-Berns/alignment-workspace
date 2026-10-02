import Cleanroom.Lit.LitShutdownPrefs.Lottery
import Cleanroom.Lit.LitShutdownPrefs.Comb
import Cleanroom.Lit.LitShutdownPrefs.Traj
import Cleanroom.Lit.LitShutdownPrefs.Weak
import Cleanroom.Lit.LitShutdownPrefs.Strict
import Cleanroom.Lit.LitShutdownPrefs.SIS
import Cleanroom.Lit.LitShutdownPrefs.SISWitnesses
import Cleanroom.Lit.LitShutdownPrefs.ThreeTheorems
import Cleanroom.Lit.LitShutdownPrefs.Post
import Cleanroom.Lit.LitShutdownPrefs.PostAppendix
import Cleanroom.Lit.LitShutdownPrefs.PostConsistency
import Cleanroom.Lit.LitShutdownPrefs.Dominated
import Cleanroom.Lit.LitShutdownPrefs.TimestepDominance
import Cleanroom.Lit.LitShutdownPrefs.CostModel
import Cleanroom.Lit.LitShutdownPrefs.Unanimity
import Cleanroom.Lit.LitShutdownPrefs.Drest
import Cleanroom.Lit.LitShutdownPrefs.DrestDerivation
import Cleanroom.Lit.LitShutdownPrefs.Turner

/-!
# `lit-shutdown-prefs`: incomplete preferences and shutdown

Root module of the coherence line of the shutdown literature. A dependent imports this one name
and gets the lottery carrier (`Lottery`, product-form `mass`/`condSum`, `condOn`), the two
preference frameworks (`Weak.*`: weak preference primitive, Sen's corollaries, the six
conditions; `Strict.*`: behavioural strict preference primitive, behavioural indifference/gap),
the shutdown-influencing state and Thornley's three theorems (`SIS.first_theorem_averse`,
`second_theorem`, `third_theorem`) with their witnesses and Thorstad's refuted restatement, the
POST-agency definitions of record (`POST`, `POSL`, `ILPACS`, `Neutrality`, `ReSIC`, `Maximal`) and
chain (with the consistency results on POSL ∧ ILPACS in `PostConsistency`), **`TimestepDominates`** (the definition `corr-landscape` cites) with the TD principle,
witnesses, cost model and ILPACS violation, the unanimity reading of POST, the DReST
usefulness/neutrality results, and Turner's Fact.

Files: `Lottery`, `Comb`, `Traj` (carriers); `Weak`, `Strict` (frameworks W and S); `SIS`,
`SISWitnesses` (Targets 2–4); `ThreeTheorems` (5–6); `Post`, `PostAppendix`, `PostConsistency`,
`Dominated` (7, 8(a)(b), 10, 11);
`TimestepDominance`, `CostModel`, `Unanimity` (8(c), 9, 14, 23, 25); `Drest`, `DrestDerivation` (12, 13, 27);
`Turner` (15).
-/
