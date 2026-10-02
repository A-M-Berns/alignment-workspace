import Cleanroom.Li.LiSpliceCondition.Defs
import Cleanroom.Li.LiSpliceCondition.Splice
import Cleanroom.Li.LiSpliceCondition.Condition
import Cleanroom.Li.LiSpliceCondition.Translate
import Cleanroom.Li.LiSpliceCondition.Open
import Cleanroom.Li.LiSpliceCondition.Transfer
import Cleanroom.Li.LiSpliceCondition.Utility
import Cleanroom.Li.LiSpliceCondition.Perturb
import Cleanroom.Li.LiSpliceCondition.Stopping
import Cleanroom.Li.LiSpliceCondition.Witnesses
import Cleanroom.Li.LiSpliceCondition.DayIndexed
import Cleanroom.Li.LiSpliceCondition.Candidate
import Cleanroom.Li.LiSpliceCondition.DayIndexedWitness

/-!
# `li-splice-condition` — splices, finite perturbations and conditioning on refuted sentences

Root module of package `Cleanroom.Li.LiSpliceCondition` ([[li-splice-condition-mandate]]),
importing every file:

| file | content |
|---|---|
| `Defs` | splice atoms (family 4, sub-family 1), `splice`/`paritySplice`, `parityTrader`, `CriterionPreserving`, `condLeg`/`zeroOut`/`reprice`, `condExpect`, `UndecidedLUV`, `staleHistory` |
| `Splice` | T1: computable splice market, the Convergence-theorem refutation, the parity trader's exact net worth and exploitation with explicit gain, its e.c. certificate, the `o(1)` refutation at the path level and its conditional inductor-level form, the parity trader under summable disagreement |
| `Condition` | T3.1 vacuity at a refuted sentence, T3.2 the junk value and reachability, T3.5 the dichotomy, T3.6 consequences |
| `Translate` | T3.3 the translated traders over FAF's `Trader`: exact on refuted worlds, bounded by explicit sums |
| `Open` | the OPEN statements of record: the translation certificate (B1), the harmonic inductor pair, positivity on a refuted sentence, refreezing, 063(b), Claim CC-limit in a realized-value reading (its unconditional analogue refuted outright), the summable conjecture |
| `DayIndexed` | (repair rounds 1–2) 063(a)'s "inductor over a process" readings: the growing-conjunction reading is FAF's theorem with no floor (the inventory's covered case); the learned-past reading proved with the floor *derived* (provability induction; per-day positivity, or a finite patch); the single-condition reading over an accumulating process refuted at the alternating instance, with the floor inhabited by a finite patch; the (B3) sharpening (every e.c. selling schedule on a refuted sentence is summable) |
| `Candidate` | (repair round 2) 063(a) in the source's own reading — unchosen candidates with an exploration floor, held by no process: gated non-exploitation through FAF's conditioning translator (`conditioned_candidate_not_gatedExploits`) |
| `DayIndexedWitness` | (repair rounds 1–2) the 063(a) refutation over `paperDP 𝗜𝚺₁` with the explicit exploit; the growing reading in FAF's consistent branch; the candidate reading's hypotheses inhabited; the learned-past N− (constant family) and the varying N+ over FAF's LIA of the atom prefix process |
| `Transfer` | T3.4/T3.5 the two horns over the criterion (modulo B1), computable markets of `zeroOut`/`reprice`, the conditional identity |
| `Utility` | T4: undecided LUVs, `hval` as a hypothesis (and its failure), antitone limit CDF given implications, the limit as a prior, obedience versus deference |
| `Perturb` | T2: criterion preservation, finite patches versus whole-day overwrites, Statement 2(a) at the finite-coordinate grain, the grade lattice over bare sequences, tail properties |
| `Stopping` | T5: LI adapted stopping (summed `ccee`) |
| `Witnesses` | the N+ packages over `liaHistory (paperDP 𝗜𝚺₁)` |

Deliverables: `run/wp/li-splice-condition/li-splice-condition-{report,findings,ledger}.md`,
`li-splice-condition-open.txt`.
-/
