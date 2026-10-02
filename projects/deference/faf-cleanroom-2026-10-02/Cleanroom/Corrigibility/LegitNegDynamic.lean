import Cleanroom.Corrigibility.LegitNegDynamic.Cells
import Cleanroom.Corrigibility.LegitNegDynamic.Dinkelbach
import Cleanroom.Corrigibility.LegitNegDynamic.T2Floor
import Cleanroom.Corrigibility.LegitNegDynamic.Consultation
import Cleanroom.Corrigibility.LegitNegDynamic.TwoStage
import Cleanroom.Corrigibility.LegitNegDynamic.Blackmail
import Cleanroom.Corrigibility.LegitNegDynamic.Capture
import Cleanroom.Corrigibility.LegitNegDynamic.Investment
import Cleanroom.Corrigibility.LegitNegDynamic.Dominance
import Cleanroom.Corrigibility.LegitNegDynamic.Revision
import Cleanroom.Corrigibility.LegitNegDynamic.Abolition
import Cleanroom.Corrigibility.LegitNegDynamic.Histories
import Cleanroom.Corrigibility.LegitNegDynamic.Partial

/-!
# `legit-neg-dynamic`: legitimacy negatives — dynamics, blackmail and self-reference (clusters D–E)

Root module of the package (faf-cleanroom run, 2026-09-30). Namespace
`Cleanroom.Corrigibility.LegitNegDynamic`; depends on `legit-neg-static` (the `Problem` of record,
the proposals, readouts, scorings and toys) and `legit-neg-pricing` (`Basic`, `Scoring`,
`Inertness`, `Timing`, `Lexical`). Modules, in dependency order:

- `Cells` — definition (a): partitions, cell policies, the T1 objectives of a policy, the tower
  identity, D2(i) (dynamic consistency and Good's theorem for every per-terminal utility) and its
  converse, the policy problem; D1(ii)'s congruences.
- `Dinkelbach` — D2(iii): the `λ*` lemma over any `Problem`, its T2 and T1 forms, the cellwise
  identification of updateless P2 with P3 at `W ≡ λ*`, V2, the D2(ii) instances.
- `T2Floor` — D1: the cell formula on `toyD`, margin `v`, the neighbourhood corollary, the knife-edge,
  P2's cell threshold, R2's tie.
- `Consultation` — D3: S2 referenced to the agent's actual information; V3's exact condition; the
  graded-EU register; the negligence escape.
- `TwoStage` — definition (b): lotteries, policy-dependent two-stage problems, the surely-void floor.
- `Blackmail` — D4: every updateful proposal yields; P2 updatelessly under S1/S3; V4; the anger term
  and its identification failure over every function of the on-path distribution.
- `Capture` — D5: the floor on the capture toy, the window, `P(L)`'s inconsistency, the graded and
  lexical escapes and their price, V5's deontic layer.
- `Investment` — D6: the four architectures, 2-032's lemma, the thresholds, V6.
- `Dominance` — E1: anticipation-robustness is branchwise dominance.
- `Revision` — E2/E3 and E6: the revision toy, `Δ`, the exact case analysis, the knife-edge and the
  Lipschitz bound, the odds lemma, the rules layer, the refuted "iff" and its surviving neighbour,
  the two-rule shadow.
- `Abolition` — E4: cdot manipulates iff `ρ > v/m`, the graded thresholds, the lexicographic and
  prospective escapes.
- `Histories` — E5: the fixture's histories and `stepOk`, M1's sets and incentive, M2's `2^5` fixed
  points, M3's degeneracy and 2-021, M4, V-E5's retroactive reading, 2-027.
- `Partial` — the extension: the crossing lemma and the family with threshold `σ̂ = 7/9`.

Deliverables: `run/wp/legit-neg-dynamic/legit-neg-dynamic-{report,findings,ledger}.md`, `-open.txt`.
-/
