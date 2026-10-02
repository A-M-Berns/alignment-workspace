import Cleanroom.Fa.FaTheoremA.Defs
import Cleanroom.Fa.FaTheoremA.Analysis
import Cleanroom.Fa.FaTheoremA.Half1
import Cleanroom.Fa.FaTheoremA.Engine
import Cleanroom.Fa.FaTheoremA.LemmaP
import Cleanroom.Fa.FaTheoremA.TheoremA
import Cleanroom.Fa.FaTheoremA.Decided
import Cleanroom.Fa.FaTheoremA.Cee
import Cleanroom.Fa.FaTheoremA.Errata
import Cleanroom.Fa.FaTheoremA.Extensions
import Cleanroom.Fa.FaTheoremA.Witnesses

/-!
# `fa-theorem-a` — Theorem A and Half 1: fixed questions are delay-proof

Root module of the package `Cleanroom.Fa.FaTheoremA` ([[fa-theorem-a-mandate]]; report
[[fa-theorem-a-report]], findings [[fa-theorem-a-findings]], ledger [[fa-theorem-a-ledger]]).

| file | content |
|---|---|
| `Defs` | the quote feature and its ramps (T1 denotation), **T2** generability certificates |
| `Analysis` | the pure-analysis steps (divergence of a gate firing i.o., one-sided averages, subsequence, dominance) |
| `Half1` | `quote_unbiased`, **T3** `half1` (+ dual, corollaries), **T4** `engine_no_persistent_bias` (general + quote); the `δ = 0` junk record |
| `Engine` | the gate argument on a generable `{0,1}` day-set, both signs |
| `LemmaP` | **T6** `lemmaP` (Route A), `lemmaP_const`; `evenDays_pgenerable` (a non-trivial generable day-set) |
| `TheoremA` | **T5** `theoremA`, `theoremA_below`, `claim2`, `viol`/`summable`/`liminf` packaging |
| `Decided` | **T7** the decided case |
| `Cee` | **T8** `cee_ofCrossQuote` (heavy import, own file) |
| `Errata` | **T9** PE2, PE5, the mis-cited engine |
| `Extensions` | **T11** `theoremA_convergentFamily`; the convergence-free limit-range form (OP16); **T10** `calibration_route` |
| `Witnesses` | W1 (N−), W2 (N+, `decided_w2` and `theoremA_w2`), W3 and W4 (N+ for the hypothesis package, N− for the content: the gate / day-set instance is implied by the all-days limit, recorded by `half1_w3_from_convergence`); the only file importing the LIA compiler |

Dependents import the submodules they need (`Defs`, `Half1`, `Engine`, `LemmaP`, `TheoremA`),
none of which imports `Construction.LIACompiler`.
-/
