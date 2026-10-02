import Cleanroom.Bli.BliAssemble.Defs
import Cleanroom.Bli.BliAssemble.Chain
import Cleanroom.Bli.BliAssemble.Map
import Cleanroom.Bli.BliAssemble.Coding
import Cleanroom.Bli.BliAssemble.SmallList
import Cleanroom.Bli.BliAssemble.Certificate
import Cleanroom.Bli.BliAssemble.Headline
import Cleanroom.Bli.BliAssemble.Process
import Cleanroom.Bli.BliAssemble.Inherit
import Cleanroom.Bli.BliAssemble.Fixpoint
import Cleanroom.Bli.BliAssemble.Lia

/-!
# `bli-assemble` — B1 over FAF's inductor: the non-degenerate BLI is a logical inductor (root)

Root module of the package `bli-assemble` (area `bli`, namespace `Cleanroom.Bli.BliAssemble`),
the assembly of the BLI program's 70 % milestone L2 from `bli-trajectory` (the constructed
market), `bli-superbelief` (the tent terms) and `bli-transfer` (the expressible-overlay transfer
theorem). Imports every file.

* **Defs** (target 0, 1) — `bliOv` (the re-pricing, `bliPrice`'s large branch verbatim),
  `bliHistory_eq_overlay` (**target 1**: `bliHistory Q 𝓜 sk c = overlay (ratHistory Q) (bliOv …)`,
  `L`, exact), `minEntry`, `chainExpr`, `tentExprMap`, `dyadicMesh`.
* **Chain** (target 2) — `chainProbH_singleton_eq_lastMarg` (a), `chainProbH_restart` (b, the
  restart identity at the chain's earliest day), `denoteRat_chainExpr` (c, for **every** Tier-A
  parse).
* **Map** (target 3) — `tentMap : ExprMap (ratHistory Q) (bliOv …)`, all six fields proved;
  `tentMap_fires_two_chain` (the two-atom-with-small-part audit); `tentExprMap_rank`.
* **Coding** (target 0) — `writeOutCoding`: injective on the grid, large, and the write-out
  property `|S m| ≤ log₄ code`.
* **Certificate** (targets 5, 6) — `tentExprRun` and `tentRunAgrees` (proved); **OPEN**
  `tentOracle_exists` (the `FP` oracle) and `bliOv_computableTable` (the table);
  `tentCertificate` from the open oracle.
* **Headline** (targets 4, 7, 11) — **L2, the row of record**: `bliHistory_isLogicalInductor_of`
  (`C`; the certificate and the table as named hypotheses — Status `partial: rewrite certificate
  open`); the second and third forms rest on the open rows; `bliHistory_tent_package`,
  `bliHistory_tent_LI_and_BLI` (transport); `bliHistory_isLogicalInductor_denominator`.
* **Process** (target 9) — L2 over `bliDP` (`L`), `StateLearns`, `bliDP_settles_states`, past
  state atoms are the base's.
* **Inherit** (target 10, L7) — transport on machine-named families (a)–(d), and where it
  stops (e): face positivity, no e.c. family names the next-state atoms, the dichotomy.
* **Fixpoint** (target 9(c)) — `liaStates_eq_of_eq_prefix` (FAF's LIA at day `k` depends on
  the process through stages `≤ k` only), `actualFix`, `actualFix_spec`,
  `exists_stateLearns_fixpoint` (the self-consistent state-learning instance, every process).
* **Lia** (target 8) — `bli_hypotheses_paperDP` (N+ at `paperDP 𝗜𝚺₁`: everything except the
  certificate and the table), `bli_package_paperDP` (with the criterion, resting on the open
  rows), `bliHistory_ne_lia_of_offSupport`, `exists_stateLearns_fixpoint_paperDP`.

Deliverables: `run/wp/bli-assemble/` (`bli-assemble-report.md`, `bli-assemble-findings.md`,
`bli-assemble-ledger.md`, `bli-assemble-open.txt`).
-/
