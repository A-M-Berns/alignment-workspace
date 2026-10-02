import Cleanroom.Bli.BliExactBase.Defs
import Cleanroom.Bli.BliExactBase.Splice
import Cleanroom.Bli.BliExactBase.Mixing
import Cleanroom.Bli.BliExactBase.Tables
import Cleanroom.Bli.BliExactBase.Obstruction
import Cleanroom.Bli.BliExactBase.Convex
import Cleanroom.Bli.BliExactBase.Bundle
import Cleanroom.Bli.BliExactBase.Open
import Cleanroom.Bli.BliExactBase.QuoteLane
import Cleanroom.Bli.BliExactBase.Linked
import Cleanroom.Bli.BliExactBase.Kernel
import Cleanroom.Bli.BliExactBase.Segment
import Cleanroom.Bli.BliExactBase.Bli
import Cleanroom.Bli.BliExactBase.Skeleton
import Cleanroom.Bli.BliExactBase.Live
import Cleanroom.Bli.BliExactBase.Uncharged

/-!
# `bli-exact-base` — Bases with exact finite-time self-trust: the finite-segment splice; the
self-trust obstruction; the open construction

Root module of the package `bli-exact-base` (area `bli`, namespace `Cleanroom.Bli.BliExactBase`).
Report, findings, ledger and open list: `run/wp/bli-exact-base/`.

* **Splice** (construction-facing) — K7a: `spliceHistory H t`, FAF's LIA over `paperDP 𝗜𝚺₁`
  re-priced on the day-`n` small sentences, `n < H`, at finitely many `(day, sentence)` pairs
  (`segmentPatch H`); `splice_computableMarket`, `splice_finiteSupportPerturbation`,
  `splice_isLogicalInductor` (FAF's corrected `thm:ifp` from `paperLIA`).
* **Defs** — the segment forms `D_PC_on`, `D_ND_on`, the small-sentence coherence
  `CoherentOnSmall`/`D_PCsmall`/`D_PCsmall_on`, and their relation to `bli-linkage`'s
  `PCPσ ∧ E1x` on one day.
* **Mixing** — K7b's D-ND mixing lemma (`mixRat_trichotomy`), complete world families and their
  existence, the uniform mixture, free atoms are undecided.
* **Tables** — the segment tables `segmentPrice`/`segmentTable`; K7a instantiated; K7b:
  `segment_D_PCsmall_on`, `segment_D_ND_on`; the literal `D_PC` is empty for every finite
  perturbation of the LIA (`not_coherentOn_of_finiteSupportPerturbation`, `not_D_PC_on_splice`,
  `not_D_PC_lia`); N+ (`splice_ne_lia_day4`, `freshCoord`, `splice_freshCoord_interior`,
  `segment_package`).
* **Obstruction** (FAF-free) — M4's obstruction theorem: on the constrained set the bundle trade
  is worth `1 − rep r₀` in the world `(φ, lit r₀)` whatever the price (`obstruction`,
  `obstruction_slack`), with the artifact check (`constrained_nonempty`, `contrast_acceptable`,
  `obstruction_package`, `obstruction_two_cells`).
* **Convex** — bli-soto-b-026: the self-trust set is convex (`selfTrustSet_convex`), its N−/N+
  members, the wrong-weights finding (`wrong_weights_counterexample`, `mixture_cond_identity`),
  the inter-stage form (`kernel_interstage`).
* **Bundle** — bli-soto-b-025: the `n = 1` bundle market, its two definitional claims
  (`faith`, `nnucell`), the midpoint slack, cross-coordinate incoherence, and its
  non-acceptability against its own bundle trade (`bundleMarket_not_acceptable`).
* **QuoteLane** (construction-facing) — K7c (a)–(c): the splice's own value family and
  `RationalQuoteCode` (`spliceValue`, `spliceQuoteCode`), cell truth / cell quote code / cell
  literals reflected at the splice's rounded price (`spliceCellSentence_reflected`, `_enters`,
  `_neg_enters`), the cell family `spliceCF`, the pinned set eventually the whole segment
  index at `halfRound` (`pinned_eventually_splice`, `exists_segment_day`), the LIA's cells are
  not the splice's (`lia_splice_cells_disagree_day4`), and **stage freshness proved** (K7c (c)):
  no sentence of stage `n` mentions a quotation atom of input `> n`
  (`quotationClaimCode_fresh_of_lt`, by the dovetailer's input bound), so the splice's day-`(n+1)`
  cell literals are fresh at stage `n` for every table and code (`stageFresh_splice`; an OPEN of
  round 0, closed in continuation 1).
* **Linked** — K7d's first lemma: faith at `⊤` charges only candidates valuing `⊤` at `1`
  (`charged_val_top_eq_one`, `charged_top_cell_rep_one`).
* **Kernel** — K7d's Route W, code-oblivious: the slice worlds override every stage-fresh atom of
  day-`(n+1)` cell-literal shape for the three segment coordinates, whatever its code (`litIdx`,
  `LitShape`, `slice`), which dissolves the self-reference of a table that must price its own
  quote literals (header); the eight candidates `tbl3`/`kStates`, the state system `kSystem`,
  the kernel mixture `kMix` with coherence (`kMix_coherentOn`), partition (`kMix_partitionAt`),
  faith (`kMix_faith`), `SpuriousEntails`/`ValuesAtRep` (`kSystem_spuriousEntails`,
  `kSystem_valuesAtRep`), two charged candidates (`kMix_two_charged`).
* **Segment** — K7c (d)/K7d at the splice: the linked table `linkedPrice` (the kernel on every
  day), `linkedSplice H` a logical inductor (`linkedSplice_isLogicalInductor`), `D_PCsmall_on`
  (`linked_D_PCsmall_on`), `freshCoord` at `1/2`; the per-day package inhabited on every day
  `2 ≤ n < H` with the splice's own cell family and two charged candidates
  (`segment_package_inhabited`, N+, no `StageFresh` hypothesis); the identity through
  `nnu_day` on every pinned coordinate (`linked_nnu_day`, `segment_D_NNUcell_on`); the kernel's
  own identity (`kernel_identity`); the realized next state is the charged candidate `q₁`
  (`linked_actual_state_charged`, the chain's first step); **stage-level non-dogmatism is
  incompatible with the linked package** (`linked_package_dogmatic`, `linked_not_D_ND_on`); OPEN `linked_segment_day_exists`
  (a pinned day before the horizon: the quote code's size, findings F16). Continuation 2: the
  family of record re-indexed by `Fin (2 ^ k₀ n)` (`kAt`, `WAt`; the dyadic refinement), the
  boundary day `n + 1 = H` (`linked_boundary`: the realized day-`H` pattern is charged iff the
  LIA's rounded `⊥`/`⊤` cells are `0`/`1`), and the trilemma's sharpness over the inductor
  (`trilemma_sharp_segment`, mandate § 10 (c)).
* **Bli** — K7e: the tent BLI over the splice `spliceBli H t 𝓜 c`; the criterion transported
  from `bli-assemble`'s row of record with its two named obligations (`spliceBli_isLogicalInductor_of`,
  `partial: rewrite certificate open`); the bundle (`spliceBli_package`); the **exact
  small-sentence update at a grid price** (`bli_update_small_exact_of_gridVal`, general), on
  segment days (`spliceBli_update_exact`), at the denominator mesh on every day
  (`spliceBli_update_exact_denominator`, `spliceBli_TB_tierA_denominator`), and at the computable
  `segmentMesh K` for the linked table (`kMixRat_mem_gridVals`, `linkedPrice_mem_gridVals`,
  `exists_segment_K`, `linkedBli_update_exact_segment`, `linkedBli_package`).
* **Skeleton** — `segmentSkeleton H K hK : Skeleton smallIndex (segmentMesh K).d` for
  `bli-witness-lia`: on segment days the law at the linked table `linkedTable n` is the two-point
  law on the two slice marginals `sliceT n`/`sliceF n` (the kernel's decomposition
  `linkedPrice_eq_avg`; `IsProb`, `Balanced` proved; `segKernel`), the tent elsewhere; the coin
  structure at `freshCoord` (`sliceTable_fresh`, `sliceT_ne_sliceF`); the skeleton BLI
  `segmentBli` with the two charged states at `1/2` (`segmentBli_state_half`), the scoped bundle
  (`segmentBli_isBLI_scoped`), the exact update on segment days (`segmentBli_update_exact`), and
  its criterion OPEN (`segmentBli_isLogicalInductor`, mandate § 6).
* **Tables**, continued (continuation 2) — § 10 (b): the seam at horizon `4` (`seam_day4`,
  `seam_package`: small-sentence coherence on every day `< 4`, lost on day `4`).
* **Open** — `ExactlyEnforceable` (bli-slides-043), K7 as its finite-horizon instance
  (`exactlyEnforceable_segment`), `ReflectsRounded`, `BoundedMagnitude`, and the four OPEN rows
  (`exactlyEnforceable_allDays`, `worldMarket_exists`, `bundleMarket_LI_exists`,
  `weakening_exists`).

Not built (report § Not done): the chain across days in table form (the two-point law does not
charge the realized next table — the cell-form chain `linked_actual_state_charged` is the
statement of record), the short cell quote code (the repair of `linked_segment_day_exists`), the
four-cell kernel with interior representatives.
-/
