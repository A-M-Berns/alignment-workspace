import Cleanroom.Bli.BliExactness.Defs
import Cleanroom.Bli.BliExactness.Abstract
import Cleanroom.Bli.BliExactness.PCLIC
import Cleanroom.Bli.BliExactness.Smoothed
import Cleanroom.Bli.BliExactness.Accuracy
import Cleanroom.Bli.BliExactness.Liar
import Cleanroom.Bli.BliExactness.Perturb
import Cleanroom.Bli.BliExactness.Backbone
import Cleanroom.Bli.BliExactness.Open

/-!
# `bli-exactness`: exactness limits — the liar, introspection, the exact/asymptotic gap, PC-LIC,
the asymptotic backbone, expected accuracy

Root module of the package `bli-exactness` (area `bli`, namespace `Cleanroom.Bli.BliExactness`).
Every BLI constraint is an *exact, day-by-day* version of something a logical inductor has only
*asymptotically*; this package draws the boundary of that exactness programme from both sides.

**FAF-free files** (no `Construction.*`; what `def-*` packages may import):
* `Defs` — the midpoint identities `ExactReflection`/`ExactSelfTrustX` (over a cell family; the
  mandate's all-cells shape `ExactReflectionAllCells` is kept only with its collapse lemma) and
  `ExactNNUAt`/`ExactNNU`; **the refuted objects of record, in the interval form** (repair
  round 2): `ExactReflectionInterval`/`ExactSelfTrustXInterval`, `ExactNNUAtInterval`/
  `ExactNNUInterval`, with `ExactReflection.interval`/`ExactNNUAt.interval` (midpoint ⟹ interval);
  `ExactIntro` (used by no theorem), `EntailsIn`/`RespectsEntailment`/`TheoryWorlds`,
  `mixture_respectsEntailment`; the F5 artifact isolated (`decided_conditional`,
  `decided_fails_midpoint`, `top_fails_midpoint`), the encoding checks `top_exact_interval`/
  `top_fails_below_cell`, and **the `⊤`-collapse of the midpoint predicate over every sentence**
  (`coherentTop_forces_zero`, `coherentTop_not_exactReflection`; the interval form's honest
  constraint `coherentTop_interval_below_cell`); Soto's two-clause bundle market
  `sotoBundleHistory` (N−: `sotoBundle_exactSelfTrustX`, `sotoBundle_exactNNUAt`,
  `sotoBundle_top_incoherent`) and the PDF 20 finding `sotoBundle_top_lt_one`.
* `Abstract` — X1 (a) `exact_reflection_fails_abstract` (interval form; midpoint corollary
  `_mid`; N+ `abstractWitness`), X2 (i) `no_sharp_fixed_point`, `no_zero_indicator_fixed_point`,
  bli-soto-b-024's `selfTrust_not_world_local`.
* `PCLIC` — X5: Soto's PC-LIC (strategies as fixed rational vectors — a disclosed variant), the
  `⊤`-shorter refutation `pclic_empty`, the repair `A'` with `A'_telescopes` and
  `noProfit_iff_benefit_nonpos`.
* `Smoothed` — X6 (v) `exactSelfTrustX_imp_smoothed` (+ N− `sotoBundle_smoothed`).
* `Accuracy` — X7 (exact) `accuracy_gap`, `futureErr_le_currentErr`, `accuracy_gap_eq_zero_iff`,
  `tent_gap_pos` (N+), `b0_gap_zero`.

**Construction-facing files** (import `Construction.Paper.Market` / `Construction.Freeze.Oracle`):
* `Liar` — X1 (b) `liar_cell_conditional`, `exact_reflection_fails_liar` (interval form; `_mid`),
  the demoted F5 artifact `liar_midpoint_fails_any_cell` (+ N− `liar_cell_witness`), N+
  `liar_oneSided_witness_of_ne`, `not_exactReflection_of_liar`, `pointWorld_not_exactReflection`;
  X1 (c) `lia_liar_asymptotic`; X1 (d) `bliHistory_liar`, `liar_notMem_Sminus`; X2 (ii)
  `lia_never_exact_on_liar`.
* `Perturb` — X3 `x3_witness` (a computable LI over `paperDP 𝗜𝚺₁`, a point mass on the five
  moved sentences, violating exact D-NNU and D-ST-x on day 1 **in the interval forms**:
  `x3_not_exactNNUAtInterval`, `x3_interval_violation`, `x3_not_exactReflectionInterval`; midpoint
  corollaries `x3_not_exactNNUAt`, `x3_cell_inequality`, `x3_not_exactSelfTrustX`),
  `d_nnu_day1_vacuous` (Known issue 4), and the FAF discharge of Soto's bundle market
  (`quoteAt_cellInjective`, `quoteAt_conjDisjoint`, `objectLevel_quoteAt_of_not_isAnd`,
  `quoteAt_sotoBundle_exactSelfTrustX`, `quoteAt_sotoBundle_top_lt_one`, N−
  `sotoBundle_x3Cells_witness`).
* `Backbone` — X6 (i) `nnu_asymptotic`, (ii) `self_trust_smoothed_const`, (iii)
  `no_predictable_push`/`no_predictable_drop`.
* `Open` — X1 (d3) conditional on B1 being a `ComputableMarket` (`marketLiar`,
  `bli_liar_restoration`, `bli_never_exact_on_own_liar`); **no open statement in Lean** — the
  package's open items (X5 (v), X7-LI) are prose entries in
  `run/wp/bli-exactness/bli-exactness-open.txt`.

Report, findings, ledger: `run/wp/bli-exactness/`.
-/
