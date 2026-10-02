import Cleanroom.Udt.UdtHarmonyBargain.Defs
import Cleanroom.Udt.UdtHarmonyBargain.Perturbed
import Cleanroom.Udt.UdtHarmonyBargain.Lex
import Cleanroom.Udt.UdtHarmonyBargain.Counting
import Cleanroom.Udt.UdtHarmonyBargain.Harmony
import Cleanroom.Udt.UdtHarmonyBargain.Support
import Cleanroom.Udt.UdtHarmonyBargain.Thm111
import Cleanroom.Udt.UdtHarmonyBargain.Neighbour
import Cleanroom.Udt.UdtHarmonyBargain.PropS
import Cleanroom.Udt.UdtHarmonyBargain.Existence
import Cleanroom.Udt.UdtHarmonyBargain.PropSWitness
import Cleanroom.Udt.UdtHarmonyBargain.Translation
import Cleanroom.Udt.UdtHarmonyBargain.TreeWitnesses
import Cleanroom.Udt.UdtHarmonyBargain.Mugging
import Cleanroom.Udt.UdtHarmonyBargain.Critch

/-!
# `Cleanroom.Udt.UdtHarmonyBargain`: harmony, bargaining and the trembling-hand refutation of
Theorem 11.1

Root module of the `udt-harmony-bargain` work package (faf-cleanroom run, 2026-09-30).
Sources: [[superconditioning-mismatched-ontologies]] Part II §9–§13 and the cf-workflow harmony
thread (`repair/harmony.md`). Built over FAF's `SafeParetoImprovements.Game` and EconCSLib's
mixed strategies; depends on `dp-core-tree` (trees, values, the catalogue) and `fix-kakutani`.

* `Defs`: decision-points, `utilGame`, `ParetoDom` (= `Pi.lt`, FAF's strict Pareto improvement),
  the bargaining game `bargain`/`outcome`/`inter`, `BargainNash` ↔ EconCSLib's
  `IsNashEquilibrium`, welfare rules, `wSum`, `argmaxSel`, `exists_welfareSel` (T1, T2).
* `Perturbed`: `Floor`, `IsPerturbedNash`, `THPE` (SC Def. 10.4 verbatim), `THPESelten`,
  `expectedPayoff_update_eq_sum`, `constrainedBR_iff`, `THPE.isMixedNashEq`, `thpe_pure_isNash`,
  `thpe_of_unifPert`, `thpe_of_dominant` (T3).
* `Lex`: the two-player order-`ε` expansion and `uniform_thpe_of_lex` (T3(iii)).
* `Counting`: sums over acceptable sets grouped by membership bits.
* `Harmony`: `Harmonious`, `HarmoniousPure` and the strategic/universe-profile plumbing.
* `Support`: `THPE.support_isBestResponse`, weights, dominance transfer.
* `Thm111`: **Theorem 11.1 refuted** (`thm111_refuted`) with the HA-4′ 2×2 game (T4).
* `Neighbour`: the surviving neighbour (`no_all_but_one_improvement`), finding F2 reversed (T5).
* `PropS`: **Proposition S** — homogeneous harmony is optimality (`harmonious_subset_optimal`),
  uniqueness without safe batnas (`unique_without_safe_batna`) (T7(a),(c)).
* `Existence`: perturbed and trembling-hand equilibria exist, from `fix-kakutani` (T6).
* `PropSWitness`: `exists_harmonious_optimum`, the Stag Hunt, the constant game, Theorem H′(b′)
  on trees (T7(b), T8(b′)).
* `Translation`: `DP(B)` — chance profiles, `U_homogeneous_eq_value`, `homogeneousGame`,
  `pointSpecificGame`, the shared-seed identity (T9).
* `TreeWitnesses`: TN-V2 (updating breaks harmony, T8(d)) and the miniature (T11).
* `Mugging`: the two-prior mugging's veto and the refuted slogan (T10).
* `Critch`: weighted welfare and mixtures, the converse failure, Claim 12.3's identity, Open Q7
  (T12, T13, T14).
-/
