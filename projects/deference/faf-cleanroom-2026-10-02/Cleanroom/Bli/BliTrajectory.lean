import Cleanroom.Bli.BliTrajectory.Defs
import Cleanroom.Bli.BliTrajectory.Parser
import Cleanroom.Bli.BliTrajectory.Lemmas
import Cleanroom.Bli.BliTrajectory.Degenerate
import Cleanroom.Bli.BliTrajectory.Partition
import Cleanroom.Bli.BliTrajectory.Update
import Cleanroom.Bli.BliTrajectory.JournalResponse
import Cleanroom.Bli.BliTrajectory.Refutations
import Cleanroom.Bli.BliTrajectory.Marginals
import Cleanroom.Bli.BliTrajectory.SelfTrust
import Cleanroom.Bli.BliTrajectory.Coherent
import Cleanroom.Bli.BliTrajectory.DenominatorMesh
import Cleanroom.Bli.BliTrajectory.Pinning
import Cleanroom.Bli.BliTrajectory.PartitionWitness
import Cleanroom.Bli.BliTrajectory.TriState

/-!
# `bli-trajectory`: the constructed market over an abstract base, the trajectory prior,
Bayesian update, the finite refutations

Root module of the package `bli-trajectory` (area `bli`, namespace
`Cleanroom.Bli.BliTrajectory`). Imports every file of the package **except `TentModulus`**
(repair round 2: it imports `Cleanroom.Bli.BliSuperbelief.Modulus`, a cross-package dependency
beyond the mandate's `bli-found`/`bli-finite`; whether dependents carry it is the orchestrator's
call — it is gated alongside the root modules); all are finite (no `Measure.lean` exists —
M11/T1-infinite were not attempted — so nothing here imports
`Mathlib.MeasureTheory`/`Mathlib.Probability.Kernel.*`).

* **Defs** (D1–D4) — `smallIndex`, `StateCoding` (+ `decode`, `tableVal`, `exists_stateCoding`),
  `bliStateSystem`, the coding-aware Tier-A parser (`hasFutureAtom`, `NoFutureState`, `parse`,
  `tierA`, `latestEntry`, `Consistent`), the forward chain probability `chainProbH`/`chainMass`,
  `tierAPrice`, `bliPrice`, `bliHistory`, B0 (`pointMass`, `extendZero`, `degStep`, `degLaw`,
  `degAt`, `b0Price`, `b0History`), and the abstract helpers (`marginalMass`, `marginalJoint`,
  `FaithMarginal`, `BayesRatio`, `TB_on`, the scoped predicates `E2xScoped`/`E3Scoped`/
  `E3finScoped`/`FaithMarginalScoped`/`IsBLI_RomanScoped`, `KernelLip`).
* **Parser** — the parses of every constraint shape, largeness of anything mentioning a future
  candidate atom, `latestEntry`/`Consistent`, the day shift `parse_of_parse_succ`, the
  `chainProbH` algebra (restart identity `chainProbH_cons_succ`, path positivity), price unfolding.
* **Lemmas** (M1, M3) — the F8 constraint lemmas (`bli_small`, `bli_state`, `bli_cond2_scoped`,
  `bli_cond3_scoped`, `bli_cond3fin_scoped`, `bli_balance`, `bli_partition`, `bli_update_small`,
  `bliHistory_mem_Icc`, `bli_E1r_of_grid`; all `L`), the scoped bundle `bliHistory_isBLI_scoped`,
  the tent instance's non-degeneracy and the N+ `bliHistory_tent_two_states`.
* **Degenerate** (M2) — `degLaw_balanced_iff`, `degLaw_not_kernel`, `pointMass_not_nonDegenerate`,
  the continuation `degAt`, B0's constraint rows, `b0_pos_iff`, `b0_unique_state` (N−),
  `faithMarginalScoped_of_e2xScoped`, `b0_simplified_bli` (M7 iv).
* **Partition** (M4) — `e4_iff_partition_mass` over FAF worlds; `bli_e4_and_partition_mass`.
* **Update** (M5, M6) — `bli_update_small_ratio`, `bli_update_small_exact_iff`,
  `bli_bayesRatio_small_of_grid`, `b0_update_small_exact`; `bli_update_tierA_exact`/`_ratio`,
  `bli_TB_on_tierA`, `chainProbH_lipschitz`, `bli_update_tierA_modulus`.
* **JournalResponse** (M8) — `Reflection`, `journalResponse_forced`, `journalResponse_truth`,
  `eisenstat_form_consistent`, `eisenstat_response_unsettled`.
* **Refutations** (M7, M9) — the recipe history and `recipe_isBLI_Roman` (full scope),
  `constraints_not_imply_update`, `faithMarginal_of_e2x`, `faithMarginal_not_imp_e2x`,
  `e2x_full_scope_fails`, `tb_refuted`.
* **Marginals** — the front decomposition of `Traj` (`Traj.cons`/`first`/`tail`,
  `sum_trajGrid_cons`, `trajLaw_cons`) and `chainProbH_eq_trajMass`: the forward chain
  probability is the mass `bli-finite`'s `trajLaw` gives the chain's event.
* **SelfTrust** (M10) — `e2i_smoothed_self_trust`, `e2x_smoothed_self_trust` with FAF's `ctsInd`.
* **Coherent** (M7 (iii), repair round 1) — the four-world mixture `cohHistory`/`cohSystem` and
  `faithMarginal_coherent_not_imp_e2x`: coherence (`CoherentOn ∅ A` on every day, market, base
  and tables) plus `FaithMarginal` (with `E1x`, `E3`, `E4`, `E5`) does not imply `E2x` — for a
  **non-injective** system (two codes, one table; relabelled `(c)` in repair round 2).
* **Pinning** (repair round 2, from audit r2's probe) — `two_state_pinning`,
  `two_state_pinning_scope`: with two *distinct* additive tables, faith in the marginals on a
  `⋏`/`∼`-closed scope forces constraint 2 — why the two-state witnesses need identical tables.
* **TriState** (M7 (iii), repair round 2) — `triHistory`/`triSystem`, nine worlds per day and
  three pairwise distinct coherent tables, every world holding exactly one next-day state
  (`triWorld_unique_state`); `faithMarginal_coherent_distinct_not_imp_e2x`: coherence plus
  `FaithMarginal` does not imply `E2x` even under the injective (partition) reading of "LUV
  coherence".
* **PartitionWitness** (repair round 2, from audit r2's probe) — `pwHistory`/`pwSystem`,
  `partition_package_inhabited` (N+) and `e4_at_witness`: `e4_iff_partition_mass`'s hypothesis
  package is inhabited.
* **DenominatorMesh** (repair round 1) — `denominatorMesh Q`, the mesh on which every actual
  table of a base in `[0, 1]` is a grid table (`actualTable_mem_grid_denominatorMesh`), and the
  grid rows instantiated there with no grid hypothesis (`bli_E1r_denominator`,
  `bli_TB_on_tierA_denominator`, `b0_isBLI_scoped_denominator`, `b0_simplified_bli_denominator`,
  `actualState_eq_actualTable_denominator`).
* **TentModulus** (repair round 2, from audit r2's probe; **not imported here**) —
  `kernelLip_tent` (the tent skeleton has ℓ¹-modulus `4·|S m|`, from `bli-superbelief`'s
  `tentLaw_l1_le`) and `bli_update_tierA_modulus_tent` (the modulus row at the tent with `hQ`
  alone).
-/
