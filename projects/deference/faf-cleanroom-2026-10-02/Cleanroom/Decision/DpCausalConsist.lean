import Cleanroom.Decision.DpCausalConsist.PiSums
import Cleanroom.Decision.DpCausalConsist.Truncate
import Cleanroom.Decision.DpCausalConsist.Defs
import Cleanroom.Decision.DpCausalConsist.Collapse
import Cleanroom.Decision.DpCausalConsist.Dag3
import Cleanroom.Decision.DpCausalConsist.Dags
import Cleanroom.Decision.DpCausalConsist.Witness3
import Cleanroom.Decision.DpCausalConsist.Witness3B
import Cleanroom.Decision.DpCausalConsist.Latent
import Cleanroom.Decision.DpCausalConsist.NR
import Cleanroom.Decision.DpCausalConsist.NRValue
import Cleanroom.Decision.DpCausalConsist.NRValueWeak
import Cleanroom.Decision.DpCausalConsist.Regular
import Cleanroom.Decision.DpCausalConsist.TbTheta
import Cleanroom.Decision.DpCausalConsist.TbThetaNR
import Cleanroom.Decision.DpCausalConsist.NRWitness
import Cleanroom.Decision.DpCausalConsist.MixtureWitness
import Cleanroom.Decision.DpCausalConsist.PR
import Cleanroom.Decision.DpCausalConsist.Mixture
import Cleanroom.Decision.DpCausalConsist.MixJunk
import Cleanroom.Decision.DpCausalConsist.Newcomb
import Cleanroom.Decision.DpCausalConsist.OverwriteDag
import Cleanroom.Decision.DpCausalConsist.Bypass

/-!
# `dp-causal-consist`: causal consistency — Theorem 3 over FAF's DAGs, `CDT_π`, Axiom NR,
policy-responsiveness and the LLC readings

Root module of the package `Cleanroom.Decision.DpCausalConsist` (mandate
`run/wp/dp-causal-consist/dp-causal-consist-mandate.md`). Depends on `dp-calibration`,
`dp-local-opt` and, through them, `dp-core-tree`; the DAG side is stated over FAF's
`FactoredSpaces` (`Digraph`, `CPD`, `FactorizesOverDAG`, `Distr`, `condProb`).

* `PiSums`: sum splitting over `Pt Val`; the eight points of `Fin 3 → Bool`.
* `Truncate`: `sum_cpd_prod_eq_one` (T1's one real lemma), the truncated factorization, the
  conditional distribution, descendants and the fixed algebra, Pearl's invariance (T1), the
  local Markov identity at a node (FAF API request), Theorem 3(i) (T2).
* `Defs`: the ℚ→ℝ seam, `expState`/`cfG`, `CfState`, `mixState` (Definition 25's mixture with
  the averaging axiom), cells/`NRAt`/`kPart` (Axiom NR), `Responsive` (Definition PR),
  `TCdtAt`, the LLC predicates.
* `Dag3`: the `Fin 3 → Bool` toolkit (Bernoulli factors, table DAGs, rank acyclicity, CPDs
  from rate tables, evaluation lemmas).
* `Dags`: T3(B) — the direct-effect law, the seven compatible DAGs, the identity on the four with
  `pa(m) ⊆ {ℓ}` and its failure for every CPD on the three with `k ∈ pa(m)` (Pearl invariance);
  T1's non-vacuity; T4(a) the null-act fill.
* `Witness3`: the (S1)-shaped tree family (recording for every procedure, pre-query lesion
  cells, the calibrated state at `⊤`), the direct-effect tree's bridge to `directP`, Theorem
  3(ii) and (iv) instantiated through the theorems (N+).
* `Witness3B`: the (S1) law's joint independence and T3(A) for every compatible structure; the
  noisy-XOR refutation of the pairwise reading of (iii); the N− companion of (iv) (the proviso
  is needed).
* `Latent`: T4(d) — the latent-cancellation structure, `m ⊥ k` as FAF's `CondIndepVar`, the
  interventional rates `1/2`, `23/40`, the mixture effect `−3w/40`.
* `NR`: T8 — the K-partition iff with explicit cell guards, what Axiom NR forces, the
  recording-point coincidence with the evidential criterion.
* `NRValue` (repair round 1): the averaging axiom over a finite partition; Axiom NR forces the
  `V`-component of the act too where every cell meets it positively (`nr_forces_kpart_V`).
* `NRValueWeak` (repair round 2): the same `V`-forcing under `nr_forces_kpart`'s weaker guard —
  every *positive* cell meets the act — plus support regularity of the supposition
  (`nr_forces_kpart_V'`; audit r2 adv N3).
* `Regular`: support regularity of the calibrated and conditioned states; `kPart`'s value formula.
* `TbTheta`: T8 — `TB(θ)`, the five evaluations of `cross` at a mixed label, NR-cf = the
  deviation, the stay-label conditional and the guard failure of `nr_forces_kpart`.
* `TbThetaNR`: T8's N− — a family of `NRAt` components at the stay label whose `cf(cross)`
  differs from `kPart` on a positive-mass event and whose NR-cf(cross) is `−10θ + (1−θ)v` for
  every fill `v` (finding F4 in Lean).
* `NRWitness` (repair round 2): `NRAt` is inhabited where the NR headlines apply — the K-partition
  state is an `NRAt` component on an act every cell meets (`kPartCf`, `kPartCf_nrAt`), `cfK` at
  every mixed label of `TB(θ)`, `cfKS1` at the recorded direct-effect point with `exo := ℓ`, and the
  instantiations of `tb_nrAt_V_cross`/`nrcf_eq_deviation`/`nrcf_ne_forcing` and
  `nr_evidential_at_recording` on them.
* `MixtureWitness` (repair round 2): T5's `labCdt` — the prior supported on one structure makes
  the mixed supposition that structure's `cf^G` (`mixState_V_of_labCdt`) and `CDT_π` its argmax
  (`cdtpi_of_labCdt`); `mechanismDAG`/`mechanismStructure` (`gColl`/`sColl`) for the direct-effect
  tree; and `direct_tcdt_mix_iff_tedt_LMK`, a literal `n = 1` instance of `tcdt_mix_iff_tedt`.
* `PR`: T10 — Definition PR's tautology (kind T) and the four battery rows (overwrite, opaque
  Newcomb, `TB(θ)`, the mugging); Definition-6 verdict numbers on opaque Newcomb (T7).
* `Mixture`: T5 — `CDT_π`, `T_OCC` at a point, the restated corollary (`CDT_π ∩ A_d^+ ⊆ argmax`,
  equality and `T_CDT ↔ T_EDT` under the proviso); T6(b) — conditioning is non-responsive on
  the pre-query algebra at a recorded point.
* `MixJunk` (repair round 1): finding F9's two-point counterexample — the naive Definition-25
  mixture formula fails the averaging axiom on a `State` with junk off the support.
* `Newcomb` (repair round 1): T7(a) — on opaque Newcomb the fill marginal and the value agree
  under 6 and 6′ while the joints differ; T4(c) — the fill is independent of the live act under 6
  and not under 6′ (the shared seed breaks Lemma 3's conclusion); T7(b) — `V(two) − V(one) = S`
  under 6 and `V'(one) − V'(two) = (2p−1)L − S` under 6′.
* `OverwriteDag` (repair round 1): T4(b) on `overwrite` — the temporal structure's truncated law
  differs from the calibrated conditional at the non-recorded point; T6 — the contrast where
  `cf^G` holds `{ℓ = 1}` and conditioning moves it, and `nonResponsive_shared` at recorded points.
* `Bypass` (repair round 1): T4(b) on the bypass tree — coverage fails, the temporal structure is
  compatible, its truncated `k`-rate is `21/200` for both acts while the calibrated conditionals
  are `(12+9q)/(20(1+9q))` and `1/20`; at `q = 1` the realized act's identity holds (finding).
* `Collapse`: Theorem 3(ii)–(iv) — Lemma 3′ in the state, the collapse at recorded points (strict
  and limit calibration), the joint-independence form (iii), `T_CDT ↔ T_EDT` under the proviso (iv).
-/
