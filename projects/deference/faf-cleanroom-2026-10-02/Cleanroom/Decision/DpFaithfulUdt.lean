import Cleanroom.Decision.DpFaithfulUdt.Procs
import Cleanroom.Decision.DpFaithfulUdt.Faithful
import Cleanroom.Decision.DpFaithfulUdt.BestReply
import Cleanroom.Decision.DpFaithfulUdt.SelfConfirming
import Cleanroom.Decision.DpFaithfulUdt.OnePoint
import Cleanroom.Decision.DpFaithfulUdt.Pdc
import Cleanroom.Decision.DpFaithfulUdt.Mugging
import Cleanroom.Decision.DpFaithfulUdt.Kfold
import Cleanroom.Decision.DpFaithfulUdt.KfoldAffine
import Cleanroom.Decision.DpFaithfulUdt.Carrier
import Cleanroom.Decision.DpFaithfulUdt.Cluster
import Cleanroom.Decision.DpFaithfulUdt.PiB
import Cleanroom.Decision.DpFaithfulUdt.ManyPoints
import Cleanroom.Decision.DpFaithfulUdt.DataCost
import Cleanroom.Decision.DpFaithfulUdt.Open

/-!
# `dp-faithful-udt`: faithful updatelessness, self-confirming policies and the first-personal
procedures

Root module of the package `Cleanroom.Decision.DpFaithfulUdt`; dependents (`dp-firstperson-sc`)
import this one name. Over `dp-core-tree`, `dp-calibration`, `dp-local-opt`, `dp-fairness-reloc`,
`dp-edt-udt-fair` (imported file by file; no definition of record restated). See
`run/wp/dp-faithful-udt/`.

**Definitions of record** (frozen once released):
* `Procs`: Definition 17's four procedures — `udtDomain`/`udtArgmax`/`udtProc` (`UDT_{s°,ρ}`, literally
  `dp-calibration`'s `edtProc` at the constant state `s°` on the events `ρ`), `cdtProc`, `cudtProc`;
  Definition 18's theories `TUdt`, `TCdt`, `TCudtAt`/`TCudt`; the counterfactual structure `Cf`
  (total, outside `State`) with v2 Definition 2's `Success` and the packaging `Cf.ofEvents`; the
  prior state `priorState` and **`MaskedPriorCalibrated`** (Definition 11, strict rule, under a
  full-support self-model); the **disposition coordinate of record `polEv U d a`** (the relocated
  tree's `pol_d = a`); Theorem 2's point game `BR` and `Nash`.
* `Faithful`: Definition F1 at the state level (`LawFaithfulAt`, `ValueFaithfulAt`, through a
  projection of the enriched carrier) and the leaf level (`LeafLawFaithfulWrt`, `LeafLawFaithful`,
  with `labEv`).
* `BestReply`: `PureOptimal` (`Π*`). `SelfConfirming`: `SelfConfirming` (advocacy grade).
* `OnePoint`: the R1 state and counterfactual structure on dispositions, `r1State`, `r1Cf`.
* `Pdc`: `occEv`, `occPay`, the per-run state `occState` (D5), `SuccessOn`, D4's `pdcState` and
  `pdcCf`.
* `Mugging`: `LawFaithfulFor`, `mugMat` (the material conditional), `mugWp` (the would-pay
  events), `CfDeviationCalibratedAt`.
* `Kfold`: the 2-fold mugging's leaves `tLeaf`/`hLeaf`, the labelling `kfLab` (`(coin, r)`),
  `transferE`, `concavePayE`, `linearPayE`/`linearRefuseE`.
* `KfoldAffine`: `coinOfK`/`kfLabK` (the `(coin, r)` labelling for any `k`), the first-draw sets
  `firstDrawPayE`/`firstDrawRefuseE`, the payoff-class sets `payClassE`/`refuseClassE` for an
  arbitrary coupling, the round-1 counterexample couplings `halfB`, `b4`.
* `Carrier`: `mug1SscState` (the self-locating state of the self-model on `B₁`).
* `Cluster`: the joint disposition `polTuple`, `clusterDomain`, **`clusterBranch`** (the cluster
  branch of `Π_A`, UDT1.1 = EDT at the relocated root).
* `PiB`: the strongly fair sequential Stag Hunt `seqStag` (`StagPt`, `stage2`, `stagPay`,
  `profHHH`), the recorded-act dispositions `stagRho`, `stag2Rho`, `twoStagPay`.
* `ManyPoints`: the sequential binary trees `seq2 v`, `seq3 v` (`seq3 coalPay = threeCoal`), FA-11's
  `coordPay`, FA-13′'s `tieTable` and output `mixAAAt`, `other`, the thresholds `trembleBound`.
* `Open`: `seq4`, `single`.

**Theorems** (each file's docstring says which target it serves): `Procs` (T1), `Faithful` (T2:
`polEv_lawFaithful`, `polEv_valueFaithful`, **`udtProc_polEv_eq_bestReply`**), `BestReply` (T3:
**`isOptimal_udtProc_iff_support_subset_optima`** as a restatement, `amd_inclusion_not_optimal`),
`SelfConfirming` (T4: **`selfConfirming_iff_nash`**, **`nash_iff_coherent`**,
`third_nash_coherent_not_udtProc` (refutation of the procedure-level identity),
`twoStag_tremble_HH`, `third_tUdt_miscoordinates`; T2's witness `twoStag_udtProc_product`),
`OnePoint` (T5: `udtProc_onePoint`, `udtProc_onePoint_isOptimal_of_almostFair`, FA-6′
`udtProc_strict_collapse`; T8: `cudtProc_r1`, `cudtProc_r1_eq_udtProc`,
`cudtProc_eq_udtProc_of_evidential`), `Pdc` (T11(a): `pdcState_V_eq_ssa`, `piB_eq_ssa_argmax`;
T11(b): `tCudtAt_pdc_iff_coherentPureAt`, `tCudtAt_pdc_iff_coherentAt_of_almostFair`; T12:
**`siaSum_le_iff_ssa`**, `siaSum_eq_mass_mul_ssa`), `Mugging` (T6: the three candidates, FA-3
`mug1_faithful_pay_iff`/`mug1_faithful_refuse_iff`, `no_event_faithful_both`; T8 instances;
T12's witness; F15's `payCf_cudt_pays`), `Kfold` (T7: **`kfold2_concave_no_refuse_faithful`**,
`kfold2_concave_pay_faithful`, the linear rows; T10: `mass_inter_occ_eq_sum_deviatePure` and FP-9's
provisos), `KfoldAffine` (T18(a) at `k = 2`: **`kfold2_norm_faithful_both_iff_affine`**,
`kfold2_norm_pay_faithful_iff`, `kfold2_norm_refuse_faithful_iff`; the round-0 OPEN row refuted,
**`kfold_faithful_iff_affine_refuted`**), `Carrier` (T9: `mug1_act_disposition_asymmetry`,
`mug1_ssc_carrier_collapse`, `mug1_ssc_carrier_identity`, `mug1_pdc_evidential_agree`,
`mug1_oc_carrier_diverge`; T5's witness `mug1_udtProc_onePoint_pays`), `Cluster` (T11(d):
`polTuple_V`, `mem_clusterBranch_iff`, **`clusterBranch_isOptimal`**), `PiB` (T11(c):
`seqStag_stronglyFair`, `seqStag_HHH_coherent_not_optimal`, **`seqStag_pdc_undefined_d2S`**,
`seqStag_piB_vacuous`; T11(e): `twoStag_piA_ne_piB`), `ManyPoints` (T13(iv):
**`seq3_tie_refutation`**; T13(iii): **`seq2_tremble_inclusion`**, `seq2_tremble_udtProc_isOptimal`;
T14(a): `corrLaw_not_pi`), `DataCost` (T15(a): `hamming_le_prod`, `hamming_eq_prod_iff`), `Open`
(T13(ii) on two points: `seq2_strict_bestReply`; the OPEN rows
`kfold_faithful_iff_affine_normalized_open`, `kfold_pay_faithful_iff_locus_open`,
`readingS_seq3_open`, `readingS_seq4_open`, `strict_bestReply_open`).
-/
