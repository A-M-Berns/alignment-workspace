import Cleanroom.Udt.UdtSupercondition.Mass
import Cleanroom.Udt.UdtSupercondition.Thinning
import Cleanroom.Udt.UdtSupercondition.Defs
import Cleanroom.Udt.UdtSupercondition.Anticipation
import Cleanroom.Udt.UdtSupercondition.DZ
import Cleanroom.Udt.UdtSupercondition.Calibration
import Cleanroom.Udt.UdtSupercondition.Landscape
import Cleanroom.Udt.UdtSupercondition.Canonical
import Cleanroom.Udt.UdtSupercondition.Coherence
import Cleanroom.Udt.UdtSupercondition.Witnesses
import Cleanroom.Udt.UdtSupercondition.WitnessesB
import Cleanroom.Udt.UdtSupercondition.WitnessCountable
import Cleanroom.Udt.UdtSupercondition.KL

/-!
# `Cleanroom.Udt.UdtSupercondition`: superconditioning with mismatched ontologies

Root module of the `udt-supercondition` work package (faf-cleanroom run, 2026-09-29).
Dependents (`corr-reflect-frames`, `dp-firstperson-sc`, `udt-endorse-policy`) import this one name.
Source: [[superconditioning-mismatched-ontologies]] (SC), Part I and §12/§14. Representation:
point-set over countable types with `PMF` (SC §0.2, §0.10); every division sits behind a
positivity hypothesis (`condOn`); calibration-type predicates are multiplicative.

* `Mass`: `mass`, `condOn`, the fibre toolkit.
* `Thinning`: `BoundedDensity`, `couple`, `toSubtype`, `thin`, density steering (`steerThin`).
* `Defs`: `CondModel`, `HasCondModel`, `CommonInfo` (`C₁`, `C₂`), `Compatible`, `CompatibleAE`,
  `SameOntologyModel`, `jointLaw`, thinned models, `productModel`, `SameOntologyModel.dz`.
* `Anticipation`: `AnticipationStructure`, `priorPredictive`, `Calibrated` (SC-internal),
  `Reflective`, `calibrated_implies_reflective` (Prop 3.8 ⇒), `condKernel`, `JointCalibrated`,
  `CMCalibrated` (Def 4.1) and its thinning-closure, `cmCalibrated_of_sameOntology` (Prop 4.2),
  `BridgeCalibrated` (Def 5.1).
* `DZ`: T1 `condModel_exists`, T2 `compatible_boundedDensity`, T3 `compatible_range_subset`,
  T4 `commonInfo_condModel_iff` (Thm 2.4 repaired), T5 `sameOntology_condModel_iff` and the
  finite corollary, the mixture identity (★_C), T6 `trivialCI_condition`.
* `Calibration`: T9 `calibrated_condModel_exists` / `calibrated_condModel_iff` (Thm 4.5),
  T10 `compatible_calibrated_iff_bridgeCalibrated` (Prop 4.7 corrected; a.e. variant
  `BridgeCalibrated.of_compatibleAE_cmCalibrated`; `bridgeCalibrated_trivialCI`), T11
  `CrossCoherent` and `crossCoherent_iff_ineq` (Def 12.2), its collapse
  `crossCoherent_iff_compatible` (via `bridgeCalibrated_exists_of_range`; repair round 1) and the
  fixed-structure `CrossCoherentVia` with `crossCoherentVia_iff`.
* `Landscape`: `JeffreyOnA`, T12 `jeffrey_of_anticipationEvidence` / `jeffrey_of_evidenceCI`,
  T19 `jeffreyOnA_iff_density_const`, T20 `jeffrey_iff_evidenceCI` and
  `thinningClosed_nonrestrictive`.
* `Canonical`: T13 `canonicalPosteriors`, `JeffreyMixtures`, `dzPosteriors`, the inclusions;
  T14 `CalibratedRefinement`, `refinement_kernel_averages` (Prop 6.3),
  `refinement_posteriors_eq_condOn` (Prop 6.4; round-0 name `refinement_top_eq_condOn` kept as an
  alias).
* `Coherence`: T15 `EpistemicallyCoherent`, `CoherentVia`, `Downstream`,
  `epistemicallyCoherent_iff_condOn`, `downstream_isPartialOrder`; T16 `VarAnticipation`,
  `universallyShared`; T17 `UtilityAgreement` and its lemmas.
* `Witnesses`, `WitnessesB`, `WitnessCountable`: every N+ witness and refutation instance
  (`thm24_sufficiency_refuted`, `prop47_refuted`, `reflective_not_calibrated_witness`, the T4/T9
  witnesses, `bridgeCalibrated_not_calibrated` (N+ on `parity4`, repair round 1; the trivial-`C`
  corner is the N− `bridgeCalibrated_not_calibrated_trivialCI`), both T13 strictness witnesses
  and `post13_not_jeffreyOnA`, `condOn_not_dz_witness`, `sameOntology_unbounded_witness`,
  `pairJeffrey_not_evidenceCI_witness` (N+, repair round 1) and the N−
  `jeffrey_not_evidenceCI_witness`).
* `KL`: T18 finite Gibbs (`klFin_nonneg`, `klFin_eq_zero_iff`), the chain rule
  `klFin_condOn_chain`, `geometricUpdate_ge` / `geometricUpdate_eq_iff` (the I-projection onto
  `{Q(S) = 1}` is conditioning); the measure-level `geometricUpdate_klDiv_open` is OPEN.
-/
