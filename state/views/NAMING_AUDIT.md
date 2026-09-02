# Naming audit sheet

Generated from the Lean library and the live documents by `python3 -m checkers.workspace_state --write-handoff`.

**Input to the maintainer's batched naming audit, and nothing else.**
Every name here ships marked provisional under `AGENTS.md` §6. This sheet
says what each one is, which round introduced it, and how far it has
spread. It carries no recommendation, and no round rules on any of it.

*Propagates* is where a name is spelled outside the file defining it.
`registry` means it is a statement of record, so renaming it is a registry
diff; `wiki` means it has reached the human register; `note` a living note;
`prose` `PRIORITIES.md` or `DECISIONS.md`. `Lean only` is the cheapest to
change, and the count of those is the size of the free choice remaining.

## deference — 207 names, 123 of them Lean only

| name | kind | round | propagates | declaration |
|---|---|---|---|---|
| `advantage_estimate` | theorem | 2026-08-11-phase-ii-promotion | registry | `Workspace.Deference.Contrib.CertificateBounds.advantage_estimate` |
| `advisor_has_a_universal_veto` | theorem | 2026-08-12-reachable-corrective-control | registry | `Workspace.Deference.Contrib.ReachableCorrectiveControl.advisor_has_a_universal_veto` |
| `canCorrectFuture_iff` | theorem | 2026-08-12-reachable-corrective-control | registry | `Workspace.Deference.Contrib.ReachableCorrectiveControl.canCorrectFuture_iff` |
| `canCorrectFuture_measures_advisor_cooperation` | theorem | 2026-08-12-reachable-corrective-control | registry | `Workspace.Deference.Contrib.ReachableCorrectiveControl.canCorrectFuture_measures_advisor_cooperation` |
| `canCorrect_iff` | theorem | 2026-08-12-reachable-corrective-control | registry | `Workspace.Deference.Contrib.ReachableCorrectiveControl.canCorrect_iff` |
| `defect_bound` | theorem | 2026-08-11-phase-ii-promotion | registry | `Workspace.Deference.Contrib.CertificateBounds.defect_bound` |
| `delegation_bridge` | theorem | 2026-08-11-phase-ii-promotion | registry, prose | `Workspace.Deference.Contrib.DelegationBridge.delegation_bridge` |
| `delegation_bridge_unconditional` | theorem | 2026-08-11-phase-ii-promotion | registry | `Workspace.Deference.Contrib.DelegationBridge.delegation_bridge_unconditional` |
| `exposure_harvest_attained` | theorem | 2026-08-11-phase-ii-promotion | registry | `Workspace.Deference.Contrib.ExposureGeometry.exposure_harvest_attained` |
| `exposure_harvest_bound` | theorem | 2026-08-11-phase-ii-promotion | registry | `Workspace.Deference.Contrib.ExposureGeometry.exposure_harvest_bound` |
| `extensional_admits_both` | theorem | 2026-08-11-phase-ii-promotion | registry | `Workspace.Deference.Contrib.SubstitutionSeparation.extensional_admits_both` |
| `forecloses_iff` | theorem | 2026-08-12-reachable-corrective-control | registry | `Workspace.Deference.Contrib.ReachableCorrectiveControl.forecloses_iff` |
| `gradeRegister_strict` | theorem | 2026-08-11-phase-ii-promotion | registry, note | `Workspace.Deference.Contrib.CertificateBounds.gradeRegister_strict` |
| `gradeTrust_of_refinement` | theorem | 2026-08-11-phase-ii-promotion | registry | `Workspace.Deference.Contrib.DelegationBridge.gradeTrust_of_refinement` |
| `greedy_duality` | theorem | 2026-08-11-phase-ii-promotion | registry | `Workspace.Deference.Contrib.ExposureGeometry.greedy_duality` |
| `magnitude_not_traderPayoff` | theorem | 2026-08-11-phase-ii-prediction | registry | `Workspace.Deference.Contrib.MagnitudePrediction.magnitude_not_traderPayoff` |
| `margin_forces_agreement` | theorem | 2026-08-11-phase-ii-promotion | registry | `Workspace.Deference.Contrib.CertificateBounds.margin_forces_agreement` |
| `netWorth_eq_zero` | theorem | 2026-08-11-phase-ii-prediction | registry | `Workspace.Deference.Contrib.MagnitudePrediction.CoherentMixture.netWorth_eq_zero` |
| `override_bound` | theorem | 2026-08-11-phase-ii-promotion | registry | `Workspace.Deference.Contrib.CertificateBounds.override_bound` |
| `principal_has_no_exclusive_effect` | theorem | 2026-08-12-reachable-corrective-control | registry | `Workspace.Deference.Contrib.ReachableCorrectiveControl.principal_has_no_exclusive_effect` |
| `selection_eq_of_margin` | theorem | 2026-08-11-phase-ii-promotion | registry | `Workspace.Deference.Contrib.CertificateBounds.selection_eq_of_margin` |
| `separation_requires_disagreement` | theorem | 2026-08-11-phase-ii-promotion | registry | `Workspace.Deference.Contrib.SubstitutionSeparation.separation_requires_disagreement` |
| `sharpTrader_netWorth_eq` | theorem | 2026-08-11-phase-ii-prediction | registry | `Workspace.Deference.Contrib.MagnitudePrediction.sharpTrader_netWorth_eq` |
| `signed_bddAbove_of_bddBelow` | theorem | 2026-08-11-phase-ii-prediction | registry | `Workspace.Deference.Contrib.MagnitudePrediction.signed_bddAbove_of_bddBelow` |
| `signed_bddAbove_of_bddBelow_rpn` | theorem | 2026-08-11-stage-v-li-native | registry, note | `Workspace.Deference.Contrib.MagnitudePrediction.signed_bddAbove_of_bddBelow_rpn` |
| `sim_depends_only_on_inducedChoice` | theorem | 2026-08-11-phase-ii-promotion | registry | `Workspace.Deference.Contrib.SubstitutionSeparation.sim_depends_only_on_inducedChoice` |
| `sq_error_split` | theorem | 2026-08-11-phase-ii-prediction | registry | `Workspace.Deference.Contrib.MagnitudePrediction.sq_error_split` |
| `staticView_eq` | theorem | 2026-08-11-stage-v-li-native | registry, note | `Workspace.Deference.Contrib.StaticViewFactorization.staticView_eq` |
| `unitTrader_netWorth_eq` | theorem | 2026-08-11-phase-ii-prediction | registry, note | `Workspace.Deference.Contrib.MagnitudePrediction.unitTrader_netWorth_eq` |
| `unpredictability_separates` | theorem | 2026-08-11-phase-ii-promotion | registry | `Workspace.Deference.Contrib.SubstitutionSeparation.unpredictability_separates` |
| `value_eq_of_price_realization_eq` | theorem | 2026-08-11-stage-v-li-native | registry, note | `Workspace.Deference.Contrib.StaticViewFactorization.value_eq_of_price_realization_eq` |
| `namespaceIsLive` | def | unrecorded | Lean only | `Workspace.Deference.namespaceIsLive` |
| `AddSubagent` | def | 2026-08-12-cartesian-frames | Lean only | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.AddSubagent` |
| `AgentInert` | def | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.AgentInert` |
| `BiextEquiv` | def | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.BiextEquiv` |
| `Frame` | structure | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame` |
| `Hom` | structure | 2026-08-12-cartesian-frames | Lean only | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.Hom` |
| `Hom.comp` | def | 2026-08-12-cartesian-frames | Lean only | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.Hom.comp` |
| `Hom.id` | def | 2026-08-12-cartesian-frames | Lean only | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.Hom.id` |
| `Homotopic` | def | 2026-08-12-cartesian-frames | Lean only | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.Homotopic` |
| `HomotopyEquiv` | def | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.HomotopyEquiv` |
| `Iso` | structure | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.Iso` |
| `LabelledWorld` | structure | 2026-08-12-cartesian-frames | Lean only | `Workspace.Deference.Contrib.CartesianFrameBridge.LabelledWorld` |
| `MultSubagent` | def | 2026-08-12-cartesian-frames | Lean only | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.MultSubagent` |
| `PresentAction` | inductive | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.PresentAction` |
| `World` | structure | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.World` |
| `agentSetoid` | def | 2026-08-12-cartesian-frames | Lean only | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.agentSetoid` |
| `collapse` | def | 2026-08-12-cartesian-frames | Lean only | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.collapse` |
| `commit` | def | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.commit` |
| `constSection` | def | 2026-08-12-cartesian-frames | Lean only | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.constSection` |
| `delegated` | abbrev | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.delegated` |
| `envSetoid` | def | 2026-08-12-cartesian-frames | Lean only | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.envSetoid` |
| `externalQuot` | def | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.externalQuot` |
| `foreclose` | abbrev | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.foreclose` |
| `futureFrame` | def | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.futureFrame` |
| `image` | def | 2026-08-12-cartesian-frames | note, prose | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.image` |
| `labelledAgent` | abbrev | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.labelledAgent` |
| `labelledHuman` | abbrev | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.labelledHuman` |
| `mapWorlds` | def | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.mapWorlds` |
| `partitionSections` | def | 2026-08-12-cartesian-frames | Lean only | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.partitionSections` |
| `pin` | def | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.pin` |
| `presentStage` | abbrev | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.presentStage` |
| `preserve` | abbrev | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.preserve` |
| `simRead` | abbrev | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.simRead` |
| `simulated` | abbrev | 2026-08-12-cartesian-frames | note | `Workspace.Deference.Contrib.CartesianFrameBridge.simulated` |
| `totalSetoid` | def | 2026-08-12-cartesian-frames | Lean only | `Workspace.Deference.Contrib.CartesianFrameBridge.Frame.totalSetoid` |
| `transfer` | abbrev | 2026-08-12-cartesian-frames | note, prose | `Workspace.Deference.Contrib.CartesianFrameBridge.transfer` |
| `Act` | abbrev | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.CertificateBounds.WorkedCase.Act` |
| `J` | def | 2026-08-11-phase-ii-promotion | note | `Workspace.Deference.Contrib.CertificateBounds.WorkedCase.J` |
| `Jhat` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.CertificateBounds.WorkedCase.Jhat` |
| `S` | def | 2026-08-11-phase-ii-promotion | wiki, note, prose | `Workspace.Deference.Contrib.CertificateBounds.WorkedCase.S` |
| `advantage` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.CertificateBounds.advantage` |
| `defect` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.CertificateBounds.defect` |
| `eta` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.CertificateBounds.WorkedCase.eta` |
| `gatedAct` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.CertificateBounds.gatedAct` |
| `gradeValuation` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.CertificateBounds.gradeValuation` |
| `p` | def | 2026-08-11-phase-ii-promotion | wiki, note, prose | `Workspace.Deference.Contrib.CertificateBounds.WorkedCase.p` |
| `v` | def | 2026-08-11-phase-ii-promotion | note, prose | `Workspace.Deference.Contrib.CertificateBounds.WorkedCase.v` |
| `vhat` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.CertificateBounds.WorkedCase.vhat` |
| `EX` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.DelegationBridge.E1.EX` |
| `GradeTrust` | def | 2026-08-11-phase-ii-promotion | prose | `Workspace.Deference.Contrib.DelegationBridge.GradeTrust` |
| `J` | def | 2026-08-11-phase-ii-promotion | note | `Workspace.Deference.Contrib.DelegationBridge.E1.J` |
| `W` | def | 2026-08-11-phase-ii-promotion | note, prose | `Workspace.Deference.Contrib.DelegationBridge.E1.W` |
| `c` | def | 2026-08-11-phase-ii-promotion | wiki, note, prose | `Workspace.Deference.Contrib.DelegationBridge.E1.c` |
| `disagreementMass` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.DelegationBridge.disagreementMass` |
| `gradeMargin` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.DelegationBridge.gradeMargin` |
| `p` | def | 2026-08-11-phase-ii-promotion | wiki, note, prose | `Workspace.Deference.Contrib.DelegationBridge.E1.p` |
| `valuation` | def | 2026-08-11-phase-ii-promotion | note | `Workspace.Deference.Contrib.DelegationBridge.valuation` |
| `Act` | abbrev | 2026-08-11-stage-iii-fud | Lean only | `Workspace.Deference.Contrib.EnvelopeDominance.WorkedCase.Act` |
| `Cell` | abbrev | 2026-08-11-stage-iii-fud | Lean only | `Workspace.Deference.Contrib.EnvelopeDominance.WorkedCase.Cell` |
| `IsCellMaximiser` | def | 2026-08-11-stage-iii-fud | Lean only | `Workspace.Deference.Contrib.EnvelopeDominance.IsCellMaximiser` |
| `St` | abbrev | 2026-08-11-stage-iii-fud | Lean only | `Workspace.Deference.Contrib.EnvelopeDominance.WorkedCase.St` |
| `X` | def | 2026-08-11-stage-iii-fud | note, prose | `Workspace.Deference.Contrib.EnvelopeDominance.WorkedCase.X` |
| `cell` | def | 2026-08-11-stage-iii-fud | note | `Workspace.Deference.Contrib.EnvelopeDominance.WorkedCase.cell` |
| `cellMass` | def | 2026-08-11-stage-iii-fud | Lean only | `Workspace.Deference.Contrib.EnvelopeDominance.cellMass` |
| `cellValue` | def | 2026-08-11-stage-iii-fud | Lean only | `Workspace.Deference.Contrib.EnvelopeDominance.cellValue` |
| `delta` | def | 2026-08-11-stage-iii-fud | prose | `Workspace.Deference.Contrib.EnvelopeDominance.WorkedCase.delta` |
| `envelopeGap` | def | 2026-08-11-stage-iii-fud | Lean only | `Workspace.Deference.Contrib.EnvelopeDominance.envelopeGap` |
| `p` | def | 2026-08-11-stage-iii-fud | wiki, note, prose | `Workspace.Deference.Contrib.EnvelopeDominance.WorkedCase.p` |
| `phi` | def | 2026-08-11-stage-iii-fud | prose | `Workspace.Deference.Contrib.EnvelopeDominance.WorkedCase.phi` |
| `v` | def | 2026-08-11-stage-iii-fud | note, prose | `Workspace.Deference.Contrib.EnvelopeDominance.WorkedCase.v` |
| `valuation` | def | 2026-08-11-stage-iii-fud | note | `Workspace.Deference.Contrib.EnvelopeDominance.valuation` |
| `F` | def | 2026-08-11-phase-ii-promotion | note, prose | `Workspace.Deference.Contrib.ExposureGeometry.Greedy.F` |
| `InWindow` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.ExposureGeometry.InWindow` |
| `Pierces` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.ExposureGeometry.Pierces` |
| `WindowsDisjoint` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.ExposureGeometry.WindowsDisjoint` |
| `a` | def | 2026-08-11-phase-ii-promotion | wiki, note, prose | `Workspace.Deference.Contrib.ExposureGeometry.Greedy.a` |
| `exposure` | def | 2026-08-11-phase-ii-promotion | wiki | `Workspace.Deference.Contrib.ExposureGeometry.exposure` |
| `orbit` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.ExposureGeometry.Greedy.orbit` |
| `points` | def | 2026-08-11-phase-ii-promotion | prose | `Workspace.Deference.Contrib.ExposureGeometry.Greedy.points` |
| `accelTrader` | def | 2026-08-11-faithful-acceleration | note | `Workspace.Deference.Contrib.FaithfulAcceleration.accelTrader` |
| `banked` | def | 2026-08-11-faithful-acceleration | Lean only | `Workspace.Deference.Contrib.FaithfulAcceleration.banked` |
| `bias` | def | 2026-08-11-faithful-acceleration | Lean only | `Workspace.Deference.Contrib.FaithfulAcceleration.bias` |
| `dsWeight` | def | 2026-08-11-faithful-acceleration | Lean only | `Workspace.Deference.Contrib.FaithfulAcceleration.dsWeight` |
| `gateA` | def | 2026-08-11-faithful-acceleration | Lean only | `Workspace.Deference.Contrib.FaithfulAcceleration.gateA` |
| `gateH` | def | 2026-08-11-faithful-acceleration | Lean only | `Workspace.Deference.Contrib.FaithfulAcceleration.gateH` |
| `holdEF` | def | 2026-08-11-faithful-acceleration | Lean only | `Workspace.Deference.Contrib.FaithfulAcceleration.holdEF` |
| `softInd` | def | 2026-08-11-faithful-acceleration | Lean only | `Workspace.Deference.Contrib.FaithfulAcceleration.softInd` |
| `tradeEF` | def | 2026-08-11-faithful-acceleration | Lean only | `Workspace.Deference.Contrib.FaithfulAcceleration.tradeEF` |
| `weight` | def | 2026-08-11-faithful-acceleration | Lean only | `Workspace.Deference.Contrib.FaithfulAcceleration.weight` |
| `weightEF` | def | 2026-08-11-faithful-acceleration | Lean only | `Workspace.Deference.Contrib.FaithfulAcceleration.weightEF` |
| `Pr` | def | 2026-08-11-faithful-acceleration | Lean only | `Workspace.Deference.Contrib.InheritedAlgebra.AntiExpert.Pr` |
| `X` | def | 2026-08-11-faithful-acceleration | note, prose | `Workspace.Deference.Contrib.InheritedAlgebra.AntiExpert.X` |
| `CoherentMixture` | structure | 2026-08-11-phase-ii-prediction | Lean only | `Workspace.Deference.Contrib.MagnitudePrediction.CoherentMixture` |
| `coinMixture` | def | 2026-08-11-phase-ii-prediction | Lean only | `Workspace.Deference.Contrib.MagnitudePrediction.coinMixture` |
| `coinPrices` | def | 2026-08-11-phase-ii-prediction | Lean only | `Workspace.Deference.Contrib.MagnitudePrediction.coinPrices` |
| `coinWorld` | def | 2026-08-11-phase-ii-prediction | Lean only | `Workspace.Deference.Contrib.MagnitudePrediction.coinWorld` |
| `magnitudeSum` | def | 2026-08-11-phase-ii-prediction | Lean only | `Workspace.Deference.Contrib.MagnitudePrediction.magnitudeSum` |
| `sharpEF` | def | 2026-08-11-phase-ii-prediction | Lean only | `Workspace.Deference.Contrib.MagnitudePrediction.sharpEF` |
| `sharpTrader` | def | 2026-08-11-phase-ii-prediction | Lean only | `Workspace.Deference.Contrib.MagnitudePrediction.sharpTrader` |
| `sharpnessDeficit` | def | 2026-08-11-phase-ii-prediction | Lean only | `Workspace.Deference.Contrib.MagnitudePrediction.sharpnessDeficit` |
| `signedSum` | def | 2026-08-11-phase-ii-prediction | Lean only | `Workspace.Deference.Contrib.MagnitudePrediction.signedSum` |
| `squaredSum` | def | 2026-08-11-phase-ii-prediction | Lean only | `Workspace.Deference.Contrib.MagnitudePrediction.squaredSum` |
| `unitTrader` | def | 2026-08-11-phase-ii-prediction | note | `Workspace.Deference.Contrib.MagnitudePrediction.unitTrader` |
| `AAct` | inductive | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.AAct` |
| `CanCorrect` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.CanCorrect` |
| `CanCorrectFuture` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.CanCorrectFuture` |
| `Channel` | inductive | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.Channel` |
| `EAct` | inductive | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.EAct` |
| `Forecloses` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.Forecloses` |
| `HAct` | inductive | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.HAct` |
| `Level` | inductive | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.Level` |
| `Level.up` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.Level.up` |
| `Preserves` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.Preserves` |
| `Reach` | inductive | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.Reach` |
| `Responsive` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.Responsive` |
| `SameImmediate` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.SameImmediate` |
| `St` | structure | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.St` |
| `StA` | structure | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.AuthLabel.StA` |
| `Tag` | inductive | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.Tag` |
| `V` | structure | 2026-08-12-reachable-corrective-control | note, prose | `Workspace.Deference.Contrib.ReachableCorrectiveControl.EnvBlame.V` |
| `VCanCorrect` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.EnvBlame.VCanCorrect` |
| `VCanCorrectFuture` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.EnvBlame.VCanCorrectFuture` |
| `VE` | inductive | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.EnvBlame.VE` |
| `VForecloses` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.EnvBlame.VForecloses` |
| `VReach` | inductive | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.EnvBlame.VReach` |
| `VResponsive` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.EnvBlame.VResponsive` |
| `aA` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.AuthLabel.aA` |
| `aE` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.AuthLabel.aE` |
| `aH` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.AuthLabel.aH` |
| `aObs` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.AuthLabel.aObs` |
| `aStep` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.AuthLabel.aStep` |
| `applyA` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.applyA` |
| `applyE` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.applyE` |
| `applyH` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.applyH` |
| `dec` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.AuthLabel.dec` |
| `enc` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.AuthLabel.enc` |
| `hToA` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.hToA` |
| `live` | def | 2026-08-12-reachable-corrective-control | note, prose | `Workspace.Deference.Contrib.ReachableCorrectiveControl.live` |
| `obs` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.obs` |
| `resetRun` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.resetRun` |
| `s0` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.s0` |
| `s1a` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.s1a` |
| `s1b` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.s1b` |
| `s2a` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.s2a` |
| `s2b` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.s2b` |
| `s3a` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.s3a` |
| `s3b` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.s3b` |
| `setTag` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.setTag` |
| `step` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.step` |
| `stepHFirst` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.stepHFirst` |
| `stillRun` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.stillRun` |
| `trace` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.trace` |
| `unexercised` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.unexercised` |
| `vA` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.EnvBlame.vA` |
| `vE` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.EnvBlame.vE` |
| `vH` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.EnvBlame.vH` |
| `vstep` | def | 2026-08-12-reachable-corrective-control | Lean only | `Workspace.Deference.Contrib.ReachableCorrectiveControl.EnvBlame.vstep` |
| `Architecture` | structure | 2026-08-11-stage-v-li-native | Lean only | `Workspace.Deference.Contrib.StaticViewFactorization.WorkedCase.Architecture` |
| `FactorsThroughStaticView` | def | 2026-08-11-stage-v-li-native | note | `Workspace.Deference.Contrib.StaticViewFactorization.FactorsThroughStaticView` |
| `agentAuthorized` | def | 2026-08-11-stage-v-li-native | Lean only | `Workspace.Deference.Contrib.StaticViewFactorization.WorkedCase.agentAuthorized` |
| `humanAuthorized` | def | 2026-08-11-stage-v-li-native | Lean only | `Workspace.Deference.Contrib.StaticViewFactorization.WorkedCase.humanAuthorized` |
| `jurisdictionValue` | def | 2026-08-11-stage-v-li-native | Lean only | `Workspace.Deference.Contrib.StaticViewFactorization.WorkedCase.jurisdictionValue` |
| `staticValue` | def | 2026-08-11-stage-v-li-native | Lean only | `Workspace.Deference.Contrib.StaticViewFactorization.WorkedCase.staticValue` |
| `ConstantOnCells` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.SubstitutionSeparation.ConstantOnCells` |
| `IsMaximizerSelector` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.SubstitutionSeparation.IsMaximizerSelector` |
| `choice` | def | 2026-08-11-phase-ii-promotion | prose | `Workspace.Deference.Contrib.SubstitutionSeparation.M.choice` |
| `inducedSelection` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.SubstitutionSeparation.inducedSelection` |
| `kt` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.SubstitutionSeparation.M.kt` |
| `p` | def | 2026-08-11-phase-ii-promotion | wiki, note, prose | `Workspace.Deference.Contrib.SubstitutionSeparation.M.p` |
| `realizedQuantity` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.SubstitutionSeparation.realizedQuantity` |
| `schemeDelegate` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.SubstitutionSeparation.schemeDelegate` |
| `schemeSim` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.SubstitutionSeparation.schemeSim` |
| `v` | def | 2026-08-11-phase-ii-promotion | note, prose | `Workspace.Deference.Contrib.SubstitutionSeparation.M.v` |
| `valuation` | def | 2026-08-11-phase-ii-promotion | note | `Workspace.Deference.Contrib.SubstitutionSeparation.M.valuation` |
| `vh` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.SubstitutionSeparation.M.vh` |
| `vhAccurate` | def | 2026-08-11-phase-ii-promotion | Lean only | `Workspace.Deference.Contrib.SubstitutionSeparation.M.vhAccurate` |

## normativity — 409 names, 347 of them Lean only

| name | kind | round | propagates | declaration |
|---|---|---|---|---|
| `BudgeterAt_value_eq_of_safe` | theorem | 2026-08-16-traderized-enforcement | registry, note | `Workspace.Normativity.Contrib.AssessmentProcess.BudgeterAt_value_eq_of_safe` |
| `admissiblePatterns_complete` | theorem | 2026-08-19-deductive-region | registry | `Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_complete` |
| `admissiblePatterns_ne_nil_iff` | theorem | 2026-08-19-deductive-region | registry | `Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_ne_nil_iff` |
| `admissiblePatterns_sound` | theorem | 2026-08-19-deductive-region | registry | `Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_sound` |
| `budgetedTrader_netWorth_floor` | theorem | 2026-08-16-traderized-enforcement | registry, note | `Workspace.Normativity.Contrib.AssessmentProcess.budgetedTrader_netWorth_floor` |
| `chain_compiles` | theorem | 2026-08-10-repo-scaffolding | registry | `Workspace.Smoke.chain_compiles` |
| `deductiveRegion_eq_convexHull` | theorem | 2026-08-19-deductive-region | registry | `Workspace.Normativity.Contrib.DeductiveRegion.deductiveRegion_eq_convexHull` |
| `deductive_end_to_end` | theorem | 2026-08-18-projection-enforcement | registry, note | `Workspace.Normativity.Contrib.DeductiveEffective.deductive_end_to_end` |
| `end_to_end_effective` | theorem | 2026-08-18-projection-enforcement | registry, note, prose | `Workspace.Normativity.Contrib.EnforcedCompiler.ProjectionSchedule.end_to_end_effective` |
| `end_to_end_of_constraints_effective` | theorem | 2026-08-18-projection-enforcement | registry, note | `Workspace.Normativity.Contrib.EffectiveRepresentation.end_to_end_of_constraints_effective` |
| `enforcement_day_value_nonneg` | theorem | 2026-08-16-traderized-enforcement | registry, note | `Workspace.Normativity.Contrib.DeductiveEnforcement.enforcement_day_value_nonneg` |
| `enforcement_netWorth_nonneg` | theorem | 2026-08-16-traderized-enforcement | registry, note | `Workspace.Normativity.Contrib.DeductiveEnforcement.enforcement_netWorth_nonneg` |
| `exists_budgetedTrader_exploits` | theorem | 2026-08-16-traderized-enforcement | registry, note | `Workspace.Normativity.Contrib.AssessmentProcess.exists_budgetedTrader_exploits` |
| `exists_maxMin_representation` | theorem | 2026-08-18-maxmin-representation | registry | `Workspace.Normativity.Contrib.MaxMinRepresentation.exists_maxMin_representation` |
| `faf_asympEq_refl` | theorem | 2026-08-10-repo-scaffolding | registry | `Workspace.Smoke.faf_asympEq_refl` |
| `gap_le_of_mixture` | theorem | 2026-08-16-traderized-enforcement | registry, note | `Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_mixture` |
| `gap_le_of_net_cover` | theorem | 2026-08-16-traderized-enforcement | registry, note | `Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_net_cover` |
| `isLogicalInductor_of_computableMarket` | theorem | 2026-08-16-traderized-enforcement | registry, note | `Workspace.Normativity.Contrib.DeductiveEnforcement.isLogicalInductor_of_computableMarket` |
| `isPiecewiseAffineOn_maxMin` | theorem | 2026-08-18-maxmin-representation | registry | `Workspace.Normativity.Contrib.MaxMinRepresentation.isPiecewiseAffineOn_maxMin` |
| `marketValueRat_enforcementStrategy` | theorem | 2026-08-16-traderized-enforcement | registry, note | `Workspace.Normativity.Contrib.EnforcementStrategy.marketValueRat_enforcementStrategy` |
| `no_efficient_trader_exploits` | theorem | 2026-08-16-traderized-enforcement | registry, note | `Workspace.Normativity.Contrib.AssessmentFirm.no_efficient_trader_exploits` |
| `no_efficient_trader_exploits` | theorem | 2026-08-16-traderized-enforcement | registry, note | `Workspace.Normativity.Contrib.EnforcementPreservation.no_efficient_trader_exploits` |
| `no_efficient_trader_exploits_of_worldInclusive` | theorem | 2026-08-16-traderized-enforcement | registry, note | `Workspace.Normativity.Contrib.DeductiveEnforcement.no_efficient_trader_exploits_of_worldInclusive` |
| `rowViolation_le_of_intensity_ge` | theorem | 2026-08-16-traderized-enforcement | registry, note | `Workspace.Normativity.Contrib.EnforcementStrategy.rowViolation_le_of_intensity_ge` |
| `trading_firm_dominance` | theorem | 2026-08-16-traderized-enforcement | registry, note | `Workspace.Normativity.Contrib.AssessmentFirm.trading_firm_dominance` |
| `witness_market_not_exploited` | theorem | 2026-08-16-traderized-enforcement | registry, note | `Workspace.Normativity.Contrib.DeductiveEnforcement.witness_market_not_exploited` |
| `namespaceIsLive` | def | unrecorded | Lean only | `Workspace.Normativity.namespaceIsLive` |
| `TradingFirm` | def | 2026-08-16-traderized-enforcement | note | `Workspace.Normativity.Contrib.AssessmentFirm.TradingFirm` |
| `TradingFirmAt` | def | 2026-08-16-traderized-enforcement | note | `Workspace.Normativity.Contrib.AssessmentFirm.TradingFirmAt` |
| `budgetComponents` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentFirm.budgetComponents` |
| `componentAt` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentFirm.componentAt` |
| `componentTrader` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentFirm.componentTrader` |
| `firmTrader` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentFirm.firmTrader` |
| `history` | def | 2026-08-16-traderized-enforcement | wiki, prose | `Workspace.Normativity.Contrib.AssessmentFirm.history` |
| `quote` | def | 2026-08-16-traderized-enforcement | note | `Workspace.Normativity.Contrib.AssessmentFirm.quote` |
| `states` | def | 2026-08-16-traderized-enforcement | wiki, note | `Workspace.Normativity.Contrib.AssessmentFirm.states` |
| `tradingFirmTrader` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentFirm.tradingFirmTrader` |
| `Assessment` | structure | 2026-08-16-traderized-enforcement | note | `Workspace.Normativity.Contrib.AssessmentProcess.Assessment` |
| `BudgeterAt` | def | 2026-08-16-traderized-enforcement | note | `Workspace.Normativity.Contrib.AssessmentProcess.BudgeterAt` |
| `Exploits` | def | 2026-08-16-traderized-enforcement | note | `Workspace.Normativity.Contrib.AssessmentProcess.Assessment.Exploits` |
| `FiniteDetermined` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.FiniteDetermined` |
| `IsLogicalInductor` | def | 2026-08-16-traderized-enforcement | note, prose | `Workspace.Normativity.Contrib.AssessmentProcess.Assessment.IsLogicalInductor` |
| `PayoutAgrees` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.PayoutAgrees` |
| `allTrue` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.allTrue` |
| `allTrueLive` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.allTrueLive` |
| `budgetScaleFeature` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.budgetScaleFeature` |
| `budgetWorldScaleOf` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.budgetWorldScaleOf` |
| `budgetedTrader` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.budgetedTrader` |
| `deductiveContext` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.deductiveContext` |
| `deductiveRestrict` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.deductiveRestrict` |
| `emptyProcess` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.emptyProcess` |
| `freshAtom` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.freshAtom` |
| `lateAllTrueLive` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.lateAllTrueLive` |
| `ofDeductiveProcess` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.ofDeductiveProcess` |
| `plausibleAssessments` | def | 2026-08-16-traderized-enforcement | note | `Workspace.Normativity.Contrib.AssessmentProcess.Assessment.plausibleAssessments` |
| `priorBudgetBreach` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.priorBudgetBreach` |
| `ratPayout` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.ratPayout` |
| `rawPriorWorthOf` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.rawPriorWorthOf` |
| `rawWorthOf` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.rawWorthOf` |
| `supportUpTo` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.supportUpTo` |
| `worldValueFeatureOf` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.AssessmentProcess.worldValueFeatureOf` |
| `DistanceComplete` | def | 2026-08-16-traderized-enforcement | note, prose | `Workspace.Normativity.Contrib.CoherenceModulus.DistanceComplete` |
| `IsCredence` | structure | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.CoherenceModulus.IsCredence` |
| `gap` | def | 2026-08-16-traderized-enforcement | wiki, note | `Workspace.Normativity.Contrib.CoherenceModulus.gap` |
| `l1` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.CoherenceModulus.l1` |
| `mixture` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.CoherenceModulus.mixture` |
| `Computation` | structure | unrecorded | prose | `Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.Computation` |
| `RationalConstraintSchedule` | structure | unrecorded | prose | `Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule` |
| `RationalConstraintSchedule.canonicalRepresentation` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.canonicalRepresentation` |
| `RegionRepresentation` | structure | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.RegionRepresentation` |
| `RegionRepresentation.Effective` | structure | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.RegionRepresentation.Effective` |
| `atom0` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.atom0` |
| `clampRep` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.clampRep` |
| `emptyComputation` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.emptyComputation` |
| `emptyEffective` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.emptyEffective` |
| `emptySchedule` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.emptySchedule` |
| `fragment` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.fragment` |
| `intervalComputation` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.intervalComputation` |
| `intervalEffective` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.intervalEffective` |
| `intervalRepresentation` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.intervalRepresentation` |
| `intervalSchedule` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.intervalSchedule` |
| `market` | def | unrecorded | note | `Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.market` |
| `pointPolytope` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.pointPolytope` |
| `regionPred` | def | unrecorded | prose | `Workspace.Normativity.Contrib.ConstraintSchedule.regionPred` |
| `regionPred` | def | unrecorded | prose | `Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.regionPred` |
| `schedule` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.schedule` |
| `scheduleComputation` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.scheduleComputation` |
| `target` | def | unrecorded | note | `Workspace.Normativity.Contrib.ConstraintSchedule.target` |
| `target` | def | unrecorded | note | `Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.target` |
| `targetAt` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.targetAt` |
| `vertexData` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ConstraintSchedule.RationalConstraintSchedule.vertexData` |
| `deductivePolytopeEff` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveEffective.deductivePolytopeEff` |
| `deductiveProjectionSchedule` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveEffective.deductiveProjectionSchedule` |
| `deductiveReps` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveEffective.deductiveReps` |
| `deductiveScheduleComputation` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveEffective.deductiveScheduleComputation` |
| `aggregateAt` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.DeductiveEnforcement.aggregateAt` |
| `history` | def | 2026-08-16-traderized-enforcement | wiki, prose | `Workspace.Normativity.Contrib.DeductiveEnforcement.history` |
| `quote` | def | 2026-08-16-traderized-enforcement | note | `Workspace.Normativity.Contrib.DeductiveEnforcement.quote` |
| `realizedAggregate` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.DeductiveEnforcement.realizedAggregate` |
| `realizedEnforcer` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.DeductiveEnforcement.realizedEnforcer` |
| `realizedFirm` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.DeductiveEnforcement.realizedFirm` |
| `states` | def | 2026-08-16-traderized-enforcement | wiki, note | `Workspace.Normativity.Contrib.DeductiveEnforcement.states` |
| `witnessEnforcer` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.DeductiveEnforcement.witnessEnforcer` |
| `witnessPres` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.DeductiveEnforcement.witnessPres` |
| `witnessProcess` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.DeductiveEnforcement.witnessProcess` |
| `witnessRow` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.DeductiveEnforcement.witnessRow` |
| `witnessSentence` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.DeductiveEnforcement.witnessSentence` |
| `admissiblePatterns` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns` |
| `admissiblePatternsEff` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatternsEff` |
| `atomP` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.atomP` |
| `atomQ` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.atomQ` |
| `contextAtoms` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.contextAtoms` |
| `contextList` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.contextList` |
| `deductiveRegion` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.deductiveRegion` |
| `deductiveVertices` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.deductiveVertices` |
| `extend` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.extend` |
| `fragmentAtoms` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.fragmentAtoms` |
| `patternsFrom` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.patternsFrom` |
| `regionContext` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.regionContext` |
| `restrictTo` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.restrictTo` |
| `tableOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.tableOf` |
| `vertex` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.vertex` |
| `witnessWorld` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveRegion.witnessWorld` |
| `deductiveMarket` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveSchedule.deductiveMarket` |
| `deductivePolytope` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveSchedule.deductivePolytope` |
| `deductiveSchedule` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveSchedule.deductiveSchedule` |
| `deductiveTarget` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveSchedule.deductiveTarget` |
| `emptyProcess` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveSchedule.emptyProcess` |
| `ratVertex` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.DeductiveSchedule.ratVertex` |
| `adjOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.adjOf` |
| `candidatePairsOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.candidatePairsOf` |
| `coefEntry` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.coefEntry` |
| `coeffListOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.coeffListOf` |
| `compOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.compOf` |
| `compileLen` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.compileLen` |
| `compileOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.compileOf` |
| `conNonnegOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.conNonnegOf` |
| `conSumGeOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.conSumGeOf` |
| `conSumLeOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.conSumLeOf` |
| `conSupportOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.conSupportOf` |
| `conUpperOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.conUpperOf` |
| `conVertGeOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.conVertGeOf` |
| `conVertLeOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.conVertLeOf` |
| `cutAt` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.cutAt` |
| `detAux` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.detAux` |
| `detCombine` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.detCombine` |
| `detOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.detOf` |
| `dirOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.dirOf` |
| `effectiveRepresentation` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.effectiveRepresentation` |
| `effectiveRepresentation_effective` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.effectiveRepresentation_effective` |
| `faceBase` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.faceBase` |
| `faceListOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.faceListOf` |
| `faceRest` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.faceRest` |
| `gramEntry` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.gramEntry` |
| `gramInvEntry` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.gramInvEntry` |
| `gramMat` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.gramMat` |
| `gramOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.gramOf` |
| `groupOfListL` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.groupOfListL` |
| `idxListOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.idxListOf` |
| `matList` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.matList` |
| `mkConOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.mkConOf` |
| `pieceOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.pieceOf` |
| `projectorFamilyOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.projectorFamilyOf` |
| `projectorRepOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.projectorRepOf` |
| `repOfListL` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.repOfListL` |
| `setRow` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.setRow` |
| `subMats` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.subMats` |
| `systemOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.systemOf` |
| `unitRow` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.unitRow` |
| `vtxOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.vtxOf` |
| `zeroBlock` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EffectiveRepresentation.zeroBlock` |
| `EffectiveEnforcerComputation` | structure | unrecorded | prose | `Workspace.Normativity.Contrib.EnforcedCompiler.EffectiveEnforcerComputation` |
| `compiler` | def | unrecorded | wiki, prose | `Workspace.Normativity.Contrib.EnforcedCompiler.compiler` |
| `enfPrefixFromTradeListsAtFuel` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EnforcedCompiler.enfPrefixFromTradeListsAtFuel` |
| `EffectiveEnforcer` | structure | unrecorded | Lean only | `Workspace.Normativity.Contrib.EnforcedComputation.EffectiveEnforcer` |
| `EffectiveEnforcer.adaptive` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EnforcedComputation.EffectiveEnforcer.adaptive` |
| `EffectiveEnforcer.strategy` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EnforcedComputation.EffectiveEnforcer.strategy` |
| `EnforcedBoundedEvaluatorCompiler` | structure | unrecorded | Lean only | `Workspace.Normativity.Contrib.EnforcedComputation.EnforcedBoundedEvaluatorCompiler` |
| `enfAggregateFromStages` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EnforcedComputation.enfAggregateFromStages` |
| `enfEncodedQuote` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EnforcedComputation.enfEncodedQuote` |
| `enfEncodedQuoteAtFuel` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EnforcedComputation.enfEncodedQuoteAtFuel` |
| `enfEncodedQuoteNatAtFuel` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EnforcedComputation.enfEncodedQuoteNatAtFuel` |
| `enfPrefixAtFuel` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EnforcedComputation.enfPrefixAtFuel` |
| `enfPrefixFromStagesAtFuel` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EnforcedComputation.enfPrefixFromStagesAtFuel` |
| `enfStatePrefix` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.EnforcedComputation.enfStatePrefix` |
| `aggregateAt` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementPreservation.aggregateAt` |
| `history` | def | 2026-08-16-traderized-enforcement | wiki, prose | `Workspace.Normativity.Contrib.EnforcementPreservation.history` |
| `quote` | def | 2026-08-16-traderized-enforcement | note | `Workspace.Normativity.Contrib.EnforcementPreservation.quote` |
| `realizedAggregate` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementPreservation.realizedAggregate` |
| `realizedEnforcer` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementPreservation.realizedEnforcer` |
| `realizedFirm` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementPreservation.realizedFirm` |
| `states` | def | 2026-08-16-traderized-enforcement | wiki, note | `Workspace.Normativity.Contrib.EnforcementPreservation.states` |
| `Presentation` | structure | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementStrategy.Presentation` |
| `Row` | structure | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementStrategy.Row` |
| `coefficientFeature` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementStrategy.coefficientFeature` |
| `compiledPosition` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementStrategy.Presentation.compiledPosition` |
| `coords` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementStrategy.Presentation.coords` |
| `enforcementStrategy` | def | 2026-08-16-traderized-enforcement | note | `Workspace.Normativity.Contrib.EnforcementStrategy.enforcementStrategy` |
| `intensities` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementStrategy.Presentation.intensities` |
| `normals` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementStrategy.Presentation.normals` |
| `priceCombo` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementStrategy.priceCombo` |
| `rhss` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementStrategy.Presentation.rhss` |
| `rowAt` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementStrategy.Presentation.rowAt` |
| `rowIndex` | abbrev | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementStrategy.Presentation.rowIndex` |
| `rowViolation` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementStrategy.Presentation.rowViolation` |
| `violationFeature` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementStrategy.violationFeature` |
| `witnessPresentation` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.EnforcementStrategy.witnessPresentation` |
| `LinCon` | abbrev | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.LinCon` |
| `Sat` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.LinCon.Sat` |
| `Sat` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.Sat` |
| `baseVerdict` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.baseVerdict` |
| `coeffs` | abbrev | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.LinCon.coeffs` |
| `combine` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.combine` |
| `comboCoeffs` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.comboCoeffs` |
| `const` | abbrev | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.LinCon.const` |
| `elim` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.elim` |
| `elimStep` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.elimStep` |
| `eval` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.LinCon.eval` |
| `feasible` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.feasible` |
| `lastCoeff` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.lastCoeff` |
| `of` | def | unrecorded | wiki, note, prose | `Workspace.Normativity.Contrib.FourierMotzkin.LinCon.of` |
| `strict` | abbrev | unrecorded | note | `Workspace.Normativity.Contrib.FourierMotzkin.LinCon.strict` |
| `wClosed` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.wClosed` |
| `wEqUnsat` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.wEqUnsat` |
| `wFeasible` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.wFeasible` |
| `wInfeasible` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.wInfeasible` |
| `wOpen` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.wOpen` |
| `wTwoSat` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.wTwoSat` |
| `wTwoUnsat` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.FourierMotzkin.wTwoUnsat` |
| `IsSupportPresentation` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.IntrinsicCoherence.IsSupportPresentation` |
| `presentationNet` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.IntrinsicCoherence.presentationNet` |
| `IsPiecewiseAffineOn` | def | 2026-08-18-maxmin-representation | Lean only | `Workspace.Normativity.Contrib.MaxMinRepresentation.IsPiecewiseAffineOn` |
| `absComponent` | def | 2026-08-18-maxmin-representation | Lean only | `Workspace.Normativity.Contrib.MaxMinRepresentation.absComponent` |
| `absPiece` | def | 2026-08-18-maxmin-representation | Lean only | `Workspace.Normativity.Contrib.MaxMinRepresentation.absPiece` |
| `negLine` | def | 2026-08-18-maxmin-representation | Lean only | `Workspace.Normativity.Contrib.MaxMinRepresentation.negLine` |
| `segmentComponent` | def | 2026-08-18-maxmin-representation | Lean only | `Workspace.Normativity.Contrib.MaxMinRepresentation.segmentComponent` |
| `segmentDomain` | def | 2026-08-18-maxmin-representation | Lean only | `Workspace.Normativity.Contrib.MaxMinRepresentation.segmentDomain` |
| `AQ` | inductive | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.AQ` |
| `Adm` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.StandingTrace.Adm` |
| `AnchorStanding` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.AnchorStanding` |
| `Attention` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.Attention` |
| `BQ` | inductive | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.BQ` |
| `Fresh` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.StandingTrace.Fresh` |
| `Grounded` | inductive | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.StandingTrace.Grounded` |
| `IssueTrace` | structure | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace` |
| `IssueTraceCore` | structure | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.IssueTraceCore` |
| `Licensing` | structure | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.Licensing` |
| `Licensing.standsFor` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.Licensing.standsFor` |
| `Live` | def | 2026-08-29-normative-continuity-concordance | prose | `Workspace.Normativity.Contrib.NormativeContinuity.TraceData.Live` |
| `LiveGate` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.LiveGate` |
| `NoPermanentWait` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.NoPermanentWait` |
| `NoRouteWait` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.TraceData.NoRouteWait` |
| `NonStarving` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.NonStarving` |
| `Omega` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.TraceData.Omega` |
| `OtherRequirements` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.OtherRequirements` |
| `Reach` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.TraceData.Reach` |
| `ReachGate` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.ReachGate` |
| `Ready` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.TraceData.Ready` |
| `Routes` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.TraceData.Routes` |
| `StandingTrace` | structure | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.StandingTrace` |
| `TraceData` | structure | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.TraceData` |
| `WaitResponsive` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.WaitResponsive` |
| `Work` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.TraceData.Work` |
| `anc` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.TraceData.anc` |
| `fixA` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixA` |
| `fixB` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixB` |
| `fixE` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixE` |
| `fixE_issueTrace` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.fixE_issueTrace` |
| `mattersOf` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.IssueTraceCore.mattersOf` |
| `onCycle` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.TraceData.onCycle` |
| `only` | structure | 2026-08-29-normative-continuity-concordance | note, prose | `Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.only` |
| `opp` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.TraceData.opp` |
| `shareAttention` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.IssueTrace.shareAttention` |
| `succ` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.TraceData.succ` |
| `toIssueTrace` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.Fixtures.toIssueTrace` |
| `toIssueTrace` | def | 2026-08-29-normative-continuity-concordance | Lean only | `Workspace.Normativity.Contrib.NormativeContinuity.IssueTraceCore.toIssueTrace` |
| `waits` | def | 2026-08-29-normative-continuity-concordance | prose | `Workspace.Normativity.Contrib.NormativeContinuity.TraceData.waits` |
| `SemanticAction` | inductive | 2026-08-11-phi-regret-bridge | Lean only | `Workspace.Normativity.Contrib.PhiRegretBridge.SemanticAction` |
| `actual` | def | 2026-08-11-phi-regret-bridge | note | `Workspace.Normativity.Contrib.PhiRegretBridge.Witness.actual` |
| `cumulativeLoss` | def | 2026-08-11-phi-regret-bridge | Lean only | `Workspace.Normativity.Contrib.PhiRegretBridge.cumulativeLoss` |
| `decode` | def | 2026-08-11-phi-regret-bridge | Lean only | `Workspace.Normativity.Contrib.PhiRegretBridge.Witness.decode` |
| `labelLoss` | def | 2026-08-11-phi-regret-bridge | Lean only | `Workspace.Normativity.Contrib.PhiRegretBridge.Witness.labelLoss` |
| `labelMap` | def | 2026-08-11-phi-regret-bridge | Lean only | `Workspace.Normativity.Contrib.PhiRegretBridge.Witness.labelMap` |
| `repoLoss` | def | 2026-08-11-phi-regret-bridge | Lean only | `Workspace.Normativity.Contrib.PhiRegretBridge.Witness.repoLoss` |
| `repoMap` | def | 2026-08-11-phi-regret-bridge | Lean only | `Workspace.Normativity.Contrib.PhiRegretBridge.Witness.repoMap` |
| `_root_.Workspace.Normativity.Contrib.PolyhedralProjection.AffineForm.toAffineMap` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralCoverage._root_.Workspace.Normativity.Contrib.PolyhedralProjection.AffineForm.toAffineMap` |
| `dirs` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralCoverage.dirs` |
| `faceList` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralCoverage.faceList` |
| `unitSegment` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralCoverage.unitSegment` |
| `AffineForm` | structure | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralProjection.AffineForm` |
| `AffineForm.eval` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralProjection.AffineForm.eval` |
| `Face` | structure | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralProjection.Face` |
| `Regular` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralProjection.Face.Regular` |
| `candidate` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralProjection.Face.candidate` |
| `cell` | def | unrecorded | note | `Workspace.Normativity.Contrib.PolyhedralProjection.cell` |
| `coefQ` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralProjection.Face.coefQ` |
| `coord` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralProjection.Face.coord` |
| `dim` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralProjection.Face.dim` |
| `dir` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralProjection.Face.dir` |
| `dirQ` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralProjection.Face.dirQ` |
| `gramInvQ` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralProjection.Face.gramInvQ` |
| `gramQ` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralProjection.Face.gramQ` |
| `piece` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralProjection.Face.piece` |
| `rhs` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.PolyhedralProjection.Face.rhs` |
| `groupOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionBridge.groupOf` |
| `ofGeom` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionBridge.ofGeom` |
| `repOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionBridge.repOf` |
| `restrict` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionBridge.restrict` |
| `unitFragment` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionBridge.unitFragment` |
| `cumValue` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionBudget.cumValue` |
| `wAtom` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionBudget.wAtom` |
| `wFrag` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionBudget.wFrag` |
| `wHistory` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionBudget.wHistory` |
| `wLam` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionBudget.wLam` |
| `wProj` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionBudget.wProj` |
| `wRegion` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionBudget.wRegion` |
| `wTrader` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionBudget.wTrader` |
| `wWorld` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionBudget.wWorld` |
| `FragmentLocal` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCalibrated.FragmentLocal` |
| `calibratedIntensity` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCalibrated.calibratedIntensity` |
| `extend` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCalibrated.extend` |
| `resistance` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCalibrated.resistance` |
| `AffineForm` | abbrev | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.AffineForm` |
| `AffineForm.coeff` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.AffineForm.coeff` |
| `AffineForm.evalQ` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.AffineForm.evalQ` |
| `AffineForm.evalR` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.AffineForm.evalR` |
| `Fragment` | structure | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.Fragment` |
| `Fragment.toFinset` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.Fragment.toFinset` |
| `Group` | abbrev | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.Group` |
| `Rep` | abbrev | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.Rep` |
| `affineEF` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.affineEF` |
| `coefEF` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.coefEF` |
| `groupEF` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.groupEF` |
| `groupEval` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.groupEval` |
| `groupEvalQ` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.groupEvalQ` |
| `projectionStrategy` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.projectionStrategy` |
| `repEF` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.repEF` |
| `repEval` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.repEval` |
| `repEvalQ` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCompiler.repEvalQ` |
| `HomotheticCore` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCore.HomotheticCore` |
| `coreAtom` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCore.coreAtom` |
| `equalityRegion` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCore.equalityRegion` |
| `halfSpace` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCore.halfSpace` |
| `livePoss` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionCore.livePoss` |
| `effectiveEnforcer` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionEffective.effectiveEnforcer` |
| `ProjectionSchedule` | structure | unrecorded | note, prose | `Workspace.Normativity.Contrib.ProjectionEnforcer.ProjectionSchedule` |
| `ProjectionSchedule.enforcer` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionEnforcer.ProjectionSchedule.enforcer` |
| `ProjectionSchedule.fragment` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionEnforcer.ProjectionSchedule.fragment` |
| `ProjectionSchedule.intensity` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionEnforcer.ProjectionSchedule.intensity` |
| `ProjectionSchedule.market` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionEnforcer.ProjectionSchedule.market` |
| `ProjectionSchedule.rep` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionEnforcer.ProjectionSchedule.rep` |
| `ProjectionScheduleComputation` | structure | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionEnforcer.ProjectionScheduleComputation` |
| `repAt` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionEnforcer.repAt` |
| `IsNearestPoint` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionForce.IsNearestPoint` |
| `dist2` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionForce.dist2` |
| `ip` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionForce.ip` |
| `shares` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionForce.shares` |
| `sqDist` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionForce.sqDist` |
| `Realizes` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionMarket.Realizes` |
| `affineEFof` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionPrimrec.affineEFof` |
| `coefEFof` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionPrimrec.coefEFof` |
| `groupEFof` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionPrimrec.groupEFof` |
| `repEFof` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectionPrimrec.repEFof` |
| `Holds` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.Holds` |
| `cOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.cOf` |
| `candidatePairs` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.candidatePairs` |
| `coeffFn` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.coeffFn` |
| `combSet` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.combSet` |
| `comp` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.comp` |
| `compForm` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.compForm` |
| `conNonneg` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.conNonneg` |
| `conSumGe` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.conSumGe` |
| `conSumLe` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.conSumLe` |
| `conSupport` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.conSupport` |
| `conUpper` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.conUpper` |
| `conVertGe` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.conVertGe` |
| `conVertLe` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.conVertLe` |
| `embC` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.embC` |
| `embL` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.embL` |
| `embX` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.embX` |
| `gram` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.gram` |
| `groupOfList` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.groupOfList` |
| `idxList` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.idxList` |
| `lamOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.lamOf` |
| `lamVal` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.lamVal` |
| `mkCon` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.mkCon` |
| `natsOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.natsOf` |
| `nf` | abbrev | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.nf` |
| `nv` | abbrev | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.nv` |
| `projectorFamily` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.projectorFamily` |
| `projectorRep` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.projectorRep` |
| `projectorRepMap` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.projectorRepMap` |
| `ptOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.ptOf` |
| `qOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.qOf` |
| `repOfList` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.repOfList` |
| `resid` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.resid` |
| `system` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.system` |
| `vtx` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.vtx` |
| `witnessOf` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.ProjectorGenerator.witnessOf` |
| `Pt` | abbrev | unrecorded | Lean only | `Workspace.Normativity.Contrib.RationalPolytope.Pt` |
| `_root_.RationalPolytope` | structure | unrecorded | Lean only | `Workspace.Normativity.Contrib.RationalPolytope._root_.RationalPolytope` |
| `carrier` | def | unrecorded | Lean only | `RationalPolytope.carrier` |
| `proj` | def | unrecorded | Lean only | `RationalPolytope.proj` |
| `toPt` | def | unrecorded | Lean only | `Workspace.Normativity.Contrib.RationalPolytope.toPt` |
| `vertexSet` | def | unrecorded | Lean only | `RationalPolytope.vertexSet` |
| `deficit` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.TraderizedEnforcement.deficit` |
| `pair` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.TraderizedEnforcement.pair` |
| `position` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.TraderizedEnforcement.position` |
| `violation` | def | 2026-08-16-traderized-enforcement | Lean only | `Workspace.Normativity.Contrib.TraderizedEnforcement.violation` |

