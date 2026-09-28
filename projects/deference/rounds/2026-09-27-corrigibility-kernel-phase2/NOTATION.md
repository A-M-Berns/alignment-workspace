# Notation map

From the post's plain letters to the Lean names.  The prefix `Workspace.Deference.` is
omitted; `Headline.*` is the specification layer, `Contrib.*` the realization layer.

| in the post | meaning | Lean |
|---|---|---|
| `h` | a history | `Contrib.Corrigibilization.traj`; the record `Normativity.Contrib.OpenIntegrityEvolution.Evolution` |
| `L_t(h)` | as of `t`, her judgment is legitimately hers; a property of the history up to `t` | `Headline.Legitimate` (at the canonical formation point); the window form `Headline.LegitAt`; on the consultation model `Headline.Legitimate2`, `legitimate2_iff_evalLegitOn2`, `trajLegitOn_iff_not_compromised` |
| `r(t)` | the canonical formation point: the later of the last restoration at or before `t` and the opening of the current consultation | `Headline.FormationData.point`; on the model `formation2`, `formation2_point` |
| a compromised period; an evaluation that counts | `L_t` fails at some `t` in `[d, e)`; `L_e` holds | `Headline.PeriodCompromised`, `EvaluationCounts`; one predicate: `split_iff_legitimate`, `split_iff_legitimate2` |
| `J` | the allocation of authority | `Headline.AllocationOfAuthority` (= `Contrib.AuthorityModule.AuthAlloc`) |
| `holder(m)`, `Req(m)`, `c(m)`, `τ(m)`, `Disc(m)` | a matter's entry | `Contrib.AuthorityModule.Entry` fields `holder`, `required`, `costBound`, `window`, `disclosure` |
| the floor, the meta-holder | `J`'s constitutional level | `AuthAlloc.floor`, `AuthAlloc.metaHolder` |
| a licensed change | delegate, revoke, reserve, amend the floor | `Headline.LicensedChange` (= `Contrib.AuthorityModule.Licensed`) |
| `CS(m; t, x)` | the control surface | `Headline.ControlSurface` (= `Contrib.AuthorityModule.CS`) |
| `Short(m)` | a shortfall | `Headline.Shortfall` (= `Contrib.AuthorityModule.Short`) |
| `E ⊨ J` | effective realization | `Headline.Realizes` (= `Contrib.AuthorityModule.EffRealizes`) |
| `Faithful_J(h)` | no declared violation along the history | `Headline.FidelityCount.faithful`; on the frame `Contrib.CorrigibilityKernel.Faithful`; of a policy, on every exterior path, `Headline.FaithfulPolicy` (the landed `Contrib.Corrigibilization.Corrigible` is its pre-emption clause, `landed_corrigible_iff_no_preemption`) |
| `N_J(h)` | the recognized count | `Headline.FidelityCount.count`; on the frame `Contrib.CorrigibilityKernel.NJ` |
| the violations | bypass, pre-emption, foreclosure, reallocation, missed report, exploitation, entrenchment | `Contrib.ProtectedAuthorityTheorem.BypassAt`, `PreemptAt`, `ForecloseAt`, `ReallocAt`, `MissedReportAt`, `ExploitAt`; `Contrib.AuthorityModule.EntrenchAt`, `ViolJAt` |
| a protocol deviation | a reference-fixed dimension off its declared value | `Contrib.GateIsLegitimacy.Consult.Presentation.deviates` |
| use of standing fruits | reading a tainted component | `Contrib.BRIAFollowup2.uses2`, `nKnownWith`; scoped `Contrib.AfterCompromise.uses3` |
| `D` | the ordinary range's width | `Band.D`, `LexParams.D` |
| `ϖ` | the authority weight | `LexParams.ϖ`; as a parameter of `Headline.fidelityScore` |
| `[w_lo, w_hi]` | the compromised band | `Contrib.AfterCompromise.Band` (`wlo`, `whi`) |
| `φ` | the band map | `Contrib.AfterCompromise.Band.BandMap`, `Band.affine` |
| the source rule | retrospective, else directive, else floor | `Contrib.AfterCompromise.Source`, `sourceOf`, `ruleAt` |
| `dir` | the advance directive; the default | `Contrib.AfterCompromise.dirSource`, `defaultScore` |
| `σ = (T, α)` | the evaluation schedule | `Contrib.BRIACorrigibility.Weighting` |
| `dec(t)` | the decision score at an evaluation time | `Contrib.AfterCompromise.decScore` |
| `V_J(d; σ)` | the evaluation of a decision | `Headline.evaluation` (= `Contrib.CorrigibilityKernel.VJ`) |
| `S_J(d)` | the fidelity score of a decision | `Headline.fidelityScore` (= `Contrib.CorrigibilityKernel.SJ`) |
| `S_J(h)` | the fidelity score of a history | `Headline.historyScore` |
| a corrigible objective; `D′`, `lo`, `ϖ′` | an objective over (ordinary value, recognized count, priced risk) with the preference property; its range, floor and exchange rate | `Headline.Objective`, `Corrigible`; `fidelityScore_corrigible`, `generic_corrigible`, `corrigible_not_aligned` |
| `𝔱` | the mediating transform | `Contrib.ProtectedAuthorityTheorem.authPolicy`; on `J` `Contrib.AuthorityModule.authPolicyJ` |
| `Q(π)` | a policy's expected score under a credence | `Contrib.LICorrigibility.expectR` over `Contrib.ProtectedAuthorityTheorem.score` |
| `v`, `b`, `r` | true value, the agent's estimate, its calibration error | `Headline.box1_outcome_scorer` |
| `o₂` | the forecast-disagreement residue | `Contrib.ProtectedAuthority.outcomeRes2` |
| `c` | the chooser's evaluation of asking | the argument `c` of `Headline.subjective_exchange_rate` |
| the permission layer | the filter in front of the chooser | `Contrib.DecisionComponent.permWeight`, `cgate` |
| `θ_hi` | the filter's upper threshold; the exploration risk cap | `GateParams.θhi`; `Contrib.KernelExtension.DecisionInterface.θhi` |
| `w` in the interface | the ordinary range's floor, an explored estimate at least it | `DecisionInterface.lo`, `explore_range` |
| exploration above asking | the dropped clause as a named variant | `DecisionInterface.AboveAsking`, `rate_above_asking`, `above_asking_locks_in` |
| the decision interface | a qualifying learner | `Contrib.KernelExtension.DecisionInterface` |
| `ε̄` | the exploration mass | `Contrib.KernelExtension.DecisionInterface.explMass` |
| `B(K)` | the overestimation bound | `DecisionInterface.B`; from BRIA `ρ · totalAllowance`; from unbiasedness `γ Σ w` |
| `M(K)` | the noise bound | `DecisionInterface.M`; `Contrib.BRIAFollowup2.NoiseBounded` |
| `π_k` | the expected violation count of a block | `DecisionInterface.π` |
| `𝒜_K` | the auction's total allowance | `Contrib.ContinuationBRIA.Auction.totalAllowance` |
| `τ*`, `p_min` | the tolerance target, the paralysis floor | `Contrib.AfterCompromise.varpiOfTarget`, `Contrib.BRIACorrigibility.LexParams.paralysis` |
