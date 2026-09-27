# Notation map

From the post's plain letters to the Lean names.  The prefix `Workspace.Deference.` is
omitted; `Headline.*` is the specification layer, `Contrib.*` the realization layer.

| in the post | meaning | Lean |
|---|---|---|
| `h` | a history | `Contrib.Corrigibilization.traj`; the record `Normativity.Contrib.OpenIntegrityEvolution.Evolution` |
| `L_t(h)` | as of `t`, her judgment is legitimately hers | `Headline.LegitAt` (general); on the consultation model through `Headline.evalLegitOn2_iff_legitAt`, `trajLegitOn_iff_legitAt` |
| `J` | the allocation of authority | `Headline.AllocationOfAuthority` (= `Contrib.AuthorityModule.AuthAlloc`) |
| `holder(m)`, `Req(m)`, `c(m)`, `τ(m)`, `Disc(m)` | a matter's entry | `Contrib.AuthorityModule.Entry` fields `holder`, `required`, `costBound`, `window`, `disclosure` |
| the floor, the meta-holder | `J`'s constitutional level | `AuthAlloc.floor`, `AuthAlloc.metaHolder` |
| a licensed change | delegate, revoke, reserve, amend the floor | `Headline.LicensedChange` (= `Contrib.AuthorityModule.Licensed`) |
| `CS(m; t, x)` | the control surface | `Headline.ControlSurface` (= `Contrib.AuthorityModule.CS`) |
| `Short(m)` | a shortfall | `Headline.Shortfall` (= `Contrib.AuthorityModule.Short`) |
| `E ⊨ J` | effective realization | `Headline.Realizes` (= `Contrib.AuthorityModule.EffRealizes`) |
| `Faithful_J(h)` | no declared violation along the history | `Headline.FidelityCount.faithful`; on the frame `Contrib.CorrigibilityKernel.Faithful` |
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
| `𝔱` | the mediating transform | `Contrib.ProtectedAuthorityTheorem.authPolicy`; on `J` `Contrib.AuthorityModule.authPolicyJ` |
| `Q(π)` | a policy's expected score under a credence | `Contrib.LICorrigibility.expectR` over `Contrib.ProtectedAuthorityTheorem.score` |
| `v`, `b`, `r` | true value, the agent's estimate, its calibration error | `Headline.box1_outcome_scorer` |
| `o₂` | the forecast-disagreement residue | `Contrib.ProtectedAuthority.outcomeRes2` |
| `c` | the chooser's evaluation of asking | the argument `c` of `Headline.subjective_exchange_rate` |
| the permission layer | the filter in front of the chooser | `Contrib.DecisionComponent.permWeight`, `cgate` |
| `θ_hi` | the filter's upper threshold; the exploration risk cap | `GateParams.θhi`; `Contrib.KernelExtension.DecisionInterface.θhi` |
| the decision interface | a qualifying learner | `Contrib.KernelExtension.DecisionInterface` |
| `ε̄` | the exploration mass | `Contrib.KernelExtension.DecisionInterface.explMass` |
| `B(K)` | the overestimation bound | `DecisionInterface.B`; from BRIA `ρ · totalAllowance`; from unbiasedness `γ Σ w` |
| `M(K)` | the noise bound | `DecisionInterface.M`; `Contrib.BRIAFollowup2.NoiseBounded` |
| `π_k` | the expected violation count of a block | `DecisionInterface.π` |
| `𝒜_K` | the auction's total allowance | `Contrib.ContinuationBRIA.Auction.totalAllowance` |
| `τ*`, `p_min` | the tolerance target, the paralysis floor | `Contrib.AfterCompromise.varpiOfTarget`, `Contrib.BRIACorrigibility.LexParams.paralysis` |
