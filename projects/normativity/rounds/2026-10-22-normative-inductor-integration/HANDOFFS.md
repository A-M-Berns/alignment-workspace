# The handoffs, audited

The dispatch's pipeline, arrow by arrow: the Lean objects on each side, the theorem that joins
them, what it leaves undischarged, and what kind of gap it was. The state before this round is
PR #129 at `b1c17d30`; the state after is this round's commits.

```
accounted history ──adm──▶ grounds ──survivors──▶ canonical bundle ──bundlePres/κ──▶ enforcer
     O : ObligationState       Grounds d           NormState.bundle              WarrantSchedule.enforcer
                                                        │                              │
                                                        │ SupportedOn / interval        │ EffectiveEnforcer.adaptive DP
                                                        ▼                              ▼
                                                   licence, elimination      W.market DP = DeductiveEnforcement.history
                                                                                       │
                                            excess_le_tol ◀── rowViolation_le_tol ─────┤── isLogicalInductor
                                                   │                                   │
                             bracket_at_market / functional_at_market                  │ liability (OddsBankroll.Account)
                                                   ▼                                   │
                                     Problem.scoreR_le / scoreR_ge  ──▶ gate ──▶ PracticalCert ──▶ progress_bound
```

| arrow | left object | right object | theorem | before this round | gap class |
|---|---|---|---|---|---|
| accounted history → warrants | `ObligationState S anchor` (`OpenIntegrityEvolution`) | `Grounds d` | `Admission O G`: `origin : Occurrence d → Occ`, every ground's origin exposed | no object connected them; the Normative Inductor theorems quantified over an `Evaluation O` unrelated to the grounds | **missing semantic input**; typed, not derived (item 128) |
| warrants → active warrants | `Grounds d`, `DocketState`, `Settlement d` | `Grounds.survivors` | `mem_survivors`: in the grounds, not undercut (own port or a defeater port), kept by `settleOutcome`, citing a survivor; `activeIds_fixed` | `survivors` consumed the own port and `settleOutcome` and retired one step along `cites`; `defeaters` unused; occurrence 3 survived the undercut of 2 | **substantive**: the rule was wrong; repaired by the least fixed point |
| active warrants → joint region | `NormState` | `NormState.bundle`, `.region` | `region_iff`: the cube, the pins, every survivor's row, every live structural row | `Grounds.region` (port-only), `Grounds.settledRegion` (survivors, no structural rows), `forcedRegion` (seed, port-only) were three regions | **integration**: one bundle, `bundle_eq_settledBundle` and `region_iff` relate the views |
| joint region → certificates | `NormState.bundle` | `SupportedOn`, `Licensed` | `supportedOn_admissibleOn`, `NormState.licence_chain` | `Supported` cited the port-only bundle `Grounds.bundle`, so a certificate citing a rebutted or undercut occurrence stayed supported | **integration**: `Supported` is now `SupportedOn (settledBundle)`, the state's licence `SupportedOn N.bundle` |
| joint region → elimination | `NormState.seed` | `forcedInterval` | `NormState.interval_spec` (= `forcedInterval_spec`) | the elimination ran on `(seedAt n, W)` built by hand to equal the survivors | **integration**: `interval` reads the same seed as the bundle |
| joint region → enforcer rows | `NormState.bundle`, `wit` | `WarrantSchedule`, `compileAt` | `compileAt_eq_of_check`, `region_compileAt`, `mem_compileAt` | `rows5 := survivors.map toForceRow` by hand; no withholding; intensity a constant `β = 10` | **integration + accountability**: force withheld without a checked witness |
| enforcer → market | `EffectiveEnforcer` | `DeductiveEnforcement.history DP (E.adaptive DP)` | `WarrantSchedule.market`, `realizedEnforcer_strat` (`rfl`) | the warrant enforcer lived on the *assessment* market `EnforcementPreservation.history L`, where no computability result exists; the force layer's computability lives on the deductive market | **architectural mismatch**: resolved by running the rowwise trader on the deductive market; the assessment-market bankroll is an instance of the same `Account` |
| affordability | `OddsBankroll.Account` | `−B ≤ netWorth` | `Account.netWorth_ge_neg_odds`, `.netWorth_ge_neg_odds_reopened`; `WarrantSchedule.liability`, `.liability_reopened` | proved once, on the assessment market, with `3` baked in | **integration**: the interface is the account; cap `3` discharged on both markets (`enforcer_netWorth_lt_three`; the source firm's `tradingFirmTrader_netWorth_floor`) |
| market → Logical Induction | `W.market DP` | `IsLogicalInductor (W.market DP) DP` | `WarrantSchedule.isLogicalInductor` from `hliab` and `EffectiveEnforcerComputation`, the latter from `WarrantSchedule.computation` for finite-phase schedules | `ComputableMarket` was a hypothesis | **computability**: discharged for finite-phase schedules; the deductive process's computability stays an input (`DeductiveProcessComputation`), discharged at the fixture |
| market → conformance | `W.market DP` | `rowViolation ≤ tol`, `excess ≤ tol` | `rowViolation_le_tol`, `excess_le_tol`, `excess_le_tol_of_admitted` | `rowViolation_le_of_intensity_ge` needed the maker's contract and the volume term as hypotheses; nothing discharged them at the realized market | **substantive**: discharged from `marketMaker_day_value_le_cube` and `Strategy.abs_value_le`; a rational feasibility witness in the cube is the one hypothesis |
| conformance → certified bounds | rowwise excess | a functional's value at the price | `FunctionalCert.le_of_excess`, `BoundCert.transport`, `bracket_at_market`, `functional_at_market` | nothing: the dispatch's "do not silently identify rowwise violation with distance to the region" | **substantive**: the multiplier mass is the Lipschitz constant; distance to the region is not derived (item 125) |
| certified bounds → adapter | displayed scores | `softGate` | `Problem.scoreR_le`, `scoreR_ge`, `massOff_le`, `practicalCert` | `GatedChoice` needed `Region u A τ`, `Margin`, `Within b u d` at a region point `u`; no theorem produced them from the market | **integration**: the synthetic region point `u` makes `softGate_massOff_le_displayed` apply to displayed exclusion and margin |
| adapter → Progress | `PracticalCert` at every served edge | `Evaluation.progress_bound` | `AdapterProtocol.uptake` (derives `PracticalUptake`), `warrant_inductor` | `PracticalUptake` was a hypothesis of every end-to-end theorem | **integration**: derived; the declared constants (`lamS`, `ρ`, `Γ`, `εad`, `D`) and the adequacy losses are the inputs |

**Same objects, same history.** Every theorem in the right-hand chain is stated on
`W.market DP` for the one `W := schedule N F wit tol htol` built from the state process `N`;
the gate reads `W.market DP s (W.ι j)`; the certificates cite `W.bundle s = (N s).bundle`; the
enforcer's realized strategy is `enforcementStrategy (W.realizedPres DP n) n` by `rfl`.

**Computability**, as the dispatch asked: `ComputableMarket (W.market DP)` is not assumed.
It follows from `EnforcedCompiler.computableMarket` once the trade map is primitive
recursive, which `WarrantSchedule.computation` proves for a bundle schedule through finitely
many phases and a primitive recursive tolerance. The deductive process's own computability
(`DeductiveProcessComputation DP`) is the remaining input, discharged at the fixture
(`WarrantInductorWitness.process`) from the stage function being a step function.
