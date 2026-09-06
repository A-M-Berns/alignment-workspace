# Normative Inductor gap audit

Evidence labels are those required by the dispatch. Wiki pages supplied orientation only.

| Arrow | Landed input | This round | Remaining obligation | Status |
|---|---|---|---|---|
| history → qualitative `O_P` | `DefeatTrace`, `IssueTrace`, `Kind`, `dispose_successor` in `NormativeContinuity.lean` | `ObligationExport`, `export_sound`: historical exposure, live docket, immutable supplied specification, total unique fate, and live/discharged descendant | Join all concrete history event constructors; authenticate the supplied anchored specification and settlement-backed closure | lean-proved structural adapter; proposed definition/interface for full history |
| `O_P` → compiler input | PR82 §2 requires strict-prefix typed provenance | `Bundle.WellFormed` checks every cited row against the live docket; `failure_conserves` preserves cited obligations for every result | Prove row realization from anchored specifications, authority, current semantics, and distinct normative/value provenance | lean-proved conservation; open semantic compiler |
| compiler → joint operative region | `RationalPolytope`, `PolyhedralCoverage`, `ProjectionCompiler` and `EffectiveRepresentation` consume effective rational polyhedra | `checkCompiled_iff`, `compile_sound`, and `conflict_sound` prove witness/conflict soundness for a declared rational-row schema | Completeness for the schema; row-to-vertex conversion; alias/provenance checker | lean-proved soundness; open completeness/integration |
| joint region → projection enforcer | `EffectiveRepresentation.end_to_end_of_constraints_effective` | `CompiledDay.represents` types representability; `compiled_end_to_end` instantiates the landed theorem | Produce `vertices` and its equality to the compiled row region effectively | lean-proved conditional composition; proposed interface/open constructor |
| joint region → joint feasibility | Projection requires nonempty carrier, not interior | checked rational witness implies nonempty region; sound Farkas certificate refutes it | Decide feasibility or return `Unknown`; nonempty price region still does not imply response compatibility | lean-proved alternatives; open decision procedure/completeness |
| affordable service → schedule | PR82 reports the predictable-window cheapest-date construction at paper level | `Workload.liability_le`, `adapted`, `residual_zero`, `total_service_eq_total_claim`; `sampleWorkload_affordable` inhabits it | Connect liability weights to the market enforcer; online/adversarial docket remains open | lean-proved declared finite workload; open market connector/general scheduler |
| schedule → traderized uptake | `public_work_le_projection_work`; projection-force stack | `work_of_calibrated`, `work_ratio_le`, `mean_le_sqrt_mean_sq` | For each service date, identify public sup defect and projection work and provide positive cumulative intensity | lean-proved algebra; open per-date connector |
| uptake → practical response | PR82 `calibration_through_value_correspondence`, randomized argmax, `practical_response_compose` | `anchored_response_transport` packages `M=2L`, `epsilon=L(2 zeta+eta)+epsilon_resp` | Concrete authenticated counterfactual values and response adequacy against the realized distribution | lean-proved algebra; ambient assumption/open ecology |
| response → service transport | PR82 admissible edges and `old_service_implies_amplification` | `EndToEndHypotheses.edge` requires a certificate for every positive-mass edge against its one service defect | Construct an adapted transport plan before observing response; certify all edges sharing one realized `Pi_s` jointly | proposed interface; open realization |
| semantic edge → semantic chain | PR82 `affine_transport_compose` and exact-carry algebra | `chain_transport`, `chainCert_exact_carry` prove the finite fold | Generate quantitative constants; certify disposition as `(1,0)` if that policy is retained | lean-proved fold; ambient assumption/open generator |
| service transport → Progress | PR82 had an abstract paper proof and exact fixture | `progress_bound` proves the finite three-term inequality; `progress_bound_quadratic` derives `Prog ≤ Gamma sqrt(sum rho/sum lambda)+epsilonBar+D r` | Asymptotic vanishing hypotheses and construction of certified finite-horizon data | lean-proved finite theorem; open rates/construction |
| augmented enforcer → ordinary LI | `EnforcementPreservation.isLogicalInductor_of_computableMarket`; effective deductive construction in `end_to_end_of_constraints_effective` | final `EndToEndHypotheses.end_to_end` combines named certificates, packaged LI, and Progress | General history/compiler/scheduler connectors must construct the package; arbitrary regions require computable market | lean-proved conditional composition; open realization |

## Dependency graph

```text
Integrity + settlement trust + Robust Openness
                 |
                 v
      authenticated history export O_P
                 |
                 v
 typed row realization --> feasibility witness / accountable conflict
                 |                    |
                 v                    +--> conserved obligations
 effective rational representation
                 |
                 v
 projection enforcer -- SafeCert + computable market --> ordinary LI
                 |
                 v
        lambda d^2 <= rho
                 |
 value/response certificate + joint edge compatibility
                 |
                 v
 adapted service transport + affine semantic chain
                 |
                 v
 Prog <= Gamma sqrt(sum rho/sum lambda) + epsilonBar + D r
```

The final theorem is conditional because the arrows named as open above are fields, not derived facts.
