# Claims registry — normativity

**Specification layer.** Every entry's *statement of record* is a checker
invocation or a fully-qualified Lean declaration, never prose. The class is part
of the claim; a class change is a diff to this file and therefore a maintainer
act. See `AGENTS.md`.

Schema: `### <id>` followed by one fenced `json` block with `class`,
`statement_of_record`, `answers_item`, `provenance`, and `docs`.

## The frozen consolidation is not migrated into this registry

`projects/normativity/consolidation-aug9/` carries **180 claims** with their own statuses. They
are **deliberately not re-registered here**, and the reason is not laziness.

Their statements of record are theory-part prose plus a verifier **inside the
frozen tree** — code that predates this regime and that a contributor did not
write, but that is also not the house checker harness. Re-registering them would
mean either relabelling 180 claims under a class vocabulary they were not stated
in, or asserting that the house checkers adjudicate them, and neither is true.
The frozen tree is immutable, so its own labels cannot be changed even if that
were desirable.

What holds instead: the tree is a **foundation**, verified continuously by CI's
`consolidation-verification` gate, which re-runs its own verifier on every push and
confirms 180 claims with statuses agreeing between its theory parts and its
ledger. Cite its claims by identifier against the frozen path, carrying the
status the tree itself gives them.

Migrating selected claims — most naturally as Lean ports — is filed as an open
problem rather than done by relabelling.

---

## Registered claims

### The traderization arc

Every entry below is a theorem its round presented as a result, filed with
the pull request that shipped it. `docs.verification` is the paper handoff,
which states each theorem in the form the paper would; `docs.context` is the
round register that says what it rests on.

### li.assessment.budgeter-value

```json
{
  "project": "normativity",
  "short_name": "lem:budgeter 1 over an assessment process",
  "origin_round": "2026-08-16-traderized-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.AssessmentProcess.BudgeterAt_value_eq_of_safe"
  },
  "answers_item": "47",
  "provenance": {
    "generator": "maintainer's round 2026-08-16-traderized-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-16-traderized-enforcement/THEOREM_MAP.md"
  },
  "note": "The budgeted trader's value equals the raw trader's while the budget is safe, over an arbitrary assessment process. Nesting is consumed here as well as in the floor: the available capital in each world's loss cap must be positive."
}
```

### li.assessment.budgeter-floor

```json
{
  "project": "normativity",
  "short_name": "lem:budgeter 2 over an assessment process",
  "origin_round": "2026-08-16-traderized-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.AssessmentProcess.budgetedTrader_netWorth_floor"
  },
  "answers_item": "47",
  "provenance": {
    "generator": "maintainer's round 2026-08-16-traderized-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-16-traderized-enforcement/THEOREM_MAP.md"
  },
  "note": "The budgeted trader's net worth has the source's floor at every plausible assessment. Nonemptiness of the world family is not a hypothesis: the scaling infimum over an empty plausible set is one."
}
```

### li.assessment.budgeter-exploits

```json
{
  "project": "normativity",
  "short_name": "lem:budgeter 3 over an assessment process",
  "origin_round": "2026-08-16-traderized-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.AssessmentProcess.exists_budgetedTrader_exploits"
  },
  "answers_item": "47",
  "provenance": {
    "generator": "maintainer's round 2026-08-16-traderized-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-16-traderized-enforcement/THEOREM_MAP.md"
  },
  "note": "An exploiting trader yields a budgeted exploiting trader, over an arbitrary assessment process."
}
```

### li.assessment.firm-dominance

```json
{
  "project": "normativity",
  "short_name": "lem:tfdom over an assessment process",
  "origin_round": "2026-08-16-traderized-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.AssessmentFirm.trading_firm_dominance"
  },
  "answers_item": "47",
  "provenance": {
    "generator": "maintainer's round 2026-08-16-traderized-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-16-traderized-enforcement/THEOREM_MAP.md"
  },
  "note": "The generalized trading firm dominates every budgeted trader, stated against the pinned dependency's own Strategy, Trader, EF and PCWorld."
}
```

### li.assessment.criterion

```json
{
  "project": "normativity",
  "short_name": "the generalized market is not exploited",
  "origin_round": "2026-08-16-traderized-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.AssessmentFirm.no_efficient_trader_exploits"
  },
  "answers_item": "47",
  "provenance": {
    "generator": "maintainer's round 2026-08-16-traderized-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-16-traderized-enforcement/THEOREM_MAP.md"
  },
  "note": "MarketMaker applied to the generalized trading firm satisfies the exploitation criterion relative to the assessment process. The market-computability premise is carried exactly as the pinned source carries it for itself."
}
```

### force.strategy-value

```json
{
  "project": "normativity",
  "short_name": "the enforcement position's exact rational market value",
  "origin_round": "2026-08-16-traderized-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.EnforcementStrategy.marketValueRat_enforcementStrategy"
  },
  "answers_item": "41",
  "provenance": {
    "generator": "maintainer's round 2026-08-16-traderized-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-16-traderized-enforcement/ENFORCEMENT.md"
  },
  "note": "The compiled enforcement position is a legal Strategy whose value against a payout table is exactly the quantity the force inequalities bound. Without this identity those inequalities are algebra about a vector rather than theorems about the strategy the market prices."
}
```

### force.row-tolerance

```json
{
  "project": "normativity",
  "short_name": "per-row conformance from a sufficient intensity",
  "origin_round": "2026-08-16-traderized-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.EnforcementStrategy.rowViolation_le_of_intensity_ge"
  },
  "answers_item": "41",
  "provenance": {
    "generator": "maintainer's round 2026-08-16-traderized-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-16-traderized-enforcement/ENFORCEMENT.md"
  },
  "note": "Positivity of the disturbance is load-bearing and is carried in the statement: at zero disturbance the intensity condition is met by a zero intensity, which enforces nothing."
}
```

### force.preservation

```json
{
  "project": "normativity",
  "short_name": "bounded assessed liability preserves the criterion",
  "origin_round": "2026-08-16-traderized-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.EnforcementPreservation.no_efficient_trader_exploits"
  },
  "answers_item": "41",
  "provenance": {
    "generator": "maintainer's round 2026-08-16-traderized-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-16-traderized-enforcement/FUNDING_AND_SAFETY.md"
  },
  "note": "Sufficiency only. The converse is item 40 and the forward proof discards information, so this is not an equivalence. The added trader is arbitrary; being an enforcement trader is not used."
}
```

### force.deductive-day-nonneg

```json
{
  "project": "normativity",
  "short_name": "zero liability at every date, deductively",
  "origin_round": "2026-08-16-traderized-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.DeductiveEnforcement.enforcement_day_value_nonneg"
  },
  "answers_item": "41",
  "provenance": {
    "generator": "maintainer's round 2026-08-16-traderized-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-16-traderized-enforcement/DEDUCTION_SPECIAL_CASE.md"
  },
  "note": "Every deductively plausible world lies in the coherence polytope, so the enforcement position's day value is nonnegative there for any nonnegative intensity."
}
```

### force.deductive-cumulative-nonneg

```json
{
  "project": "normativity",
  "short_name": "zero cumulative liability, deductively",
  "origin_round": "2026-08-16-traderized-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.DeductiveEnforcement.enforcement_netWorth_nonneg"
  },
  "answers_item": "41",
  "provenance": {
    "generator": "maintainer's round 2026-08-16-traderized-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-16-traderized-enforcement/DEDUCTION_SPECIAL_CASE.md"
  },
  "note": "Per-date nonnegativity summed. This is why deduction is the free case rather than one instance among equals: the risk capital is exactly zero, so no affordability side-condition binds and the tolerance schedule is unconstrained."
}
```

### force.deductive-criterion

```json
{
  "project": "normativity",
  "short_name": "the modified market satisfies the original criterion",
  "origin_round": "2026-08-16-traderized-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.DeductiveEnforcement.no_efficient_trader_exploits_of_worldInclusive"
  },
  "answers_item": "41",
  "provenance": {
    "generator": "maintainer's round 2026-08-16-traderized-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-16-traderized-enforcement/DEDUCTION_SPECIAL_CASE.md"
  },
  "note": "The dominance step is the pinned source's own trading_firm_dominance at its own DeductiveProcess, so the conclusion is the source's criterion over D rather than a generalization of it."
}
```

### force.deductive-inductor

```json
{
  "project": "normativity",
  "short_name": "the modified market is a logical inductor",
  "origin_round": "2026-08-16-traderized-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.DeductiveEnforcement.isLogicalInductor_of_computableMarket"
  },
  "answers_item": "41",
  "provenance": {
    "generator": "maintainer's round 2026-08-16-traderized-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-16-traderized-enforcement/DEDUCTION_SPECIAL_CASE.md"
  },
  "note": "The criterion form, assembled as the dependency's own IsLogicalInductor. Its computable-market hypothesis is discharged separately by the projection arc's compiler."
}
```

### force.deductive-witness

```json
{
  "project": "normativity",
  "short_name": "the safety theorem's hypothesis package is inhabited",
  "origin_round": "2026-08-16-traderized-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.DeductiveEnforcement.witness_market_not_exploited"
  },
  "answers_item": "41",
  "provenance": {
    "generator": "maintainer's round 2026-08-16-traderized-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-16-traderized-enforcement/DEDUCTION_SPECIAL_CASE.md"
  },
  "note": "A deductive process revealing one atom, an added trader, and the liability bound derived from the force algebra rather than assumed, at a presentation a legal price can violate. A theorem whose hypotheses nothing satisfies is empty, and the kernel cannot see the difference."
}
```

### coherence.modulus-soundness

```json
{
  "project": "normativity",
  "short_name": "no support-function row reports more than the distance",
  "origin_round": "2026-08-16-traderized-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_mixture"
  },
  "answers_item": "42",
  "provenance": {
    "generator": "maintainer's round 2026-08-16-traderized-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-16-traderized-enforcement/PROOF_CLOSURE.md"
  },
  "note": "The soundness half of the coherence measure. It does not answer item 42, which asks for a polynomially presentable family; it is the half of the measure item 42's narrowing is stated against."
}
```

### coherence.modulus-net-cover

```json
{
  "project": "normativity",
  "short_name": "conformance on a net bounds the support gap",
  "origin_round": "2026-08-16-traderized-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_net_cover"
  },
  "answers_item": "42",
  "provenance": {
    "generator": "maintainer's round 2026-08-16-traderized-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-16-traderized-enforcement/PROOF_CLOSURE.md"
  },
  "note": "Conformance at tolerance on an l1-net of a stated mesh bounds every support gap by tolerance plus mesh, with Lipschitz constant one. The constant is attained, so the bound is sharp; row conformance on an arbitrary presentation bounds no distance at all."
}
```

### compiler.schedule-end-to-end

```json
{
  "project": "normativity",
  "short_name": "the projection schedule's effective market is a logical inductor",
  "origin_round": "2026-08-18-projection-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.EnforcedCompiler.ProjectionSchedule.end_to_end_effective"
  },
  "answers_item": "48",
  "provenance": {
    "generator": "maintainer's round 2026-08-18-projection-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-18-projection-enforcement/FINAL_FORMALIZATION_STATUS.md"
  },
  "note": "No supplied market, region or representation. The one standing hypothesis is that the enforcer's trade map is primitive recursive, which is the definition of an effective enforcer and sits where the source's own process certificate sits."
}
```

### compiler.constraints-end-to-end

```json
{
  "project": "normativity",
  "short_name": "the constraint schedule's effective market is a logical inductor",
  "origin_round": "2026-08-18-projection-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.EffectiveRepresentation.end_to_end_of_constraints_effective"
  },
  "answers_item": "48",
  "provenance": {
    "generator": "maintainer's round 2026-08-18-projection-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-18-projection-enforcement/FINAL_FORMALIZATION_STATUS.md"
  },
  "note": "The generic form over a rational constraint schedule, written a second time over raw non-dependent data because the structured pipeline's types are not Primcodable. The obstruction was never that the generator is ineffective."
}
```

### compiler.deductive-end-to-end

```json
{
  "project": "normativity",
  "short_name": "finite-date coherence with the original criterion, deductively",
  "origin_round": "2026-08-18-projection-enforcement",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.DeductiveEffective.deductive_end_to_end"
  },
  "answers_item": "48",
  "provenance": {
    "generator": "maintainer's round 2026-08-18-projection-enforcement",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-18-projection-enforcement/FINAL_FORMALIZATION_STATUS.md"
  },
  "note": "The source's criterion over D together with per-date conformance at a computable tolerance schedule, assuming nothing about the deductive process beyond the source's own certificate plus propositional satisfiability of each stage. Computable, not efficient: the generator is doubly exponential in the fragment dimension."
}
```

### maxmin.representation

```json
{
  "project": "normativity",
  "short_name": "a piecewise affine function is a max of mins of its components",
  "origin_round": "2026-08-18-maxmin-representation",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.MaxMinRepresentation.exists_maxMin_representation"
  },
  "answers_item": "50",
  "provenance": {
    "generator": "maintainer's round 2026-08-18-maxmin-representation",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-18-maxmin-representation/README.md"
  },
  "note": "Ovchinnikov Theorem 4.1(a), for a nonempty convex domain in a topological real vector space. The source's proof silently needs full-dimensionality; the statement does not, and the round's errata carry a counterexample to the source's own nonemptiness claim."
}
```

### maxmin.converse

```json
{
  "project": "normativity",
  "short_name": "a max of mins of affine components is piecewise affine",
  "origin_round": "2026-08-18-maxmin-representation",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.MaxMinRepresentation.isPiecewiseAffineOn_maxMin"
  },
  "answers_item": "50",
  "provenance": {
    "generator": "maintainer's round 2026-08-18-maxmin-representation",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "projects/normativity/rounds/2026-08-18-maxmin-representation/README.md"
  },
  "note": "Theorem 4.1(b). The agreement obligation quantifies over all pieces, including index triples outside the relevant selection sets, so each piece carries a guard."
}
```

### region.patterns-sound

```json
{
  "project": "normativity",
  "short_name": "every enumerated pattern is realised by a plausible world",
  "origin_round": "2026-08-19-deductive-region",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_sound"
  },
  "answers_item": "51",
  "provenance": {
    "generator": "maintainer's round 2026-08-19-deductive-region",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "prompts/2026-08-19-deductive-region/REPORT.md"
  },
  "note": "Stated with the rational payout table rather than the real-valued one, which is what makes the list rational; the two agree by the repository's existing payout identity."
}
```

### region.patterns-complete

```json
{
  "project": "normativity",
  "short_name": "every plausible world's pattern is enumerated",
  "origin_round": "2026-08-19-deductive-region",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_complete"
  },
  "answers_item": "51",
  "provenance": {
    "generator": "maintainer's round 2026-08-19-deductive-region",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "prompts/2026-08-19-deductive-region/REPORT.md"
  },
  "note": "Completeness over the priced fragment, with no hypothesis on the fragment: coordinates may repeat or be empty."
}
```

### region.patterns-nonempty-iff

```json
{
  "project": "normativity",
  "short_name": "the enumeration is nonempty exactly when the stage is satisfiable",
  "origin_round": "2026-08-19-deductive-region",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_ne_nil_iff"
  },
  "answers_item": "51",
  "provenance": {
    "generator": "maintainer's round 2026-08-19-deductive-region",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "prompts/2026-08-19-deductive-region/REPORT.md"
  },
  "note": "A biconditional, so the satisfiability hypothesis is exact rather than merely sufficient: no weaker hypothesis suffices and no stronger one is used."
}
```

### region.hull

```json
{
  "project": "normativity",
  "short_name": "the region restricted to the fragment is the hull of the vertex list",
  "origin_round": "2026-08-19-deductive-region",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.DeductiveRegion.deductiveRegion_eq_convexHull"
  },
  "answers_item": "51",
  "provenance": {
    "generator": "maintainer's round 2026-08-19-deductive-region",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md",
    "context": "prompts/2026-08-19-deductive-region/REPORT.md"
  },
  "note": "An image equality, which is the form with content: membership is defined through the hull, so the unfolding form is definitional and says nothing. Duplicate-freeness of the fragment is used in the surjectivity direction only. The predicate is not a decision procedure: membership of an arbitrary real price vector is not decided here."
}
```

### smoke.faf-asymp-refl

```json
{
  "project": "normativity",
  "short_name": "FAF asymptotic-equivalence reflexivity smoke test",
  "origin_round": "2026-08-10-repo-scaffolding",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Smoke.faf_asympEq_refl"
  },
  "answers_item": "13",
  "provenance": {
    "generator": "maintainer's round 2026-08-10-repo-scaffolding",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-10-repo-scaffolding/REPORT.md",
    "context": "README.md"
  },
  "note": "Reaches a real declaration in the pinned dependency. Certifies the chain, not mathematics."
}
```

### smoke.chain-compiles

```json
{
  "project": "normativity",
  "short_name": "dependency-chain compilation smoke test",
  "origin_round": "2026-08-10-repo-scaffolding",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Smoke.chain_compiles"
  },
  "answers_item": "13",
  "provenance": {
    "generator": "maintainer's round 2026-08-10-repo-scaffolding",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-10-repo-scaffolding/REPORT.md",
    "context": "README.md"
  },
  "note": "States a Mathlib limit in the dependency's own vocabulary, so it typechecks only if both halves of the chain agree."
}
```

### simplex.rational-points-sum-to-one

```json
{
  "project": "normativity",
  "short_name": "rational simplex points sum to one",
  "origin_round": null,
  "status": "active",
  "class": "enumeration-verified",
  "statement_of_record": {
    "kind": "checker",
    "checker": "enumeration",
    "parameters": {
      "domain": "rational-simplex",
      "dimension": 3,
      "denominator": 6,
      "property": "satisfies-linear-constraints",
      "constraints": [
        {"coefficients": [1, 1, 1], "rhs": 1, "equality": true}
      ]
    }
  },
  "answers_item": "13",
  "provenance": {
    "generator": "maintainer's round 2026-08-10-contribution-architecture",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "checkers/README.md",
    "context": "CONTRIBUTING.md"
  },
  "note": "A worked example of the schema, not a research result: the house enumeration checker generates the 28 rational simplex points at denominator six and confirms each sums to one. It exists so the registry, the checker and the CI job are exercised by something real before any research claim depends on them."
}
```

### The legitimacy spine

The canonical theory of Legitimate Evolution and Normative Induction, registered at
the canonicalization of 2026-09-08 against item 78. Statements are exact; the
conditional Normative Inductor theorems are deliberately absent (see
`ni.progress-bound`).

### legitimacy.evolution-conservation

```json
{
  "project": "normativity",
  "short_name": "Integrity evolution conserves answerability",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.LegitimateEvolution.Evolution.conservation"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-07-final-pressure-pass",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md"
  },
  "note": "Answerability Conservation: along an Integrity evolution between accounted states, exposure only grows, every recorded answer or closure receipt persists, and the resolution witness each occurrence's account denotes is transported from the earlier state. Inhabited by `Witness.ev₀₁`. The hypotheses are the certificate data; nothing semantic is assumed beyond the protocol's typed inputs."
}
```

### legitimacy.propagate-to-segment

```json
{
  "project": "normativity",
  "short_name": "the target account is the propagation of the source",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.LegitimateEvolution.Evolution.propagate_toSegment"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-07-final-pressure-pass",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md"
  },
  "note": "An evolution's target account equals the propagation of its source account along the underlying segment: the account is determined by the certificate, so witnesses cannot disagree about either endpoint."
}
```

### legitimacy.receipts-immutable

```json
{
  "project": "normativity",
  "short_name": "a transition rewrites no recorded receipt",
  "origin_round": "2026-09-06-mathematical-consolidation",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.terminals_subst"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-06-mathematical-consolidation",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md"
  },
  "note": "Substitution at live ports keeps every terminal receipt and adds only the terminals of the substituted accounts. With `livePorts_subst` this is the three-fate accounting at the leaf level: terminal fates persist, live leaves are replaced."
}
```

### legitimacy.faithful-carry

```json
{
  "project": "normativity",
  "short_name": "carry is faithful by construction",
  "origin_round": "2026-09-06-mathematical-consolidation",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.evaluate_subst"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-06-mathematical-consolidation",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md"
  },
  "note": "The resolution witness a substituted account denotes is the original account's witness with each live port read through its replacement. Faithful transformation of live content is a consequence of the account type."
}
```

### legitimacy.multiplicity-witness

```json
{
  "project": "normativity",
  "short_name": "equal anchors, distinct fates",
  "origin_round": "2026-09-06-mathematical-consolidation",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness.distinct_fates"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-06-mathematical-consolidation",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md"
  },
  "note": "Two occurrences with the same anchor, one answered and one carried by a single transition, have accounts with fates `{answered}` and `{live}`. Occurrence identity lives outside the content type and the accounting is occurrence-indexed; an exact witness that equal content does not collapse debts."
}
```

### legitimacy.segment-trans

```json
{
  "project": "normativity",
  "short_name": "legitimate segments compose at a shared state",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.LegitimateEvolution.LegitimateSegment.trans"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-07-final-pressure-pass",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md"
  },
  "note": "Composition of legitimate-evolution certificates: the underlying evolutions concatenate at the literally shared state and per-state openness composes (`AllStates.trans`). Inhabited by `Witness.composed`, whose composite's accounts keep two equal-anchor occurrences apart."
}
```

### legitimacy.endpoint-trans

```json
{
  "project": "normativity",
  "short_name": "the endpoint relation is transitive",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.LegitimateEvolution.Legitimate.trans"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-07-final-pressure-pass",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md"
  },
  "note": "`Legitimate` is `Nonempty LegitimateSegment`; it hides the witness for consumers and is transitive. The certificate remains available for audit."
}
```

### legitimacy.answerable

```json
{
  "project": "normativity",
  "short_name": "Diachronic Answerability, decomposed",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.LegitimateEvolution.LegitimateSegment.answerable"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-07-final-pressure-pass",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md"
  },
  "note": "A legitimate segment yields Answerability Conservation from Integrity and Robust Openness (coverage of every live concern and the protected party's standing on every applicable one, actual branch and each counterfactual) at both endpoints, and by construction at every state between. Diachronic Answerability is derived, not a third conjunct."
}
```

### legitimacy.endpoint-only-insufficient

```json
{
  "project": "normativity",
  "short_name": "endpoint-only openness admits laundered exclusion",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.LegitimateEvolution.Witness.endpoint_only_insufficient"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-07-final-pressure-pass",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md"
  },
  "note": "Exact counterexample: a two-transition evolution open at both endpoints whose middle state has a live concern with no adequate route; it is not a legitimate segment. This is why openness is required at every state."
}
```

### openness.persistence-sufficient

```json
{
  "project": "normativity",
  "short_name": "the persistence bill gives Robust Openness on the actual and counterfactual branches",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.NonCapture.Scenario.robustOpenActual_of_persistence"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-07-final-pressure-pass",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md"
  },
  "note": "Actual coverage inside the protected route set, actual standing, silent-prefix coverage, componentwise persistence of protected routes, and principal standing give `RobustOpenActual`. A sufficient external certificate, not the contract: `Witness.persistence_not_necessary` separates it from Robust Openness. Inhabited by `Witness.persistence_inhabited`."
}
```

### openness.certplus-is-robust-openness

```json
{
  "project": "normativity",
  "short_name": "the split bill is Robust Openness itself",
  "origin_round": "2026-09-06-mathematical-consolidation",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.NonCapture.Scenario.certPlus_iff_robustOpen"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-06-mathematical-consolidation",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md"
  },
  "note": "Given actual coverage, the bill `(S) ∧ (R+) ∧ (P)` is logically equivalent to counterfactual Robust Openness: the conclusion factored by a case split, not an independent sufficient condition. Recorded so that the bill is not presented as a certificate."
}
```

### openness.actual-branch-witness

```json
{
  "project": "normativity",
  "short_name": "counterfactual openness does not contain the actual condition",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.NonCapture.Witness.counterfactual_open_not_actual"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-07-final-pressure-pass",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md"
  },
  "note": "Exact witness: counterfactual-only Robust Openness holds while the actual prefix has a live concern with no route and no principal standing. The public predicate is therefore `RobustOpenActual`, actual branch explicit."
}
```

### progress.edge-bound

```json
{
  "project": "normativity",
  "short_name": "the finite Progress bound at the edge endpoint",
  "origin_round": "2026-09-06-mathematical-consolidation",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.NormativeInductorComposition.edge_progress_bound"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-06-mathematical-consolidation",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md"
  },
  "note": "Transport-weighted edge response loss plus residual is bounded by the amplification-weighted service-mean defect, the transport-weighted error, and the residual charge, from nonnegative transport and defect, `PracticalCert` on every positive edge, and the weighted column bound. Executed by a Codex worker within the consolidation round."
}
```

### progress.edge-bound-quadratic

```json
{
  "project": "normativity",
  "short_name": "the quadratic Progress bound",
  "origin_round": "2026-09-06-mathematical-consolidation",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.NormativeInductorComposition.edge_progress_bound_quadratic"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-06-mathematical-consolidation",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md"
  },
  "note": "With intensity-normalized service weights and the uptake certificate `λ_s d_s² ≤ ρ_s`, the first term is `Γ √(Σρ/Σλ)`. Inhabited by `edge_progress_witness` with all three terms positive."
}
```

### progress.headline-separation

```json
{
  "project": "normativity",
  "short_name": "the headline endpoint is not the edge endpoint",
  "origin_round": "2026-09-06-mathematical-consolidation",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.NormativeInductorComposition.edge_headline_separation"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-06-mathematical-consolidation",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md"
  },
  "note": "Two equally weighted services with edge losses 0 and 1 average to one half, below a headline loss of one. The exposure-headline theorems remain as an optional corollary needing a dominance premise this shows is not free."
}
```

### ni.progress-bound

```json
{
  "project": "normativity",
  "short_name": "the Progress bound on the accounted export",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.NormativeInductionInterface.Evaluation.progress_bound"
  },
  "answers_item": "78",
  "provenance": {
    "generator": "maintainer's round 2026-09-07-final-pressure-pass",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md",
    "context": "projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md"
  },
  "note": "The quadratic bound typed on `Evaluation (O : ObligationState)`: the practical/uptake certificate at the realized market gives the three-term bound. Inhabited by `Witness.uptake` and `Witness.bound` at the Integrity witness state. The two conditional Normative Inductor theorems consuming it are not registered: the general one's Logical-Induction hypotheses are uninhabited, and the deductive one's joint package has no single witness."
}
```
