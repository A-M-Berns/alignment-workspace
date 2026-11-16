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

The canonical theory of legitimacy and Normative Induction, registered at the
canonicalization of 2026-09-08 against item 78 and renamed at the
legitimacy-internal-external round of 2026-09-25. Legitimacy is internal ∧ external:
internal legitimacy is Integrity (the record's evolution, `integrity.*`) and authorship
(`authorship.*` in the deference registry); external legitimacy is Robust Openness
(`openness.*`) and transparency (unregistered, `TransparentChannel.Realizes`). The
conjunction of Integrity with Robust Openness at every state is the **open Integrity
evolution** (`open-integrity.*`), one component of legitimacy and the object the
activated-value stack consumes. Statements are exact; the conditional Normative Inductor
theorems are deliberately absent (see `ni.progress-bound`).

Old → new map of the renaming (the old entries stay below, `superseded`, and their
declarations resolve through deprecated aliases for one release):

| old id | new id | declaration | reason |
|---|---|---|---|
| `legitimacy.evolution-conservation` | `integrity.evolution-conservation` | `Workspace.Normativity.Contrib.LegitimateEvolution.Evolution.conservation` → `Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.conservation` | an Integrity result; the id names the component of internal legitimacy it belongs to |
| `legitimacy.propagate-to-segment` | `integrity.propagate-to-segment` | `Workspace.Normativity.Contrib.LegitimateEvolution.Evolution.propagate_toSegment` → `Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.propagate_toSegment` | an Integrity result; the id names the component |
| `legitimacy.receipts-immutable` | `integrity.receipts-immutable` | `unchanged` → `unchanged` | an Integrity result stated in `OccurrenceIntegrity`; the id names the component |
| `legitimacy.faithful-carry` | `integrity.faithful-carry` | `unchanged` → `unchanged` | an Integrity result stated in `OccurrenceIntegrity`; the id names the component |
| `legitimacy.multiplicity-witness` | `integrity.multiplicity-witness` | `unchanged` → `unchanged` | an Integrity witness; the id names the component |
| `legitimacy.segment-trans` | `open-integrity.segment-trans` | `Workspace.Normativity.Contrib.LegitimateEvolution.LegitimateSegment.trans` → `Workspace.Normativity.Contrib.OpenIntegrityEvolution.OpenIntegritySegment.trans` | the conjunction Integrity ∧ Robust Openness is the open Integrity evolution, one component of legitimacy, not legitimacy |
| `legitimacy.endpoint-trans` | `open-integrity.endpoint-trans` | `Workspace.Normativity.Contrib.LegitimateEvolution.Legitimate.trans` → `Workspace.Normativity.Contrib.OpenIntegrityEvolution.OpenIntegrity.trans` | the endpoint relation of the open Integrity evolution |
| `legitimacy.answerable` | `open-integrity.answerable` | `Workspace.Normativity.Contrib.LegitimateEvolution.LegitimateSegment.answerable` → `Workspace.Normativity.Contrib.OpenIntegrityEvolution.OpenIntegritySegment.answerable` | Diachronic Answerability is derived from the open Integrity evolution |
| `legitimacy.endpoint-only-insufficient` | `openness.endpoint-only-insufficient` | `Workspace.Normativity.Contrib.LegitimateEvolution.Witness.endpoint_only_insufficient` → `Workspace.Normativity.Contrib.OpenIntegrityEvolution.Witness.endpoint_only_insufficient` | a Robust Openness necessity witness; the id names the component of external legitimacy |

### integrity.evolution-conservation

```json
{
  "project": "normativity",
  "short_name": "Integrity evolution conserves answerability",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.conservation"
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
  "note": "Answerability Conservation: along an Integrity evolution between accounted states, exposure only grows, every recorded answer or closure receipt persists, and the resolution witness each occurrence's account denotes is transported from the earlier state. Inhabited by `Witness.ev₀₁`. The hypotheses are the certificate data; nothing semantic is assumed beyond the protocol's typed inputs. Renamed 2026-09-25 (the legitimacy-internal-external round): an Integrity result; the id names the component of internal legitimacy it belongs to.",
  "supersedes": "legitimacy.evolution-conservation"
}
```

### legitimacy.evolution-conservation

```json
{
  "project": "normativity",
  "short_name": "Integrity evolution conserves answerability",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "superseded",
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
  "note": "Answerability Conservation: along an Integrity evolution between accounted states, exposure only grows, every recorded answer or closure receipt persists, and the resolution witness each occurrence's account denotes is transported from the earlier state. Inhabited by `Witness.ev₀₁`. The hypotheses are the certificate data; nothing semantic is assumed beyond the protocol's typed inputs. Superseded 2026-09-25 by `integrity.evolution-conservation`; the declaration name is kept resolving by a deprecated alias for one release.",
  "superseded_by": "integrity.evolution-conservation"
}
```

### integrity.propagate-to-segment

```json
{
  "project": "normativity",
  "short_name": "the target account is the propagation of the source",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.propagate_toSegment"
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
  "note": "An evolution's target account equals the propagation of its source account along the underlying segment: the account is determined by the certificate, so witnesses cannot disagree about either endpoint. Renamed 2026-09-25 (the legitimacy-internal-external round): an Integrity result; the id names the component.",
  "supersedes": "legitimacy.propagate-to-segment"
}
```

### legitimacy.propagate-to-segment

```json
{
  "project": "normativity",
  "short_name": "the target account is the propagation of the source",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "superseded",
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
  "note": "An evolution's target account equals the propagation of its source account along the underlying segment: the account is determined by the certificate, so witnesses cannot disagree about either endpoint. Superseded 2026-09-25 by `integrity.propagate-to-segment`; the declaration name is kept resolving by a deprecated alias for one release.",
  "superseded_by": "integrity.propagate-to-segment"
}
```

### integrity.receipts-immutable

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
  "note": "Substitution at live ports keeps every terminal receipt and adds only the terminals of the substituted accounts. With `livePorts_subst` this is the three-fate accounting at the leaf level: terminal fates persist, live leaves are replaced. Renamed 2026-09-25 (the legitimacy-internal-external round): an Integrity result stated in `OccurrenceIntegrity`; the id names the component.",
  "supersedes": "legitimacy.receipts-immutable"
}
```

### legitimacy.receipts-immutable

```json
{
  "project": "normativity",
  "short_name": "a transition rewrites no recorded receipt",
  "origin_round": "2026-09-06-mathematical-consolidation",
  "status": "superseded",
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
  "note": "Substitution at live ports keeps every terminal receipt and adds only the terminals of the substituted accounts. With `livePorts_subst` this is the three-fate accounting at the leaf level: terminal fates persist, live leaves are replaced. Superseded 2026-09-25 by `integrity.receipts-immutable`; the declaration name is kept resolving by a deprecated alias for one release.",
  "superseded_by": "integrity.receipts-immutable"
}
```

### integrity.faithful-carry

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
  "note": "The resolution witness a substituted account denotes is the original account's witness with each live port read through its replacement. Faithful transformation of live content is a consequence of the account type. Renamed 2026-09-25 (the legitimacy-internal-external round): an Integrity result stated in `OccurrenceIntegrity`; the id names the component.",
  "supersedes": "legitimacy.faithful-carry"
}
```

### legitimacy.faithful-carry

```json
{
  "project": "normativity",
  "short_name": "carry is faithful by construction",
  "origin_round": "2026-09-06-mathematical-consolidation",
  "status": "superseded",
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
  "note": "The resolution witness a substituted account denotes is the original account's witness with each live port read through its replacement. Faithful transformation of live content is a consequence of the account type. Superseded 2026-09-25 by `integrity.faithful-carry`; the declaration name is kept resolving by a deprecated alias for one release.",
  "superseded_by": "integrity.faithful-carry"
}
```

### integrity.multiplicity-witness

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
  "note": "Two occurrences with the same anchor, one answered and one carried by a single transition, have accounts with fates `{answered}` and `{live}`. Occurrence identity lives outside the content type and the accounting is occurrence-indexed; an exact witness that equal content does not collapse debts. Renamed 2026-09-25 (the legitimacy-internal-external round): an Integrity witness; the id names the component.",
  "supersedes": "legitimacy.multiplicity-witness"
}
```

### legitimacy.multiplicity-witness

```json
{
  "project": "normativity",
  "short_name": "equal anchors, distinct fates",
  "origin_round": "2026-09-06-mathematical-consolidation",
  "status": "superseded",
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
  "note": "Two occurrences with the same anchor, one answered and one carried by a single transition, have accounts with fates `{answered}` and `{live}`. Occurrence identity lives outside the content type and the accounting is occurrence-indexed; an exact witness that equal content does not collapse debts. Superseded 2026-09-25 by `integrity.multiplicity-witness`; the declaration name is kept resolving by a deprecated alias for one release.",
  "superseded_by": "integrity.multiplicity-witness"
}
```

### open-integrity.segment-trans

```json
{
  "project": "normativity",
  "short_name": "legitimate segments compose at a shared state",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.OpenIntegrityEvolution.OpenIntegritySegment.trans"
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
  "note": "Composition of legitimate-evolution certificates: the underlying evolutions concatenate at the literally shared state and per-state openness composes (`AllStates.trans`). Inhabited by `Witness.composed`, whose composite's accounts keep two equal-anchor occurrences apart. Renamed 2026-09-25 (the legitimacy-internal-external round): the conjunction Integrity ∧ Robust Openness is the open Integrity evolution, one component of legitimacy, not legitimacy.",
  "supersedes": "legitimacy.segment-trans"
}
```

### legitimacy.segment-trans

```json
{
  "project": "normativity",
  "short_name": "legitimate segments compose at a shared state",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "superseded",
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
  "note": "Composition of legitimate-evolution certificates: the underlying evolutions concatenate at the literally shared state and per-state openness composes (`AllStates.trans`). Inhabited by `Witness.composed`, whose composite's accounts keep two equal-anchor occurrences apart. Superseded 2026-09-25 by `open-integrity.segment-trans`; the declaration name is kept resolving by a deprecated alias for one release.",
  "superseded_by": "open-integrity.segment-trans"
}
```

### open-integrity.endpoint-trans

```json
{
  "project": "normativity",
  "short_name": "the endpoint relation is transitive",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.OpenIntegrityEvolution.OpenIntegrity.trans"
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
  "note": "`Legitimate` is `Nonempty LegitimateSegment`; it hides the witness for consumers and is transitive. The certificate remains available for audit. Renamed 2026-09-25 (the legitimacy-internal-external round): the endpoint relation of the open Integrity evolution.",
  "supersedes": "legitimacy.endpoint-trans"
}
```

### legitimacy.endpoint-trans

```json
{
  "project": "normativity",
  "short_name": "the endpoint relation is transitive",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "superseded",
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
  "note": "`Legitimate` is `Nonempty LegitimateSegment`; it hides the witness for consumers and is transitive. The certificate remains available for audit. Superseded 2026-09-25 by `open-integrity.endpoint-trans`; the declaration name is kept resolving by a deprecated alias for one release.",
  "superseded_by": "open-integrity.endpoint-trans"
}
```

### open-integrity.answerable

```json
{
  "project": "normativity",
  "short_name": "Diachronic Answerability, decomposed",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.OpenIntegrityEvolution.OpenIntegritySegment.answerable"
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
  "note": "A legitimate segment yields Answerability Conservation from Integrity and Robust Openness (coverage of every live concern and the protected party's standing on every applicable one, actual branch and each counterfactual) at both endpoints, and by construction at every state between. Diachronic Answerability is derived, not a third conjunct. Renamed 2026-09-25 (the legitimacy-internal-external round): Diachronic Answerability is derived from the open Integrity evolution.",
  "supersedes": "legitimacy.answerable"
}
```

### legitimacy.answerable

```json
{
  "project": "normativity",
  "short_name": "Diachronic Answerability, decomposed",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "superseded",
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
  "note": "A legitimate segment yields Answerability Conservation from Integrity and Robust Openness (coverage of every live concern and the protected party's standing on every applicable one, actual branch and each counterfactual) at both endpoints, and by construction at every state between. Diachronic Answerability is derived, not a third conjunct. Superseded 2026-09-25 by `open-integrity.answerable`; the declaration name is kept resolving by a deprecated alias for one release.",
  "superseded_by": "open-integrity.answerable"
}
```

### openness.endpoint-only-insufficient

```json
{
  "project": "normativity",
  "short_name": "endpoint-only openness admits laundered exclusion",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.OpenIntegrityEvolution.Witness.endpoint_only_insufficient"
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
  "note": "Exact counterexample: a two-transition evolution open at both endpoints whose middle state has a live concern with no adequate route; it is not a legitimate segment. This is why openness is required at every state. Renamed 2026-09-25 (the legitimacy-internal-external round): a Robust Openness necessity witness; the id names the component of external legitimacy.",
  "supersedes": "legitimacy.endpoint-only-insufficient"
}
```

### legitimacy.endpoint-only-insufficient

```json
{
  "project": "normativity",
  "short_name": "endpoint-only openness admits laundered exclusion",
  "origin_round": "2026-09-07-final-pressure-pass",
  "status": "superseded",
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
  "note": "Exact counterexample: a two-transition evolution open at both endpoints whose middle state has a live concern with no adequate route; it is not a legitimate segment. This is why openness is required at every state. Superseded 2026-09-25 by `openness.endpoint-only-insufficient`; the declaration name is kept resolving by a deprecated alias for one release.",
  "superseded_by": "openness.endpoint-only-insufficient"
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

### The warrant licence chain

The citation discipline for `Licensed` and its two countermodels, round
`2026-10-20-warrant-enforcement-semantics`, against item 56.

### warrant.licence-chain

```json
{
  "project": "normativity",
  "short_name": "Licensed → Supported → Admissible",
  "origin_round": "2026-10-20-warrant-enforcement-semantics",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantEntitlement.licence_chain"
  },
  "answers_item": "56",
  "provenance": {
    "generator": "maintainer's round 2026-10-20-warrant-enforcement-semantics",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/LICENCE_CHAIN.md",
    "context": "projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/COUNTERMODELS.md"
  },
  "note": "A licensed verdict is supported on the record's grounds and admissible in their region; supported-to-admissible is by rational convexity of the bundle's region (region_convex), not a projection."
}
```

### warrant.supported-admissible

```json
{
  "project": "normativity",
  "short_name": "Supported → Admissible",
  "origin_round": "2026-10-20-warrant-enforcement-semantics",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantEntitlement.supported_admissible"
  },
  "answers_item": "56",
  "provenance": {
    "generator": "maintainer's round 2026-10-20-warrant-enforcement-semantics",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/LICENCE_CHAIN.md",
    "context": "projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/COUNTERMODELS.md"
  },
  "note": "A verdict bracketed by two cited bound certificates with attained endpoints is attained in the region."
}
```

### warrant.admissible-not-supported

```json
{
  "project": "normativity",
  "short_name": "Admissible does not imply Supported",
  "origin_round": "2026-10-20-warrant-enforcement-semantics",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.admissible_not_supported"
  },
  "answers_item": "56",
  "provenance": {
    "generator": "maintainer's round 2026-10-20-warrant-enforcement-semantics",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/LICENCE_CHAIN.md",
    "context": "projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/COUNTERMODELS.md"
  },
  "note": "Two occurrences with the same row; defeating one leaves the region unchanged, refuses the certificate citing it, and admits a certificate citing the survivor. The countermodel to any licence depending only on the region."
}
```

### warrant.supported-not-licensed

```json
{
  "project": "normativity",
  "short_name": "Supported does not imply Licensed",
  "origin_round": "2026-10-20-warrant-enforcement-semantics",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.supported_not_licensed"
  },
  "answers_item": "56",
  "provenance": {
    "generator": "maintainer's round 2026-10-20-warrant-enforcement-semantics",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/LICENCE_CHAIN.md",
    "context": "projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/COUNTERMODELS.md"
  },
  "note": "Two verdicts inside a forced interval of positive width, both supported by one cited certificate; licensed on the record that authorizes the selecting event and not on the one that does not."
}
```

### warrant.selection-not-transparent

```json
{
  "project": "normativity",
  "short_name": "the unauthorized selection fails transparency",
  "origin_round": "2026-10-20-warrant-enforcement-semantics",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.selection_not_transparent"
  },
  "answers_item": "56",
  "provenance": {
    "generator": "maintainer's round 2026-10-20-warrant-enforcement-semantics",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/LICENCE_CHAIN.md",
    "context": "projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/COUNTERMODELS.md"
  },
  "note": "An instance of GateIsLegitimacy.tiebreak_transparency: two continuations with the same declared inputs and different advisor contributions at the selection event fail TransparentAt for every reference."
}
```

### Rebuttal by settlement and the seed statics

Round `2026-10-21-rebuttal-and-end-to-end`; the dispatch's registration list, against items 113, 39, 117 and 119.

### rebuttal.settleform-sound

```json
{
  "project": "normativity",
  "short_name": "settleForm keeps exactly the specialized rows of non-degenerate forms",
  "origin_round": "2026-10-21-rebuttal-and-end-to-end",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantEntitlement.settleForm_eq_some_iff"
  },
  "answers_item": "113",
  "provenance": {
    "generator": "maintainer's round 2026-10-21-rebuttal-and-end-to-end",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/REBUTTAL.md",
    "context": "projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/REBUTTAL.md"
  },
  "note": "The rule of M1-M2 as a function on the form; a form whose premise, antecedent or consequent coordinate is pinned false contributes no row, every other form contributes its specialized row with its own strength. The removed rows are the contraposing ones (strength_contraposes)."
}
```

### rebuttal.liability-rebutted

```json
{
  "project": "normativity",
  "short_name": "the fixture's bankroll across the rebuttal",
  "origin_round": "2026-10-21-rebuttal-and-end-to-end",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.liability_rebutted"
  },
  "answers_item": "113",
  "provenance": {
    "generator": "maintainer's round 2026-10-21-rebuttal-and-end-to-end",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/REBUTTAL.md",
    "context": "projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/REBUTTAL.md"
  },
  "note": "Under the rule, with Y refuted at nE and the applicability port defeated at n0, the enforcer's assessed net worth is at least -3 rho (2 + rho) at every live world at every date, through netWorth_ge_neg_odds_reopened; the dispatch's 3 rho is refuted by the round's cushion exhibit (test-supported)."
}
```

### seed.forced-interval-spec

```json
{
  "project": "normativity",
  "short_name": "the computed forced interval is valid and attained over the reals",
  "origin_round": "2026-10-21-rebuttal-and-end-to-end",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.SeedStatics.forcedInterval_spec"
  },
  "answers_item": "39",
  "provenance": {
    "generator": "maintainer's round 2026-10-21-rebuttal-and-end-to-end",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/seed/rounds/2026-09-16-seed-statics/STATICS.md",
    "context": "projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md"
  },
  "note": "Fourier-Motzkin elimination of every coordinate but phi computes endpoints that bound P(phi) over the real forced region and are attained there. Rational attainment is item 118."
}
```

### seed.forced-interval-bounds

```json
{
  "project": "normativity",
  "short_name": "the computed endpoints are valid rational bounds",
  "origin_round": "2026-10-21-rebuttal-and-end-to-end",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.SeedStatics.forcedInterval_bounds"
  },
  "answers_item": "39",
  "provenance": {
    "generator": "maintainer's round 2026-10-21-rebuttal-and-end-to-end",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/seed/rounds/2026-09-16-seed-statics/STATICS.md",
    "context": "projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md"
  },
  "note": "LowerBound and UpperBound on the rational forced region for the elimination's endpoints, when the real region is nonempty."
}
```

### seed.independence-strict

```json
{
  "project": "normativity",
  "short_name": "seed-independence under strict humility",
  "origin_round": "2026-10-21-rebuttal-and-end-to-end",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.SeedStatics.seed_independence_strict"
  },
  "answers_item": "117",
  "provenance": {
    "generator": "maintainer's round 2026-10-21-rebuttal-and-end-to-end",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/seed/rounds/2026-09-16-seed-statics/CRITERION.md",
    "context": "projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md"
  },
  "note": "A point forced by a closed convex layer cut by an open layer is forced by the closed layer alone; two reasoners sharing the closed layer with strict substantive rows pin the same coordinate to the same value. Refuted for item-level humility by c3_refuted."
}
```

### seed.eventually-const

```json
{
  "project": "normativity",
  "short_name": "conditional stabilization on a finite discovery class",
  "origin_round": "2026-10-21-rebuttal-and-end-to-end",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.SeedStatics.eventually_const_of_finite"
  },
  "answers_item": "117",
  "provenance": {
    "generator": "maintainer's round 2026-10-21-rebuttal-and-end-to-end",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/seed/rounds/2026-09-16-seed-statics/STABILIZATION.md",
    "context": "projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md"
  },
  "note": "Along a chain with a monotone raised subset of a finite class and monotone settlement, any quantity computed from the two is eventually constant."
}
```

### convergence.hull-mass-anti

```json
{
  "project": "normativity",
  "short_name": "hull mass is nonincreasing under nesting",
  "origin_round": "2026-10-21-rebuttal-and-end-to-end",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.ConvergenceMeasure.hullMass_anti"
  },
  "answers_item": "119",
  "provenance": {
    "generator": "maintainer's round 2026-10-21-rebuttal-and-end-to-end",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/seed/rounds/2026-09-17-convergence-measure/DYNAMICS.md",
    "context": "projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md"
  },
  "note": "Settlement, shared narrowing and private narrowing lower the hull mass under nonnegative weights."
}
```

### convergence.discord-persists

```json
{
  "project": "normativity",
  "short_name": "discord persists under nesting",
  "origin_round": "2026-10-21-rebuttal-and-end-to-end",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.ConvergenceMeasure.discord_persists"
  },
  "answers_item": "119",
  "provenance": {
    "generator": "maintainer's round 2026-10-21-rebuttal-and-end-to-end",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/seed/rounds/2026-09-17-convergence-measure/DYNAMICS.md",
    "context": "projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md"
  },
  "note": "Once the common interval is empty no narrowing restores it; only reopening can."
}
```

### convergence.discord-pairwise

```json
{
  "project": "normativity",
  "short_name": "discord is pairwise (Helly in dimension one)",
  "origin_round": "2026-10-21-rebuttal-and-end-to-end",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.ConvergenceMeasure.discord_iff_pair"
  },
  "answers_item": "119",
  "provenance": {
    "generator": "maintainer's round 2026-10-21-rebuttal-and-end-to-end",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/seed/rounds/2026-09-17-convergence-measure/MANY.md",
    "context": "projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md"
  },
  "note": "The common interval is empty iff some pair of reasoners has disjoint intervals; merged infeasibility is not pairwise, which is item 119."
}
```

### inductor.grounded-survivors

```json
{
  "project": "normativity",
  "short_name": "the survivors are the grounded fixed point",
  "origin_round": "2026-10-22-normative-inductor-integration",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantEntitlement.mem_survivors"
  },
  "answers_item": "112",
  "provenance": {
    "generator": "maintainer's round 2026-10-22-normative-inductor-integration",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-10-22-normative-inductor-integration/THEOREM_STORY.md",
    "context": "projects/normativity/rounds/2026-10-22-normative-inductor-integration/HANDOFFS.md"
  },
  "note": "An occurrence survives iff it is in the grounds, not undercut (own port or a defeater port), kept by settleOutcome, and cites a survivor; the survivors are the least fixed point of activeStep, so undercut, retirement, vacuity and rebuttal propagate along citation chains of every length with no closure on the settlement."
}
```

### inductor.conformance

```json
{
  "project": "normativity",
  "short_name": "rowwise conformance at the realized deductive market",
  "origin_round": "2026-10-22-normative-inductor-integration",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.excess_le_tol"
  },
  "answers_item": "39",
  "provenance": {
    "generator": "maintainer's round 2026-10-22-normative-inductor-integration",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-10-22-normative-inductor-integration/THEOREM_STORY.md",
    "context": "projects/normativity/rounds/2026-10-22-normative-inductor-integration/HANDOFFS.md"
  },
  "note": "With a rational cube point in the day's compiled bundle's region, every row of the bundle has excess at most the tolerance at the displayed price of the augmented deductive market; the slack and volume terms are the real market maker's contract and the ordinary aggregate's syntactic bound, and the calibrated intensity buys the tolerance. Rowwise, not distance to the region (item 125)."
}
```

### inductor.certificate-transport

```json
{
  "project": "normativity",
  "short_name": "a supported verdict's bracket holds at the displayed price within mass times tolerance",
  "origin_round": "2026-10-22-normative-inductor-integration",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.bracket_at_market"
  },
  "answers_item": "124",
  "provenance": {
    "generator": "maintainer's round 2026-10-22-normative-inductor-integration",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-10-22-normative-inductor-integration/THEOREM_STORY.md",
    "context": "projects/normativity/rounds/2026-10-22-normative-inductor-integration/HANDOFFS.md"
  },
  "note": "A certificate's multiplier sum is the Lipschitz constant of its bound in the rows' excesses (FunctionalCert.le_of_excess); for a verdict supported on the day's bundle the displayed price lies in the certified bracket widened by mass times the tolerance on each side."
}
```

### inductor.warrant-inductor

```json
{
  "project": "normativity",
  "short_name": "the warrant Normative Inductor: LI, conformance, provenance, adapter, Progress on one market",
  "origin_round": "2026-10-22-normative-inductor-integration",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantInductor.warrant_inductor"
  },
  "answers_item": "35",
  "provenance": {
    "generator": "maintainer's round 2026-10-22-normative-inductor-integration",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-10-22-normative-inductor-integration/THEOREM_STORY.md",
    "context": "projects/normativity/rounds/2026-10-22-normative-inductor-integration/HANDOFFS.md"
  },
  "note": "On the augmented deductive market of the compiled schedule of a normative state process: Logical Induction over the deductive process from a liability bound and the enforcer's effectiveness; rowwise conformance at every enforced date and the provenance of every held row to an entitled survivor, a structural row or a pin; the gate's inadequate mass at most κ times the public defect, itself at most the certificates' mass times the tolerance; and the Progress bound with PracticalUptake derived. The entitlement (with its Expresses relation), the adequate sets, the adequacy losses and the declared constants are the semantic inputs; the compiler's results are the compile inputs, and a withheld date carries no conformance claim. Since 2026-10-23 the hypotheses are ent (Entitlement), res (CompileResult) and henf (Enforced) in place of adm, wit and hcheck."
}
```

### inductor.witness

```json
{
  "project": "normativity",
  "short_name": "the warrant Normative Inductor, run with computability and liability discharged",
  "origin_round": "2026-10-22-normative-inductor-integration",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantInductorWitness.inductor"
  },
  "answers_item": "35",
  "provenance": {
    "generator": "maintainer's round 2026-10-22-normative-inductor-integration",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-10-22-normative-inductor-integration/THEOREM_STORY.md",
    "context": "projects/normativity/rounds/2026-10-22-normative-inductor-integration/HANDOFFS.md"
  },
  "note": "warrant_inductor at the five-sentence fixture, Scenario A (the undercut): the deductive process and the enforcer are computable (process, computation), the bankroll across the rebuttal is −72 (liability); the gate puts mass at most 1/25 on refraining before the undercut and 1/100 on the surviving warrant after the rebuttal (gate_bounds); Progress ≤ 37/100 (progress_le). Since 2026-10-23 the entitlement is on state₀ with both accounts live and every date's compile outcome is enforced."
}
```

### inductor.rebuttal-run

```json
{
  "project": "normativity",
  "short_name": "the warrant Normative Inductor, run on the rebuttal of a still-active strength (Scenario B)",
  "origin_round": "2026-10-23-normative-inductor-consolidation",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantInductorRebuttal.inductor"
  },
  "answers_item": "35",
  "provenance": {
    "generator": "maintainer's round 2026-10-23-normative-inductor-consolidation",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-10-23-normative-inductor-consolidation/THEOREM.md",
    "context": "projects/normativity/rounds/2026-10-23-normative-inductor-consolidation/THEOREM_STORY.md"
  },
  "note": "warrant_inductor at the same fixture with a quiet docket: the strength is operative until its consequent is refuted at date 8 and leaves by rebuttal (operative_before, withdrawn); every date is enforced; the bankroll is −72 (liability) with the applicability row among those the post-refutation slack world dominates. The same question (act on the conclusion or refrain) is posed at dates 4 and 9: the region flips (region_flips), no Excludes or Margins certificate exists at date 9 (no_certificate_after), and the gate's mass on acting goes from at least 24/25 to 0 at the realized market (same_question); the dropped service's mass 1/4 is in the residual (residual_restricted)."
}
```

### inductor.contraposition-blocked

```json
{
  "project": "normativity",
  "short_name": "rebuttal withdraws the strength row that, kept, would have made the compiled system infeasible",
  "origin_round": "2026-10-23-normative-inductor-consolidation",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantInductorRebuttal.contraposition_blocked"
  },
  "answers_item": "113",
  "provenance": {
    "generator": "maintainer's round 2026-10-23-normative-inductor-consolidation",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-10-23-normative-inductor-consolidation/THEOREM.md",
    "context": "projects/normativity/rounds/2026-10-23-normative-inductor-consolidation/THEOREM_STORY.md"
  },
  "note": "At date 9 of Scenario B the specialized strength row reads 2/3·P(X∧A) ≤ 0 while the enforced applicability row with X settled true forces P(X∧A) ≥ 3/4 (antecedent_open): the date-9 bundle with the strength row appended has empty region. Rebuttal by settlement removes the row, so the antecedent's credence stays where the applicability puts it rather than being suppressed by contraposition."
}
```

### scoreside.same-question-two-realizations

```json
{
  "project": "normativity",
  "short_name": "the rebuttal run's decision in two realizations: on prices with no obligation on conduct, and on the score with the obligation charged",
  "origin_round": "2026-11-07-score-side-binding",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantInductorScoreSide.same_question_two_realizations"
  },
  "answers_item": "35",
  "provenance": {
    "generator": "maintainer's round 2026-11-07-score-side-binding",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-07-score-side-binding/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-07-score-side-binding/REPORT.md"
  },
  "note": "The rebuttal run's market and bundle, with the obligation on conduct 'refrain while the originating obligation's account is live' — one shortfall sentence per date, and the named hypothesis Assessed: the valuation settling the sentences makes the date-n sentence true iff ShortfallAt n, read off the state accounted at n (state₀ at every date) — charged at ϖ times the market's price of the date's shortfall sentence and subtracted from the acting score. On prices with no obligation on conduct: the rebuttal run's same_question. On the score, under Assessed: acting with mass at least 24/25 at date 4 while ϖ times the date-4 shortfall price is at most 19/240 (the hypothesis hsmall), refraining with certainty at date 9 for every nonnegative charge, acting assessed a shortfall at both dates (before, after). The realization stores the run's schedule, so bundle_unchanged and market_unchanged (rfl) are design facts, not results, and no_conduct_row says the one row refrain was compiled to is held at no date. A charge reaching the acting score's room above τ zeroes the act's weight with no price moved (override). The strength row is necessary: at p₀ = (1, 3/4, 0, 0, 3/4), in the cube and satisfying every date-4 row but the specialized strength row, the charged gate refrains with certainty for every nonnegative charge (strength_row_necessary; scoreGate_eq_gateAt ties that gate to the realized one). Not shown: that the market prices the shortfall sentences well, or that they are generable."
}
```

### scoreside.conduct-on-prices-conflicts

```json
{
  "project": "normativity",
  "short_name": "the obligation on conduct compiled onto prices conflicts with the epistemic rows at date 4",
  "origin_round": "2026-11-07-score-side-binding",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantInductorScoreSide.conduct_on_prices_conflicts"
  },
  "answers_item": "35",
  "provenance": {
    "generator": "maintainer's round 2026-11-07-score-side-binding",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-07-score-side-binding/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-07-score-side-binding/REPORT.md"
  },
  "note": "The date-4 bundle of the rebuttal run with the conduct row P(X∧A∧Y) ≤ 1/3 appended has no admissible price vector: the three-row Farkas certificate conductCert (the specialized strength row, two thirds of the specialized applicability row, the conduct row) sums to 0 ≤ −1/6, through conflict_sound. A compiler returning it withholds the date. At date 9 the conduct row is implied by the pin and adds nothing (conduct_on_prices_idle)."
}
```

### solvency.bounded-iff-frequency

```json
{
  "project": "normativity",
  "short_name": "solvency as soundness: a warrant schema's enforcer liability is bounded iff the consequent's frequency on undefeated instances is not systematically below the strength",
  "origin_round": "2026-11-07-score-side-binding",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantSolvency.Schema.bounded_iff_frequency"
  },
  "answers_item": "61",
  "provenance": {
    "generator": "maintainer's round 2026-11-07-score-side-binding",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-07-score-side-binding/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-07-score-side-binding/REPORT.md"
  },
  "note": "For a Schema (strength c; per instance, undefeated and the settled consequent), the liability DecisionComponent.liability realized held is bounded below by −B at every date iff c·U_n − T_n ≤ B at every date, U_n the undefeated count and T_n the true consequents among them (outperformance_eq). An instance of bounded_iff_not_outperformed; the reduction of WarrantForce's calibrated trade to a unit position per instance is the named hypothesis UnitPosition (solvent_iff). Witnesses: always_true_bounded, always_false_unbounded."
}
```

### solvency.conflict-names-suspects

```json
{
  "project": "normativity",
  "short_name": "a valid conflict certificate shows at every cube point some positively weighted bundle row violated there, so rows all valid at one point cannot conflict",
  "origin_round": "2026-11-07-score-side-binding",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.WarrantSolvency.suspect_in_bundle"
  },
  "answers_item": "133",
  "provenance": {
    "generator": "maintainer's round 2026-11-07-score-side-binding",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-07-score-side-binding/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-07-score-side-binding/REPORT.md"
  },
  "note": "In the generality of NormativeInductorComposition.FarkasCert: at every price vector some positively weighted row is violated (exists_violated_suspect); against a bundle whose rows the certificate may weight, at every cube point some positively weighted row of the bundle itself is violated there (the cube rows hold in the cube) — the violated row may differ from point to point; no single row is shown violated everywhere. Hence if every weighted row is valid at a point no valid conflict certificate exists (no_conflict_of_sound), and when all suspects but one hold at a point the remaining one is violated there (unique_suspect). Reading a conflict as a mis-admission needs the further premise that admission demands validity at the point in question; the theorem does not supply it. Also stated on a NormState (suspect_in_normState)."
}
```

### robust.eight-world-strengths

```json
{
  "project": "normativity",
  "short_name": "on the eight-world model the robust strength of the signal's warrant is 3/5 over the undefeated extensions, and 3/4 with the contrary challenge a defeater",
  "origin_round": "2026-11-07-score-side-binding",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.RobustWarrant.robustStrength_both"
  },
  "answers_item": "133",
  "provenance": {
    "generator": "maintainer's round 2026-11-07-score-side-binding",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-07-score-side-binding/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-07-score-side-binding/REPORT.md"
  },
  "note": "The model (a binary quantity, a signal of accuracy 3/4, a challenge of accuracy 2/3, independent given the quantity) is stated locally with exact rationals. The strength row at 3/4 is valid at the record with the signal alone (valid_at_signal, Pr(Y | A) = 3/4) and invalid at the record with the contrary challenge (invalid_at_contrary, Pr(Y | A ∧ C) = 3/5); embedded in a three-coordinate fragment, settleOutcome keeps the form, the quiet docket undercuts nothing, and the repository's grounded survivor rule Grounds.survivors applied to the warrant's grounds at that record keeps it (kept_under_challenge, not_undercut, survives_challenge), while the contributed row is violated by her posterior (contributed_row_invalid); the opposing warrant at 2/3 makes the rows infeasible (naive_conflict). The robust reading Robust (a constraint over a declared set of undefeated extensions) is sound (robust_sound); the statement of record robustStrength_both conjoins robustStrength_all (3/5 over the three extensions) and robustStrength_defeated (3/4 with the contrary challenge a defeater); the extension sets Uall and Udef are declared inputs, not derived from any defeat mechanism. The opposing warrant's strength is 2/5 and the robust rows meet at 3/5 (against_robust_iff, robust_meet)."
}
```

### standing.reallocated-entitles-nothing

```json
{
  "project": "normativity",
  "short_name": "admission by standing: with Protocol.Admitted read off the authority allocation, a reallocated obligation entitles nothing",
  "origin_round": "2026-11-07-score-side-binding",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.AdmissionByStanding.reallocated_entitles_nothing"
  },
  "answers_item": "128",
  "provenance": {
    "generator": "maintainer's round 2026-11-07-score-side-binding",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-07-score-side-binding/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-07-score-side-binding/REPORT.md"
  },
  "note": "admittedByStanding: an obligation occurrence is admitted at history h when its issuer holds its matter under the allocation current at h; first-person commitments are matters the reasoner holds itself. The witness's state₀ rebuilt over the protocol with standing under J₀ (the first obligation the principal's, the second the reasoner's own) inhabits Entitlement for the witness's grounds at every date with admission carrying content (entitlementS, admitted_by_allocation, first_person_admitted). Under J₁, the allocation moving the first matter to the agent, the first obligation is not admitted at any history (reallocated_not_admitted) and no entitlement over any obligation state of that protocol may trace an occurrence to it — the counterpart of answered_not_entitled with the account replaced by the allocation. The hypothesis package is inhabited: over protocolS₁ an Initial can expose only obligation 1 (Initial admits every exposed occurrence, and obligation 0 is admitted at no history), and entitlementS₁ over stateS₁ — every origin at obligation 1, admitted under J₁, account live, Expresses total — is the witness (witness_origin: its conclusion there reads 1 ≠ 0). Expresses remains typed."
}
```

### rows.incompatibility-entailment

```json
{
  "project": "normativity",
  "short_name": "on the rational row language incompatibility entailment coincides with certificate entailment, relative to the cube and with no nonemptiness hypothesis",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.IncompatibilitySemantics.incEntails_iff_certEntails"
  },
  "answers_item": "118",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "Incompatible L is a FarkasCert over L's rows and the cube rows, a valid conflict result of the compiler (incompatible_iff_conflict), and holds iff L has no cube point (incompatible_iff_not_feasible: soundness farkas_sound, completeness the rational alternative RowAlternative.alternative, read in from the pinned EconCSLib theorem_of_alternative). CertEntails is an EntailCert over allowed rows; a BoundCert is the case of a row s·x φ ≤ v (ofBoundCert, toBoundCert). Both notions equal validity on the cube points of the list (incEntails_iff_sem, certEntails_iff_sem); against an infeasible list a scaled conflict certificate added to a cube certificate derives every row (certEntails_of_incompatible), so no nonemptiness hypothesis is needed. Restricted to contexts of leverage forms of strength at most one the relation is total, because the all-ones point satisfies every such form (humble_forms_feasible, formIncEntails_total, form_role_needs_rows)."
}
```

### seed.bound-certified

```json
{
  "project": "normativity",
  "short_name": "every valid lower bound on a forced region has a bound certificate over the forced bundle's allowed rows",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.IncompatibilitySemantics.lowerBound_certified"
  },
  "answers_item": "118",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "For LowerBound S W st F φ c there are m and cert : BoundCert d m φ (-1) with every row allowed against forcedBundle S W st F and c ≤ −cert.value; the upper-bound form is upperBound_certified. Through certEntails_iff_sem. No nonemptiness of the region is assumed: against an empty region every bound is certified. The hypothesis is inhabited by lowerBound_witness (the bound 1/2 on SeedStatics.widenSeed). Item 118's second theorem."
}
```

### seed.forced-interval-rational

```json
{
  "project": "normativity",
  "short_name": "the forced interval computed by elimination inhabits the rational predicate: its endpoints are valid bounds attained at rational points",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.IncompatibilitySemantics.forcedInterval_isForcedInterval"
  },
  "answers_item": "118",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "IsForcedInterval S W st F φ (forcedInterval S W st F φ).1 (forcedInterval S W st F φ).2 under ∃ x, forcedRegionR S W st F x. From SeedStatics.forcedInterval_spec (attainment at real points) and exists_rat_point_at, which rests on RowAlternative.exists_rat_of_real: a rational system feasible over ℝ is feasible over ℚ. The hypothesis is inhabited by forcedInterval_witness (widenSeed). Item 118's first theorem."
}
```

### expresses.kept-row-demands-no-more

```json
{
  "project": "normativity",
  "short_name": "the strength row the rebuttal rule keeps demands no more than a robust warrant of at least its strength whose undefeated extensions include every record the rule keeps it at",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.ExpressesByRole.settled_demandsNoMore"
  },
  "answers_item": "128",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "A Requirement (events A, Y, strength c, undefeated extensions U) denotes its models, the nonnegative measures satisfying RobustWarrant.Robust. A form is a content — rows per record — under the plain rule or the settled rule (settleOutcome). DemandsNoMore: every list of rows incompatible with the content at a record is incompatible with the requirement there, equivalently every model satisfies the content's rows at every record of positive mass (demandsNoMore_iff, by completeness of conflicts). Hypotheses: c' ≤ w.c, ι XA = w.A, ι XAY = w.A ∩ w.Y, and every kept record's event in w.U; inhabited by settled_expresses on the eight-world fragment (A, A∧Y, C) with U the kept extensions. Necessity: stronger_not_expresses (the strength), defeater_not_expressed (the extensions). The interpretation ι and U are declared. The same-role strength (SameRole) is defined, refuted for a weaker row (weaker_noMore_not_same), and not proved for the exact row."
}
```

### expresses.entitlement-discriminates

```json
{
  "project": "normativity",
  "short_name": "an entitlement whose Expresses carries content: over one accounted state the kept row at 3/5 is entitled, the plain row is not, and the row at 3/4 is not",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.ExpressesByRole.entitlement_discriminates"
  },
  "answers_item": "128",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "stateW is two obligations over the protocol with admission by standing under J₀, anchored at the requirement at 3/5 over the kept extensions and at the requirement at 3/4 with the contrary challenge a declared defeater. entitlementW inhabits Entitlement stateW [occ35] (ExpressesNoMore ι settled). The plain row demands more at the record settling the consequent false, where it reads 3/5·P(A) ≤ 0 and the eight-world measure, a model of the requirement, prices A at 1/5 (plain_not_expresses; the conflict contraCert in contraposition_as_expression). The row at 3/4 is too strong for the first anchor and, against the second, is kept by the rebuttal rule at the contrary-challenge record where the measure violates it (defeater_not_expressed). The first fixture in which entitlement fails for a reason other than a dead account or a reallocated matter. Item 128, clause (a), the Expresses half; clauses (b) and (c) are untouched."
}
```

### expresses.plain-row-demands-more

```json
{
  "project": "normativity",
  "short_name": "the plain linear strength row demands more than a robust warrant wherever a model gives the antecedent positive posterior at a record settling the consequent false",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.ExpressesByRole.plain_demandsMore"
  },
  "answers_item": "113",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "Item 113's phenomenon as a statement about expression: at a record pinning the consequent false the specialized strength row forces the antecedent to zero (WarrantEntitlement.strength_contraposes), while a model of the requirement may price it positively. Hypotheses: 0 < c, a model μ, a settlement pinning XAY false, positive record mass, positive antecedent mass on the record; inhabited by plain_not_expresses (record mass 5/8, antecedent mass 1/8). Beside it models_null_at_rebuttal: a model of a requirement of positive strength gives the antecedent mass zero on any undefeated extension on which the consequent is false."
}
```

### content.conservative-iff-image

```json
{
  "project": "normativity",
  "short_name": "a vocabulary change is conservative on the old fragment iff the image of the new region equals the old region",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.Conservativity.conservative_iff"
  },
  "answers_item": "134",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "Refines: the pullback of every row the old region forces is forced by the new; AddsNothing: every old row whose pullback the new region forces was forced by the old; Conservative: both. refines_iff: refinement iff the image lies in the old region. addsNothing_iff: adding nothing iff the old region lies in the image, by separating_row and the rational alternative (RowAlternative.alternative_family). A coordinate map is the 0/1 translation, its image the projection; injectivity is unused. The extension of a seed along a coordinate map by new items always refines (extend_refines). Fixtures: ext₁ conservative; ext₂, a new term whose introduction row P(T) ≥ 4/5·P(X) and elimination row P(Y) ≥ 3/4·P(T) force P(Y) ≥ 3/10 over P(X) ≥ 1/2, with the certificate badCert, refines and is not conservative (bad_not_conservative), and is conservative with the elimination port defeated. SeedStatics.seed_independence_strict is conservativity on pins only (strict_layer_adds_no_pin, strict_layer_adds_rows)."
}
```

### precedent.rationalizable-iff-acyclic

```json
{
  "project": "normativity",
  "short_name": "a case base read off the record is rationalized by one strict order on reasons iff the graph on its cases has no cycle",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.PrecedentConstraint.rationalizable_iff_acyclic"
  },
  "answers_item": "117",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "A reason is a leverage form, its kind the form with the strength erased; V covers W when each form of W has a form of V of its kind and at least its strength. A Case is read off the record by caseOf: survivors' forms prevailed and every undercut occurrence's form was outweighed, whatever the settlement. A case says that anything covering its winners beats anything its losers cover; Rationalizable Γ is the existence of an irreflexive transitive relation on reason sets containing every case's decision, equivalently no cycle of dominance (rationalizable_iff_no_dominance_cycle), equivalently no cycle in the graph Next on cases; a rank increasing along the edges suffices (rationalizable_of_rank). The pairwise condition Consistent (consistent_iff_pairwise) is necessary and not sufficient: three cases in a cycle pass it and have no order (cycle_not_rationalizable). Permitted Γ c is Rationalizable (c :: Γ), antitone in Γ. Fixtures on (X, ¬X, D): a forbidden continuation, two permitted by distinguishing (a ground of a new kind; a greater opposing strength), and a situation in which both decisions are permitted and not jointly (both_permitted) — the constraint allows and does not rank. The reading of undercut as outweighed is the model's; the record carries no decision object. The attribution of the reason model to its author is unverified, and the model has no sides: any reason set may be compared with any other."
}
```

### precedent.permitted-iff-reach

```json
{
  "project": "normativity",
  "short_name": "a continuation is permitted by a case base iff the base is rationalizable and the reach of its holding does not put the continuation's losers at or above its winners",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.PrecedentHolding.permitted_iff"
  },
  "answers_item": "117",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "Holding Γ is the transitive closure of PrecedentConstraint.Dominates Γ on reason sets; Reach Γ V U is Covers V U ∨ Holding Γ V U, a preorder. The holding of c :: Γ is computed from the holding of Γ and c alone (holding_cons), so two case bases with the same holding permit the same continuations after any further continuations (permitted_congr, permitted_append_congr): the cases may be forgotten and the holding kept. Among rationalizable bases the reach is exactly what permission reads (permission_eq_iff_reach_eq); the holding is finer — a case whose winners cover its losers enters the holding and leaves the reach unchanged (holding_not_minimal). Restricted to a set R of reason sets containing every continuation's winners and losers, the reach on R × R with the rationalizability bit is closed under continuation (agreeOn_cons), and for finite R it is eventually constant along any sequence of continuations (reachSet_eventually_const, permission_eventually_const). A finite set Φ of forms supplies such an R: a reason set drawn from Φ covers and is covered by its list of distinct forms (normal, covers_normal), of which there are at most 2^|Φ| (reasonSets, card_reasonSets_le), and the holding does not distinguish reason sets that cover each other (holding_congr_covers), so the holding on all reason sets drawn from Φ and permission for every continuation drawn from Φ are eventually constant along any sequence of continuations (holding_eventually_const_of_finite_forms, permission_eventually_const_of_finite_forms); nothing bounds the stage at which they stop changing. The union of two case bases is rationalizable iff the union of their holdings has no cycle (rationalizable_append_iff), with two merged-discord fixtures. No hypotheses; both sides occur (PrecedentConstraint.permitted_distinguished, forbidden_not_permitted)."
}
```

### precedent.staircase-irredundant

```json
{
  "project": "normativity",
  "short_name": "over one pair of kinds no case of a staircase of n cases at strictly increasing strengths is redundant: the reverse decision at the i-th strength is forbidden by the staircase and permitted without its i-th case",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.PrecedentHolding.staircase_irredundant"
  },
  "answers_item": "117",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "staircase s n is the cases ⟨[premise 0 (s j)], [premise 1 (s j)]⟩ for j < n. For strictly increasing s and i < n, ¬ Permitted (staircase s n) (against s i) and Permitted ((staircase s n).filter (· ≠ step s i)) (against s i), the second by a rank on cases. Beside it, stairs_permitted_iff (the reverse decision at s i is permitted by the staircase at the steps l iff i ∉ l) and stairs_holding_injective (two staircases over one scale with the same holding have the same steps): so n strengths over one pair of kinds carry a different holding for each set of steps, 2^n of them, and the kinds of reasons alone give no finite representation; the count is read off the injectivity and not formalized. The statement of record says each case is needed under deletion and nothing about other generators of the same holding. The hypotheses are inhabited within strengths in (0,1) by humbleScale (humbleScale_spec) and staircase_witness."
}
```

### precedent.assessor-sets-precedent

```json
{
  "project": "normativity",
  "short_name": "with the case of an assessed act set by the assessor's verdict, a later choice is forbidden by an act assessed a shortfall and would be permitted had the act itself set the precedent",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.AssessedConduct.assessor_sets_precedent"
  },
  "answers_item": "117",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "An AssessedAct carries the grounds the act was taken on, the surviving grounds against it and a Verdict; its proposal is ⟨grounds, against⟩ and its case is the proposal if assessed adequate and the reverse if assessed a shortfall. ofCertificate is the adapter from DecisionComponent.ActCertificate at Ent := Form d: the grounds against and the verdict are further inputs, the licence and lineage are not read. ConsistentConduct: each choice permitted by the case base of the assessed acts before it, i.e. by the reach of the assessed past (consistentConduct_cons_iff). The fixture: the act on P(X) ≥ 3/4 against P(¬X) ≥ 1/2 assessed a shortfall; the later choice on P(X) ≥ 7/10 against P(¬X) ≥ 3/5 (repeat_forbidden); a later choice with a ground of a new kind is permitted (distinguished_consistent). Where a choice and its reverse are both permitted the reach relates their reason sets in neither direction (permitted_both_silent), and a shortfall verdict on a choice the reach backs leaves the assessed case base unrationalizable (shortfall_of_backed_not_rationalizable, assessor_bound). A closed statement about the fixture, for every verdict on the later choice. Nothing ties the verdict to WarrantInductorScoreSide.Assessed."
}
```

### content.forget-region-is-projection

```json
{
  "project": "normativity",
  "short_name": "Fourier–Motzkin elimination of a coordinate computes the projection of a bundle's region along the coordinate map that drops it, at rational points",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.Forgetting.forget_region"
  },
  "answers_item": "134",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "eliminate k L is FourierMotzkin.elim — the step SeedStatics.project iterates — on the rows with coordinate k moved last, read back as rows; forget k B applies it to the bundle's rows and the cube rows. eliminate_sat_iff: the eliminated rows hold at a rational x iff x is the restriction along k.succAbove of a rational solution, the rational point by RowAlternative.exists_rat_of_real. Consequences: a row over the retained coordinates is forced by the full bundle iff by the forgotten one (forget_exact), certified against one iff against the other (forget_certified), and the change is conservative (forget_conservative); SeedStatics.project on a bundle's system is the projection onto one coordinate (project_iff_projection); projections compose (projection_comp). Adding nothing along a one-coordinate extension is then a finite family of entailment certificates (VocabularyAct.addsNothing_certified). No hypotheses. Item 134, clause (d), for one coordinate; the certificate search and several coordinates at once are not assembled into a decision procedure."
}
```

### content.forget-settled

```json
{
  "project": "normativity",
  "short_name": "a settled coordinate may be forgotten: the rows specialized at its settlement and restricted to the other coordinates give the projection of the forced region under every docket state and every later settlement",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.Forgetting.forget_settled"
  },
  "answers_item": "134",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "For F.val k = some b and F.le F': projection k.succAbove (forcedRegion S W st F') x iff x is in the cube, pinned by F' restricted to the other coordinates, and satisfies dropCoord k (specialize F r) for the row r of every substantive item live at st and every warrant, and of every structural item live at st. The right side reads the seed's and the warrants' rows — selected by the docket state queried, so every item's row is retained and not only the items live when k is forgotten — with their ports and ids, and the later settlement on the retained coordinates. The hypotheses are inhabited by forget_settled_witness (X settled true in liveSeed). Its counterpart: an account with no live port denotes one resolution and every later substitution leaves its receipts and its denotation unchanged (OccurrenceIntegrity.Program.closed_evaluate_const, closed_subst), which is what OpenIntegrityEvolution.Conservation reads of it."
}
```

### content.licensed-no-challenge

```json
{
  "project": "normativity",
  "short_name": "a vocabulary change licensed by a refinement certificate on its declared protected fragment admits no valid challenge on that fragment",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.VocabularyAct.licensed_no_challenge"
  },
  "answers_item": "134",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "VocabularyChange carries owner, T, old, new, fragment; it is data on rows and not a step of the accounted state. Licensed V: for every row allowed against the fragment, CertEntails V.new (pull V.T p); it holds iff the change refines the fragment (licensed_iff_refines), and reads neither old nor owner. A Challenge is a row, an EntailCert of it and a point; Challenge.Valid — the certificate's rows allowed against a list Γ of old rows, the point a cube point of the new commitments, the pullback failing there — is decidable. A valid challenge is a broken commitment and every broken commitment has one (Challenge.sound, challenge_complete); an unlicensed change admits a valid challenge on the fragment (unlicensed_has_challenge). FragmentOfOld V — every protected row has an entailment certificate against the old commitments — ties the fragment to them, and under it a valid challenge on the fragment is a broken commitment of the old (challenge_on_fragment_breaks_old). The hypothesis is inhabited by split_licensed (the split change protecting the credence rows, which satisfy FragmentOfOld by split_fragmentOfOld), and splitChallenge_valid shows a commitment outside the fragment validly challenged. Who may issue a change is not determined: the authority module allocates matters to holders and names none for vocabulary. Three readings of a broken commitment (Bars, Accounted, Split) are predicates beside it, each a function of the commitment's Charge (readings_of_charge); none is adopted."
}
```

### memory.live-forget-cost

```json
{
  "project": "normativity",
  "short_name": "forgetting an unsettled coordinate costs the later forced interval: over P(Y) ≥ 3/4·P(X), forgetting X before it settles leaves P(Y) the whole of [0,1] where the full record forces [3/4,1] once X settles true, and forgetting X after it settles keeps P(Y) ≥ 3/4",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.Forgetting.live_forget_cost"
  },
  "answers_item": "135",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "liveSeed is the seed over (X, Y) with the one item Form.strength 0 1 (3/4). Three conjuncts: the projection of the forced region under the empty settlement along the map dropping X is the cube on Y — exact at the time, by content.forget-region-is-projection; IsForcedInterval liveSeed [] quiet settledX 1 (3/4) 1; and the projection of the forced region under settledX is {x | InCube x ∧ 3/4 ≤ x 0}. A closed statement about the fixture. The loss is 3/4 at the lower endpoint and is not visible as slack at the time of forgetting."
}
```

### memory.schedule-slack

```json
{
  "project": "normativity",
  "short_name": "along a schedule of forgetting steps each agreeing with a reference step off a set of worlds, a row's excess exceeds its excess under the reference schedule by at most its oscillation times the accumulated mass on those sets",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.Forgetting.schedule_slack"
  },
  "answers_item": "135",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "K t, K₀ t : Recollection (n (t+1)) (n t) retell the stage-t worlds as the stage-(t+1) worlds, the schedule and a reference schedule of which nothing is assumed; the reference is exact forgetting when its steps are maps of worlds. chain K T composes them; scheduleLoss K B q T is the sum over t < T of the mass (chain K t).push q places on B t. Hypotheses: K t and K₀ t agree off B t, q nonnegative, the row's coefficients in [lo, hi]. By induction from Recollection.approx_step and retold_bounds. Where the stage masses are bounded by a sequence with bounded partial sums, or a summable one, the loss is bounded uniformly in the number of stages (schedule_bounded, schedule_summable). The hypotheses are inhabited by schedule_slack_witness. The loss measured is a row's excess at world-distribution level, compared between two stochastic schedules; no defect measure of the program's is transported, and the cost of forgetting an unsettled coordinate (memory.live-forget-cost) is not of this form."
}
```

### memory.selective-forgetting

```json
{
  "project": "normativity",
  "short_name": "choosing which coordinate to drop after seeing the record obtains the interval [0,1] on both of two records where each coordinate fixed in advance leaves [3/4,1] on one of them and the full record forces [3/4,1] on both",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.Forgetting.selective_forgetting"
  },
  "answers_item": "135",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "recOn a is the seed over (φ, A, B) with the one item P(φ) ≥ 3/4 · P(a); afterForget a k F'' is the projection of its forced region along the map dropping k, pinned by the later settlement on the two retained coordinates (later, the restriction of bothTrue by later_eq). Six conjuncts: IsInterval for the choice made after seeing the record on both records (0, 1), for each fixed coordinate on the record it misses (3/4, 1), and IsForcedInterval for the full record on both (3/4, 1). A closed statement about the fixture. The choices fixed in advance are choices of a coordinate; a rule fixed in advance that names the coordinate by its role reproduces the adaptive result, and no theorem compares classes of policies. The gain, 3/4 at the lower endpoint, has the form of the non-capture rounds' omission bound (ReasonSupply.adverse_union) read with one omitted row's adverse sensitivity; the instantiation is not made in Lean, and that result does not separate a fixed from an adaptive choice."
}
```

### seed.adapter-certificates-exist

```json
{
  "project": "normativity",
  "short_name": "every valid upper bound on a rational functional over a bundle's region has a cited functional certificate of at most that value",
  "origin_round": "2026-11-08-content-recollection",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Normativity.Contrib.AdapterCertificates.exists_citedFunctional"
  },
  "answers_item": "118",
  "provenance": {
    "generator": "maintainer's round 2026-11-08-content-recollection",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md",
    "context": "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"
  },
  "note": "From IncompatibilitySemantics.certEntails_iff_sem, with a citation chosen for each weighted row. Consequences for WarrantInductor.Problem: where every inadequate response scores at most a rational t ≤ τ at every point of the region, upper certificates making Excludes hold exist (excludes_of_region); where every margin witness scores at least a rational t ≥ τ + δ, lower certificates making Margins hold at tolerance 0 exist (margins_of_region). Not derived: a threshold with no rational between it and the region's supremum, and Margins at a positive tolerance, where the tolerance multiplies the certificate's mass. The hypothesis is inhabited by citedFunctional_witness (SeedStatics.widenSeed)."
}
```
