# Claims registry — deference

**Specification layer.** Every entry's *statement of record* is a fully-qualified
Lean declaration, never prose. The class is part of the claim; a class change is a
diff to this file and therefore a maintainer act. See `AGENTS.md`.

Schema: `### <id>` followed by one fenced `json` block with `class`,
`statement_of_record`, `answers_item`, `provenance`, and `docs`.

## What is here, and what is not

Every entry is a theorem its round's report presents as a result, and every one is
kernel-checked, sorry-free, and audits to the three allowed axioms. Four bodies of
work in `lean/Workspace/Deference/Contrib/` are deliberately absent, and the reasons
are the rounds' own:

- **`FaithfulAcceleration.weight_not_divergent` and
  `MagnitudePrediction.squaredError_bdd_of_sharpness_bdd`** ship no term inhabiting
  their full hypothesis package — each carries an undischarged
  `EfficientlyComputable` certificate — so neither can be promoted to the record.
  They are labelled `unverified-nonvacuous` where they live.
- **The inherited transcriptions** in `InheritedAlgebra.lean` and the Layer-1 half
  of `FaithfulAcceleration.lean` restate declarations of another body of work. That
  they re-elaborate here is a real result about the port, and it is not this
  repository establishing them.
- **`EnvelopeDominance.lean`** proves what its name says and not what its round
  wanted: its maximiser is built from the evaluating agent's own credence, so it
  represents no distinct future agent, and its dominance statement is
  `sum of maxima >= sum of anything`. The round records this as its central defect.
- **`CartesianFrameBridge.lean`** states its results over a mirrored fragment of an
  upstream library at a commit this repository does not pin, under an `Iso` weaker
  than the authoritative one. Registering it would register statements about the
  copy. `PRIORITIES.md` item 52 is to import the real definitions and delete the
  mirror; registration belongs after that.

The refutations in `ReachableCorrectiveControl` **are** registered. A theorem that
breaks its own round's protection claims is a result, and the strongest thing that
round produced.

---

## Registered claims

### delegation.bridge

```json
{
  "project": "deference",
  "short_name": "the finite delegation bridge",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.DelegationBridge.delegation_bridge"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-finite-kernel/REPORT.md"
  },
  "note": "The local form under a named GradeTrust hypothesis. The uniform `2M` form was deliberately not ported: it rests on the grade-to-quantity link the programme decided to derive rather than assume."
}
```

### delegation.bridge-unconditional

```json
{
  "project": "deference",
  "short_name": "the delegation bridge without its trust hypothesis",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.DelegationBridge.delegation_bridge_unconditional"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-finite-kernel/REPORT.md"
  },
  "note": "The corollary that drops the hypothesis where the refinement supplies it."
}
```

### delegation.gradetrust-refinement

```json
{
  "project": "deference",
  "short_name": "refinement gives grade trust",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.DelegationBridge.gradeTrust_of_refinement"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-finite-kernel/REPORT.md"
  },
  "note": "The second corollary of the bridge."
}
```

### certificate.margin-forces-agreement

```json
{
  "project": "deference",
  "short_name": "a margin forces agreement",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.CertificateBounds.margin_forces_agreement"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-certificates/REPORT.md"
  },
  "note": "Wave-1 L1. Finite, order- and arithmetic-only, with a constructed inhabitation witness."
}
```

### certificate.selection-eq-of-margin

```json
{
  "project": "deference",
  "short_name": "the selection is determined by the margin",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.CertificateBounds.selection_eq_of_margin"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-certificates/REPORT.md"
  },
  "note": "Wave-1 L1, the equality form."
}
```

### certificate.override-bound

```json
{
  "project": "deference",
  "short_name": "the override bound",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.CertificateBounds.override_bound"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-certificates/REPORT.md"
  },
  "note": "Wave-1 L2."
}
```

### certificate.defect-bound

```json
{
  "project": "deference",
  "short_name": "the defect bound",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.CertificateBounds.defect_bound"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-certificates/REPORT.md"
  },
  "note": "Wave-1 L3."
}
```

### certificate.advantage-estimate

```json
{
  "project": "deference",
  "short_name": "the advantage estimate",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.CertificateBounds.advantage_estimate"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-certificates/REPORT.md"
  },
  "note": "Wave-1 L7."
}
```

### certificate.grade-register-strict

```json
{
  "project": "deference",
  "short_name": "the strict grade-register theorem",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.CertificateBounds.gradeRegister_strict"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-certificates/REPORT.md"
  },
  "note": "Wave-1 Theorem C'. Theorem C's V-register comparator clause is deliberately absent, resting on the movement hypothesis the phase exists to replace."
}
```

### exposure.greedy-duality

```json
{
  "project": "deference",
  "short_name": "piercing duality for the greedy selection",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ExposureGeometry.greedy_duality"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-densification/REPORT.md"
  },
  "note": "Wave-1 Lemma 1."
}
```

### exposure.harvest-bound

```json
{
  "project": "deference",
  "short_name": "the exposure-harvest bound",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ExposureGeometry.exposure_harvest_bound"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-densification/REPORT.md"
  },
  "note": "Wave-1 Theorem 2."
}
```

### exposure.harvest-attained

```json
{
  "project": "deference",
  "short_name": "the exposure-harvest bound is attained",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ExposureGeometry.exposure_harvest_attained"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-densification/REPORT.md"
  },
  "note": "Sharpness: the bound is not merely an upper bound."
}
```

### substitution.extensional-admits-both

```json
{
  "project": "deference",
  "short_name": "extensional data admits delegation and simulation alike",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.SubstitutionSeparation.extensional_admits_both"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-channel/REPORT.md"
  },
  "note": "Wave-1 Proposition 1. One of the four establishing that valuation data cannot separate delegation from an accurate simulator."
}
```

### substitution.sim-depends-on-induced-choice

```json
{
  "project": "deference",
  "short_name": "simulation reads only the induced choice",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.SubstitutionSeparation.sim_depends_only_on_inducedChoice"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-channel/REPORT.md"
  },
  "note": "Wave-1 Proposition 2."
}
```

### substitution.separation-requires-disagreement

```json
{
  "project": "deference",
  "short_name": "separation requires disagreement",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.SubstitutionSeparation.separation_requires_disagreement"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-channel/REPORT.md"
  },
  "note": "Wave-1 Proposition 6."
}
```

### substitution.unpredictability-separates

```json
{
  "project": "deference",
  "short_name": "unpredictability separates the two conducts",
  "origin_round": "2026-08-11-phase-ii-promotion",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.SubstitutionSeparation.unpredictability_separates"
  },
  "answers_item": "23",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-promotion",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-promotion/REPORT.md",
    "context": "prompts/2026-08-11-deference-channel/REPORT.md"
  },
  "note": "Wave-1 Proposition 7. The separation is not inferable from a run; this states the condition under which it exists at all."
}
```

### magnitude.unit-trader-networth

```json
{
  "project": "deference",
  "short_name": "the signed error sum is exactly a trader payoff",
  "origin_round": "2026-08-11-phase-ii-prediction",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.MagnitudePrediction.unitTrader_netWorth_eq"
  },
  "answers_item": "21",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-prediction",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-prediction/REPORT.md",
    "context": "prompts/2026-08-11-phase-ii-prediction/REPORT.md"
  },
  "note": "No remainder term: the criterion has an instrument for the signed functional."
}
```

### magnitude.signed-bounded

```json
{
  "project": "deference",
  "short_name": "the signed sum cannot be bounded below and unbounded above",
  "origin_round": "2026-08-11-phase-ii-prediction",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.MagnitudePrediction.signed_bddAbove_of_bddBelow"
  },
  "answers_item": "21",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-prediction",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-prediction/REPORT.md",
    "context": "prompts/2026-08-11-phase-ii-prediction/REPORT.md"
  },
  "note": "Ordinary Logical Induction gives signed calibration, under the emission certificate."
}
```

### magnitude.signed-bounded-actual

```json
{
  "project": "deference",
  "short_name": "the signed bound against the source's own criterion",
  "origin_round": "2026-08-11-stage-v-li-native",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.MagnitudePrediction.signed_bddAbove_of_bddBelow_rpn"
  },
  "answers_item": "21",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-stage-v-li-native",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-stage-v-li-native/REPORT.md",
    "context": "prompts/2026-08-11-stage-v-li-native/REPORT.md"
  },
  "note": "Stage V's form: invokes the pinned dependency's own no-exploitation theorem and retains only the substantive bounded-downside premise, which the constant-tautology declarations inhabit."
}
```

### magnitude.mixture-networth-zero

```json
{
  "project": "deference",
  "short_name": "every trader averages to zero over a coherent mixture",
  "origin_round": "2026-08-11-phase-ii-prediction",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.MagnitudePrediction.CoherentMixture.netWorth_eq_zero"
  },
  "answers_item": "21",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-prediction",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-prediction/REPORT.md",
    "context": "prompts/2026-08-11-phase-ii-prediction/REPORT.md"
  },
  "note": "No hypothesis on the trader — not on efficiency, rank, or what it reads. This is the mechanism behind the impossibility below."
}
```

### magnitude.not-trader-payoff

```json
{
  "project": "deference",
  "short_name": "the magnitude functional is not a trader payoff",
  "origin_round": "2026-08-11-phase-ii-prediction",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.MagnitudePrediction.magnitude_not_traderPayoff"
  },
  "answers_item": "21",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-prediction",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-prediction/REPORT.md",
    "context": "prompts/2026-08-11-phase-ii-prediction/REPORT.md"
  },
  "note": "An impossibility, and intrinsic to cash settlement rather than to the feature grammar: net worth is affine in the payout vector and the absolute value is not. This is why the magnitude target is retired."
}
```

### magnitude.sq-error-split

```json
{
  "project": "deference",
  "short_name": "the exact squared-error split",
  "origin_round": "2026-08-11-phase-ii-prediction",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.MagnitudePrediction.sq_error_split"
  },
  "answers_item": "21",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-prediction",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-prediction/REPORT.md",
    "context": "prompts/2026-08-11-phase-ii-prediction/REPORT.md"
  },
  "note": "For binary settlement, exactly; `sq_error_le_of_mem_Icc` gives the inequality that survives the substitution."
}
```

### magnitude.sharp-trader-networth

```json
{
  "project": "deference",
  "short_name": "the squared-error sum splits into a payoff and a price term",
  "origin_round": "2026-08-11-phase-ii-prediction",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.MagnitudePrediction.sharpTrader_netWorth_eq"
  },
  "answers_item": "21",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-phase-ii-prediction",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-phase-ii-prediction/REPORT.md",
    "context": "prompts/2026-08-11-phase-ii-prediction/REPORT.md"
  },
  "note": "Exactly, in every world, on every day. The first summand is a trader payoff; the second is a function of the assessed agent's own prices."
}
```

### jurisdiction.value-eq-of-price-realization

```json
{
  "project": "deference",
  "short_name": "value is determined by price and realization",
  "origin_round": "2026-08-11-stage-v-li-native",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.StaticViewFactorization.value_eq_of_price_realization_eq"
  },
  "answers_item": "28",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-stage-v-li-native",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-stage-v-li-native/REPORT.md",
    "context": "prompts/2026-08-11-stage-v-li-native/REPORT.md"
  },
  "note": "The polymorphic factorization: a valuation whose only inputs are realization maps priced by one measure cannot see anything else."
}
```

### jurisdiction.static-view-eq

```json
{
  "project": "deference",
  "short_name": "the static view factors through price and realization",
  "origin_round": "2026-08-11-stage-v-li-native",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.StaticViewFactorization.staticView_eq"
  },
  "answers_item": "28",
  "provenance": {
    "generator": "maintainer's round 2026-08-11-stage-v-li-native",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-11-stage-v-li-native/REPORT.md",
    "context": "prompts/2026-08-11-stage-v-li-native/REPORT.md"
  },
  "note": "Item 28's conditional core. It does not establish unrestricted jurisdiction invisibility, and the worked architecture pair exhibits a toy jurisdiction label that differs while the static view agrees."
}
```

### corrective.can-correct-iff

```json
{
  "project": "deference",
  "short_name": "corrective capability characterised at the field level",
  "origin_round": "2026-08-12-reachable-corrective-control",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ReachableCorrectiveControl.canCorrect_iff"
  },
  "answers_item": "60",
  "provenance": {
    "generator": "maintainer's round 2026-08-12-reachable-corrective-control",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-12-reachable-corrective-control/REPORT.md",
    "context": "prompts/2026-08-12-reachable-corrective-control/REPORT.md"
  },
  "note": "A conclusion, not a definition: capability is defined by quantifying over the transition relation, and this characterises it by reading a state field."
}
```

### corrective.can-correct-future-iff

```json
{
  "project": "deference",
  "short_name": "reachable corrective capability characterised at the field level",
  "origin_round": "2026-08-12-reachable-corrective-control",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ReachableCorrectiveControl.canCorrectFuture_iff"
  },
  "answers_item": "60",
  "provenance": {
    "generator": "maintainer's round 2026-08-12-reachable-corrective-control",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-12-reachable-corrective-control/REPORT.md",
    "context": "prompts/2026-08-12-reachable-corrective-control/REPORT.md"
  },
  "note": "The time-indexed form."
}
```

### corrective.forecloses-iff

```json
{
  "project": "deference",
  "short_name": "foreclosure characterised at the field level",
  "origin_round": "2026-08-12-reachable-corrective-control",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ReachableCorrectiveControl.forecloses_iff"
  },
  "answers_item": "60",
  "provenance": {
    "generator": "maintainer's round 2026-08-12-reachable-corrective-control",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-12-reachable-corrective-control/REPORT.md",
    "context": "prompts/2026-08-12-reachable-corrective-control/REPORT.md"
  },
  "note": "The third characterisation."
}
```

### corrective.no-exclusive-effect

```json
{
  "project": "deference",
  "short_name": "the principal has no exclusive effect",
  "origin_round": "2026-08-12-reachable-corrective-control",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ReachableCorrectiveControl.principal_has_no_exclusive_effect"
  },
  "answers_item": "60",
  "provenance": {
    "generator": "maintainer's round 2026-08-12-reachable-corrective-control",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-12-reachable-corrective-control/REPORT.md",
    "context": "prompts/2026-08-12-reachable-corrective-control/REPORT.md"
  },
  "note": "A refutation the round proved against itself: the advisor reproduces the principal's entire successor state at every state, so the model has no protected coordinate."
}
```

### corrective.advisor-veto

```json
{
  "project": "deference",
  "short_name": "the advisor has a universal veto",
  "origin_round": "2026-08-12-reachable-corrective-control",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ReachableCorrectiveControl.advisor_has_a_universal_veto"
  },
  "answers_item": "60",
  "provenance": {
    "generator": "maintainer's round 2026-08-12-reachable-corrective-control",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-12-reachable-corrective-control/REPORT.md",
    "context": "prompts/2026-08-12-reachable-corrective-control/REPORT.md"
  },
  "note": "A refutation. Corrective capability quantifies the advisor existentially, so it is not a statement about the principal's control."
}
```

### corrective.capability-measures-cooperation

```json
{
  "project": "deference",
  "short_name": "reachable capability measures advisor cooperation",
  "origin_round": "2026-08-12-reachable-corrective-control",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ReachableCorrectiveControl.canCorrectFuture_measures_advisor_cooperation"
  },
  "answers_item": "60",
  "provenance": {
    "generator": "maintainer's round 2026-08-12-reachable-corrective-control",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "prompts/2026-08-12-reachable-corrective-control/REPORT.md",
    "context": "prompts/2026-08-12-reachable-corrective-control/REPORT.md"
  },
  "note": "A refutation, and the sharpest: it exhibits an advisor policy that destroys the capability at every horizon while the preservation predicate certifies it."
}
```

### authorship.mediation-by-reexecution

```json
{
  "project": "deference",
  "short_name": "reason mediation by construction under a committed, re-executed principal program",
  "origin_round": "2026-09-10-committed-principal-program",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.EvaluationEcosystem.reasonMediated_of_reexecution"
  },
  "answers_item": "87",
  "provenance": {
    "generator": "maintainer's round 2026-09-10-committed-principal-program",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-10-committed-principal-program/PRINCIPAL_PROGRAM.md",
    "context": "prompts/2026-09-10-committed-principal-program/REPORT.md"
  },
  "note": "Clause 2 of item 87 only, not the bill. For any frame over the ecosystem's logs, any audited class of activated continuations sharing the mandated program, and any policy, the committed payload factors through the trace at commitment with factor map `eval π_P`. Inhabited by `Instance.mediation_witness`: two continuations with equal traces and different logs, both activated. What it does not say: that the trace, the scope or the pair class are declared correctly, or that any log is authentic."
}
```

### kernel.box1-fidelity-versus-fully-updated-deference

```json
{
  "project": "deference",
  "short_name": "Box 1: the outcome scorer's margin for asking is at most 2r where nothing is left to learn, the fidelity scorer's at least ϖ − (D − c)",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Headline.box1_one_model"
  },
  "answers_item": "104",
  "provenance": {
    "generator": "maintainer's round 2026-09-27-corrigibility-kernel-phase2",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md",
    "context": "prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md"
  },
  "note": "One menu, two options; one estimate within `r` of the true value. Scoring outcomes only, on a world where the true values agree, the margin for asking is at most `2r`; scored on the fidelity score with acting a recognized violation, the margin is at least `ϖ − (D − b(ask))` for every estimate, price and credence; the identity's forecast term is at most `2r`. Inhabited by `HouseSale.box1`. What it does not say: that acting is recognized as a bypass (effect completeness, description faithfulness) or that the count is exact (count integrity)."
}
```

### kernel.box2-dominance

```json
{
  "project": "deference",
  "short_name": "Box 2, dominance: Q(𝔱π) ≥ Q(π) + (ϖ′ − (D′ − lo))·Pr(π violates) under every credence, for any corrigible objective; at the fidelity score the margin is ϖ − (D − w_lo)",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Headline.box2_dominance"
  },
  "answers_item": "104",
  "provenance": {
    "generator": "maintainer's round 2026-09-27-corrigibility-kernel-phase2",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md",
    "context": "prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md"
  },
  "note": "Where `π` does not violate, `𝔱π` agrees with it; where it does, `𝔱π`'s evaluation is at least the band's floor and `π` carries a violation. The margin is restated from the landed `ϖ − D` because the mediated branch may itself be compromised (ruling R5); `box2_optimal_faithful` gives credence-zero violation for optimal policies under the window condition; `box2_dominance_legitimate` is the landed case. Restated by the follow-up (2026-09-27, Part 1): `box2_dominance_corrigible` proves the same for any corrigible objective (`Headline.Corrigible`) at the margin `ϖ′ − (D′ − lo)`, and this statement of record is its instance at the fidelity score; Box 2 does not read her evaluation. Inhabited by the house-sale parameters."
}
```

### kernel.box2-mediation

```json
{
  "project": "deference",
  "short_name": "Box 2, mediation: 𝔱 on the allocation of authority is corrigible under effect completeness and delegation safety, and reproduces the approve branch",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Headline.box2_mediation_corrigible"
  },
  "answers_item": "104",
  "provenance": {
    "generator": "maintainer's round 2026-09-27-corrigibility-kernel-phase2",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md",
    "context": "prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md"
  },
  "note": "With `box2_mediation_approve_branch`: on approval `𝔱π` releases the latch with `π`'s task component up to the required report. Inhabited by `ProtectedAuthorityTheorem.Witness.corrigible_instance` on the two-state physics; the obstruction without delegation safety is `box2_delegated_cut`. What it does not say: anything about foreclosure's reach cone (EXT)."
}
```

### kernel.box2-finite-time

```json
{
  "project": "deference",
  "short_name": "Box 2, finite time: at every day of a logical inductor the violating option scores below D − ϖ < 0 and the compliant one at least 0, from the price range alone",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Headline.box2_finite_time"
  },
  "answers_item": "104",
  "provenance": {
    "generator": "maintainer's round 2026-09-27-corrigibility-kernel-phase2",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md",
    "context": "prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md"
  },
  "note": "With `box2_gate_finite_time`: consulting beats bypass at every day whatever the inductor believes about legitimacy, the window at the band's floor. Inhabited by the pinned inductor witnesses of the li-corrigibility round."
}
```

### kernel.box3-gap-exchange-rate

```json
{
  "project": "deference",
  "short_name": "Box 3: compromise risk p for gain g against safe V₀ is accepted iff p(V₀ + g − c) ≤ g, hence only if p ≤ g/(g + |w_hi|)",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Headline.box3_gap_exchange_rate"
  },
  "answers_item": "104",
  "provenance": {
    "generator": "maintainer's round 2026-09-27-corrigibility-kernel-phase2",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md",
    "context": "prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md"
  },
  "note": "The gap sets the threshold; the small-gap witness `box3_small_gap` forces it."
}
```

### kernel.box3-no-laundering

```json
{
  "project": "deference",
  "short_name": "Box 3: manipulate, disclose, have the period evaluated stays in the band below honest conduct",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Headline.box3_no_laundering"
  },
  "answers_item": "104",
  "provenance": {
    "generator": "maintainer's round 2026-09-27-corrigibility-kernel-phase2",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md",
    "context": "prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md"
  },
  "note": "Lower by `ϖ` per counted deviation."
}
```

### kernel.box3-no-incentive-to-compromise

```json
{
  "project": "deference",
  "short_name": "Box 3: every compromised outcome scores below every legitimate one; at equal value legitimacy is worth the gap",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Headline.box3_no_incentive_to_compromise"
  },
  "answers_item": "104",
  "provenance": {
    "generator": "maintainer's round 2026-09-27-corrigibility-kernel-phase2",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md",
    "context": "prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md"
  },
  "note": "The witnesses `box3_conditioning_fails` and `box3_sealed_no_incentive` show why the gate multiplies rather than conditions."
}
```

### kernel.box3-restoration

```json
{
  "project": "deference",
  "short_name": "Box 3: restoration returns a decision to her value; inside the band the agent prefers better outcomes and is indifferent at the floor; suppression loses",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Headline.box3_restoration"
  },
  "answers_item": "104",
  "provenance": {
    "generator": "maintainer's round 2026-09-27-corrigibility-kernel-phase2",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md",
    "context": "prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md"
  },
  "note": "With `box3_band_order` and `box3_suppression_loses` (the band's width below `ϖ`, the disclosure deadline at or before the settlement window's close). Inhabited by `HouseSale.box3_capture_reported_and_restored`."
}
```

### kernel.hierarchy-per-decision

```json
{
  "project": "deference",
  "short_name": "The hierarchy per decision: violation-free legitimate above violation-free compromised above any recognized violation",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Headline.hierarchy_per_decision"
  },
  "answers_item": "104",
  "provenance": {
    "generator": "maintainer's round 2026-09-27-corrigibility-kernel-phase2",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md",
    "context": "prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md"
  },
  "note": "Over any evaluation schedule, with `D − ϖ < w_lo`. Inhabited by `CorrigibilityKernel.Witness.hierarchy_instance` at the worked parameters."
}
```

### kernel.hierarchy-history

```json
{
  "project": "deference",
  "short_name": "The hierarchy per history under mean-of-evaluations, sum-of-counts aggregation; summed evaluations fail it",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Headline.history_hierarchy"
  },
  "answers_item": "104",
  "provenance": {
    "generator": "maintainer's round 2026-09-27-corrigibility-kernel-phase2",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md",
    "context": "prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md"
  },
  "note": "With `summed_counterexample`: `K·D − ϖ` beats `K·w_lo` once `K (D − w_lo) > ϖ`. Inhabited by the house-sale fixture (`test_history_hierarchy_and_summed_counterexample`)."
}
```

### kernel.subjective-exchange-rate

```json
{
  "project": "deference",
  "short_name": "Any option a maximizer of a corrigible objective prefers to asking carries no recognized violation and a priced probability of unfaithfulness at most (D′ − c)/ϖ′; at the fidelity score, (D − c)/ϖ",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Headline.subjective_exchange_rate"
  },
  "answers_item": "104",
  "provenance": {
    "generator": "maintainer's round 2026-09-27-corrigibility-kernel-phase2",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md",
    "context": "prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md"
  },
  "note": "With `subjective_exchange_rate_li` at every finite day of a logical inductor. Restated by the follow-up (2026-09-27, Part 1): `subjective_exchange_rate_corrigible` (= `Corrigible.exchange`) proves it for any corrigible objective; this statement of record is the fidelity-score form, which takes any bid. It does not read her evaluation. Inhabited by `HouseSale.exchange_rate_at_25` (`1/50` at `ϖ = 25`, `c = 1/2`)."
}
```

### kernel.extension-realized-rate

```json
{
  "project": "deference",
  "short_name": "The extension's interface theorem: avg π ≤ avg (D − c_k)/ϖ + ε̄ ((D − w)/ϖ + θ_hi) + (B(K) + M(K))/(ϖ Σ w_k)",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.KernelExtension.DecisionInterface.realized_rate"
  },
  "answers_item": "104",
  "provenance": {
    "generator": "maintainer's round 2026-09-27-corrigibility-kernel-phase2",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md",
    "context": "prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md"
  },
  "note": "For any chooser at the decision interface; with `maximizer_excludes` and `exploration_never_violates`. Restated by the follow-up (2026-09-27, Part 3): the exploration set's third clause is dropped, so the exploration term is the honest `ε̄ ((D − w)/ϖ + θ_hi)` (`lo = w` the range floor, `explore_range` the range fact) rather than `ε̄ θ_hi`; the clause survives as the variant `AboveAsking` with `rate_above_asking`, under which no-lock-in holds only for options estimated at least as good as asking (`above_asking_locks_in`, the fixture `src/exploration_lockin.py`). Inhabited by the BRIA realization `briaInterface`. What it does not say: that `B(K)` is `o(K)` — that is the realization's to discharge (BRIA's budget; unbiasedness from feedback, PAPER)."
}
```

### kernel.extension-bria-realization

```json
{
  "project": "deference",
  "short_name": "Continuation BRIA realizes the interface with no exploration and B(K) = ρ 𝒜_K, recovering the landed per-block bound",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.KernelExtension.bria_rate"
  },
  "answers_item": "104",
  "provenance": {
    "generator": "maintainer's round 2026-09-27-corrigibility-kernel-phase2",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md",
    "context": "prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md"
  },
  "note": "From `overestimation_le_allowance_opening` under the landed hypotheses (feasibility, consistency, inquiry on the menu, the conditional-expectation bound, the noise over all blocks). Follow-up (2026-09-27, Part 3): `briaInterface` takes the interface's range floor `w` as an idle parameter (no exploration steps); the statement of record is unchanged. Inhabited by the after-compromise round's auction fixtures."
}
```

### kernel.corrigible-fidelity-score

```json
{
  "project": "deference",
  "short_name": "The fidelity score is corrigible: known faithfulness beats known unfaithfulness by ϖ − (D − w) whatever the ordinary values, and risk is accepted only at (D − c)/ϖ",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Headline.fidelityScore_corrigible"
  },
  "answers_item": "104",
  "provenance": {
    "generator": "maintainer's round 2026-09-27-corrigibility-kernel-phase2, follow-up Part 1",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md",
    "context": "prompts/2026-09-27-corrigibility-kernel-phase2/FOLLOWUP.md"
  },
  "note": "`Headline.Corrigible U D′ lo ϖ′` is the preference property over recognized violations (window `D′ − ϖ′ < lo`; the known clause with the margin `ϖ′ − (D′ − lo)`; the risk clause at the exchange rate). The evaluation form `bid − ϖ n − ϖ p` at `D`, `w`, `ϖ` has it. What it does not say: that the ordinary term is her evaluation (`corrigible_not_aligned` shows it need not be)."
}
```

### kernel.corrigible-generic

```json
{
  "project": "deference",
  "short_name": "Any bounded objective O ∈ [0, D′] less ϖ′ per recognized violation and ϖ′ per unit of priced risk, with D′ − ϖ′ < lo ≤ 0, is corrigible",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Headline.generic_corrigible"
  },
  "answers_item": "104",
  "provenance": {
    "generator": "maintainer's round 2026-09-27-corrigibility-kernel-phase2, follow-up Part 1",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md",
    "context": "prompts/2026-09-27-corrigibility-kernel-phase2/FOLLOWUP.md"
  },
  "note": "From the authority-module round's generic lexical lemma (`generic_lexical_local`) with the risk term added. The class includes objectives whose ordinary term is not her evaluation: `corrigible_not_aligned` exhibits the landed misaligned fixture (`undisclosed_undominated`) as corrigible and ranking the uncounted manipulation above honest conduct. Corrigible is not aligned."
}
```
