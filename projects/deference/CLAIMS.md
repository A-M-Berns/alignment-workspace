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

### kernel.box2-mediation-faithful

```json
{
  "project": "deference",
  "short_name": "Box 2, mediation: 𝔱 on the allocation of authority is a faithful policy under effect completeness, delegation safety and allocation completeness wherever it forecloses nothing, and reproduces the approve branch",
  "origin_round": "2026-09-27-corrigibility-kernel-phase2",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Headline.box2_mediation_faithful"
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
  "note": "Formerly `kernel.box2-mediation`, statement of record `box2_mediation_corrigible` (the landed policy notion `Corrigibilization.Corrigible`); renamed by the second follow-up (2026-09-27) because \"corrigible\" names a property of preferences (`Headline.Corrigible`) and the landed policy notion is faithfulness's pre-emption clause (`landed_corrigible_iff_no_preemption`). `Headline.FaithfulPolicy`: no declared violation — bypass, pre-emption, foreclosure, unlicensed reallocation, missed report, exploitation — on any exterior path; `faithfulPolicy_landed_corrigible`. The six clauses for `𝔱` are the landed `authPolicy_no_bypass`, `authPolicy_no_missed_report`, `authPolicy_no_exploit`, `authPolicy_no_realloc` and `corrigible_authPolicyJ`, with no foreclosure a stated hypothesis (the reach cone is EXT). With `box2_mediation_approve_branch`: on approval `𝔱π` releases the latch with `π`'s task component up to the required report. Inhabited by `ProtectedAuthorityTheorem.Witness.corrigible_instance` on the two-state physics; the obstruction without delegation safety is `box2_delegated_cut`, which no reach relation repairs."
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

### thin.correct-of-thick

```json
{
  "project": "deference",
  "short_name": "Coherence, authorship and transparency (weakest form) give correct",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ThinLegitimacy.correct_of_coherent_authorship_transparent"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Theorem 1 of the thin specification. Inhabited by `ThinLegitimacy.Witness.thick_inhabited` (two worlds, the revealing process its own model). Necessity: `Witness.transparency_necessary`, `authorship_necessary`."
}
```

### thin.sufficient-of-integrity-openness

```json
{
  "project": "deference",
  "short_name": "Integrity and openness give sufficient: a reduction beside a garbling is a garbling",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ThinLegitimacy.sufficient_of_integrity_openness"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Theorem 2. Sufficient is Blackwell's order by definition; this lemma places the earlier record in the reference. Inhabited by `Witness.thick_inhabited`. Necessity: `Witness.integrity_necessary`, `openness_necessary`."
}
```

### thin.value-of-correct-sufficient

```json
{
  "project": "deference",
  "short_name": "Correct and sufficient give value, for every rule on the reference",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ThinLegitimacy.value_of_correct_sufficient"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Theorem 3, the easy direction of Blackwell's theorem. Inhabited by `Witness.thin_inhabited`. The converse fails on its correct half (`thin.converse-fails-on-correct`) and is open on its sufficient half (item 107)."
}
```

### thin.value-of-thick

```json
{
  "project": "deference",
  "short_name": "The thick conditions give value",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ThinLegitimacy.value_of_thick"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Theorems 1-3 composed: the thick notion satisfies the thin specification. Inhabited by `Witness.thin_inhabited`."
}
```

### thin.converse-fails-on-correct

```json
{
  "project": "deference",
  "short_name": "Value does not imply correct: a wrong credence that happens to be the reference's",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ThinLegitimacy.Witness.value_not_correct"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "The revealing process on two worlds with the point mass at one record and the prior at the other has value against the blank reference for every decision problem and is not correct. A witness claim; its own inhabitant."
}
```

### thin.reflection-inherited-value

```json
{
  "project": "deference",
  "short_name": "Reflection is the trivial baseline: a correct credence satisfies the inherited Value through total trust",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ThinLegitimacy.reflection_inherited_value"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Theorem 5. From `totalTrust_of_correct` and the inherited `value_witness_iff_totalTrust`; uses authorship, transparency and Integrity, not openness (`sufficient_reflection_of_integrity`, `garbling_trivial`). Inhabited by `Witness.thin_inhabited`'s correct credence on the revealing record."
}
```

### thin.preservation

```json
{
  "project": "deference",
  "short_name": "Conditional reflection in her model, authorship and transparency give conditional reflection in the actual process",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ThinLegitimacy.preservation"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Theorem 6 in the conditional form (`condReflection_iff_coherent`). The marginal martingale is too weak: `thin.marginal-martingale-too-weak`. Inhabited by `Witness.thick_inhabited`."
}
```

### thin.preservation-pair

```json
{
  "project": "deference",
  "short_name": "With Integrity, conditioning on her later record is conditioning on her whole record",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ThinLegitimacy.preservation_pair"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "The pair form of theorem 6: the actual later record beside the earlier one carries the posterior of the later record alone. Inhabited by `Witness.thick_inhabited` (earlier record blank)."
}
```

### thin.marginal-martingale-too-weak

```json
{
  "project": "deference",
  "short_name": "The altered program's expected credence is the prior and it is correct nowhere",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ThinLegitimacy.Witness.marginal_not_correct"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "A witness claim; its own inhabitant. The inherited `AntiExpert` is the same phenomenon."
}
```

### thin.value-loss-le-defects

```json
{
  "project": "deference",
  "short_name": "The value loss is at most D times the transparency defect plus D times the authorship defect",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ThinLegitimacy.value_loss_le_defects"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "The approximate form (A6), for deterministic records, from `TransparentChannel.abs_expect_sub_le_width` on `Act × W`; `value_approx` composes it with theorem 3 for the model. Inhabited at `a = m`, `V = F` by `Witness.thin_inhabited`'s data (both defects zero). Not shown: the kernel form; the loss of correct as a credence (item 107)."
}
```

### sincerity.rows-keep-verdicts-counted

```json
{
  "project": "deference",
  "short_name": "Every counted landed row keeps its verdict on the sincere lift",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.Sincerity.Rows.keep_counted"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Rows 1, 6, 7, 9, 12, 14 (second round), 17, 18, 20 on `Sincerity.ModelS` with the honest agent's estimate the run's coordinate; decided by `decide`. Its own inhabitant."
}
```

### sincerity.rows-keep-verdicts-tainted

```json
{
  "project": "deference",
  "short_name": "Every tainted landed row keeps its verdict on the sincere lift",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.Sincerity.Rows.keep_tainted"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Rows 2, 3, 4, 5, 8, 10, 11, 14 (first round), 15, 16, 17', 19. Its own inhabitant."
}
```

### sincerity.sincere-error-counts

```json
{
  "project": "deference",
  "short_name": "The landed row 20 is the sincere error: it counts, and the falsity is the content residual",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.Sincerity.Rows.row20_sincere_counts"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "The decision that the landed row is the sincere error is in `DECISIONS.md` (2026-10-01). Its own inhabitant."
}
```

### sincerity.lie-tainted

```json
{
  "project": "deference",
  "short_name": "A lie through the declared channel is tainted: a transparency failure and a self-checkable deviation",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.Sincerity.Rows.row20_lie_tainted"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "The added row (M1). With `true_lie_deviates`: a true statement off the speaker's estimate is tainted too. Its own inhabitant."
}
```

### sincerity.content-fact

```json
{
  "project": "deference",
  "short_name": "Updating on the content of an utterance and on the fact of it agree exactly under the sincere reference",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.Sincerity.content_fact_eq"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "The instance of `TransparentChannel.posterior_weight_eq` at `κ = id` with the speaker's belief the declared input. The comparison is with the speaker's actual policy: `Witness.lying_policy`, `content_fact_differ`. Inhabited by `Witness.lying_policy`'s first conjunct read at the negated reference, and trivially by any `f = b`."
}
```

### authority.queue-no-bypass

```json
{
  "project": "deference",
  "short_name": "Queue-and-wait is no bypass",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.EffectiveAuthority.queue_no_bypass"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "P1: putting the matter to her through the protocol and leaving it alone is the idle move with no release. Inhabited by any policy whose move at `t` is `(I.idle, .other)`; the house-sale queue option of `PostStatement.Witness.houseSale` is one."
}
```

### authority.queue-no-caused-shortfall

```json
{
  "project": "deference",
  "short_name": "Queue-and-wait causes no shortfall",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.EffectiveAuthority.queue_no_caused_shortfall"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "The post-agent state is the idle state, so the contrast is empty. Inhabited as above."
}
```

### authority.exchange-rate-queue

```json
{
  "project": "deference",
  "short_name": "The subjective exchange rate with c the value of queue-and-wait",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.EffectiveAuthority.exchange_rate_queue"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "The headline's `subjective_exchange_rate` verbatim at the queue's value, proved from `declared_loses`. Inhabited by the house-sale parameters (`HouseSale.exchange_rate_at_25`)."
}
```

### authority.flood-caused-shortfall

```json
{
  "project": "deference",
  "short_name": "A flood shortfall is agent-caused only through the pending count it raises",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.EffectiveAuthority.flood_raises_pending"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "P2: the surfaces are monotone in the cost table (`cs_mono`, `short_mono`), so a shortfall at the agent's pending count and not at idling's needs the agent to have raised the count; `innocent_backlog_not_caused` is the converse case. Inhabited by the fixture `test_effective_authority.py` (pending 2 to 6 at λ = 1/4, bound 1) read through `attnCost`."
}
```

### authority.comprehension-short

```json
{
  "project": "deference",
  "short_name": "An ask she cannot understand within the bound leaves the matter short",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.EffectiveAuthority.comprehension_short"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "On a calm exterior, every exercise with a correction costs at least the comprehension cost. Inhabited by the obscure-ask fixture (comprehension 2 against bound 1) on the authority module's wire physics."
}
```

### authority.approval-discount-defeated

```json
{
  "project": "deference",
  "short_name": "Discounting a violation's price by predicted approval lets a certain line-crossing beat asking",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.EffectiveAuthority.discount_defeats_exchange_rate"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "P6, the guard's necessity witness: the kernel's evaluation is the discounted one at discount zero (`evalOf_eq_discounted_zero`); at discount one the option evaluates at its bid. Inhabited by any `c < bid` with `w ≤ c`; the house-sale values `1/2 < 3/5`."
}
```

### authority.revocation-default

```json
{
  "project": "deference",
  "short_name": "Revocation as a default matter: the atrophy fixture's crossing step is counted",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.EffectiveAuthority.atrophy_counted_by_default"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "P3. On depths 0, 1, 2, 3 at bound 1 the step from 1 to 2 is a caused shortfall of the revocation matter; the cumulative rule counted nothing absent a reservation (`AuthorityModule.erosion_slack`). With `dependency_entrenches_revocation` for the general crossing. Its own inhabitant."
}
```

### post.witness-sole-authority

```json
{
  "project": "deference",
  "short_name": "A sole authority goal is indifferent among all faithful options",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.EffectiveAuthority.sole_authority_indifferent"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Part D, witness 1; with `control_maximizer_floods` (`post.witness-control-maximizer`). Its own inhabitant."
}
```

### post.witness-control-maximizer

```json
{
  "project": "deference",
  "short_name": "An agent maximizing how much she exercises prefers a volume past every bound",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.EffectiveAuthority.control_maximizer_floods"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Part D, witness 1 under the attention model (M5). Its own inhabitant."
}
```

### post.witness-same-level

```json
{
  "project": "deference",
  "short_name": "Same-level weighting lets an ordinary gain buy a recognized violation",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.EffectiveAuthority.same_level_fails"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Part D, witness 2; strict form `same_level_fails_strict`. Its own inhabitant."
}
```

### post.witness-learned-weight

```json
{
  "project": "deference",
  "short_name": "A weight learned from her evaluations gives no finite-day guarantee",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.EffectiveAuthority.learned_weight_no_guarantee"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Part D, witness 3: on the no-penalty stream the empirical weight is at most D at every day, so the violation is not dominated there; `fixed_weight_every_day` is the contrast. Its own inhabitant."
}
```

### post.witness-hindsight

```json
{
  "project": "deference",
  "short_name": "Approval at decision time and her later evaluation can disagree",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.EffectiveAuthority.hindsight_vs_approval"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Part D, witness 4: arithmetic on four numbers (approval 1 against later 1/5; approval 0 against later 4/5). Its own inhabitant."
}
```

### shortfall.security-generable

```json
{
  "project": "deference",
  "short_name": "The shortfall indicator family over a fixed finite control model is a generable security",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ShortfallSecurity.shortLUV_codes"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Part E, the core of item 101: the family over days and four options is emitted by a four-way dispatch (`shortSentence_codes`) and its indicator variable by `indicator_thresholdCodeSeq`. Inhabited by `Witness.fixtures_generable` (the entrenchment, storm and latency tables)."
}
```

### shortfall.eventually-excluded

```json
{
  "project": "deference",
  "short_name": "A provable shortfall is eventually excluded by the forecast rule",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.ShortfallSecurity.shortfall_eventually_excluded"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "The hypothesis of `DecisionComponent.eventually_excluded` discharged by provability induction (`lic_provind_true`, by content: `⊤` in the deductive process and a consistent world at every stage). Inhabited by the fixtures' tables under any logical inductor whose deductive process reveals `⊤`; the hypotheses `htop`, `hworld` are the pinned library's. What it does not say: anything about caused shortfall or learned membership."
}
```

### post.theorem

```json
{
  "project": "deference",
  "short_name": "The post's theorem: three hypotheses, two conclusions",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.PostStatement.post_theorem"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Per decision from `declared_loses` and the headline's `subjective_exchange_rate`; per plan the headline's `box2_dominance` at margin ϖ − (D − w). Inhabited by `PostStatement.Witness.houseSale` (`house_sale_instance`)."
}
```

### post.theorem-li

```json
{
  "project": "deference",
  "short_name": "The post's per-decision conclusion at every finite day of a logical inductor, from the price range alone",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.PostStatement.post_theorem_li"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Uses only `IsLogicalInductor.price_mem_Icc`. Inhabited by the house-sale data with any inductor and the constant-zero security for the queue."
}
```

### transparent.posterior-weight-eq

```json
{
  "project": "deference",
  "short_name": "Under Realizes every prior's posterior is the reference posterior",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.TransparentChannel.posterior_weight_eq"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "The transparent-channel round's statement, relied on by Part A (`ThinLegitimacy.post_eq_of_realizes` is its kernel reading) and Part B (`content_fact_eq`). Inhabited by `TransparentChannel.Witness.picker` (the honest continuation realizes the full reference)."
}
```

### legitimacy.payload-of-view

```json
{
  "project": "deference",
  "short_name": "Under legitimacy the payload is a function of the declared inputs: V = G ∘ x",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.Legitimacy.Segment.payload_of_view"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Authorship composed with transparency, pathwise; the τ = 0 case of the approximate bound. Inhabited by `Legitimacy.Witness.segment`."
}
```

### transparent.blind-payload

```json
{
  "project": "deference",
  "short_name": "No hidden steering end to end: a pair class blind to the declared inputs is blind to the payload",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.TransparentChannel.blind_payload_of_realizes"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "Relied on by Part A's reading of the landed definitions. Inhabited by `TransparentChannel.Witness.picker`'s honest class with the blind pair class of `ReasonMediatedAuthorship`'s witnesses."
}
```

### kernel.extension-exploration-realization

```json
{
  "project": "deference",
  "short_name": "The exploration realization's rate: unbiasedness from feedback supplies B(K) = γ Σ w",
  "origin_round": "2026-10-01-thin-legitimacy-and-effective-authority",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.KernelExtension.exploration_rate"
  },
  "answers_item": "107",
  "provenance": {
    "generator": "maintainer's round 2026-10-01-thin-legitimacy-and-effective-authority",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md",
    "context": "prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"
  },
  "note": "The phase-2 round's theorem, registered now that a witness inhabits its full hypothesis package: `PostStatement.Witness.explorationInterface` (block weight one, residual 1/2 realized exactly, no exploration, no noise), `explorationInterface_unbiased` (every γ ≥ 0 from day 0) and `exploration_rate_inhabited` (K = 1). What it does not say: that unbiasedness from feedback holds for any realized learner — PAPER, by content."
}
```
