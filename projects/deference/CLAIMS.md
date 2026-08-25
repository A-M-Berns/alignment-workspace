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
