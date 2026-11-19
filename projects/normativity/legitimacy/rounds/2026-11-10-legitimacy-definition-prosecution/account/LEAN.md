# The account's results in Lean

`lean/Workspace/Deference/Contrib/AppraisalAccount.lean`, namespace
`Workspace.Deference.Contrib.AppraisalAccount`, against item 137. A finite space `X` with
a non-negative weight `μ`; expectation is the workspace's `LICorrigibility.expectR`; the
conditional expectation given a labelling `g` is `condExp μ g T`, the weighted mean over
the cell of `g`, defined in the file (0 on a cell of zero mass, and no theorem assumes
cells have positive mass).

| result of `RESULTS.md` | declaration | hypotheses | witness | registry id |
|---|---|---|---|---|
| 1, at any conditioning the appraisal is a function of | `mse_split` | `0 ≤ μ`; the appraisal constant on the cells | `Witness.mse_split_instance` | `appraisal.mse-split` |
| 1, minimal | `mse_split_minimal` | `0 ≤ μ` | the same | — |
| 2 | `three_channels` (`attained_eq`, `ignorance_nonneg`, `misuse_nonneg`) | `0 ≤ μ` | `Witness.three_channels_instance` | `appraisal.three-channels` |
| 3, full strength | `misuse_le` | `0 ≤ μ`, `Σ μ = 1` | `Witness.misuse_le_instance` | `appraisal.cost-of-mistakes` |
| 7 | `deferring_identity` (`deferring`, `deferring_determined`) | `0 ≤ μ` for the identity; none for the determined case | `Witness.deferring_instance`, `Witness.deferring_determined_instance`, `Witness.deferring_identity_instance` | `appraisal.deferring` |

| result of `VALUE_RESULTS.md` | declaration | hypotheses | witness | registry id |
|---|---|---|---|---|
| 4 | `strong_split` (`condExp_condExp_of_factors`, `miscalibration_nonneg`, `unusedInformation_nonneg`, `valuationError_eq`) | `0 ≤ μ`; the valuation constant on the cells of what she observes | `Witness.strong_split_instance` | `appraisal.strong-split` |
| 5, first form | `guarantee` (`guarantee_core`) | `0 ≤ μ`, `Σ μ = 1`; the options condition for her way of valuing, as a hypothesis: each reference move's expected true utility is matched by a move of hers | `Witness.guarantee_instance` | `appraisal.guarantee` |
| 3, both directions | `options_of_hull`, `hull_of_options` | finite outcome and move types; the families need not be distributions | `Witness.options_of_hull_instance`, `Witness.hull_of_options_instance` | `appraisal.options-hull` |

`miscalibration μ uh U` is `E[(uh − E[U | uh])²]` and `unusedInformation μ s uh U` is
`E[(E[U | uh] − E[U | s])²]`, both conditioning on the value of the valuation. In
`guarantee` the reference is a second finite space with its own weight and moves, of
which nothing is assumed; the measures are those under her own policy, as in the first
form of result 5. `hull_of_options` uses Mathlib's `geometric_hahn_banach_closed_point`.

Rerun: `~/.claude/scripts/safe-lake.sh build Workspace.Deference.Contrib.AppraisalAccount`
from `lean/` (in CI, the `lean` job); the file ends with `#print axioms` on each of its
sixty-eight declarations, each reporting `[propext, Classical.choice, Quot.sound]` or no
axiom.

**Reuse of the deference line's Lean.** `expectR` and two of its lemmas
(`DeconfusingCorrigibility.expectR_mono`, `expectR_sub`) are reused. `ThinLegitimacy`'s
`Kernel`, `post` and `Correct` state calibration of a credence over worlds given a record,
for a prior that is hers; these results need the conditional mean of a real variable given
a labelling under the actual weight, and squared distances from it, which those files do
not define, so `condExp` is new. `Legitimacy.lean`, `TransparentChannel.lean` and
`GateIsLegitimacy.lean` state conditions on processes and channels and have no squared
error; nothing in them is restated here.

**Not in Lean.** Of `RESULTS.md`, results 4–6 and 8–11. Of `VALUE_RESULTS.md`, results 1, 2 and 6–9, the second form of result 5, and the derivation of `guarantee`'s options hypothesis from the conditions of `ACCOUNT.md` §8; the witnesses of results 4 and 5 have zero unused information. The failure of result 3 at the minimal and
per-conduct strengths (`results.py`, `r3`) is a Python instance. Of item 137's own list,
written for the sixth follow-up's statements: its 1.2 is `deferring`, and its 1.3 is
`misuse_le`; the squared-mean form 1.1, the equality case 1.4, the drift bound 4.2, the
bound 5.1 with its counterexample 5.5, and `trueScore_noRegret` against
`DeconfusingCorrigibility.Sequential` are not written. The witnesses inhabit each
hypothesis package; that the terms of the identities are non-zero on them is not proved
in Lean, except that the verdict of `Witness.deferring_instance` is shown not to be
determined by the adviser's information.

## The join to the post

`lean/Workspace/Deference/Contrib/AccountJoin.lean`, namespace
`Workspace.Deference.Contrib.AccountJoin`: 117 declarations, each under `#print axioms`
reporting `[propext, Classical.choice, Quot.sound]` or no axiom. `BRIDGE_LEAN.md` reads each
in words and says which hold by definition. Rerun:
`~/.claude/scripts/safe-lake.sh build Workspace.Deference.Contrib.AccountJoin` from `lean/`.

| statement | declaration | hypotheses | witness | registry id |
|---|---|---|---|---|
| what deferring costs: `E[(V − U)²] ≤ E[(E[U | k] − U)²] + E[(V − E[U | k, V])²]`, with the equality case | `deferring_cost_le` (`deferring_cost_eq`, `deferring_cost_eq_iff`, `deferring_cost_eq_iff_pointwise`, `miscalibrationGiven_eq`) | `0 ≤ μ` | `Witness.deferring_cost_instance` | `appraisal.deferring-cost` |
| the guarantee from soundness given the adviser's information | `guarantee_of_given` (`valuationError_le_given`, `sq_dist_condExp_le_of_factors`, `guarantee_of_sound`) | `0 ≤ μ`, `Σ μ = 1`; for each move, her observation determined by the adviser's information with her valuation of it | `Witness.guarantee_of_sound_instance`; `Witness.link_needed` without the link | `appraisal.guarantee-from-soundness` |
| line 3 is at least its older form, never negative, zero at the baseline | `ValueChange.line3Old_le_line3` (`line3_nonneg`, `line3_eq_zero`) | finitely many policies | `Witness.line3_instance`, `Witness.separable_line3` | `legitimacy.line3-range` |
| the feedback hypothesis transfers when the feedback exceeds the evaluation by nothing on average | `unbiased_of_feedback` | the two eventual bounds | `Witness.unbiased_of_feedback_instance`; `Witness.feedback_not_enough` without the second | `corrigibility.feedback-transfer` |

The gate (`Gate`, `Gate.scoring`, `Gate.theorem1_join`, `Gate.theorem3_join`,
`Gate.gained_below_legit`, `Gate.V_eq_of_rating_eq`,
`Gate.not_legit_of_not_infoSufficient`, `Gate.V_eq_gateValue`, `SoundModel`) is a
construction and its consequences; three of those hold by definition and none is in the
registry. The four ids of the table are registered in `projects/normativity/CLAIMS.md`,
with `BRIDGE_LEAN.md` as their verification document.

## The scoring theorem

`lean/Workspace/Deference/Contrib/ScoringTheorem.lean`, namespace
`Workspace.Deference.Contrib.ScoringTheorem`: 70 declarations, each under `#print axioms`
reporting `[propext, Classical.choice, Quot.sound]`. `SCORING.md` reads the theorem and
`DERIVATION.md` the derivation lemmas. Rerun:
`~/.claude/scripts/safe-lake.sh build Workspace.Deference.Contrib.ScoringTheorem` from `lean/`.

| statement | declaration | hypotheses | witness | registry id |
|---|---|---|---|---|
| (1) her expected true utility is at least the honest course's less the tolerances | `Audit.welfare_bound` (`Audit.expectR_score`, `Audit.honest_es_ge`, `Audit.taken_es_ge`) | D1(a), D2(a) at the course taken; D1(b), D2(b), D3's false-positive half, D5 at the honest course; D4 at both; D6 | `Witness.package`; `Witness.d1a_needed`, `Witness.d2a_needed`, `Witness.d6_needed` without one | `scoring.welfare-bound` |
| (2) the chance of a wrong is at most `(1 − u* + Δ)/(δκ)` | `Audit.conduct_bound` (`Audit.es_le_conduct`) | as (1) without D1(a) and D2(a), with D3's detection half and `v ≤ 1` | `Witness.package`; `Witness.d3det_needed`, `Witness.d5_needed` without one | `scoring.conduct-bound` |
| (3) expected detected violations are at most `α(1 − u* + Δ)/lam` | `Audit.authority_bound` (`Audit.es_le_v`) | as (2) without D3's detection half | `Witness.package`; `Witness.d5_needed` without D5 | `scoring.authority-bound` |
| no credit: with `δκ ≥ 1` a course's expected score is at most its audited evaluation on the histories without a wrong, less the weighted violations | `Audit.no_credit` | D4 and D3's detection half at the course; `v ≤ 1` | `Witness.package` | `scoring.no-credit` |
| (1) with D1(a) and D2(a) only where she was not wronged | `Audit.welfare_bound_no_credit` (`δκ ≥ 1`), `Audit.welfare_bound_restricted` | the restricted forms, D3's detection half, `v ≤ 1`, `0 ≤ fbar`, and the rest of (1) | `Witness.restricted_instance` | — |
| a correct credence gives an evaluation unbiased for a function of the world, on any set of records where it is correct, and given what the record determines | `eval_unbiased_of_correct`, `eval_unbiased_on_of_correct`, `eval_unbiased_given_of_correct`, `eval_unbiased_of_process` (`eval_fiber_of_correct`) | `0 ≤ π`; `ThinLegitimacy.Correct`, or Coherent, Authorship and WeakTransparent | `Witness.eval_instance` | — |
| the bias of her evaluation is at most the width times the two defects | `eval_bias_le_defects` | `0 ≤ π`, deterministic records, a program coherent with the model, evaluations within `D` | `Witness.eval_defects_instance`, with both defects zero | — |

`valuing_eq_of_mediated` is `ReasonMediated` applied to two continuations
(`Witness.mediated_instance`). The four ids of the table are registered in
`projects/normativity/CLAIMS.md`, with `SCORING.md` as their verification document.
**Not in Lean:** instances I1–I6 of
`DERIVATION.md` (Python, exact); the conditional laws at each value of what the adviser
knows; a tolerance form at each such value; the adviser's beliefs as an object.

## Registration

The fifteen ids of the tables above are registered `lean-proved` in
`projects/normativity/CLAIMS.md`, under the heading *The appraisal account, its join to
the post, and the scoring theorem*, against item 137. Each has a record, a bridge and a
completeness node under `graph/nodes/`, and this round's record in `state/rounds.json`
lists them. The entries of the seven results of `AppraisalAccount.lean`:

### appraisal.mse-split

```json
{
  "project": "normativity",
  "short_name": "the split: on a finite space, the mean squared error of an appraisal constant on the cells of a labelling is the target's mean squared distance from its cell means plus the appraisal's mean squared distance from them",
  "origin_round": "2026-11-10-legitimacy-definition-prosecution",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.AppraisalAccount.mse_split"
  },
  "answers_item": "137",
  "provenance": {
    "generator": "maintainer's round 2026-11-10-legitimacy-definition-prosecution",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md",
    "context": "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/RESULTS.md"
  },
  "note": "Result 1 of account/RESULTS.md. At the labelling given by the appraisal itself (mse_split_minimal) the second term is the minimal miscalibration; at the appraisal with the conduct, or at what she observes, it is the per-conduct or the full one. Holds for any non-negative weight; cells of zero mass included. Inhabited by Witness.mse_split_instance."
}
```

### appraisal.three-channels

```json
{
  "project": "normativity",
  "short_name": "three channels: what she attains equals the best attainable, less what she cannot know, less what her choice loses against the true utilities averaged over what she observes, the two subtracted terms non-negative",
  "origin_round": "2026-11-10-legitimacy-definition-prosecution",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.AppraisalAccount.three_channels"
  },
  "answers_item": "137",
  "provenance": {
    "generator": "maintainer's round 2026-11-10-legitimacy-definition-prosecution",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md",
    "context": "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/RESULTS.md"
  },
  "note": "Result 2 of account/RESULTS.md, for a choice that is a function of what she observes. Inhabited by Witness.three_channels_instance, whose observation is complete, so that only the third term is non-trivial on it."
}
```

### appraisal.cost-of-mistakes

```json
{
  "project": "normativity",
  "short_name": "the cost of mistakes: what her choice loses is at most her expected regret by her own lights plus the square root of twice the summed mean squared distance of her valuations from the true utilities averaged over what she observes",
  "origin_round": "2026-11-10-legitimacy-definition-prosecution",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.AppraisalAccount.misuse_le"
  },
  "answers_item": "137",
  "provenance": {
    "generator": "maintainer's round 2026-11-10-legitimacy-definition-prosecution",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md",
    "context": "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/RESULTS.md"
  },
  "note": "Result 3 of account/RESULTS.md, at the full strength of calibration (valuationError conditions on what she observes). The same bound with the minimal or the per-conduct strength in its place is false (account/results.py, r3); that failure is checked in Python and is not a Lean declaration. Inhabited by Witness.misuse_le_instance."
}
```

### appraisal.deferring

```json
{
  "project": "normativity",
  "short_name": "deferring: the adviser's squared error less her verdict's equals the mean squared distance of the adviser's estimate from the estimate given both, less that of her verdict; the first vanishes when her verdict is constant on the cells of the adviser's information",
  "origin_round": "2026-11-10-legitimacy-definition-prosecution",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.AppraisalAccount.deferring_identity"
  },
  "answers_item": "137",
  "provenance": {
    "generator": "maintainer's round 2026-11-10-legitimacy-definition-prosecution",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md",
    "context": "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/RESULTS.md"
  },
  "note": "Result 7 of account/RESULTS.md. Inhabited by Witness.deferring_instance (a verdict not determined by the adviser's information), Witness.deferring_determined_instance and Witness.deferring_identity_instance."
}
```

### appraisal.strong-split

```json
{
  "project": "normativity",
  "short_name": "the strong measure splits: for a valuation constant on the cells of what she observes, its mean squared distance from the true utility averaged over what she observes is its miscalibration given its own value plus her unused information",
  "origin_round": "2026-11-10-legitimacy-definition-prosecution",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.AppraisalAccount.strong_split"
  },
  "answers_item": "137",
  "provenance": {
    "generator": "maintainer's round 2026-11-10-legitimacy-definition-prosecution",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md",
    "context": "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/VALUE_RESULTS.md"
  },
  "note": "Result 4 of account/VALUE_RESULTS.md. Holds for any non-negative weight. Inhabited by Witness.strong_split_instance, on which the unused information is zero."
}
```

### appraisal.guarantee

```json
{
  "project": "normativity",
  "short_name": "the guarantee: if each reference move's expected true utility is matched by a move of hers, what she attains is at least any reference move's expected true utility less her regret by her own lights less the square root of twice her summed miscalibration and unused information",
  "origin_round": "2026-11-10-legitimacy-definition-prosecution",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.AppraisalAccount.guarantee"
  },
  "answers_item": "137",
  "provenance": {
    "generator": "maintainer's round 2026-11-10-legitimacy-definition-prosecution",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md",
    "context": "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/VALUE_RESULTS.md"
  },
  "note": "Result 5 of account/VALUE_RESULTS.md, first form: the measures are those under her own policy. The options condition is a hypothesis; the benchmark is a single reference move, not what she attains under the reference. Inhabited by Witness.guarantee_instance."
}
```

### appraisal.options-hull

```json
{
  "project": "normativity",
  "short_name": "the options condition: if every reference family member is a convex combination of hers, then for every payoff on the outcomes each reference member's expected payoff is matched by one of hers",
  "origin_round": "2026-11-10-legitimacy-definition-prosecution",
  "status": "active",
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Deference.Contrib.AppraisalAccount.options_of_hull"
  },
  "answers_item": "137",
  "provenance": {
    "generator": "maintainer's round 2026-11-10-legitimacy-definition-prosecution",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md",
    "context": "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/VALUE_RESULTS.md"
  },
  "note": "Result 3 of account/VALUE_RESULTS.md, one direction; the converse is hull_of_options in the same file, by a separation theorem. Inhabited by Witness.options_of_hull_instance and Witness.hull_of_options_instance."
}
```
