# The account's results in Lean

`lean/Workspace/Deference/Contrib/AppraisalAccount.lean`, namespace
`Workspace.Deference.Contrib.AppraisalAccount`, against item 137. A finite space `X` with
a non-negative weight `μ`; expectation is the workspace's `LICorrigibility.expectR`; the
conditional expectation given a labelling `g` is `condExp μ g T`, the weighted mean over
the cell of `g`, defined in the file (0 on a cell of zero mass, and no theorem assumes
cells have positive mass).

| result of `RESULTS.md` | declaration | hypotheses | witness | proposed registry id |
|---|---|---|---|---|
| 1, at any conditioning the appraisal is a function of | `mse_split` | `0 ≤ μ`; the appraisal constant on the cells | `Witness.mse_split_instance` | `appraisal.mse-split` |
| 1, minimal | `mse_split_minimal` | `0 ≤ μ` | the same | — |
| 2 | `three_channels` (`attained_eq`, `ignorance_nonneg`, `misuse_nonneg`) | `0 ≤ μ` | `Witness.three_channels_instance` | `appraisal.three-channels` |
| 3, full strength | `misuse_le` | `0 ≤ μ`, `Σ μ = 1` | `Witness.misuse_le_instance` | `appraisal.cost-of-mistakes` |
| 7 | `deferring_identity` (`deferring`, `deferring_determined`) | `0 ≤ μ` for the identity; none for the determined case | `Witness.deferring_instance`, `Witness.deferring_determined_instance`, `Witness.deferring_identity_instance` | `appraisal.deferring` |

Rerun: `~/.claude/scripts/safe-lake.sh build Workspace.Deference.Contrib.AppraisalAccount`
from `lean/` (in CI, the `lean` job); the file ends with `#print axioms` on each of its
fifty declarations, each reporting `[propext, Classical.choice, Quot.sound]` or no axiom.


**Reuse of the deference line's Lean.** `expectR` and two of its lemmas
(`DeconfusingCorrigibility.expectR_mono`, `expectR_sub`) are reused. `ThinLegitimacy`'s
`Kernel`, `post` and `Correct` state calibration of a credence over worlds given a record,
for a prior that is hers; these results need the conditional mean of a real variable given
a labelling under the actual weight, and squared distances from it, which those files do
not define, so `condExp` is new. `Legitimacy.lean`, `TransparentChannel.lean` and
`GateIsLegitimacy.lean` state conditions on processes and channels and have no squared
error; nothing in them is restated here.

**Not in Lean.** Results 4–6 and 8–11. The failure of result 3 at the minimal and
per-conduct strengths (`results.py`, `r3`) is a Python instance. Of item 137's own list,
written for the sixth follow-up's statements: its 1.2 is `deferring`, and its 1.3 is
`misuse_le`; the squared-mean form 1.1, the equality case 1.4, the drift bound 4.2, the
bound 5.1 with its counterexample 5.5, and `trueScore_noRegret` against
`DeconfusingCorrigibility.Sequential` are not written. The witnesses inhabit each
hypothesis package; that the terms of the identities are non-zero on them is not proved
in Lean, except that the verdict of `Witness.deferring_instance` is shown not to be
determined by the adviser's information.

## Registration

**Not registered.** The site build refuses a registered claim that no map node carries
(`tests/site_build.py`), a node needs an author handle, and the executor's handle is not
mapped in `graph/policy.yaml`, which this pass may not edit. The four theorems ship in
the contribution namespace, unregistered. To register: map the handle; append the
entries below to `projects/normativity/CLAIMS.md` under a heading *The appraisal
account*; file the record, bridge and completeness nodes for each as for
`seed.adapter-certificates-exist`; set `registered_classes` to `["lean-proved"]` and
`claim_changes` to the four ids in this round's record in `state/rounds.json`.

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
