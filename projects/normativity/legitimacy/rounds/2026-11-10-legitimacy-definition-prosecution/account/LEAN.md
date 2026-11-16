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

Rerun: `~/.claude/scripts/safe-lake.sh build Workspace.Deference.Contrib.AppraisalAccount`
from `lean/` (in CI, the `lean` job); the file ends with `#print axioms` on each of its
fifty declarations, each reporting `[propext, Classical.choice, Quot.sound]` or no axiom.
The registry entries are in `projects/normativity/CLAIMS.md` under *The appraisal account*.

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
