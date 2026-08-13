# Adversarial review, and what was done with it

**Status:** `ci-only`. The review ran in a separate Claude Opus 5 context, given the Lean
file and the dispatch's fourteen attacks, and **not** given the constructing context's
reasoning. It wrote and compiled its own adversary constructions against the file.

**Outcome: the verdict was downgraded**, from `Representation-positive` as drafted to
`Mixed`. Two of the round's three headline claims did not survive. Every finding was
accepted; none was argued down.

## How the findings were handled

Refutations are **theorems in the file**, not replies in prose. §10 of
`lean/Workspace/Deference/Contrib/TimeIndexedCapability.lean` carries the review's own
constructions, reproved in place, so a reader meets the refutation next to the thing it
refutes and the kernel checks both.

| review finding | now in the file as |
|---|---|
| the cut freezes the run; the family collapses onto the trajectory | `run_freeze`, `cutRun_eq_run_min` |
| `Forecloses` has no family content | `forecloses_iff_one_step` |
| the frame certification does not exclude a label | `spurFrame`, `spurFrame_agentInert_iff` |
| the cardinality control is a decoy that passes for the label | `spur_cardinality_control` |
| the prevention claim was never proved | `honest_prevention` — correct quantifier, weakened hypothesis |
| ratchet stipulated while the docstring denied it; `coupled_antitone` cited and nonexistent | docstring rewritten, dangling reference removed |
| `exercise` is not a transition; `prediction_does_not_confer` is `false = false` | docstrings rewritten to call it a stipulation |
| `Actor` is the authorization flag the round claimed to avoid | recorded in the report §5 |
| the capability corrects nothing — `CWorld` disconnected from `St` | recorded in the report §5 |
| T3's difference is immediate, not future | docstring rewritten |
| T5's endpoint clause is `rfl`-true for a degenerate reason | recorded in the report §4 |
| five internal section references off by one | corrected |

## What the review confirmed rather than broke

Kept, and load-bearing for the successor: shared history is genuinely enforced by
`run_congr` and `cutRun_shared_history` rather than stipulated — this was attacked and
held; foreclosure attributes causally, so `Forecloses π m s` entails the advisor performed
a severing act; the foreclosure time is unique; and the boundary conventions `m < n`,
`m < k` are forced rather than chosen. `HasCorr` is genuinely not action-cardinality and
is not faked by duplicate or inert actions — though the review noted the file's argument
for that is a decoy and the real reason is that the agent carrier is `Bool` at every
state.

## The one thing the review asked for

> make the sealed continuation actually differ from a frozen prefix — give the state
> autonomous or principal-driven dynamics so that `step .idle ≠ id`

Everything that failed traces to its absence. The report's §9 carries it as the
successor's requirement.

## A note on the process

The pre-review draft of this round's technical register claimed
`Representation-positive` and was wrong in the same way this project's previous round was
corrected for: a real observation stated a notch past its evidence. The review was worth
more than the construction, and running it against a fresh context rather than
self-auditing is why it caught the collapse in its first check.
