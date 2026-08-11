# Track F — adversarial theorem-shape review

Run in a **separate Claude Opus 5 context** with no access to the round's report or
reasoning, per the dispatch's §16 independence requirement. It was given the frozen
specification, the harness, the Lean module, and the five claims to attack; it was not
told which answer was wanted.

Its verdicts were accepted substantially in full, and the round's central claims were
withdrawn or restated as a result. This register records what it found. The round's
`REPORT.md` records what changed because of it.

## Verdicts as returned

| claim | verdict |
|---|---|
| dominance of the transferred arm | **sound but trivial, and mislabelled** — the Lean statement carries one hypothesis, that `φ` is a per-cell maximiser, and no fairness condition at all. The content is `∑ maxima ≥ ∑ anything`. The docstring described a statement that was not there |
| the regret identity | **tautology** — proved by distributivity of subtraction over a finite sum. Nothing is discovered, and the file's own header already conceded the reading would be overclaiming |
| the rubber-stamp reading | **false as a biconditional** — only one direction was proved and only one was checked. Counterexample supplied: the arms disagree, the principal is maximally decisive, and the gap is still zero, because the cell is indifferent in the *quantity* |
| circularity inheritance | **sound, but not "inherited" — it is the same object.** Under F2 the gap *is* the delegation deficit against the later-measurable comparator class, so the collapse applies directly rather than by analogy. Two caveats: it was verified only at singleton cells, and it constrains credence-free hypotheses, which the round's competence hypothesis is not |
| the gated competence bound | **sound and non-circular, but misclassified and near-vacuously tested** — it compares grades to a conditional expectation, so the credence occurs in it; it is a joint competence–credence hypothesis, the same error the competence track caught for grade trust |

## The finding that ended the round's positive reading

> `FU` is not a future agent; it is the upper envelope of the comparator class, and it is
> fully computable by the current agent at time `n`.

The FU arm's selection was defined as the argmax of the evaluator's own objective under
the evaluator's own credence. Combined with "future `A` is `A_n` conditioned", the arm
contains no cognition `A_n` lacks. Three consequences it drew:

1. Skeleton v2 §4 declared `FU[g]` a hole and warned that careless invention is how it
   collapses; Stage II §11 listed the time-indexed `A_t` and the jurisdiction-transfer
   object as prerequisites 1 and 2. The round filled the hole with the envelope Stage II
   had already priced and said is not `FU[g]`.
2. The real load-bearing assumption is **infallibility**, not "no evaluative drift". It
   supplied a witness with every fairness condition intact in which a better-informed but
   fallible future agent makes the gap strictly negative.
3. The specification waives `⊥` and defers all capability structure, deleting the one
   carrier Stage II identified as holding all of protection's valuation content — and
   then reports that no jurisdictional term appears. "Guaranteed by construction, not
   found."

## Harness defects it found

Twelve, of which the substantive ones: two checks in the architecture-blindness section
were vacuous (the two "different architectures" were constructed from byte-identical
arguments); two checks in the collapse section were vacuous (`len(...) == 4` and
`max(xs) in xs`); the information witness moved two variables rather than one, so its
conclusion did not follow from its own code; the agenda witness widened *both* arms
because the model carried a single shared menu; the competence section's headline was
95.8% padding, with most "satisfying instances" passing at a bound at or above `2B` that
every gap satisfies unconditionally; the sweep never varied the fairness dimension; the
gated bound shipped no inhabitation witness, which `AGENTS.md`'s Lean regime forbids for
promotion; and the specification's claim that all seven fairness conditions were
machine-verified was false.

It also confirmed what was sound: the harness exits 0, no float appears on any verdict
path, and the Lean module compiles with all declarations auditing to the three standard
axioms.

## Disposition

Every defect above is fixed or withdrawn in the round's final state. The vacuous checks
are removed, the two confound witnesses now move exactly one variable each, the converse
counterexample is carried, the informative-instance count is reported rather than hidden,
the sweep's fairness restriction is stated, the missing inhabitation witness is supplied,
the competence hypothesis is reclassified, and the Lean module is renamed to what it
proves. The round's verdict is rewritten from a positive reading to a negative one.

One point is recorded as **not** adopted: the review calls the dominance result
"mislabelled" and the identity a "tautology", and both are now stated in exactly those
terms — but the statements themselves are kept rather than deleted, because they are true,
kernel-checked, and reusable for whatever successor supplies a real future agent. What was
wrong was the reading placed on them, not the mathematics.

## Provenance

Executor: **Claude Opus 5** (Anthropic), independent context, 2026-08-11, under the
Stage III round. Prompt author of the review brief: Claude Opus 5 (the round's
orchestrator). Review status: `ci-only`. This register is the orchestrator's summary of
that context's returned findings, not a verbatim transcript.
