# Stage IV — independent adversarial review

Run in a **separate Claude Opus 5 context** with no access to the constructing round's
reasoning, per the dispatch's §23. It was given the specification, the harness, the Lean
module, and the five claims to attack; it was not told which answer was wanted.

Its verdicts were accepted substantially in full. The round's positive reading is
withdrawn, the claimed-gate harness is deleted, and the specification is marked as a
collapsed construction. This register records what it found; the parent report records
what changed because of it.

An earlier run of this review was **interrupted by the constructing agent**: repairing an
unrelated pull-request conflict involved a `git stash` that removed the still-untracked
harness out from under the reviewer mid-read, and it stalled. No findings were lost — it
had not yet produced any — and the artifacts were committed before the re-run so the same
failure could not recur. It is recorded because it was a process failure of the
orchestrator's making, not of the reviewer's.

## Verdicts as returned

**The gate: no, it collapses** — in a weaker but structurally identical way to Stage III,
and the headline instance additionally fails the gate's own stated test.

| claim | verdict |
|---|---|
| dominance under a Bayes-rational principal | **circular — and it is Stage III's own theorem with the arms swapped** |
| transfer wins under a fallible principal | **confounded** — the principal's information was never varied, and the *reported* witness has the principal twice as wrong as the later agent |
| advice loss is real | **false** — refuted by a strictly *more* fallible later agent; the loss is bandwidth, not error contamination |
| the same action under both jurisdictions | **sound but trivial** — the check tests `len(same) > 0`, and the reported "4 of 4" is a tie resolved by list order |
| fallibility requires interior | **false as stated** — needs an unstated full-support hypothesis on the later credence |

## The three findings that ended the round

**1. The later agent is still derived.** `κ_A` differs from the evaluator's conditional
argmax by exactly one argument — the credence. It remains a total function of objects the
specification itself declares known at `n`. What a different credence buys is the freedom
to name, on each cell, an action optimal under *some* measure; it does not buy a process
the evaluator lacks. And in the headline instance the transferred arm's realisation is
**constant** (`a` at all four states), so the evaluator does know the realised action —
the property the round's gate exists to establish. The check meant to catch this was
rigged: its second disjunct was a module constant, so it could not fail, and its label
asserted the opposite of what its code established.

**2. Jurisdiction does no mathematical work.** Setting the principal's credence to the
later agent's, with the full-signal interface, makes the delegated arm identical to the
transferred arm at **every one of 32,805 instances**. The transferred arm is a coordinate
in the delegated arm's parameter space. Reproduced independently by the orchestrator
before acceptance.

**3. The dominance result is the collapsed theorem, relocated.** Under the
action-recommendation interface the transferred arm's realisation *is* the message, so
the claim reduces to "the maximum over a cell is at least a member of it" — the exact
statement the Stage III review already condemned. Stage III put the evaluator's argmax on
the transferred side and the transferred side trivially won; Stage IV puts it on the
delegated side and the delegated side trivially wins.

The scan behind it is padding: **19,468 of 26,244 instances contain no fallible later
agent at all**, i.e. they are Stage III instances, the exact configuration the round was
dispatched to eliminate; and 21,186 of the remainder are ties rather than strict wins.

## Vacuous checks and label/code mismatches

Ten of twenty-three checks could not fail, including one literal `True` and one `or True`.
The Stage III review found four such checks; this round reproduced the defect at higher
density. Seven labels claimed more than their code computed — among them "the realised
action is not constant" (it is), "D differs from FU" (it does not, and the check is
`or True`), and "BOT is a selectable effect" (the code tests list membership; BOT is
selected nowhere in the displayed instance).

It also caught a reporting error: the round described the harness as running 28 checks. It
ran 23. The figure was carried over from the Stage III report.

## What it confirmed

Exact arithmetic throughout — every verdict path is a rational, no float anywhere. The
harness ran as claimed and the Lean compiled with permitted axioms only. The fragility is
tie resolution, not rounding, which exactness does not protect against: two of the five
claims flip when the option order is reversed.

## The structural point, which is the round's most valuable output

> Any two authorisation regimes that induce the same realisation map are *identical
> objects* in a signature whose only outputs are maps `Ω → Π ⊔ {⊥}` priced by one
> measure. That is not a finding about jurisdiction; it is the signature refusing to
> carry the concept. A model that could tell the arms apart needs the authorisation
> relation itself in the type — skeleton v2 §4a is the right instinct — not a third
> credence.

## Disposition

Accepted. The claimed-gate harness is deleted rather than repaired; `diagnose_collapse.py`
replaces it and every check in it records a defect. The specification is marked collapsed
and its two false claims are corrected in place. One item is recorded as **not** adopted:
the review notes that a *fairer* witness for the transfer-wins claim exists in the same
scan (380 instances where the principal is no more wrong than the later agent). That is
true, and it does not rescue the claim, because the blindness confound applies to those
instances too — so the claim is withdrawn rather than re-witnessed.

## Provenance

Executor: **Claude Opus 5** (Anthropic), independent context, 2026-08-11. Review brief
written by the round's orchestrator, Claude Opus 5 (Anthropic). Review status: `ci-only`.
This register is the orchestrator's summary of the returned findings, not a verbatim
transcript.
