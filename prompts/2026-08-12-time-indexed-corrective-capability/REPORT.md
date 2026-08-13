# Report — time-indexed corrective capability

**Prompt author:** GPT-5.6 Sol (OpenAI). **Executor:** Claude Opus 5 (Anthropic).
**Dispatched and executed:** 2026-08-12.

**Verdict: `Mixed`.** Deliverables:
`projects/deference/rounds/2026-08-12-time-indexed-corrective-capability/` —
`TIME_INDEXED_CORRECTIVE_CAPABILITY.md` (verification register),
`TIME_INDEXED_CORRECTIVE_CAPABILITY_FOR_HUMANS.md` (human register), `REVIEW.md`
(adversarial review and disposition). Lean:
`lean/Workspace/Deference/Contrib/TimeIndexedCapability.lean`.

## Deviations from the prompt

**1. Base branch.** The dispatch says to begin from the current appropriate base. `main`
does not carry the corpus-reconciliation round, and this round's premises are that
round's findings — Q3's second candidate and the sealed-sibling shape. The branch is
therefore stacked on `round/2026-08-12-corpus-reconciliation` (pull request #25, open and
green) rather than on `main`. If #25 is closed unmerged, this round's `PRIORITIES.md` and
`RESEARCH_STATE.md` edits need rebasing; nothing in the Lean depends on it.

**2. The Cartesian Frames dependency.** §XIV prefers the authoritative library. It is not
pinned — `lean/lakefile.toml` pins a commit predating `CartesianFrames/`, and repinning is
a maintainer decision still in `DECISIONS.md`'s queue. Per §XIV's own instruction not to
alter the trust chain, this round imported the **existing in-repo mirror** in
`CartesianFrameBridge.lean` rather than mirroring anything new. No new mirroring was done
and the trust chain is untouched.

**3. §X, the next theorem's shape, is deliberately omitted.** The dispatch permits it
only if T1–T8 substantially pass. They do not.

## Files read

`lean/Workspace/Deference/Contrib/CartesianFrameBridge.lean` in full;
`lean/lakefile.toml`, `lean-toolchain`, `Workspace.lean`, `Workspace/Deference/Basic.lean`;
`PRIORITIES.md` Q3; `RESEARCH_STATE.md`; `projects/deference/notes/DISPATCH_QUEUE.md`;
`lean/Workspace/Deference/Contrib/PROVENANCE.md`; `PROVENANCE.md`.

**Not read**, and named because it bears on the audit: `FINITE_MODEL_SKELETON.md`. The
round built a standalone model rather than binding to the skeleton, so the skeleton's
carriers were never consulted — which is itself a limitation, recorded in the report's
obstruction table as the reason the "one decision index deep" row is not repaired.

## Files changed

New: the round directory (4 files), `prompts/2026-08-12-time-indexed-corrective-capability/`
(2 files), `lean/Workspace/Deference/Contrib/TimeIndexedCapability.lean`.
Modified: `PRIORITIES.md` (Q3), `RESEARCH_STATE.md` (a second standing bar),
`projects/deference/notes/DISPATCH_QUEUE.md` (the return),
`lean/Workspace/Deference/Contrib/PROVENANCE.md` and `PROVENANCE.md` (rows).

**No source tree touched.** No item filed. Q3 not graduated. `DECISIONS.md` unchanged —
no maintainer-level choice was resolved and none needed reserving beyond what the queue
already holds.

## What happened

The construction was built to the dispatch's specification and passed, on its own
reading, seven of eight tests. The adversarial review — run in a separate context with
the file and the fourteen attacks, without this round's reasoning — broke it in its first
check, and the failure is structural rather than a proof gap.

**The cut is a freeze, not a sibling.** Silencing the advisor was implemented as the
advisor idling. The state has no dynamics of its own, so idling is the identity and the
"counterfactual continuation" is the actual run stopped early:
`cutRun π n k s = run π (min n k) s`. Every state in the family is a state the trajectory
already passed through, so the cut index is not a second coordinate — it is time, reindexed.
`Forecloses` therefore collapses to a two-frame condition on one run.

Two further breaks: the "not a hidden label" certification passes verbatim for the field
the file itself designated as an inert control, so it excludes nothing; and the
simulation control is a gate no run reads, whose theorem is `false = false` with the
quantified predictor never applied.

All fourteen findings were accepted. **The refutations are theorems in §10 of the Lean
file**, reproved in place, rather than prose replies — so the kernel checks the negative
result alongside the thing it refutes, and a reader meets them together.

## What survives

- **Endpoint preservation and corrective capability are independent**, in both
  directions, as exact finite witnesses. The round's positive contribution, on a
  deliberately degenerate model, with one of the two witnesses `rfl`-true for a
  degenerate reason.
- **Shared history is genuinely enforced** by `run_congr`, `cutRun_shared_history` and
  `cutRun_agree_below` — attacked and held.
- **Foreclosure attributes causally and uniquely**: the predicate entails the advisor
  performed a severing act, at a unique time.
- **`honest_prevention`**, the theorem the round's prevention claim should have been.

## What the round produced instead of its target

One requirement, machine-checked and cheap to apply: **a cut-time index carries
counterfactual weight only if the model has dynamics that run without the advisor.**
An index over a system that stops when the advisor stops is a reindexing of time. That is
now a standing bar in `RESEARCH_STATE.md` and the third sharpening of Q3.

## Priorities, decisions, outstanding actions

**Filed:** nothing. **Reworded:** Q3, with the failure and the bar. **Decisions taken:**
none.

**Outstanding maintainer actions.** One, and it is not new work:

1. **Whether to attempt the successor** — the same model with autonomous dynamics. It is
   the same question as whether Q3's target is worth another attempt, which is *what is
   worth proving* and already sits in `DECISIONS.md`'s queue under the Q3 entry. No
   separate line was added, deliberately: the queue should stay short, and this is
   evidence bearing on an entry already in it rather than a new decision.

## What this round does not establish

- **No corrigibility theorem, and no progress toward one.** The representation gap is
  open.
- **No claim the approach is wrong.** The collapse is a property of this model's
  dynamics. Whether a model with autonomous dynamics passes T1 is untested, and is
  recorded as a conjecture rather than an expectation.
- **Nothing about the source corpus.** Its sealed-sibling family consists of *continuing*
  deliberations; this model's cut freezes. The difference is the finding.
- **Nothing about forging, seizure or bypass** — not modelled, which is weaker than the
  roadmap requires of a protected channel.
- **Nothing about computational futurity or competence.** Q4, item 24 and item 25 stand
  exactly where they were.
- **The Cartesian-frames round is not weakened.** One intended *use* of `AgentInert` does
  not carry what was hoped; that is a fact about the use, not the result.
- **Nothing is registered.** The line has no registry, so it still establishes nothing by
  this repository's standard.

## Gates

`python3 tests/run.py`: all green — six project runners, seven gate self-tests, name lint
clean over 93 Markdown files, Lean sorry gate clean over 15 files, axiom discipline
present on every file.

`lake build Workspace.Deference.Contrib.TimeIndexedCapability`: **completed
successfully**. 18 declarations, `sorry`-free, each auditing to `[propext]` — a proper
subset of the allowed three. No new axioms, no `axiom` declaration, no change to any
pre-existing file's build status or axiom output.
