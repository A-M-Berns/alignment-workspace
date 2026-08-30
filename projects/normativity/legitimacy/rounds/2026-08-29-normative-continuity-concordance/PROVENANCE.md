# Provenance

## The checkpoint

`NORMATIVE_CONTINUITY.tex`, `NORMATIVE_CONTINUITY.pdf`, `PROOF_PASS.md` and
`src/fixtures.py` are the `AGENT-CONSOLIDATED` checkpoint received from the maintainer's
`~/Downloads` on 2026-08-29 and are not edited here; `ORIGIN.md` carries their digests and
the reason this pair, and not the three older `.tex` files beside it, is the checkpoint.
Generator of those four files: Claude Fable 5 (Anthropic), the hostile proof pass of
2026-08-29 (an interactive session, no `prompts/` round of its own; its prompt is quoted in
`PROOF_PASS.md` §1 and the present round's `PROMPT.md` §1). The synthesis they repair was
authored in the maintainer's chat sessions with GPT-5.6 Sol (OpenAI) and Claude
(Anthropic) on 2026-08-29; the earlier Answerable Process one-pager it consolidates is a
2026-08-28 Downloads artifact of the same kind, not a repository round.

## Frozen inputs

**None imported.** The Legitimate Evolution round is cited by path and quoted in
`CONCORDANCE.md`; no file of it is copied or modified. `src/fixtures.py` imports nothing
from any round.

## This round

| file or glob | generator | review status | date |
|---|---|---|---|
| `README.md`, `CONCORDANCE.md`, `THEOREM_MAP.md`, `ORIGIN.md`, `PROVENANCE.md`, `tests/**` | `prompts/2026-08-29-normative-continuity-concordance/` (executor: Claude Fable 5, Anthropic; prompt author: the maintainer with GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-29 |
| `lean/Workspace/Normativity/Contrib/NormativeContinuity.lean` | same | `ci-only` | 2026-08-29 |

The concordance's source quotations were gathered by a read-only subagent (Claude Fable
5) and checked against the files by the executor before use.

## New names introduced

All provisional under `AGENTS.md` §6: *issue trace* (`IssueTrace`), *standing trace*,
*reach gate* / *live gate* (`ReachGate`, `LiveGate`), *no-route wait* (`NoRouteWait`),
*wait responsive*, *non-starving*, `Grounded` (the inductive tree), `anchor_grounded`,
the fixture names `fixA`, `fixB`, `fixE`.

## What was computed rather than asserted

Every Lean claim in `THEOREM_MAP.md` was built with `lake build` in this tree and printed
its axioms. Every Python fixture claim is re-run by `tests/run.py`. The concordance's
classifications are readings, not computations, and are labelled as such.
