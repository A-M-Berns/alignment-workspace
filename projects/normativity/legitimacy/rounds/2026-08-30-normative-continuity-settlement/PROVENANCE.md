# Provenance

## Derived from the checkpoint

`NORMATIVE_CONTINUITY.tex` is revision 2 of the `AGENT-CONSOLIDATED` checkpoint in
`../2026-08-29-normative-continuity-concordance/` (digest there and in `ORIGIN.md`
here); the checkpoint is not edited. What changed and why: `ORIGIN.md`, the revision's
"Revision 2" paragraph, and `SETTLEMENT.md`. `src/fixtures.py` is byte-identical to the
checkpoint's.

## Frozen inputs

**None imported.** Legitimate Evolution is cited by entry number (A5, A11, A17, A21,
A34, S1) where a decision supersedes it; no file of it is copied or modified.

## This round

| file or glob | generator | review status | date |
|---|---|---|---|
| `README.md`, `SETTLEMENT.md`, `THEOREM_MAP.md`, `ORIGIN.md`, `PROVENANCE.md`, `NORMATIVE_CONTINUITY.tex`, `NORMATIVE_CONTINUITY.pdf`, `src/settled_model.py`, `tests/**` | `prompts/2026-08-30-normative-continuity-settlement/` (executor: Claude Fable 5, Anthropic; prompt author: the maintainer with GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-30 |
| `lean/Workspace/Normativity/Contrib/NormativeContinuity.lean` §4 (the settlement additions) | same | `ci-only` | 2026-08-30 |

## New names introduced

All provisional under `AGENTS.md` §6: *admitted occurrences* (`Adm_n`), *no permanent
wait* (`NoPermanentWait`), *share attention* (`shareAttention`), `IssueTraceCore`,
`mattersOf`, `toIssueTrace` (the realization), *matter bookkeeping* (the lemma), the
witness trace `W`, and the status label `NORMATIVE-CONTINUITY-MATH-SETTLED` with the
gloss the dispatch supplied.

## What was computed rather than asserted

Every Lean claim in `THEOREM_MAP.md` was built with `lake build` in this tree and printed
its axioms. The witness trace and every regression are run by `tests/run.py`. The
arguments of `SETTLEMENT.md` §1, §2 and §9 are readings and are labelled as such; the
incoherence of model B (§1) is an argument, not a formalized theorem.
