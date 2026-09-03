# Provenance

| files | generator | review status | date | originating round | chat bundle |
| --- | --- | --- | --- | --- | --- |
| `*.md`, `src/*.py`, `tests/*.py` | Claude Opus 5 (Anthropic); prompt author Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-02 | `prompts/2026-09-02-unified-grounds-answerable-defeat/` | none |
| `lean/Workspace/Normativity/Contrib/NormativeContinuity.lean` §5, and the deletion of §2 and §4.2 | Claude Opus 5 (Anthropic); prompt author Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-02 | same | none |

The dispatch names its executor `unrecorded`; the executor was in fact Claude Opus 5,
and it is recorded here rather than left blank, per `AGENTS.md` §Provenance.

## What this round consumed

**As hypotheses** (`depends_on` in `state/rounds.json`):

- `2026-08-30-normative-continuity-settlement` — the settled specification, revision 2.
  The unification is surgery on its Lean spine and preserves every theorem in it.
- `2026-08-30-answerability-carriers` — the join-semilattice load algebra and
  Slice-wise Conservation, restated here with the `disp` receipt at bottom.
- `2026-08-30-anchored-slices-auth-transfer` — the transfer/identity-frame machinery
  the disposal edge uses.
- `2026-08-31-normative-affordability` — F3 and the persistence criterion, consumed
  frozen. `κ^r_N` is defined on top of them; nothing in that round is edited.
- `2026-08-23-transition-certificates` — postulate 5's collapse, cited by content
  (row 5 of its `MEMO.md`, failure code `posterior-basis`, test
  `test_no_self_grounding_clause_exists_yet_the_attacks_fail`) and **narrowed** by this
  round's first finding.

**Cited, not consumed:** `2026-08-31-faithful-semantic-preservation` (the
authentication side of item 77, not used here); the September checkpoint's
`ANSWERABILITY_AND_SERVICE.md` §6 and `OPEN_PROBLEMS.md` §2 for why item 77's three
questions are one.

## What changed outside this directory

- `lean/Workspace/Normativity/Contrib/NormativeContinuity.lean` — §5 added;
  `StandingTrace`, `Licensing`, the inductive `Grounded`, and §4.2's
  `grounded_replay_admitted` / `grounded_replay_live` / `Adm` **deleted as primitives**
  and re-derived in §5. Header docstring updated; `#print axioms` block updated.
- `DECISIONS.md` — the Defeat Principle entry, and three items appended to
  *Awaiting the author*.
- `PRIORITIES.md` — item 77 annotated with what this round settled and what it left.
- `state/rounds.json` — the round record with `depends_on`.

## Web use

None. No web source was consulted, and in particular **the Horty prior-art check that
item 77 asks for was not performed** — see `REPORT.md` §5 and outstanding action 5.
