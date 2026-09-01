# Origin — the September 2026 normativity checkpoint

**Status: `agent-consolidated`.** Ordinary content — editable and reviewable, not
machine-protected. The norm is that it is not tweaked. Edit it when there is a
reason — a correction, a scrub, a supersession — state the reason in the commit, and
record substantive edits in `DECISIONS.md`. Rewriting it to fit new work is not a
reason; that work belongs in a new round, and this tree is superseded by a later
checkpoint rather than rewritten into one.

## What it is

The consolidation of the normativity / diachronic-answerability / legitimacy program
as it stood on 1 September 2026: a minimal current theory with an audited dependency
spine, a status ledger over fifty-seven results and interfaces, a supersession map, a
roadmap, sharply scoped open problems, the reconciliation of the conceptual
answerability theory with the service mathematics, an assessment of the candidate
legitimacy decomposition, the reconciliation with the August 9 consolidation, and a
self-administered audit against sixteen questions a fresh agent should be able to
answer from canonical documents alone.

Its purpose is that nobody should have to reconstruct the theory by reading research
rounds in date order. If that is ever necessary, this tree has a gap and the gap is
the bug.

## What is frozen here, and what is deliberately not

**Frozen: this tree.** It is a record of what the program held on a date, which is
the only thing that makes *"which of two conflicting statements is current"*
answerable at all. A checkpoint that later rounds amend in place stops being that.

**Not frozen: `wiki/`.** The human-facing register is expected to move as
understanding does, and is never permanently frozen. Freezing a checkpoint freezes a
record; an explanation must stay free to improve. The wiki pages that carry this
material — Serviceability, Diachronic Answerability, Liability and Affordability,
Progress, Actionability and Normative Force, Why Normativity?, Prior Art — are
outside this tree and outside this status.

**Not frozen: the research rounds** under `projects/normativity/legitimacy/rounds/`.
They are provenance and were never this tree's to edit.

**Future work builds on this rather than into it.** A later consolidation is a new
checkpoint that supersedes this one.

## Provenance

Not an external intake. This tree was produced inside the repository by a dispatched
consolidation pass and carries no archive or tree digest, because there was no
archive: `PROVENANCE.md` beside this file records what was read, what was judged
rather than inherited, the one external input, and the web use.

| | |
|---|---|
| produced | 2026-09-01 |
| generator | Claude Opus 5 (Anthropic) |
| review status | `ci-only` — no maintainer has vouched for the content |
| dispatch record | `prompts/2026-09-01-normativity-consolidation/` |
| frozen by | `DECISIONS.md`, 2026-09-01, *the September checkpoint freezes at merge; the wiki never does* |

Three passes made it: the consolidation itself, a cleanup pass removing internal
inconsistencies, and a pass landing six maintainer decisions. All three are in this
branch's history with their reasons.

## One known future edit

The **naming audit** over the program's provisional names is outstanding and
maintainer-owned. When it lands it will edit this tree, which is a maintainer act
with a stated reason and is what the norm permits — noted here so it does not read
as a violation of the freeze.

## Verification

No fixtures live here; the tree is prose over work verified elsewhere. Its pointers
are checked by `tests/dead_pointers.py` and `tests/untracked_pointers.py`, its
provisional names by `tests/name_lint.py`, and its round record by
`checkers.workspace_state`. The exact-rational fixtures it describes belong to the
rounds it cites and run under `python3 tests/run.py`.
