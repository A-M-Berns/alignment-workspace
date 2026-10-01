# Origin — the corrigibility note dump, 2026-10-01

**Status: `agent-consolidated`.** Ordinary content — editable and
reviewable, not machine-protected. The norm is that it is not tweaked. Edit it
when there is a reason, state the reason in the commit, and record substantive
edits in `DECISIONS.md`. Rewriting it to fit new work is not a reason.

## What it is

The record of a conversation between a maintainer and Claude, 2026-09-13 to
2026-10-01, testing the thesis that corrigibility is less anti-natural than the
standard arguments make it look once value change is represented as belief
change. In these files **the author** is that maintainer; **AUTHOR** marks the
author's words, quoted, and **CLAUDE** marks Claude's proposals and derivations,
which the author has not vetted.

| file | what it is |
|---|---|
| `corrigibility-discussion-outline.md` | the running record: the thesis verbatim, the ordered list of anti-naturality arguments, and the resolutions item by item with registers |
| `position-statement.md`, `-v2.md`, `-v3.md` | frozen snapshots of the thesis on 2026-09-13 and 2026-09-14, each written as the input to an agent run, with the checklists I1–I18, J1–J10 and K1–K10 |
| `corrigibility-bli-thread-and-early-questions-audit.md` | a second claude.ai thread (logical induction, Bayesian logical induction) mapped onto the record, and an audit of sixteen early questions |
| `value-change-as-epistemic-update.md` (and `.tex`, `.pdf`) | the four-picture note on item 1: value change as conditioning on a finer algebra, Good's theorem for value change, reflection versus no-expected-net-update |
| `fixtures/value_change_journey.py` | exact-`Fraction` recomputation of every number the note marks *computed*; `tests/run.py` runs it |
| `corrigibility-reading-list-v1.md` | the annotated reading list the discussion started from |
| `CITATIONS.md` | the third-party works the documents cite, with links |

The note's Appendix A and §5.1 cite `../../decision-theory/decision-problems-note-dump-2026-10-01/`,
received the same day.

## As received

| | |
|---|---|
| received | 2026-10-01 |
| archive sha256 | n/a — assembled in-repo from the author's working files, never an archive |
| tree sha256 at intake | `188db3014e6382e71112280dcc430e91e0d79bf07388e0420e759b3d1c69cc91` |
| files at intake | 12 |

## Intake deltas — what differs from the working files

- **Naming.** The author's name is replaced by *the author* throughout the
  Markdown, and the register tag that carried it by AUTHOR. Published works are cited by
  author name as before, and so are the two other researchers whose ideas the
  record credits (Sam Eisenstat for the meta-belief observation reading of
  superconditioning, Tim Parker for the v2.1 revision of the decision-problems
  notes). The Eisenstat attribution is the author's own, in his words in the
  thesis; the note's restatement of it keeps its unvetted flag. The PDF's byline
  names the author.
- **Links.** Obsidian `[[wikilinks]]` became ordinary Markdown links: to files
  in this tree, to `../note-dump-2026-08-11/notes/` for the two corpus notes
  cited, to the decision-problems tree, and to `CITATIONS.md` for third-party
  works. `CITATIONS.md` was built at intake from the metadata of the local
  copies the conversations read.
- **Local identifiers removed**: machine and session names, workflow run ids,
  and paths into the author's working tree.
- **Corrections.** In the Markdown note, eight section cross-references that
  still carried an earlier section numbering were set to the numbering the
  LaTeX already used, and the file map was rewritten for this tree. In the
  outline, two LaTeX commands that a tab character had corrupted (`\to`,
  `\text`) were restored. The fixture's docstrings carried the same stale
  section numbers and were corrected.
- **LaTeX.** The register macro and names were changed as above, Appendix A's
  source line now credits Tim Parker and points to the decision-problems tree,
  and the PDF was rebuilt from the edited source.
- **Added**: `tests/run.py`, `CITATIONS.md`, and this file.

## Not included

- **Two claude.ai threads** the record cites by file name,
  `2026-09-13__corrigibility-anti-naturality-opening__claude-ai-paste` and
  `2026-09-14__bli-thread-conditioning-vs-prior-overrides__claude-ai-paste`.
  They are a chat dump and are held for the author's read-through sign-off
  under `AGENTS.md`'s release gate.
- **The agent runs** the record describes: `workflow-2026-09-13/`,
  `workflow-2026-09-14/`, `workflow-2026-09-14b/`, and a run of 2026-09-25 on
  legitimacy-weighted deference. Labels of the form INDEX §C*n*, §D*n*, A*n*,
  R*n*, and the paths `plan/…` and `followup/…`, point into their outputs.
- **The local copies** of third-party texts, which this repository has no right
  to redistribute; `CITATIONS.md` links each one.

## Vetting status

Everything marked CLAUDE is unvetted by the author, as the files themselves
say. Nothing in this tree is registered in this repository's claims sense. The
fixture's checks are the only machine-checked content, and they check
arithmetic, not the note's arguments.

## What cites it

Nothing at intake.

## Checking this receipt

The tree hash is sha256 over LF-joined lines `<sha256(file)>␣␣<relative path>`,
sorted by path, excluding bytecode artifacts — and **this file**, which did not
exist in that form at intake. Recompute it that way and you learn whether the
tree has moved since it arrived. Nothing enforces that it has not: this is a
receipt, not a gate. The protection that remains is that this path is
specification layer in `tests/path_gate.py`.
