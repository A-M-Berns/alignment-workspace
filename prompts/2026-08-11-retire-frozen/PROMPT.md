# ROUND — retire `frozen/`, adopt `agent-consolidated`

Extends the governance architecture; AGENTS.md rules apply. Read from the public
repo after `patch/priorities-and-slop` merges. Confirm current state yourself.

## What changes and why

`frozen/` treats four trees as immutable inputs, enforced by a CI gate on hash
drift and a manifest-update rule. The maintainer's decision: the received work
becomes ordinary content inside the two research lines, and the discipline that
replaces immutability is a **status**, not a wall.

The reasoning, recorded so the trade is visible in the ledger rather than
implicit. What the freeze bought: a stable citable path, a record of what each
tree was when received, and protection against an agent quietly rewriting the
corpus. What it cost: every legitimate change — the two scrub rounds already —
had to go through a manifest procedure, and material that is the *starting point*
of ongoing work was structurally forbidden from being worked on. The first two
benefits do not require immutability; they require a **receipt** (the hash at
intake) and a status that says *do not casually edit this*. Only the third
requires a wall, and the wall is aimed at a failure — an agent silently rewriting
inherited notes — that the path gate, review, and git history already make
visible.

Keep the receipts. Drop the wall.

## A. Move the trees

- `frozen/consolidation_aug9/` -> `projects/leverage/consolidation-aug9/`
- `frozen/deference-note-dump-2026-06-27/` -> `projects/deference/note-dump-2026-06-27/`
- `frozen/dose-response-note-dump-2026-07-02/` -> `projects/deference/dose-response-note-dump-2026-07-02/`
- `frozen/references-citations-2026-08-11/` -> alongside the note dumps in
  `projects/deference/`, since it supersedes their `references/` payloads

`git mv`, preserving content exactly; this round changes no bytes inside any tree.
Update every reference — seventeen tracked files mention `frozen/`, including
`tests/path_gate.py`, `tests/name_lint.py`, `checkers/`, `AGENTS.md`,
`CONTRIBUTING.md`, `README.md`, `PRIORITIES.md`, `PROVENANCE.md`, both project
READMEs, `projects/leverage/CLAIMS.md`, and the PR template. Reports under
`prompts/` keep their paths as written; they are records.

`frozen/MANIFEST.md` and `FROZEN_INPUT_CHECKSUMS.json` do not survive as such —
their content moves per B.

## B. Receipts, not a gate

Each moved tree gets an `ORIGIN.md` at its root recording what the manifest
recorded: what it is, where it came from and when, the sha256 of the archive as
received, the tree hash at intake, one line on what cites it, and — for the note
dumps — the redistribution note about third-party material and the scrub history
by date. This is a receipt: it says what the tree was when it arrived, so a later
reader can tell whether it has moved since. Nothing enforces that it has not.

Retire `tests/check_frozen.py` and the `frozen-integrity` job.

**Sequencing that will bite you if missed:** `frozen-integrity` is one of the
eight required status checks in branch protection. A required check that no longer
reports blocks every pull request permanently. Update
`.github/branch-protection.json` and re-apply protection via
`.github/apply-branch-protection.sh` as part of this change, and confirm by
querying the branch's protection that the required-check list matches the CI job
list exactly. Report both lists.

## C. `agent-consolidated` status

Add to AGENTS.md, in the same section as the epistemic classes but distinct from
them — this is a status about how a document is *treated*, not about what is
established:

> **`agent-consolidated`.** A tree produced by a consolidation round, or received
> as a settled bundle, and treated as done. It is ordinary content: editable,
> reviewable, and not machine-protected. The norm is that it is not tweaked.
> Edit it when there is a reason — a correction, a scrub, a supersession — state
> the reason in the commit, and record substantive edits in `DECISIONS.md`.
> Rewriting a consolidated tree to fit new work is not a reason; that work belongs
> in `forward/` or a new round directory, and the consolidated tree is superseded
> by a later one rather than rewritten into it.

Mark each moved tree `agent-consolidated` in its `ORIGIN.md` and in `PROVENANCE.md`.
Contributors do not edit consolidated trees at all: add the paths to the
specification-path list in `tests/path_gate.py`, which is where the protection now
lives — visible and reviewable rather than hash-enforced.

## D. The self-verification job stays

`foundations-verification` runs the consolidation own verifier and is the one
piece of the frozen apparatus that carries real information: it tells you whether
the consolidated results still verify in a current environment. Retarget it to the
new path, drop its second step (the removed hash check), and rename the job
honestly — it no longer verifies anything *frozen*. Keep the run-from-a-copy
pattern.

Consider proposing, not deciding: this job is a slow gate against an input that
now changes only deliberately, so a schedule plus runs on toolchain and CI changes
may serve better than every push. If you propose it, the required-check list
changes again, so raise it as an outstanding action rather than doing it here.

## E. No residue

Per *no negative ontologies*: no `frozen/` stub, no "formerly frozen" phrasing in
living documents, no vocabulary in AGENTS.md or CONTRIBUTING.md that presumes an
immutable tier. The word "frozen" survives only in `prompts/`, in `DECISIONS.md`
history, and inside the moved trees own text where it is those documents own
wording. Report any place where removing the concept left a rule with a hole.

DECISIONS.md: a dated entry recording the retirement, with the trade above stated
in two or three sentences.

## Report

ROUND_REPORT.md per convention, **Outstanding maintainer actions** first. Include:
the full reference-update list; the before/after required-check lists with the
protection query that confirms them; every gate re-run after the move, including
that `path_gate` now covers the consolidated paths and was exercised, not merely
green; and any rule left with a hole by E.

---
Prompt author: Claude Fable 5 (Anthropic), 2026-08-11, in a maintainer-directed
session. Dispatched by the maintainer.
