# PATCH ROUND — attribution, provenance, names, and a missing round record

Extends the governance architecture; AGENTS.md rules apply. Read from the public
repo at `917c7da`. Confirm current state yourself; pointers below are not a spec.
Five items, all in root documents and CI scripts, dispatched together because they
collide.

## A. Model attribution at pull-request level

Commit trailers work — `Model:` and `Prompt-author-model:` are on recent commits.
The gap is the pull request: a reviewer sees no attribution without opening each
commit, and a squash merge can drop trailers into a body nobody wrote
deliberately.

1. `PULL_REQUEST_TEMPLATE.md`: add a **Model attribution** section beside the DCO
   section — they are the same kind of assertion. It asks for one of: human-written
   (no model); the executor model; or, for a dispatched round, executor plus
   prompt-author. State that `unrecorded` is correct where the executor is
   genuinely unknown, and that guessing is worse.
2. AGENTS.md model-attribution paragraph: attribution is recorded at both levels —
   per commit as a trailer, and once in the pull-request body. A squash merge
   carries the attribution into the squashed message.
3. CI: extend `tests/dco.py` or add a sibling wired into the same job that fails
   when the PR body has no non-empty Model attribution section. Check presence and
   non-emptiness; say in the docstring, as the DCO gate already does about itself,
   that this checks an assertion was made and not that it is true. If the PR body
   is unreachable in the current workflow context, report that rather than forcing
   it, and say what you would need.

## B. Two provenance schemes are live at once (the real conflict)

AGENTS.md carries the three origin classes (`human` / `llm-reviewed` /
`llm-unreviewed`) around line 145, and the two-field scheme — **generator** plus
**review status** (`maintainer-reviewed` / `ci-only`) — around line 450. The
governance round introduced the second to replace the first, because the
three-class scheme cannot express an external contributor's work. Both stand in
the binding document, so the repository does not have a provenance scheme; it has
two.

Resolve to the two-field scheme. Rewrite the earlier section to define generator
and review status, delete the three-class table, and update every dependent
reference: `PROVENANCE.md`, the PR template's provenance section, the
external-citation sentence if it names a class, and any script parsing class
names. Keep what only the first section carries — unreviewed content is allowed
and must be labelled, and flagship documents may not remain unreviewed.
DECISIONS.md records the supersession; the document itself keeps no trace of the
old scheme.

## C. The program is still named after two people

`README.md` line 3 reads "the working monorepo for the Berns–Demski research
program", against the standing names-off decision.

1. Rewrite it as a description of what the program is, in the register the README
   already uses. Do not substitute initials or coin a lab name — the program has
   no name, and naming it is reserved to the maintainer.
2. `DECISIONS.md` carries the same phrase. Judgment call, to be made by reading
   and reported: if that line is a **dated record of what was decided**, it is
   history and stays — the ledger is where history lives. If it functions as the
   repo's **standing scope statement** that other documents rely on, rewrite it and
   note the change in a new dated entry.
3. Leave handles and URLs alone: `CODEOWNERS`, `tests/path_gate.py`, the FAF
   dependency URLs, `.github/apply-branch-protection.sh`, `SETUP_REPORT.md`, and
   the DECISIONS entry recording the second maintainer joining. Handles and URLs
   are infrastructure, not prose about a program.
4. Add a name lint to the existing docs/lint job, or a small script it calls:
   scan tracked Markdown outside `prompts/` and `frozen/` for the maintainers'
   personal names; allow `DECISIONS.md` (ledger) and allow GitHub handles
   anywhere. Keep it small and easy to update when the maintainer set changes, and
   do not make it a spec-path dependency for contributors. The reason this is a
   lint and not a memo: the licensing round's residue sweep reported clean while
   this line sat in the README, because it searched for change-memorial phrasing
   and not for the other standing decision. If it cannot go in cleanly, say so and
   report what you would add instead.

## D. Two rounds have no record under `prompts/`

`prompts/` holds five round directories. PR #1 (go public, protection, first
scrub) and PR #2 (scrub round 2) have none, though AGENTS.md requires every round's
PROMPT.md and REPORT.md to be committed there. The dispatch-provenance trail has
two holes in its first week.

Create both directories from the material that exists — the maintainer supplies
the dispatched prompts; the reports can be reconstructed from the PR bodies and
commit messages, clearly marked as reconstructed-after-the-fact with the date, not
presented as contemporaneous. If a prompt is unavailable, record that rather than
paraphrasing one into existence.

## E. Stale claim-class list

The PR template's claim-class comment omits `contributor-checked`. Update it to the
full ordering.

## Report convention change (apply to your own report)

When a round reserves an item to the maintainer, the report lists it under
**Outstanding maintainer actions**, not only in prose. The GitHub-side repository
rename is the live example: #4 renamed everything in-repo and correctly left the
settings-side rename to the maintainer, but nothing in the report surfaced it as
an outstanding action, so the repository is still `alignment-workstudio` on GitHub
while two files point at `alignment-workspace`. Add the convention to AGENTS.md,
and list under it, for this round, anything you leave to the maintainer.

## Report

ROUND_REPORT.md per convention: the attribution gate and what it cannot check; the
provenance resolution with its dependent-reference list; the §C.2 determination
with reasoning; the name lint and what it does not catch; what was and was not
recoverable for §D; and the outstanding-actions list.

---
Prompt author: Claude Fable 5 (Anthropic), 2026-08-11, in a maintainer-directed
session. Dispatched by the maintainer.
