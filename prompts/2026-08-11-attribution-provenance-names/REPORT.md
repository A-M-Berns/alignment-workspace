# Attribution, provenance, names, missing round records — report

Dispatch: `PROMPT.md` beside this file, verbatim.

## Outstanding maintainer actions

1. **Supply the scrub round 2 dispatch.** Not recoverable from the repository;
   `prompts/2026-08-11-scrub-round-2/PROMPT.md` records the gap. Pasting the
   original over that file closes it.
2. **Supply the contributor-checkers dispatch.** Same gap, not in §D's scope:
   `prompts/2026-08-11-contributor-checkers/` has a report and no prompt.
3. **Decide whether the program gets a name.** The README now describes the work
   instead of naming it. Naming is reserved.
4. **Review `tests/name_lint.py`'s allowlist** if the maintainer set changes —
   `MAINTAINER_NAMES` is the single place to edit.

**Closed during this round:** the GitHub-side repository rename, outstanding from
PR #4. The maintainer performed it; the repository is `alignment-workspace`. This
round attempted it and was refused by the executing environment's permission
classifier, which blocks repository-settings mutations — worth recording, because
it means the settings-side half of any future rename is not something a round can
finish on its own.

## A. Attribution at pull-request level

The template gains a **Model attribution** section beside the DCO section, with
four options: human-written, executor model, dispatched round (prompt-author plus
executor), and `unrecorded`. AGENTS.md records that attribution lives at both
levels and that a squash merge must carry the section into the squashed message.

`tests/attribution.py` runs in the `dco` job. It reads the body from the workflow
**event payload**, not the API — no token, no network, consistent with the
zero-secrets rule.

**What it cannot check:** whether the attribution is true. No gate can tell which
model wrote a paragraph. It refuses the silent omission, which is the failure mode
actually seen — not a false claim but no claim at all. The docstring says this, as
the DCO gate's does.

**What it nearly failed to check.** The first implementation stripped the `- [ ]`
marker from unchecked options and tested the remainder for non-emptiness. Each
template option carries its own label text, so an untouched template left
"**Human-written** — no model produced…" behind and passed. A gate that accepts
the pristine template is ceremonial. The parse now drops the whole option
including wrapped continuation lines, and the seven cases — including the pristine
template — are a `--self-test` wired into CI, not a one-time check.

**One workflow change was needed.** The event payload is a snapshot from when the
event fired, and GitHub's "re-run jobs" replays that same snapshot. A contributor
who fixed the body after a failure would re-run and fail identically, with no way
forward but an empty commit. `pull_request` therefore now lists
`types: [opened, synchronize, reopened, edited]`. The cost is that title and body
edits re-run all eight jobs including Lean; removing `edited` reverts that and
reintroduces the trap.

## B. Provenance resolved to two fields

AGENTS.md's *Provenance* section now defines **generator** and **review status**;
the three-class table is gone. The *Identity* section, which had been the second
definition, now points at the first and keeps only the argument for why the fields
are separate. What the old section uniquely carried is preserved: unreviewed
content is allowed and must be labelled, and flagship documents may not remain
`ci-only`.

Dependent references:

| where | change |
|---|---|
| `PROVENANCE.md` | header rewritten; table column `class` → `generator` + `review status`; 13 rows converted; the `prompts/*/PROMPT*.md` and `prompts/*/REPORT.md` rows restated |
| `CONTRIBUTING.md` | reader rule 2, which defined the three classes |
| `README.md` | "most of this repository is `llm-unreviewed`" → `ci-only` |
| `.github/PULL_REQUEST_TEMPLATE.md` | the provenance section's field list |
| `AGENTS.md` external-citation sentence | **no change needed** — it already says "maintainer-reviewed" and names no class |
| scripts | **none** — grep found no script parsing class names; the only matches outside prose were Markdown |

`GOVERNANCE_REPORT.md`, `SETUP_REPORT.md` and `SCRUB_REPORT.md` say
`llm-unreviewed` and keep it. They are round records, and *no negative ontologies*
already settles that completed records keep the vocabulary that was true when
written.

## C. Names

**C.1.** README line 3 now describes the program: what makes an agent's normative
state accountable, and what makes deference to a principal stable rather than
merely imposed. No initials, no coined name.

**C.2 determination: the `DECISIONS.md` line is history and stays.** Three
reasons. It sits under a dated heading in *Settled*, whose stated function is to
record decisions and not re-litigate them. Nothing depends on it — grep finds no
document referencing it, and the README's line was a parallel statement rather
than a citation of it. And it is dated 2026-08-10, before the names-off posture
existed, so it records a decision genuinely made under different terms; the README
line was residue of it, not a live restatement.

The counter-argument, for the record: its heading reads "repository name and
**scope**", and the rename round edited it in place, which is not how a frozen
record is treated. That was mandated by *no negative ontologies*, and it changed a
project name rather than the substance — but it does show the ledger is not
strictly append-only, which weakens the "pure record" reading. If the maintainer
reads it the other way, it is one edit plus a dated entry.

**C.4. The lint.** `tests/name_lint.py`, wired into the existing `python` job and
into `tests/run.py` — deliberately not a new job, because CI job names are
required-check contexts and a ninth would need branch protection re-applied before
any pull request could merge. There is no `docs/lint` job to add it to; the
`python` job is the nearest existing home.

Scope: tracked Markdown, excluding `prompts/` and `frozen/`, exempting
`DECISIONS.md`, ignoring anything in backticks or fenced blocks. It caught two
passages in `SCRUB_REPORT.md` quoting a maintainer by name; both generalized. 37
files clean.

**What it does not catch:** non-Markdown files; a name split across a line break;
a name inside backticks, which is the deliberate exemption for handles, paths and
URLs and is therefore also a hole someone could write prose into; third-party
names, since it knows only the maintainer set; and any description that identifies
a person without naming them. It is a floor against the specific regression that
already happened, not a guarantee of anonymity.

## D. Missing round records

Two directories created, both marked reconstructed-after-the-fact with the date.

**`2026-08-11-public-flip-and-scrub/`** (PR #1). Recovered: the dispatch, which
was three short inline instructions during the branch-protection session, quoted
as given. The report is reconstructed from the pull-request body and three commit
messages, and states what is not recoverable — the round's own account of its
deviations. A report from a merged pull request can say what was done, never what
the round decided and did not write down.

**`2026-08-11-scrub-round-2/`** (PR #2). **The dispatch is not recoverable.**
`PROMPT.md` records that, quotes the fragments held in the session record — the
title, and the standing instruction the round worked from — and labels them as
evidence about the dispatch rather than the dispatch. Not paraphrased into
existence. The round's substantive report is not lost: `SCRUB_REPORT.md` was
written contemporaneously, so `REPORT.md` points at it rather than restating it.

A third gap, outside §D's scope: `prompts/2026-08-11-contributor-checkers/` has a
report and no prompt. Listed above.

## E. Claim classes

The template's claim-class comment now reads lean-proved / enumeration-verified /
witness-checked / contributor-checked / test-supported / conjectured, strongest
first, and notes that `contributor-checked` is capped by the invocation path
rather than by what the pull request declares.

## Gates

All green locally: name lint (37 files), attribution self-test (7/7), attribution,
dco, contrib hygiene, path gate, conservativity, check_frozen, repo runner,
checkers self-test (9/9), registries (3 entries). `py_compile` clean. The workflow
YAML is not parsed locally — PyYAML is not installed — so the two CI edits were
made as asserted string replacements and are validated by CI.

## Attribution

| | |
|---|---|
| prompt author | Claude Fable 5 (Anthropic) |
| executor | Claude Opus 5 (Anthropic) |
| date | 2026-08-11 |
