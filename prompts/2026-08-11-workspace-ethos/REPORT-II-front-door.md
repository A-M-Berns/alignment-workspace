# Report — ethos pass II, front-door consolidation

**Prompt author:** GPT-5.6 Sol (OpenAI). **Executor:** Claude Opus 5 (Anthropic).
**Date:** 2026-08-11. **Review status:** `ci-only`.
**Write scope:** documentation and front-door surfaces. No research claim,
theorem, epistemic class, definition or Stage IV artifact was changed.

The first pass's report is `REPORT.md` beside this file. This one covers the
front-door work and corrects two premises of its own dispatch.

## Two dispatch premises were wrong, and one changes the deliverable

**Stage III is not merged into `main`.** The dispatch says it is. `main` is at
`b7207e9` and is **30 commits behind** this branch; `git branch --contains` for
the Stage III commit returns only `round/2026-08-11-deference-corrigibility`.
Stages II, III and IV all live on this branch alone. Nothing in the pass depended
on the claim, but a front-door audit that assumed `main` was current would have
audited the wrong tree.

**Stage IV closed as a negative result while this pass was running, and its
persisted report contradicts the dispatch's description of it.** The dispatch
lists a provisional Stage IV status — a nontrivial future-agent model passing its
local gate, anti-collapse checks passing, model debt likely reduced — and says an
independent red team was still required. That red team ran, and the round was
stopped by it. Per the dispatch's own §20, the persisted final report governs over
an earlier status message, so this pass reconciled with `REPORT.md` and
`REPORT-red-team.md` in `prompts/2026-08-11-stage-iv-future-agent/`.

What actually holds: no future agent was constructed, the claimed-gate harness was
deleted, ten of its twenty-three checks could not fail, the dominance result is
Stage III's collapsed theorem with the arms swapped, and the round's positive
reading is withdrawn. **Had this pass written the dispatch's version of Stage IV
into the front door, it would have published a positive research claim that the
round itself had already retracted.** That is the exact failure the layer
distinction exists to prevent, arriving from the direction nobody watches — a
maintainer-authored prompt, not an agent's report.

## Recovery check

The first pass's changes are intact. `RESEARCH_STATE.md`,
`prompts/2026-08-11-workspace-ethos/`, `AGENTS.md`, `CONTRIBUTING.md`,
`README.md`, `prompts/README.md`, plus `PRIORITIES.md`, `DECISIONS.md`,
`PROVENANCE.md`, `tests/path_gate.py`, `.github/apply-branch-protection.sh`,
`projects/deference/notes/TERMS.md` and the removal of `GOVERNANCE_REPORT.md` are
all present and uncommitted. No semantic merge was required: `main` predates all of
it, and the deference rounds touched none of the same surfaces. **No
reconstruction uncertainty.**

## Before and after

### Before — what a fresh reader would have misunderstood

1. **That the deference line had not started.** Its landing page said `kernel/` was
   "reserved, and deliberately empty, for the finite deference kernel round", that
   the line "has no claim ledger yet", and described what would happen "when the
   first round lands". Four stages had landed.
2. **That the repository is a notes collection.** The root README opened on two
   research lines and a verification recipe, with nothing about how work flows,
   what has been ruled out, or why the layers exist.
3. **That `frozen/` machinery is live.** The pull-request template still asked
   contributors to tick `python3 tests/check_frozen.py`, a script deleted with the
   `frozen/` retirement. A contributor following the checklist hits a crash.
4. **That the deference line holds 155 theorems across 10 files.** The ledger and
   `TERMS.md` both said so; `Contrib/` holds 8 files and 167 theorem or lemma
   declarations. Both numbers wrong, in a headline sentence.
5. **That the FUD comparator work had a positive result.** `RESEARCH_STATE.md`'s
   worked example was written against Stage III's pre-review reading, and was one
   round stale before this pass began.

### After — what is recoverable directly

**The README was then rewritten again, on maintainer instruction, to depend on no
current research content at all** — no result, count, stage or open question. The
reasoning is the fourth defect below: this pass *itself* put a theorem count into a
front-door document and the count was stale the same day. A surface that describes
current content is a surface that is usually wrong, and the durable fix is to route
to `RESEARCH_STATE.md` rather than to summarise it. It is now split into *For
humans*, left blank as a stub because that is the one surface whose voice should be
the author's and not a model's, and *For AIs*, drafted: what binds an arriving
agent, that `ci-only` is the standing condition and endorsement may not be
inferred, the precedence order, that `prompts/` is history, what is reserved, and
the injection rule. All of it is structural and none of it drifts. `RESEARCH_STATE.md` opens with *Where the lines
stand*: per line, the question, the aspiration and the construction on both
registers, the controlling gap with its debt kind, and the next controlling
question — with the type-level obstruction stated as **argued, not proved**. The
deference landing page routes to the five notes documents, states plainly that all
of it is `ci-only` and that nothing is `workspace-established`, and points at the
two failed rounds as method.

**`GOVERNANCE_REPORT.md` is gone.** Moved under `prompts/` earlier in the pass,
then removed entirely on the maintainer's ruling. Its content is superseded and
lives in current surfaces — `checkers/README.md` and the checker docstrings, the
path gate, and the ledger entries that answered its four open questions. The one
thing that made deleting it non-trivial was repaired first: it was **both**
dual-register documents of the registered claim
`simplex.rational-points-sum-to-one`, now repointed to `checkers/README.md` and
`CONTRIBUTING.md`. Its round attribution survives in `PROVENANCE.md` and records
that no round record exists, which is a real and accepted loss.

### Intentionally preserved as history

Everything under `prompts/` mentioning `frozen/`, `check_frozen.py`,
`frozen-integrity`, `foundations-verification` or the old eight-gate set — roughly
sixty references across twenty round records. Those are correct records of what
was true when written, and *no negative ontologies* keeps supersession in git
history and `DECISIONS.md` rather than in annotations on the superseded document.
The settled `DECISIONS.md` entries describing the retired machinery stay for the
same reason. `projects/deference/notes/README.md`'s pointer to a not-yet-existing
`../CLAIMS.md` also stays: it is a live rule about precedence, and the ledger
explains in its first lines why the file does not exist.

### Still unresolved — compression debt that remains

- **The deference line has no claims registry.** Well over a hundred
  kernel-verified theorems, none registered, so by this repository's own standard
  the line has established nothing. Filed as friction; **not** fixed here, per the
  dispatch's §15.
- **Round records cannot be filtered for currency without the ledger.** A reader
  arriving at a report by path gets no signal that a later entry supersedes it.
  `prompts/README.md` states the rule; the artifacts carry no marking, deliberately.
- **The roadmap remains long.** Recovering the deference architecture still means
  reading it; only *status* is now compressed.

## Procedural-bloat red team

The pass was required to remove more confusion than process it added. It did,
measurably: `RESEARCH_STATE.md` went from 355 lines to **302** while gaining the
per-line current-state section, because three things were deleted.

1. **The abstract "state shape" convention.** It described a document shape in
   prose and the document then did not use it. The *Where the lines stand*
   sections now demonstrate it, and Stage IV's report used the shape without ever
   being told to, which is better evidence than a rule.
2. **The Interfaces section** — four bullets of supplies/does-not-supply for
   deference components. `TERMS.md` now carries "what it does **not** mean" per
   row, and the roadmap carries the originals. Three copies of one distinction.
3. **The worked A/C/G example.** Duplicated the deference section above it and was
   a round stale. Replaced by a pointer.

**One rule was deleted because it was wrong.** The first pass ruled two debt
categories out — formalization and verification — as redundant with the epistemic
class ordering. Stage IV's report reached for "formalization debt" anyway, in a
table it wrote unprompted. The prohibition is gone and the list is now explicitly
not closed: these are words for thinking with, not a controlled vocabulary. A
taxonomy that has to be enforced against the people using it is not earning its
keep.

**Two counts were deleted rather than corrected.** `TERMS.md` and the ledger both
asserted a theorem total that drifted within hours of being written — by my own
hand, in the first pass. Replaced with count-robust wording, keeping only the
number that carries meaning: zero registered. A canonical document that requires
manual number maintenance will be wrong most of the time.

**Declined again:** a status header on every note; a per-line `FRONTIER.md`; a
deprecation marker on superseded round records; any gate on layer or aspiration
metadata; a dashboard of current counts.

## Parallel safety

No Stage IV artifact was touched. `FUTURE_AGENT_SPEC.md`, the round directory, the
Lean modules and the harness are untouched by this pass; its own uncommitted
changes to them are its own. Item 25 and item 27 substance is unchanged.

One documentary change is adjacent and is declared: **`PRIORITIES.md` Q3 was
updated** to record that Stage IV sharpened it from an open question into a
near-impossibility, quoting the round's own §4 and carrying its "argued, not
proved" qualification. That is Q3's status changing because a round reported, not
a change to Stage IV.

The stale counts repaired in the deference ledger and `TERMS.md` are factual
repairs under `AGENTS.md` §14's dead-pointer exception, not reinterpretations.

## What this round does not establish

- No research claim originates here. The deference section of `RESEARCH_STATE.md`
  is compressed from that line's ledger and roadmap and defers to them; where it
  and they disagree, they win.
- **Nothing from Stage IV is canonized.** Its report is `ci-only`, its own
  positive reading is withdrawn, and the type-level obstruction is argued from an
  exhaustive check over one parameterisation rather than proved. The front door
  says so.
- The front-door audit covers the surfaces named in the dispatch plus the
  pull-request template. It is not a repository-wide link check.
- Whether the front door now works for an external researcher is untested. It is
  written for one; nobody has read it as one.

## Human review surfaces

Five, and only the first three are judgment rather than fact.

1. **The root README's description of the workspace** — "a working research
   repository on agent foundations, run mostly by AI agents under a maintainer's
   direction", and the four-question framing. This is the sentence an external
   reader forms their impression from.
2. **The deference aspirational-versus-constructed gloss** in `RESEARCH_STATE.md`,
   in particular the constructed philosophical claim: *a valuation over realisation
   maps cannot distinguish who authorised an action, so the question cannot be
   settled in that register* — and that nothing established bears on whether
   transferring jurisdiction is justified.
3. **Q3's reclassification** from open question to near-impossibility.
4. Mechanical: the stale counts, the pull-request template line, the landing pages.
5. Mechanical: the three deletions in the bloat pass.

## Outstanding maintainer actions

1. **Nothing new is reserved.** The queue in `DECISIONS.md` is unchanged at one
   entry — read `checkers/`.
2. **Split the commit.** Two rounds' work sits uncommitted in one tree. This pass
   is `README.md`, `RESEARCH_STATE.md`, `AGENTS.md`, `CONTRIBUTING.md`,
   `PRIORITIES.md`, `DECISIONS.md`, `PROVENANCE.md`, `prompts/README.md`,
   `tests/path_gate.py`, `.github/apply-branch-protection.sh`,
   `.github/PULL_REQUEST_TEMPLATE.md`, `projects/leverage/CLAIMS.md`,
   `projects/deference/README.md`, `projects/deference/notes/README.md`,
   `projects/deference/notes/TERMS.md`, the ledger's count sentence,
   the removal of `GOVERNANCE_REPORT.md`, and `prompts/2026-08-11-workspace-ethos/`.
   **This resolved itself**: Stage IV committed its own work at `73beaf2` while this
   pass was closing, so everything now uncommitted is this round's and `git add -A`
   is safe.
