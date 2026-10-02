# Prompt — 2026-10-02-graph-prototype

The round that built the argument map under `graph/` and its checker, run from the maintainer's private workspace as a sequential Workflow of five agents (spec, checker, fixtures, docs, cold review) followed by three single-agent passes (repair, v1, fill). The common preamble every agent read, then each mandate, verbatim apart from Obsidian links rendered as code spans.


---

<!-- 00-common.md -->

# Common instructions for the 2026-10-02 implementation round

## Purpose
Build the first working version of the argument-map system, as a staging tree at `research/prioritization/graph-prototype/` laid out exactly as it will land in the public repository `research/alignment-workspace/` (which is read-only for you): `graph/` (frame, nodes, events, policy, proposals, derived, tasks, view), `chats/` (archive format only; empty here), `checkers/graph.py` (the checker, importable as `checkers.graph` beside the existing `checkers/` package), `tests/test_graph.py`, and `graph/PROTOCOL.md` plus an `AGENTS.md` section draft. The orchestrating session moves the tree upstream once the checker passes on the fixtures; nothing you write is public yet, but write it as if it were.

## Authority, in order
1. `research/prioritization/notes/rulings.md`: rulings 1–29 and corrections C1–C2. **Binding.** Where any design note disagrees with a ruling or a correction, the ruling wins and the note is out of date (in particular: ruling 28 makes expected utility the only value; presets are status rules only; ruling 27 defines the outside option; C2 withdraws the ±1 claim-truth value as a value; C1 removes the hard viability threshold from the act; ruling 21 removes second-person admission; ruling 12 says approval mints no level; ruling 26 says agents consult users on presentation).
2. `notes/protocol-draft-v1.md`: the protocol as last written for contributors; follow its file layout, node/event/frame/policy schemas and task kinds except where a ruling or correction overrides them, and say in `BUILD.md` where you deviated and why.
3. `notes/loop-spec-v2.md` and `notes/ranking-design-v3b.md`: the detailed interfaces and the ranking; apply C1 and C2 to the ranking: value the act smoothly on the outcome scale with the default-trajectory outside option; the frontier continuation is optional and off by default; do not rescale the decision term ad hoc (report both terms separately and combine by a documented rule the user can see).
4. The fixtures' sources: `notes/example-C.md` (fifteen deference nodes) and `notes/example-A.md` (instrumental-convergence cluster); the deference wiki pages under `research/wiki/` and the upstream note dump under `research/alignment-workspace/projects/deference/note-dump-2026-08-11/` for statements and sources.

## Build rules
- Python 3.12 standard library only; exact `fractions.Fraction` wherever a number is compared with a threshold or summed into a status (upstream AGENTS.md rule 2); floats allowed inside the ranking's value-of-information estimates, which are advice, not claims.
- The checker refuses, never repairs: a node file containing a level, credence or status; a derived field typed by hand; an event whose records do not resolve (records are optional in the prototype and checked only when present); unknown kinds or roles; cycles.
- Everything derived goes to `graph/derived.json`; views are regenerated, never edited.
- **Dialogue and malleability (ruling 29).** The agent-facing text you write must strongly encourage an agent to ask its user whether a thing makes sense before and after acting, to propose design revisions when use shows a problem, and to log every design change and every rolled-back edit in `graph/DESIGN-LOG.md` with a one-line reason, so that harm from malleability (rollbacks, user confusion) can be noticed and the encouragement scaled back later. Per ruling 26 the agent asks each user about presentation preferences unless a user-specific CLAUDE.md or AGENTS.md in context already records them.
- Memory: this machine has about 6 GB and one out-of-memory kill ends every session. Keep tests small (the two fixtures, under a few thousand enumerated worlds); no parallel heavy processes.
- Read-only inside `research/alignment-workspace/`; write only under `research/prioritization/graph-prototype/` and `research/prioritization/notes/` (your BUILD or report notes). Deliverable filenames must not begin with REPORT, SUMMARY, FINDINGS or ANALYSIS. No state-changing `git`.
- Writing for humans follows `research/alignment-workspace/AGENTS.md` *No negative ontologies* and the self-contained rule: define terms where used; no references to design rounds or earlier versions; hard-wrap the files that will live upstream to match that repository's style; no personal names in evaluative prose (Abram may be named as maintainer); Markdown links, not wikilinks.

## Return value
A script reads your final message: return the structured summary requested.


---

<!-- build-spec.md -->

# Mandate: BUILD.md, the implementation specification

Deliverable: `research/prioritization/graph-prototype/BUILD.md` (under 300 lines).

Write the specification the coder will implement: the directory layout; every file format as a schema with a complete example (frame.yaml, a node file for each kind including `cases` rows and `choose`, an event line, policy.yaml, a proposal file); the checker's refusal rules as a numbered list; the derivations in order (levels V and J from events; status per preset rule; proof sets; load; values as expected utility only with the outside option; the map term and the decision term as separate numbers; the ranking and the scoped query; the task list and the view); the test plan on the two fixtures (what the deference graph's first task list must be, taken from the rulings and the examples, and what the instrumental-convergence cluster's attack chain must do when the Turner 2024 picture is filed and when a response is filed). Mark each item Decided (cite the ruling number), Default, or Open. Where protocol-draft-v1 and a ruling disagree, follow the ruling and list the deviation in a final section.


---

<!-- checker.md -->

# Mandate: the checker

Deliverables: `research/prioritization/graph-prototype/checkers/graph.py`, `.../checkers/__init__.py` if needed for import, `.../tests/test_graph.py`, runnable as `python3 -m checkers.graph --root <tree>` (lint, derive, write derived.json/tasks.md/view.md; exit non-zero on any refusal) and `python3 -m checkers.graph --self-test`.

Implement `BUILD.md` exactly; where it is silent, follow the authority order in 00-common.md. Keep it to a few files and under about 1500 lines total; stdlib only. The ranking is version 0: exact over the fixtures, map term and decision term reported separately per unit with the documented combination rule, window-only, frontier off by default behind a flag; scoped query by node id. Write the tests first for the refusal rules, then for the derivations on a tiny synthetic graph, then on the fixtures once they exist (the fixture agent runs after you; leave fixture tests that read whatever `graph/` contains). Run everything you write.


---

<!-- docs.md -->

# Mandate: the documents that live with the graph

Deliverables under `research/prioritization/graph-prototype/`: `graph/PROTOCOL.md` (the protocol as it will be read in the repository: derived from `notes/protocol-draft-v1.md` with rulings 26–29 and corrections C1–C2 applied, every "decided/default/open" register kept, paths made real, hard-wrapped; under 500 lines; glossary kept), `AGENTS-graph-section.md` (the section to be added to the repository's `AGENTS.md`: what an agent may do alone against `graph/`, what it must pose to its user, the dialogue-and-revision encouragement and the DESIGN-LOG duty of ruling 29, the presentation-preference rule of ruling 26, the public-by-default rule of ruling 17 with handles, and the no-second-person rule of ruling 21), `graph/DESIGN-LOG.md` (format and first entry: what was built, dated), and a `graph/README.md` of one screen that tells a newcomer with a coding agent what to do first. Read `BUILD.md` and the checker's `--help` output so the documents describe what exists.


---

<!-- fixtures.md -->

# Mandate: the two fixtures

Deliverables: node, frame, policy and event files under `research/prioritization/graph-prototype/graph/` for (1) the deference program's fifteen nodes from `notes/example-C.md`, re-expressed under rulings 10, 16, 27, 28 (the prose-proof leaf as a `cases` node with pictures U, D and a residual; the program as a plan root with a sub-frame if BUILD.md provides one, otherwise as a plan; a gestalt credence on the plan root; the outside option set on the frame; failure classes left untagged where the story is "the program does not pay off"), with every statement checked against its source in `research/wiki/` or the upstream note dump and quoted in the Source section; and (2) the instrumental-convergence cluster from `notes/example-A.md` with the Turner 2024 picture filed and the Krakovna–Kramar response filed, both as a contributor's own filings (ruling 21). All credences and weights are illustrative and marked so in the event lines' `gloss`. Run `python3 -m checkers.graph --root research/prioritization/graph-prototype` until it passes; where the checker refuses something the fixture needs, write the gap into `graph-prototype/FIXTURE-NOTES.md` rather than editing the checker. Record what the first task list says.


---

<!-- mandate-fill.md -->

# Mandate: fill the starting graph with AI numbers (ruling 34), 2026-10-02

Read first: `research/prioritization/workflow-2026-10-02/00-common.md` (follow it), `research/prioritization/notes/rulings.md` (rulings 10, 16, 21, 25, 27, 28, 32, 34 and C1–C2), `graph-prototype/graph/PROTOCOL.md` (§2 nodes and pictures, §3 ladders, §4 value, §5 events; the event field table), `graph-prototype/graph/README.md`, `graph-prototype/graph/frame.yaml`, every file under `graph-prototype/graph/nodes/`, and `graph-prototype/graph/tasks.md` as the checker currently writes it.

The author ruled (34): "we need to fill in numbers on the graph with AI to start, and humans can vet as we go … humans should just revise the numbers when they seem wrong." You are the AI that fills them. Your handle is `@smithy-verity` (already in `policy.yaml`). Work only under `research/prioritization/graph-prototype/graph/events/` (your ledger `smithy-verity.jsonl`) plus regenerating the derived files with the plain run; do not edit nodes, the checker, tests or documents — if the checker refuses a shape you need, record it under `open` instead of changing code. Commit nothing. One checker run at a time; no Lean.

## What to judge, and how

1. **Every leaf statement in the graph** gets an `estimate` with a range (not a point) and a `gloss` that gives your reasoning in two to five sentences, citing what you read. Read the sources the node file points to before judging: for the deference cluster, `research/li-deference.md`, the `research/wiki/` pages the nodes name, and the clean-room results in `research/faf-cleanroom/cleanroom-digest.md` §2 and §4 (kernel-checked refutations and proofs are the strongest evidence you have; say when a Lean result settles a leaf, and say which reading it settles); for the instrumental-convergence and corrigibility clusters, the references the nodes cite (Turner et al. 2021/2024, Krakovna–Kramár, the corrigibility outline at `research/corrigibility/corrigibility-discussion-outline.md`). Where a source is missing, say so in the gloss and widen.
2. **Every table row** (the pictures of each `cases` node, including the two valuation nodes' rows only if the protocol lets a non-maintainer judge them — it does not for the author's ruled weights; leave those) gets your weight and conditional as the protocol's event shapes allow for an AI handle. Residual rows take the remainder. If weights or conditionals have no AI-writable shape, record that under `open` and give the numbers in the gloss of an `estimate` on the picture statement so a human can transcribe them.
3. **Every root and sub-frame step** gets a `gestalt` with a range and reasoning, written after the leaves, and your gloss says where your gestalt departs from what the leaves would derive and why.
4. **Calibration.** Ranges reflect your actual uncertainty; do not centre on 0.5 out of caution, and do not narrow below what you can defend. Where the node's statement is ambiguous between readings, say which reading you judged. Mark attribution questions (ATTRIBUTION-UNVETTED) where your evidence is about a person's intent.
5. Run the plain checker; fix any refusal in your own ledger; the four committed files regenerate. Confirm the task list now leads with human tasks (vetting, admitting rows) rather than gestalts, and copy the commit line into your report.

## Report (structured): `headline`; `events_written` (count by kind); `leading_tasks` (the first eight ranked units as the checker prints them); `commit_line`; `strongest_moves` (five leaves whose number a Lean result or a source settled, with the Lean name or citation); `widest_uncertainties` (five leaves you could not narrow, and what would narrow them); `open` (shapes the checker refused, rows you could not judge); `for_abram` (only what needs the author: numbers you expect him to disagree with, with your reason, self-contained and with terms defined in place).


---

<!-- mandate-repair.md -->

# Mandate: repair the graph prototype after the cold review (2026-10-02)

Read first, in this order: `research/prioritization/workflow-2026-10-02/00-common.md` (and follow it), `research/prioritization/notes/prototype-review-2026-10-02.md` (the review you are answering), `research/prioritization/graph-prototype/BUILD.md`, `graph-prototype/graph/PROTOCOL.md`, `graph-prototype/graph/README.md`, `graph-prototype/checkers/graph.py`, `graph-prototype/tests/test_graph.py`, `graph-prototype/FIXTURE-NOTES.md`. The rulings ledger `research/prioritization/notes/rulings.md` is the authority where the review and the documents disagree about intent; do not invent rulings.

Work only under `research/prioritization/graph-prototype/`. Do not touch `research/alignment-workspace/`. Commit nothing; the orchestrator commits. Keep memory modest: run the checker on one tree at a time, never in parallel; never launch Lean.

## Must do

1. **World model scales.** Enumerate per connected component of leaves (components joined by shared leaves across roots), combining components by independence, so the fixture plus any new table or row passes without touching a cap. Keep a cap per component, state it in PROTOCOL §4 and README with the refusal as a numbered rule (`13`, "component too large", naming the root and the count). Prove it on the review's own case: copy the review's added files from `workflow-2026-10-02/artifacts/review-copy/graph/` (the `a2-monotone-in-resources` table, its two pictures, the reviewer ledger and handle) into a scratch copy of the fixture under your scratchpad and show the run passes with the statuses the review saw in its diagnostic copy. Add a test that files such a table on the shipped fixture and passes.
2. **Generated files are flag-independent; logs are separable.** `tasks.md`, `view.md`, `derived.json`, `versions.json` render identically whatever `--why`, `--as`, `--scope` are given; per-user and scoped renders go to stdout or to an uncommitted path named in the output. `WARN`/`OK`/`REFUSE` lines go to stderr; `--dry-run` prints parseable JSON to stdout only and the README says what it is for (and offers the way to see the task list without writing). `versions.json` carries a `generated_hash` and a hand edit is refused under rule 7. The digest reports root status flips, including flips through preset budgets. Fix the failing shipped test by the stderr change, not by loosening the test. The README's "must print OK" sentence becomes true (the registry WARN is explained or moved).
3. **Close the vocabulary gaps.** PROTOCOL gets: a table of refusal rules 1–13 with one line each; the event id convention (unique across all ledgers, and a per-handle prefix rule so two contributors' pull requests do not collide, enforced by the checker); the full event field list, marking which fields the checker reads; the policy keys the fixture carries (`maintainer`, `illustrative`, `reask_days`, `time_tested_years`) with what reads them or "reserved"; the node fields `installment`, `tag`, `supersedes`; the `rule` value format; the ranked-unit line vocabulary (`load`, `bears on`, `weakest proof-set leaf`, `cross-audit preferred`, size letters, rate). Terms in the review's "Terms I had to guess" list each get a definition where first used.
4. **Review items 2, 5, 6, 7, 10, 11, 12, 13, 15** are fixed in code or documents so that the two agree; say which way each went in the DESIGN-LOG entry.
5. **Review items 4, 8, 9, 14** need a decision. Take the Default that keeps the documents' stated intent (rulings: 12 approval mints no level; 16 gestalts; 27/28/C2 value; refuted and conceded nodes stay live by default) and record each as a dated `change` line in `graph/DESIGN-LOG.md` with a one-sentence reason, marked `Default` so the author can overrule: 4 — a root with a derived probability gets no gestalt unit ranked; it is listed unranked as "no gestalt yet"; 8 — anchor 14 requires an `external` event logged by a handle other than the Statement's author, and the documents say what clears the attribution flag; 9 — a conceded plan is not a leading candidate; the commit line names the best non-conceded plan or says there is none, and the outside option's `null` utility prints as "unplaced" with the plan values shown as intervals over the whole scale, as C2 and ruling 27 imply; 14 — a range judgment on a leaf that becomes a table is marked `stale: leaf became a table` and listed under the residual row as a suggestion, not used.
6. Run `python3 -m unittest discover -s tests` and `python3 -m checkers.graph --self-test` and the plain run on the fixture; all green. Update `BUILD.md`'s deviations list and `FIXTURE-NOTES.md` where your changes close a listed gap.

## Report (structured result)

`headline` (one sentence), `changed_files` (list), `fixed_items` (review item numbers with one line each), `defaults_taken` (items 4, 8, 9, 14 with the sentence logged), `tests` (counts before and after, and the enumeration test's component counts and run time on the fixture-plus-table case), `open` (anything you could not do, with why), `for_abram` (questions only the author can settle, self-contained, defining terms in place).


---

<!-- mandate-v1.md -->

# Mandate: v1 of the graph prototype before public landing (2026-10-02)

Read first: `research/prioritization/workflow-2026-10-02/00-common.md` (follow it), `research/prioritization/notes/rulings.md` rulings 25, 27–33 and corrections C1–C2, `graph-prototype/BUILD.md`, `graph-prototype/graph/PROTOCOL.md`, `graph-prototype/checkers/graph.py`, `graph-prototype/tests/test_graph.py`, `graph-prototype/graph/DESIGN-LOG.md`, and `research/prioritization/notes/ranking-design-v3b.md` §Q1 (sub-frames) and `one-question-many-roots.md`. The author's words on 2026-10-02: "please calculate the default-trajectory utility by putting a case node with equal probability on each of the current named utility levels. 'Failure nobody describes' should be somewhat worse, excluding the 1.0 option, since it is failure after all"; "Seems a bit like building a worse version when you already know what the better version looks like?"; "we should get rid of the illustrative handles."

Work only under `research/prioritization/graph-prototype/`. Commit nothing. One checker run at a time; no Lean.

## Must do

1. **Outside option and residual as `cases` nodes (ruling 32).** The frame's `outside_option` points at a node `default-trajectory` of kind `cases` whose rows are the frame's named classes with equal weight and conditional 1 each (value = mean of class utilities = 0 on ruling 25's classes); the frame's residual class is likewise a `cases` node `undescribed-failure` over the same classes excluding the top one (mean −0.25). Both carry `provisional: true` and a Statement in the usual register. The checker derives the outside-option value and the residual value from these nodes (weights are judgment events like any row; the fixture's initial equal weights are set by the maintainer handle as the author's ruling, event kind `rule` citing ruling 32). Plan values and the commit line use them. Update PROTOCOL §4, BUILD, tests.
2. **Sub-frames (ruling 33).** A plan root may be a programme: a sub-frame whose own roots are its steps (plans or shared claims) with the sub-frame's question and classes. The parent values the programme as the sub-frame's best non-conceded plan value (or the sub-frame's own outside option when none), and the decision term treats the programme's steps as units in the parent. Implement the simplest sound form; document what the parent reads from the child and what it does not. Refile the deference programme in the fixture as a sub-frame over its steps (the `step-*` nodes and the bridge). Tests on the synthetic tree and the fixture.
3. **Revive task (ruling 33).** A conceded plan or table gets a ranked unit "revive <table>" whose action is arguing the conceding conditional back above the bar; its rate follows the ordinary observation units; the commit line's "until a revival" points at it.
4. **Gestalt width (ruling 33).** A gestalt's displayed width follows the judgment ladder only, not the root's vettedness floor. Tests.
5. **Attribution flag (ruling 33).** An explicit event kind `attribution` (human, non-author, with `verdict: vouched|disputed` and a `ref`) is the only thing that clears the attribution-unvetted flag; remove the wording match. Tests, PROTOCOL §3/§5, rule table.
6. **Illustrative handles removed (ruling 33).** Delete the `illustrative` key, the `@h1`/`@h2` handles and their ledgers; the fixture carries structure, roots and the two `rule` events of item 1 by the maintainer handle, and shows "no belief" where there are no judgments. Every test that needed numbers uses the synthetic tree. Update FIXTURE-NOTES and README accordingly (the fixture is now the starting graph for real contributors, not a demonstration).
7. **Rulings 31–33 and the triage acceptances** are reflected in PROTOCOL's registers (Decided where the author ruled). Record every change as a dated `change` line in `graph/DESIGN-LOG.md`.
8. Green: `python3 -m unittest discover -s tests`, `--self-test`, the plain run (one `OK` line on stderr), and byte-identity of the four committed files across flags.

## Report (structured): `headline`, `changed_files`, `done` (items 1–8, one line each), `sub_frame_semantics` (what the parent reads from the child, in five sentences), `open`, `for_abram` (self-contained, terms defined in place; only what genuinely needs the author).


---

<!-- review.md -->

# Mandate: review of the prototype

Deliverable: `research/prioritization/notes/prototype-review-2026-10-02.md` (under 200 lines).

Act as a contributor with a coding agent who has only `graph-prototype/graph/README.md`, `graph/PROTOCOL.md` and the checker. On a copy of the tree in `workflow-2026-10-02/artifacts/review-copy/`: run the checker; read the first task list; perform the top task as a simulated ten-minute session (write the event line the way the protocol says an agent would, from an invented but plausible human answer, marked as simulated); re-run the checker; file one picture against a node you disagree with and re-run; try three things the checker should refuse and confirm it does. Then report: what worked, every point where the documents and the code disagree, every term you had to guess, the three most confusing moments, and the three changes you would make first. Do not modify the prototype itself.
