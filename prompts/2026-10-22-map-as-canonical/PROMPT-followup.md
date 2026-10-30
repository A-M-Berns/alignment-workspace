# Prompt — map-as-canonical, follow-up on PR #131 (2026-10-23)

You are working in the `alignment-workspace` repository, on the branch
`round/2026-10-22-map-as-canonical` (PR #131, head `86e3f35`), continuing the round of
2026-10-22. This is not a new round: commit on that branch, append to its
`prompts/2026-10-22-map-as-canonical/REPORT.md` under a heading *Follow-up of 2026-10-23*,
and put this prompt verbatim beside it as `PROMPT-followup.md`. Auto-merge stays OFF. Run
`python3 -m checkers.graph --root .` and `python3 tests/run.py` before every commit.

## What this follow-up is for

A review of PR #131 found that the round made every object of the program exist in the map
and left the map flat: 249 of 260 formal results have a frame as their only parent; every
item's only parent is a docket whose Statement says nothing; the registry's `answers_item`
join is prose, not an edge; the old August frames sit beside the new programmes undissolved,
so each line carries two decompositions; 681 script-parsed hypothesis and setting leaves
doubled the node count without adding a reading; and `derived.json` grew to 15 MB with an
830k-line diff, which the repository cannot absorb once per round. This follow-up fixes
those six things. It writes no number, judgment, acceptance or priority word, and no event
in any human's ledger.

Two rules carry over from the round's prompt and bind here: structure and numbers are
decoupled; and where the protocol cannot hold something, change the protocol through its
own mechanism (a design-log line, a Default register, a refusal rule) rather than bending
the content. Every path, field, kind and node id named below was read from the branch at
`86e3f35`; confirm each before relying on it and correct this prompt in the report where it
is wrong.

## Maintainer rulings

Land as one dated `DECISIONS.md` entry, the first commit of the follow-up, marked as taken
by one maintainer in conversation with the other's confirmation outstanding (append to the
existing 2026-10-22 queue line rather than opening a second).

**F1. Hypotheses are filed when read, not parsed.** A `record` leaf may carry
`hypotheses: unread` in place of a list of hypothesis-leaf ids. The record's Source then
carries the declaration's signature verbatim (binders included), so a reader has what the
parsed leaves held. A formal result with an unread record is an `and` of record, bridge and
completeness leaf, and the view and the index say *hypotheses unread* beside it. Filing the
hypotheses is a human reading act or an agent act from a human's reading of the Lean;
a later round may rank it as a unit, but this follow-up does not. The 511 hypothesis leaves
and 170 setting leaves the round parsed from signatures are removed and the records they
belonged to set to `unread`. Hypothesis leaves that predate the round (the 68 that existed on
`main` at `4eb420f`, filed by reading) stay as they are.

**F2. The registry join is an edge.** Every formal result built from a registry entry with
an `answers_item` carries `work: [{kind: priorities, ref: <n>}]` for that item, and the
index inverts it: each item record in `index.json` lists `answered_by` (the formal-result
ids) and each formal result lists `answers`. An item's `item_status` does not change — closing
an item is the maintainer's (DECISIONS.md, *the reservation bar and epistemic debt*,
"closed needs a statement of record") — but the index and the render show the registered
answers beside an open item.

**F3. The large derived files leave the tree.** `graph/derived.json` and `graph/index.json`
are no longer committed. The checker still writes them on the plain run, to `graph/` as now,
and `.gitignore` excludes them; CI uploads both as workflow artifacts on every run and
publishes them to the branch `derived` (orphan, force-pushed, one commit per `main` push,
with the `main` commit hash in its message), which is where a site generator reads them
from. `graph/versions.json` stays committed and keeps `generated_hash` for both files, so a
hand-edited or stale derivation is still refused and a rerun still changes nothing. The
digest's "previous committed derivation" (`checkers/graph.py`, the function that reads
`HEAD:./graph/derived.json`) reads instead the `versions.json` at HEAD plus whatever
`derived.json` is on disk or on the `derived` branch, and says in its digest line which it
compared with. `graph/tasks.md` and `graph/view.md` stay committed: they are the
human-readable renders and a pull request's diff of them is the point. Report the size of
the pack before and after, and the size of each committed generated file.

**F4. One decomposition per line.** The pre-existing frames `normativity-line` (under
`normativity`) and `legitimacy-reasons-programme` (under `legitimacy`) are dissolved: each
child is moved to the new programme whose question it bears on (`seed-theory`,
`operative-force`, `normative-inductor`, `response-learning`, `normative-record`;
`integrity-and-record`, `openness-and-non-capture`, `authorship-and-transparency`), or,
where it bears on none, made a root of the line frame directly, never of a docket. The two
frame ids survive as deprecated aliases in the report's old→new map. Every move is a row in
a table in the report — node id, from, to, one line of reason citing the node's own
Statement — so a maintainer can review placements in one sitting and reverse any. The same
treatment for any other pre-existing sub-frame under the two lines whose question the new
programmes now ask (the round's report §6 lists 27 pre-existing sub-frames; say which of them
this applies to and which stay). `deference-and-trust`, `decision-theory`,
`stance-and-level`, `abstraction-arc` and `enabling-work` are not touched by this ruling:
their reorganization is the second maintainer's.

**F5. A formal result sits under the claim it establishes.** For each formal result whose
only parent is a frame, find the existing informal claim node it is the formal version of,
and merge them: the existing claim node keeps its id and its place in every argument and
becomes the `and` of the record, bridge and completeness leaf (the pattern
`legit-composition` / `legit-composition.record` already follows); the registry-id node
becomes a deprecated alias listed in the old→new map, and the registry id stays recorded on
the record leaf's `statement_of_record` and in the index so a claim id still resolves. The
matching is mechanical and conservative — rules in Part 3 — and a result with no match or
more than one stays where it is, listed. The target is not zero bagged results; it is that
every result that *has* an informal claim in the map is attached to it.

**F6. Items are docketed by programme where the evidence places them.** An item whose
`context` paths lie under a round directory from which a programme's formal results were
registered (`origin_round`), or whose `project` marker names a subproject with its own
programme (`normativity.seed` → `seed-theory`), moves from the line's docket to a docket
under that programme; the rest stay in the line's docket. Each docket's Statement is
rewritten to say what it is: "Work orders filed against <programme>, not yet attached to the
goal each serves; their placement is the maintainer's." A docket is a `shared-claim` root
today; the report says whether that role or a frame field for dockets would represent it
more honestly, and proposes the latter in a design-log line if so, without applying it.

## Part 1 — F1 and F2: records

Remove the parsed hypothesis and setting leaves; set each affected record to
`hypotheses: unread`; move the signature text from the removed leaves' Sources into the
record's Source; update each result's `and` children and its completeness leaf's Statement
(it names the conjuncts). Extend `checkers/graph.py`: `hypotheses: unread` is legal on a
record (rule 2's required-fields clause), a record with it is flagged in `derived.json`,
`index.json` and `view.md`, and a `hypotheses` list that mixes ids with `unread` is refused.
Add the `priorities` pointer from `answers_item` to every registry-built formal result
(superseded entries included), and the `answers` / `answered_by` inversion to the index
schema (bump it to `graph-index/2` and update §6.1 of `graph/MAP-AS-CANONICAL.md`). Update
`checkers/priorities_render.py` so a rendered item lists its registered answers in one line
under its heading, and the render gate with it. `PROTOCOL.md` §2 *Formal results* and §9
rule 2 say what the code does; one design-log line each for F1 and F2.

## Part 2 — F4: dissolve the old frames

For each child of `normativity-line` and `legitimacy-reasons-programme`, read its Statement
and Source and move it to the programme whose question it bears on; where its Source cites a
round or document that a programme's narrative or results also cite, that programme; where
it bears on none, the line frame. Roles and presets carry over. A child that is itself a
frame (`corrigibility-landscape` and the stage frames among them) moves whole. Then remove
the two frames from their parents' `children` and `roots`, keep their node files with
`superseded_by` naming the line frame (the protocol's existing mechanism for a retired node),
and run the checker: nothing may be left attached to nothing. The table of moves goes in the
report.

## Part 3 — F5: attach results to their claims

Candidates for a bagged result `R` (an `and` with a `.record` child whose only parent is a
frame) are existing nodes `C` in the same line, not themselves formal results, such that any
of: `C`'s Source cites the Lean file or declaration `R`'s record names; `C`'s Source cites
`R`'s `origin_round` directory and `C`'s Statement shares its subject with `R`'s registry
`short_name` (the round states the test it used — a shared content word after the evaluative
list is removed is the floor); or `C`'s id is the registry id with its line prefix stripped
or its dots made hyphens. Merge only when exactly one candidate survives; list the rest
under *unmatched* (no candidate) and *ambiguous* (several, with the candidates named) in the
report. A merge: `C` gains `R`'s record, bridge and completeness children (bridge
`attribution` unchanged); `C`'s kind becomes `and` if it was a leaf, with its former
Statement kept as the `and`'s Statement; `R`'s id goes in the old→new map and `R`'s file
gets `superseded_by: C`; any pointer or root naming `R` is repointed to `C`. If `C` already
has a record child (a result landed twice under two ids), say so and reserve it rather than
merging. Report the counts: bagged before, merged, unmatched, ambiguous, bagged after.

## Part 4 — F6: dockets by programme

Apply the two placement rules; rewrite the docket Statements; file the per-programme dockets
as `shared-claim` roots of their programme (the current form) and write the design-log
proposal for a better form if the round has one. Report the per-docket counts before and
after.

## Part 5 — F3: the derived files

Make the `.gitignore`, CI and checker changes; add the `derived` branch publish step to
`.github/workflows/ci.yml` under the existing write-scope enumeration (`WORKFLOW SCOPE`
gate must pass with the new write scope declared); remove `graph/derived.json` and
`graph/index.json` from the tree in a commit of their own, after the content commits, so the
branch's diffs above it remain reviewable. Update `graph/README.md` step 1 and `AGENTS.md`
*Commit only what the plain run writes*. One design-log line.

## Report

Under *Follow-up of 2026-10-23* in the round's `REPORT.md`, in order: verification (the
checker's OK line before and after, `tests/run.py` output, node counts by kind before and
after, pack size before and after); the moves table of Part 2; the merge counts and the
unmatched and ambiguous lists of Part 3; the docket counts of Part 4; every protocol and
checker change with its design-log line and rule; deviations from this prompt with reasons;
corrections to this prompt; what this follow-up did not do (the reorganization of the second
maintainer's lines; attaching unmatched results; placing items under goals; filing any
hypothesis by reading; the site); and additions to the reserved list, each with its *turns
on* line (the ambiguous merges; dockets' representation; whether `tasks.md` and `view.md`
should follow the derived files out of the tree if they too grow).
