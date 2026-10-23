# Report — the map as the canonical index of the program (2026-10-22)

| | |
|---|---|
| Prompt author | the maintainer, relayed verbatim (`PROMPT.md`) |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code, one session |
| Deliverables | `graph/MAP-AS-CANONICAL.md`, `graph/SURVEY.md`, the restructured map (`graph/`), `checkers/graph.py`, `checkers/priorities_render.py`, `checkers/wiki_refs.py`, the rendered `PRIORITIES.md`, the anchored `DECISIONS.md`, the attached wiki, `README.md`, `AGENTS.md`, the gates |
| Dates | 2026-10-22 |
| Register | `ci-only`: the maintainers have read none of it; rulings M1–M8 were taken by one maintainer in conversation and the second maintainer's confirmation is queued |

## 1. Verification

**The checker, before and after** (`python3 -m checkers.graph --root .`, Python 3.12):

```
before  OK 1561 nodes, 2411 events, 2021 ranked units; research first: the decision term (printed, not applied) favours vet hull-condition-total-trust (ranked unit 19), D 0.00016
after   OK 3059 nodes, 2411 events, 4685 ranked units; research first: the decision term (printed, not applied) favours vet hull-condition-total-trust (ranked unit 202), D 0.00016
```

No `WARN` before; after, one `WARN` line: `DECISIONS.md: 241 of 291 decision anchors have no node pointing at them (first: …; every anchor's pointers are in graph/index.json)` — the warning the prompt asked for, summarized to one line because one line per entry drowned the OK line (the index carries `pointed_by` per anchor). The self-test (`--self-test`) passes with the eleven null inputs this round added.

**`tests/run.py`**: `ALL GREEN (80 project(s))` on the final tree (the unit tests take about four minutes: the fixture class derives the 3059-node graph several times, and the oracle regression is capped as §7 says), with the new gates in the run: `PRIORITIES RENDER: the committed file equals the render (137 items)`, `WIKI REFS: clean over 34 page(s); 304 reference(s) resolve`, `WIKI STATE BINDINGS: clean over 34 page(s); 3 binding(s) verified`, `WORKSPACE STATE: valid — 6 projects, 178 modern claims, 1 foundations, 180 foundation claims, 126 rounds, 52 terms, 137 priorities, 10 interface objects`. The full output of the final run is in §9. Lean was not built (`WORKSPACE_LEAN` unset; no Lean file changed).

**Counts by node kind** (before → after): `and` 125 → 303; `cases` 47 → 47; `frame` 33 → 46; `leaf` 1291 → 2593; `or` 65 → 70. Leaves: assumption 32 → 32; bridge 85 → 263; completeness 125 → 303; hypothesis 68 → 714; partition 47 → 47; picture 202 → 202; question 188 → 192; record 82 → 260; route 123 → 123; step 211 → 211; task 116 → 234; want 12 → 12.

**Counts by pointer kind** (nodes carrying the kind, before → after): `priorities` 36 → 13 (the 17 merged item nodes dropped their own pointer; the 13 nodes that point at items they are not stay); `open` 18 → 18; `round` 8 → 194; `decision` 0 → 61; `foundation` 0 → 1; `private` 0 → 0.

**The render gate**: `python3 -m checkers.priorities_render --check` passes; the only change the first render made to `PRIORITIES.md` was placing every `workspace-priority` marker on the line after its heading (items 74–128 and `F7`–`F8` had a blank line first).

## 2. Deviations from the prompt, with reasons

- **Formal results are 178, not 174, and the records matched were 4, not 82 reconciled.** The prompt expected the 82 landed `record` leaves to be renames of registry entries. They are not: 78 name declarations of the clean room `projects/deference/faf-cleanroom-2026-10-02/` and no registry lists them; the registries have no old-id→new-id table beyond the `superseded_by` field (11 entries). The 78 are kept as they were, flagged *not in a claims registry*, and the gap is filed (§4). Every registry entry, superseded ones included, got a formal result; a superseded entry's `and` carries `superseded_by` naming its successor's result.
- **Hypothesis leaves were read by script, not by a reading session.** 511 hypothesis leaves and 170 setting leaves were parsed from the Lean signatures (explicit proposition binders, named `h…` or carrying a relation, as hypotheses; data binders as one definitional setting leaf). Binders declared with `variable` in a section are not in a signature and are not listed. Every hypothesis is `discharge: open`; the registry notes settle none in a form a script can read. Two `and` Statements and one bridge fell back to a generic sentence because the registry's note used a word on the evaluative list (`kernel.extension-realized-rate`, `li.assessment.budgeter-value`, `kernel.box3-gap-exchange-rate.bridge`); the note is quoted in the Source.
- **Items are docketed by project, not by section.** Part 2 says an item whose goal cannot be identified hangs under the plan frame of its `project`; the file's late sections do not follow projects (items 112–128 sit under *Deference line — second wave* with normativity projects), so the dockets follow the `workspace-priority` marker. 120 items are docketed and listed in §5; the 17 merged ones keep their place.
- **The `touches` lists are mechanical.** 283 entries could not be read for their bearing in one round; `touches` holds the explicit mentions (items, registry ids, backticked node ids) and 49 entries have one. A ruling's unstated bearing is for a later pass.
- **Frames were re-owned by line and wants by source attribution** beyond M1's rename, because the blanket rename would have made the first maintainer the owner of wants quoted from the second's notes (`projects/deference/note-dump-2026-08-11/README.md` attributes `notes/`, the lab and the chats to him). Agent-decided, reversible, listed in `DECISIONS.md` *Awaiting the author*.
- **No new want was filed.** Part 6 permits wants for `@anson` from the published corrigibility post; the thirteen existing wants already cover the post's material and the round filed none, so no priority word question arises beyond the thirteen.
- **`wiki/CONVENTIONS.md` is attached** (to `enabling-work`) although the prompt lists only `ORIGIN.md`, `Sources.md`, `_Sidebar.md` and `Prior-Art.md` as possibly unattached: the conventions page narrates the wiki's own machinery, which is enabling work.
- **The rulings entry does not backtick `graph/index.json`**: `tests/dead_pointers.py` refuses a backticked path that does not exist, and the index exists only from the third commit.
- **A WIP commit was used and squashed.** The checker changes were snapshotted while the restructure ran, then folded into the third commit; the branch's history has the proposal first and the rulings second, as asked.

## 3. Corrections to the prompt

- "the two registries hold about 80 entries" — they hold 178 (105 deference, 73 normativity; 167 active, 11 superseded).
- "41 nodes carry `work: {kind: priorities}` today" — 41 pointers on 36 nodes, to 36 distinct items.
- "Today eight nodes carry such [round] pointers" — correct (8 nodes, 8 rounds).
- "every page under `wiki/`" — 34 files: 32 pages and two repo-only files (`ORIGIN.md`, `CONVENTIONS.md`).
- M1 says "the ledger file, its event ids `maintainer-001`/`-002`" — correct; the two rulings on the valuation nodes are the only human events.
- `checkers/wiki_state_bindings.py` binds quantities, not names; a sibling checker (`checkers/wiki_refs.py`) was needed for claims, items and rounds, as the prompt allowed.
- The prompt's "a `narrative` path that does not exist is refused" is implemented; a path outside `wiki/` is refused too.
- Everything else named in the prompt (paths, fields, kinds, policy keys, node ids) exists on `main` at `4eb420f`.

## 4. What the protocol could not represent

`graph/SURVEY.md`, *What the protocol cannot represent*, lists eight; the ones filed as extensions or reserved:

1. A kernel-checked declaration outside every listed registry (the 80 clean-room records): reserved (a registry for the clean room is a trust-chain question).
2. A work order's goal: the per-project docket is the protocol-conformant placeholder; no extension.
3. A ruling's effect beyond its explicit mentions: no extension; a `supersedes` field on the anchor line is the candidate.
4. An owner confirming a drafted frame: `filed_from: wiki` and its removal by the owner; a `confirm` event is the alternative, reserved.
5. The foundation's ledger as a pointer target: the `foundation` work kind (`state/foundations.json` ids), filed.
6. Two pages narrating one node: `narrative` accepts a list, filed.

No `graph/proposals/P-<n>.md` was written: each extension was small enough to land through a design-log line and the protocol's Default register, per M4; the reserved ones are queue entries.

## 5. Goal not identified

The 120 items in the dockets (an `or` of routes under the line's frame; the 17 merged items keep their earlier place):

- `docket-normativity` (39, under `normativity`): 1, 3, 4, 5, 6, 29, 30, 31, 32, 33, 35, 39, 40, 46, 41, 44, 45, 43, 42, 47, 49, 50, 51, 74, 78, 79, 80, 81, 82, 85, 112, 113, 114, 116, 123, 124, 125, 126, 127.
- `docket-legitimacy` (22, under `legitimacy`): 53, 54, 55, 56, 57, 58, 59, 61, 62, 64, 65, 66, 70, 67, 68, 69, 71, 72, 73, 88, 115, 128.
- `docket-seed` (6, under `seed-theory`): 117, 118, 119, 120, 121, 122.
- `docket-deference` (38, under `deference-and-trust`): Q1, Q2, Q3, Q4, 52, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 60, 83, 84, 86, 87, 89, 90, 92, 93, 97, 98, 99, 100, 101, 102, 103, 104, 107, 111, 28.
- `docket-workspace` (15, under `enabling-work`): F1–F8, 10, 11, 12, 13, 36, 37, 38.

The 17 merged (old id → `item-<n>`): computable-coherence-modulus → item-2, market-and-traders-modeled → item-7, doubly-soft-weight-class → item-8, forcing-headlines-not-squeezes → item-9, fa-public-port → item-14, punishing-menu-vs-public-port → item-34, modified-market-computable → item-48, sigma-n-computable → item-63, closed-loop-affordability → item-75, semantic-transport-modulus → item-76, authorized-disposition → item-77, oracle-relativized-li → item-91, belief-decision-compatibility → item-105, li-bria-updateful-endpoint → item-106 (an `and`; its completeness leaf is `item-106.complete`), thin-spec-for-evaluations → item-108, thin-preservation-li-principal → item-109, thin-baseline-definition → item-110. Items with several candidate nodes (2, 27, 103, 106, 107) got a fresh node where no single node stood for the item alone.

## 6. Unattached narratives and unpointed rounds

**Wiki pages that are no node's narrative** (10): `ORIGIN.md` (a receipt), `Sources.md` (a bibliography), `_Sidebar.md` (navigation), `Prior-Art.md` (a field map), `Glossary.md` (vocabulary), `Relation-to-the-Field.md` (nine lines, a field map), legitimately; and `Roadmap.md` (it narrates every line at once; its item mentions carry references), `Theorem-Spine.md` (it narrates every formal result at once; 68 references), `Why-Normativity.md` (motivation, no one node) and `Continuation-BRIA.md` (the learning layer, whose nodes are the BRIA cluster inside `updateless-dt-programme` and `public-corrigibility-line`; no one frame is its subject). The last four are for a maintainer to place or to leave.

**Frames lacking a narrative** (30 of 46): the eleven new line and programme frames have one except `decision-theory`, `stance-and-level` and `authorship-and-transparency`; the 27 pre-existing sub-frames below the lines (`abstraction-arc`, `legitimacy-reasons-programme`, `updateless-dt-programme`, the three level frames, the corrigibility-landscape sub-frames, the stage frames, and the rest) have no page of their own.

**Rounds no node points at** (6): `2026-08-11-admin-cleanup`, `2026-08-11-public-flip-and-scrub`, `2026-08-11-rename-alignment-workspace`, `2026-08-11-retire-frozen`, `2026-08-11-scrub-round-2`, `2026-08-24-cleanup-and-compress` — scrubs, renames and cleanups. The 119 others: 23 workspace-prompt research dispatches are pointed at from the line or programme they served; 12 infrastructure rounds from `enabling-work`; the rest from the formal results they registered (`origin_round`) and the line frames of their project. `2026-10-02-graph-prototype` is indexed with path `graph` and is pointed at by that path.

**Placement unclear** (left where it was): `wiki-corpus-maintenance` (a plan of `deference-and-trust`, arguably enabling work); the Progress results under `normative-inductor` (the sidebar files normative induction under legitimacy); `deference-toward-bounded-agents` and `corrigibility-landscape`, whose home is `legitimacy` because that line is walked first (each is also a root of `deference-and-trust`).

## 7. Protocol and checker changes

Each with its design-log line (all dated 2026-10-22 in `graph/DESIGN-LOG.md`) and the refusal rule it touched:

| change | rule | design-log line |
|---|---|---|
| layout admits `MAP-AS-CANONICAL.md`, `SURVEY.md`, `index.json`; the scale test reads bytes on macOS | 11 | "the layout admits …" |
| `@maintainer` → `@anson`, `@abram` mapped, `maintainer` a list, `rule`/`survey` by any maintainer | 5 | "ruling M1 …" |
| `owner` a handle or a list on every frame | 2 | "ruling M5 …" |
| shared roots (a node in several frames; a want in one; roles agree) | 1 | "shared roots …" |
| `narrative` (a page or list under `wiki/`, must exist); `filed_from: wiki` on frames | 2 | "`narrative` on the top frame …" |
| `decision` and `foundation` pointer kinds; `round` resolves through `state/rounds.json`; `priorities` resolves to item nodes | 1, 2 | "ruling M7 …" |
| item nodes and their fields; `PRIORITIES.md` rendered by `checkers/priorities_render.py` and gated | 1, 2, 12 | "ruling M6 …" |
| `graph/index.json`, the fifth committed file | 7 (its hash) | "ruling M8 …" |
| `the-program` and the seven lines; `checkers/wiki_refs.py` | — | "ruling M2 …" |
| the scale test derives in a child process; the fixture copier carries `wiki/`, `DECISIONS.md` and the state files | — | "the scale test derives its fixture in a child process …" |
| the oracle regression skips shipped roots above twelve proof-set variables (the warrant inductor's result has 25; the enumerator took 40 minutes on it) | — | "the oracle regression on the shipped graph skips …" |

Eleven null inputs were added to the checker's self-test (a narrative naming no page, a narrative outside `wiki/`, a decision pointer to no anchor, a foundation pointer to no foundation, a want in two frames, a shared root with two roles, an AI handle in a frame's owner list, an AI handle in the maintainer list, `filed_from: wiki` on a leaf, an item node without its fields, an `item-` id without `item`); `checkers/priorities_render.py` and `checkers/wiki_refs.py` ship their own self-tests with null inputs; `tests/path_gate.py` gained three cases. `AGENTS.md`'s `graph/` section, `graph/README.md` and `graph/PROTOCOL.md` (§1, §2, §8, §9) say what the code does.

**Where the checker or protocol assumed one maintainer or one owner, and what was done**: `policy.yaml`'s `maintainer` (now a list; rule 5); the `rule`/`survey` check and anchor 18 (any maintainer); the top frame's `owner`, every frame's `owner`, the view's "frame owner", the goal table's "owner" and `derived.json`'s `frame.owner` (a list, joined for display, `owners` beside it); the prose "the maintainer owns the top frame" in PROTOCOL §2 (rewritten). Left as is: a want's one owner (by M5); `placed_by` on the outcome classes (one handle, the maintainer who placed them); the `users` presentation map (per handle already); `audit` cross-audit preference (per handle). The protocol's "the maintainer's design rulings are cited by number" (§7) stays single in wording and applies to either maintainer.

## 8. What this round did not do

The website; the intake verbs (challenge, bridge judgment) beyond their schemas in the proposal document; the lifting of any of the foundation's 180 claims; any reconciliation of numbers (no event, judgment, priority word or acceptance was written; every node filed is at level 0 with no belief); a registry for the clean-room records; reading the 283 ledger entries for their unstated bearing; wants for either maintainer; placing the four wiki pages left unattached; the per-sub-frame narratives.

## 9. Test output

```
self-test PASS
CONTRIB HYGIENE: 0 contributor checker(s), stdlib-only, each with a meaning docstring and a check function
CONSERVATIVITY: 4 spec files, no axioms, shape unchanged
WORKFLOW SCOPE: clean over 3 workflow(s); 2 enumerated write-scope job(s)
DEAD POINTERS: clean over 58 live document(s) — 918 rooted path(s) resolve, 8 of them into declared trees and each saying so; 105 unrooted and 221 glob(s) not this gate's business; 14 historical span(s) and 5 ledger cita
UNTRACKED POINTERS: clean — 333 round-record path(s) and 973 resolving citation(s) are in the repository, not merely on this disk
WORKSPACE STATE: valid — 6 projects, 178 modern claims, 1 foundations, 180 foundation claims, 126 rounds, 52 terms, 137 priorities, 10 interface objects
WIKI LINKS: clean over 32 page(s) (links resolve; repository links are commit-pinned)
WIKI STATE BINDINGS: clean over 34 page(s); 3 binding(s) verified against the state emission
WIKI REFS: clean over 34 page(s); 304 reference(s) resolve
PRIORITIES RENDER: the committed file equals the render (137 items)
Ran 140 tests in 148.556s
OK
GATE COVERAGE: 11 gate scripts, all invoked (5 self-test only — no local form)
LEAN SORRY GATE: clean over 108 files
LEAN AXIOM DISCIPLINE: every file carries `#print axioms`
PROJECTS:
LEAN BUILD SKIPPED: set WORKSPACE_LEAN=1 to run `lake build`
ALL GREEN (80 project(s))
  … 80 PASS lines, one per project runner, elided
```

## 10. Reserved to the maintainers

In `DECISIONS.md`, *Awaiting the author*, each with its *turns on* line: the second maintainer's confirmation of M1–M8; the wording of `the-program`'s question and of every line frame's; the roots marked *owner has not confirmed* (nine drafted frames, the re-owned sub-frames, the re-owned wants); which of the foundation's 180 claims are lifted (four are cited by name, from the item-1 node); the priority words on every want; whether the clean-room records get a registry; the top frame's owner and the sub-frames' owners; the placements the round left where they were.

## Outstanding maintainer actions

1. Confirm or strike rulings M1–M8 (`DECISIONS.md`, 2026-10-22) — the second maintainer, by a dated entry.
2. Read `graph/MAP-AS-CANONICAL.md` and merge or return the pull request (auto-merge is off).
3. For each drafted frame, keep or redraft it, and remove `filed_from: wiki` from the node file to confirm it: `normativity`, `legitimacy`, `seed-theory`, `operative-force`, `normative-inductor`, `response-learning`, `normative-record`, `integrity-and-record`, `openness-and-non-capture`, `authorship-and-transparency`.
4. Give each want its priority word (`priority` event in your ledger, through your agent), or disown it.
5. Decide the reserved placements and whether the clean room gets a registry.

## Follow-up of 2026-10-23

| | |
|---|---|
| Prompt | the maintainer, relayed verbatim (`PROMPT-followup.md`), answering a review of PR #131 |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code, one session |
| Commits | six on `round/2026-10-22-map-as-canonical` above `86e3f35`: the rulings F1–F6; the records (F1, F2); the dissolution, the merges and the dockets (F4, F5, F6); the derived files (F3) with the checker, CI and the documents; the removal of the two files alone; this report with the queue entries |
| Register | `ci-only`; rulings F1–F6 taken by one maintainer in conversation, the second maintainer's confirmation appended to the round's queue entry |

### 1. Verification

**The checker, before and after** (`python3 -m checkers.graph --root .`, Python 3.12):

```
before  OK 3059 nodes, 2411 events, 4685 ranked units; research first: the decision term (printed, not applied) favours vet hull-condition-total-trust (ranked unit 202), D 0.00016
after   OK 2415 nodes, 2411 events, 3389 ranked units; research first: the decision term (printed, not applied) favours vet hull-condition-total-trust (ranked unit 203), D 0.00016
```

The one `WARN` line is the round's (`DECISIONS.md: 244 of 295 decision anchors have no node pointing at them …`; 295 anchors now: the follow-up's entry, pointed at by the two line frames it restructured, and its three queue entries, pointed at by nothing). New since F3, one `DIGEST` line before the `OK` says what the digest compared with; on this tree: `DIGEST compared with graph/derived.json on disk (the derivation versions.json at HEAD records): 0 status(es) flipped, 0 root status(es) flipped, 0 level(s) moved, 0 event(s) counted since, 0 revision(s), 0 want(s) filed since, 0 proposal(s) awaiting`. The self-test passes with the two null inputs this follow-up added.

**`tests/run.py`** on the final tree: `ALL GREEN (80 project(s))`, with `PRIORITIES RENDER: the committed file equals the render (137 items)`, `WORKFLOW SCOPE: clean over 4 workflow(s); 3 enumerated write-scope job(s)` and the unit tests green (two tests added, four extended for the `DIGEST` line, the aliases and the merged results). The full tail is in §10. Lean was not built (no Lean file changed).

**Counts by node kind** (before → after): `and` 303 → 305; `cases` 47 → 47; `frame` 46 → 46; `leaf` 2593 → 1945; `or` 70 → 72. Leaves: assumption 32 → 32; bridge 263 → 263; completeness 303 → 303; hypothesis 714 → 68; partition 47 → 47; picture 202 → 202; question 192 → 192; record 260 → 260; route 123 → 123; step 211 → 209; task 234 → 234; want 12 → 12. The 646 leaves gone are the 511 hypothesis and 135 setting leaves the round parsed (F1); the two steps gone became the `and` nodes of their formal results (F5); the two `or` nodes added are the dockets of F6; the two frames retired by F4 keep their files.

**Pack size** (`git count-objects -vH`, in the worktree, before the follow-up → after its six commits): loose objects 27.59 MiB (2,479 objects) → 39.48 MiB (3,113 objects); the pack 77.83 MiB in 10 packs, unchanged (no repack ran). The intermediate commits still carry `graph/derived.json` and `graph/index.json` (the prompt asked for the removal in a commit of its own after the content commits), so the pack grows by their blobs once more before shrinking at every later commit. **Committed generated files** after the follow-up: `graph/versions.json` 898,083 bytes (832,924 before; it now records the two derivation hashes), `graph/tasks.md` 202,461 bytes (203,367), `graph/view.md` 684,884 bytes (753,495); the two uncommitted ones on disk: graph/derived.json 11,634,243 bytes (14,769,185 before) and graph/index.json 3,498,828 bytes (3,719,006).

**Old → new map** (deprecated aliases, each file kept with `superseded_by`): `normativity-line` → `normativity`; `legitimacy-reasons-programme` → `legitimacy`; `kernel.box2-finite-time` → `kernel-box2-finite-time`; `thin.value-of-thick` → `thin-value-of-thick` (the two registry ids resolve through `claims` in the index and `registry_id` on the record leaf).

### 2. Part 2 — the moves (ruling F4)

Of the 27 pre-existing sub-frames below the lines, the ruling applies to two, which are dissolved: `normativity-line` (6 roots) and `legitimacy-reasons-programme` (77 roots, three of them frames). Its three sub-frames (`formalism-open-questions-0-3`, `legit-dynamics-learning`, `legitimacy-meets-syntax`) ask questions none of the three legitimacy programmes asks (the li-deference formalism's open questions; learning and repairing legitimacy; legitimacy as local rules of sanity), so each moves whole to the line frame as a plan root. `corrigibility-landscape` with its eight sub-frames and `deference-toward-bounded-agents` stay where they are (their questions are corrigibility's and the bounded agent's, asked by no programme). The thirteen sub-frames under `deference-and-trust`, `decision-theory`, `stance-and-level`, `abstraction-arc` and `enabling-work` are not touched, per the ruling.

The reading rule, applied to each child's Statement and Source: a child whose Statement is the programme's own object (the thin specification and the thick definition; the authorship clause; the traderization arc; the Progress bound) or whose Source cites the round from which that programme's results were registered goes to the programme; the maintainer's logical-induction-register legitimacy theory (the gated trust principles, the endpoint-preservation model, the clean-room results, the legitimacy-weighted objectives and their cruxes), the bridge between the two theories, the reasons thread and the wants bear on none of the three programmes' questions and become roots of `legitimacy`; the normativity line's foundation, consolidation problems and paper candidates become roots of `normativity`. Roles and presets carried over unchanged; the four items among the children (`item-75`, `item-108`, `item-109`, `item-110`) are roots of a frame, not of a docket.

| node | kind | role | from | to | reason |
|---|---|---|---|---|---|
| `normativity-aug9-foundation` | leaf/step | shared-claim | `normativity-line` | `normativity` | the foundation of the whole line ("one hundred and eighty claims under its own ledger"); it bears on no one programme |
| `normativity-layer-I-closed` | leaf/step | shared-claim | `normativity-line` | `normative-inductor` | its Statement is the fixed-era composition "from obligation stream to Progress and substrate preservation"; the Progress bound (progress.*) is what this programme's results register |
| `traderization-arc` | leaf/step | shared-claim | `normativity-line` | `operative-force` | its Statement, "a constraint on prices compiles to a legal trading strategy in the market recursion, the modified market is a logical inductor over an assessment process", is the arc whose registered results (li.assessment.*, force.*, coherence.*, compiler.*, maxmin.*, region.*) this programme holds; its own Notes say so |
| `normativity-learning-track` | leaf/question | shared-claim | `normativity-line` | `response-learning` (already a root there) | already a root of response-learning (a shared root since the round); the dissolution leaves it there |
| `normativity-consolidation-open-1-6` | leaf/question | shared-claim | `normativity-line` | `normativity` | the six open problems span the consolidation ("persistence of the certified core minimum, a computable coherence modulus … schema-level demand rates"); no one programme asks them |
| `normativity-paper-candidates` | leaf/step | shared-claim | `normativity-line` | `normativity` | "four extraction candidates exist for papers from the normativity line": a line-level claim |
| `legit-definition-endorsement` | cases | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (cases: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-corrects-trust-principles` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-per-formalism-family` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-gated-trust-li` | or | plan | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (or: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-ddb-transfer` | and | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (and: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-locality-forced` | and | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (and: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-reflection-unsat-modest` | and | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (and: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-composition` | and | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (and: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-li-self-correction-identity` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-correction-function-learned` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/question: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-condition-vs-predict-reality` | cases | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (cases: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-anchor-of-L` | cases | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (cases: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-global-or-local-form` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/question: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-trust-improvable` | or | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (or: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-endpoint-preservation` | leaf/step | plan | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `idleness-on-G-grade-a` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `idleness-on-G-with-certificate` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `claim1-diagonal-illegitimate` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `corrupt-strictly-contains-inadmissible` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `trace-nonrecoverability` | and | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (and: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `trace-nonrecoverability-li` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/question: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `wirehead-iff-finite` | and | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (and: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `certificate-enforcement` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `predication-dichotomy` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `d3-identification` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `corrigibility-faithful-plus-legit-on-self` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `non-modification-conjecture` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/question: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-v1-improvable` | or | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (or: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `public-legitimacy-theory` | and | plan | `legitimacy-reasons-programme` | `authorship-and-transparency` | its Statement is the public two-level theory, "a thin specification … and a thick definition …, and proves that the thick conditions satisfy the thin specification", which is this programme's question |
| `thin-converse-open` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `authorship-and-transparency` | its Statement is the thin level's converse ("sufficient is necessary for value"); its Source cites thin.converse-fails-on-correct, a result of this programme |
| `thin-value-loss-bound` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `authorship-and-transparency` | its Statement is the thin level's two-term bound; its Source cites thin.value-loss-le-defects, a result of this programme |
| `item-109` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `authorship-and-transparency` | its Statement is the thin preservation theorem for a logical-inductor principal; its context is the thin-legitimacy round from which thin.preservation was registered |
| `item-110` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `authorship-and-transparency` | its Statement asks for a definition of the thin level's baseline; its context is the thin-legitimacy round from which this programme's results were registered |
| `item-108` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `authorship-and-transparency` | its Statement asks for the thin properties' form for valuations; its context is the thin-legitimacy round from which this programme's thin.* results were registered |
| `gate-is-legitimacy` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `public-layer-II` | and | plan | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (and: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `item-75` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/question: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `li-corrigibility-inequality-public` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legitimate-deference-regret` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `effective-authority-layer` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `authorship-and-transparency` | its Statement ends "with sincerity conditions on which verdicts count"; its Source cites the sincerity.* claims and the thin-legitimacy round, whose sincerity results this programme holds |
| `cnl-post` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `authorship-and-transparency` | its Statement says the post is "backed by that round's theorem", the thin preservation theorem this programme holds; its Source is the thin-legitimacy round's Part F |
| `public-legitimacy-improvable` | or | shared-claim | `legitimacy-reasons-programme` | `authorship-and-transparency` | the improvement claim on public-legitimacy-theory ("the thick and thin legitimacy theory … can be improved"); it moves with the claim it improves |
| `legit-two-theories-bridge` | cases | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (cases: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `bridge-defect-vs-thin-correct` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/question: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `bridge-trace-vs-transparency` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/question: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-objective-proposals` | cases | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (cases: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `illegitimate-world-ever-better` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/question: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `p2-manages-the-news` | and | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (and: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `inferability-positivity` | and | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (and: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `updateless-p2-cellwise-p3` | and | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (and: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `deterrence-not-identified-on-path` | and | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (and: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `corr-legit-modif-frames` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-branch-evaluation-defense-requirements` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `readout-R1-vs-R2` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/question: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `retroactive-vs-prospective-judging` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/question: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `anger-substitute-for-updatelessness` | cases | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (cases: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-meta-revision` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/question: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `corrigibility-needs-consequentialist-wrapper` | cases | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (cases: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `align-to-legitimacy-over-endorsement-risk` | leaf/step | risk-story | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-weighted-objective-improvable` | or | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (or: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `formalism-open-questions-0-3` | frame | plan | `legitimacy-reasons-programme` | `legitimacy` | a pre-existing sub-frame whose question none of the three programmes asks; it moves whole to the line |
| `internal-standard-never-settled` | cases | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (cases: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-dynamics-learning` | frame | plan | `legitimacy-reasons-programme` | `legitimacy` | a pre-existing sub-frame whose question none of the three programmes asks; it moves whole to the line |
| `reasons-subcase-of-legitimacy` | cases | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (cases: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `public-internal-legitimacy-is-reasons` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `authorship-and-transparency` | its Statement is the authorship clause ("authorship requires at each step a grounding selection from the reason trace's pre-state prefix"), this programme's question of when a verdict is the principal's own |
| `reason-mediated-authorship` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `authorship-and-transparency` | its Statement is "authorship of a future evaluation is exclusive principal binding together with reason mediation"; the programme holds authorship.mediation-by-reexecution |
| `reasons-statics-public` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `public-line-leaves-semantics-alone` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `brandom-objectivity-structural` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `brandom-relative-prices` | leaf/step | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/step: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `reason-exchange-representation-theorem` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/question: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legit-intersubjectivity-pre-rationality` | leaf/question | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (leaf/question: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `reasons-improvable` | or | shared-claim | `legitimacy-reasons-programme` | `legitimacy` | the Statement bears on none of the three programmes' questions (or: the maintainer's logical-induction-register legitimacy theory, its cruxes, the clean-room results and the reasons thread); a root of the line |
| `legitimacy-meets-syntax` | frame | plan | `legitimacy-reasons-programme` | `legitimacy` | a pre-existing sub-frame whose question none of the three programmes asks; it moves whole to the line |
| `want-figure-out-legitimacy` | leaf/want | want | `legitimacy-reasons-programme` | `legitimacy` | a want of the line's owner; a want is a root of one frame, its owner's placement |
| `want-corrigibility-theorems-via-legitimacy` | leaf/want | want | `legitimacy-reasons-programme` | `legitimacy` | a want of the line's owner; a want is a root of one frame, its owner's placement |
| `want-legitimacy-anti-meme-post` | or | want | `legitimacy-reasons-programme` | `legitimacy` | a want of the line's owner; a want is a root of one frame, its owner's placement |

The frames' Notes say where their former roots went (`normativity`, `legitimacy`, `operative-force`, `response-learning`); the two retired frames' Notes name this table.

### 3. Part 3 — the merges (ruling F5)

**Counts**: bagged before 244 (an `and` with a record child whose only parent is a frame; the prompt's 249 counted the five results attached only through `given` edges, which are not bagged, and 11 more sit under an `and`); merged 2; unmatched 180; ambiguous 54; blocked 8 (one candidate the protocol cannot merge into); reserved 0 (no candidate already carried a record); bagged after 242.

**The rules as applied.** Candidates for a result `R` are nodes in the same line as `R` (the subtree of a line frame `R` is in), not formal results or their leaves, frames, items or wants, matched by any of the prompt's three rules; the match is read in tiers, the strongest first, and a tier with a match ends the search: (1) *id*: the candidate's id is the registry id with its first dotted component stripped or its dots made hyphens; (2) *declaration*: the candidate's Source cites the declaration's full name, the Lean file the record names, or the declaration's last component where that component is an identifier (it carries an underscore, a capital or a digit, so `preservation` or `criterion` as English words do not match) and no other registry declaration ends in it; (3) *round*: the candidate's Source cites the result's `origin_round` directory and its Statement shares a content word with the registry `short_name` (lowercase alphabetic tokens of four letters or more, the function words, the evaluative list and the words *claim, result, theorem, holds, proved* removed, plurals folded; one shared word is the floor the prompt sets). One-to-one: a candidate that is the sole candidate of several results at one tier is ambiguous for all of them, and a stronger tier's match takes the claim (a weaker tier's sole candidate already taken is blocked). A merge needs an assertion-shaped candidate: a step or assumption leaf without `given`; a question leaf (a question's positive answer), a route leaf (a way an improvement goes), an `or` or `cases` node (which hold no record), an `and` (it has its own completeness leaf, and which survives needs a rule) or a leaf carrying `given` (an `and` may not) is listed as blocked with the reason.

| result (now an alias) | claim | matched by | the claim was | repointed |
|---|---|---|---|---|
| `kernel.box2-finite-time` | `kernel-box2-finite-time` | id | leaf/step under formalism-open-questions-0-3 | public-corrigibility-line |
| `thin.value-of-thick` | `thin-value-of-thick` | id | leaf/step under public-legitimacy-theory | authorship-and-transparency |

**Ambiguous** (several candidates, or one shared with another result at the same tier):

- `capability-beyond-oversight` (declaration tier): `rs-press-discounting` (declaration (last component)) — the candidate is also the sole candidate of `erosion-under-silence`
- `erosion-under-silence` (declaration tier): `rs-press-discounting` (declaration (last component)) — the candidate is also the sole candidate of `capability-beyond-oversight`
- `mart-implies-value-refuted-unconditional` (declaration tier): `cleanroom-deference-headlines` (declaration (last component)) — the candidate is also the sole candidate of `timely-pointwise-tower-refuted-in-setting`
- `timely-pointwise-tower-refuted-in-setting` (declaration tier): `cleanroom-deference-headlines` (declaration (last component)) — the candidate is also the sole candidate of `mart-implies-value-refuted-unconditional`
- `asklist.offprotocol-deviation-finite` (round tier): `post-corrigible-normative-learning` (origin round + shared words: protocol) — the candidate is also the sole candidate of `post.theorem`, `transparent.blind-payload`
- `asklist.rows-keep-verdicts-counted` (round tier): `effective-authority-layer` (origin round + shared words: verdict) — the candidate is also the sole candidate of `asklist.rows-keep-verdicts-tainted`, `authority.comprehension-short`, `authority.queue-no-bypass`, `authority.queue-no-caused-shortfall`, `post.witness-control-maximizer`, `shortfall.atom-generable`, `shortfall.deferred-eventually-excluded`, `shortfall.eventually-excluded`, `shortfall.table-generable`, `sincerity.rows-keep-verdicts-counted`, `sincerity.rows-keep-verdicts-tainted`, `sincerity.sincere-error-counts`
- `asklist.rows-keep-verdicts-tainted` (round tier): `effective-authority-layer` (origin round + shared words: verdict) — the candidate is also the sole candidate of `asklist.rows-keep-verdicts-counted`, `authority.comprehension-short`, `authority.queue-no-bypass`, `authority.queue-no-caused-shortfall`, `post.witness-control-maximizer`, `shortfall.atom-generable`, `shortfall.deferred-eventually-excluded`, `shortfall.eventually-excluded`, `shortfall.table-generable`, `sincerity.rows-keep-verdicts-counted`, `sincerity.rows-keep-verdicts-tainted`, `sincerity.sincere-error-counts`
- `authority.approval-discount-defeated` (round tier): `post-corrigible-normative-learning` (origin round + shared words: asking, line); `effective-authority-layer` (origin round + shared words: approval)
- `authority.comprehension-short` (round tier): `effective-authority-layer` (origin round + shared words: cannot) — the candidate is also the sole candidate of `asklist.rows-keep-verdicts-counted`, `asklist.rows-keep-verdicts-tainted`, `authority.queue-no-bypass`, `authority.queue-no-caused-shortfall`, `post.witness-control-maximizer`, `shortfall.atom-generable`, `shortfall.deferred-eventually-excluded`, `shortfall.eventually-excluded`, `shortfall.table-generable`, `sincerity.rows-keep-verdicts-counted`, `sincerity.rows-keep-verdicts-tainted`, `sincerity.sincere-error-counts`
- `authority.exchange-rate-queue` (round tier): `post-corrigible-normative-learning` (origin round + shared words: value); `authority-typed-corrigibility` (origin round + shared words: exchange, rate); `thin-value-of-thick` (origin round + shared words: value); `effective-authority-layer` (origin round + shared words: queue)
- `authority.flood-caused-shortfall` (round tier): `post-corrigible-normative-learning` (origin round + shared words: through); `authority-typed-corrigibility` (origin round + shared words: agent, only); `effective-authority-layer` (origin round + shared words: caused, count, flood, shortfall)
- `authority.queue-no-bypass` (round tier): `effective-authority-layer` (origin round + shared words: queue) — the candidate is also the sole candidate of `asklist.rows-keep-verdicts-counted`, `asklist.rows-keep-verdicts-tainted`, `authority.comprehension-short`, `authority.queue-no-caused-shortfall`, `post.witness-control-maximizer`, `shortfall.atom-generable`, `shortfall.deferred-eventually-excluded`, `shortfall.eventually-excluded`, `shortfall.table-generable`, `sincerity.rows-keep-verdicts-counted`, `sincerity.rows-keep-verdicts-tainted`, `sincerity.sincere-error-counts`
- `authority.queue-no-caused-shortfall` (round tier): `effective-authority-layer` (origin round + shared words: queue, shortfall) — the candidate is also the sole candidate of `asklist.rows-keep-verdicts-counted`, `asklist.rows-keep-verdicts-tainted`, `authority.comprehension-short`, `authority.queue-no-bypass`, `post.witness-control-maximizer`, `shortfall.atom-generable`, `shortfall.deferred-eventually-excluded`, `shortfall.eventually-excluded`, `shortfall.table-generable`, `sincerity.rows-keep-verdicts-counted`, `sincerity.rows-keep-verdicts-tainted`, `sincerity.sincere-error-counts`
- `authority.revocation-default` (round tier): `authority-typed-corrigibility` (origin round + shared words: allocation); `effective-authority-layer` (origin round + shared words: caused, revocation, shortfall)
- `kernel.box1-fidelity-versus-fully-updated-deference` (round tier): `authority-typed-corrigibility` (origin round + shared words: fidelity); `four-corrigibility-definitions` (origin round + shared words: fidelity); `kernel-lexical-order-hypothesis` (origin round + shared words: outcome)
- `kernel.box2-dominance` (round tier): `authority-typed-corrigibility` (origin round + shared words: fidelity, objective, score); `four-corrigibility-definitions` (origin round + shared words: corrigible, fidelity, score); `kernel-lexical-order-hypothesis` (origin round + shared words: score)
- `kernel.box2-mediation-faithful` (round tier): `authority-typed-corrigibility` (origin round + shared words: allocation, authority, faithful); `four-corrigibility-definitions` (origin round + shared words: faithful)
- `kernel.box3-gap-exchange-rate` (round tier): `authority-typed-corrigibility` (origin round + shared words: only, risk) — the candidate is also the sole candidate of `kernel.extension-exploration-realization`, `post.witness-learned-weight`
- `kernel.box3-no-incentive-to-compromise` (round tier): `kernel-box2-finite-time` (origin round + shared words: below); `authority-typed-corrigibility` (origin round + shared words: score); `four-corrigibility-definitions` (origin round + shared words: legitimacy, legitimate, score); `kernel-lexical-order-hypothesis` (origin round + shared words: below, compromised, equal, legitimacy, legitimate, outcome, score, value, worth)
- `kernel.box3-no-laundering` (round tier): `kernel-box2-finite-time` (origin round + shared words: below); `kernel-lexical-order-hypothesis` (origin round + shared words: below)
- `kernel.box3-restoration` (round tier): `authority-typed-corrigibility` (origin round + shared words: agent, prefer); `kernel-lexical-order-hypothesis` (origin round + shared words: outcome, value)
- `kernel.corrigible-fidelity-score` (round tier): `authority-typed-corrigibility` (origin round + shared words: fidelity, only, risk, score, unfaithfulnes); `four-corrigibility-definitions` (origin round + shared words: corrigible, fidelity, score); `kernel-lexical-order-hypothesis` (origin round + shared words: score, value)
- `kernel.corrigible-generic` (round tier): `authority-typed-corrigibility` (origin round + shared words: objective, risk); `four-corrigibility-definitions` (origin round + shared words: corrigible)
- `kernel.extension-exploration-realization` (round tier): `authority-typed-corrigibility` (origin round + shared words: rate) — the candidate is also the sole candidate of `kernel.box3-gap-exchange-rate`, `post.witness-learned-weight`
- `kernel.hierarchy-per-decision` (round tier): `four-corrigibility-definitions` (origin round + shared words: legitimate); `kernel-lexical-order-hypothesis` (origin round + shared words: compromised, legitimate)
- `kernel.subjective-exchange-rate` (round tier): `kernel-box2-finite-time` (origin round + shared words: option); `authority-typed-corrigibility` (origin round + shared words: fidelity, objective, prefer, score, unfaithfulnes); `four-corrigibility-definitions` (origin round + shared words: corrigible, fidelity, score); `kernel-lexical-order-hypothesis` (origin round + shared words: score)
- `legitimacy.payload-of-view` (round tier): `post-corrigible-normative-learning` (origin round + shared words: declared, legitimacy); `cnl-post` (origin round + shared words: legitimacy)
- `post.flood-below-asking` (round tier): `post-corrigible-normative-learning` (origin round + shared words: asking, protocol); `authority-typed-corrigibility` (origin round + shared words: score); `effective-authority-layer` (origin round + shared words: flood)
- `post.theorem` (round tier): `post-corrigible-normative-learning` (origin round + shared words: post) — the candidate is also the sole candidate of `asklist.offprotocol-deviation-finite`, `transparent.blind-payload`
- `post.theorem-li` (round tier): `post-corrigible-normative-learning` (origin round + shared words: post); `thin-value-of-thick` (origin round + shared words: decision, finite)
- `post.witness-control-maximizer` (round tier): `effective-authority-layer` (origin round + shared words: flood, revocation, shortfall) — the candidate is also the sole candidate of `asklist.rows-keep-verdicts-counted`, `asklist.rows-keep-verdicts-tainted`, `authority.comprehension-short`, `authority.queue-no-bypass`, `authority.queue-no-caused-shortfall`, `shortfall.atom-generable`, `shortfall.deferred-eventually-excluded`, `shortfall.eventually-excluded`, `shortfall.table-generable`, `sincerity.rows-keep-verdicts-counted`, `sincerity.rows-keep-verdicts-tainted`, `sincerity.sincere-error-counts`
- `post.witness-hindsight` (round tier): `post-corrigible-normative-learning` (origin round + shared words: value); `thin-value-of-thick` (origin round + shared words: value); `effective-authority-layer` (origin round + shared words: approval)
- `post.witness-learned-weight` (round tier): `authority-typed-corrigibility` (origin round + shared words: fixed) — the candidate is also the sole candidate of `kernel.box3-gap-exchange-rate`, `kernel.extension-exploration-realization`
- `post.witness-sole-authority` (round tier): `authority-typed-corrigibility` (origin round + shared words: authority, risk); `effective-authority-layer` (origin round + shared words: authority)
- `shortfall.atom-generable` (round tier): `effective-authority-layer` (origin round + shared words: shortfall) — the candidate is also the sole candidate of `asklist.rows-keep-verdicts-counted`, `asklist.rows-keep-verdicts-tainted`, `authority.comprehension-short`, `authority.queue-no-bypass`, `authority.queue-no-caused-shortfall`, `post.witness-control-maximizer`, `shortfall.deferred-eventually-excluded`, `shortfall.eventually-excluded`, `shortfall.table-generable`, `sincerity.rows-keep-verdicts-counted`, `sincerity.rows-keep-verdicts-tainted`, `sincerity.sincere-error-counts`
- `shortfall.deferred-ahead` (round tier): `authority-typed-corrigibility` (origin round + shared words: only); `effective-authority-layer` (origin round + shared words: shortfall)
- `shortfall.deferred-eventually-excluded` (round tier): `effective-authority-layer` (origin round + shared words: shortfall) — the candidate is also the sole candidate of `asklist.rows-keep-verdicts-counted`, `asklist.rows-keep-verdicts-tainted`, `authority.comprehension-short`, `authority.queue-no-bypass`, `authority.queue-no-caused-shortfall`, `post.witness-control-maximizer`, `shortfall.atom-generable`, `shortfall.eventually-excluded`, `shortfall.table-generable`, `sincerity.rows-keep-verdicts-counted`, `sincerity.rows-keep-verdicts-tainted`, `sincerity.sincere-error-counts`
- `shortfall.eventually-excluded` (round tier): `effective-authority-layer` (origin round + shared words: shortfall) — the candidate is also the sole candidate of `asklist.rows-keep-verdicts-counted`, `asklist.rows-keep-verdicts-tainted`, `authority.comprehension-short`, `authority.queue-no-bypass`, `authority.queue-no-caused-shortfall`, `post.witness-control-maximizer`, `shortfall.atom-generable`, `shortfall.deferred-eventually-excluded`, `shortfall.table-generable`, `sincerity.rows-keep-verdicts-counted`, `sincerity.rows-keep-verdicts-tainted`, `sincerity.sincere-error-counts`
- `shortfall.security-generable` (round tier): `authority-typed-corrigibility` (origin round + shared words: fixed); `thin-value-of-thick` (origin round + shared words: finite); `effective-authority-layer` (origin round + shared words: shortfall)
- `shortfall.table-generable` (round tier): `effective-authority-layer` (origin round + shared words: shortfall) — the candidate is also the sole candidate of `asklist.rows-keep-verdicts-counted`, `asklist.rows-keep-verdicts-tainted`, `authority.comprehension-short`, `authority.queue-no-bypass`, `authority.queue-no-caused-shortfall`, `post.witness-control-maximizer`, `shortfall.atom-generable`, `shortfall.deferred-eventually-excluded`, `shortfall.eventually-excluded`, `sincerity.rows-keep-verdicts-counted`, `sincerity.rows-keep-verdicts-tainted`, `sincerity.sincere-error-counts`
- `sincerity.lie-tainted` (round tier): `post-corrigible-normative-learning` (origin round + shared words: declared, through, transparency); `thin-value-of-thick` (origin round + shared words: transparency)
- `sincerity.rows-keep-verdicts-counted` (round tier): `effective-authority-layer` (origin round + shared words: verdict) — the candidate is also the sole candidate of `asklist.rows-keep-verdicts-counted`, `asklist.rows-keep-verdicts-tainted`, `authority.comprehension-short`, `authority.queue-no-bypass`, `authority.queue-no-caused-shortfall`, `post.witness-control-maximizer`, `shortfall.atom-generable`, `shortfall.deferred-eventually-excluded`, `shortfall.eventually-excluded`, `shortfall.table-generable`, `sincerity.rows-keep-verdicts-tainted`, `sincerity.sincere-error-counts`
- `sincerity.rows-keep-verdicts-tainted` (round tier): `effective-authority-layer` (origin round + shared words: verdict) — the candidate is also the sole candidate of `asklist.rows-keep-verdicts-counted`, `asklist.rows-keep-verdicts-tainted`, `authority.comprehension-short`, `authority.queue-no-bypass`, `authority.queue-no-caused-shortfall`, `post.witness-control-maximizer`, `shortfall.atom-generable`, `shortfall.deferred-eventually-excluded`, `shortfall.eventually-excluded`, `shortfall.table-generable`, `sincerity.rows-keep-verdicts-counted`, `sincerity.sincere-error-counts`
- `sincerity.sincere-error-counts` (round tier): `effective-authority-layer` (origin round + shared words: count) — the candidate is also the sole candidate of `asklist.rows-keep-verdicts-counted`, `asklist.rows-keep-verdicts-tainted`, `authority.comprehension-short`, `authority.queue-no-bypass`, `authority.queue-no-caused-shortfall`, `post.witness-control-maximizer`, `shortfall.atom-generable`, `shortfall.deferred-eventually-excluded`, `shortfall.eventually-excluded`, `shortfall.table-generable`, `sincerity.rows-keep-verdicts-counted`, `sincerity.rows-keep-verdicts-tainted`
- `thin.converse-fails-on-correct` (round tier): `post-corrigible-normative-learning` (origin round + shared words: correct, value); `thin-value-of-thick` (origin round + shared words: correct, value)
- `thin.correct-of-thick` (round tier): `post-corrigible-normative-learning` (origin round + shared words: correct, transparency); `thin-value-of-thick` (origin round + shared words: authorship, coherence, correct, give, transparency)
- `thin.covert-blocking-correct-iff` (round tier): `post-corrigible-normative-learning` (origin round + shared words: correct); `thin-value-of-thick` (origin round + shared words: correct)
- `thin.marginal-martingale-too-weak` (round tier): `post-corrigible-normative-learning` (origin round + shared words: correct); `thin-value-of-thick` (origin round + shared words: correct)
- `thin.preservation` (round tier): `post-corrigible-normative-learning` (origin round + shared words: transparency); `thin-value-of-thick` (origin round + shared words: authorship, give, transparency)
- `thin.reflection-inherited-value` (round tier): `post-corrigible-normative-learning` (origin round + shared words: correct, through, value); `thin-value-of-thick` (origin round + shared words: correct, value)
- `thin.sufficient-of-integrity-openness` (round tier): `post-corrigible-normative-learning` (origin round + shared words: sufficient); `thin-value-of-thick` (origin round + shared words: give, integrity, opennes, sufficient)
- `thin.value-loss-le-defects` (round tier): `post-corrigible-normative-learning` (origin round + shared words: transparency, value); `thin-value-of-thick` (origin round + shared words: authorship, transparency, value)
- `thin.value-of-correct-sufficient` (round tier): `post-corrigible-normative-learning` (origin round + shared words: correct, sufficient, value); `thin-value-of-thick` (origin round + shared words: correct, give, sufficient, value)
- `transparent.blind-payload` (round tier): `post-corrigible-normative-learning` (origin round + shared words: declared) — the candidate is also the sole candidate of `asklist.offprotocol-deviation-finite`, `post.theorem`

**Blocked** (one candidate the protocol cannot merge into):

- `anticipation-branchwise-dominance--corrigibility-risk` → `rs-mistaken-anticipation` (declaration (last component)): the candidate carries given (rules-certified-or-learned), which an and may not; a conditional leaf stays a leaf
- `deterrence-not-identified-on-path` → `anger-substitute-for-updatelessness` (declaration (last component)): the candidate is a cases node, which cannot hold a record
- `kernel-conditioning-fails-witness` → `rs-no-strategic-legitimacy-defense` (declaration (last component)): the candidate carries given (kernel-conditioning-fails-witness@valid), which an and may not; it is conditioned on the result itself
- `li-deference-collapse-scoped` → `route-immodest-regular-value` (declaration (last component)): the candidate is a route leaf (a way the improvement goes, not an assertion the record establishes)
- `local-criterion-three-cells` → `question-relative-deference-li` (declaration (last component)): the candidate is a question leaf (a question's positive answer, not an assertion the record establishes)
- `uea-floored-agent-theorem` → `uea-floor-log-form` (declaration): the candidate is a route leaf (a way the improvement goes, not an assertion the record establishes)
- `void-branch-deterrence-floor--corrigibility-risk` → `rs-captor-service` (declaration (last component)): the candidate carries given (kernel-restoration@valid), which an and may not; it is conditioned on the result itself
- `thin.preservation-pair` → `thin-value-of-thick` (origin round + shared words: integrity): the candidate is the id-tier match of thin.value-of-thick, which carries its record


**Unmatched** (no candidate):

`agency-correspondence-refuted`, `asklist.order-by-want-tainted`, `asklist.volume-by-want-tainted`, `authorship.mediation-by-reexecution`, `base-rate-working-picture`, `basin-formal-object`, `bli-exactness-limits`, `bli-sources-refuted`, `carey-everitt-thm10-vacuous`, `cdt-defined-for-learner`, `certificate.advantage-estimate`, `certificate.defect-bound`, `certificate.grade-register-strict`, `certificate.margin-forces-agreement`, `certificate.override-bound`, `certificate.selection-eq-of-margin`, `coherence.modulus-net-cover`, `coherence.modulus-soundness`, `compiler.constraints-end-to-end`, `compiler.deductive-end-to-end`, `compiler.schedule-end-to-end`, `condensation-correspondence-theorem`, `condensation-equivalence-ae`, `conditioning-manages-news`, `convergence.discord-pairwise`, `convergence.discord-persists`, `convergence.hull-mass-anti`, `corrective.advisor-veto`, `corrective.can-correct-future-iff`, `corrective.can-correct-iff`, `corrective.capability-measures-cooperation`, `corrective.forecloses-iff`, `corrective.no-exclusive-effect`, `counterfactual-mugging-with-evidence`, `dd-is-conditional-independence`, `ddb-finite-frames-formalized`, `deconfusing.corollary-a`, `deconfusing.corollary-b`, `deconfusing.corollary-limit`, `deconfusing.theorem1`, `deconfusing.theorem2a`, `deconfusing.theorem2b`, `deconfusing.theorem2b-strict`, `deconfusing.theorem2c`, `deconfusing.theorem2c-tau`, `deconfusing.theorem3a`, `deconfusing.theorem3a-rate`, `deconfusing.theorem3b`, `delegation.bridge`, `delegation.bridge-unconditional`, `delegation.gradetrust-refinement`, `dp-dutch-book-done`, `exact-self-trust-refuted`, `exposure.greedy-duality`, `exposure.harvest-attained`, `exposure.harvest-bound`, `fa-trust-half-weak-grades`, `force.deductive-criterion`, `force.deductive-cumulative-nonneg`, `force.deductive-day-nonneg`, `force.deductive-inductor`, `force.deductive-witness`, `force.preservation`, `force.row-tolerance`, `force.strategy-value`, `front-running-anticipated-pushes`, `general-modification-object`, `generalized-lic`, `harmony-as-bargaining`, `hedged-value-unconditional`, `inductor.certificate-transport`, `inductor.conformance`, `inductor.contraposition-blocked`, `inductor.grounded-survivors`, `inductor.rebuttal-run`, `inductor.warrant-inductor`, `inductor.witness`, `inferability-and-positivity`, `inferability-positivity`, `integrity.evolution-conservation`, `integrity.faithful-carry`, `integrity.multiplicity-witness`, `integrity.propagate-to-segment`, `integrity.receipts-immutable`, `jurisdiction.static-view-eq`, `jurisdiction.value-eq-of-price-realization`, `kernel-restoration`, `kernel.extension-bria-realization`, `kernel.extension-realized-rate`, `kernel.hierarchy-history`, `learning-versus-freezing`, `legit-composition`, `legit-ddb-transfer`, `legit-locality-forced`, `legit-reflection-unsat-modest`, `legitimacy-conditioned-reflection`, `legitimacy.answerable`, `legitimacy.endpoint-only-insufficient`, `legitimacy.endpoint-trans`, `legitimacy.evolution-conservation`, `legitimacy.faithful-carry`, `legitimacy.multiplicity-witness`, `legitimacy.propagate-to-segment`, `legitimacy.receipts-immutable`, `legitimacy.segment-trans`, `li-corrigibilization-theorem`, `li.assessment.budgeter-exploits`, `li.assessment.budgeter-floor`, `li.assessment.budgeter-value`, `li.assessment.criterion`, `li.assessment.firm-dominance`, `magnitude.mixture-networth-zero`, `magnitude.not-trader-payoff`, `magnitude.sharp-trader-networth`, `magnitude.signed-bounded`, `magnitude.signed-bounded-actual`, `magnitude.sq-error-split`, `magnitude.unit-trader-networth`, `maxmin.converse`, `maxmin.representation`, `mm-theorem-3-4-refuted`, `ni.progress-bound`, `open-integrity.answerable`, `open-integrity.endpoint-trans`, `open-integrity.segment-trans`, `openness.actual-branch-witness`, `openness.certplus-is-robust-openness`, `openness.endpoint-only-insufficient`, `openness.persistence-sufficient`, `osg-theorem1-corollary`, `p2-manages-the-news`, `post.witness-same-level`, `pressure-as-external-trader`, `progress.edge-bound`, `progress.edge-bound-quadratic`, `progress.headline-separation`, `ps-cor614-orbit-count`, `rebuttal.liability-rebutted`, `rebuttal.settleform-sound`, `region.hull`, `region.patterns-complete`, `region.patterns-nonempty-iff`, `region.patterns-sound`, `ro-ftc-finite-core-from-brouwer`, `ro-generalized-kakutani-refuted`, `seed.eventually-const`, `seed.forced-interval-bounds`, `seed.forced-interval-spec`, `seed.independence-strict`, `selection-collapse--corrigibility-risk`, `shutdown-button-toy`, `simplex.rational-points-sum-to-one`, `sincerity.content-fact`, `smoke.chain-compiles`, `smoke.faf-asymp-refl`, `substitution.extensional-admits-both`, `substitution.separation-requires-disagreement`, `substitution.sim-depends-on-induced-choice`, `substitution.unpredictability-separates`, `thornley-three-theorems`, `trace-nonrecoverability`, `transparent.posterior-weight-eq`, `tt-finite-frames-settled`, `turner-vnm-fact`, `two-lesions-propositions-checked`, `udt-trust-existence-and-tightness`, `udt101-influence-calculus`, `uea-horizon-quantifiers`, `uea-post-usc-backwards`, `uea-printed-2025-refuted`, `uea-sink-or-swim-trap`, `uea-t1-key-lemma-refuted-finite`, `updateful-when-appropriate`, `updateless-p2-cellwise-p3`, `warrant.admissible-not-supported`, `warrant.licence-chain`, `warrant.selection-not-transparent`, `warrant.supported-admissible`, `warrant.supported-not-licensed`, `wirehead-iff-finite`

**What the lists say.** Both merges are id matches: the round filed `kernel-box2-finite-time` and `thin-value-of-thick` as steps and later registered the same statements under the dotted ids, and the two now hold their records. Forty-nine of the fifty-four ambiguous results are round-tier matches onto six summary claims (`effective-authority-layer`, `post-corrigible-normative-learning`, `thin-value-of-thick`, `authority-typed-corrigibility`, `kernel-lexical-order-hypothesis`, `four-corrigibility-definitions`), each the informal statement of a *cluster* of registered declarations; an `and` holds one record and one bridge, so a claim established by seven declarations has no shape in the protocol and no mechanical rule can place the seven. That gap, not the matching, is what the ambiguous list measures; it is queued (§9). The 180 unmatched results are registry entries whose claims the map never stated informally (the deference `corrective.*`, `deconfusing.*`, `magnitude.*`, `substitution.*` and `certificate.*` families, the normativity `force.*`, `region.*`, `warrant.*` and `progress.*` families, most of the clean-room records): the map's informal layer stops at the round summaries.

### 4. Part 4 — the dockets (ruling F6)

**The rules as applied.** A programme's origin rounds are the `origin_round` paths of the registry entries whose formal results sit under it (through `state/rounds.json`); an item in a line's docket whose `context` paths lie under exactly one programme's origin round, that programme in the item's own line, moves to a docket under it; an item whose round is shared by programmes of two lines, or whose only hit is a programme of another line, stays and is listed; the project marker `normativity.seed` names `seed-theory`, whose docket already held the six seed items. The line is the item's `project` marker's (`normativity`, `normativity.seed` → normativity; `normativity.legitimacy` → legitimacy; `deference` → deference-and-trust; `none` → enabling-work). The rule was applied inside `normativity` and `legitimacy`; a hit in `deference-and-trust` is listed, not applied (the second maintainer's line).

| docket | before | after |
|---|---|---|
| `docket-deference` | 38 | 38 |
| `docket-legitimacy` | 22 | 22 |
| `docket-normative-inductor` | — | 1 |
| `docket-normativity` | 39 | 36 |
| `docket-operative-force` | — | 1 |
| `docket-seed` | 6 | 7 |
| `docket-workspace` | 15 | 15 |

**Items with evidence** (every item whose context or marker names a programme's round):

- `item-10` (project none, in `docket-workspace`): cross-line: context under prompts/2026-08-10-repo-scaffolding (origin round of operative-force's results, line normativity); not applied, the item stays in its line's docket
- `item-117` (project normativity.seed, in `docket-seed`): project marker normativity.seed names the subproject whose programme is seed-theory; already there
- `item-118` (project normativity.seed, in `docket-seed`): project marker normativity.seed names the subproject whose programme is seed-theory; already there
- `item-119` (project normativity.seed, in `docket-seed`): project marker normativity.seed names the subproject whose programme is seed-theory; already there
- `item-120` (project normativity.seed, in `docket-seed`): project marker normativity.seed names the subproject whose programme is seed-theory; already there
- `item-121` (project normativity.seed, in `docket-seed`): context under projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end, the origin round of seed-theory's results; already there
- `item-122` (project normativity.seed, in `docket-seed`): project marker normativity.seed names the subproject whose programme is seed-theory; already there
- `item-123` (project normativity, in `docket-normativity`): context under projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end, the origin round of seed-theory's results — **moved**
- `item-124` (project normativity, in `docket-normativity`): context under projects/normativity/rounds/2026-10-22-normative-inductor-integration, the origin round of normative-inductor's results — **moved**
- `item-24` (project deference, in `docket-deference`): context under prompts/2026-08-11-phase-ii-prediction, the origin round of deference-finite-results's results; not applied: the reorganization of deference-and-trust is the second maintainer's
- `item-39` (project normativity, in `docket-normativity`): context under projects/normativity/rounds/2026-08-16-traderized-enforcement, the origin round of operative-force's results — **moved**
- `item-61` (project normativity.legitimacy, in `docket-legitimacy`): cross-line: context under projects/normativity/rounds/2026-08-16-traderized-enforcement (origin round of operative-force's results, line normativity); not applied, the item stays in its line's docket
- `item-78` (project normativity, in `docket-normativity`): ambiguous: its context round (projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass) registered results of normative-inductor (normativity) and of integrity-and-record and openness-and-non-capture (legitimacy); a round several programmes share places nothing; stays
- `item-88` (project normativity.legitimacy, in `docket-legitimacy`): cross-line: context under projects/normativity/rounds/2026-08-16-traderized-enforcement (origin round of operative-force's results, line normativity); not applied, the item stays in its line's docket

Three items moved (`item-39` → `docket-operative-force`, new; `item-124` → `docket-normative-inductor`, new; `item-123` → `docket-seed`); the two new dockets are shared-claim roots of their programmes. Not applied, each listed above with its evidence: `item-78` (its round registered results of `normative-inductor` and of two legitimacy programmes: a shared round places nothing), `item-61` and `item-88` (legitimacy items whose context is the traderized-enforcement round of `operative-force`: cross-line), `item-10` (a workspace item whose context is the repo-scaffolding round, from which the two `smoke.*` entries under `operative-force` were registered: cross-line, and the smoke claims are no programme's results in any reading), `item-24` (the second maintainer's line). Every docket's Statement now reads *Work orders filed against <programme>, not yet attached to the goal each serves; their placement is the maintainer's* (seven dockets; the five existing ones version-bumped, since a Statement change without a bump is refused).

**Representation.** A docket is an `or` node tagged `either-suffices`, a shared-claim root of its frame. That form makes it a goal of the ranking with a derived probability and a status, which it is not: a work order with no goal identified asserts nothing, and "some filed work order is executed" was a sentence written to give the `or` a Statement. A `dockets` field on a frame — the item ids the frame's work orders are, read by the index as the frame's work orders and by the ranking as routes under no goal, carrying no status — would represent it more honestly. Proposed in a design-log line, not applied; queued (§9).

### 5. Protocol and checker changes

| change | rule | design-log line |
|---|---|---|
| `hypotheses: unread` on a record; a list mixing ids with the word refused; the record and its `and` flagged *hypotheses unread* in `derived.json`, the index and the view, and as a unit signal | 2 (and 1 no longer reads `unread` as an id) | 2026-10-23, "ruling F1 …" |
| `registry_id` on a record; a `priorities` pointer on every registry-built result; index schema `graph-index/2` (`items[].answered_by`, `formal_result`, `claims`); the render's *Registered answers in the map* line | — (index schema; the render gate reads the same nodes) | 2026-10-23, "ruling F2 …" |
| a retired frame (`superseded_by`) is exempt from "a frame node is a plan root of some frame", holds no roots and no children, is no spell-out candidate and carries no *unspelled* flag | 2 | 2026-10-23, "ruling F4 …" |
| the merge pattern (a claim's `and` gains a result's record, bridge and completeness; the result's `and` superseded) needs no checker change; `claims` in the index resolves the registry id | — | 2026-10-23, "ruling F5 …" |
| docket Statements rewritten; a docket stays a shared-claim `or` root; a frame field proposed | — | 2026-10-23, "ruling F6 …" and the proposal line |
| `graph/derived.json` and `graph/index.json` uncommitted (`.gitignore`; the ci job uploads both as artifacts; the `derived` workflow publishes `main`'s through `derived-publish`, enumerated in `AGENTS.md`); `versions.json` records both derivation hashes under `generated`; `previous_derivation` reads the branch `derived`, else the file on disk that `versions.json` at HEAD records; the `DIGEST` line names the source; the digest leaves `tasks.md` | 7 unchanged (a hand edit of a generated file on disk is still refused); `WORKFLOW SCOPE` conditions 1–5 | 2026-10-23, "ruling F3 …" |

Protocol text: §2 *Formal results* (unread hypotheses, `registry_id`, the priorities edge), §9 rule 2 (the hypotheses clause; retired frames), the file table (which generated files are committed), §6's digest paragraph, the glossary's docket and index entries. `graph/MAP-AS-CANONICAL.md` §6.1 is schema 2. `graph/README.md` step 1 and `AGENTS.md` *Commit only what the plain run writes* say which files are committed; `AGENTS.md` *Security* enumerates `derived-publish`.

Tests: `test_record_hypotheses_unread` (the flag in the three places, the refusals) and `test_index_schema_two_on_the_fixture` (the inversion, the claims map, the retired frames, the render line) added; two null inputs in the checker's self-test (a mixed hypotheses list; a retired frame still holding roots); the plain-run test tolerates the `DIGEST` line.

### 6. Deviations from this prompt, with reasons

- **The publish step is a separate workflow, `.github/workflows/derived.yml`, not a step of `ci.yml`.** `tests/workflow_scope.py` refuses write scope in any workflow triggered on `pull_request`, and `ci.yml` is; AGENTS.md's condition 1 says why. `ci.yml` gained the read-scope half (the plain run and the artifact upload on every run); the write-scope job `derived-publish` lives in the new workflow behind `push` to `main`, reads the artifact of its read-scope sibling and runs `.github/derived-publish.sh`, which commits the two files as data and verifies the branch after the push (condition 5). The gate passes with the enumeration extended.
- **The digest left `tasks.md`.** Its comparison is now whatever derivation is at hand (the branch `derived` after a fetch, or the file on disk when it is the derivation `HEAD` records), and a committed file that read it would change on a fetch or a rerun. The digest stays in `derived.json` and on the `DIGEST` line, which names its source as the ruling asks; `tasks.md` keeps the spell-out candidates, the agent work and the proposals awaiting.
- **`versions.json` records a derivation hash, not the files' `generated_hash`.** The hash leaves out the digest (which varies with the comparison) and the day's audit draw (which varies with the date), so a rerun on another day or beside another `derived` branch leaves `versions.json` unchanged; each file's own `generated_hash` still covers all of it and a hand edit is refused as before. "A stale derivation is refused" is read as: a derivation whose hash is not the one `versions.json` records is never taken for the previous derivation.
- **F6 was applied inside `normativity` and `legitimacy`, and a round shared by programmes of two lines places nothing.** The ruling names no line, but a docket under `deference-finite-results` reorganizes `deference-and-trust`, which F4 reserves to the second maintainer, so `item-24` is listed and left; `item-78` would have gone to `normative-inductor` on the one hit in its own line while its round also registered the legitimacy spine's results, and its title (*Canonicalize the legitimacy spine*) says the mechanical placement would have been wrong, so a shared round is read as no evidence.
- **F5's candidates are assertion-shaped and the match is tiered.** A question or route leaf, an `or`, a `cases`, an `and` with its own completeness leaf and a leaf carrying `given` are listed as blocked rather than merged (the first two are not assertions a record establishes; the others the protocol cannot give a record without a further rule); the declaration's last component counts only as an identifier; and the id rule beats a round-tier match so that `thin.value-of-thick` goes to the node named after it rather than being lost to the eleven other `thin.*` results that cite the same round. Two merges result; the prompt's "the target is not zero bagged results" is taken at its word.
- **Completeness leaves and docket Statements carry a version bump.** Rule 4 refuses a Statement change without one; 178 completeness leaves are at `version: 2` (the Statement names the conjuncts and the unread hypotheses) and the five existing dockets likewise.
- **The ruling text drops the backticks around the two removed paths** (`graph/derived.json`, `graph/index.json` in F3) and the round's PROVENANCE row names graph/index.json without backticks: `tests/dead_pointers.py` refuses a backticked path that does not exist and `tests/untracked_pointers.py` one that exists on disk and is not in the repository (the second gate does not read the `historical` marker the first does), which both are after the fifth commit. No ruling is reworded; an italic note after the entry carries the corrected counts.
- **The two new dockets' Sources cite the evidence rule, not the project marker**, since the marker (`normativity`) is the line's and placed nothing.

### 7. Corrections to this prompt

- "249 of 260 formal results have a frame as their only parent" — 244; five more (`ro-collapse-repair`, `udt-trust-margin-reading`, `udt-trust-pointwise-refuted`, `udt-trust-repaired`, `uea-plain-agent-bound`) have no parent and are attached only as the `given` parent of another node or row, and 11 sit under an `and`.
- "681 script-parsed hypothesis and setting leaves", "511 hypothesis leaves and 170 setting leaves" — 646: 511 hypothesis leaves and 135 setting leaves (50 of the 178 results had no proposition binder and 43 no data binder). The 68 pre-existing hypothesis leaves include the clean-room `.setting` leaves; untouched.
- "add the `derived` branch publish step to `.github/workflows/ci.yml`" — not possible under the repository's own gate (§6, first item); the read-scope half is there, the write-scope job is in `derived.yml`.
- "`derived.json` grew to 15 MB" — 14.8 MB (14,769,185 bytes) at `86e3f35`; `index.json` 3.7 MB; `versions.json` 833 KB.
- "the function that reads `HEAD:./graph/derived.json`" is `previous_derivation` in `checkers/graph.py`; confirmed, replaced as the ruling says.
- "every formal result built from a registry entry with an `answers_item`" — all 178 entries carry one (a string); every value resolves to an item node.
- The pattern `legit-composition` / `legit-composition.record` has a fourth conjunct, `legit-composition.setting`, a hypothesis leaf filed by reading; a merged claim copies the result's children whatever they are, so the pattern holds either way.
- Everything else named in the prompt (paths, fields, kinds, node ids, the 27 sub-frames, the 68 pre-existing leaves) exists at `86e3f35` as stated.

### 8. What this follow-up did not do

The reorganization of the second maintainer's lines (`deference-and-trust`, `decision-theory`, `stance-and-level`, `abstraction-arc`, `enabling-work`, including `item-24`'s placement and the thirteen sub-frames there); attaching the 180 unmatched, 54 ambiguous and 8 blocked results; placing any item under the goal it serves (the dockets say so in their Statements); filing any hypothesis by reading (every registry-built record says *unread*); the site; a `dockets` frame field (proposed, not applied); confirming any drafted frame (the `filed_from: wiki` flags stand); any number, judgment, acceptance, priority word or human event.

### 9. Additions to the reserved list

Queued in `DECISIONS.md`, *Awaiting the author*, each with its *turns on* line and an anchor:

- **The ambiguous and blocked merges of F5** (54 and 8, §3). *Turns on:* which claim a result establishes where several summary claims cite one round, and whether a claim established by several registered declarations gets a shape of its own — a reading of the mathematics, not a mechanical rule.
- **How a docket is represented** (§4). *Turns on:* whether a work order with no goal identified should count as a goal of the ranking at all — what the map's numbers are for.
- **Whether `tasks.md` and `view.md` follow the derived files out of the tree** (their sizes in §1). *Turns on:* whether a reviewer reads the renders in the diff or on the published branch — where review happens, once the site exists.

### 10. Test output

```
WORKFLOW SCOPE: clean over 4 workflow(s); 3 enumerated write-scope job(s)
DEAD POINTERS: clean over 58 live document(s) — 926 rooted path(s) resolve, 8 of them into declared trees and each saying so; 105 unrooted and 221 glob(s) not this gate's business; 14 historical span(s) and 5 ledger citation(s) exempt
UNTRACKED POINTERS: clean — 333 round-record path(s) and 981 resolving citation(s) are in the repository, not merely on this disk
WORKSPACE STATE: valid — 6 projects, 178 modern claims, 1 foundations, 180 foundation claims, 126 rounds, 52 terms, 137 priorities, 10 interface objects
WIKI REFS: clean over 34 page(s); 304 reference(s) resolve
PRIORITIES RENDER: the committed file equals the render (137 items)
Ran 142 tests in 115.050s

OK
GATE COVERAGE: 11 gate scripts, all invoked (5 self-test only — no local form)
LEAN SORRY GATE: clean over 108 files
LEAN AXIOM DISCIPLINE: every file carries `#print axioms`
PROJECTS:
LEAN BUILD SKIPPED: set WORKSPACE_LEAN=1 to run `lake build`
ALL GREEN (80 project(s))
  … 80 PASS lines, one per project runner, elided (the run on the fifth commit's tree; the sixth commit changes documents only and its run is green too)
```

## Second follow-up of 2026-10-23

Prompt: `prompts/2026-10-22-map-as-canonical/PROMPT-followup-2.md`, verbatim. Rulings G1–G4 landed as one dated `DECISIONS.md` entry (anchor `2026-10-23--map-second-follow-up-digest-one-shape-frames-hold-bearing-unconfirmed-want-weighs-nothing`), the first commit of this follow-up, with the second maintainer's confirmation appended to the round's M1–M8 queue entry; the queued entry *How a docket is represented* is closed by G2. Auto-merge stays off. Every commit was preceded by `python3 -m checkers.graph --root .`, `python3 tests/run.py` and, at the commits that touch the checker, `python3 -m unittest discover -s checkers/tests -t .` in a detached checkout of the commit under test with no `graph/derived.json` on disk and no `derived` branch (the state CI is in). Commits above `4dc8811`: `c81f0ca4` (the rulings), `92b973c0` (G1), `b183ad66` (G2), `1d0c2e25` (G3), `84872ad5` (G4), `eaee0762` (Part 4) and the report commit.

### 1. Verification

Before (the branch at `4dc8811`, the CI run of that head): the checker `OK 2415 nodes, 2411 events, 3389 ranked units`; CI red on one test, `test_table_filed_on_the_fixture_passes`, `KeyError: 'statuses_flipped'` (`Ran 142 tests … FAILED (errors=1)`); no other test failed there.

After (the last commit):

- the checker: `OK 2408 nodes, 2411 events, 1886 ranked units; research first: the decision term (printed, not applied) favours vet hull-condition-total-trust (ranked unit 16), D 0.00016`, one WARN (the summary of unpointed decision anchors, `244 of 295`), and `DIGEST compared with graph/derived.json on disk (the derivation versions.json at HEAD records): 0 status(es) flipped, 0 root status(es) flipped, 0 level(s) moved, 0 event(s) counted since, 0 revision(s), 0 want(s) filed since, 0 proposal(s) awaiting`;
- `tests/run.py`: `ALL GREEN (80 project(s))` (the gates' lines in §9);
- the unit tests the way CI runs them, in the CI-shaped checkout: ``Ran 146 tests in 108.321s`, `OK``.

Node count 2415 → 2408 (the seven docket files). Ranked units 3389 → 1886: the 177 formal results and 120 items that were goals of the ranking as shared-claim roots are held now, so the units that read them for their own entropy are gone; the units on the claims that remain roots are unchanged in kind.

Root counts per frame before (`4dc8811`) and after, with what each frame now holds; the 32 other frames have the roots they had and hold nothing. The top frame holds nothing.

| frame | roots before | roots after | held |
|---|---|---|---|
| `authorship-and-transparency` | 31 | 11 | 20 |
| `deference-and-trust` | 29 | 28 | 38 |
| `deference-finite-results` | 31 | 0 | 31 |
| `enabling-work` | 8 | 7 | 15 |
| `integrity-and-record` | 17 | 0 | 17 |
| `legitimacy` | 72 | 11 | 82 |
| `normative-inductor` | 18 | 1 | 17 |
| `normativity` | 9 | 8 | 36 |
| `openness-and-non-capture` | 4 | 0 | 4 |
| `operative-force` | 29 | 1 | 28 |
| `public-corrigibility-line` | 65 | 12 | 53 |
| `seed-theory` | 10 | 0 | 16 |

Held nodes in all: 357, in 12 frames. Frames whose `roots` became empty: `deference-finite-results`, `integrity-and-record`, `openness-and-non-capture`, `seed-theory`; each is flagged *spelled; nothing yet a goal (N held)* and is no spell-out candidate (spell-out candidates 13 → 13).

### 2. Part 1 — the digest has one shape (G1)

`digest()` returns the same eight keys whatever `previous_derivation` found: with nothing to compare with, `compared_with` is null, the four lists are empty, `events_new` is 0, and `proposals_awaiting` lists the proposals awaiting approval as before (see §7, deviations). `digest_line` prints `DIGEST no previous derivation to compare with …` when `compared_with` is null, as before. `DIGEST_KEYS` names the shape and a unit test (`test_digest_has_one_shape_without_a_previous_derivation`) pins it on a fresh tree and after a second run.

The audit of every test under `checkers/tests/` that reads `D["digest"]`:

| test | how it gets its previous derivation |
|---|---|
| `test_revise_and_draft` | three plain runs on its own temporary tree; the second and third compare with the first's `derived.json`, written by the test |
| `test_digest_reports_node_and_root_flips` | the same pattern, twice |
| `test_digest_has_one_shape_without_a_previous_derivation` (new) | asserts the keys with no previous derivation, then runs again and asserts the same keys with one |
| `test_table_filed_on_the_fixture_passes` | the only one that read a file a prior run left behind (the `graph/derived.json` copied from the working tree, present locally, absent in CI); it now runs the plain run once on its unmodified copy before the edit, and asserts `compared_with` names that file |

`Fixtures.copy_fixture` now drops the two uncommitted generated files from every copy (`g.UNCOMMITTED`), so no fixture test can depend on a `derived.json` or `index.json` the working tree happened to hold. No test was loosened to tolerate a missing key. The CI run at `4dc8811` failed on no other test.

### 3. Part 2 — what a frame holds (G2)

The field, the rules and the renders are in §6. The three moves, mechanically:

- **Dockets dissolved.** The seven `docket-*` nodes (every node whose id begins `docket-`): each removed from its frame's `roots` and `children`, its children appended to the frame's `holds` in the docket's order, its file deleted (not superseded). 120 items held: `docket-deference` (38 under `deference-and-trust`), `docket-legitimacy` (22 under `legitimacy`), `docket-normative-inductor` (1 under `normative-inductor`), `docket-normativity` (36 under `normativity`), `docket-operative-force` (1 under `operative-force`), `docket-seed` (7 under `seed-theory`), `docket-workspace` (15 under `enabling-work`).
- **Round-filed formal results.** A shared-claim root of a frame at `4dc8811` that is a formal result (an `and` with a `record` child) and was a root of no frame at `4eb420f8`, the commit the round began from, moved from `roots` to `holds`. That is how the round's and the follow-up's filings were told from roots that predate the round: a formal result that was already a root somewhere on 2026-10-21 (the 72 landed results under `updateless-dt-programme`, `level-super-turing`, `legitimacy-weighted-deference` and the other pre-existing programmes, and the two claims F5 merged results into) stays a root. 177 results held, in 8 frames.
- **F4's line-level roots.** The 60 rows of the follow-up's moves table whose destination is `legitimacy` with the reason "bears on none of the three programmes" (the three sub-frames moved whole and the three wants are roots still: a frame and a want may not be held). Held by `legitimacy`.

What the rule left as roots: the item nodes that are shared-claim roots of a frame directly rather than through a docket (`item-75`, `item-91`, `item-108`, `item-109`, `item-110`; `item-75` is among the 60 F4 rows and is held), the two enabling-work claims the round filed (`enabling-map-as-canonical`, `enabling-program-site`), and every root that predates the round (§8).

A gestalt on a held node: 40 AI gestalt events (`@smithy-verity`) target nodes that are now held and roots nowhere (the F4 line-level claims). Rule 5 ("a gestalt targets a goal") would have refused the tree; a held node ranks under `--scope` naming it, where its gestalt is used, so rule 5 now admits a node a frame holds as a gestalt target. No event was written, withdrawn or moved.

### 4. Part 3 — bearing (G3) and the want weight (G4)

G3: the render line reads *Registered results bearing on this item:*; the index keys are `items[].bearing` and `formal_result.bears_on` (the second renamed with the first, since a result that bears on an item does not answer it); schema `graph-index/3` covers G2's `membership` and `holds` too. `item_status` is read from the item node and nothing in the checker or the render moves it (the fixture test asserts every item's status is the file's word).

G4: `priority_value` returns 0 for a want with `filed_from: quote` and no `priority` event by its owner, the word's weight once the owner writes one, and the Default `medium` for a want filed in a session; `none` still disowns. The view says *priority unset (owner has not confirmed: weight 0)*, the pooled list's note says the want weighs nothing until the word, and the per-owner line says so too. The self-test gained three facts: a quoted want with no word weighs `0/1`, with `low` `1/4`, a want its owner filed without a word `1/2`. The shipped graph: 13 wants are `filed_from: quote` without a word; their weight went from 1/2 to 0.

### 5. Part 4 — the recorded hash of `derived.json`

Cause, as far as this machine can tell. Two plain derivations of the same tree under Python 3.12.13 and Python 3.13.13 (the `uv` builds, this Mac) are byte-identical, and so are two under `PYTHONHASHSEED=1` and `=777`: the interpreter's version and the hash seed are not the cause. The derivation reads the disk in one place beyond the tree, the private-source flag (`source_private_only`, a path's existence), and the one node it applies to names a tracked path, so a checkout of the same commit cannot differ there. The derivation holds about 30,600 floats (per unit: bits, weighted bits, rate, the decision term, the per-goal shares; per goal: weight, entropy, promise; per node: weighted informs), each computed through the platform's math library (`log2`, `exp`, `pow`) and serialized at full `repr` precision; two math libraries that differ in the last bit of `log2` give two hashes of one derivation while every rendered number (three decimals) agrees, which is the symptom reported (the renders unchanged, the hash moved). That is the remaining variable, and it is the one the prompt's remedy addresses.

Fix: `derivation_hash` is taken over `canonical(D)`: keys as strings and sorted, Fractions exact as `p/q`, sets sorted, dates as ISO strings, every float at six significant digits (`HASH_FLOAT_DIGITS`), a signed zero as zero. The hash is a function of the derivation at that precision. A unit test perturbs every unit's bits, weighted bits and rate by one ulp and expects the same hash, and expects a different one for a changed status or a changed number. Not verified on the other machine: this follow-up had no second platform; if a plain run there still dirties `versions.json`, the diff of `derived.json` between the two machines names the field, and §10 reserves it.

### 6. Protocol and checker changes, with the design-log lines

| change | where | rule | design-log line |
|---|---|---|---|
| the digest has one shape (`DIGEST_KEYS`); `digest_line` reads `compared_with` | `checkers/graph.py` | — (a derived file's shape) | none: a derived-file shape, no protocol change; G1's text in `DECISIONS.md` |
| a frame's `holds`: attachment by membership; a held id must resolve; no node both held and a root of one frame, none held twice, no frame, valuation node or want held; a retired frame holds nothing | `checkers/graph.py` (lint), `PROTOCOL.md` §2 *What a frame holds*, §9 rules 1 and 2 | 1, 2 | ruling G2 |
| held nodes outside status, value, stake, goal set, margin, load and units; `--scope` naming a held node ranks it (kind `held`); a frame with `roots: []` and a non-empty `holds` is spelled, flagged *spelled; nothing yet a goal (N held)*, no spell-out candidate | `checkers/graph.py` (`goal_info`, `ranking`, `derive`), `PROTOCOL.md` §2, §8 | — | ruling G2 |
| `derived.json`: `held` per frame, `held_by` and the flag *held by* on the node, `frame.holds`, `subframe.holds`; the index: `in_frames[].membership`, `frame.holds`, schema `graph-index/3`; the view: *Held* under each frame, counts on the frame lines; tasks: the count on the goal tree | `checkers/graph.py`, `graph/MAP-AS-CANONICAL.md` §6, §6.1 | — | ruling G2 |
| a gestalt may target a node a frame holds | `checkers/graph.py`, `PROTOCOL.md` §9 rule 5 | 5 | ruling G2 (the first line) |
| the dockets retired: §5's item sentence, §8 *Item node, docket (retired)*, `MAP-AS-CANONICAL.md` §7 | `PROTOCOL.md`, `graph/MAP-AS-CANONICAL.md` | — | ruling G2, the three moves |
| *Registered results bearing on this item*; `items[].bearing`, `formal_result.bears_on` | `checkers/priorities_render.py`, `checkers/graph.py`, `PROTOCOL.md` §2, `MAP-AS-CANONICAL.md` §6.1 | — | ruling G3 |
| an unconfirmed quoted want weighs 0 | `checkers/graph.py` (`priority_value`, the notes and lines), `PROTOCOL.md` §2, §6, §8, `graph/README.md` | — (a Default) | ruling G4 |
| the derivation hash over `canonical(D)` | `checkers/graph.py` | — | Part 4 |

Self-test null inputs added (rule): a held id that resolves to nothing (1); a node both held and a root of one frame (2); a want in `holds` (2). Self-test facts added: the three want weights of G4. Unit tests added: `test_digest_has_one_shape_without_a_previous_derivation`, `test_held_nodes_are_attached_and_no_goals`, `test_unconfirmed_want_weighs_nothing`, `test_derivation_hash_is_canonical`; `test_index_schema_two_on_the_fixture` became `test_index_schema_three_on_the_fixture`; `test_hoist_rule_on_the_fixture` counts a `spell-out` line among the lines that rest on no AI number (an unspelled frame is read at a stand-in 1/2), because with the held results out of the goal set the spell-out of `normative-record` rose into the printed forty; `test_personal_weights` gives its quoted want the owner's word first (G4).

Documents touched beyond the protocol: `graph/README.md` (the frame paragraph, the want line), `AGENTS.md` (*Goals are frames and wants*), `graph/MAP-AS-CANONICAL.md` §1, §6, §6.1, §7, the Notes of the twelve frames whose roots moved (what each holds now and where the dockets went), `graph/DESIGN-LOG.md` (five new lines).

### 7. Deviations from this prompt, with reasons

- **`proposals_awaiting` is not emptied** when there is nothing to compare with. The ruling says the lists are empty in that case; this list is not a comparison (it names the proposals awaiting approval in the current derivation, and `tasks.md` prints the same list), so emptying it would make the digest say there are none when there are. The key is always present; the comparison lists and counts are empty and zero as ruled. Reversible in one line.
- **`formal_result.answers` renamed to `bears_on`** beside the ruled `answered_by` → `bearing`: the ruling's principle (a result bears on an item, it does not answer it) covers both ends of the join; leaving one as *answers* would have left the schema saying what the ruling retracts.
- **Rule 5 admits a held node as a gestalt target.** Not in the prompt; forced by the tree: 40 AI gestalts sit on claims that the third move holds and no frame roots. The alternatives were to write or withdraw events (forbidden) or to leave those claims as roots (against G2).
- **The schema is `graph-index/3` from the G2 commit**, not the G3 commit: G2 changes `in_frames` and the frame records, and a schema number names a shape; the G3 commit renames the keys inside the same number. §6.1 describes schema 3 as both.
- **The unit tests in the CI-shaped checkout** were run at the G1 commit, the G2 commit and the last commit, not before every commit: the checkout is a detached worktree of the commit under test, and the two commits between change documents and one function each; `tests/run.py` (which runs the same suite on the working tree, with `derived.json` present) ran before every commit.

### 8. Corrections to this prompt

- The prompt's "five things to fix" says CI raises `KeyError` in `test_table_filed_on_the_fixture_passes` "and possibly others": the run at `4dc8811` failed on that one test only (`Ran 142 tests`, `FAILED (errors=1)`).
- "A docket is an `or` with `either-suffices`": correct; seven dockets, not five (the follow-up added `docket-operative-force` and `docket-normative-inductor`).
- The want-weight function is `priority_value` (the prompt says "the want-weight function"); `PRIORITY_WORDS` is a dict constant and keeps its values, the Default moved in the function.
- "`in_frames` gains a `membership: holds` entry beside `role`": done so that every entry carries `membership` (`root` or `holds`); a held entry's `role` is null.
- The prompt names `previous_derivation`'s "callers": there is one, `committed_files`; the fix is in `digest` itself, which every caller gets.
- Part 4's premise, "varies across interpreters": not reproduced on this machine across 3.12 and 3.13 (§5); the hash was still made canonical as the part asks.

### 9. Test output

```
WORKFLOW SCOPE: clean over 4 workflow(s); 3 enumerated write-scope job(s)
DEAD POINTERS: clean over 58 live document(s) — 940 rooted path(s) resolve, 8 of them into declared trees and each saying so; 106 unrooted and 222 glob(s) not this gate's business; 14 historical span(s) and 5 ledger citation(s) exempt
UNTRACKED POINTERS: clean — 333 round-record path(s) and 998 resolving citation(s) are in the repository, not merely on this disk
WORKSPACE STATE: valid — 6 projects, 178 modern claims, 1 foundations, 180 foundation claims, 126 rounds, 52 terms, 137 priorities, 10 interface objects
WIKI REFS: clean over 34 page(s); 304 reference(s) resolve
PRIORITIES RENDER: the committed file equals the render (137 items)
OK 2408 nodes, 2411 events, 1886 ranked units; research first: the decision term (printed, not applied) favours vet hull-condition-total-trust (ranked unit 16), D 0.00016; nothing written (--dry-run)
Ran 146 tests in 109.309s
OK
GATE COVERAGE: 11 gate scripts, all invoked (5 self-test only — no local form)
LEAN SORRY GATE: clean over 108 files
LEAN AXIOM DISCIPLINE: every file carries `#print axioms`
PROJECTS:
  … 80 PASS lines, one per project runner, elided (the run on the Part 4 commit's tree; the report commit changes documents only and its run is green too)
LEAN BUILD SKIPPED: set WORKSPACE_LEAN=1 to run `lake build`
ALL GREEN (80 project(s))
```

The unit tests in the CI-shaped checkout (the last commit):

```
$ python3 -m unittest discover -s checkers/tests -t .   # in a detached checkout of eaee0762; no graph/derived.json, no branch derived
Ran 146 tests in 108.321s
OK
```

### 10. What this follow-up did not do, and the notes for the maintainers

Not done:

- The item nodes that are shared-claim roots directly (`item-91` under `deference-and-trust`; `item-108`, `item-109`, `item-110` under `authorship-and-transparency`) and the two enabling-work claims (`enabling-map-as-canonical`, `enabling-program-site`) stay roots: the ruling's three moves do not name them. They are goals of the ranking as the dockets were. *Turns on:* whether a single work order filed under the goal it serves is a route of that goal (a child) or a thing the frame holds — the same question G2 answered for the dockets, asked of five nodes.
- The 4 frames with `roots: []` and held nodes have no goal; the ranking values each programme as unspelled did (no option value). Naming their goals is a maintainer's spelling-out.
- Part 4 is not verified on a second platform.

Notes for the maintainers:

- **The branch's history holds seven versions of the derived files** (the prompt says five; `git log -- graph/derived.json graph/index.json` lists seven commits that changed them, from `0a73a063` to `a0ae3d07`, before `5b1e2bba` removed them): each a blob of 11–15 MB for `graph/derived.json` and 3–4 MB for `graph/index.json`. A squash merge of the pull request keeps none (the squashed tree has neither file), where the repository's convention is a merge commit, which keeps all seven in the history forever (pack loose objects 41.51 MiB, 10 packs 77.83 MiB at the Part 4 commit). *Turns on:* whether the maintainers trade the merge-commit convention for a small history once, or keep the convention and the copies, or rewrite the branch before merging (a force-push to the pull request, which nobody but the maintainers should do).
- **`stance-and-level` is a plan root only because the protocol makes every frame one.** The cruxes the second maintainer filed (the computability levels as three sub-frames and nine shared claims, the updateful-versus-updateless questions among them) are roots of a frame that is a plan root of `the-program`; a frame node is a root only as a plan (rule 2), so the group of cruxes enters the plan decision as a programme whose steps are the level frames, and is valued as one. The second maintainer may prefer his cruxes back as `shared-claim` roots of `the-program`, grouped by a field rather than a frame. Not changed here. *Turns on:* whether the frame tree is the only grouping the map offers (then a group of cruxes is a frame and a plan) or a field on a root may group roots without making the group a goal — a protocol choice the second maintainer's own filing should drive.

Reserved additions to `DECISIONS.md`, *Awaiting the author*: none new; the M1–M8 entry now carries G1–G4's confirmation.

## Provenance

Generator: Claude Fable 5.1 (Anthropic), executing the maintainer's prompt; review status `ci-only`. The scripts that produced the mechanical parts (the signature parser, the item transcription, the anchor writer, the survey counts) ran from the session's scratch directory and are not committed; `graph/SURVEY.md`'s appendix gives the one-liners that reproduce every count. Model attribution trailer on every commit.
