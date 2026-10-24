# Survey of the surfaces the map indexes

*Part 0 of the 2026-10-22 map-as-canonical round (provisional name). One row per
human-facing or specification-layer surface, as it stood on `main` at `4eb420f`
and as the round leaves it. Every count is computed; the commands are in the
appendix, and the "after" numbers are what those commands print on the round's
branch.*

## The table

| surface | holds (count) | ids | joins to | written | in the map at `4eb420f` | in the map after this round |
|---|---|---|---|---|---|---|
| `README.md` | prose: layout, precedence, status of the lines (120 lines) | none | names `AGENTS.md`, `RESEARCH_STATE.md`, `PRIORITIES.md`, `DECISIONS.md`, the lines by name | hand-written | none | none; its status prose corrected (below) |
| `RESEARCH_STATE.md` | prose: the one adjudicator command, the canonical checkpoint path (23 lines) | none | `python3 -m checkers.workspace_state --json`; `projects/normativity/legitimacy/checkpoint-2026-09-01/` | hand-written | none | none |
| `PRIORITIES.md`, numbered items | 125 work orders in 9 sections, each a `### n.` heading with a `workspace-priority` marker | item numbers 1–128 (three numbers unused) | registries' `answers_item`; nodes' `work: {kind: priorities}`; `DECISIONS.md` item mentions; wiki item mentions | hand-written | 41 pointers from 36 nodes to 36 distinct items; no node per item | one node per item (`item-<n>`, 125); the file is a render |
| `PRIORITIES.md`, *Where ingenuity is the bottleneck* | 4 entries (`Q1`–`Q4`), one section | `Q<n>` | `DECISIONS.md` (the Q3 queue entry) | hand-written | none | one `question` leaf per entry (`item-q<n>`) |
| `PRIORITIES.md`, *Workspace friction* | 8 entries (`F1`–`F8`) and item 28 | `F<n>` | `DECISIONS.md` (F6, F8 entries) | hand-written | none | one `task` leaf per entry (`item-f<n>`) |
| `DECISIONS.md`, *Awaiting the author* | 22 queued entries, bullets `- **Title.** … *Turns on:* …` | none | items by mention (6 entries), rounds by path | hand-written | none | each bullet carries an anchor `open--<slug>` and a `touches` list; 22 anchors, 6 with touches |
| `DECISIONS.md`, *Settled* | 260 dated entries (261 after this round's ruling) | none | items by mention (35 entries), registry ids by mention (7), node ids (0) | hand-written | 16 nodes cite the file in prose, none by anchor | every entry carries an anchor `<date>--<slug>` and `touches`; 49 entries touch a node, item or claim; 61 nodes point at 50 entries |
| `PROVENANCE.md` | 196 table rows over files and globs; 82 distinct round citations | file paths, round directories | `prompts/<round>/` | hand-written | none (provenance is not a map object) | none; the round adds its own rows |
| `CONTRIBUTING.md` | prose: the gates, the two layers, the claim classes (276 lines) | none | the gate commands, `AGENTS.md` | hand-written | none | none |
| `AGENTS.md` | the binding standards and the `graph/` section (1043 lines) | none | every gate, `graph/PROTOCOL.md` | hand-written | none | none; the `graph/` section gains the canonical-index rule |
| `projects/normativity/CLAIMS.md` | 73 entries (64 active, 9 superseded) in four sections | registry ids (`li.*`, `force.*`, …) | `answers_item` → items (16 distinct); `origin_round` → rounds (12); `statement_of_record` → Lean declarations; `superseded_by` → entries | hand-written, parsed by `checkers/registry.py` | 4 of the 82 record leaves name an entry of either registry | 73 formal results, ids the registry ids |
| `projects/deference/CLAIMS.md` | 105 entries (103 active, 2 superseded) | registry ids | `answers_item` → items (7 distinct); `origin_round` → rounds (8) | same | (as above) | 105 formal results |
| `projects/normativity/README.md`, `projects/deference/README.md`, `projects/decision-theory/README.md` | entry-point prose (19, 12, 39 lines) | none | `state/projects.json` entry points | hand-written | none | none |
| `projects/normativity/notes/` (5 files), `projects/deference/notes/` (10 files) | lab specifications and ledgers | none | cited by registries' `docs` and by nodes' Sources | hand-written | cited from node Sources | unchanged |
| the consolidated trees in `SPEC_PATHS` (11 trees: `consolidation-aug9` 69 files, the September checkpoint 13, the deck 3, four deference note dumps 42/228/14/13, the references tree 2, two clean rooms 3284/40, the decision-problems dump 2) | received or consolidated work, each with an `ORIGIN.md` | the foundation's 180 claim ids (`NL-…`), clean-room package names | `state/foundations.json`; node Sources (the clean room is the Source of most of the 82 landed records) | `agent-consolidated` | one node for the foundation (`normativity-aug9-foundation`); the clean room through 78 record leaves | the foundation node gains a `foundation` pointer; the clean-room records stay (§*What the protocol could not represent*) |
| `state/projects.json` (6), `state/rounds.json` (125), `state/foundations.json` (1), `state/vocabulary.json` (52 terms), `state/theorem_interface.json` (7 modules, 10 objects) | the structured state | project, round, foundation, term, interface ids | rounds → `prompts/` and `projects/*/rounds/` paths, claims, `depends_on`; foundations → the consolidation tree | hand-written JSON, validated | 8 nodes point at 8 rounds | 125 rounds: 119 pointed at by 194 nodes, 6 unpointed (listed in the report) |
| `state/views/*` (4 files) | generated renders of the state | — | — | generated (`--write-handoff`) | none | none |
| `wiki/` (34 files: 32 pages, `ORIGIN.md`, `CONVENTIONS.md`) | the human register, 6989 lines; 4 state bindings on 3 pages; 95 item mentions; registry ids and round ids in prose | page names | links between pages (checked), commit-pinned links into the repository (checked), bindings to the state (checked) | hand-written with bindings | none | 24 pages are the `narrative` of a frame or node; 304 `<!--ref:…-->` references resolve |
| rounds under `prompts/` (127 directories; 44 indexed with `prompts/` paths) and `projects/*/rounds/` (87 directories; 80 indexed rounds under `projects/`) | prompts, reports, artifacts | round ids (`YYYY-MM-DD-slug`) | `state/rounds.json`, registries' `origin_round`, `PROVENANCE.md` | hand-written, verbatim | 8 round pointers | 194 round pointers |
| `graph/frame.yaml` | the top question, 5 classes, 2 valuation nodes, 4 roots | root ids | nodes | hand-written | — | `owner` a handle, `narrative: wiki/Home.md`; the plan root is `the-program` |
| `graph/nodes/` | 1561 nodes: 125 `and`, 47 `cases`, 33 `frame`, 1291 `leaf`, 65 `or`; leaves: 32 assumption, 85 bridge, 125 completeness, 68 hypothesis, 47 partition, 202 picture, 188 question, 82 record, 123 route, 211 step, 116 task, 12 want | node ids | `work` pointers (41 priorities, 19 open, 8 round), `statement_of_record` → registries | AI-drafted, human-reviewed by events | — | 3059 nodes: 303 `and`, 47 `cases`, 46 `frame`, 2593 `leaf`, 70 `or`; leaves: 263 bridge, 303 completeness, 714 hypothesis, 260 record, 234 task; pointers: 42 priorities, 19 open, 194 round, decision on 61 nodes, 1 foundation |
| `graph/events/` | 2411 events: `@maintainer` 2, `@smithy-verity` 1396, `@smithy-verity-opus55` 1013 | event ids `<handle>-<n>` | node ids, row ids | written from users' words | — | the human ledger is `anson.jsonl` (`anson-001`, `-002`); no event added |
| `graph/policy.yaml` | parameters, 3 handles, 2 registries | handles | registries → `projects/*/CLAIMS.md` | hand-written | — | 4 handles (`@anson`, `@abram`, two AI); `maintainer` a list |

## Inconsistencies found

Each with the two locations that disagree.

1. **Handles.** `graph/policy.yaml` maps one human handle, `@maintainer`, to `A-M-Berns`; `.github/CODEOWNERS` and `tests/path_gate.py` name two co-equal maintainers. Every frame was owned by `@maintainer`, including the frames filed from the second maintainer's public notes (`projects/deference/note-dump-2026-08-11/README.md` attributes `notes/` to him). Resolved by ruling M1 and by re-owning frames and wants by line (report, *Part 6*).
2. **`README.md` versus the rounds.** `README.md` said the Deference line "is paused on two maintainer decisions" and that there are "two research lines"; `state/rounds.json` indexes 27 deference rounds from 2026-09-06 to 2026-10-01 and `state/projects.json` lists `decision-theory` active since the 2026-09-29 ruling. Corrected in `README.md`.
3. **`wiki/Home.md` versus `state/projects.json`.** Home says "two research lines and one bridge"; the state has three active top-level projects. One sentence added to Home.
4. **Wiki prose versus the registry's renames.** Six registry ids named on `wiki/Theorem-Spine.md` (5) and `wiki/Openness-Coverage-and-Non-Capture.md` (1) are superseded entries (`legitimacy.evolution-conservation` → `integrity.evolution-conservation`, `legitimacy.propagate-to-segment` → `integrity.propagate-to-segment`, `legitimacy.receipts-immutable` → `integrity.receipts-immutable`, `legitimacy.faithful-carry` → `integrity.faithful-carry`, `legitimacy.multiplicity-witness` → `integrity.multiplicity-witness`, `legitimacy.endpoint-only-insufficient` → `openness.endpoint-only-insufficient`). Found by `checkers/wiki_refs.py` once the references were declared; corrected to the current ids.
5. **Records versus registries.** 82 `record` leaves at `4eb420f`; 178 registry entries. Only 4 records name a registry entry (`li-deference-collapse-scoped.record` and three siblings); 78 name declarations of the clean room `projects/deference/faf-cleanroom-2026-10-02/`, which no registry lists, so they read *not in a claims registry* and cap at level 2; 174 entries had no record. The prompt's "about 80 entries" was 178. After the round: 260 records, 180 matching an entry, 80 clean-room records (78 landed plus the two new ones the round did not file, see the report), 0 entries without a formal result.
6. **`state/rounds.json` versus `prompts/`.** The index lists 125 rounds; `prompts/` holds 127 directories (the two extra are `README.md`'s directory and this round's, created on this branch) and `projects/*/rounds/` holds 87 directories against 80 indexed under `projects/` (the seven others are the legitimacy rounds indexed under `prompts/` paths). No dangling index entry; `--check` passes.
7. **`PRIORITIES.md` marker placement.** Items 1–73 carry the `workspace-priority` marker on the line after the heading; items 74–128 and `F7`–`F8` after a blank line. `checkers/workspace_state.py` reads both; the render normalizes to the first form (the only byte change the render makes to the file beyond none).
8. **`DECISIONS.md` ordering.** The *Settled* section runs newest-first from 2026-09-15 down to 2026-08-11 and then oldest-first from 2026-08-26 to 2026-10-23: two conventions in one file (the ledger's own rule, "a new entry goes beneath the last entry sharing its date", produces the second). Not changed; the anchors do not depend on order.
9. **`checkers/tests/test_graph.py` on macOS.** `test_scale` read `ru_maxrss` as kilobytes; macOS reports bytes, so the test failed on every Mac and never in CI. Fixed in the round's first commit.

Checks that found nothing: every `<!--state:…-->` binding matches the emission (3 bindings on 3 pages, plus one in `wiki/CONVENTIONS.md`'s grammar example, which the checker skips); every registry `answers_item` names an existing item; every `work: {kind: priorities}` ref names an item; every `work: {kind: round}` ref is a directory of the tree; every wiki link resolves and every repository link is commit-pinned (`checkers/wiki_links.py`).

## What is represented twice

- **A priority item**: `PRIORITIES.md` (the entry), the registry's `answers_item`, the nodes' `priorities` pointers, and now its item node. After the round the node is the source and the file is its render; the pointers and `answers_item` join by number.
- **A registered claim**: the registry entry, its Lean declaration, the wiki's prose statement (Theorem Spine and the component pages), and now its formal result in the map. The registry stays the statement of record; the map cites it by id.
- **A maintainer ruling**: `DECISIONS.md` (the entry), the round report that proposed it, the `PRIORITIES.md` annotation that records its effect on an item (`*narrowed 2026-10-21: …*`), and the wiki's "ruled (`DECISIONS.md`, 2026-09-08)" mentions. The entry is the record; the map points at it by anchor.
- **The status of a line**: `README.md`, `wiki/Home.md`, each line's wiki page (*Current status*), `RESEARCH_STATE.md` and the frames' Statements. The numbers are bound to the state; the prose is corrected where it disagreed.
- **A round**: its directory, `state/rounds.json`, `PROVENANCE.md`'s rows, the registry's `origin_round`, the wiki's pinned links, and now the `round` pointers. The index is the record; the map points at it by path.
- **The foundation's 180 claims**: `projects/normativity/consolidation-aug9/LEDGER.md` (the ledger), `state/foundations.json` (the count), the wiki's bound count, items 1–6 (which cite claims by id). One node stands for the foundation.
- **The maintainer set**: `.github/CODEOWNERS`, `tests/path_gate.py` (`MAINTAINERS`), `graph/policy.yaml` (`maintainer`, `handles`). Three lists that must agree; the round makes the third agree with the first two.

## What the protocol cannot represent

Listed with the smallest extension that would hold each; none is forced.

1. **A kernel-checked declaration outside every listed registry.** The 80 clean-room records (`projects/deference/faf-cleanroom-2026-10-02/packages/*`) are kernel-checked in a tree this repository's CI does not build and no registry lists, so they cap at level 2 with *not in a claims registry*. The protocol's anchor 4 reads only `registries`. Extension: a registry for the clean room, or a `registries` entry pointing at the clean room's own ledger with a class the protocol maps to *kernel-backed* (reserved; it is a maintainer decision which trees adjudicate).
2. **A work order's goal.** The protocol attaches a task under the goal it serves; 120 of the 137 items name no node-level goal the round could identify without judgment it was not dispatched to exercise. They hang as routes of a per-project docket (`or`) under the line's frame. Extension: none needed; the docket is a protocol-conformant placeholder and the report lists every item as *goal not identified*.
3. **A ruling's effect.** A ruling touches items, claims and nodes; the `touches` list records the explicit mentions only. A ruling that amends an earlier ruling is not linked to it (the ledger says so in prose). Extension: a `supersedes` field in the anchor line, when the maintainers want it.
4. **Two wiki pages for one node, or one page for several.** Represented: `narrative` accepts a list, and the index inverts it. Nothing lacking.
5. **A frame's owner confirming a drafted decomposition.** No event kind exists for "the owner read this frame and keeps it"; the round uses `filed_from: wiki` and its removal by the owner. Extension (reserved): a `confirm` event on a frame, if the maintainers prefer an event to an edit.
6. **The second maintainer's ledger.** `@abram` is mapped and has no ledger until he writes an event; `CODEOWNERS` gets his ledger line then. Nothing lacking.
7. **A round the map honestly cannot point at.** Six administrative rounds (scrubs, renames, cleanups) serve no node; the report lists them. The index carries every round with an empty `pointed_by`. Nothing lacking.
8. **The hand ordering of items as a lens.** `maintainer_order` is transcribed data, as ruled; the ranking does not read it. Whether it should is the one *Open* question the protocol kept about `PRIORITIES.md` and the task list, and it stays open.

## Appendix: the commands

The counts come from `python3 scratchpad/survey.py <root>` as run by the round (the script is reproduced in the report's provenance section) and from these one-liners, run on `main` at `4eb420f` for the "before" column and on the branch for the "after":

```
python3 -m checkers.graph --root .                       # OK <nodes> nodes, <events> events, <units> ranked units
grep -h '^kind:' graph/nodes/*.md | sort | uniq -c        # nodes by kind
grep -h '^leaf_kind:' graph/nodes/*.md | sort | uniq -c   # leaves by kind
grep -ho 'kind: [a-z]*, ref' graph/nodes/*.md | sort | uniq -c   # work pointers by kind
grep -c '' graph/events/*.jsonl                           # events by handle
grep -c '^### [0-9]*\.' PRIORITIES.md; grep -c '^### Q' PRIORITIES.md; grep -c '^### F' PRIORITIES.md
grep -c '^### 20' DECISIONS.md; grep -c '^- \*\*' <(sed -n '/## Awaiting the author/,/## Settled/p' DECISIONS.md)
python3 -m checkers.workspace_state --json | python3 -c 'import json,sys; d=json.load(sys.stdin); print(len(d["claims"]), len(d["rounds"]), len(d["priorities"]))'
python3 -m checkers.wiki_links; python3 -m checkers.wiki_state_bindings; python3 -m checkers.wiki_refs
ls wiki/*.md | wc -l; ls -d prompts/*/ | wc -l; ls -d projects/*/rounds/*/ projects/*/*/rounds/*/ | wc -l
```
