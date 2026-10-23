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

## Provenance

Generator: Claude Fable 5.1 (Anthropic), executing the maintainer's prompt; review status `ci-only`. The scripts that produced the mechanical parts (the signature parser, the item transcription, the anchor writer, the survey counts) ran from the session's scratch directory and are not committed; `graph/SURVEY.md`'s appendix gives the one-liners that reproduce every count. Model attribution trailer on every commit.
