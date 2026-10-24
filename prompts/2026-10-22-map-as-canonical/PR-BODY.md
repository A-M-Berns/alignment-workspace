The body of pull request #131 as posted at the closing pass of 2026-10-24 (`prompts/2026-10-22-map-as-canonical/PROMPT-closing.md`). Links point at the branch `round/2026-10-22-map-as-canonical`; the report sections cited are in `prompts/2026-10-22-map-as-canonical/REPORT.md` (the round's sections §1–§10, then *Follow-up of 2026-10-23* §1–§10, then *Second follow-up of 2026-10-23* §1–§10).

---

## 1. What this pull request does

The map under `graph/` becomes the canonical index of the research program. Under the top question sits one plan, `the-program`, with seven lines, each a frame with its own owner and question. Every registered claim, every `PRIORITIES.md` item, every `DECISIONS.md` entry and every narrative wiki page has one node in the map or one attachment to it. `PRIORITIES.md` is a render of the item nodes, and `DECISIONS.md` entries carry machine-readable anchors. The two large generated files, `graph/derived.json` and `graph/index.json`, are not committed; CI publishes them to the branch `derived`.

## 2. Final state, with numbers

- Nodes: 2,408 (second follow-up, §1).
- Ranked units: 1,886, from 2,021 on `main` before the round and 4,685 at the round's first state (round report §1; second follow-up §1). The fall is the held results and work orders leaving the goal set, not a change to any number.
- Formal results: one per registry entry, 178 entries (105 deference, 73 normativity; round report §3), every registry-built record saying `hypotheses: unread` with the Lean signature verbatim in its Source (follow-up §1); the 68 hypothesis leaves that predate the round, filed by reading, remain (follow-up §1, the counts by node kind).
- Items: 137, each a node, `PRIORITIES.md` rendered from them (round report §1, the render gate).
- Decision anchors: 295, of which 244 no node points at (second follow-up §1); every anchor's pointers are in the index.
- Narratives: 24 wiki pages attached to frames and nodes; 10 pages are no node's narrative, six of them legitimately and four for a maintainer to place: `Roadmap.md`, `Theorem-Spine.md`, `Why-Normativity.md`, `Continuation-BRIA.md` (round report §6).
- Rounds: 119 of the 126 indexed rounds are pointed at from the map; the six unpointed are scrubs, renames and cleanups (round report §6) and the seventh is this round's own record.
- Held nodes: 361 in 12 frames (second follow-up §1 gives 357; the closing pass holds four more, below). Frames with no goal yet, `roots: []` with held nodes: `deference-finite-results`, `integrity-and-record`, `openness-and-non-capture`, `seed-theory` (second follow-up §1).
- Wants: 13, all filed from their owners' quoted words and all at weight 0 until an owner gives a priority word (second follow-up §4).

## 3. What changed across the three passes

**The round (2026-10-22; rulings M1–M8, `DECISIONS.md` anchor `2026-10-22--map-canonical-index-program-maintainer-handles`; report §1–§10).** The restructure: the handles `@anson` and `@abram`; `trust-modelling` widened into `the-program` with seven line frames; every registry entry a formal result; every item a node and `PRIORITIES.md` a render; decision anchors; `narrative` pointers to the wiki; round pointers; the structure-only index. Node count 1,561 → 3,059.

**The follow-up (2026-10-23; rulings F1–F6, anchor `2026-10-23--map-follow-up-hypotheses-unread-registry-edge-derived-files-one-decomposition`; report *Follow-up of 2026-10-23*).** Hypotheses are filed when read, not parsed: 646 parsed leaves removed, every registry-built record `hypotheses: unread`. The registry join is an edge (`registry_id`, a pointer from each result to the item its entry answers). The two derived files leave the tree for the branch `derived`. The two pre-existing frames `normativity-line` and `legitimacy-reasons-programme` are dissolved, each root moved by a stated reason (the moves table, Part 2). Of 244 formal results that hung on a frame alone, 2 were merged under the informal claims they establish; 54 ambiguous and 8 blocked are listed (Part 3). Node count 3,059 → 2,415.

**The second follow-up (2026-10-23; rulings G1–G4, anchor `2026-10-23--map-second-follow-up-digest-one-shape-frames-hold-bearing-unconfirmed-want-weighs-nothing`; report *Second follow-up of 2026-10-23*).** The digest has one shape (CI's one failure). A frame `holds` what it is about without making it a goal: the dockets dissolved and deleted, 177 round-filed results and 60 line-level legitimacy claims held. A registered result *bears on* an item and closes nothing. An unconfirmed want weighs nothing. The hash `versions.json` records is over a canonical serialization, floats at six significant digits; the first maintainer reports (in the closing prompt, not in a report section) that on 2026-10-23 a plain run on Linux with Python 3.13 left `versions.json` clean. Node count 2,415 → 2,408.

The closing pass (2026-10-24) holds the four item nodes that were still shared-claim roots directly, adds the principle G2 encodes to `graph/MAP-AS-CANONICAL.md` §2, and writes this body; it takes no ruling.

## 4. What needs the second maintainer

Each question can be answered by replying to this pull request, one number at a time. The answers are the next round's first commit.

**1. Confirm or strike the rulings M1–M8, F1–F6, G1–G4.** One dated `DECISIONS.md` entry by `@abram` closes the queue line `open--second-maintainer-confirmation-rulings-m1-m8`. *Turns on:* whether the co-maintainer accepts the program's shape as filed.

The ones that changed his filings:

- M1 — the handles: `@maintainer` → `@anson`; `@abram` added; `maintainer` in `graph/policy.yaml` a list.
- M2 — one program, not two plans: `trust-modelling` widened into `the-program`, owned by both, its roots the seven lines.
- M5 — a frame may have several owners.
- G4 — a want filed from quoted words weighs 0 until its owner gives a word.

The ones that are repository mechanics:

- M3 — normativity's and legitimacy's programmes drafted from the wiki, confirmed by removing `filed_from: wiki`.
- M4 — the map is the foundational layer and may move.
- M6 — `PRIORITIES.md` is a render of the item nodes.
- M7 — `DECISIONS.md` stays the prose record; each entry carries one anchor line.
- M8 — the structure-only index graph/index.json.
- F1 — hypotheses are filed when read; a record may say `hypotheses: unread`.
- F2 — the registry join is an edge (`registry_id`, a pointer to the item).
- F3 — the two derived files leave the tree for the branch `derived`.
- F4 — one decomposition per line: `normativity-line` and `legitimacy-reasons-programme` dissolved.
- F5 — a formal result sits under the claim it establishes (two merges).
- F6 — items docketed by programme (the dockets since dissolved by G2).
- G1 — the digest has one shape.
- G2 — a frame holds what it is about; its roots are its goals.
- G3 — a registered result bears on an item rather than answering it.

**2. The wording of `the-program`'s question and the seven lines' questions.** Provisional wordings, his to amend (queue line `open--wording-program-s-question-every-line-frame-s`). *Turns on:* whether each question is the one its owner asks.

- [`the-program`](https://github.com/A-M-Berns/alignment-workspace/blob/round/2026-10-22-map-as-canonical/graph/nodes/the-program.md): "Which formal account of how humans and AI systems learn from, correct and rely on each other guides AI safety engineering work?"
- [`normativity`](https://github.com/A-M-Berns/alignment-workspace/blob/round/2026-10-22-map-as-canonical/graph/nodes/normativity.md): "What does learning from reasons require of a reasoner: which statics a normative seed forces, how a constraint acquires operative force in a market, and what the Normative Inductor, from seed through reasons, compile, enforcement and revision, establishes end to end?"
- [`legitimacy`](https://github.com/A-M-Berns/alignment-workspace/blob/round/2026-10-22-map-as-canonical/graph/nodes/legitimacy.md): "What must stay true of a trajectory's record, verdicts and channels of influence, inside it and at its boundary, for a later judgment to count as the principal's own, and what does corrigibility consume from that?"
- [`deference-and-trust`](https://github.com/A-M-Berns/alignment-workspace/blob/round/2026-10-22-map-as-canonical/graph/nodes/deference-and-trust.md): "Which research on trust between a human inductor and an AI inductor, at the logical-induction level, reaches a formal account of trust that guides AI safety engineering work?"
- [`decision-theory`](https://github.com/A-M-Berns/alignment-workspace/blob/round/2026-10-22-map-as-canonical/graph/nodes/decision-theory.md): "Which decision theory for computationally uncertain agents, on the updateless side and in the synthesis of logical induction with bounded inductive rationality, is tractable, and which of its results bear on AI safety engineering?"
- [`stance-and-level`](https://github.com/A-M-Berns/alignment-workspace/blob/round/2026-10-22-map-as-canonical/graph/nodes/stance-and-level.md): "Where should the program work: at which level of computability, under which decision-theoretic stance, and does the computationally unbounded level represent the phenomena that matter?"
- [`abstraction-arc`](https://github.com/A-M-Berns/alignment-workspace/blob/round/2026-10-22-map-as-canonical/graph/nodes/abstraction-arc.md): "Which work on abstraction, logical induction and agency gives the program a representation theorem for logical inductors, a decision theory set in that representation, and a notion of scale-free agency that covers cooperative equilibria?"
- [`enabling-work`](https://github.com/A-M-Berns/alignment-workspace/blob/round/2026-10-22-map-as-canonical/graph/nodes/enabling-work.md): "Which repository infrastructure makes the trust research vettable and publishable?"

**3. His lines.** `deference-and-trust`, `decision-theory`, `stance-and-level`, `abstraction-arc` and `enabling-work` were filed and not reorganized (ruling F4 excludes them); `deference-and-trust` carries the trust half of the former `updateful-trust-li` with its roots unchanged (its Notes say so). Does he want them as they are, or a round that reorganizes them under his direction? *Turns on:* whether these lines' decompositions are his or placeholders.

**4. `stance-and-level`.** It is a plan root of `the-program` only because the protocol makes every frame a plan root; the alternative is his cruxes as `shared-claim` roots of `the-program`, grouped by a field rather than a frame (second follow-up §10). Which? *Turns on:* whether the frame tree is the map's only grouping or a field may group roots without making the group a goal.

**5. His legitimacy theory.** F4 found that the 60 line-level nodes of `legitimacy-reasons-programme` are the logical-induction-register theory (legitimacy as a correction to the trust principles) rather than the September theory the three programmes `integrity-and-record`, `openness-and-non-capture` and `authorship-and-transparency` carry; since G2 they are held by `legitimacy`, not goals (the moves table: follow-up report Part 2; the held list: `legitimacy`'s `holds`). A fourth programme under `legitimacy` (provisional name "legitimacy in the trust principles", owner `@abram`), left held, or placed otherwise? *Turns on:* whether that theory is a line of work in its own right or material the three programmes absorb.

**6. The 13 wants.** Each was re-owned by the attribution of its source document (round report §2, the deviation on re-owning; the queue line `open--priority-words-every-want` says five and eight, the tree today has four `@anson` and nine `@abram`). Which are his, and his word on each: `high`, `medium`, `low` or `none` (a `priority` event in his ledger, through his agent). *Turns on:* the owner's one word, which nobody else writes. Currently `@abram`:

- `want-basin-of-attraction-formalized`: Basin-of-attraction arguments for alignment, Christiano's basin of corrigibility among them, are formalized as well as can be done.
- `want-corrigibility-theorems-via-legitimacy`: The legitimacy notion of corrigibility is formalized and theorems state what it can and cannot accomplish.
- `want-figure-out-legitimacy`: The question of what legitimacy is, and how it enters the trust principles, is settled well enough for the rest of the roadmap to build on it.
- `want-intentional-stance-math`: A mathematical characterization states when it is rational to regard observed phenomena as agentic, obtained by combining a picture of agency with a picture of abstraction.
- `want-legitimacy-anti-meme-post`: The argument that unconditional Reflection is the wrong trust principle for an embedded agent, with legitimacy as its correction, is stated with mathematical precision.
- `want-legitimacy-corrigibility-theorems`: The legitimacy-based notion of corrigibility, under which an agent is corrigible where it sees human shutdown and modification decisions as legitimate, is formalized, with theorems proved about what it can and cannot accomplish.
- `want-legitimacy-meets-syntax`: Legitimacy is related to local rules of sanity, with inferentialist semantics connected to map-territory semantics.
- `want-methodology-note`: The case for and against working at the computationally unbounded level, as against tackling boundedness head-on, is stated with the approach each side suggests.
- `want-uea-review`: Cole Wyeth's revised Theorem 1 (rOSI) is assessed in a written account that places it against tiling, Vingean uncertainty and updatelessness and carries the finite-shadow results with their registers.

Currently `@anson` (listed so the attribution can be corrected either way):

- `want-address-anti-naturality`: The published arguments for the anti-naturality of corrigibility are gone through one by one and their hidden or under-scrutinized assumptions are addressed.
- `want-formal-model-of-dynamics`: A model exists in which the dynamic conditions for things turning out well, with corrigibility as a subgoal, are formally established.
- `want-sigma-algebra-changes`: The representation of corrigibility covers changes of the sigma-algebra, taken up after the absolutely continuous case has been studied thoroughly.
- `want-truth-through-literature-dialogue`: The corrigibility picture is developed in dialogue with the literature's positions toward the truest picture rather than a defended one.

**7. The clean-room records.** 78 kernel-checked declarations of `projects/deference/faf-cleanroom-2026-10-02/` are `record` leaves that no listed registry holds, so they cap at level 2 (round report §2; its §4 item 1 and the queue line `open--whether-clean-room-records-get-registry` say 80). Whether the clean room gets a registry is a trust-chain decision. *Turns on:* whether a tree this repository's CI does not build may adjudicate validity for the map.

**8. The top frame's owner.** `@anson` alone today; `the-program` is owned by both (queue line `open--top-frame-s-owner-sub-frames-owners`). Both at the top too? *Turns on:* whose question the top frame poses, a presentation input only.

### What needs the first maintainer

- Confirm or redraft the ten frames marked `filed_from: wiki`, by removing the field or rewriting the frame: `normativity`, `legitimacy`, `seed-theory`, `operative-force`, `normative-inductor`, `response-learning`, `normative-record`, `integrity-and-record`, `openness-and-non-capture`, `authorship-and-transparency` (queue line `open--roots-marked-owner-has-not-confirmed`; it says nine and lists ten).
- His priority word on each of his wants (the four listed under §4.6, and any of the nine that are his).
- The four unattached wiki pages: `Roadmap.md`, `Theorem-Spine.md`, `Why-Normativity.md`, `Continuation-BRIA.md` (round report §6).
- The four frames with no goal yet: `deference-finite-results`, `integrity-and-record`, `openness-and-non-capture`, `seed-theory` (second follow-up §1 and §10).
- The 54 ambiguous and 8 blocked merges of F5 (follow-up report Part 3; queue line `open--ambiguous-blocked-merges-ruling-f5`).

## 5. How to merge

A squash merge is recommended, against the repository's merge-commit convention, for one reason: seven commits on the branch carry versions of `graph/derived.json` (11–15 MB each) and `graph/index.json` (3–4 MB each); a merge commit keeps all seven in the history forever, and a squash keeps none (second follow-up §10, with the pack sizes: 10 packs at 77.83 MiB, loose objects 41.51 MiB at the Part 4 commit). The round's prompts and reports under `prompts/2026-10-22-map-as-canonical/` and the three `DECISIONS.md` entries preserve the pass-by-pass history that the squash removes from `git log`.

The rulings are in force as one maintainer's with the other's confirmation queued, which is the state the regulations designed for a ruling taken in conversation, so the merge does not wait on §4. The answers to §4 are the next round's first commit.

If squash-merged, carry the *Model attribution* section below into the squashed commit message.

## 6. After the merge

The `derived` workflow runs for the first time on `main`: check that the branch `derived` appears with both files and that its one commit's message names the `main` commit it derives from (`derived: the plain derivation of main at <sha>`), since the workflow has never executed. Then the next round is the vertical slice: five reference claims connected by reading, and a site prototype walking one question through them. Not another structural pass.

---

## Layer touched

- [ ] **Proof layer only** — required for non-maintainer pull requests
- [x] Specification layer (maintainers only; `path-gate` fails otherwise)

## Claim class

none

## Ships a contrib checker

- [ ] This PR adds a checker under `checkers/contrib/`

## Statement of record

none

## PRIORITIES item answered

none — a workspace round; it files no item and registers no claim. `PRIORITIES.md` is a render of the item nodes (ruling M6).

## What this addresses

The map as the canonical index of the program (§1 above); `graph/MAP-AS-CANONICAL.md` is the proposal document.

## What covers it

- `python3 tests/run.py` — `ALL GREEN (80 project(s))` at every commit.
- `python3 -m checkers.graph --root .` — `OK 2408 nodes, 2411 events, 1886 ranked units`, one `WARN` (the summary of decision anchors no node points at); `--self-test` passes.
- `python3 -m unittest discover -s checkers/tests -t .` in a CI-shaped checkout (no `graph/derived.json`, no branch `derived`) — green at the last code commit.

- [x] `python3 tests/run.py` green locally
- [x] Lean builds and audits clean (or: this PR touches no Lean)
- [ ] `python3 -m checkers.run` green, if this PR touches a claims registry — not touched
- [x] Exact arithmetic throughout, or floats confined to marked exploration code
- [x] Necessity witnesses for each hypothesis, or a statement of why not feasible — not applicable, no theorem

## New names introduced

All provisional: the frame ids (`the-program` and the seven lines, the programmes drafted from the wiki), the item node scheme `item-<n>`, the field `holds`, the index schema `graph-index/3`, the branch `derived`.

## Provenance entries added or updated

`PROVENANCE.md`: the file-table row for `prompts/2026-10-22-map-as-canonical/` (extended at each follow-up) and three attribution rows; the round's record in `state/rounds.json`.

## Documentation surfaces

- [x] Verification register (exact statements, hypotheses, how to re-verify) — each report section's §1 and `graph/SURVEY.md`
- [ ] Interpretation or philosophical gloss proposed in the PR description for maintainer consideration
- [ ] Not applicable — this PR adds no results

## Anything the author must decide

§4 above.

## Developer Certificate of Origin

- [x] Every commit is signed off (`Signed-off-by: A. M. Berns <ansonberns@gmail.com>`)

## Model attribution

- [x] **Dispatched round** — **Prompt-author-model:** the maintainer, relayed verbatim; **Model:** Claude Fable 5.1 (Anthropic)

Model: Claude Fable 5.1 (Anthropic)

## Consolidated trees

- [x] This PR does not modify a tree marked `agent-consolidated`
