# Prompt — the map as the canonical index of the program (2026-10-22)

You are working in the `alignment-workspace` repository, on `main` after the merge of
PR #129 (commit `4eb420f`). Do not stack this round on an unmerged branch; there is none.

This is a workspace round, not a research round: it produces no theorem and registers no
claim. Its artifacts live under `graph/` and in the specification-layer files it
restructures. The prompt goes verbatim in `prompts/2026-10-22-map-as-canonical/PROMPT.md`
and the report beside it. Check that no round directory with this date-slug exists before
creating it. New priority items, if the round files any within its scope, start at 129.

One pull request. Auto-merge OFF; the merge is the maintainers'. The first commit on the
branch is the proposal document of Part 8, so that it can be read on the pull request
before the restructuring commits land beneath it. Run `python3 -m checkers.graph --root .`
and `python3 tests/run.py` before every commit; a commit that leaves either failing is not
made.

## What this round is for

After this round, the structure under `graph/` faithfully represents the whole research
program — both maintainers' agendas as owned plans under the top frame, every registered
claim as a formal result, every priority item as a leaf, every maintainer decision reachable
from the nodes it touched, every narrative page attached to the frame it narrates, every
round pointed at from the nodes it produced — so that a website can be generated from that
structure alone. The website is not built here. The round's job is to make the map the one
index of the program and to turn the duplicate human-facing files into renders of it or
attachments to it.

Two principles govern every part.

**Structure and numbers are decoupled.** The frame tree, the `and`/`or` support, the records,
bridges, hypotheses, `cases` tables, wants and task leaves are the structure. The judgment
ladder, the probabilities, the utilities and the ranking are a lens on that structure. This
round changes structure and touches no number: it writes no `estimate`, `gestalt`, judgment,
acceptance or `priority`, and no event of any kind in a human's ledger.

**Where the protocol cannot represent something, file the gap; do not force the content.**
`graph/PROTOCOL.md` §2 lists the node kinds and §9 the refusals. A document, an item or a
ruling that has no honest place in that ontology is listed in the report under *What the
protocol could not represent*, with the smallest protocol extension that would hold it,
proposed as a `graph/proposals/P-<n>.md` where the mechanism fits and otherwise as a
reserved line. Routing around the protocol silently is the failure `AGENTS.md`
*Structural defects are reported* names.

Every path, field, kind, policy key and node id named in this prompt was read from `main`
at `4eb420f`. Confirm each exists before relying on it, and correct this prompt in the
report where it is wrong.

## Maintainer rulings

Record these as one dated `DECISIONS.md` entry as the round's second commit (after the
proposal document), marked as taken by one maintainer in conversation with the other's
confirmation outstanding.

**M1. Handles.** `graph/policy.yaml` maps the only human handle, `@maintainer`, to
`A-M-Berns`, and no handle exists for `abramdemski`, although `.github/CODEOWNERS` and
`tests/path_gate.py` name both as co-equal maintainers. The round renames `@maintainer` to
`@anson` (the ledger file, its event ids `maintainer-001`/`-002` → `anson-001`/`-002`, and
every reference, with the design-log line recording the rename) and adds `@abram` →
`abramdemski`, `kind: human`. The `maintainer:` key in `policy.yaml` is read by the checker
as a single handle: the round reports every place the checker or the protocol assumes one
maintainer and applies the co-maintainer reading where the change is contained (a list of
handles for that key is the expected form), reserving the rest.

**M2. One program, not two plans.** The top frame's question already encompasses the whole
program ("How does the relationship between humans and AI systems go, and what can we do
about it?") and stays as it is. Under it there is one plan, not two: the existing plan frame
`trust-modelling` is widened into the program itself — provisional id `the-program`, with a
question of the shape "which formal account of how humans and AI systems learn from, correct
and rely on each other guides AI safety engineering work" (the round words it from the wiki's
Home page and the existing node's Statement, and lists it as provisional). Its roots are the
lines, each a sub-frame:

- `normativity` — what learning from reasons requires: statics, traderization, seed theory,
  the normative inductor as the end-to-end object (seed → reasons → compile → enforce →
  revise). Owner `@anson`. Programmes drafted per M3.
- `legitimacy` — what must stay true of the process: integrity, openness, authorship;
  corrigibility hangs here as its consumer. Owners `@anson, @abram`.
- `deference-and-trust` — the trust half of today's `updateful-trust-li`: the LI deference
  collapse, bounded agents, the conjectures and inter-inductor trust. Owner `@abram`.
- `decision-theory` — the updateless programme and LI+BRIA (today's
  `updateless-dt-programme`, plus `projects/decision-theory/`). Owner `@abram`.
- `stance-and-level` — the cruxes every line reads: updateful versus updateless, the
  computability levels (`level-super-turing`, `level-above-quantifiable`, `level-poly-time`
  stay as they are beneath it), and `crux-unbounded-represents-phenomena` with the
  `*-guides-engineering` family. Owner `@abram`. These are cruxes about where to work, not
  lines of work, and the frame's Statement says so.
- `abstraction-arc` — as today. Owner `@abram`.
- `enabling-work` — as today, extended with the map and the site. Owners `@anson, @abram`.

`updateful-trust-li` is split: its deference roots go to `deference-and-trust`;
`legitimacy-reasons-programme` and `normativity-line` go under `normativity` and
`legitimacy` as their Statements direct; roots that belong to two lines
(`corrigibility-landscape`, `deference-toward-bounded-agents` and whatever else the round
finds) are filed once and listed as roots of each frame that reads them — the graph is a
DAG and a node may have several parents; the round does not duplicate a node to give each
line its own copy. The frame `updateful-trust-li` itself is retired (its id kept as a
deprecated alias in the report's old→new map, so that cited paths still resolve) unless the
round finds a residue that is neither trust nor normativity, in which case it says what.
Owner of `the-program`: `@anson, @abram`.

**M3. Normativity's programmes are drafted from the wiki.** The round drafts the
sub-frames of `normativity` from `wiki/Normativity.md`, `wiki/Normative-Inductor.md`,
`wiki/Seed-Theory.md`, `wiki/Theorem-Spine.md` and `wiki/Roadmap.md` (and `legitimacy`'s
from `wiki/Legitimacy.md`, `wiki/Integrity.md`, `wiki/Openness-Coverage-and-Non-Capture.md`,
`wiki/Corrigibility.md`), attaching the existing nodes and the formal results of Part 1
beneath them. Every root the round files this way is marked *owner has not confirmed* in
the view and listed in the report for a maintainer sitting.

**M4. The map is the foundational layer, and it is allowed to move.** The map's structure
is the load-bearing index of the specification layer: a priority item, a registered claim,
a decision and a narrative page each have exactly one node or one attachment in the map,
and the human-facing files that duplicate them become renders of the map or attachments to
it, per Parts 2–5. This is not a freeze of the protocol: where the program outgrows the
ontology, the protocol changes through its own mechanism (a proposal, a design-log line, a
Decided/Default register change) rather than the content being bent to fit, and the round's
report lists every place it had to choose between the two.

**M5. Frames may have several owners.** A frame's `owner` may be a list of human handles
(`owners`, or `owner` accepting a list — pick one form, document it in `PROTOCOL.md` §2 and
in refusal rule 2, and apply it). A want keeps exactly one owner, because its priority word
is one person's. The round reports every display and rule that read a frame's owner as a
single handle and what it did with each.

**M6. `PRIORITIES.md` becomes a generated render of item nodes**, like `graph/tasks.md`.
Item nodes are specification layer: `tests/path_gate.py`'s `SPEC_PATHS` and
`.github/CODEOWNERS` are extended to cover them (the two must agree). The maintainer's hand
ordering of items is carried over as transcribed data on each node, not as a priority word,
and the render preserves it.

**M7. `DECISIONS.md` stays the maintainers' prose record** and the highest-precedence source
(`README.md` *Precedence*). It is not migrated into events: an agent writes no `rule` event
and no line in a maintainer's ledger (`AGENTS.md`, *What an agent writes only from its
user's words*). Instead each entry gains a stable anchor and a machine-readable `touches`
line, and the map links to entries through a new `work` pointer kind `decision`. The round
adds the machine lines only; it does not reword a ruling.

**M8. The structure-only index is committed.** The checker emits the nodes, edges,
attachments, pointers and human events, without derived numbers, to `graph/index.json` on
the plain run, committed like `derived.json`, so a pull request's diff shows what a round
changed in the public picture. Its schema is the contract of Part 7.

## Part 0 — Survey

Write `graph/SURVEY.md` (provisional name). One table, one row per human-facing or
specification-layer surface: `README.md`, `RESEARCH_STATE.md`, `PRIORITIES.md` (the
numbered items and the *Where ingenuity is the bottleneck* section separately),
`DECISIONS.md` (*Awaiting the author* and *Settled* separately), `PROVENANCE.md`,
`CONTRIBUTING.md`, `AGENTS.md`, each `projects/*/CLAIMS.md`, each `projects/*/README.md`
and `notes/`, the consolidation and checkpoint trees listed in `SPEC_PATHS`,
`state/*.json` and `state/views/*`, every page under `wiki/`, every round under `prompts/`
and `projects/*/rounds/`, and `graph/` itself (frame, nodes by kind, events by handle,
`policy.yaml`). For each row: what objects it holds and how many; what ids they carry; which
other surfaces those ids join to and by what field; whether the surface is hand-written,
generated, or hand-written with bindings; and what in the map already represents it (node
ids or none).

Below the table, three lists.

*Inconsistencies found*, each with the two locations that disagree. Check at least: every
`<!--state:...-->` binding against `python3 -m checkers.workspace_state --json`; every
prose status claim in `README.md` and `wiki/Home.md` against the state (the README's line
that the Deference line is paused on two maintainer decisions is one to test against the
rounds of September and October); every registry `answers_item` against an existing item;
every `work: {kind: priorities}` ref against an existing item and every
`work: {kind: round}` ref against a round in the tree; every registry entry against a
`record` node and the reverse (there are 82 `record` leaves and the two registries hold
about 80 entries — report the symmetric difference by id); every wiki link against an
existing page or node.

*What is represented twice*, each with the surfaces that carry it.

*What the protocol cannot represent*, as described above.

Counts in this document are computed, not estimated, and the commands that produced them
are given.

## Part 1 — Formal results

Every registry entry in the `registries` list of `policy.yaml` has exactly one formal result
in the map: an `and` of its `record` leaf (whose `statement_of_record` is the registry's
declaration or checker invocation), one hypothesis leaf per hypothesis with its `discharge`
tag, one `bridge` with its `attribution`, and the completeness leaf (`PROTOCOL.md` §2,
*Formal results*). Reconcile the symmetric difference found in Part 0: file what is missing
at level 0 with `author` the round's AI handle, and for a record that names no live registry
entry, find the rename in the registry's old-id→new-id table and update the record rather
than deleting it. Where a formal result has no hypothesis leaves because the filing session
did not read the Lean, read the declaration's signature and file them, each tagged `open`
unless the signature or the registry note settles it; a `bridge` filed this way carries
`attribution: formalizer-stated`.

The 180 claims of `projects/normativity/consolidation-aug9/` are a foundation under its own
ledger and are deliberately not in the modern registry (`projects/normativity/CLAIMS.md`,
first section). Do not file 180 nodes. File the foundation as one node whose statement says
what the foundation is and whose `work` points at its ledger, attached under the normativity
plan of Part 6; list in the report how many of its claims are cited by name from nodes that
already exist, so a later round can decide which to lift.

## Part 2 — Items

One node per numbered item in `PRIORITIES.md`: a `task` leaf for a work order (the item has
a deliverable shape and an acceptance check) and a `question` leaf for an entry of the
*Where ingenuity is the bottleneck* section. The node's Statement is the item's problem
statement; its fields carry the item number, the difficulty tag, the `workspace-priority`
marker's values (`project`, `dispatchable`), the deliverable shape, the acceptance check, the
context paths, the item's open/closed status, and the item's position in the file as
transcribed data (field name provisional, e.g. `maintainer_order`). Where an item node
already exists (41 nodes carry `work: {kind: priorities}` today), merge into it rather than
filing a second; the `work` pointer is then redundant with the node's own number, and the
round decides whether the kind survives for pointers from *other* nodes to an item.

Attach each item node under the goal it serves, as a route or as evidence (`AGENTS.md`,
*What an agent does alone*: a task hangs under its goal as a route or as evidence, never as
a conjunct, unless the goal's Statement names the deliverable). An item whose goal the round
cannot identify is attached under the plan frame of its `project` and listed in the report
as *goal not identified*.

Then make `PRIORITIES.md` a render. The checker (or a new module under `checkers/` the plain
run invokes) writes it from the item nodes in the transcribed order, with the file's standing
preamble and the ingenuity section preserved as rendered sections, and `tests/run.py` gains a
gate that the committed file equals the render. Update `SPEC_PATHS` and `CODEOWNERS` together
so that item node files are specification layer. Demand-gating is unchanged: a contributor
still proposes items as issues, and a round files items only within its scope. This round's
scope is transcription; it files no new item except as its own report requires.


## Part 3 — Decisions

Give every entry under *Settled* in `DECISIONS.md` a stable anchor (an HTML comment or an
explicit heading id; pick one convention and state it in the proposal document) derived from
the entry's date and a slug of its title, and a one-line `touches:` list of the node ids,
item numbers and claim ids the ruling bears on, in a form the checker can parse. Do the same
for each entry under *Awaiting the author*, marked as open. The round adds these lines; it
changes no word of any ruling.

Add `decision` as a `work` pointer kind in `checkers/graph.py` (its ref the anchor), extend
refusal rule 2's kind list, and add the pointer to every node a ruling touches. Refuse an
anchor that resolves to no entry, and warn on an entry no node points at. Record each
checker change as a `graph/DESIGN-LOG.md` line.


## Part 4 — Narratives

The wiki stays where it is (`wiki/` is specification layer and the hosted wiki is
force-pushed from it). Attach it. Add a `narrative` field to frames and, where a page is
about one node, to that node (a protocol extension; document it in `PROTOCOL.md` §2 and in
the refusal table — a `narrative` path that does not exist is refused). Every frame has a
narrative or is listed in the report as lacking one; every wiki page is the narrative of
something or is listed as unattached (`ORIGIN.md`, `Sources.md`, `_Sidebar.md` and
`Prior-Art.md` may be legitimately unattached; say which and why).

Where a wiki page names a registered claim, an item or a round in prose, add the id in the
form the state-bindings checker (`checkers/wiki_state_bindings.py`) or a sibling checker can
resolve, so that a renamed claim or a closed item fails the build rather than going stale.
Fix every binding mismatch and every prose status claim Part 0 found, in `README.md` and
`wiki/Home.md` included, by binding the number or status to the state where a binding form
exists and by correcting the prose where it does not; list each correction in the report.

## Part 5 — Rounds

Every round in `state/rounds.json` is pointed at by `work: {kind: round}` from at least one
node: the formal results it registered, the items it filed or closed, the frame it served.
Today eight nodes carry such pointers and the state lists 125 rounds. Fill the gap from the
registries' `origin_round` fields, the rounds' reports, and the items' context paths. A round
no node can honestly point at (an administrative round, a scrub) is listed in the report,
not forced onto a node.

## Part 6 — The program and its lines

Apply M1, M2, M3 and M5, in that order: handles and the multi-owner rule first, because the
frames of M2 need both. Widen `trust-modelling` into `the-program`; file the seven line
frames with their owners; split `updateful-trust-li` and retire it; draft normativity's and
legitimacy's programmes from the wiki; attach every existing frame, formal result and item
under the line its Statement belongs to, filing shared roots once. Where an existing node's
placement is unclear, leave it where it is and list it in the report under *placement
unclear* rather than guessing. Wants for `@anson` may be filed only from his public words
with `filed_from: quote` (the published corrigibility post; wiki pages are a maintainer's
words — state in the report which source each want was drawn from); every one stays
*owner has not confirmed*, and no priority word is written on any of them. Report every
place the checker or protocol assumed one maintainer or one owner and what the round did
about it.

Hold the AI-drafted frames to the same standard as any filing: every root's Statement is in
research terms and cites only public sources.

## Part 7 — The structure-only index

Add to `checkers/graph.py` a structure-only emission: every node with its kind, fields,
Statement, Source, narrative, pointers and edges (parts, support, `given`, evidence,
refinement), every frame with its roots and owner, every human event in every ledger, and
no derived number, level, status or rank. Written on the plain run to the path M8 sets.
Document its schema in the proposal document; it is the contract a site generator will build
against, so every id in it is the id a URL will carry.

## Part 8 — The proposal document

`graph/MAP-AS-CANONICAL.md` (provisional name), the branch's first commit, revised as the
later parts teach. It states:

1. The ontology mapping — which existing object becomes which node kind, field or
   attachment (the table from Part 0 with the "becomes" column filled), and which files
   become renders.
2. The structure/numbers decoupling, and what the ranking is for once structure is canonical.
3. The governance of contribution: per-contributor ledgers owned by their handle through
   `CODEOWNERS` (one line per ledger), want nodes under a per-handle path the proof layer
   covers, and the checker as the only gate on either. State what this does and does not
   change about the two-layer trust model (`AGENTS.md`, *The two layers*): it creates no
   middle tier, because a contributor's own ledger is self-attribution checked for form, not
   trust.
4. The three contribution verbs as event schemas for a later round to implement, not this
   one: a *challenge* (against a record, a hypothesis or a bridge; a failure story with
   sources; becomes a proposed `cases` row or a proposed attack on the bridge), a *want*
   (already in the protocol), and a *bridge judgment* (a human says whether the formal
   statement means what the informal claim says, naming what they checked — the existing
   `attribution` event where it fits, a new kind where it does not).
5. The standing rules for a challenge, stated in the program's own vocabulary: a round that
   cites a challenge is a *response* and nothing more; *answered* is a checker act (a verified
   counterexample or a kernel-checked refutation landed) or a maintainer act; *disposed* is a
   maintainer act that names a successor; nothing else extinguishes a challenge.
6. What the website renders from the index of Part 7, as a list of page kinds keyed by id
   (frame, formal result with its bridge, item, decision, round, narrative) and three views
   (the frame tree, the support of one node, the feed of changes), with the rule that a page
   shows AI-drafted structure visibly lighter than anything a human event has touched.
7. Every choice this round made beyond its rulings, marked agent-decided and reversible, and
   the reserved list.

## Reserved to the maintainers

Append to *Awaiting the author* in `DECISIONS.md`, each with its *turns on* line: the
wording of `the-program`'s question and of every line frame's; the roots marked *owner has
not confirmed*; which of the foundation's 180 claims are lifted into the map; the priority
words on every want filed in Part 6; and anything a part above explicitly reserves. M1–M8
were taken by one maintainer in conversation; the entry landing them says so, and the
second maintainer's confirmation is listed as outstanding.

## The report

`prompts/2026-10-22-map-as-canonical/REPORT.md`. In order: the verification section first —
the `OK` line of the checker before and after, the `tests/run.py` output, the counts by node
kind and by pointer kind before and after, the render gate passing; then deviations from this
prompt with reasons; corrections to this prompt; *What the protocol could not represent*;
*goal not identified* items; unattached narratives and unpointed rounds; every protocol and
checker change with its design-log line and the refusal rule it added or changed; what this
round did not do (the site, the intake verbs, the lifting of foundation claims, the
reconciliation of numbers); and the reserved list. Model attribution trailer on every
commit per `AGENTS.md` *Provenance*.
