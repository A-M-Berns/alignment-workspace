# The map as the canonical index of the program

*Proposal document of the 2026-10-22 map-as-canonical round (provisional name;
`prompts/2026-10-22-map-as-canonical/`). It states what the round turns the map
into, what it leaves alone, and what it reserves. Every choice marked
**agent-decided** is reversible by a maintainer ruling; the reserved list is at
the end and in `DECISIONS.md`, *Awaiting the author*.*

The map under `graph/` is the one index of the research program: both
maintainers' agendas as owned plans under the top frame, every registered claim
as a formal result, every priority item as a leaf, every maintainer decision
reachable from the nodes it touched, every narrative page attached to the frame
it narrates, every round pointed at from the nodes it produced. The
human-facing files that duplicated those objects become renders of the map or
attachments to it. A website can be generated from the structure alone; it is
not built here.

Two principles govern every part. **Structure and numbers are decoupled**: the
frame tree, the `and`/`or` support, the records, bridges, hypotheses, `cases`
tables, wants and task leaves are the structure; the judgment ladder, the
probabilities, the utilities and the ranking are a lens on it. This round
changes structure and touches no number. **Where the protocol cannot represent
something, the gap is filed**, as a proposal or a reserved line, and the
content is not bent to fit.

## 1. The ontology mapping

| surface | holds | becomes |
|---|---|---|
| `graph/frame.yaml` | the top question, its owner, classes, valuations, four roots | unchanged in question and classes; `owner` may be a list; gains `narrative: wiki/Home.md`; the plan root `trust-modelling` is widened into `the-program` |
| `graph/nodes/<id>.md` | one node per claim, frame, table, leaf | unchanged in kind; frames gain `narrative` and may have several owners; a node may be a root of several frames (shared roots); since the second follow-up of 2026-10-23 (ruling G2) a frame may `hold` nodes it is about without making them goals |
| `graph/events/<handle>.jsonl` | one ledger per contributor | the only human ledger is renamed from `maintainer` to `anson` (ids `anson-001`, `-002`); a second human handle `@abram` is mapped and has no ledger until it writes an event |
| `graph/policy.yaml` | parameters, handles, registries | `maintainer` is a list of human handles; `handles` maps `@anson` and `@abram` |
| `projects/*/CLAIMS.md` (two registries, 178 entries) | registered claims with a statement of record | each entry has exactly one formal result in the map: an `and` whose id is the registry id, of a `record` leaf (statement of record = the declaration), one hypothesis leaf per hypothesis read from the Lean signature, one `bridge` with `attribution`, one completeness leaf; the registry stays the statement of record and the map cites it |
| the 82 landed `record` leaves whose declarations are not registry entries | clean-room and package declarations | kept as they are (they cap at level 2, *not in a claims registry*); the gap is filed in §7 |
| `PRIORITIES.md`, numbered items | work orders (125, plus 4 ingenuity entries and 8 friction entries) | one node per entry, id `item-<n>` (`item-q<n>` for *Where ingenuity is the bottleneck*, `item-f<n>` for *Workspace friction*), a `task` leaf for a work order and a `question` leaf for an ingenuity entry, or the node that already stood for the item (17 merged, renamed into the scheme); the item's fields (number, title, difficulty tag, heading annotations, project, dispatchable, deliverable shape, acceptance check, context paths, open/closed status, position, section) on the node; the item's body verbatim in a `## Item` section of the node file |
| `PRIORITIES.md`, the file | the maintainers' ordered list | **a render** of the item nodes in the transcribed order, written by `checkers/priorities_render.py` on the plain checker run from `state/priorities_sections.md` (the standing preamble and each section's intro) and the item nodes; `tests/run.py` gates that the committed file equals the render |
| `DECISIONS.md` | the maintainers' prose rulings (261 settled, 22 queued before this round's additions) | stays the highest-precedence prose record; each entry gains one machine line (an anchor and a `touches` list: 283 anchors, 49 with touches read from the entries' explicit mentions); 61 nodes point at 50 entries through the `work` pointer kind `decision`; no ruling is reworded and no event is written |
| `wiki/*.md` | narrative pages (32 pages, 2 repo-only files) | 24 pages attached to frames and nodes through the `narrative` field (a page or a list of pages); 304 claims, items and rounds named in prose carry a resolvable reference (`checkers/wiki_refs.py`), which found six superseded ids to correct |
| `state/rounds.json` (125 rounds, 126 with this one) | the round index | 119 rounds pointed at by `work: {kind: round}` from 194 nodes (the formal results by `origin_round`, the line and programme frames by project, the enabling work by the infrastructure rounds); 6 administrative rounds unpointed, listed in the report |
| `state/foundations.json` | the August 9 foundation | one node (`normativity-aug9-foundation`) whose `work` pointer of kind `foundation` names the foundation's id; its 180 claims are not filed |
| `README.md`, `wiki/Home.md` | prose status claims | bound to the state where a binding form exists, corrected where it does not |
| graph/index.json | — | **new, generated**: the structure-only emission the checker writes on the plain run (§6); not committed since the follow-up of 2026-10-23 (ruling F3), published to the branch `derived` |
| `graph/SURVEY.md`, this document | — | new hand-written documents under `graph/` |

The worked example of how a registered result is connected to the informal claim it
establishes, by reading (the claim as the `and` of its formal results and its own
completeness leaf; hypotheses filed as leaves with their discharge tags; the bridge
rewritten to name the gap; the improvement claim's routes as what remains) is
`projects/enabling/rounds/2026-10-24-site-vertical-slice/CONNECTIONS.md`, five connections
including the multi-record one.

What stays hand-written and specification layer: `AGENTS.md`, `CONTRIBUTING.md`,
`README.md`, `RESEARCH_STATE.md`, `PROVENANCE.md`, `DECISIONS.md`, the registries,
the wiki, `graph/PROTOCOL.md`, `graph/README.md`, `graph/frame.yaml`,
`graph/policy.yaml`, and now `state/priorities_sections.md` and the item nodes
`graph/nodes/item-*.md` (`tests/path_gate.py` and `.github/CODEOWNERS` both list them).

## 2. Structure and numbers

The structure is what this round files; it is what a site renders, what a
pointer resolves against, and what the registries, the item list and the ledger
join to. The numbers (levels, judgments, probabilities, values, the ranking)
are derived from the ledgers by the checker and are a lens on the structure:
they say how far each piece has been checked and what to read next. Once the
structure is canonical the ranking's job is unchanged and narrower: it orders
the vetting and research of a map that is now complete as an index, so a unit's
path runs through the program's real lines and a goal's stake reads from the
agenda both maintainers own. Nothing in this round writes an `estimate`,
`gestalt`, judgment, acceptance or `priority`, and the lens is not recomputed
by hand anywhere.

The map is a representation of the research program, only part of which is an
argument (ruling G2 of the second follow-up, 2026-10-23; `DECISIONS.md` anchor
`2026-10-23--map-second-follow-up-digest-one-shape-frames-hold-bearing-unconfirmed-want-weighs-nothing`).
A frame's roots are its goals and enter the ranking; what a frame holds is what
it is about and does not. Three readings run over the one structure and do not
share inference semantics: the argument view (support, formal results,
conditions, objections), where a node's probability and status are derived from
what it rests on; the research map (lines, programmes, their questions, and what
each holds), where a programme's registered results and work orders sit under it
without being its goals; and the contribution view (work orders, challenges,
wants), where an item is a thing to do and a want its owner's word, neither a
claim the ranking forecasts. A number computed in one reading is not a number in
another: a held result's level says how far it has been checked, not how likely
its programme is to succeed, and a work order's presence under a frame says
nothing about any status.

## 3. Governance of contribution

- **Per-contributor ledgers, owned by their handle.** `graph/events/<handle>.jsonl`
  is written only from that person's words; `.github/CODEOWNERS` carries one
  line per human ledger, naming the handle's GitHub account, so a pull request
  touching a ledger is reviewed by its owner. (This round adds the line for
  `anson`; a line for `abram` is added with the first event in that ledger.)
- **Wants under a per-handle path the proof layer covers.** A want node is
  `graph/nodes/want-<slug>.md` with its `owner`; it is proof layer, as every
  node is, and the only facts about it a checker enforces are form: the owner
  is a mapped human, the id begins `want-`, it is a root of exactly one frame,
  and only the owner writes its `priority`.
- **The checker is the only gate on either.** Rule 5 refuses an event in the
  wrong ledger, an id without the ledger's prefix, a priority by anyone but the
  owner; nothing else adjudicates a ledger line.

What this does and does not change about the two-layer trust model
(`AGENTS.md`, *The two layers*): it creates no middle tier. A contributor's own
ledger is self-attribution checked for form, not trust: the events in it mint
levels on nodes only as the protocol's anchors say (a level of 10 and above
needs a second human), they are public under the handle, and nothing a
verdict depends on reads them. The specification layer stays maintainer-owned;
the item nodes join it because `PRIORITIES.md` is now their render.

## 4. The three contribution verbs (event schemas for a later round)

Not implemented here; stated so that a later round builds them against one
design.

- **challenge** — against a `record`, a `hypothesis` or a `bridge`: a failure
  story with sources. Event fields: `kind: challenge`, `target: {node}`,
  `story` (the failure in the challenger's words), `sources` (public
  citations), `proposes: {row: <picture id>}` or `proposes: {attack: bridge}`.
  It becomes a proposed `cases` row under the target (the agent drafts the
  picture leaf and the partition bump) or a proposed attack on the bridge (a
  row under the bridge once it is a table). A challenge is an event in the
  challenger's ledger; the row it proposes is a draft until admitted.
- **want** — already in the protocol (`want: true`, `owner`, `filed_from`,
  the `priority` event).
- **bridge judgment** — a human says whether the formal statement means what
  the informal claim says, naming what they checked. Where the human is not the
  node's author this is the existing `attribution` event (`verdict: vouched |
  disputed`, `ref`). Where the author judges their own bridge, or the judgment
  is on a hypothesis's `discharge` tag rather than the attribution, a new kind
  `bridge-judgment` with `verdict: holds | fails`, `checked` (said items) and
  `ref`, minting no level, is the proposal; it clears no flag and is shown
  beside the bridge.

## 5. Standing rules for a challenge

In the program's own vocabulary: a round that cites a challenge is a *response*
and nothing more; it answers nothing by citing. A challenge is *answered* by a
checker act (a verified counterexample landed, or a kernel-checked refutation
registered, either of which the checker can see) or by a maintainer act (a
`rule` event naming the challenge). A challenge is *disposed* by a maintainer
act that names a successor (the challenge is carried to another node, the way
a disposal carries an obligation to a successor under the Defeat Principle).
Nothing else extinguishes a challenge: not a new version of the target, not a
response round, not the passage of time.

## 6. What the website renders from the index

graph/index.json (schema in §6.1) is the contract, and since the site-vertical-slice round
(2026-10-24; rulings S2–S4) the site exists: `site/build.py`, standard library only, reads
the index, `graph/derived.json` for the ranking page alone, the state files, the
registries, the decision anchors, the wiki source, the policy and the human ledgers, and
writes `_site/`. One id, one URL: `/n/<node id>/`, `/items/<n>/`, `/decisions/<anchor>/`,
`/rounds/<round id>/`, `/claims/<registry id>/` (a redirect to the node the record belongs
to), `/wiki/<Page>/`, `/by/<handle>/`; two ids that map to one path fail
the build, as does any reference that does not resolve (`site/README.md`). Pages, as built:

- **front page**: the map, filling the viewport (ruling S5, 2026-10-30): one pannable,
  zoomable network graph — the concept network of `state/concepts.json`, whose members
  are goals and threads, new constructions, mathematical objects, prior work and
  philosophical concepts, the repository wiki's terms among them and beyond them — small
  jewel-toned nodes colour-coded by kind, force-laid, every link hand-chosen with its
  relation categories and a one-line why on edge hover, every node a popup ending in its
  tagged merged work from `state/prs.json`; the question and lede in an about panel over
  the canvas, the feed's head collapsed below.
- **frame** (`/n/<frame>/`): question, owners, the narrative rendered, roots by role, what it
  holds by kind (formal results, items, other), sub-frames, the path up to the top frame,
  *no goal yet* where `roots` is empty.
- **node** (`/n/<id>/`): Statement, Source, Notes, kind, author and the human events on it,
  edges above and below (part, given, root-of, held-by), work pointers resolved, the frames
  it is in; for a formal result the **bridge card**: the informal claim it is a conjunct of,
  the declaration with its Lean file at the commit, the bridge's Statement and attribution,
  the hypotheses with their tags or *unread*, the registry class and review status, and the
  improvement claim's routes as *what remains*; a collapsed *ranking* section.
- **item**, **decision**, **round**, **wiki** (references resolved to links carrying the
  target's live class or status; the page's and its sources' last-changed dates), **handle**
  (frames owned, wants with their priority state, events), the **feed**, the **theorem
  spine** (connected formal results by the part edges between their claims, class-coloured;
  held-only results listed as unconnected), the **ranking** page (the content of
  `graph/tasks.md` with the digest, labelled as the lens it is), and **search** (a
  client-side index over ids, Statements, titles and registry short names).
The rule for every page holds as built: an AI-drafted node (an AI author, no human event on
it) renders in a lighter register with the label *drafted*, and the ranking's numbers appear
nowhere but the ranking page and the collapsed section. The intake verbs on every node page
— comment, challenge, estimate, want — are prefilled GitHub issues carrying the node id and
a protocol-shaped body; the site accepts no write, and a maintainer round sweeps what lands
into ledger events. The map is the site's one tab; the planned additions are a chat tab
(a bring-your-own-key bot over the map and the record), a stats/status page (a time
graph with an activity digest), and a comment system based on the map — comments keyed
by concept id, collected through the prefilled-issue verbs the concept cards and full
views already carry, rendered from a `state/comments.json` a maintainer round curates —
and nothing else. Not yet built: those two tabs, in-page
filing without the GitHub detour, and pages for the held results beyond what the bridge
card shows them as.

### 6.1 Schema of graph/index.json

Written on the plain run beside the other generated files, hashed like them
(`generated_hash`), identical whatever flags the run was given, with no derived
number, level, status or rank. Since the follow-up of 2026-10-23 (ruling F3) it
is not committed: `.gitignore` excludes it, CI keeps it as an artifact of every
run and publishes `main`'s to the branch `derived` beside `derived.json`, and
`graph/versions.json` records its derivation hash. A site generator reads the
branch.

```
{
  "schema": "graph-index/3",
  "generated": "<ISO date>",
  "generated_hash": "<sha over the rest>",
  "frame": {"question", "owners": [handles], "narrative", "classes": [ids],
            "valuations": [ids], "outside_option", "undescribed_failure",
            "roots": [{"id", "role"}], "holds": [ids]},
  "handles": {"@h": {"kind": "human" | "ai", "github" | "model"}},
  "nodes": {"<id>": {
      "kind", "leaf_kind", "author", "size", "version",
      "statement", "source", "notes", "narrative",
      "children": [ids], "rows": [{"picture", "class", "given", "residual"}],
      "given", "work": [{"kind", "ref"}],
      "fields": {every other frontmatter key as written},
      "frame": {"question", "owners", "roots": [{"id", "role"}], "holds": [ids]}   // frames only
      "in_frames": [{"frame", "role", "membership": "root" | "holds"}],          // schema 3: held nodes have no role
      "hypotheses": [ids] | "unread", "registry_id"                // record leaves only (schema 2)
      "formal_result": {"record", "hypotheses": [ids] | "unread",  // an and with a record child (schema 2)
                        "registry_id", "bears_on": [item numbers]}      // schema 3: bears_on (was answers)
  }},
  "items": {"<item>": {"node": "<node id>", "bearing": [formal-result node ids]}},   // schema 3: bearing (was answered_by)
  "claims": {"<registry id>": "<node id of its formal result>"},                          // schema 2
  "decisions": [{"anchor", "date", "title", "status", "touches": [{"kind", "ref"}],
                 "pointed_by": [node ids]}],
  "rounds": [{"id", "path", "pointed_by": [node ids]}],
  "narratives": {"wiki/<Page>.md": [node ids, or "top"]},
  "events": [every event line of every human ledger, as written]
}
```

Every id is the id a URL carries: node ids, registry ids (formal results),
`item-<n>`, decision anchors, round ids and wiki paths.

Schema 2 (the follow-up of 2026-10-23, rulings F1 and F2) adds the registry
join as data: a record leaf's `hypotheses` (a list of hypothesis-leaf ids, or
`"unread"` where no one has filed them by reading) and `registry_id`; on the
`and` of every formal result a `formal_result` block with the record, the
hypotheses, the registry id and the items it answers; `items` as records with
`answered_by`; and `claims`, which resolves a registry id to its node whatever
the node's id is (a result merged under the claim it establishes keeps its
registry id here).

Schema 3 (the second follow-up of 2026-10-23, ruling G2) adds what a frame
holds: `holds` on the top frame and on every frame record, and `in_frames`
entries that carry `membership` (`root` with the role, or `holds` with no
role), so a site lists a programme's registered results and work orders
under it without reading them as its goals. Ruling G3 (the same follow-up)
renames `items[].answered_by` to `bearing` and `formal_result.answers` to
`bears_on`: a registered result bears on an item and closes nothing; an item's
`item_status` is the maintainer's word in the item node, which no result moves.

## 7. Choices beyond the rulings, and the reserved list

Each **agent-decided** choice is reversible; the rejected alternative is named.

- **Formal-result ids are the registry ids.** `inductor.conformance` is the
  `and`; its leaves are `inductor.conformance.record`, `.bridge`, `.complete`,
  `.setting` and `.h<k>`. *Rejected:* a prefixed id (`claim-…`), which would
  make the registry join a translation rather than an identity.
- **Hypothesis leaves are read from the Lean signature by script.** One
  `.setting` leaf (`discharge: definitional`) for the declaration's data binders
  and one leaf per explicit proposition binder, tagged `open` unless the registry
  note settles it; the bridge carries `attribution: formalizer-stated` and its
  Statement is the registry's own reading. *Rejected:* filing the 174 results
  without hypotheses, which the protocol's *Formal results* paragraph does not
  allow.
- **Item node ids are `item-<n>`**, the 36 existing nodes that stood for one
  item each being renamed into the scheme, so that one glob covers the item
  files in the path gate. *Rejected:* keeping the descriptive ids and listing
  36 paths in `tests/path_gate.py`.
- **An item's body is kept verbatim** in a `## Item` section of its node, and
  the render regenerates the heading and the metadata line from the fields.
  *Rejected:* re-typing the bodies as Statements, which would reword the
  maintainers' work orders.
- **Items hang in per-project dockets** (`docket-normativity`, `-legitimacy`,
  `-seed`, `-deference`, `-workspace`: one `or` of routes per project of the
  `workspace-priority` marker, a shared-claim root of the line's frame) where no
  finer goal was identified; the 17 items whose nodes already stood somewhere
  keep their place; the report lists the 120 docketed items as *goal not
  identified*. *Rejected:* conjunct attachment, which the protocol forbids for
  tasks, and placement by section heading, which puts seed items under the
  deference line because the file's late sections do not follow projects.
  *Dissolved* by ruling G2 of the second follow-up (2026-10-23): each
  docket's items are held by the frame it hung under (`holds`) and the
  docket files are deleted.
- **Decision anchors** are `<date>--<slug>` for settled entries and
  `open--<slug>` for queued ones, the slug the first six content words of the
  title, written as an HTML comment (`<!-- decision: <anchor>; touches:
  kind:ref, … [; status: open] -->`) on the line after the heading (settled)
  or as the bullet's last line (queued), with `touches` extracted mechanically
  from the entry's explicit mentions of items (`item 87`, `items 92–93`),
  registry ids and backticked node ids. A pointer is added to the node each
  touch names: the item's node, the claim's formal result, the node itself.
  *Rejected:* heading ids, which the hosted renderers show; hand-read touches,
  which 283 entries do not allow in one round.
- **Round pointers** use the round's `path` from `state/rounds.json`; the
  checker resolves a `round` ref as a directory or as a round id or path.
- **A `foundation` work pointer kind** (ref an id in `state/foundations.json`)
  is the smallest extension that lets the foundation node point at its ledger.
- **A node may be a root of several frames** when it is neither a frame nor a
  want and every entry names the same role; the first frame in the frame tree's
  order is its home for paths. *Rejected:* duplicating the node per frame.
- **`owner` accepts a list** on frames (the form chosen over a second key
  `owners`), and `maintainer` accepts a list in `policy.yaml`.
- **Existing frames are re-owned by the line they sit under** (29 frames:
  `@abram` for the deference, decision-theory, stance and abstraction lines,
  both maintainers under legitimacy, `@anson` for the corrigibility landscape
  and its sub-frames), and **the thirteen wants by the attribution of their
  source documents** (the deference note dump's `notes/`, lab and chats are
  the second maintainer's by its own README; the corrigibility position
  statements are the published post's material, the first maintainer's; the
  unbounded-embedded sources sit in the second maintainer's level line): eight
  wants to `@abram`, five to `@anson`, every one still *owner has not
  confirmed*. *Rejected:* the blanket rename of every `@maintainer` to
  `@anson`, which would have made the first maintainer the owner of wants
  quoted from the second's words.
- **A `foundation` pointer kind** and **a `wiki` value of `filed_from`** are
  the two smallest extensions filed (§7 of the survey); **`narrative` accepts a
  list** so that two pages can narrate one node.
- **`wiki/ORIGIN.md`, `Sources.md`, `_Sidebar.md`, `Prior-Art.md`,
  `CONVENTIONS.md`, `Glossary.md`, `Relation-to-the-Field.md`** are legitimately
  unattached: receipt, bibliography, navigation, conventions, a glossary and a
  field map narrate no one node.
- **The top frame keeps its single owner `@anson`**, since M2 says the top
  frame stays as it is and lists owners for `the-program` and its lines only.

**Reserved to the maintainers** (also in `DECISIONS.md`, *Awaiting the author*):
the second maintainer's confirmation of M1–M8; the wording of `the-program`'s
question and of every line frame's; the roots marked *owner has not confirmed*
(nine drafted frames, the re-owned sub-frames, the re-owned wants); which of
the foundation's 180 claims are lifted into the map; the priority words on
every want; whether the 80 clean-room records should have a registry of their
own; the top frame's owner and the sub-frames' owners; the placements the
round left where they were.
