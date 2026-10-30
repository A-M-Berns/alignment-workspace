# The site

A static site generated from the argument map and the repository: `python3 site/build.py`
reads graph/index.json (running the plain checker first if the file is absent),
`graph/derived.json` (for the one page about the ranking), `state/projects.json`,
`state/rounds.json`, `state/foundations.json`, the claims registries under
`projects/*/CLAIMS.md`, the anchors of `DECISIONS.md`, the wiki source under `wiki/`,
`graph/policy.yaml`, the human ledgers under `graph/events/*.jsonl`, and `site/lede.md`,
and writes `_site/` (gitignored). The standard library only; no framework and no build
step beyond that command (ruling S2, 2026-10-24).

The site is a render. Nothing on it is typed by hand except `site/lede.md` (the front
page's one paragraph), and it is binding-checked: every `<!--bind:…-->` marker must agree
with the state. A build fails on any reference that does not resolve, as the checker
refuses one; `tests/site_build.py` runs the build as a gate under `tests/run.py`.

## The map is the front page (ruling S5, 2026-10-30)

`/` is a zoomable canvas: `/assets/map.js` (vanilla JavaScript, SVG) lays `/assets/map.json`
out as nested regions and zooms — the top question opens into the lines, a line into its
frame's goals and holds, a claim into its conjuncts; cross-edges (`part`, `given`, `held`)
draw between visible nodes on request. Three containments over the same node set are the
views: **concept** (the frame tree continued into the part edges), **rounds** (nodes under
the round that produced them), **class** (formal results by epistemic class). Clicking a
node loads its `/n/<id>/frag.html` — the node page's body without the layout — into a
panel; `/#n=<id>` (ids with `/` as `--`) deep-links it. Without JavaScript the front page
lists the lines as links, and every node remains a full page.

Every node page and fragment ends with the intake verbs — comment, challenge, estimate,
want — each a prefilled GitHub issue carrying the node id and a protocol-shaped body. The
site accepts no write; a maintainer round sweeps what lands into ledger events
(`graph/PROTOCOL.md`).

## One id, one URL (ruling S4)

Every object has exactly one path, derived from its id. The generator refuses two ids that
map to one path. These paths are the contract later rounds (the chatbot, the intake verbs)
build on.

| object | path | from |
|---|---|---|
| a node of the map (frames included) | `/n/<node id>/`, its fragment `/n/<node id>/frag.html` | graph/index.json `nodes` |
| a priority item | `/items/<n>/` (`<n>` the item number, `Q1`, `F3`) | the item nodes |
| a decision entry | `/decisions/<anchor>/` | the `<!-- decision: … -->` lines of `DECISIONS.md` |
| a round | `/rounds/<round id>/` | `state/rounds.json` |
| a registered claim | `/claims/<registry id>/` | the registries; redirects to the node its record belongs to |
| a wiki page | `/wiki/<Page>/` | `wiki/<Page>.md` |
| a handle | `/by/<handle without @>/` | `graph/policy.yaml` |
| the map data | `/assets/map.json` | the containments and edges above |
| the feed, the theorem spine, the ranking, search | `/feed/`, `/spine/`, `/ranking/`, `/search/` | — |

A path segment is the id with `/` replaced by `--`; ids contain no other character a URL
cannot carry. Two ids that collapse to one segment are a build failure.

## Pages

- **Front page** (`/`): the top frame's question, the lede, the map canvas, the feed's
  head collapsed below it.
- **Frame page** (`/n/<frame>/`): question, owners, narrative, roots by role, what it holds by
  kind, sub-frames, the path up to the top frame; *no goal yet* where `roots` is empty.
- **Node page** (`/n/<id>/`): Statement, Source, Notes, kind, author and the human events on
  it, parents and children by edge kind (part, given, root-of, held-by), work pointers
  resolved, the frames it is in; for a formal result the bridge card (the informal claim,
  the declaration with its Lean file, the bridge, the hypotheses with their tags or *unread*,
  the registry class and review status, and the improvement claim's routes as *what
  remains*); a collapsed *ranking* section with the node's numbers; the intake verbs.
- **Item, decision, round, wiki, handle pages**, the **feed**, the **theorem spine**, the
  **ranking** page (the content of `graph/tasks.md` with the digest, labelled as the lens
  it is) and **search** (a client-side index over ids, Statements, titles and registry
  short names).

AI-drafted nodes (an AI author and no human event) render in a lighter register with the
label *drafted*, on the canvas and on the pages. Every page shows the commit it was built
from.

## Building locally

```
python3 -m checkers.graph --root .     # writes graph/index.json and graph/derived.json
python3 site/build.py                 # writes _site/ (Python ≥ 3.12)
python3 -m http.server -d _site 8000   # then open http://localhost:8000/
```

`python3 site/build.py --check` builds into a temporary directory and reports the counts and
any unresolved reference without writing `_site/`; that is what the gate runs.
