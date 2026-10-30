# Prompt — the site, as one vertical slice (2026-10-24)

You are working in the `alignment-workspace` repository. Branch from
`round/2026-10-22-map-as-canonical` at its head (PR #131, unmerged by the maintainers'
choice): this round is STACKED on it, and that is deliberate — everything it reads (`holds`,
`graph-index/3`, the item nodes, the uncommitted derived files) exists only there. Open the
pull request with base `round/2026-10-22-map-as-canonical`, not `main`, so the diff is this
round's alone; the body says "stacked on #131; merge #131 first" in its first line. Touch no
file #131 touched unless a part below names it. Auto-merge OFF.

Round directory `projects/enabling/rounds/2026-10-24-site-vertical-slice/` (a new line
directory, `projects/enabling/`, for workspace rounds — see Part 0); the prompt verbatim in
`prompts/2026-10-24-site-vertical-slice/PROMPT.md`. New priority items start at 129. Run
`python3 -m checkers.graph --root .` and `python3 tests/run.py` before every commit.

## What this round is for

The map is now the canonical index of the program and is flat where it matters: results are
held by programmes, not connected to the claims they establish. This round does two things
that test each other. It connects five reference results to the claims they are for, by
reading, as the precedent every later connection follows; and it builds the first version of
the website — a static site generated from the map and the repository, with one guided walk
from a research question down through those five results to the work a visitor could pick
up. Building the walk is how the round finds out whether the five were connected in the
right shape. The site is not finished after this round; the walk is.

Rules that bind: structure and numbers are decoupled, and the site renders structure and
human events, showing numbers only where a page is explicitly about the ranking; AI-drafted
structure is visibly lighter than anything a human event has touched; the protocol changes
through its own mechanism where it cannot hold something; no number, judgment, acceptance,
priority word or human event is written. Every path, id and field named below was read from
the branch at #131's head; confirm each and correct this prompt in the report where it is
wrong.

## Maintainer rulings

Land as one dated `DECISIONS.md` entry, the first commit, marked as taken by one maintainer
in conversation with the other's confirmation outstanding.

**S1. The five reference results.** [MAINTAINER: keep or swap any.]
`compiler.deductive-end-to-end` (the traderization headline, `deductive_end_to_end`);
`warrant.licence-chain` (Licensed ⇒ Supported ⇒ Admissible); `openness.certplus-is-robust-openness`
(`certPlus_iff_robustOpen`, the legitimacy spine's equivalence); the `effective-authority-layer`
cluster (the seven `authority.*` and five `sincerity.*` claims of
`projects/deference/CLAIMS.md`, one informal claim established by twelve declarations — the
multi-record precedent); `delegation.bridge` (the finite delegation bridge, so the walk
crosses into the deference line). Each is connected per Part 1 and nothing else is: the
precedent is the deliverable, not coverage.

**S2. The site is generated, stdlib-only, and never a second source.** `site/` holds a
Python generator (standard library only, like the checkers; a few hundred lines of
hand-written CSS and vanilla JavaScript for navigation and client-side search; no framework,
no build step beyond `python3 -m site.build`). It reads `graph/index.json` (running the plain
checker first if the file is absent), `state/*.json`, the two registries, `DECISIONS.md`'s
anchors, the wiki source and `graph/events/*.jsonl`, and writes `_site/` (gitignored). A
build fails on any reference that does not resolve, exactly as the checker refuses one: the
build is a gate, run by `tests/run.py`. Nothing on the site is typed by hand except the walk
documents of Part 2 and the front page's one lede paragraph, both of which live in the
repository and are binding-checked.

**S3. Deployment.** A workflow `.github/workflows/site.yml` builds `_site/` on every push and
pull request (read scope; uploads it as an artifact so a reviewer can open a pull request's
build) and, on `push` to `main` only, deploys it to GitHub Pages through a write-scope job
enumerated in `AGENTS.md` *Security* like `derived-publish`. No custom domain in this round:
`site/CNAME` is added only when the maintainer supplies one [MAINTAINER: domain, or
"none yet"]. The Pages deploy will not run until #131 and this merge; the artifact is the
preview until then.

**S4. One id, one URL.** Every node, item, decision anchor, round, registry id, wiki page and
handle has exactly one path on the site, derived from its id: `/n/<node id>/`,
`/items/<n>/`, `/decisions/<anchor>/`, `/rounds/<round id>/`, `/claims/<registry id>/`
(redirecting to its record's node), `/wiki/<Page>/`, `/by/<handle>/`. The generator refuses
two ids that map to one path. These paths are the contract the chatbot and the intake round
will build on; document them in `site/README.md`.

## Part 0 — the enabling line directory

Workspace rounds have no `projects/` home: `2026-10-02-graph-prototype` indexed itself with
path `graph`. Create `projects/enabling/README.md` (three paragraphs: what the line is, that
its rounds build the repository's machinery, that it registers no claims) and
`projects/enabling/rounds/`; add the project to `state/projects.json` with `status: active`,
`parent: null`, the README as its entry point; point the `enabling-work` frame's `narrative`
at `wiki/CONVENTIONS.md` as now and add `work: {kind: round, ref: projects/enabling/rounds/2026-10-24-site-vertical-slice}`
to the `enabling-program-site` claim. If `workspace_state --check` or the path gate objects to
a project with no `CLAIMS.md`, say so and give it an empty registry with the standard header
rather than suppressing the check.

## Part 1 — the five connections, by reading

For each of S1's five, in its own commit, read the Lean declaration(s), the registry entry
and note, the round report named in `docs`, and the wiki page that narrates the programme,
and then:

1. **Find or file the informal claim** `C` the result establishes: the sentence a reader of
   the wiki would take the theorem to show. Search existing nodes first (the F5 ambiguous
   list in the follow-up report Part 3 names candidates for the authority cluster:
   `effective-authority-layer`). Where an existing node is that claim, use it; where none is,
   file it, `author` the round's AI handle, Source the wiki page and report that state it.
2. **Make `C` the `and` of its formal result(s)** per the merge pattern of F5: `C`'s children
   gain the formal-result `and`(s) — for the authority cluster, twelve of them, which is the
   multi-record shape: a claim-`and` whose conjuncts are formal-result `and`s, each with its
   own record, bridge and completeness leaf — plus `C`'s own completeness leaf whose Statement
   says what the conjuncts together establish and what they do not. The formal-result ids
   stay as nodes (they are not superseded; they are now parts of `C`), leave the frame's
   `holds`, and `C` becomes a `shared-claim` root of the programme that held them, so the
   claim — not the theorem — is the goal.
3. **File the hypotheses by reading.** Replace `hypotheses: unread` on each record with
   hypothesis leaves, one per hypothesis of the declaration as a reader would state it (not
   one per binder: a structure's fields that are bookkeeping are one leaf; a substantive
   assumption is its own), each with its `discharge` tag chosen by reading
   (`definitional`, `proved-in-model`, `restates-conclusion`, `open`) and a one-line reason in
   its Notes. Where a hypothesis restates the conclusion, say so: that is the finding the
   protocol's level rule exists for.
4. **Rewrite the bridge by reading.** The bridge's Statement says, in the reader's words,
   what the informal claim asserts and what the declaration certifies, and names the gap
   where there is one (a parameter fixed in the Lean that the claim leaves free; a finite
   fixture where the claim is general; an assessment-relative criterion where the claim
   sounds absolute). `attribution` stays `formalizer-stated` — the round is not the author.
5. **File what is missing** between `C` and the programme's question as routes under `C`'s
   improvement claim (`improves: C`, `reality: <what the programme asks>`, routes conditioned
   on `C@valid`, the residual route), each route naming the existing item it corresponds to
   where one exists (`work: {kind: priorities, ref: n}`) and otherwise a new item filed within
   this round's scope, in `PRIORITIES.md`'s format via its node. This is the "what remains"
   a visitor reads.
6. **Record the connection** in a table in the report: result ids → `C` → hypotheses with
   tags → the bridge's named gap → the routes and their items. The five tables are the
   precedent document; collect them as `projects/enabling/rounds/<this>/CONNECTIONS.md` and
   link it from `graph/MAP-AS-CANONICAL.md` §1 as the worked example of the pattern.

Everything filed here is at level 0 and AI-drafted; the site shows it as such. The round
writes no `attribution` event (a human's) and no `admit`.

## Part 2 — the walk

A walk is a hand-written document in `site/walks/<slug>.md` whose body is prose and whose
every step names an id the build resolves; the generator renders it as a guided page where
each step shows the live node (its Statement, kind, status of human reading, what holds it,
what it holds) with the walk's prose beside it. One walk this round:
`site/walks/normative-inductor-corrigible.md`, from the question "What would it take to show
that a normative inductor learns in a way that is both genuinely normative and corrigible to
a principal?" down through `the-program`, `normativity` and `legitimacy`, the five claims of
Part 1 (the authority cluster and `openness.certplus-is-robust-openness` on the legitimacy
side; `compiler.deductive-end-to-end`, `warrant.licence-chain` on the normativity side;
`delegation.bridge` where deference enters), their bridges and their named gaps, to the
routes and items of step 5 — ending on three concrete things a visitor could do: an item to
execute, a bridge to judge, a want to file. The prose is the round's draft, marked as such on
the page, for the maintainers to rewrite; the structure (which ids, in which order) is what
the round is asked to get right, and the report says where the walk could not be made to
flow because the map lacked an edge — those are findings about the map, listed, not patched
around in prose.

## Part 3 — the generator and the pages

`site/build.py` and its modules. Pages, each from the index and the files S2 names:

- **Front page**: the top frame's question; `the-program` and its seven lines as cards (the
  line's question, its owners, its narrative's first paragraph, counts of roots / held
  results / held items / open items, each count a binding); the one lede paragraph from
  `site/lede.md` (hand-written, binding-checked); the walk(s); the feed. Owners shown by
  handle with the GitHub account from `policy.yaml`.
- **Frame page** (`/n/<frame>/`): question, owners, narrative (the wiki page rendered),
  roots grouped by role, what it holds grouped by kind (formal results, items, other), the
  sub-frames, the path up to the top frame, "no goal yet" where `roots` is empty.
- **Node page** (`/n/<id>/`): Statement, Source, Notes, kind and leaf kind, author and
  whether a human event has touched it (which, by whom, when — from the ledgers), its
  parents and children by edge kind (part / given / root-of / held-by), its `work` pointers
  resolved (rounds, items, decisions, foundation), the frames it is in. For a formal result:
  the **bridge card** — the informal claim on top, the record's declaration with a link to
  the Lean file at the commit, the bridge's Statement and attribution, the hypotheses with
  their tags or *unread*, the registry class and review status, and beneath it the
  improvement claim's routes as "what remains".
- **Item page** (`/items/<n>/`): the rendered item (title, difficulty, project, status,
  deliverable, acceptance, context links), results bearing on it, rounds that touched it,
  the frame that holds it or the goal it is a route of, decisions that touch it.
- **Decision page** (`/decisions/<anchor>/`): the entry's prose from `DECISIONS.md` (by
  anchor, verbatim), its `touches` resolved, nodes that point at it, open/settled.
- **Round page** (`/rounds/<id>/`): date, project, verdict, prompt and report rendered,
  claims it registered, items it filed, nodes that point at it.
- **Wiki page** (`/wiki/<Page>/`): the source rendered; every claim, item and round reference
  the `wiki_refs` checker resolves becomes a link carrying the target's live class or status;
  a "sources last changed" date from git beside the page's own last-changed date.
- **Handle page** (`/by/<handle>/`): the frames they own, the wants they own with priority
  state, their events in order.
- **Feed** (`/feed/`): merged rounds, claims registered, items opened/closed, decisions
  landed, by date, from `rounds.json`, the registries' `origin_round`, item status and the
  decision anchors.
- **Theorem spine** (`/spine/`): the formal results as a DAG by the part/given edges between
  their claims, class-coloured, from `graph-index/3`; held-only results listed below as
  unconnected. Small and honest this round; the five connected claims are what it will show.
- **Search**: a client-side index over ids, Statements, titles and registry short names.

Rendering rules: Markdown rendered by a small stdlib renderer the round writes (headings,
lists, code, links, emphasis; nothing fancier — say what it does not support); AI-drafted
nodes (no human event) in a lighter register with a one-word label; every page shows the
commit it was built from; no number from the ranking appears except on `/n/<id>/` under a
collapsed "ranking" section and on a `/ranking/` page that renders `tasks.md`'s content with
the digest, labelled as the lens it is. Mobile-usable, one stylesheet, dark mode by media
query. Load `artifact-design`'s guidance only if it is available to you; otherwise plain,
legible typography is the standard.

## Part 4 — gates and workflow

`tests/site_build.py`: the build runs on the tree and fails on an unresolved reference, a
duplicate path, a walk step naming no id, a binding in `lede.md` or a walk that disagrees
with the state; registered in `tests/run.py` and the gate-coverage list. `site.yml` per S3,
with `WORKFLOW SCOPE` passing and the write-scope job enumerated. `.gitignore` gains `_site/`.
`AGENTS.md` gains a short *The site under `site/`* section (what it reads, that it is a
render, that the walks and lede are the only prose, how to build locally) and the
enumeration; `CONTRIBUTING.md` *Where to find work* points at the site once it exists;
`graph/MAP-AS-CANONICAL.md` §6 is brought to what was built.

## Reserved to the maintainers

Append to *Awaiting the author*, each with its *turns on* line: the walk's prose and whether
the walk's structure is right; the five bridges' rewritten Statements and the hypotheses'
tags (a human reading of each, which is the `attribution` event and the vetting the protocol
asks for); the informal claims the round filed where none existed; the custom domain; and
anything Part 2 found the map lacked.

## Report

`prompts/2026-10-24-site-vertical-slice/REPORT.md`. Verification first: the checker's OK and
DIGEST lines before and after, `tests/run.py`, the build's output (pages generated by kind,
unresolved references = 0, build time), a screenshot or text dump of the walk page and one
bridge card from the built `_site/`; then the five connection tables (or the link to
`CONNECTIONS.md`); the walk's findings about the map; deviations; corrections to this
prompt; what the site does not yet do (the intake verbs; the chatbot; the remaining 230-odd
held results; the second maintainer's lines; the domain); the reserved list; the merge
order (#131 first, then this).
