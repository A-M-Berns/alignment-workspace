# Report — the site, as one vertical slice (2026-10-24)

Prompt: `prompts/2026-10-24-site-vertical-slice/PROMPT.md`, verbatim. Branch `round/2026-10-24-site-vertical-slice`, stacked on `round/2026-10-22-map-as-canonical` at `1a6c60d8` (pull request #131, unmerged by the maintainers' choice); this round's pull request has that branch as its base, so its diff is this round's alone. Rulings S1–S4 landed as one dated `DECISIONS.md` entry (anchor `2026-10-24--site-vertical-slice-five-reference-results-generated-site-one-id-one-url`), the first commit, taken by one maintainer in conversation with the other's confirmation outstanding. Auto-merge is off. Commits: `553c1dab` land the four maintainer rulings (S1–S4) in DECISIONS.md; `3bfcb902` the enabling line directory (Part 0); `71214f34` connect compiler.deductive-end-to-end by reading (1 of 5); `dec367d4` connect warrant.licence-chain by reading (2 of 5); `4757c049` an AI handle is derived from its model, never chosen; `5239d3ea` connect openness.certplus-is-robust-openness by reading (3 of 5); `d328680a` connect the effective-authority cluster by reading (4 of 5); `85984d3a` connect delegation.bridge by reading (5 of 5); `81943780` the generated site, the walk, the gate and the workflow (Parts 2–4) and the report commit. Every commit was preceded by `python3 -m checkers.graph --root .` and `python3 tests/run.py`.

## 1. Verification

**The checker, before and after** (`python3 -m checkers.graph --root .`, Python 3.12):

```
before  OK 2408 nodes, 2411 events, 1886 ranked units; research first: the decision term (printed, not applied) favours vet hull-condition-total-trust (ranked unit 16), D 0.00016
        DIGEST no previous derivation to compare with (neither the branch derived nor a derived.json on disk that versions.json records)
after   OK 2467 nodes, 2411 events, 2094 ranked units; research first: the decision term (printed, not applied) favours vet hull-condition-total-trust (ranked unit 43), D 0.00016
        DIGEST compared with graph/derived.json on disk (the derivation versions.json at HEAD records): 0 status(es) flipped, 0 root status(es) flipped, 0 level(s) moved, 0 event(s) counted since, 0 revision(s), 0 want(s) filed since, 0 proposal(s) awaiting
```

One WARN line throughout, the summary of decision anchors no node points at (250 of 301). The self-test passes.

**`tests/run.py`** on the final tree: `ALL GREEN (80 project(s))`, with the new gate `SITE BUILD` in the run (§9 has the tail). Lean was not built (no Lean file changed).

**The build** (`python3 site/build.py --check`, the gate's form):

```
SITE BUILD: {"commit": "819437805845061c93df0df35b796bd3588cf10e", "counts": {"connected": 85, "decisions": 301, "held": 345, "items": 141, "lines": 7, "nodes": 2467, "registered": 178, "results": 249, "rounds": 127, "wiki_pages": 34}, "pages": {"claim-redirect": 178, "decision": 301, "feed": 1, "front": 1, "handle": 4, "item": 141, "listing": 6, "node": 2467, "ranking": 1, "round": 127, "search": 1, "search-index": 1, "spine": 1, "walk": 1, "wiki": 34}, "paths": 3253, "seconds": 2.17, "unresolved": 0}
```

Pages by kind, unresolved references 0, build time as the line says. A text dump of the walk page's first steps and of one bridge card from the built `_site/` is in §9.

**Counts** (before → after): nodes 2,408 → 2,467 (the hypothesis leaves, the three filed claims with their completeness leaves, the improvement claims, the routes and the four new items); ranked units 1,886 → 2,094 (the five claims and their improvement claims and routes are goals now); held nodes 361 → 345 (the five results and the twelve of the cluster left their frames' `holds`); items 137 → 141; registered results connected to an informal claim (a `part` edge above them) 69 → 85.

## 2. Part 0 — the enabling line directory

`projects/enabling/README.md` (three paragraphs), `projects/enabling/rounds/2026-10-24-site-vertical-slice/` (its README and `CONNECTIONS.md`), the project in `state/projects.json` (`status: active`, `parent: null`, the README its entry point), the round in `state/rounds.json` (`project: enabling`, depends on the map round), the `enabling-work` frame's narrative unchanged at `wiki/CONVENTIONS.md`, and the `enabling-program-site` claim pointing at the round. `checkers.workspace_state --check` raised no objection to a project without a `CLAIMS.md` (its rule is that a registry belongs to an active project, not that every project has one), so no empty registry was added.

## 3. Part 1 — the five connections

The tables are `projects/enabling/rounds/2026-10-24-site-vertical-slice/CONNECTIONS.md`, linked from `graph/MAP-AS-CANONICAL.md` §1 as the worked example. In one line each:

| result(s) | `C` | found or filed | frame(s) `C` is a root of | hypotheses (tags) | routes → items |
|---|---|---|---|---|---|
| `compiler.deductive-end-to-end` | `traderized-finite-date-conformance` | found (a step leaf of `formalism-open-questions-0-3`, made an `and`) | `operative-force` (new), `formalism-open-questions-0-3` (kept) | 4: two schedules and the source's certificate (definitional), satisfiable stages (open) | 39, 42, 43, **129** (new) |
| `warrant.licence-chain` | `verdict-licence-chain` | filed | `normative-inductor` | 4: record state, certificate (definitional); the Supported clause (**restates the conclusion**); the authorized event (definitional, carried not used) | 115, 56 |
| `openness.certplus-is-robust-openness` | `split-bill-is-robust-openness` | filed | `openness-and-non-capture` (its first goal) | 3: scenario, protected routes (definitional); actual coverage (open) | **130** (new) |
| the twelve `authority.*` and `sincerity.*` | `effective-authority-layer` | found (a step leaf, made the `and` of twelve results) | `authorship-and-transparency` (kept), `public-corrigibility-line` (new, shared) | 16 over twelve records: fixtures and cases definitional; the sincere reference and the calm exterior open | 107, 101, **131** (new) |
| `delegation.bridge` | `local-delegation-bridge` | filed | `deference-finite-results` (its first goal) | 2: cell masses (definitional); grade trust (open, imported) | **132** (new), 23 |

Each `C` is the `and` of its formal result(s) and its own completeness leaf; the formal-result ids stay as nodes (conjuncts, not aliases) and left their frames' `holds`; every bridge was rewritten by reading with `attribution: formalizer-stated`; every record's `hypotheses: unread` became a list. The reading rule for the tags is stated at the head of `CONNECTIONS.md`. The finding the level rule exists for: the licence chain's first arrow, Licensed → Supported, is the definition of Licensed read back, so one hypothesis leaf is tagged *restates the conclusion* and the result's content is the second arrow alone.

A protocol change the first connection forced, through the protocol's own mechanism: a range `estimate` on a leaf that has since become an `and` or an `or` is stale (*leaf became an and*), beside the existing *leaf became a table*, since the node's probability is now derived from its children; eleven AI estimates on claims earlier rounds made `and`s went stale with it (`PROTOCOL.md` §2 and §3, one design-log line). Numbers moved where those estimates had counted: 12 events (smithy-verity-100, smithy-verity-101, smithy-verity-102, smithy-verity-170, smithy-verity-218, smithy-verity-220, smithy-verity-223, smithy-verity-224, smithy-verity-301, smithy-verity-302, smithy-verity-451, smithy-verity-473); the affected nodes' levels and the units on them changed as the digest of the first connection's run recorded, and no committed render carries the digest.

## 4. Part 2 — the walk

`site/walks/normative-inductor-corrigible.md`: the question, then `the-program`, `normativity`, `operative-force`, the conformance claim, its result and its improvement claim; `normative-inductor`, the licence-chain claim and result; `legitimacy`, `openness-and-non-capture`, the split-bill claim and result; `authorship-and-transparency`, the effective-authority layer and two of its twelve results; `deference-and-trust`, `deference-finite-results`, the delegation bridge claim and result; then the three things a visitor could do: item 129 to execute, the licence chain's bridge to judge, and `legitimacy-meets-syntax` as the frame under which to file a want. 24 steps, every one resolving; the page marks the prose as the round's draft.

**What the walk found the map lacked** (findings, not patched around in prose):

- No edge runs from the normativity line's compiled conformance to a trust bound the deference line reads; the walk crosses lines only through `the-program`, and item 129 is the route that would supply the edge.
- The authority results were held by two frames (`public-corrigibility-line` the seven, `authorship-and-transparency` the five); the claim they establish is now a shared root of both, which is the map's way of saying one claim serves two programmes.
- Nothing connects the inductor's licence (normativity) to the legitimacy line's syntax frame (`legitimacy-meets-syntax`), where the question's two halves meet; the walk ends there by naming the frame.
- The walk's last step cannot name a want: a want a visitor would file does not exist until filed, so the step names the frame it would be filed under.
- Two programmes had no goal at all until this round (`openness-and-non-capture`, `deference-finite-results`): their first goals are the claims a theorem happens to establish, which is a placement the maintainers should confirm (queued).

## 5. Part 3 — the generator and the pages

`site/build.py` with `site/load.py`, `site/pages.py`, `site/md.py`, `site/assets/style.css`, `site/assets/app.js`; `site/README.md` is the URL contract. Pages built: claim-redirect 178, decision 301, feed 1, front 1, handle 4, item 141, listing 6, node 2467, ranking 1, round 127, search 1, search-index 1, spine 1, walk 1, wiki 34; 3253 paths in all. Front page, frame, node (with the bridge card and a collapsed ranking section), item, decision, round, wiki (references resolved to links carrying the live class or status; the page's and its sources' last-changed dates from git), handle, feed, theorem spine, ranking (the content of `graph/tasks.md` with the digest, labelled as the lens), search (a client-side index over ids, Statements, titles and registry short names), walks, and `/claims/<id>/` redirects. AI-drafted nodes render in a lighter register with the label *drafted*; every page shows the commit it was built from; one stylesheet with dark mode by media query; mobile-usable.

The Markdown renderer (`site/md.py`) supports ATX headings, paragraphs, one-level-nested lists, fenced code, block quotes, pipe tables, horizontal rules, inline code, emphasis, strong, links, wiki links and HTML comments. It does not support deeper nesting, setext headings, footnotes, definition lists, raw inline HTML (escaped), images (rendered as links), reference-style links, task lists or math.

## 6. Part 4 — gates and workflow

`tests/site_build.py` runs `site/build.py --check` as a gate and carries the self-test (a lede binding that disagrees, a binding naming no count, a walk with no step, two ids on one path, an unresolved id, a walk step naming no node failing the real build, and the live tree building); registered in `tests/run.py` (`GATE_SELF_TESTS` and the real form). `.github/workflows/ci.yml` builds the site at read scope on every push and pull request and keeps `_site/` as an artifact; `.github/workflows/site.yml` deploys `main`'s build to GitHub Pages through `site-deploy` (`pages: write`, `id-token: write`), enumerated in `AGENTS.md` *Security* with its `write-scope` marker; `WORKFLOW SCOPE` passes. `.gitignore` gains `_site/`. `AGENTS.md` gains *The site under `site/`*; `CONTRIBUTING.md` *Where to find work* points at the site; `graph/MAP-AS-CANONICAL.md` §6 describes what was built and §1 links `CONNECTIONS.md`.

## 7. Deviations from the prompt, with reasons

- **`python3 -m site.build` cannot run; the command is `python3 site/build.py`.** `site` is the name of a standard-library module Python imports at startup, so a package of that name is shadowed and `-m site.build` fails with "site is not a package". The directory keeps the prompt's name; the generator is a script in it with its sibling modules on the path.
- **The pull-request build lives in `ci.yml`, not `site.yml`.** The repository's own gate (`tests/workflow_scope.py`) forbids a write-scoped job in any workflow that lists `pull_request`; `site.yml` is the push-to-`main` deploy alone, as `derived.yml` is. The rulings entry says so beside S3.
- **The improvement claim of each connected claim is a root of the programme alone.** Where `C` is a root of two frames (the conformance claim, the authority layer), the protocol's "the frame holding X's root" is ambiguous; the programme that held the result got the improvement claim.
- **The effective-authority claim is a shared root of two frames**, not moved: its seven authority results were held by `public-corrigibility-line` and its five sincerity results by `authorship-and-transparency`, where the dissolution of the legitimacy-and-reasons programme had placed the claim; making it a root of both is the only shape in which both frames' holds empty into one claim.
- **A new item is its route.** The four new items (129–132) are route leaves carrying the item fields, so the work order hangs under the goal it serves as the protocol asks, rather than a task leaf beside a route pointing at it.
- **A protocol change** (the stale range on a leaf that became an `and`), §3 above; not in the prompt, forced by the first connection.
- **Two slips in method, corrected before building on them:** twice a chained command committed on a run that had failed (a failing fixture test, then the workflow-scope gate on a not-yet-enumerated workflow); each time the failure was fixed and the suite rerun green on the committed tree before the next commit, and the second commit's content was unchanged by the fix (the failing input was an untracked file).

## 8. Corrections to this prompt

- "`graph-index/3`, the item nodes, the uncommitted derived files exist only there": correct; `holds` too.
- "the F5 ambiguous list in the follow-up report Part 3 names candidates for the authority cluster: `effective-authority-layer`": correct (its rows for `authority.comprehension-short`, `authority.queue-no-bypass` and others name it).
- "`openness.certplus-is-robust-openness` (`certPlus_iff_robustOpen`, the legitimacy spine's equivalence)": the declaration is `Scenario.certPlus_iff_robustOpen` in `NonCaptureCertificate.lean`; it is the openness programme's compression theorem, not the spine's.
- "the seven `authority.*` and five `sincerity.*` claims": correct; the seventh authority result is `authority.revocation-default`, whose declaration is `Dep.atrophy_on_module` (re-pointed by the thin-legitimacy follow-up).
- "`enabling-work` frame's `narrative` at `wiki/CONVENTIONS.md` as now": correct.
- "add `work: {kind: round, …}` to the `enabling-program-site` claim": done; it is a task leaf, and the field is `work:` with one entry.
- "New priority items start at 129": correct; the tree's highest was 128 and `maintainer_order` 137.
- `python3 -m site.build`: see §7.
- "`site/CNAME` is added only when the maintainer supplies one": correct; no domain was supplied, so none exists, and the rulings entry names the path without backticks because the pointer gate refuses a backticked path that does not exist.
- Everything else named (paths, ids, fields) exists on the branch at `1a6c60d8`.

## 9. Test output

```
WORKFLOW SCOPE: clean over 5 workflow(s); 4 enumerated write-scope job(s)
DEAD POINTERS: clean over 58 live document(s) — 976 rooted path(s) resolve, 8 of them into declared trees and each saying so; 110 unrooted and 228 glob(s) not this gate's business; 14 historical span(s) and 5 ledger citation(s) exempt
UNTRACKED POINTERS: clean — 335 round-record path(s) and 1035 resolving citation(s) are in the repository, not merely on this disk
WORKSPACE STATE: valid — 7 projects, 178 modern claims, 1 foundations, 180 foundation claims, 127 rounds, 52 terms, 141 priorities, 10 interface objects
WIKI REFS: clean over 34 page(s); 304 reference(s) resolve
PRIORITIES RENDER: the committed file equals the render (141 items)
OK 2467 nodes, 2411 events, 2094 ranked units; research first: the decision term (printed, not applied) favours vet hull-condition-total-trust (ranked unit 43), D 0.00016; nothing written (--dry-run)
Ran 146 tests in 124.385s
OK
SITE BUILD: {"commit": "85984d3a7a8925585f1c9525ebf5c5adb63cb215", "counts": {"connected": 85, "decisions": 296, "held": 345, "items": 141, "lines": 7, "nodes": 2467, "registered": 178, "results": 249, "rounds": 127, "wiki_pages": 34}, "pages": {"claim-redirect": 178, "decision": 296, "feed": 1, "front": 1, "handle": 4, "item": 141, "listing": 6, "node": 2467, "ranking": 1, "round": 127, "search": 1, "search-index": 1, "spine": 1, "walk": 1, "wiki": 34}, "paths": 3248, "seconds": 1.99, "unresolved": 0}
GATE COVERAGE: 12 gate scripts, all invoked (5 self-test only — no local form)
LEAN SORRY GATE: clean over 108 files
LEAN AXIOM DISCIPLINE: every file carries `#print axioms`
PROJECTS:
  … 80 PASS lines, one per project runner, elided
LEAN BUILD SKIPPED: set WORKSPACE_LEAN=1 to run `lake build`
ALL GREEN (80 project(s))
```

The build line and a text dump of the walk page's head and of one bridge card (`_site/n/warrant.licence-chain/index.html`), from the built site:

```
SITE BUILD: {"commit": "819437805845061c93df0df35b796bd3588cf10e", "counts": {"connected": 85, "decisions": 301, "held": 345, "items": 141, "lines": 7, "nodes": 2467, "registered": 178, "results": 249, "rounds": 127, "wiki_pages": 34}, "pages": {"claim-redirect": 178, "decision": 301, "feed": 1, "front": 1, "handle": 4, "item": 141, "listing": 6, "node": 2467, "ranking": 1, "round": 127, "search": 1, "search-index": 1, "spine": 1, "walk": 1, "wiki": 34}, "paths": 3253, "seconds": 2.17, "unresolved": 0}

# /walks/normative-inductor-corrigible/ (the first four steps, as text)
What would it take to show that a normative inductor learns in a way that is both genuinely normative and corrigible to a principal?
a guided walk
The prose of this walk is the round's draft, marked as such for the maintainers to rewrite; each step shows the live node beside it.
The round's draft (2026-10-24), for the maintainers to rewrite. The structure of the walk, which nodes in which order, is what the round was asked to get right; the prose beside each step is a reading, not a ruling.
The question has two halves, and the map keeps them in two lines. Genuinely normative is the normativity line's question: what learning from reasons requires of a reasoner, from a seed of obligations through the market in which a constraint acquires force, to the licence under which a verdict may be announced. Corrigible to a principal is the legitimacy line's: what must stay true of a trajectory'
1
One plan under the top question, owned by both maintainers, whose roots are the seven lines. Everything below is a sub-frame of it; the two halves of our question are two of its lines, and a third, deference and trust, is where the principal's trust in a faster inductor is modelled.
the-program
A formal account of how humans and AI systems learn from, correct and rely on each other, refined until it models their situation, guides AI safety engineering work.
frame · drafted
root of the top frame (plan)
holds 0 node(s); 7 root(s)
2
The line for genuinely normative. Its question names the pieces in order: the statics a seed forces, how a constraint acquires operative force in a market, and what the Normative Inductor establishes end to end. Two of its programmes carry the results we visit: operative force, and the inductor itself.
normativity
A reasoner that answers to legitimately incurred obligations without ceasing to be a logical inductor exists as a conditional theorem, built from the seed statics, operative force bought under a finite liability account, a proof-carrying compiler from the accounted record to a region, and the response-learning bound.
frame · drafted
root of the-program (plan)
holds 36 node(s); 8 root(s)
3
How a constraint on prices acquires force in a market: the traderization arc. The programme holds the arc's registered results; since this round one of them is connected to the claim it establishes, which is now the programme's first goal.
operative-force
Logical Induction generalizes from a deductive process to an assessment process, an enforcement position compiles to a legal trading strategy with a conformance algebra, the criterion is preserved under bounded assessed liability, and for deduction the original criterion and finite-date coherence follow from a compiled market that assumes nothing about the deductive process beyond the pinned sourc
frame · drafted
root of normativity (plan)
holds 27 node(s); 3 root(s)

# /n/warrant.licence-chain/ (the bridge card, as text)
Bridge card
A conjunct of the informal claim verdict-licence-chain: A verdict licence is a certificate supported on the compiled bundle together with an authorized record event, and a licensed verdict is supported on the record's grounds and admissible in their settled region, the step from supported to admissible holding by rational convexity of the region rather than by projection.
Declaration Workspace.Normativity.Contrib.WarrantEntitlement.licence_chain in lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean (record warrant.licence-chain.record)
Registry warrant.licence-chain: class lean-proved, status active, review ci-only, origin round 2026-10-20-warrant-enforcement-semantics; bears on item 56
Bridge (formalizer-stated; warrant.licence-chain.bridge, drafted):
The claim asserts a chain of three standings for an announced verdict: licensed implies supported implies admissible. The declaration certifies, for a record state at one step, that a verdict licensed there (supported on the record's survivors by a certificate whose cited rows are live, and issued by an authorized event) is supported on the record's grounds under its docket and settlement, and adm
Hypotheses, read:
warrant.licence-chain.h-record-state definitional: A record state at a step consists of admitted grounds, a docket, a settlement and the set of record events the record authorizes.The implicit binder `R : RecordState d` and the coordinate and value `φ`, `v`. Definitional: the object the chain is stated over, Part A's view of the record; nothing is assumed of its contents.
warrant.licence-chain.h-verdict-certificate definitional: A verdict certificate is a lower and an upper bound certificate, each row cited by occurrence, a pin or a cube face, with the two endpoints and the region points that attain them.The implicit binder `c : VerdictCert d m m' φ`. Definitional: the shape of a certificate; whether its rows are admitted is the Supported clause below.
warrant.licence-chain.h-supported restates-conclusion: The certificate's positively weighted rows are cited into the settled bundle, its endpoints bracket the verdict, and both endpoints are attained in the bundle's region (the verdict is Supported).The first conjunct of `h : Licensed R φ v c event`, since Licensed is defined as Supported together with an authorized event. It restates the conclusi
warrant.licence-chain.h-authorized-event definitional: The event that issued and selected the certificate is one the record authorizes.The second conjunct of `h : Licensed R φ v c event`. Definitional: part of what Licensed means; the conclusion does not read it (neither Supported nor Admissible mentions the event), so the chain carries the authorization clause without using it. Where a licence is
Completeness (warrant.licence-chain.complete): No premise beyond the signature's binders enters the declaration; the kernel checks it as stated. The result is the record, the four hypothesis leaves filed by reading (the record state, the verdict certificate, the Supported clause of Licensed, which restates the conclusion's first conjunct, and the authorized-event clause, which the conclusion does 
What remains (verdict-licence-chain.improvable)
The licence chain, in which a licensed verdict is supported on the record's grounds and admissible in their settled region, can be improved until it reflects a Normative Inductor whose announced verdicts are licensed end to end by its accounted record well.
route-licence-transport: A licence whose cited occurrences survive a record transition, with the issuing event still authorized and the settlement extended compatibly, is a licence after it, and a licence whose cited occurrence is defeated is not. — item 115
route-licence-authorization-from-account: What authorizes a record event is read off the accounted obligation state, so that the authorized-event clause of a licence is derived from the record rather than declared beside it. — item 56
```

## 10. What the site does not yet do

The intake verbs (filing a want, a challenge or an attribution from a page); the chatbot; pages that do more than hold the remaining 164 held results under their programmes (the bridge card shows them as *connected to no informal claim yet*); the second maintainer's lines beyond rendering them as filed; the custom domain; the deployed site itself, which waits on #131 and this merge (the `site` artifact of a CI run is the preview).

## 11. Reserved to the maintainers

Appended to `DECISIONS.md` *Awaiting the author*, each with its *turns on* line: the walk's prose and whether its structure is right; the five bridges' rewritten Statements and the hypotheses' tags; the informal claims the round filed where none existed; the site's custom domain; what the walk found the map lacked.

## 12. Merge order

#131 first (`round/2026-10-22-map-as-canonical`, a squash is recommended there), then this pull request, whose base is that branch; after both, the `derived` and `site` workflows run for the first time on `main`.
