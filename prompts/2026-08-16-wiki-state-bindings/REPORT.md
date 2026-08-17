# Report — volatile quantities in the wiki are declared and checked

**Prompt author:** Claude Fable 5 (Anthropic). **Executor:** Claude Opus 5
(Anthropic). **Dispatched and executed:** 2026-08-16, rev 2 after the first
dispatch stopped on its precondition. Write scope granted by the dispatch.

## Precondition

Satisfied on the re-send. `origin/main` is `d1ec1d6`, carrying `wiki/` and
`checkers/wiki_links.py`. The first dispatch stopped because neither was on
`main`; that report is this directory's predecessor, and the two facts it
surfaced — `--json` already present, and the emission's sections being flat
lists — are what rev 2 settled.

## What is installed

`checkers/wiki_state_bindings.py` verifies every declaration in `wiki/*.md`
against `checkers/workspace_state.py --json`, scans undeclared text for four
denylisted forms, and enforces marker hygiene. `checkers/workspace_state.py`
grows a derived `counts` section holding exactly the one aggregate a page binds.
Two statements in the wiki are annotated. `wiki/CONVENTIONS.md` states the
grammar. The gate runs in the `checkers` job, whose required-check identity is
unchanged, so `.github/branch-protection.json` is untouched.

## Discovery, and the annotation

The discovery half ran before the emitter was touched, as the dispatch requires.
Over the fourteen pages, two volatile quantities exist and nothing else does:

| page | statement | disposition |
|---|---|---|
| `Architecture.md` | `PR #31 registered no workspace claim` | `historical` — a past event |
| `Normativity.md` | `180-claim foundation` | bound to `workspace:counts.foundation_claims` |

**Unbindable: empty.** No statement was volatile with no corresponding emitter
value, so no `<!--TODO:unbindable-->` comment was written and no
emitter-extension item was filed. `counts` therefore has exactly one key.

Note what the second row shows about the design. `180-claim` is singular and
hyphenated, so the denylist pattern for claim counts does not match it — the
denylist would have let it through. It was found and bound because the
annotation pass reads the pages, and it is checked from now on because the
author declared it. That is the inversion working as intended: **the denylist is
a backstop, and the declaration is the mechanism.**

The prose is unchanged. Every page is word-for-word identical to `origin/main`
once markers and blockquote prefixes are stripped, verified mechanically rather
than by reading the diff. Inserting a marker into a wrapped paragraph moves line
breaks; `Architecture.md`'s blockquote was re-wrapped to its existing width for
that reason and for no other.

## Verification

Full local suite green. `checkers/wiki_state_bindings.py --self-test` carries 29
cases. The six the dispatch names each fail on a crafted fixture:

| fixture | failure |
|---|---|
| mismatched binding | `bound value '179' but workspace:counts.foundation_claims is '180'` |
| dangling path | `path 'counts.no_such_key' does not resolve` |
| malformed marker | `malformed marker '<!--state:workspace-->'` |
| unmarked denylist hit | `'PR #31' is a pull-request number and is not declared` |
| nested marker | `state marker opens inside an unclosed historical marker` |
| oversized historical span | `historical span covers 4 lines … maximum 3` |

Beside them: unclosed marker, empty value, unknown emission, stray closing
marker, each denylist pattern individually, and the exemptions — fenced blocks,
code spans, and text inside a historical span.

Three null inputs, each refused by `run` rather than passing: no pages; an empty
emission; and **a wiki with no bindings at all**, which is the quiet one. With
no declarations, pass 1 verifies nothing and the run reports green off the
denylist alone — the same shape as a gate that has stopped matching. A live case
pins that the current wiki has at least one binding, so the pass is not vacuous.

## Choices the dispatch left open

**`FILE` names the emission, not a section within it.** The dispatch says `FILE`
names an emission section, and its two examples both write `workspace:` with the
section as the path's first segment. The examples govern: `workspace` names
`checkers/workspace_state.py --json`, and `sources()` is the registry an
unknown `FILE` is reported against. The introspection requirement is met where it
varies — `--sections` lists the emission's sections, and a path that fails to
resolve prints them.

**Dotted paths index lists by integer position.** Without it, `counts` would be
the only reachable section and the other seven would be dead. Indexing addresses,
it does not derive, so it does not touch the settled rule that aggregation lives
in the emitter.

**Fenced blocks and code spans are skipped in every pass**, matching
`checkers/wiki_links.py`. `wiki/CONVENTIONS.md` documents the grammar by showing
it, and a checker that read its own documentation as a declaration would be one
every author had to work around.

**`counts.foundation_claims` totals every foundation claim source.** One source
exists, so the total is its count. A second source would change the number and
fail the binding, which is a false positive on a sentence about the first
foundation — loud in the safe direction, and preferable to keying by foundation
id, since the id contains a dot and a dotted path cannot address it.

## Deviations

1. **Two ledger entries and five provenance rows were restored, which the
   dispatch did not scope.** The wiki-in-repo round's `DECISIONS.md` entries and
   `PROVENANCE.md` rows are absent from `main` while everything else that round
   wrote arrived — `AGENTS.md` carries the amended *Security* section,
   `tests/workflow_scope.py` enforces it, item 38 is filed, and that round's own
   *Awaiting the author* stub, in the same file, survived. So `main` states a
   constitutional rule whose decision the ledger does not record, and three
   trust-chain files have no provenance row. All seven were recovered verbatim
   from the round's branch and are restored here. This is a record repair rather
   than a design change: the decisions are in force and visible in the tree, and
   `AGENTS.md` §14 repairs a dead pointer in place. The mechanism is filed as
   `PRIORITIES.md` F8.

2. **A friction entry was filed that the dispatch did not scope** — F8, above,
   under the §14 obligation. The dispatch says to file nothing new unless an
   unbindable statement forces it; that clause governs *priority items arising
   from the annotation pass*, and a structural defect found in the tree is filed
   under a standing rule the dispatch does not displace.

3. **`wiki/CONVENTIONS.md` and `wiki/ORIGIN.md` are scanned.** The dispatch says
   `wiki/*.md`; those two are repo-side only and never reach the hosted wiki, and
   excluding them would leave the file that documents the grammar unchecked
   against it.

4. **The gates table in `AGENTS.md` and the local-run block in
   `CONTRIBUTING.md` each gained a line**, neither named in the deliverables.
   Both enumerate what runs; a gate missing from either makes the document wrong.

## What this does not establish

- **Nothing decides which sentences are volatile.** That is the design, not a
  gap — but it means the guarantee is exactly "what an author declared is true,
  and four forms cannot appear undeclared." A volatile quantity written in a
  form outside those four, and not declared, passes. The `180-claim` case above
  is a live example of one the denylist would have missed.
- **The denylist is four patterns, seeded by what the wiki contains.** It is not
  a theory of which numbers rot.
- **`counts` has one key**, because one page binds one aggregate. Every other
  quantity the workspace could report is unreachable until something binds it.
- **A binding proves agreement, not correctness.** `180` matching the emission
  says the page agrees with `LEDGER.md`'s ID column, which is what
  `foundation_claim_count` counts. Whether that ledger is right is a different
  question and no gate here touches it.
- **The prose-identity check is mine, not a gate.** It ran once, in this round.
  Nothing stops a later change to `wiki/` from editing prose while inserting a
  marker.

## Filed

- `PRIORITIES.md` item 37 — marked answered by this round.
- `PRIORITIES.md` F8 — the merge that dropped a ledger entry and five provenance
  rows while every other file landed.
- `DECISIONS.md` — one dated entry for this round, plus the two restored.

Empty findings, reported as empty: the unbindable list is empty, and no page
carried a volatile quantity the emitter could not supply.

## Outstanding maintainer actions

1. **Confirm the restored entries and rows are wanted.** They are recovered
   verbatim, not rewritten, and the alternative reading — that they were dropped
   deliberately — would mean `main`'s *Security* section stands with no recorded
   decision behind it. If the drop was intentional, revert the restoration and
   say so in a dated entry.
2. **Rule on F8's two candidate fixes**, or neither: append dated entries beneath
   the last same-dated one rather than at the section head, so same-anchor edits
   become ordinary appends; and check that every round under `prompts/` has a
   provenance row and, where its report claims a dated entry, that the entry
   exists. Deciding it is choosing; waiting costs one silent loss per round that
   writes to a shared anchor while another pull request is open.
3. **Decide the identity a wiki pull request is opened under** — still in
   `DECISIONS.md`, *Awaiting the author*, carried from the previous round and
   untouched here.
