# Report — cleanup and compress

**Attribution.** Prompt author: Claude Fable 5 (Anthropic). Executor: Claude
Opus 5 (Anthropic). Dispatched and executed 2026-08-24. Branch
`round/2026-08-24-cleanup-and-compress`, cut from `main` at `0586da3`, in an
isolated worktree.

**Verdict.** The live documents say what is current, the deference line has a
registry, and two friction entries close as gates. `PRIORITIES.md` lands at 1,686
lines rather than under 800, and §8 gives the arithmetic for why the target is
not reachable while items stay dispatchable.

## 1. `PRIORITIES.md`, per section and per item

| section | before | after |
|---|---:|---:|
| preamble | 32 | 32 |
| Where ingenuity is the bottleneck | 172 | 121 |
| Normativity line | 106 | 103 |
| Normativity line — the learning track | 186 | 157 |
| Normativity line — traderized enforcement | 467 | 340 |
| Normativity line — legitimacy | 176 | 176 |
| Deference line | 95 | 90 |
| Deference line — first research wave | 208 | 208 |
| Deference line — second wave | 351 | 279 |
| Workspace friction | 143 | 93 |
| Infrastructure | 149 | 87 |
| **total** | **2,085** | **1,686** |

Sixty-nine items throughout; `workspace_state --check` counts them, and every
`answers_item` in both registries resolves. Seven items collapsed under R2,
twenty-nine were trimmed under R3, and thirty-three were already at the floor and
are untouched.

**Collapsed (R2)** — title, status, pointer; the body is in the record named.

| item | before → after | record now holding the body |
|---|---:|---|
| 29. Φ-regret reduction | 30 → 11 | `projects/normativity/rounds/2026-08-11-phi-regret-bridge/` |
| 48. computable belief sequence | 24 → 11 | `.../2026-08-18-projection-enforcement/FINAL_FORMALIZATION_STATUS.md` |
| 50. piecewise-affine facts | 26 → 12 | `.../2026-08-18-maxmin-representation/README.md` |
| 21. signed versus magnitude | 32 → 12 | `prompts/2026-08-11-phase-ii-prediction/REPORT.md` §1 |
| 36. wiki source synced outward | 23 → 12 | `prompts/2026-08-16-wiki-in-repo-sync/REPORT.md` |
| 37. volatile quantities | 34 → 12 | `prompts/2026-08-16-wiki-state-bindings/REPORT.md` |
| 38. write-scope enforcement | 37 → 12 | `prompts/2026-08-16-wiki-in-repo-sync/REPORT.md` |

**Trimmed to a stub, though the arithmetic calls them trimmed rather than
collapsed** — 41 (40 → 13), 47 (36 → 13), 60 (37 → 13), 23 (30 → 14), 13 (19 →
12), 28 (68 → 18), 51 (38 → 28). Each names the round record and, where the round
registered, the claim identifiers.

**The largest trims**, all under R3: Q3 (102 → 51), 39 (72 → 48), 34 (73 → 71),
30 (70 → 67), 52 (48 → 46), 46 (47 → 44), 24 (44 → 41), 25 (44 → 42), 27 (42 →
39), 40 (37 → 34), 42 (38 → 36).

**Untouched (33 items)**: Q1, Q2, Q4, 2, 4, 5, 6, 8, 9, 10, 11, 14, 15, 16, 17,
18, 19, 20, 22, 35, 49, 53, 54, 55, 56, 57, 58, 59, F1–F5. Each was already at or
near the floor for a dispatchable item.

**Q3 was reread against the queue**, as the dispatch asks. Its adjudication of the
three candidate objects is now the queue entry's, and the item keeps the question,
what killed each candidate, and what a good answer must carry. Its third candidate
is now registered as `corrective.*` and filed as item 60, which the entry says.

*Where ingenuity is the bottleneck* is otherwise not compressed.

## 2. Wiki status blocks, before and after

| page | before | after |
|---|---|---|
| `Deference.md` | "**Open / unregistered research.** The line has finite witnesses, conditional interfaces, Lean contributions, and adversarial audits, but the modern claims registry contains no substantive deference claim." | "**Paused.** The line is not being worked…" plus "**Established — `lean-proved`.** The 31 entries in this line's registry…", the impossibilities named as companion findings, and the two decisions the pause is on |
| `Corrigibility.md` | "**Open / unregistered research.** The exact reachable-control verdict is `Dynamics-positive, protection-incomplete.`" | "**Established — `lean-proved`, and mostly negative.**" plus "**Paused.** This is part of the deference line…" |
| `Home.md` | "The substantive results discussed here are currently unregistered." | both lines' registered results named; "**Deference is paused** on two decisions; normativity is where the work is"; a **Paused** entry added to *How to read status* |
| `Normativity.md` | count bound to `counts.registered_claims` | rebound to `counts.registered_claims_by_project.normativity`, because the total moved when a second line got a registry |
| `Legitimacy.md` | three components uncovered | a new section covering the reason state, transition certificates and certified interactive service — one paragraph each, what it fixes, what it consumes, its status as a living note |
| `Normative-Record-and-Inquiry.md` | "this page keeps `R` for the record until the naming is ruled on" | `𝓡_n` for the reason state and `N_{≤n}` for the record, applied through the page |
| `Roadmap.md` | 12 unattributed directions | open items only, each pointing at its priority number, in three sections with deference marked paused |
| `Relation-to-the-Field.md` | absent | a stub saying it is the maintainer's to write, linked from the sidebar |

`wiki/Architecture.md` needed no change: its status block already reads
`Open / unregistered` about the abstract theorem and dynamics, which is still
true. No wiki page says the deference line is active.

## 3. `README.md` and `CONTRIBUTING.md`

| file | before | after |
|---|---|---|
| `README.md` layout | five entries; `state/` and `wiki/` absent | seven entries; both added, and `projects/` notes that each line has its own `CLAIMS.md` |
| `README.md` verify block | three commands | five; the registry checker and the state check added, and `tests/run.py` described as running every gate's self-test |
| `README.md` pointers | six documents listed | plus one paragraph: normativity is where the work is, deference is paused |
| `CONTRIBUTING.md` local commands | 13 commands | 14; `tests/dead_pointers.py` added |
| `CONTRIBUTING.md` | (unchanged) "Five gates read a diff or a pull-request payload…" | verified still true: seven required jobs, five with local forms |

"Seven gates" and "Seven jobs decide correctness" were checked against
`.github/branch-protection.json` and are still exact. No section was added to
either file.

## 4. The deference registry

Thirty-one entries in `projects/deference/CLAIMS.md`, all `kind: lean`, class
`lean-proved`. Every declaration was confirmed to carry a `#print axioms` line.

| group | entries | `answers_item` |
|---|---:|---|
| delegation bridge and corollaries | 3 | 23 |
| certificate bounds | 6 | 23 |
| exposure geometry | 3 | 23 |
| substitution separation | 4 | 23 |
| magnitude prediction | 7 | 21 |
| static-view factorization | 2 | 28 |
| reachable corrective control | 6 | 60 (filed here) |

**Left out, and why** — the registry's own header says this, so a reader meets it
where the claims are:

- `FaithfulAcceleration.weight_not_divergent` and
  `MagnitudePrediction.squaredError_bdd_of_sharpness_bdd` ship no term inhabiting
  their full hypothesis package, each carrying an undischarged
  `EfficientlyComputable` certificate. `AGENTS.md`'s Lean regime forbids promoting
  them.
- The inherited transcriptions in `InheritedAlgebra.lean` and the Layer-1 half of
  `FaithfulAcceleration.lean` restate another body of work's declarations. That
  they re-elaborate here is a result about the port; it is not this repository
  establishing them.
- `EnvelopeDominance.lean` proves what its name says and not what its round
  wanted: its maximiser is built from the evaluating agent's own credence, so it
  represents no distinct future agent, and its dominance statement is
  `sum of maxima >= sum of anything`. The round records this as its central defect.
- `CartesianFrameBridge.lean` states its results over a mirrored fragment of an
  upstream library at a commit the repository does not pin, under an `Iso` weaker
  than the authoritative one. Item 52 is to import the real definitions and delete
  the mirror; registration belongs after that.

The reachable-corrective-control **refutations are registered**. A theorem that
breaks its own round's protection claims is a result, and the strongest thing that
round produced.

`checkers/workspace_state.py`'s "expected exactly one authoritative CLAIMS.md"
became "one registry per active project, and at least one", since the old form
encoded a fact about the workspace rather than a rule about it.

## 5. `depends_on` from prompts

**Nothing was filled, and that is the finding.** All eleven silent rounds'
dispatches name reading lists — "Read at minimum", "At minimum read closely",
"Primary current evidence", "read the source artifacts below" — or a base-branch
commit identifier. None states that the round *builds on* another round's result,
which is what R5 asks for and what would distinguish a dependency from an
orientation. Under "still no inference", each stays `[]`:

`2026-08-11-phi-regret-prep`, `2026-08-11-stage-iii-fud`,
`2026-08-11-stage-v-li-native`, `2026-08-12-cartesian-frames`,
`2026-08-12-corpus-reconciliation`, `2026-08-12-legitimacy-reorganization`,
`2026-08-13-relational-scorekeeping-bridge`,
`2026-08-13-crown-jewel-learning-theorem`, `2026-08-16-traderized-enforcement`,
`2026-08-17-counterfactual-legitimacy`, `2026-08-23-reason-representation`.

`depends_on_source` is implemented and accepted — `report` or `prompt`, and a
source set against an empty list fails — with three self-test cases. No round
record carries it. It is ready for the first dispatch that declares what it
consumes rather than what it should read.

`rests_on` re-emitted unchanged: fifteen rounds carry a non-empty transitive set,
the deepest being the certified-interactive-service round on ten.

## 6. The naming audit sheet

`state/views/NAMING_AUDIT.md`, generated by
`checkers.workspace_state --write-handoff` so it stays fresh and `--check` fails
when it is stale.

| line | rows | Lean only |
|---|---:|---:|
| deference | 207 | 126 |
| normativity | 369 | 314 |
| **total** | **576** | **440** |

Rows are vocabulary-bearing Lean identifiers — `def`, `structure`, `inductive`,
`abbrev`, `class` — plus every registered declaration, which is the set whose
renaming is a registry diff. Theorem names that are not statements of record are
out: a theorem name describes a statement and is cheap to change, while a
definition names an object other files must spell. Propagation is matched on a
backticked, word-bounded occurrence, after a substring match reported `Hom` as
having reached the wiki because there is a page called Home.

No recommendation appears in the sheet, and this round ruled on no name.

## 7. The dead-pointer gate

`tests/dead_pointers.py`, wired into `ci.yml` and `tests/run.py`; `GATE COVERAGE`
now reports eleven gate scripts. Fifteen self-test cases, four of them the null
inputs: a citation that does not resolve fails, a citation into a disposable tree
whose section does not say so fails, and both directions pass where they should.

**Seven repairs**, every one a real defect:

| document | citation | what it was |
|---|---|---|
| `PRIORITIES.md` | `tests/test_coherence.py` | round-relative, written as if rooted |
| `PRIORITIES.md` | `wiki/delay-and-visibility.md` | inside a note-dump tree, missing its prefix |
| `PRIORITIES.md` | `.../note-dump-2026-06-27/lean/LeanDeference.lean` | a superseded tree cited with no flag |
| `PROVENANCE.md` | `tests/test_regressions.py`, `tests/test_semantics.py`, `tests/test_budgeter.py` | round-relative, written as if rooted |
| `PROVENANCE.md` | `tests/test_live_worlds.py` | **deleted at `61df8af`**, its content folded into `test_semantics.py` |
| `PROVENANCE.md`, `DECISIONS.md` | `tests/check_frozen.py` | deleted; wrapped `<!--historical-->` |
| `.../GENERALIZED_LI_PAPER_HANDOFF.md` | `tests/test_coherence.py` | round-relative, written as if rooted |

The gate reports what it skips rather than hiding it: 329 rooted paths checked, 44
unrooted and 48 globs declared out of scope, 5 historical spans and 5 ledger
citations exempt. Globs are not checked because a glob in the specification list
is a pattern rather than a pointer — `projects/*/THEOREMS.md` protects a shape
with no instance today, and failing it would punish the enumeration for being
prospective. `DECISIONS.md` is exempt from the declared-tree half only:
*no negative ontologies* names the ledger one of two places history is kept, so
asking it to annotate history inverts its job. Its pointers must still resolve.

`.gitignore` gains `.claude/`. The friction section keeps all five entries, with
F2, F4 and F5 collapsed to closed stubs naming what closed them.

## 8. Deviations

1. **`PRIORITIES.md` is 1,686 lines, not under 800.** The target is not reachable
   while items stay dispatchable, and the arithmetic is not close. `AGENTS.md`'s
   demand-gating requires each item to be "a self-contained round specification an
   arbitrary agent could execute: precise statement; deliverable shape; the
   acceptance check; a context pointer; a difficulty tag." A minimal item carrying
   those is a heading, a metadata comment, a four-to-six-line statement and three
   labelled fields — about fourteen lines. Sixty-nine of those is 966 lines,
   before the 32-line preamble, the 121-line ingenuity section the dispatch
   excludes from compression, and ten section introductions. The floor is roughly
   1,150. Reaching 800 would mean cutting statements to three lines and dropping
   the fields that make an item executable, which trades a binding standard for a
   line count. I compressed to 1,686 and stopped; the remaining 500 lines above
   the floor are in the thirty-three untouched items and the eleven long trims,
   and are statements rather than history.

2. **The dispatch's "settlement decision (the trilemma — pointwise, classwise, or
   weakened target)" does not exist in the tree.** No file in `projects/deference/`
   contains "trilemma" or "weakened target", and no round posed a decision under
   that name; the pointwise/classwise distinction is real and lives in the source
   corpus, where the hard-selector pointwise route is refuted and a classwise,
   domain-relative route is what survives. The Deference page therefore says the
   line is paused on what is verifiably true: the two decisions in `DECISIONS.md`'s
   *Awaiting the author* — Q3's graduation with item 28's successor, and whether
   endpoint-preservation is a target — with the route question named as live items
   14 and 34.

3. **`PRIORITIES.md` has 69 items, not 68.** Item 60 was filed under WP4, which
   asks for "a new filed item where the report answers a demand no item states".
   The acceptance's 68 counts the state before that filing.

4. **My own compression pass swallowed two section headers, and I caught it after
   committing.** Collapsing an item replaced everything from its heading to the
   next item heading; where the collapsed item was last in its section, that span
   included the following `## ` header and its introduction, so the legitimacy and
   infrastructure sections lost theirs. Both are restored verbatim, and an audit
   against the pre-compression file now confirms all ten sections, all sixty-nine
   item headings and all sixty-nine metadata comments survive. The audit is the
   part that should have run first.

5. **`counts.registered_claims` gained a per-project sibling.** The
   `wiki_state_bindings` gate failed the moment the deference registry landed,
   because `Normativity.md` bound a total that had just moved under it. That is
   the binding working; the fix is `counts.registered_claims_by_project`, which is
   what a line's own page should have been binding.

6. **No round record, memo or report was edited**, per the non-goals.
   `git diff --name-only` against `main` shows nothing under `prompts/*/` or
   `*/rounds/*/`; `projects/normativity/notes/` changed for one pointer repair,
   which is a note rather than a round record.

## 9. What this does not establish

**Compression moved content and established nothing.** Every line this round cut
from `PRIORITIES.md` is either in the round record the collapsed item names, or is
rationale about an item rather than the item. No item became truer, no claim
changed class, and the file being shorter is a fact about reading cost. The one
thing compression can destroy is content that exists nowhere else, and §8.4 is the
near miss — a mechanical pass that silently removed two section headers and passed
every gate, because no gate reads `PRIORITIES.md` for structure.

**The deference registry asserts kernel checks, not that these are the theorems
wanted.** Thirty-one entries say the Lean kernel checked those statements against
those proofs. They do not say the statements are the right ones, and for this line
that gap is unusually wide: the strongest entries are *refutations* of what their
round set out to show, and the line is paused precisely because nobody has decided
what it should be proving instead. Registering a result and wanting it are
different acts, and only the first has happened.

**`depends_on` from prompts is a reading of dispatches, and there was none to
make.** Had a dispatch named a consumed round, the field would record what the
round was *told* to build on, not what its executor in fact used — a weaker fact
than a report's own statement, which is why `depends_on_source` distinguishes
them. As it stands the mechanism is untested against a real case, and the eleven
empty entries are empty for the same reason they were before: the reports are
silent, and the dispatches turn out to be silent too.

**The dead-pointer gate checks resolution, not correctness.** A pointer that
resolves may still name a document that no longer says what the citing sentence
claims — the case the corpus-reconciliation round paid by hand, where four of
seven pointers were byte-identical and one had materially changed. The gate
catches the tree-level version of that through the declared-tree half, and it
cannot catch the sentence-level one. Its skipped counts are printed for the same
reason: 44 unrooted citations and 48 globs are unadjudicated, and a reader should
be able to see that rather than infer coverage from a green line.

**The naming sheet is an inventory, not an analysis.** It says where each name is
and how far it has spread; it does not say which are bad, which collide, or which
a paper would have to rename. The dispatch's "alternatives that round listed if
any" column is absent, because the alternatives live in completed rounds' prose
and the sheet is generated from the tree — recovering them would mean parsing
twenty rounds' reports for free text, which is the kind of prose-reading this
repository avoids.
