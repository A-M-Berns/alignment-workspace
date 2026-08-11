# PRIORITIES rename and slop discipline — report

Dispatch: `PROMPT.md` beside this file, verbatim.

Stacked on `prompts/2026-08-11-attribution-provenance-names/`, which was open when
this round was dispatched and touches the same four documents. Line counts below
therefore distinguish the dispatch's baseline at `917c7da` from the state this
round actually started from.

## Outstanding maintainer actions

1. **Decide whether `## PRIORITIES item answered` should stay a template field
   name.** It is prose, not parsed — no script reads it — so it is free to change,
   but it is the field contributors fill in and renaming it twice is worse than
   renaming it once.
2. Carried from the previous round and still open: the scrub-round-2 dispatch and
   the contributor-checkers dispatch are both missing from `prompts/`, and whether
   the program gets a name is reserved.

## A. The rename

`git mv OPEN_PROBLEMS.md PRIORITIES.md`. Fifteen live references in eleven files:

| file | references |
|---|---|
| `checkers/registry.py` | the module docstring, the path lookup, the failure message |
| `checkers/run.py` | the self-test's temporary-tree fixture |
| `tests/path_gate.py` | the specification-path list |
| `.github/PULL_REQUEST_TEMPLATE.md` | the section heading and its comment |
| `AGENTS.md` | the specification-layer enumeration, the demand-gating rule, the gate table |
| `CONTRIBUTING.md` | the demand-gating rule, "where to find work" |
| `README.md` | the layout description, the contributing pointer |
| `GOVERNANCE_REPORT.md` | the demand-gating line, the specification-path listing |
| `PROVENANCE.md` | the table row |
| `SETUP_REPORT.md` | the item-count finding |
| `PRIORITIES.md` | its own heading and framing |

**Two references were deliberately not changed.** `PRIORITIES.md` line 32 and
`projects/leverage/README.md` line 40 both point at
`frozen/consolidation_aug9/OPEN_PROBLEMS.md` — the frozen tree's own list, which
is immutable and keeps its name. Renaming those would have produced two dangling
paths.

**Report references were changed, unlike the provenance vocabulary in the previous
round.** The distinction: a report saying "`OPEN_PROBLEMS.md` has eleven items" is
a path reference that dangles once the file moves, while a report saying its output
is `llm-unreviewed` is a statement of state at the time. Paths get updated so they
resolve; vocabulary statements stay as records.

### Framing

`# Open problems` → `# Priorities`, and the opening now says the file is the
maintainer's ranking of what would move the work rather than an inventory of what
is unsolved — so an item's absence means nobody has asked for it. Difficulty tags
unchanged. No stub, no redirect, no "formerly".

### The gate-exercise confirmation, and a bug the rename exposed

The dispatch asked for proof the gates exercise the renamed path rather than
passing on an empty match. They did not, and would not have:

```python
open_items = set()
if open_path.exists():
    open_items = set(re.findall(r"^###\s+(\d+)\.", ...))
...
if open_items and item and item not in open_items:
```

A missing file left `open_items` empty, and the guard then skipped the
answers-a-filed-item check on every claim while the gate reported green. The
rename would have silently disabled a check rather than breaking anything. Both a
missing file and an empty item set are now hard failures, and the check no longer
guards on the set being non-empty.

Two permanent self-test cases, taking the harness from 9 to 11:

```
ok: claim answering an unfiled priorities item is rejected
ok: missing PRIORITIES.md fails rather than skipping the check
```

The second is the one that matters — it fails if anyone reintroduces the skip.

Path gate, checked directly rather than inferred from a green run:

```
PRIORITIES.md          spec=True   proof=False
OPEN_PROBLEMS.md       spec=False  proof=False
```

The new name is in the specification set and the old one is in neither, which is
what a live rename should look like from the gate's side.

**One rename bug of my own, caught before commit.** Renaming the variable
`open_path` → `priorities` left two uses of the old name behind. Python would have
raised `NameError` on every registry run — loud, not silent, so CI would have
caught it — but it is the same class of error the dispatch warned about.

## B. Slop discipline

New `## Slop discipline` section in `AGENTS.md`, seven numbered rules as
dispatched, with the rationale first so the rule does not read as taste. Rule 6
cross-references §9 rather than restating it, per the dispatch. Agent reports are
named as deliverables under the rule.

`CONTRIBUTING.md` gains a `## Prose` section: the short form, the reason it is not
style policing, and that a padded pull request can be rejected on that ground. The
`## Review` list gains "prose".

## C. The application pass

| file | at `917c7da` | entering §C | after §C |
|---|---|---|---|
| `README.md` | 92 | 94 | 92 |
| `CONTRIBUTING.md` | 207 | 218 | 223 |
| `AGENTS.md` | 494 | 556 | 565 |
| `PRIORITIES.md` | 240 | 242 | 240 |

**The pass net-added lines, and that is the honest result.** Reading these four
documents against §B turned up less padding than it turned up factual defects, and
correcting a stale table costs more lines than deleting a restatement saves. The
cuts and the corrections are listed separately below so the two are not confused.

### AGENTS.md — cut

- **The doubled `---` before *No negative ontologies*.** Structural residue of an
  insertion.
- **`### 9b`.** A section number with a letter is a visible amendment marker.
  Renumbered 9b→10 and 10–12→11–13, with the four cross-references updated
  (`§12`→`§13`, `§13`→`§14`, and the gate table's write-scope row).
- **The contrib-checker asymmetry, stated then restated.** "That asymmetry is why
  one is gated and the other is merely labelled" repeated the preceding paragraph;
  cut, keeping the sentence after it, which is new content.
- **The Lean regime's opener**, which restated standard 4 in full before pointing
  at it. Now points at it.

### AGENTS.md — corrected, not cut

- **The gate table was wrong.** It listed four numbered gates and closed with "Six
  gated standards decide correctness" while CI runs eight jobs. Nine rows added:
  path-gate, conservativity, the registry and the `contributor-checked` ceiling,
  contrib hygiene, DCO, model attribution, the name lint, reserved-items, and slop
  discipline. This is the document's map of what is enforced, and it had drifted
  from the workflow.
- **Numbered gate references retired.** "Gate 1/2/3" in standards 1, 4 and 5 named
  a numbering the table no longer uses. They now name the CI job, which is also
  what branch protection matches on.

### CONTRIBUTING.md

- **Corrected:** "Four gates run in CI and all four run locally" — there are
  eight. The local-run block listed five commands under the old gate numbers; it
  now lists all eight commands the jobs run, labelled by job, and says plainly
  which two gates have no local form (`dco` reads commit sign-offs; attribution
  reads a pull-request body that does not exist yet).
- **Cut:** one stray double blank line.
- **Otherwise unchanged, deliberately.** It is contributor-facing and restates
  `AGENTS.md` by design — that is the dual register, not duplication within a
  document. Nothing in it plainly violates §B.

### README.md

- **Cut:** "That is not a slogan about openness; it is what the house discipline
  is *for*" — a negated strawman ahead of the list that makes the point.
- **Corrected:** the `PROVENANCE.md` description still described the three-class
  scheme ("what was written by a person and what by a model, and which of the
  latter the author has reviewed"), superseded by generator + review status in the
  previous round.

### PRIORITIES.md

- **Cut:** the `## Infrastructure, continued` heading — padding structure, three
  items split from the section above it for no reason. Merged.
- Otherwise unchanged. The item bodies are dense and the framing was rewritten in
  §A.

### Where §B would have cost content — left in place

- **`CONTRIBUTING.md`'s "This is an invitation, not a consolation."** Reads as
  inflated register, but it is doing real work: it tells a contributor that
  `contributor-checked` is not a demerit, which the surrounding mechanics do not
  say.
- **`AGENTS.md`'s "Everything below follows from that."** A preview sentence by
  §B.1, and load-bearing: it is what makes the four-part premise binding on the
  rest rather than decorative.
- **The trust chain's closing "If you are auditing this repository, audit that
  list."** Restates the list's purpose. Kept — it is the one instruction an
  external auditor needs, and it is where they will look.
- **`README.md`'s two-line description of each research line.** Longer than
  strictly needed; it is the only place a stranger learns what the program is.
- **`CONTRIBUTING.md`'s restatement of the contrib-checker rules** at more length
  than `AGENTS.md` states them. Cross-document restatement for a different
  audience is the dual-register design.

### Not touched, and why

Field names and checkbox text in `CONTRIBUTING.md` and the pull-request template
were verified against the scripts before this pass: `tests/attribution.py` parses
`## Model attribution`, and nothing parses any other heading or checkbox in either
document. The attribution heading was left exactly as the parser expects.

## Gates

Green locally: name lint (37 files), attribution self-test (7/7), checkers
self-test (11/11), registries (3 entries), contrib hygiene, path gate,
conservativity, `check_frozen`, repo runner, `py_compile`. The Lean gate is
unaffected — this round touches no Lean — and runs in CI.

## Attribution

| | |
|---|---|
| prompt author | Claude Fable 5 (Anthropic) |
| executor | Claude Opus 5 (Anthropic) |
| date | 2026-08-11 |
