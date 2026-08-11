# Rename round — report

Three renames, landed as one state. All eight gates green locally; the §D
consistency grep is empty.

Dispatch: `PROMPT.md` beside this file, verbatim.

## Awaiting the maintainer

1. **The name `forward/`.** The dispatch proposed it and did not confirm it, so
   per AGENTS.md rule 6 it is implemented and flagged rather than settled. It is
   one `git mv`, one file rename, and six prose references to change. Recorded as
   a stub in `DECISIONS.md`.
2. **The GitHub-side repository rename** — see §A below for what was and was not
   done, and why.

## A. The repository

`alignment-workspace` throughout. Exactly five live files carried the old
repository name, in six places; all updated:

| file | what changed |
|---|---|
| `.github/apply-branch-protection.sh` | the default `REPO` slug |
| `SETUP_REPORT.md` | the documented `gh api` branch-protection path |
| `README.md` | the title |
| `LICENSE` | the Apache-2.0 appendix copyright line — "the alignment-workspace contributors" |
| `DECISIONS.md` | the name-and-scope entry, and the licence entry's statement of that copyright wording |

The other files the dispatch's pointer list mentions carried the *library* name
rather than the repository name; they are itemised under §B.

**The GitHub-side rename is done separately from this branch** — it is a
repository-settings change, not a commit, and it is recorded at the end of this
report rather than inferred from the diff. The token in this session does carry
`repo` scope and admin on the repository, so it is not blocked for lack of
access; the dispatch reserves it only "if you lack settings scope."

GitHub's redirect from the previous path keeps existing clones, links, and the
`origin` remote working, so the file changes above are correct before and after
the settings change.

### One tension in the dispatch, resolved toward §D

§A says "the DECISIONS.md entry for this rename is where the change is
recorded," and §D says no live document may contain the old string in any
casing. A ledger entry that spelled out the previous name would satisfy the
first and fail the second.

Resolved toward §D, following the precedent set by the deference rename's own
ledger entry, which records that rename without naming what preceded it. The new
entry states the names as they now stand, says the previous names live in
`prompts/` and in git history, and does not reproduce them. Surfaced here rather
than decided silently.

## B. The Lean library and namespaces

`Workstudio` → `Workspace`. Moved with `git mv`, so the history follows:

- `lean/Workstudio.lean` → `lean/Workspace.lean` (three `import` lines rewritten)
- `lean/Workstudio/` → `lean/Workspace/` — `Smoke.lean`, `Deference/Basic.lean`,
  `Leverage/Basic.lean`
- `lean/lakefile.toml` — package `name`, `defaultTargets`, and the `lean_lib`
  name (three occurrences)
- `lean/lake-manifest.json` — the root package name entry (one occurrence)

Namespaces are now `Workspace.Smoke`, `Workspace.Leverage`,
`Workspace.Deference`, opened and closed in the three files.

Documents referencing the library or its namespaces:

| file | occurrences |
|---|---|
| `DECISIONS.md` | the one-Lake-project entry, the deference-naming entry, and the naming stub now closed (four) |
| `GOVERNANCE_REPORT.md` | four path and namespace references in the layer tables |
| `OPEN_PROBLEMS.md` | four deliverable-shape namespace pointers |
| `SETUP_REPORT.md` | two mentions in the author-pending list |
| `README.md` | the layout key |
| `PROVENANCE.md` | the `lean/Workspace/**` row's path glob |
| `projects/deference/README.md` | the directory pointer and the namespace |
| `projects/leverage/CLAIMS.md` | two `declaration` fields |

Scripts referencing the library path or the namespace prefix:

| file | occurrences |
|---|---|
| `tests/audit_axioms.py` | `LIB` |
| `tests/conservativity.py` | `LIB` |
| `tests/run.py` | the sorry gate, the axiom-discipline gate, the docstring, and the `WORKSTUDIO_LEAN` → `WORKSPACE_LEAN` environment variable (five) |
| `tests/path_gate.py` | four specification patterns and one proof pattern |
| `checkers/registry.py` | the Lean-declaration lookup directory |
| `checkers/run.py` | the self-test's temporary-tree fixture |

The last of these is not in the dispatch's pointer list: it arrives with the
contributor-checkers branch this round is stacked on (see *Deviations*).

### Clean build

`rm -rf lean/.lake/build`, then `lake build`: **13.4 s wall**, 1716 jobs,
completed successfully.

That number is the library's own rebuild with the dependency oleans intact under
`lean/.lake/packages` — 1710 of the 1716 jobs were replayed from cache and six
were actually built. It is not a from-scratch Mathlib build and should not be
read as one. Removing `.lake/packages` too would have rebuilt Mathlib and
Foundation, which measures the toolchain rather than this rename.

### The axiom audit still matches declarations

**6 results across 3 files**, all within `[propext, Classical.choice,
Quot.sound]`. The count is right: four `#print axioms` in `Smoke.lean`, one in
each namespace root. It agrees with what `lake build` printed independently —
the four `Workspace.Smoke.*` results, `Workspace.Deference.namespaceIsLive_holds`
and `Workspace.Leverage.namespaceIsLive_holds`, the latter two depending on no
axioms at all.

The dispatch's worry — a stale path prefix that matches nothing and looks like a
pass — is guarded twice in `audit_axioms.py`, and both guards were exercised
rather than read:

- An empty source list returns 1. Re-running the audit with `LIB` pointed at the
  old directory name gives `rc=1`, `AXIOM AUDIT: no Lean sources found`.
- A file whose `#print axioms` lines name declarations that do not exist reports
  nothing and is failed per-file, so a namespace rename that missed a file could
  not pass either.

## C. The leverage forward tree

`projects/leverage/workspace/` → `projects/leverage/forward/`, and
`WORKSPACE.md` → `FORWARD.md`. 58 files moved by `git mv`; contents unchanged
except for the references below.

References updated:

| file | what changed |
|---|---|
| `projects/leverage/README.md` | the section describing the tree, and the `cd forward && python3 tests/run.py` invocation |
| `PROVENANCE.md` | the `projects/leverage/forward/**` row |
| `forward/FORWARD.md` | title, and "disposable forward tree" |
| `forward/tests/run.py` | module docstring, the pointer to `FORWARD.md`, the `documents()` docstring, and the terminal `FORWARD GREEN` line |
| `forward/CONSOLIDATION_REF.md` | two prose references to the tree |
| `forward/CONVENTIONS.md` | the status-vocabulary sentence |

Prose that used *workspace* as a common noun for this tree now says *tree* or
*forward tree*, so the word is not doing double duty one directory below a
repository that owns it. `CONSOLIDATION_REF.md`'s pin and the frozen tree it
names are untouched, as instructed; the frozen digests re-verify.

**The repo-level runner needed no change.** It discovers project suites by
`rglob("tests/run.py")` under `projects/`, so the rename is invisible to it; it
now reports `PASS projects/leverage/forward`. The forward tree's own
retired-vocabulary gate re-ran over the renamed documents and is clean — worth
noting because `round` is a retired word there, so a carelessly worded rename
would have failed that gate.

## D. Consistency check

```
$ git grep -rIn -i -e workstudio -- . ':!prompts' ':!frozen'
$ echo $?
1
```

Empty. Repeated over the whole worktree including untracked files, excluding
only `.git`, `.lake`, `prompts/` and `frozen/`:

```
$ grep -rIl -i workstudio . --exclude-dir=.git --exclude-dir=.lake \
      --exclude-dir=prompts --exclude-dir=frozen
$ echo $?
1
```

Also empty. The name survives in `prompts/` (six files, history, kept verbatim
by convention) and nowhere else outside git history.

## Gates

All run locally at the tip of this branch:

| gate | result |
|---|---|
| `path_gate.py` | 29 specification patterns, 4 proof patterns, classification clean |
| `dco.py` | no PR context locally; sign-offs present on every commit |
| `checkers.run --self-test` | 9/9 |
| `contrib_hygiene.py` | 0 contributor checkers, clean |
| `checkers.run` | 3 registry entries, 1 adjudicated locally, schema ok |
| `conservativity.py` | 3 specification files, no axioms, shape unchanged |
| `tests/run.py` | all green, 1 project |
| `lake build` + `audit_axioms.py` | green; 6 results, 3 files |
| `check_frozen.py` | 4 registered inputs verified |

## Deviations, and things found on the way

1. **Stacked on `feat/contributor-checkers` (PR #3), not on `main`.** That
   branch is open, green, and touches `checkers/registry.py`,
   `checkers/run.py`, `tests/path_gate.py` and `tests/run.py` — four of the
   files this rename edits, and it introduces a fifth `Workstudio` reference in
   `checkers/run.py` that is not in the dispatch's pointer list. Basing on `main`
   would have produced conflicts and, worse, a §D grep that passes now and fails
   the moment #3 merges. This PR therefore targets `feat/contributor-checkers`;
   GitHub retargets it to `main` when #3 merges. **Merge order: #3, then this.**
   PR #2 (`scrub/round-2`) touches only `SCRUB_REPORT.md` and `frozen/**` and is
   disjoint from both — any order.

2. **Two stale stubs in `DECISIONS.md`, one closed and one removed.** The Lean
   naming stub is closed by this round, as intended. The other — "Repository
   visibility and license … currently **private** … No license file is present"
   — was already false: both were settled on 2026-08-11 in entries a few lines
   below it. Removed. Out of this round's scope, flagged rather than folded in
   silently; revert it if the stub was serving a purpose that is not visible from
   the text.

3. **`prompts/2026-08-11-contributor-checkers/` has no `PROMPT.md`.** Every other
   round directory has one, and `prompts/README.md` says a round whose prompt is
   not in the tree did not happen as far as the repository is concerned. Not
   fixed here: the verbatim text is not reconstructable from this session, and
   the directory belongs to an open PR. It needs the maintainer to paste the
   dispatch.

4. **`lean/Workspace.lean` records as delete-plus-add rather than a rename.** All
   three of its lines changed, which is below git's rename-similarity threshold.
   The file's history is reachable through `--follow`; nothing is lost.
