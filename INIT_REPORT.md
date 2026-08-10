# Repository initialization report

## Repository

**https://github.com/A-M-Berns/normative-learning** — public.

Two top-level directories: `consolidation_aug9/` (the frozen package) and
`workspace/` (the reset tree).

## Commits

| # | SHA | subject |
|---|---|---|
| 1 | `133061470f4b1ab1752380cf0785a0516e4ed446` | The August 9 consolidation, as frozen |
| 2 | `39d02ec846bad33cf58a60afe06b5a536d34692c` | Fold in three review corrections |
| 3 | `65534efe13b6b5ca25839f43363efb7f398f5e76` | The reset workspace |
| 4 | `8caec795e5598b4231267fb362fa9917b387335d` | Root plumbing and CI |

## Tags

Both annotated.

```
freeze/aug9     August 9 consolidation, completing pass included, as frozen.
freeze/aug9-r2  Review corrections folded in; current authoritative freeze.
```

`freeze/aug9` → commit 1. `freeze/aug9-r2` → commit 2, **and is the authority.**

## Verification results

**Byte-identity at `freeze/aug9`.** A digest sweep compared every file of the
imported tree against the frozen archive: **59 substantive files, 59 matching
SHA-256 digests, no file missing, none extra, no content difference.** The
archive additionally contains nine `__pycache__` bytecode artifacts, excluded as
build products — that is the full scope of the difference, and it is the only
respect in which the import is not a literal copy of the archive.

**Commit 2 diff scope.** Exactly the three corrected documents plus the report
addendum, and nothing else:

```
consolidation_aug9/COMPLETING_PASS_REPORT.md | 19 +++++++++++++-
consolidation_aug9/DEVIATIONS_ANNEX.md       |  6 +++---
consolidation_aug9/VERIFICATION.md           | 16 ++++++++++++--
```

**Consolidation suite after the corrections.** Green. Retired-name gate clean
over every non-vendored document — which covers all three corrected files —
sorry scan clean, ledger coverage 180 claims with statuses agreeing between the
theory parts and the ledger, every claim-ID family expanded, 26 frozen inputs
verified, 107 tests passing.

**Workspace suite (Commit 3).** Green: **94 tests**, vocabulary gate clean over
the three live documents, Lean skipped as expected.

**CP6 sweep (Commit 3).** Searched every `.py`, `.md`, `.json` and `.lean` file
of the workspace for references to pre-consolidation history — the old
consolidation archives, the checksum manifest, the rename manifest, the
consolidation-locating variable, pinned digests. **30 hits, all 30 inside
`attic/`, zero outside.** CP6 confirmed. (The first run of this sweep used a
path filter that silently matched nothing, reporting all 30 as violations; the
result above is from the corrected sweep.)

## CI

One workflow, `.github/workflows/suites.yml`: two jobs on stock
`ubuntu-latest` + `python3`, running `python3 tests/run.py` in
`consolidation_aug9/` and in `workspace/`, on every push and pull request. Lean
self-skips without `MATHLIB_DIR`, which is expected.

**Status: green.** Run
[31419093674](https://github.com/A-M-Berns/normative-learning/actions/runs/31419093674),
triggered by the push of commit 4, both jobs passing in 6s each:

- `consolidation` — 107 tests, ledger coverage 180 claims with statuses
  agreeing, **26 frozen inputs verified**, all checks green.
- `workspace` — 94 tests, vocabulary gate clean over three live documents,
  workspace green.

One non-blocking annotation: the runner warns that `actions/checkout@v4`
targets a deprecated Node version and was forced onto a newer one. It does not
affect either job.

**The frozen-input check passing on the runner is worth its own line.** Those
are byte-level SHA-256 digests over the vendored archive and documents, and
they were verified against a fresh clone on Linux — so the `* -text` attribute
did what it was added for, and end-of-line translation is not silently
corrupting the package across machines.

## What this report does not claim

The two suites are green locally **and** on a clean Linux runner, which is
evidence about those suites and nothing more: a green suite certifies that the
package's own gates pass, not that any claim in it is true. The byte-identity check
covers content, not filesystem metadata. And the corrections of Commit 2 were
verified by rereading each realigned line against the status quoted in its own
entry — they are not machine-checked, because no gate in the package relates an
obstacle sentence to the status it describes.
