# Retire `frozen/`, adopt `agent-consolidated` — report

Dispatch: `PROMPT.md` beside this file, verbatim.

Based directly on `main` at `9e03a0e`, which carries the recovered priorities
round and the admin-cleanup round. One commit, no stack.

## Outstanding maintainer actions

1. **Merge this pull request; until it lands, nothing else can.** Branch
   protection was re-applied here (§B) and now requires
   `consolidation-verification`, a job that exists only on this branch. That is
   the sequencing the dispatch warned about, and it resolves the moment this
   merges. Any other branch opened before then will sit on six of seven checks.
2. **Consider moving `consolidation-verification` off every-push.** Proposed, not
   done, per the dispatch. It is a slow gate against an input that now changes
   only deliberately; a schedule plus runs on toolchain and CI changes would serve
   better. Doing it changes the required-check list again, so it is a separate
   deliberate act.
3. Carried: two missing dispatches (`scrub-round-2`, `contributor-checkers`), and
   the three stubs in `DECISIONS.md`.

## A. The move

Four `git mv`s, no byte changed:

| from | to |
|---|---|
| `frozen/consolidation_aug9/` | `projects/leverage/consolidation-aug9/` |
| `frozen/deference-note-dump-2026-06-27/` | `projects/deference/note-dump-2026-06-27/` |
| `frozen/dose-response-note-dump-2026-07-02/` | `projects/deference/dose-response-note-dump-2026-07-02/` |
| `frozen/references-citations-2026-08-11/` | `projects/deference/references-citations-2026-08-11/` |

**Verified rather than asserted.** Every tree's hash was recomputed after the move
against its registered intake digest, and all four matched:

```
consolidation-aug9                  a2ca95ad…  MATCH  (59 files)
note-dump-2026-06-27                722b687a…  MATCH  (41 files)
dose-response-note-dump-2026-07-02  d34afa3c…  MATCH  (13 files)
references-citations-2026-08-11     268fbdba…  MATCH  (1 file)
```

`frozen/MANIFEST.md`, `frozen/FROZEN_INPUT_CHECKSUMS.json` and
`tests/check_frozen.py` are gone; `frozen/` no longer exists.

### Reference updates

Exactly seventeen tracked files contained the literal `frozen/`, matching the
dispatch's count. Seven contained tree paths and were rewritten mechanically:
`.github/workflows/ci.yml`, `CONTRIBUTING.md`, `PRIORITIES.md` (12 references),
`PROVENANCE.md`, `SETUP_REPORT.md`, `projects/leverage/CLAIMS.md`,
`projects/leverage/README.md`.

The rest referred to the *concept* and were rewritten by hand: `AGENTS.md`
(standard 1 rewritten, plus the runner rule, the chat-bundle pointer, the bundle
intake path, the specification-layer list, and two rows of the enforcement
table), `CONTRIBUTING.md` (reader rule 4 and hard rule 1),
`README.md` (the layout key and the two hard rules), `PROVENANCE.md` (the row and
the chat-bundle note), `.github/PULL_REQUEST_TEMPLATE.md` (the provenance comment
and the "Frozen inputs" section, now "Consolidated trees"),
`GOVERNANCE_REPORT.md` (a path listing), `projects/deference/README.md`,
`projects/deference/notes/README.md`, `tests/path_gate.py`, `tests/name_lint.py`,
`tests/run.py`.

**Not rewritten, deliberately:** `DECISIONS.md:126` and three lines in
`SETUP_REPORT.md`. Both are records — the ledger entry describes the name lint as
it was written, and `SETUP_REPORT.md` describes a gate that existed when that
round ran. The ledger rule settled in the previous round says identifiers are
updated in place so the record keeps resolving, and everything else lands as a new
entry; these are not identifiers that need to resolve, they are statements about a
past state. Rewriting them would describe a world that did not exist when they
were written. Flagged rather than silently kept.

## B. Receipts, and the required-check list

Each tree has an `ORIGIN.md`: what it is, provenance and date, archive sha256,
tree sha256 at intake, file count, what cites it, and — for the note dumps — the
third-party redistribution resolution and both scrub rounds by date. Each says
plainly that it is a receipt and not a gate, and each records that the digest
**excludes `ORIGIN.md` itself**, which did not exist at intake — without that a
reader recomputing the hash would get a mismatch and misread it as drift.

Retired: `tests/check_frozen.py`, its self-test, and the `frozen-integrity` job.

### Before and after

| before (8) | after (7) |
|---|---|
| checkers — house harness self-test and the claims registries | same |
| conservativity — no new axioms, specification shape unchanged | same |
| dco — every commit carries a sign-off | same |
| **frozen-integrity — digests and the manifest rule** | **removed** |
| **foundations-verification — the frozen consolidation re-proves itself** | **consolidation-verification — the leverage consolidation re-proves itself** |
| lean — build, sorry-free, axiom audit | same |
| path-gate — proof-layer PRs may not touch the specification layer | same |
| python — project test runners | same |

Applied with `.github/apply-branch-protection.sh`, which reads back what GitHub
stored. Confirmed three ways — payload, workflow job names, and the live branch:

```sh
gh api repos/A-M-Berns/alignment-workspace/branches/main/protection \
  --jq '.required_status_checks.contexts[]'
```

```
payload 7   ci jobs 7   live 7
payload == ci jobs : True
payload == live    : True
```

Approvals 0, code-owner reviews off, enforce-for-admins on, force-pushes and
deletions blocked — all unchanged and re-verified.

## C. `agent-consolidated`

In `AGENTS.md` beside the epistemic classes and explicitly **not comparable with
them**: the classes say what is established, this says how a document is treated.
The definition is the dispatch's, plus a paragraph on the `ORIGIN.md` receipt and
where the protection now lives.

Contributor protection moved from a hash to a list: the four tree paths are in
`SPEC_PATHS` in `tests/path_gate.py`. **Exercised, not assumed:**

```
projects/leverage/consolidation-aug9/LEDGER.md        spec=True
projects/deference/note-dump-2026-06-27/x.md          spec=True
projects/leverage/forward/src/a.py                    spec=False
frozen/x.md                                           spec=False
```

The last line matters as much as the first two: the retired path is no longer
matched by anything, so the list does not carry a dead pattern.

Marked in each `ORIGIN.md` and in `PROVENANCE.md`.

## D. The self-verification job

Retargeted, renamed `consolidation-verification`, second step dropped, and the
run-from-a-copy pattern kept — with the reason restated, since it changed: the
tree is ordinary content now, so nothing stops a runner writing into it, which is
why the job does not give it the chance.

**One consequence the dispatch did not anticipate.** `tests/run.py` discovers
project suites by `rglob("tests/run.py")` under `projects/`, so moving the
consolidation into `projects/leverage/` means the repo runner now finds and runs
its verifier too — the `python` job reports `PASS projects/leverage/consolidation-aug9`.
It runs **in place** there, not from a copy. Checked rather than assumed: after a
full local run the tree recomputes to its intake digest exactly, so the verifier
writes nothing. It is duplicated work between two jobs, which is an argument for
the schedule change proposed above.

## E. Residue, and one rule left with a hole

No `frozen/` stub, no "formerly frozen" phrasing, no vocabulary presuming an
immutable tier. The word survives in `prompts/`, in `DECISIONS.md` and
`SETUP_REPORT.md` as history, inside the moved trees' own text — and as ordinary
domain vocabulary in the deference line, where "frozen deliberation" is a
technical term and has nothing to do with this.

**The hole.** Standard 1 used to be enforced by a gate that could not be argued
with; it is now enforced by a list plus review. Against a contributor that is
equivalent — the path gate refuses them either way. Against **a maintainer, or a
maintainer-dispatched agent**, it is strictly weaker: nothing now detects a
consolidated tree being edited except a human reading the diff. The dispatch
argues this is the right trade, and the argument holds for the failure it names.
It is worth being explicit that the residual exposure is agents acting under
maintainer authority — which is most of the activity in this repository — and
that the mitigation is entirely `ORIGIN.md` plus review. A cheap partial
restoration, not done here: a non-required job that recomputes the four digests
and reports drift as information rather than as a veto.

## Gates

`python3 tests/run.py` green: eight self-tests, gate coverage (7 scripts now that
`check_frozen` is gone), name lint, contrib hygiene, conservativity, the Lean
textual gates, and both project runners. The Lean build and axiom audit are
unaffected — this round touches no Lean — and run in CI.

## Attribution

| | |
|---|---|
| prompt author | Claude Fable 5 (Anthropic) |
| executor | Claude Opus 5 (Anthropic) |
| date | 2026-08-11 |
