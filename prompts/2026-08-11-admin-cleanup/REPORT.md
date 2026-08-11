# Admin cleanup — report

Dispatch: `PROMPT.md` beside this file, verbatim.

## Outstanding maintainer actions

1. **Merge this pull request to recover the priorities round.** PR #7 was merged
   into `patch/attribution-provenance-names` at 04:43, after that branch had
   already squash-merged to `main` at 04:40. GitHub marks #7 merged; its content
   never reached `main`. This branch carries it. Details in §B.
2. **Then delete `patch/attribution-provenance-names` and
   `patch/priorities-and-slop`.** Held back deliberately — until this merges they
   are the only remote copies of the priorities round.
3. **Supply the two missing dispatches** — `2026-08-11-scrub-round-2` and
   `2026-08-11-contributor-checkers`. Nothing was supplied with this round, so the
   gaps stand as recorded.
4. **Answer the three stubs.** Each now states what deciding it costs; the
   deference one is the only one that blocks anything (§E).
5. **Consider whether `--record` should exist.** `tests/conservativity.py --record`
   is the deliberate way to re-baseline the spec shape, replacing the silent
   auto-write. It is a specification-layer escape hatch; if you would rather have
   no such flag and edit `tests/spec_shape.json` by hand, say so.

## D. A failure case for every gate

The round's substance. AGENTS.md gains a standard — *Every gate fails on its null
input* — and each of the nine gates now carries a `--self-test` run in the same CI
job as the gate, and in `tests/run.py` locally.

| gate | null input | case | where |
|---|---|---|---|
| `path_gate` | empty changed-file list **inside a pull request** | 8 cases incl. "an unknown path is in neither layer" and "no specification pattern is empty" | `tests/path_gate.py --self-test`, job `path-gate` |
| `dco` | no non-merge commits inside a pull request | 5 cases incl. "an empty message is rejected", "a sign-off without an address is rejected" | `tests/dco.py --self-test`, job `dco` |
| `attribution` | the untouched pull-request template | 7 cases; "pristine template asserts nothing" is the one that already caught a live defect | `tests/attribution.py --self-test`, job `dco` |
| `name_lint` | no Markdown in scope; a name it cannot see | 8 cases incl. "an empty file list fails rather than passing" and three pinning the backtick exemption | `tests/name_lint.py --self-test`, job `python` |
| `contrib_hygiene` | zero contributor checkers — *the current live state* | 5 cases on synthetic modules: missing docstring, third-party import, missing `check`, nested `check` | `tests/contrib_hygiene.py --self-test`, job `checkers` |
| `conservativity` | missing `spec_shape.json`; empty spec-file set | 7 cases incl. "the recorded shape exists" and "the word axiom inside an identifier is not matched" | `tests/conservativity.py --self-test`, job `conservativity` |
| `check_frozen` | a registry with no entries | 6 cases incl. "a content change moves the digest" and "the live registry is non-empty" | `tests/check_frozen.py --self-test`, job `frozen-integrity` |
| `audit_axioms` | no Lean sources; `#print axioms` naming declarations that do not exist | 7 cases incl. "silence is not a pass" and "an empty source list is a failure, not a skip" | `tests/audit_axioms.py --self-test`, job `lean` |
| registry checker | missing `PRIORITIES.md`; an unfiled item | "missing PRIORITIES.md fails rather than skipping the check", added last round | `python3 -m checkers.run --self-test`, job `checkers` |

### Four gates had real holes, not just missing tests

The audit was not a formality. Half the gates could pass while checking nothing:

- **`path_gate` and `dco` passed on an empty input inside a pull request.** Both
  printed "no pull-request context" and returned 0 when their diff came back
  empty. On a real pull request an empty diff means the fetch failed, not that the
  branch is clean — so a broken base fetch silently disabled the layer gate and
  the sign-off gate together. Both now fail when `GITHUB_BASE_REF` is set and the
  list is empty.
- **`conservativity` re-baselined itself.** A missing `tests/spec_shape.json`
  caused it to write the current shape and return 0 — so deleting the baseline
  silently re-froze the shape the gate exists to freeze, and reported green doing
  it. Now a failure, with `--record` as the deliberate way to set a baseline.
- **`check_frozen` verified an empty registry.** Zero entries produced
  `FROZEN DIGESTS VERIFIED: 0 registered inputs` and passed, which is what a wiped
  checksums file looks like from outside. Now a failure.

The two the dispatch cites were caught by a person reading code. These four were
caught by looking for the same shape deliberately, which is the argument for the
rule.

**The audit of `audit_axioms` runs on captured output, not on Lean.** Its parsing
cases feed recorded `lake env lean` lines to the regexes rather than invoking a
toolchain, so the self-test can run in every job rather than only the one with
`elan` installed. What that exercises is recognition, not elaboration — the
live run still re-elaborates every file.

## B. Branches — and the priorities round that never landed

**Confirming "merged" by branch name was the wrong test, twice.** `git branch -r
--merged` reports nothing under squash merges, and both `git diff main..branch`
and the three-dot form report differences for every branch regardless. The test
that works is whether each pull request's own merge commit is an ancestor of
`main`:

```sh
gh pr view N --json mergeCommit --jq .mergeCommit.oid
git merge-base --is-ancestor <oid> origin/main
```

| PR | branch | base | merge commit in `main`? |
|---|---|---|---|
| 1 | `flip/public-and-protection` | `main` | yes |
| 2 | `scrub/round-2` | `main` | yes |
| 3 | `feat/contributor-checkers` | `main` | yes |
| 4 | `rename/alignment-workspace` | `main` | yes |
| 6 | `patch/attribution-provenance-names` | `main` | yes |
| 7 | `patch/priorities-and-slop` | `patch/attribution-provenance-names` | **no** |

**PR #7 merged into a branch that had already been squash-merged and was a dead
end.** #6 landed on `main` at 04:40:21; #7 landed on #6's branch at 04:43:06.
GitHub retargets a stacked pull request when its base merges *while it is open*,
and #7 was merged directly against the stale base instead. `main` still had
`OPEN_PROBLEMS.md` and no `PRIORITIES.md`.

Recovered by cherry-picking `ccf229e` onto `main`; the resulting tree is
byte-identical to `patch/priorities-and-slop`'s (`003d2c3…`), so nothing was
lost or re-derived.

**This is the stacking trap I set up, and it is worth not repeating.** I stacked
two rounds on open branches to avoid conflicts, which worked, and then the merge
order that the stack required was not the one that happened. A stacked pull
request must be merged *before* its base, or retargeted to `main` after.

Deleted, with tips recorded so they remain reachable by SHA:

```
feat/contributor-checkers    2e3dba29c34513eda50a1b225f4e5db13faf3fc1
rename/alignment-workspace   c41e6725560769ff028e44457093f3bbf1e9824c
scrub/round-2                996cf925e483a67c5f9c8fb1354c3fcd736fa59b
```

Not deleted: `patch/attribution-provenance-names` and `patch/priorities-and-slop`.
Until this pull request merges they hold the only remote copies of the priorities
round.

## A. Dispatch-provenance gaps

**Nothing was supplied with this round**, so nothing was replaced. The two gaps
stand as recorded, and neither was paraphrased.

The third directory the dispatch flagged for checking,
`2026-08-11-public-flip-and-scrub`, **is not a gap of the same kind.** Its
`PROMPT.md` quotes the maintainer's three inline instructions verbatim — the
dispatch for that round *was* those instructions, and there is no separate
document that went missing. It already says so. Nothing to replace.

## C. The ledger's mutability

Adopted in the dispatch's terms, in the header rather than as an entry so it is
read before the entries are, with a sentence on why: a pointer that no longer
resolves is not history, it is a dead link, while a decision that turned out wrong
is corrected by the entry superseding it and not by editing the record of having
made it. Recorded as its own dated entry.

**One case the wording does not cover, reported rather than improvised.**
Removing something from a settled entry *for privacy* — a name, a personal
detail — is neither an identifier update nor something a later entry can fix by
appending: you cannot un-publish by adding text. It has not arisen, and this
ledger is deliberately exempt from the name lint, which is why it has not. If it
does, the header needs a third clause. Proposed shape, not applied:

> A passage removed for privacy is removed in place, and the removal is recorded
> as a dated entry that does not restate what was removed.

## E. The three stubs, with what deciding them costs

Rewritten in `DECISIONS.md` so each can be answered without reconstructing
context. Only the third blocks anything.

1. **Further leverage frozen trees — register now or later.** Registering costs a
   digest pass and makes the material citable and immutable from that moment.
   Waiting costs nothing today and risks the material drifting on your machine, so
   that what eventually gets frozen is a later version than the one the current
   work was done against. Nothing is blocked either way.
2. **The name `forward/`.** Confirming costs nothing. Changing it is one `git mv`,
   one file rename, and six prose references today — and the cost rises with every
   round that lands work in the tree or cites a path into it. The next leverage
   round is the first that would.
3. **Which deference documents are canonical.** This one forecloses.
   `projects/deference/kernel/` is reserved and empty and `notes/` holds a pointer
   and no documents, so a round dispatched against the deference line has nothing
   in-repo to work from — it would have to be handed its inputs in the dispatch,
   which is the provenance gap the convention exists to close.

## F. Consistency sweep

**F1 — `OPEN_PROBLEMS.md` references.** Not clean in the terms the dispatch
expected, and correctly so:

```sh
git grep -In "OPEN_PROBLEMS" -- . ':!prompts' ':!frozen'
```

Six hits, not two. Two are the deliberate pointers into
`frozen/consolidation_aug9/` — `PRIORITIES.md:32` and
`projects/leverage/README.md:40`. The other four are under
`projects/leverage/forward/attic/`, which the priorities dispatch explicitly
excluded as retired material. Correct as they stand; the dispatch's "except the
two" undercounted by not accounting for its own exclusion.

**F2 — required checks against job names.** Exact match, both against the payload
and against live protection:

```sh
python3 -c "…json.loads(.github/branch-protection.json) vs ^    name: in ci.yml"
gh api repos/A-M-Berns/alignment-workspace/branches/main/protection \
  --jq '.required_status_checks.contexts[]'
```

8 required contexts, 8 CI job names, none required-but-absent, none
job-but-not-required, and the live protection list matches the payload
string-for-string.

**F3 — `tests/run.py` invokes every gate script.** It did not.
`tests/conservativity.py` was never invoked locally at all, and
`tests/audit_axioms.py` was not invoked even under `WORKSPACE_LEAN`. Both wired
in — conservativity unconditionally, the axiom audit after a successful build.

Rather than assert this stays true, it is now checked: `coverage()` in
`tests/run.py` fails if any `tests/*.py` is neither invoked nor listed in
`PULL_REQUEST_ONLY`, which names the three gates whose real form needs a pull
request. Output:

```
GATE COVERAGE: 8 gate scripts, all invoked (3 self-test only — no local form)
```

## Gates

`python3 tests/run.py` green, now including nine self-tests, gate coverage,
conservativity, the name lint and contrib hygiene. Lean is unaffected — this round
touches no Lean — and runs in CI.

## Attribution

| | |
|---|---|
| prompt author | Claude Fable 5 (Anthropic) |
| executor | Claude Opus 5 (Anthropic) |
| date | 2026-08-11 |
